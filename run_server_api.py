# -*- coding: utf-8 -*-
# =====================================================
# 수직구 후보지 HTML 앱 - "다른 위치 평가하기" 전용 로컬 서버
# -----------------------------------------------------
# 기본 HTML(후보지 상세/지도/공식자료 조회)은 이 서버 없이도 그냥 열립니다.
# 이 서버는 오직 "공식자료 조회" 탭 안의 [다른 위치 평가하기] 검색창,
# 즉 QGIS가 미리 평가해놓은 후보지 목록 바깥의 임의 주소/지번을 입력해서
# 즉석으로 평가해보는 기능에만 필요합니다.
#
# 실행: 이 파일을 HTML과 같은 폴더에 두고
#       python run_server_api.py
#   브라우저로 http://localhost:8000 접속(카카오맵 등록 도메인과 동일)
#
# VWorld를 브라우저 JS가 직접 부르면 CORS로 막혀서(예: '탁상감정 보조 프로그램'
# 같은 데모도 화면엔 그냥 웹페이지처럼 보이지만 뒤에 localhost 서버가 있는 것과
# 동일한 이유) 이 파이썬 서버가 대신 호출합니다.
#
# 계산 가능한 점수: 소유(7)+작업장(6)+관리시설(3) = 16점
#   - 지장물(10점)·철도(5점)·보상난이도(4점)은 보안/현장조사 사유로 자동계산하지 않습니다.
# =====================================================

import http.server
import socketserver
import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
import json
import re
import math

import os as _os  # PORT/VWORLD_KEY를 환경변수로 받기 위함(렌더 등 배포 환경 대응)

PORT = int(_os.environ.get("PORT", "8000"))  # 렌더는 자체 포트를 PORT 환경변수로 내려줌

# ===================== 여기만 채우세요 (로컬 실행용 기본값) =====================
# 배포 환경(렌더 등)에서는 이 값을 코드에 직접 쓰지 말고, 그 서비스의
# Environment Variables 설정에서 VWORLD_KEY / VWORLD_DOMAIN 을 등록하세요.
# 환경변수가 있으면 그 값을 우선 사용하고, 없으면 아래 기본값(로컬 테스트용)을 씁니다.
VWORLD_KEY = _os.environ.get("VWORLD_KEY", "여기에 발급받은 VWorld 인증키")   # https://www.vworld.kr/dev/v4dv_apikey_s001.do
VWORLD_DOMAIN = _os.environ.get("VWORLD_DOMAIN", "")                          # 키 발급시 등록한 도메인. 없으면 빈 문자열 유지
VWORLD_STDR_YEAR = _os.environ.get("VWORLD_STDR_YEAR", "2026")                # 토지특성정보/개별공시지가 기준년도(숫자4자리)
# ============================================================

NED_BASE = "https://api.vworld.kr/ned/data"
ADDR_BASE = "https://api.vworld.kr/req/address"
WFS_BASE = "https://api.vworld.kr/req/wfs"
DATA_BASE = "https://api.vworld.kr/req/data"
HTTP_TIMEOUT = 8

MIN_AREA_M2 = 500.0
FLOOR_GATE = 5
WORKSPACE_OK_M2 = 1200.0
WORKSPACE_MID_M2 = 800.0
MGMT_MIN_W_M = 12.0
MGMT_COND_W_M = 8.0


def _get(url):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
        return resp.read().decode("utf-8", errors="replace")


def _t(node, tag):
    if node is None:
        return ""
    el = node.find(tag)
    return (el.text or "").strip() if el is not None else ""


def _qs(**params):
    return "&".join("{}={}".format(k, urllib.parse.quote(str(v), safe=""))
                     for k, v in params.items())


def clean_text(v):
    return (str(v) if v is not None else "").strip()


def classify_owner(raw):
    txt = clean_text(raw)
    if txt in ["국유지", "군유지", "시, 도유지", "시도유지", "구유지", "공유지", "공공",
               "국공유지", "외국인, 외국공공기관"]:
        return "공공"
    if txt in ["개인", "법인", "종중", "종교단체", "기타단체", "사유지", "민유지"]:
        return "사유"
    if "국" in txt or "시" in txt or "구" in txt or "공공" in txt:
        return "공공"
    if "개인" in txt or "법인" in txt or "사유" in txt:
        return "사유"
    return "미상"


def is_collective_or_large_commercial(uses_text, name_text=""):
    txt = clean_text(uses_text) + " " + clean_text(name_text)
    if txt.strip() == "":
        return False, ""
    collective_keys = ["집합", "공동주택", "아파트", "오피스텔", "연립", "다세대"]
    commercial_keys = ["판매", "업무", "상가", "백화점", "쇼핑", "마트", "시장", "호텔", "숙박", "근린생활"]
    for k in collective_keys:
        if k in txt:
            return True, "집합건물"
    for k in commercial_keys:
        if k in txt:
            return True, "대형 상업·업무시설"
    return False, ""


def sc_owner(own_class, max_floor, is_cc, has_building):
    """부지확보 용이성(7점) - 4단계
    우수(7): 공공부지(건물없음, 바로 확보 가능)
    보통(5): 공공부지이나 건물 있어 협의 필요
    조건부(3): 저층 사유지(FLOOR_GATE 미만)
    배제(0): 집합건물·대형상가 또는 고층(FLOOR_GATE 이상)
    """
    if is_cc or max_floor >= FLOOR_GATE:
        return "배제(집합건물·대형상가/고층)", 0
    if own_class == "공공":
        if has_building:
            return "보통(공공부지·협의필요)", 5
        return "우수(공공부지)", 7
    if own_class == "사유":
        return "조건부(저층 사유지)", 3
    return "조건부(소유 미상·검토필요)", 3


def sc_workspace(area_m2):
    """작업장 확보(6점) - 4단계: 확보충분/보완가능/협소/배제"""
    if area_m2 >= WORKSPACE_OK_M2:
        return "우수(작업장 확보)", 6
    if area_m2 >= WORKSPACE_MID_M2:
        return "보통(도로점용 등 보완 가능)", 4
    if area_m2 >= MIN_AREA_M2:
        return "조건부(공간 협소)", 2
    return "배제(장비배치 불가)", 0


def sc_compensation(own_class, has_building, co_owner_cnt):
    """보상 난이도(4점) - 4단계
    우수(4): 보상 없음(공공) 또는 단일 소유(사유+건물없음/공유1)
    보통(3): 소수 소유자(공유인수 2명 이상)
    조건부(2): 건물 있어 임차인·영업권 존재 가능성
    배제(0): (자동판정 어려움 - 권리관계 복잡은 현장조사 필요. 자동계산에서는 산정하지 않음)
    """
    if own_class == "공공":
        return "우수(보상 없음·공공)", 4
    if has_building:
        return "조건부(임차인·영업권 존재 가능)", 2
    if co_owner_cnt and co_owner_cnt >= 2:
        return "보통(소수 소유자)", 3
    return "우수(단일 소유)", 4


def sc_management(area_m2, short_w):
    """관리시설 배치(3점) - 4단계: 가능/일부조정/협소/배제"""
    if area_m2 >= 600 and short_w >= MGMT_MIN_W_M:
        return "우수(전기실·제어반·환기 등 가능)", 3
    if area_m2 >= MIN_AREA_M2 and short_w >= MGMT_COND_W_M:
        return "보통(일부 조정 필요)", 2
    if area_m2 >= MIN_AREA_M2:
        return "조건부(협소)", 1
    return "배제(배치 불가)", 0


def project_lonlat(coords, lat0):
    R = 6378137.0
    lat0r = math.radians(lat0)
    return [(math.radians(lon) * R * math.cos(lat0r), math.radians(lat) * R) for lon, lat in coords]


def polygon_area_perimeter(coords):
    n = len(coords)
    if n < 3:
        return 0.0, 0.0
    area2 = 0.0
    perim = 0.0
    for i in range(n):
        x1, y1 = coords[i]
        x2, y2 = coords[(i + 1) % n]
        area2 += x1 * y2 - x2 * y1
        perim += math.hypot(x2 - x1, y2 - y1)
    return abs(area2) / 2.0, perim


def convex_hull(points):
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def min_area_rect_wh(hull):
    n = len(hull)
    if n < 2:
        return 0.0, 0.0
    if n == 2:
        d = math.hypot(hull[1][0] - hull[0][0], hull[1][1] - hull[0][1])
        return 0.0, d
    best_w, best_h, min_area = 0.0, 0.0, float("inf")
    for i in range(n):
        p1, p2 = hull[i], hull[(i + 1) % n]
        ex, ey = p2[0] - p1[0], p2[1] - p1[1]
        elen = math.hypot(ex, ey)
        if elen == 0:
            continue
        ux, uy = ex / elen, ey / elen
        vx, vy = -uy, ux
        mnu = mnv = float("inf")
        mxu = mxv = float("-inf")
        for p in hull:
            dx, dy = p[0] - p1[0], p[1] - p1[1]
            du, dv = dx * ux + dy * uy, dx * vx + dy * vy
            mnu, mxu = min(mnu, du), max(mxu, du)
            mnv, mxv = min(mnv, dv), max(mxv, dv)
        w, h = mxu - mnu, mxv - mnv
        if w * h < min_area:
            min_area, best_w, best_h = w * h, w, h
    return min(best_w, best_h), max(best_w, best_h)


def shape_info_from_geojson(geometry):
    if not geometry:
        return 0.0, 0.0, 0.0
    gtype = geometry.get("type")
    coords = geometry.get("coordinates")
    if gtype == "MultiPolygon":
        ring = max((poly[0] for poly in coords), key=lambda r: len(r))
    elif gtype == "Polygon":
        ring = coords[0]
    else:
        return 0.0, 0.0, 0.0
    if len(ring) < 3:
        return 0.0, 0.0, 0.0
    lat0 = sum(p[1] for p in ring) / len(ring)
    xy = project_lonlat(ring, lat0)
    area, perim = polygon_area_perimeter(xy)
    compact = (4 * math.pi * area) / (perim * perim) if perim > 0 else 0.0
    hull = convex_hull(xy)
    short_w, long_w = min_area_rect_wh(hull)
    return short_w, long_w, compact


class VWorldResponseError(Exception):
    """VWorld가 JSON을 기대한 자리에 빈 응답/HTML 등 다른 걸 돌려준 경우.
    원본 응답 일부를 같이 담아서, 화면에 정확한 원인(키 오류/도메인 불일치/
    서비스 점검 등)이 보이게 합니다."""
    pass


def _json_get(url):
    raw = _get(url)
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        snippet = raw.strip()[:300] if raw else "(빈 응답)"
        raise VWorldResponseError("VWorld가 JSON이 아닌 응답을 반환했습니다: {}".format(snippet))


def find_parcel_by_address_text(addr):
    """
    지오코더(geocode_address)는 표기에 민감해서 흔히 실패합니다.
    대신 연속지적도 데이터(LP_PA_CBND_BUBUN)의 addr 속성에서 직접 텍스트로
    찾는 방식이라 "강동구 성내동 160-2"처럼 시/도를 빼거나 띄어쓰기가
    살짝 달라도 더 잘 찾습니다. 여러 건이 매칭되면 addr이 가장 긴 것
    (더 구체적인 지번)을 우선합니다.
    """
    url = DATA_BASE + "?" + _qs(
        service="data", request="GetFeature", data="LP_PA_CBND_BUBUN",
        key=VWORLD_KEY, domain=VWORLD_DOMAIN, format="json",
        attrFilter="addr:like:{}".format(addr), size="10", geometry="true")
    data = _json_get(url)
    fc = data.get("response", {}).get("result", {}).get("featureCollection", {})
    feats = fc.get("features") or []
    if not feats:
        return None
    feats.sort(key=lambda f: len(f.get("properties", {}).get("addr", "")), reverse=True)
    f = feats[0]
    props = f.get("properties", {})
    return {
        "pnu": props.get("pnu", ""),
        "jibun": props.get("jibun", ""),
        "addr": props.get("addr", ""),
        "geometry": f.get("geometry"),
    }


def geocode_address(addr):
    last_err = None
    for addr_type in ("PARCEL", "ROAD"):
        url = ADDR_BASE + "?" + _qs(
            service="address", request="getcoord", crs="epsg:4326",
            address=addr, format="json", type=addr_type,
            key=VWORLD_KEY, domain=VWORLD_DOMAIN)
        try:
            data = _json_get(url)
        except VWorldResponseError as e:
            last_err = e
            continue
        result = data.get("response", {}).get("result")
        if result and result.get("point"):
            pt = result["point"]
            return float(pt["x"]), float(pt["y"])
    if last_err:
        raise last_err
    return None


def _point_in_ring(x, y, ring):
    """레이캐스팅으로 점이 폴리곤 외곽선(ring) 안에 있는지 판정."""
    inside = False
    n = len(ring)
    j = n - 1
    for i in range(n):
        xi, yi = ring[i][0], ring[i][1]
        xj, yj = ring[j][0], ring[j][1]
        if ((yi > y) != (yj > y)) and (x < (xj - xi) * (y - yi) / (yj - yi + 1e-15) + xi):
            inside = not inside
        j = i
    return inside


def _point_in_geometry(x, y, geometry):
    if not geometry:
        return False
    gtype = geometry.get("type")
    coords = geometry.get("coordinates")
    if gtype == "Polygon":
        if not coords:
            return False
        if not _point_in_ring(x, y, coords[0]):
            return False
        for hole in coords[1:]:
            if _point_in_ring(x, y, hole):
                return False
        return True
    if gtype == "MultiPolygon":
        return any(_point_in_geometry(x, y, {"type": "Polygon", "coordinates": poly}) for poly in (coords or []))
    return False


def _ring_centroid(ring):
    sx = sum(p[0] for p in ring)
    sy = sum(p[1] for p in ring)
    n = len(ring) or 1
    return sx / n, sy / n


def _geometry_centroid(geometry):
    gtype = geometry.get("type")
    coords = geometry.get("coordinates")
    if gtype == "Polygon" and coords:
        return _ring_centroid(coords[0])
    if gtype == "MultiPolygon" and coords:
        return _ring_centroid(coords[0][0])
    return None


def get_parcel_by_point(x, y, buf_deg=0.0006):
    """
    좌표(x,y) 인근 필지들을 WFS bbox로 여러 개 받아온 뒤, 그중 실제로 그 점을
    포함하는 필지를 골라 반환합니다. 예전엔 bbox 안에서 그냥 첫 번째 결과를
    썼는데, 그게 클릭한 자리가 아닌 옆 필지로 잘못 잡히는 원인이었습니다.
    포함하는 필지가 하나도 없으면(드물게 경계선/도로 위 클릭 등) 중심점이
    가장 가까운 필지로 대체합니다.
    """
    bbox = "{},{},{},{}".format(x - buf_deg, y - buf_deg, x + buf_deg, y + buf_deg)
    url = WFS_BASE + "?" + _qs(
        SERVICE="WFS", REQUEST="GetFeature", TYPENAME="lp_pa_cbnd_bubun",
        VERSION="1.1.0", MAXFEATURES="30", SRSNAME="EPSG:4326", OUTPUT="json",
        BBOX=bbox, KEY=VWORLD_KEY, DOMAIN=VWORLD_DOMAIN)
    data = _json_get(url)
    feats = data.get("features") or []
    if not feats:
        return None

    containing = [f for f in feats if _point_in_geometry(x, y, f.get("geometry"))]
    if containing:
        f = containing[0]
    else:
        # 포함하는 필지가 없으면(도로/경계 등) 중심점이 가장 가까운 필지로 대체
        def dist(f):
            c = _geometry_centroid(f.get("geometry") or {})
            if not c:
                return float("inf")
            return (c[0] - x) ** 2 + (c[1] - y) ** 2
        f = min(feats, key=dist)

    props = f.get("properties", {})
    return {
        "pnu": props.get("pnu", ""),
        "jibun": props.get("jibun", ""),
        "addr": props.get("addr", ""),
        "geometry": f.get("geometry"),
    }


def fetch_land(pnu):
    out = {}
    url1 = NED_BASE + "/ladfrlList?" + _qs(
        format="xml", key=VWORLD_KEY, domain=VWORLD_DOMAIN, pnu=pnu)
    try:
        root = ET.fromstring(_get(url1))
        if root.find("error") is None:
            total = int(_t(root, "totalCount") or "0")
            if total >= 1:
                node = root.find("ladfrlVOList")
                out["지목"] = _t(node, "lndcgrCodeNm")
                out["토지면적"] = _t(node, "lndpclAr")
                out["소유구분"] = _t(node, "posesnSeCodeNm")
                out["공유인수"] = _t(node, "cnrsPsnCo")
    except Exception as e:
        out["_err_land"] = "토지임야정보 조회 실패: {}".format(e)

    url2 = NED_BASE + "/getLandCharacteristics?" + _qs(
        format="xml", key=VWORLD_KEY, domain=VWORLD_DOMAIN,
        stdrYear=VWORLD_STDR_YEAR, pnu=pnu)
    try:
        root = ET.fromstring(_get(url2))
        total = int(_t(root, "totalCount") or "0")
        if total >= 1:
            fields = root.findall("./fields/field")
            node = fields[-1] if fields else None
            out["용도지역"] = _t(node, "prposArea1Nm")
            out["용도지역2"] = _t(node, "prposArea2Nm")
            out["토지이용상황"] = _t(node, "ladUseSittnNm")
    except Exception as e:
        out["_err_char"] = "토지특성정보 조회 실패: {}".format(e)

    url3 = NED_BASE + "/getIndvdLandPriceAttr?" + _qs(
        format="xml", key=VWORLD_KEY, domain=VWORLD_DOMAIN,
        stdrYear=VWORLD_STDR_YEAR, pnu=pnu)
    try:
        root = ET.fromstring(_get(url3))
        total = int(_t(root, "totalCount") or "0")
        if total >= 1:
            fields = root.findall("./fields/field")
            node = fields[-1] if fields else None
            out["개별공시지가"] = _t(node, "pblntfPclnd")
            out["공시지가기준일"] = _t(node, "pblntfDe")
    except Exception as e:
        out["_err_price"] = "개별공시지가 조회 실패: {}".format(e)

    url4 = NED_BASE + "/getLandUseAttr?" + _qs(
        numOfRows="1000", format="xml", key=VWORLD_KEY,
        domain=VWORLD_DOMAIN, pnu=pnu)
    try:
        root = ET.fromstring(_get(url4))
        total = int(_t(root, "totalCount") or "0")
        groups = {"1": [], "2": [], "3": []}
        if total > 0:
            for node in root.findall("./fields/field"):
                grp = _t(node, "cnflcAt") or "1"
                name = _t(node, "prposAreaDstrcCodeNm")
                if name and name not in groups.setdefault(grp, []):
                    groups[grp].append(name)
        out["토지이용계획"] = {"포함": groups.get("1", []), "저촉": groups.get("2", []),
                          "기타": groups.get("3", [])}
    except Exception as e:
        out["_err_use"] = "토지이용계획 조회 실패: {}".format(e)
    return out


def fetch_building(pnu):
    url = NED_BASE + "/getBuildingUse?" + _qs(
        numOfRows="100", format="xml", key=VWORLD_KEY,
        domain=VWORLD_DOMAIN, pnu=pnu)
    try:
        root = ET.fromstring(_get(url))
        total = int(_t(root, "totalCount") or "0")
        if total <= 0:
            return {"_empty": True}
        buildings = []
        for node in root.findall("./fields/field"):
            buildings.append({
                "주용도": _t(node, "mainPrposCodeNm"),
                "세부용도": _t(node, "detailPrposCodeNm"),
                "건물명": _t(node, "buldNm"),
                "구조": _t(node, "strctCodeNm"),
                "대지면적": _t(node, "buldPlotAr"),
                "연면적": _t(node, "buldTotar"),
                "건축면적": _t(node, "buldBildngAr"),
                "높이": _t(node, "buldHg"),
                "건폐율": _t(node, "measrmtRt"),
                "용적률": _t(node, "btlRt"),
                "지상층수": _t(node, "groundFloorCo"),
                "지하층수": _t(node, "undgrndFloorCo"),
                "사용승인일": _t(node, "useConfmDe"),
                "허가일": _t(node, "prmisnDe"),
                "동명칭": _t(node, "buldDongNm"),
            })
        return {"buildings": buildings}
    except Exception as e:
        return {"_err": "건축물 조회 실패: {}".format(e)}


def score_site(land, building, geometry):
    area_m2 = float(land.get("토지면적") or 0) or 0.0
    own_class = classify_owner(land.get("소유구분"))
    try:
        co_owner_cnt = int(float(land.get("공유인수") or 0))
    except Exception:
        co_owner_cnt = 0

    blds = (building or {}).get("buildings") or []
    has_building = len(blds) > 0
    max_floor = 0
    uses, names = [], []
    for b in blds:
        try:
            max_floor = max(max_floor, int(float(b.get("지상층수") or 0)))
        except Exception:
            pass
        if b.get("주용도"):
            uses.append(b["주용도"])
        if b.get("세부용도"):
            uses.append(b["세부용도"])
        if b.get("건물명"):
            names.append(b["건물명"])
    is_cc, cc_label = is_collective_or_large_commercial("; ".join(uses), "; ".join(names))

    short_w, long_w, compact = shape_info_from_geojson(geometry)

    o_label, o_pts = sc_owner(own_class, max_floor, is_cc, has_building)
    w_label, w_pts = sc_workspace(area_m2)
    c_label, c_pts = sc_compensation(own_class, has_building, co_owner_cnt)
    m_label, m_pts = sc_management(area_m2, short_w)

    return {
        "area_m2": round(area_m2, 1),
        "own_class": own_class,
        "max_floor": max_floor,
        "is_cc": is_cc, "cc_label": cc_label,
        "co_owner_cnt": co_owner_cnt,
        "short_w": round(short_w, 1), "long_w": round(long_w, 1), "compact": round(compact, 3),
        "owner": {"label": o_label, "pts": o_pts, "max": 7},
        "workspace": {"label": w_label, "pts": w_pts, "max": 6},
        "compensation": {"label": c_label, "pts": c_pts, "max": 4},
        "management": {"label": m_label, "pts": m_pts, "max": 3},
        "total": o_pts + w_pts + c_pts + m_pts,
        "max_total": 20,
        "excluded_note": "대형 지장물 간섭(6)·지하철/철도/GTX 영향(5)·유틸리티 이설성(4) "
                          "= 15점은 보안/현장조사 사유로 자동계산하지 않습니다(35점 만점 중 20점만 자동화).",
    }


# ===================== 비밀번호 게이트 =====================
# 렌더 Environment Variables에 SITE_PASSWORD를 등록하면 그 비밀번호를 입력해야
# 사이트(정적 HTML 포함 전체)에 접근할 수 있습니다. 비워두면(로컬 테스트 등) 게이트 없이 그냥 열립니다.
# 아이디는 아무거나(빈칸이어도 됨) 입력해도 되고, 비밀번호만 일치하면 통과합니다.
SITE_PASSWORD = _os.environ.get("SITE_PASSWORD", "")
import base64 as _base64


class Handler(http.server.SimpleHTTPRequestHandler):
    def _check_auth(self):
        if not SITE_PASSWORD:
            return True
        header = self.headers.get("Authorization", "")
        if not header.startswith("Basic "):
            return False
        try:
            decoded = _base64.b64decode(header[6:]).decode("utf-8", errors="replace")
            _, _, pwd = decoded.partition(":")
        except Exception:
            return False
        return pwd == SITE_PASSWORD

    def _require_auth(self):
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="restricted"')
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        body = "비밀번호가 필요합니다.".encode("utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if not self._check_auth():
            self._require_auth()
            return
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path == "/api/search":
            self._handle_search(parsed)
            return
        if parsed.path == "/api/pnu":
            self._handle_pnu(parsed)
            return
        if parsed.path == "/api/parcel":
            self._handle_parcel(parsed)
            return
        if parsed.path == "/api/landinfo":
            self._handle_landinfo(parsed)
            return
        super().do_GET()

    def _key_ok(self):
        return bool(VWORLD_KEY) and "여기에" not in VWORLD_KEY

    def _handle_pnu(self, parsed):
        # 클릭 좌표 -> PNU만 가볍게 조회(토지/건축물 정보는 안 부름). 이미 QGIS에서
        # 평가해둔 후보(DATA)에 이 PNU가 있으면 그 결과를 그대로 쓰고, 없을 때만
        # /api/parcel 로 VWorld 풀조회 하도록 화면 쪽에서 분기합니다.
        qs = urllib.parse.parse_qs(parsed.query)
        try:
            lon = float(qs.get("lon", [""])[0])
            lat = float(qs.get("lat", [""])[0])
        except (TypeError, ValueError):
            self._send_json({"error": "lon/lat 파라미터가 올바르지 않습니다."}, 400)
            return
        if not self._key_ok():
            self._send_json({"error": "run_server_api.py 의 VWORLD_KEY가 아직 설정되지 않았습니다."}, 500)
            return
        try:
            parcel = get_parcel_by_point(lon, lat)
            if not parcel or not parcel.get("pnu"):
                self._send_json({"error": "해당 위치의 필지를 찾지 못했습니다(도로/하천 등일 수 있음)."}, 404)
                return
            pnu = re.sub(r"\D", "", parcel["pnu"])
            self._send_json({"pnu": pnu, "jibun": parcel.get("jibun"), "addr": parcel.get("addr")}, 200)
        except Exception as e:
            self._send_json({"error": "서버 처리 중 오류: {}".format(e)}, 500)

    def _handle_parcel(self, parsed):
        # 카카오맵 클릭 좌표로 바로 필지를 찾습니다(주소 텍스트 변환 단계가 없어
        # 지오코더 표기 이슈에 영향받지 않고, 점수는 계산하지 않습니다 - 지번/건축물 정보만 표시).
        qs = urllib.parse.parse_qs(parsed.query)
        try:
            lon = float(qs.get("lon", [""])[0])
            lat = float(qs.get("lat", [""])[0])
        except (TypeError, ValueError):
            self._send_json({"error": "lon/lat 파라미터가 올바르지 않습니다."}, 400)
            return
        if not self._key_ok():
            self._send_json({"error": "run_server_api.py 의 VWORLD_KEY가 아직 설정되지 않았습니다."}, 500)
            return
        try:
            parcel = get_parcel_by_point(lon, lat)
            if not parcel or not parcel.get("pnu"):
                self._send_json({"error": "해당 위치의 필지를 찾지 못했습니다(도로/하천 등일 수 있음)."}, 404)
                return
            pnu = re.sub(r"\D", "", parcel["pnu"])
            land = fetch_land(pnu)
            building = fetch_building(pnu)
            score = score_site(land, building, parcel.get("geometry"))
            self._send_json({
                "pnu": pnu, "jibun": parcel.get("jibun"), "addr": parcel.get("addr"),
                "land": land, "building": building, "score": score,
            }, 200)
        except Exception as e:
            self._send_json({"error": "서버 처리 중 오류: {}".format(e)}, 500)

    def _handle_search(self, parsed):
        qs = urllib.parse.parse_qs(parsed.query)
        addr = (qs.get("addr", [""])[0] or "").strip()
        if not addr:
            self._send_json({"error": "주소/지번을 입력하세요."}, 400)
            return
        if not self._key_ok():
            self._send_json({"error": "run_server_api.py 의 VWORLD_KEY가 아직 설정되지 않았습니다."}, 500)
            return
        try:
            try:
                parcel = find_parcel_by_address_text(addr)
            except VWorldResponseError:
                parcel = None  # 텍스트검색 실패시 좌표변환 경로로 폴백
            if not parcel or not parcel.get("pnu"):
                xy = geocode_address(addr)
                if not xy:
                    self._send_json({"error": "주소를 찾지 못했습니다. 지번(예: 강남구 개포동 171) "
                                               "또는 도로명주소로 다시 입력해보세요. "
                                               "시/도를 빼고 '구 동 번지'만 입력해도 됩니다."}, 404)
                    return
                parcel = get_parcel_by_point(xy[0], xy[1])
            if not parcel or not parcel.get("pnu"):
                self._send_json({"error": "해당 위치의 필지를 찾지 못했습니다(도로/하천 등일 수 있음)."}, 404)
                return
            pnu = re.sub(r"\D", "", parcel["pnu"])
            land = fetch_land(pnu)
            building = fetch_building(pnu)
            score = score_site(land, building, parcel.get("geometry"))
            self._send_json({
                "pnu": pnu, "jibun": parcel.get("jibun"), "addr": parcel.get("addr"),
                "land": land, "building": building, "score": score,
            }, 200)
        except Exception as e:
            self._send_json({"error": "서버 처리 중 오류: {}".format(e)}, 500)

    def _handle_landinfo(self, parsed):
        qs = urllib.parse.parse_qs(parsed.query)
        pnu = re.sub(r"\D", "", (qs.get("pnu", [""])[0] or ""))
        if len(pnu) != 19:
            self._send_json({"error": "PNU는 숫자 19자리여야 합니다."}, 400)
            return
        if not self._key_ok():
            self._send_json({"error": "VWORLD_KEY가 설정되지 않았습니다."}, 500)
            return
        try:
            self._send_json({"pnu": pnu, "land": fetch_land(pnu), "building": fetch_building(pnu)}, 200)
        except Exception as e:
            self._send_json({"error": "서버 처리 중 오류: {}".format(e)}, 500)

    def _send_json(self, obj, status):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt, *args):
        print("[{}] {}".format(self.address_string(), fmt % args))


if __name__ == "__main__":
    if "여기에" in VWORLD_KEY:
        print("=" * 70)
        print("[경고] VWORLD_KEY가 설정되지 않았습니다. 이 파일 상단에 키를 넣어주세요.")
        print("키 발급: https://www.vworld.kr/dev/v4dv_apikey_s001.do")
        print("=" * 70)
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer(("", PORT), Handler) as httpd:
        print("=" * 70)
        print("서버 시작: http://localhost:{}".format(PORT))
        print("다른 위치 평가 API: http://localhost:{}/api/search?addr=주소".format(PORT))
        if SITE_PASSWORD:
            print("[비밀번호 게이트] 활성화됨 — 접속시 브라우저가 ID/비밀번호를 물어봅니다(비밀번호만 확인).")
        else:
            print("[비밀번호 게이트] 비활성화 — SITE_PASSWORD 환경변수가 비어있어 누구나 접속 가능합니다.")
        print("Ctrl+C 로 종료")
        print("=" * 70)
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("서버 종료")
