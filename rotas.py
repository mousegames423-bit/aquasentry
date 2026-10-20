"""rotas.py - Motor de varredura e algoritmos de caminho.

Dijkstra (grade e grafo de visibilidade), rota segura, simplificação (U-turn + Ramer-Douglas-Peucker), varredura completa,
rota "borda + meio", divisão por limite de waypoints, rota manual e estimativa de tempo.
"""

import heapq
import math

from PIL import Image, ImageDraw
from scipy import ndimage
from shapely.affinity import rotate
from shapely.geometry import LineString, Point, Polygon
from shapely.ops import nearest_points, unary_union
from shapely.prepared import prep
import numpy as np

from geo_mapa import ILHA_MIN_ROTA_M2, M_LAT, _area_ll_m2, _rdp, m_lon

# ---------------- CONFIGURAÇÃO (o que você pode ajustar) ----------------
# --- Rota de varredura: tudo calculado a partir da LARGURA REAL do robô (em metros no lago, não em pixels) ---
LARGURA_ROBO_M = 0.50   # largura do barco

SOBREPOSICAO = 0.10     # 10% de sobreposição entre faixas vizinhas

ESPACAMENTO_M = round(LARGURA_ROBO_M * (1 - SOBREPOSICAO), 3)   # = 0,45 m

MARGEM_M = 3.0          # distância mínima da "parede" (GPS comum erra alguns metros)

COMPRIMENTO_MIN_FAIXA_M = 0.3

ANGULO_PASSO = 5        # direção das faixas testada de 5 em 5 graus

MAX_WAYPOINTS = 4000    # = MAX_W do firmware


# ---------- Rota de varredura (idêntica à Central v5) ----------
def _dijkstra_grade(livre, a, b):
    """Menor caminho (8 vizinhos) numa grade de água. livre = matriz True/False; a, b = (linha, coluna). None se não há."""
    H, W = livre.shape
    if not (livre[a] and livre[b]): return None
    dist = np.full((H, W), np.inf); dist[a] = 0.0
    ant = {}; fila = [(0.0, a)]
    viz = [(-1, 0, 1.0), (1, 0, 1.0), (0, -1, 1.0), (0, 1, 1.0),
           (-1, -1, 1.4142), (-1, 1, 1.4142), (1, -1, 1.4142), (1, 1, 1.4142)]
    while fila:
        d, (i, j) = heapq.heappop(fila)
        if d > dist[i, j]: continue
        if (i, j) == b: break
        for di, dj, custo in viz:
            ni, nj = i + di, j + dj
            if not (0 <= ni < H and 0 <= nj < W) or not livre[ni, nj]: continue
            if di and dj and not (livre[i + di, j] and livre[i, j + dj]): continue    # não corta quina de terra
            nd = d + custo
            if nd < dist[ni, nj]:
                dist[ni, nj] = nd; ant[(ni, nj)] = (i, j); heapq.heappush(fila, (nd, (ni, nj)))
    if not np.isfinite(dist[b]): return None
    rota = [b]
    while rota[-1] != a: rota.append(ant[rota[-1]])
    return rota[::-1]


def _caminho_grade(a, b, poly, livre_fn):
    """Plano B do desvio: Dijkstra numa grade feita SÓ com a água do polígono (metros). Devolve pontos ou None."""
    minx, miny, maxx, maxy = poly.bounds
    cel = max(0.5, max(maxx - minx, maxy - miny) / 500)
    nx, ny = int((maxx - minx) / cel) + 2, int((maxy - miny) / cel) + 2
    im = Image.new("L", (nx, ny), 0)
    dr = ImageDraw.Draw(im)
    dr.polygon([((x - minx) / cel, (y - miny) / cel) for x, y in poly.exterior.coords], fill=1)
    for r in getattr(poly, "interiors", []):                                     # ilhas: zona proibida
        dr.polygon([((x - minx) / cel, (y - miny) / cel) for x, y in r.coords], fill=0)
    livre = ndimage.binary_erosion(np.array(im, bool), iterations=1)          # 1 célula de folga da margem
    if not livre.any(): return None
    def celula(p):
        i = min(max(int(round((p[1] - miny) / cel)), 0), ny - 1); j = min(max(int(round((p[0] - minx) / cel)), 0), nx - 1)
        if livre[i, j]: return i, j
        _, idx = ndimage.distance_transform_edt(~livre, return_indices=True)    # célula de água mais próxima
        return int(idx[0][i, j]), int(idx[1][i, j])
    cam = _dijkstra_grade(livre, celula(a), celula(b))
    if cam is None: return None
    pm = [(minx + j * cel, miny + i * cel) for i, j in cam]
    saida, k = [tuple(a)], 0
    while k < len(pm) - 1:                                                      # alisa: pula células enquanto a reta for água
        prox = k + 1
        for t in range(min(len(pm) - 1, k + 80), k, -1):
            if livre_fn(pm[k], pm[t]): prox = t; break
        saida.append(pm[prox]); k = prox
    saida.append(tuple(b))
    if any(not livre_fn(p, q) for p, q in zip(saida[:-1], saida[1:])): return None   # conferência final: nada de terra
    return saida


# Menor caminho de a até b dentro do polígono. NUNCA devolve linha reta sobre terra: se não existe, devolve None.
def _caminho_seguro(a, b, nos, livre_fn, cache, poly=None):
    pontos = [tuple(a), tuple(b)] + [tuple(v) for v in nos]
    n = len(pontos)
    dist = [float("inf")] * n; ant = [-1] * n; dist[0] = 0.0
    fila = [(0.0, 0)]
    while fila:
        d, i = heapq.heappop(fila)
        if d > dist[i]: continue
        if i == 1: break
        for j in range(n):
            if j == i: continue
            L = math.dist(pontos[i], pontos[j])
            if d + L >= dist[j]: continue
            chave = (min(i, j), max(i, j)) if i >= 2 and j >= 2 else None
            if L < 1e-6: livre = True
            elif chave is not None and chave in cache: livre = cache[chave]
            else:
                livre = livre_fn(pontos[i], pontos[j])
                if chave is not None: cache[chave] = livre
            if livre:
                dist[j] = d + L; ant[j] = i
                heapq.heappush(fila, (dist[j], j))
    if dist[1] != float("inf"):
        rota = []; k = 1
        while k != -1: rota.append(pontos[k]); k = ant[k]
        return rota[::-1]
    return _caminho_grade(a, b, poly, livre_fn) if poly is not None else None      # plano B; senão, None (sem atalho por terra)


def _com_desvios(pts, poly, avisos):
    """Liga os pontos em ordem, desviando pela água. Trecho impossível é PULADO (e avisado), nunca atravessa terra."""
    if len(pts) < 2: return pts
    area_ok = prep(poly.buffer(0.1))
    livre_fn = lambda p, q: area_ok.covers(LineString([p, q]))
    simples = poly.simplify(1.5)
    nos = np.array(list(simples.exterior.coords)[:-1] + [c for r in getattr(simples, "interiors", []) for c in list(r.coords)[:-1]])
    cache = {}; saida = [pts[0]]; pulados = 0
    for q in pts[1:]:
        p = saida[-1]
        if math.dist(p, q) < 1e-6: continue
        if livre_fn(p, q): saida.append(q); continue
        cam = _caminho_seguro(p, q, nos, livre_fn, cache, poly)
        if cam: saida += cam[1:]
        else: pulados += 1
    if pulados:
        avisos.append(f"{pulados} ponto(s) da rota ficaram sem caminho de água (canal fechado pela margem de segurança) e foram "
                      f"PULADOS, para o robô nunca atravessar terra. Diminua a margem da parede ou ajuste o contorno.")
    return saida


def reduzir_rota(pts, espac, livre_fn=None, tol=0.2):
    """Menos waypoints, mesmo caminho (pts em metros):
    1) cada CURVA em U (dois pontos a ~1 espaçamento um do outro) vira UM ponto no meio;
    2) Douglas-Peucker tira pontos que desviam menos que 'tol' metros da reta (ex.: curvas suaves da margem).
    livre_fn(p, q) (opcional): confere se o trecho p-q é água; se não for, a curva não é fundida."""
    if len(pts) < 4: return list(pts)
    out = [pts[0]]; i = 1
    while i < len(pts):
        if i + 1 < len(pts) - 1 and math.dist(pts[i], pts[i + 1]) <= 1.6 * espac:
            m = ((pts[i][0] + pts[i + 1][0]) / 2, (pts[i][1] + pts[i + 1][1]) / 2)
            if livre_fn is None or livre_fn(out[-1], m):
                out.append(m); i += 2; continue
        out.append(pts[i]); i += 1
    if len(out) >= 3:
        P = np.array(out, float)
        out = [out[k] for k in _rdp(P, tol)]
    return out


def varredura_que_cabe(poly_ll, espac, margem, auto, parte, avisos, maximo=None, ilhas_ll=()):
    maximo = maximo or LIMITE_SEGURO
    """Recalcula a rota aumentando o espaçamento aos poucos até caber no limite do robô. Devolve (waypoints, espaçamento)."""
    for _ in range(5):
        avisos.clear()
        wps = gerar_varredura(poly_ll, espac, margem, auto, parte, avisos, ilhas_ll)
        if len(wps) <= maximo: break
        espac = round(espac * min(1.6, max(1.05, len(wps) / maximo * 1.03)), 3)
    return wps, espac


LIMITE_SEGURO = MAX_WAYPOINTS - 400      # alvo da rota: fica 10% abaixo do limite do robô (sobra para a conexão e imprevistos)

RESERVA_CONEXAO = 100        # pontos guardados em cada missão para o caminho "de onde o barco está até o início da parte"


def dividir_rota(wps, maximo=MAX_WAYPOINTS):
    """Rota grande demais para a memória do robô -> várias missões em sequência (cobertura 100% mantida)."""
    tam = max(10, maximo - RESERVA_CONEXAO)
    return [wps[k:k + tam] for k in range(0, len(wps), tam)] or [[]]


def rota_segura(pts, poly):
    """True se TODOS os trechos da rota ficam dentro da água (conferência final antes de aceitar a rota)."""
    area_ok = prep(poly.buffer(0.1))
    return all(area_ok.covers(LineString([p, q])) for p, q in zip(pts[:-1], pts[1:]) if math.dist(p, q) > 1e-6)


def _cadeias(poly, espac):
    """Corta o lago em faixas paralelas e agrupa os trechos em CADEIAS: sequências de faixas vizinhas que se sobrepõem
    (uma 'célula' do lago, como cada lagoa ligada por um estreito). Cada cadeia tem 1 trecho por faixa."""
    minx, miny, maxx, maxy = poly.bounds
    altura = maxy - miny
    n = max(1, math.ceil(altura / espac))
    passo = altura / n
    cadeias, ativas = [], []
    for i in range(n):
        y = miny + passo * (i + 0.5)
        inter = poly.intersection(LineString([(minx - 1, y), (maxx + 1, y)]))
        segs = []
        for g in getattr(inter, "geoms", [inter]):
            if g.geom_type == "LineString" and g.length > COMPRIMENTO_MIN_FAIXA_M:
                (x1, y1), (x2, y2) = g.coords[0], g.coords[-1]
                segs.append(((min(x1, x2), y), (max(x1, x2), y)))
        segs.sort(key=lambda t: t[0][0])
        usadas, novas = set(), []
        for sg in segs:
            melhor, ov_m = None, 0.0
            for k, ch in enumerate(ativas):
                if k in usadas: continue
                pa, pb = ch[-1]
                ov = min(sg[1][0], pb[0]) - max(sg[0][0], pa[0])
                if ov > ov_m: melhor, ov_m = k, ov
            if melhor is None:
                ch = [sg]; cadeias.append(ch); novas.append(ch)
            else:
                usadas.add(melhor); ativas[melhor].append(sg); novas.append(ativas[melhor])
        ativas = novas
    return cadeias


def _faixas(poly, espac):
    """Zigue-zague que varre UMA cadeia (célula) inteira antes de passar para a próxima; assim o barco não fica
    atravessando o lago de uma lagoa a outra a cada faixa. Entre cadeias, vai para a ponta mais próxima."""
    cadeias = _cadeias(poly, espac)
    if not cadeias: return []
    cadeias.sort(key=lambda ch: (ch[0][0][1], ch[0][0][0]))
    pts, restantes = [], list(range(len(cadeias)))
    pos = None
    while restantes:
        if pos is None: k, inverte = restantes[0], False
        else:
            melhor = None
            for kk in restantes:
                ch = cadeias[kk]
                for inv, lane in ((False, ch[0]), (True, ch[-1])):
                    d = min(math.dist(pos, lane[0]), math.dist(pos, lane[1]))
                    if melhor is None or d < melhor[0]: melhor = (d, kk, inv)
            _, k, inverte = melhor
        restantes.remove(k)
        ch = cadeias[k][::-1] if inverte else cadeias[k]
        for lane in ch:
            a, b = lane
            if pos is not None and math.dist(pos, b) < math.dist(pos, a): a, b = b, a
            pts += [a, b]; pos = b
    return pts


def _melhor_angulo(poly, espac):
    minx, miny, maxx, maxy = poly.bounds
    busca = max(espac, math.hypot(maxx - minx, maxy - miny) / 40)
    melhor, custo_melhor = 0, float("inf")
    for ang in range(0, 180, ANGULO_PASSO):
        pr = rotate(poly, -ang, origin=(0, 0))
        x0, y0, x1, y1 = pr.bounds
        n_trechos, y = 0, y0 + busca / 2
        while y <= y1:
            inter = pr.intersection(LineString([(x0 - 1, y), (x1 + 1, y)]))
            n_trechos += sum(1 for g in getattr(inter, "geoms", [inter])
                             if g.geom_type == "LineString" and g.length > COMPRIMENTO_MIN_FAIXA_M)
            y += busca
        custo = n_trechos + 1e-6 * (y1 - y0)
        if custo < custo_melhor: melhor, custo_melhor = ang, custo
    return melhor


def _enxugar(pts, tol=0.05):
    out = []
    for p in pts:
        if out and math.dist(out[-1], p) < 0.01: continue
        out.append(p)
    if len(out) < 3: return out
    res = [out[0]]
    for i in range(1, len(out) - 1):
        a, b, c = res[-1], out[i], out[i + 1]
        dx, dy = c[0] - a[0], c[1] - a[1]; L = math.hypot(dx, dy)
        if L > 1e-9 and abs(dx * (b[1] - a[1]) - dy * (b[0] - a[0])) / L < tol: continue
        res.append(b)
    res.append(out[-1])
    return res


def _base_metrica(poly_ll, ilhas_ll, to_xy):
    """O lago em metros = contorno MENOS as ilhas (zonas proibidas). Pode ficar em vários pedaços."""
    base = Polygon([to_xy(*p) for p in poly_ll])
    if not base.is_valid: base = base.buffer(0)
    polis = []
    for r in ilhas_ll or []:
        if len(r) >= 3:
            q = Polygon([to_xy(*p) for p in r])
            if not q.is_valid: q = q.buffer(0)
            if not q.is_empty and q.area >= ILHA_MIN_ROTA_M2: polis.append(q)    # ruído minúsculo nunca quebra a rota
    if polis:
        try: base = base.difference(unary_union(polis))
        except Exception: pass                                    # se a ilha der problema, a rota ainda sai (sem ela)
    return base


def _partes_de(base, margem):
    """Pedaços de água depois da margem de segurança (a margem pode separar o lago em pontes, estreitos e ilhas)."""
    enc = base.buffer(-margem)
    partes = sorted([g for g in getattr(enc, "geoms", [enc]) if g.geom_type == "Polygon" and g.area > 1.0],
                    key=lambda g: g.area, reverse=True)
    if not partes: raise ValueError("Contorno pequeno demais para a margem escolhida. Diminua a margem da parede.")
    return partes


def _passagem(a, b, base, margem, avisos):
    """Caminho PELA ÁGUA de a até b (de um pedaço do lago a outro), tolerando passar mais perto da margem do que a varredura
    (estreitos e sob pontes). Tenta margens cada vez menores; None se não existe água ligando os dois."""
    for m in (max(margem * 0.5, 1.0), 1.0, 0.5):
        t = base.buffer(-m)
        for comp in getattr(t, "geoms", [t]):
            if comp.geom_type != "Polygon" or comp.is_empty: continue
            folga = comp.buffer(0.2)
            if folga.covers(Point(a)) and folga.covers(Point(b)):
                cam = _com_desvios([tuple(a), tuple(b)], comp, [])
                if len(cam) >= 2 and math.dist(cam[-1], b) < 0.05:
                    if m < margem:
                        msg = (f"A ligação entre partes do lago passa a {m:g} m da margem (a margem de {margem:g} m não cabe no estreito). "
                               f"É só trânsito; confira se o barco aguenta essa passagem.")
                        if msg not in avisos: avisos.append(msg)
                    return cam
    return None


def _ligar_partes(percursos, areas, base, margem, avisos, passagem=_passagem):
    """Junta o percurso de cada pedaço do lago em UM caminho contínuo: sai de um pedaço e vai para o mais próximo
    pela água. Pedaço sem água ligando é avisado (e fica de fora) em vez de atravessar terra."""
    resto = [(p, a) for p, a in zip(percursos, areas) if p]
    if not resto: return []
    pts, pend = list(resto[0][0]), resto[1:]
    while pend:
        fim, melhor = pts[-1], None
        for i, (p, a) in enumerate(pend):
            for inv, d in ((False, math.dist(fim, p[0])), (True, math.dist(fim, p[-1]))):
                if melhor is None or d < melhor[0]: melhor = (d, i, inv)
        _, i, inv = melhor
        p, a = pend.pop(i)
        if inv: p = p[::-1]
        ponte = passagem(fim, p[0], base, margem, avisos)
        if ponte is None:
            avisos.append(f"Um pedaço do lago ({a.area:.0f} m²) NÃO tem água ligando ao resto nem pelos estreitos mais apertados. "
                          f"Ficou de fora desta rota: leve o barco até lá e use 'Parte do lago' para varrê-lo como outra missão.")
            continue
        pts += ponte[1:] + p[1:]
    return pts


def _varrer_parte(poly, espac, auto_angulo, avisos, reduzir=True):
    """Faixas paralelas em UM pedaço de água (metros). Devolve os pontos (x, y) já na direção real."""
    ang = _melhor_angulo(poly, espac) if auto_angulo else 0
    pr = rotate(poly, -ang, origin=(0, 0))
    pts = _faixas(pr, espac)
    pts = _com_desvios(pts, pr, avisos)
    pts = _enxugar(pts)
    livre_fn = (lambda area: (lambda p, q: area.covers(LineString([p, q]))))(prep(pr.buffer(0.1)))
    if reduzir:
        menos = reduzir_rota(pts, espac, livre_fn)                     # funde curvas em U e tira pontos inúteis
        if len(menos) < len(pts) and rota_segura(menos, pr): pts = menos   # só aceita se continuar 100% na água
    if not rota_segura(pts, pr):
        raise ValueError("A rota calculada cruzaria terra e foi descartada (nada foi enviado). Aumente a margem da parede ou corrija o contorno.")
    t = math.radians(ang); c, s = math.cos(t), math.sin(t)
    return [(x * c - y * s, x * s + y * c) for x, y in pts]


def gerar_varredura(poly_ll, espac=ESPACAMENTO_M, margem=MARGEM_M, auto_angulo=True, parte=0, avisos=None, ilhas_ll=(), reduzir=None):
    """Primeiro monta a rota com todas as curvas (faixas bem retas, mais pontos). Só se passar de LIMITE_SEGURO pontos
    é que funde as curvas em U para economizar pontos (reduzir=None = decide sozinho)."""
    if reduzir is None:
        av1 = []
        w = _gerar_varredura(poly_ll, espac, margem, auto_angulo, parte, av1, ilhas_ll, False)
        if len(w) <= LIMITE_SEGURO:
            (avisos if avisos is not None else []).extend(av1); return w
        reduzir = True
    return _gerar_varredura(poly_ll, espac, margem, auto_angulo, parte, avisos, ilhas_ll, reduzir)


def _gerar_varredura(poly_ll, espac, margem, auto_angulo, parte, avisos, ilhas_ll, reduzir):
    """Contorno (lat/lon) -> waypoints (lat, lon) cobrindo TODO o lago.
    - ilhas_ll: ilhas = zonas proibidas (a rota as contorna, com a margem de segurança);
    - parte=0: varre todos os pedaços de água (separados por estreitos, pontes ou ilhas) e liga um ao outro pela água;
      parte=N (>0): só o pedaço N (1 = o maior)."""
    avisos = avisos if avisos is not None else []
    lat0 = np.mean([p[0] for p in poly_ll]); lon0 = np.mean([p[1] for p in poly_ll])
    kx, ky = m_lon(lat0), M_LAT
    to_xy = lambda lat, lon: ((lon - lon0) * kx, (lat - lat0) * ky)
    to_ll = lambda x, y: (lat0 + y / ky, lon0 + x / kx)
    base = _base_metrica(poly_ll, ilhas_ll, to_xy)
    partes = _partes_de(base, margem)
    if parte and parte > 0: escolhidas = [partes[min(int(parte), len(partes)) - 1]]
    else: escolhidas = partes
    if len(partes) > 1:
        areas = ", ".join(f"{g.area:.0f} m²" for g in partes[:6])
        avisos.append(f"A margem de segurança separou o lago em {len(partes)} partes (áreas: {areas}). "
                      + ("A rota varre todas e passa de uma à outra pela água." if len(escolhidas) > 1
                         else f"Esta rota varre só a parte {parte}."))
    percursos = [_varrer_parte(p, espac, auto_angulo, avisos, reduzir) for p in escolhidas]
    pts = _ligar_partes(percursos, escolhidas, base, margem, avisos)
    falta = _falta_cobrir(pts, escolhidas, espac)
    if falta > 0.03 and ilhas_ll:                                            # buraco grande: tenta de novo só com as ilhas grandes
        grandes = [r for r in ilhas_ll if len(r) >= 3 and _area_ll_m2(r) >= 150.0]
        if len(grandes) < len(ilhas_ll):
            av2 = []
            try:
                w2 = _gerar_varredura(poly_ll, espac, margem, auto_angulo, parte, av2, grandes, reduzir)
                if w2 and len(w2) <= len(pts) * 3:
                    avisos[:] = av2 + [f"A rota com todas as ilhas deixava {falta*100:.0f}% do lago sem varrer; foram usadas só as ilhas "
                                       f"grandes (≥ 150 m²). As menores ficaram de fora da rota: confira o mapa."]
                    return w2
            except Exception:
                pass
    if falta > 0.03:
        avisos.append(f"Atenção: cerca de {falta*100:.0f}% da área navegável ficou sem faixa (estreitos, ilhas ou margem). Confira o mapa.")
    return [to_ll(x, y) for x, y in pts]


def _falta_cobrir(pts, areas, espac):
    """Fração da área varrível (em metros) que NÃO fica a menos de meia faixa de algum trecho da rota."""
    try:
        total = sum(a.area for a in areas)
        if total <= 0 or len(pts) < 2: return 0.0
        coberto = LineString(pts).buffer(max(espac, 0.5) * 0.75)
        return max(0.0, sum(a.difference(coberto).area for a in areas) / total)
    except Exception:
        return 0.0


# ---------- Rota "BORDA + MEIO" (inteligente): as algas se acumulam nas margens ----------
def ordenar_percurso(aneis, faixas, ligar):
    """Monta o percurso: dá as voltas na borda (da mais externa para a interna) e depois cruza o meio em faixas.
    aneis = lista de voltas (cada uma, lista de pontos sem repetir o primeiro) | faixas = pontos do zigue-zague do meio
    ligar(a, b) = caminho seguro (lista de pontos) de a até b. Cada volta começa no ponto mais perto de onde o barco está."""
    pts, pos = [], None
    for anel in aneis:
        if len(anel) < 3: continue
        i = 0 if pos is None else min(range(len(anel)), key=lambda j: math.dist(anel[j], pos))
        volta = anel[i:] + anel[:i]; volta = volta + [volta[0]]                  # fecha a volta
        pts += (ligar(pos, volta[0])[:-1] if pos is not None else []) + volta
        pos = volta[-1]
    if faixas:
        if pos is not None and math.dist(pos, faixas[0]) > math.dist(pos, faixas[-1]): faixas = faixas[::-1]
        pts += (ligar(pos, faixas[0])[:-1] if pos is not None else []) + list(faixas)
    return pts


def gerar_borda_e_miolo(poly_ll, margem=MARGEM_M, voltas=2, passo_volta=2.0, espac_meio=10.0, usar_meio=True,
                        parte=0, avisos=None, ilhas_ll=(), reduzir=None):
    """Monta primeiro SEM fundir curvas (faixas do meio bem retas); só funde se passar de LIMITE_SEGURO pontos."""
    if reduzir is None:
        av1 = []
        w, info = _borda_e_miolo(poly_ll, margem, voltas, passo_volta, espac_meio, usar_meio, parte, av1, ilhas_ll, False)
        if len(w) <= LIMITE_SEGURO:
            (avisos if avisos is not None else []).extend(av1); return w, info
        reduzir = True
    return _borda_e_miolo(poly_ll, margem, voltas, passo_volta, espac_meio, usar_meio, parte, avisos, ilhas_ll, reduzir)


def _borda_e_miolo(poly_ll, margem, voltas, passo_volta, espac_meio, usar_meio, parte, avisos, ilhas_ll, reduzir):
    """Rota que gasta menos bateria e tempo: dá 'voltas' na borda do lago e em volta de cada ilha (onde as algas se
    acumulam) e, se usar_meio, cruza o meio em faixas bem espaçadas (espac_meio metros). Todas as partes do lago entram
    (parte=0). Devolve (waypoints [(lat, lon)], info)."""
    avisos = avisos if avisos is not None else []
    lat0 = np.mean([p[0] for p in poly_ll]); lon0 = np.mean([p[1] for p in poly_ll])
    kx, ky = m_lon(lat0), M_LAT
    to_xy = lambda lat, lon: ((lon - lon0) * kx, (lat - lat0) * ky)
    to_ll = lambda x, y: (lat0 + y / ky, lon0 + x / kx)
    base = _base_metrica(poly_ll, ilhas_ll, to_xy)
    partes = _partes_de(base, margem)
    escolhidas = [partes[min(int(parte), len(partes)) - 1]] if parte and parte > 0 else partes
    if len(partes) > 1:
        avisos.append(f"A margem de segurança separou o lago em {len(partes)} partes. "
                      + ("A rota passa por todas, ligadas pela água." if len(escolhidas) > 1 else f"Esta rota usa só a parte {parte}."))
    seguro = prep(base.buffer(-max(margem * 0.5, 0.5) + 0.3))                     # nunca mais perto da margem que ~metade dela
    percursos, perimetro, n_aneis, n_faixas_tot = [], 0.0, 0, 0
    for area in escolhidas:
        perimetro += area.length
        aneis = []
        for k in range(max(1, int(voltas))):
            g = area if k == 0 else area.buffer(-k * passo_volta)
            peds = [p for p in getattr(g, "geoms", [g]) if p.geom_type == "Polygon" and p.area > 1.0]
            if not peds:
                avisos.append(f"Um pedaço do lago é estreito: só coube(ram) {k} volta(s) com {passo_volta:g} m entre elas."); break
            peds.sort(key=lambda q: (round(q.bounds[1] / 20), q.bounds[0]))      # pedaços vizinhos seguidos
            for p in peds:                                                        # TODOS os pedaços ganham volta (antes só o maior)
                p = p.simplify(0.6)                                               # DP: sem zigue-zague na margem irregular
                if p.is_empty or p.geom_type != "Polygon": continue
                aneis.append(list(p.exterior.coords)[:-1])
                aneis += [list(r.coords)[:-1] for r in getattr(p, "interiors", [])]  # voltas em torno das ilhas
        n_aneis = max(n_aneis, len(aneis))
        faixas = []
        if usar_meio and espac_meio > 0:
            interno = area.buffer(-((max(1, int(voltas)) - 1) * passo_volta + espac_meio / 2))
            peds = [p for p in getattr(interno, "geoms", [interno]) if p.geom_type == "Polygon" and p.area > 1.0]
            if not peds: avisos.append("Num pedaço do lago não sobrou espaço no meio para faixas; lá a rota é só a borda.")
            else:
                pedacos_f, pos_f = [], None
                for miolo in sorted(peds, key=lambda q: -q.area):                    # TODOS os pedaços do meio (antes só o maior)
                    ang = _melhor_angulo(miolo, espac_meio)
                    pr = rotate(miolo, -ang, origin=(0, 0))
                    t = math.radians(ang); c, sn = math.cos(t), math.sin(t)
                    livre_m = (lambda a_: (lambda p, q: a_.covers(LineString([p, q]))))(prep(pr.buffer(0.1)))
                    f = _enxugar(_com_desvios(_faixas(pr, espac_meio), pr, avisos))
                    if len(f) < 2: continue
                    n_faixas_tot += len(f) // 2                                      # (antes de fundir as curvas em U)
                    f = reduzir_rota(f, espac_meio, livre_m) if (reduzir and len(f) > 3) else f
                    pedacos_f.append([(x * c - y * sn, x * sn + y * c) for x, y in f])
                while pedacos_f:                                                     # encadeia os pedaços do meio, o mais perto primeiro
                    if pos_f is None: nxt = pedacos_f.pop(0)
                    else:
                        i = min(range(len(pedacos_f)), key=lambda j: min(math.dist(pos_f, pedacos_f[j][0]), math.dist(pos_f, pedacos_f[j][-1])))
                        nxt = pedacos_f.pop(i)
                        if math.dist(pos_f, nxt[-1]) < math.dist(pos_f, nxt[0]): nxt = nxt[::-1]
                        faixas += _com_desvios([pos_f, nxt[0]], area, avisos)[1:-1]
                    faixas += nxt; pos_f = nxt[-1]
        ligar = lambda a, b, _ar=area: _com_desvios([a, b], _ar, avisos)
        pts = ordenar_percurso(aneis, faixas, ligar)
        if not all(seguro.covers(LineString([p, q])) for p, q in zip(pts[:-1], pts[1:]) if math.dist(p, q) > 1e-6):
            raise ValueError("A rota 'borda + meio' encostaria na margem e foi descartada. Aumente a margem da parede.")
        percursos.append(pts)
    pts = _ligar_partes(percursos, escolhidas, base, margem, avisos)
    comp = sum(math.dist(p, q) for p, q in zip(pts[:-1], pts[1:]))
    cheia = sum(a.area for a in escolhidas) / ESPACAMENTO_M                       # percurso estimado da varredura completa
    info = dict(perimetro_m=perimetro, voltas=n_aneis, faixas_meio=n_faixas_tot,
                comprimento_m=comp, economia_pct=max(0.0, (1 - comp / cheia) * 100) if cheia > 0 else 0.0)
    return [to_ll(x, y) for x, y in pts], info


def estimar_missao(wps, vel_ms=0.4, s_por_curva=4.0):
    """Estimativa do tempo da missão ANTES de enviar: percurso / velocidade + um tempinho em cada curva.
    (Não inclui paradas de re-teste, limpeza do sensor nem a varredura densa.)"""
    comp = comprimento_rota_m(wps)
    curvas = 0
    if len(wps) >= 3:
        lat0 = float(np.mean([w[0] for w in wps])); kx = m_lon(lat0)
        v = [((b[1] - a[1]) * kx, (b[0] - a[0]) * M_LAT) for a, b in zip(wps[:-1], wps[1:])]
        for (x1, y1), (x2, y2) in zip(v[:-1], v[1:]):
            n1, n2 = math.hypot(x1, y1), math.hypot(x2, y2)
            if n1 > 1e-6 and n2 > 1e-6 and (x1 * x2 + y1 * y2) / (n1 * n2) < math.cos(math.radians(30)): curvas += 1
    t = comp / max(vel_ms, 0.05) + curvas * s_por_curva
    return dict(comprimento_m=comp, tempo_s=t, curvas=curvas)


def estatisticas_missao(wps, vel_ms=0.4, info_rota=None, area_lago_m2=None, potencia_w=0.0, largura_m=None):
    """Painel de estatísticas da missão (calculado antes de enviar ao robô).
    - area_varrida_m2: área REAL coberta pela faixa do barco (largura x trajeto, sem contar duas vezes onde a rota se sobrepõe);
    - cobertura_pct: quanto do lago (area_lago_m2) isso representa;
    - tempo_s / curvas: estimativa do tempo (percurso / velocidade das rodas de pá + tempo por curva);
    - economia_pct: quanto de percurso (e, portanto, de tempo e energia, supondo potência média constante) a rota inteligente
      poupa em relação a varrer tudo com o espaçamento padrão. 0 na varredura completa;
    - energia_wh: só se você informar a potência média (W); senão None (o programa não inventa um consumo)."""
    largura_m = largura_m or LARGURA_ROBO_M
    est = estimar_missao(wps, vel_ms)
    area = 0.0
    if len(wps) >= 2:
        try:
            lat0 = float(np.mean([w[0] for w in wps])); lon0 = float(np.mean([w[1] for w in wps]))
            kx = m_lon(lat0)
            xy = [((lo - lon0) * kx, (la - lat0) * M_LAT) for la, lo in wps]
            area = float(LineString(xy).buffer(largura_m / 2, cap_style=2, join_style=2).area)
        except Exception:
            area = est["comprimento_m"] * largura_m                  # plano B: sem descontar sobreposição
    economia = float((info_rota or {}).get("economia_pct", 0.0) or 0.0)
    energia = (potencia_w * est["tempo_s"] / 3600.0) if potencia_w and potencia_w > 0 else None
    return dict(area_varrida_m2=area,
                cobertura_pct=(min(100.0, area / area_lago_m2 * 100) if area_lago_m2 else None),
                comprimento_m=est["comprimento_m"], tempo_s=est["tempo_s"], curvas=est["curvas"],
                economia_pct=economia, energia_wh=energia)


def formatar_duracao(seg):
    seg = int(round(seg)); h, r = divmod(seg, 3600); m = r // 60
    return f"{h} h {m:02d} min" if h else f"{m} min"


def rota_manual(poly_ll, pontos_ll, margem=MARGEM_M, avisos=None, ilhas_ll=()):
    """Converte os pontos clicados em waypoints VÁLIDOS: cada ponto é puxado para dentro da água segura (respeitando
    a margem), os trechos contornam terra e ilhas, e pontos em partes diferentes do lago são ligados pela água."""
    avisos = avisos if avisos is not None else []
    lat0 = np.mean([p[0] for p in poly_ll]); lon0 = np.mean([p[1] for p in poly_ll])
    kx, ky = m_lon(lat0), M_LAT
    to_xy = lambda lat, lon: ((lon - lon0) * kx, (lat - lat0) * ky)
    to_ll = lambda x, y: (lat0 + y / ky, lon0 + x / kx)
    base = _base_metrica(poly_ll, ilhas_ll, to_xy)
    partes = _partes_de(base, margem)
    prontas = [prep(g.buffer(0.1)) for g in partes]
    xy = []
    for i, (la, lo) in enumerate(pontos_ll, 1):
        p = Point(to_xy(la, lo))
        k = next((j for j, pr in enumerate(prontas) if pr.covers(p)), None)
        if k is None:
            k = min(range(len(partes)), key=lambda j: partes[j].distance(p))
            q = nearest_points(partes[k], p)[0]                       # ponto mais próximo dentro da água segura
            avisos.append(f"O ponto {i} estava fora da água segura e foi movido {p.distance(q):.1f} m para dentro.")
            p = q
        xy.append(((p.x, p.y), k))
    if len(xy) < 2: raise ValueError("Marque pelo menos 2 pontos para a rota.")
    pts, i = [], 0
    while i < len(xy):
        j = i
        while j + 1 < len(xy) and xy[j + 1][1] == xy[i][1]: j += 1
        grupo = [p for p, _ in xy[i:j + 1]]
        seg = _enxugar(_com_desvios(grupo, partes[xy[i][1]], avisos)) if len(grupo) > 1 else grupo
        if pts:
            ponte = _passagem(pts[-1], seg[0], base, margem, avisos)
            if ponte is None: raise ValueError("Não há água ligando dois pontos que você marcou (estão em partes separadas do lago).")
            pts += ponte[1:]
            pts += seg[1:] if math.dist(pts[-1], seg[0]) < 1e-6 else seg
        else: pts = list(seg)
        i = j + 1
    if not rota_segura_base(pts, base): raise ValueError("A rota desenhada cruzaria terra ou uma ilha e foi descartada.")
    return [to_ll(x, y) for x, y in pts]


def rota_segura_base(pts, base, tol=0.05):
    pb = prep(base.buffer(tol))
    return all(pb.covers(LineString([p, q])) for p, q in zip(pts[:-1], pts[1:]) if math.dist(p, q) > 1e-6)


def comprimento_rota_m(wps):
    if len(wps) < 2: return 0.0
    lat0 = float(np.mean([w[0] for w in wps]))
    kx = m_lon(lat0)
    return sum(math.hypot((b[1] - a[1]) * kx, (b[0] - a[0]) * M_LAT) for a, b in zip(wps[:-1], wps[1:]))
