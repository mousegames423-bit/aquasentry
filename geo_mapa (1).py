"""geo_mapa.py - Imagem, contorno do lago e desenho do mapa.

Realce da imagem, conversão lat/lon <-> pixel, contorno híbrido (OSM + cor), completar/limpar contorno, ilhas,
edição de polígonos (shapely), download do satélite, renderização do mapa, relatório e persistência do mapa.
"""

import csv
import hashlib
import io
import json
import math
import os
import time
import urllib.parse

import contourpy
from PIL import Image, ImageDraw, ImageEnhance, ImageOps
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.figure import Figure
from scipy import ndimage
from scipy.interpolate import griddata
from shapely.geometry import Polygon
from shapely.ops import unary_union
import numpy as np
import streamlit as st

from database import CREDITOS, PASTA, TILES_DIR, hardware_id

CELULA_M = 10.0         # célula para ranquear focos no relatório

MAX_VERTICES = 200      # cerca virtual enviada ao robô (= MAX_V do firmware)

VERTICES_ROTA = 1500    # contorno usado para CALCULAR a rota (bem mais fiel)

USER_AGENT = "BioGlow-FLL/1.0 (projeto escolar; contato: SEU_EMAIL@exemplo.com)"   # troque pelo seu e-mail!

TOL_PADRAO = 45         # sensibilidade inicial da detecção da água por cor


# --- Realce automático da imagem (1.0 = sem mudança) ---
REALCE_PADRAO = dict(ativo=True, auto=1, brilho=1.10, contraste=1.25, cor=1.60, nitidez=1.40)

# ------------------------------------------------------------------------

M_LAT = 110540.0                                                   # metros por grau de latitude

def m_lon(lat0): return 111320.0 * math.cos(math.radians(lat0))   # metros por grau de longitude


# =====================================================================
#   PARTE B - IMAGEM, CONTORNO E ROTA (lógica da Central v5, sem variáveis globais)
#   bbox = (oeste, leste, sul, norte) da imagem, em graus
# =====================================================================
def realcar_imagem(img, p=None):
    """Cores fortes: estica o histograma e aumenta brilho, contraste, cor e nitidez."""
    p = p or REALCE_PADRAO
    img = img.convert("RGB")
    if not p["ativo"]: return img
    if p["auto"] > 0: img = ImageOps.autocontrast(img, cutoff=p["auto"])
    img = ImageEnhance.Brightness(img).enhance(p["brilho"])
    img = ImageEnhance.Contrast(img).enhance(p["contraste"])
    img = ImageEnhance.Color(img).enhance(p["cor"])
    img = ImageEnhance.Sharpness(img).enhance(p["nitidez"])
    return img


def lonlat_para_pixel(lon, lat, w, h, bbox):
    o, l, s, n = bbox
    return (lon - o) / (l - o) * (w - 1), (n - lat) / (n - s) * (h - 1)      # linha 0 = topo


def pixel_para_lonlat(col, lin, w, h, bbox):
    o, l, s, n = bbox
    return o + col / (w - 1) * (l - o), n - lin / (h - 1) * (n - s)


# Ramer-Douglas-Peucker: remove pontos desnecessários de uma linha mantendo a forma (P em metros)
def _rdp(P, tol):
    n = len(P)
    keep = np.zeros(n, bool); keep[0] = keep[-1] = True
    pilha = [(0, n - 1)]
    while pilha:
        i, j = pilha.pop()
        if j <= i + 1: continue
        a, b = P[i], P[j]
        ab = b - a
        L = np.hypot(ab[0], ab[1])
        seg = P[i + 1:j]
        if L == 0: d = np.hypot(seg[:, 0] - a[0], seg[:, 1] - a[1])
        else: d = np.abs(ab[0] * (seg[:, 1] - a[1]) - ab[1] * (seg[:, 0] - a[0])) / L
        k = int(np.argmax(d))
        if d[k] > tol:
            m = i + 1 + k
            keep[m] = True
            pilha += [(i, m), (m, j)]
    return np.nonzero(keep)[0]


def simplificar(poly_ll, max_pts=MAX_VERTICES, tol=0.5):
    """Reduz um contorno fechado [(lat, lon), ...] para no máximo max_pts vértices."""
    pts = np.array(poly_ll, float)
    if len(pts) > 1 and np.allclose(pts[0], pts[-1]): pts = pts[:-1]
    lat0 = pts[:, 0].mean()
    P = np.c_[pts[:, 1] * m_lon(lat0), pts[:, 0] * M_LAT]
    n = len(P)
    if n <= 3: return [tuple(p) for p in pts]
    j = int(np.argmax(np.hypot(P[:, 0] - P[0, 0], P[:, 1] - P[0, 1])))
    while True:
        k1 = _rdp(P[:j + 1], tol)
        k2 = _rdp(np.vstack([P[j:], P[:1]]), tol)
        idx = sorted(set(list(k1) + [j + t for t in k2 if j + t < n]))
        if len(idx) <= max_pts or tol > 500: break
        tol *= 1.4
    return [tuple(pts[i]) for i in idx]


def contorno_automatico(img_arr, lon, lat, tol, bbox):
    """Clique na água -> acha a margem pela cor. Devolve [(lat, lon), ...] ou None."""
    h, w = img_arr.shape[:2]
    c, l = lonlat_para_pixel(lon, lat, w, h, bbox)
    c, l = int(round(c)), int(round(l))
    if not (0 <= c < w and 0 <= l < h): return None
    rgb = img_arr[..., :3].astype(float)
    r = 3
    semente = rgb[max(0, l - r):l + r + 1, max(0, c - r):c + r + 1].reshape(-1, 3).mean(axis=0)
    dist = np.sqrt(((rgb - semente) ** 2).sum(axis=2))
    mask = dist < tol
    mask = ndimage.binary_opening(mask, iterations=2)
    mask = ndimage.binary_closing(mask, iterations=3)
    rotulos, _ = ndimage.label(mask)
    if rotulos[l, c] == 0: return None
    mask = ndimage.binary_fill_holes(rotulos == rotulos[l, c])
    linhas = contourpy.contour_generator(z=np.pad(mask.astype(float), 1)).lines(0.5)
    if not linhas: return None
    maior = max(linhas, key=len)
    cols, lins = maior[:, 0] - 1, maior[:, 1] - 1
    lons, lats = pixel_para_lonlat(cols, lins, w, h, bbox)
    return simplificar(list(zip(lats, lons)), VERTICES_ROTA, 0.3)


# ---------- Contorno HÍBRIDO: contorno do OpenStreetMap (ou clique) + máscara de cor da água ----------
# Ideia: o OSM diz ONDE está o lago (mas é "desenhado à mão" e erra a margem); a cor diz ONDE REALMENTE há água.
#  - o contorno final é feito só de pixels de água (nada de "parede esticada" sobre a terra);
#  - a máscara de cor só pode passar do OSM por EXPANSAO_MAX_M metros (limite de expansão);
#  - passagens estreitas entre partes do lago são fechadas (PONTE_M), mas só onde há água de verdade.
EXPANSAO_MAX_M = 6.0

PONTE_M = 4.0


def _disco_dist(X, r):
    """Pixels a até r pixels de X (dilatação circular rápida, via transformada de distância)."""
    return ndimage.distance_transform_edt(~X) <= r


def _fechamento(X, r):
    """Fecha frestas de até ~2r pixels (dilata e depois erode). A borda da imagem não é erodida."""
    D = np.pad(_disco_dist(X, r), 1, constant_values=True)
    return (ndimage.distance_transform_edt(D) > r)[1:-1, 1:-1]


def _rasterizar_anel(anel_ll, w, h, bbox):
    pts = [lonlat_para_pixel(lo, la, w, h, bbox) for la, lo in anel_ll]
    im = Image.new("L", (w, h), 0)
    ImageDraw.Draw(im).polygon(pts, fill=1)
    return np.array(im, bool)


def contorno_hibrido(img_arr, bbox, anel_ll=None, semente=None, tol=TOL_PADRAO,
                     expansao_max_m=EXPANSAO_MAX_M, ponte_m=PONTE_M, manter_base=False):
    """Devolve (contorno [(lat, lon), ...] ou None, [notas para mostrar ao usuário]).
    anel_ll = contorno do OSM | semente = (lon, lat) clicado na água (usado se não há anel)."""
    notas = []
    h, w = img_arr.shape[:2]
    o, l, s, n = bbox
    lat_m = (s + n) / 2
    mpx = min((l - o) * m_lon(lat_m) / (w - 1), (n - s) * M_LAT / (h - 1))      # metros por pixel
    rgb = img_arr[..., :3].astype(float)
    base = _rasterizar_anel(anel_ll, w, h, bbox) if anel_ll else None
    if base is not None and base.sum() < 50: base = None
    sem_col = sem_lin = None
    if base is not None:
        miolo = ndimage.binary_erosion(base, iterations=max(1, int(2 / mpx)))        # só o miolo: longe da margem duvidosa
        if miolo.sum() < 20: miolo = base
        cor = np.median(rgb[miolo], axis=0)
    elif semente is not None:
        c, li = lonlat_para_pixel(semente[0], semente[1], w, h, bbox)
        sem_col, sem_lin = int(round(c)), int(round(li))
        if not (0 <= sem_col < w and 0 <= sem_lin < h): return None, notas
        cor = rgb[max(0, sem_lin - 3):sem_lin + 4, max(0, sem_col - 3):sem_col + 4].reshape(-1, 3).mean(axis=0)
    else:
        return None, notas
    dist = np.sqrt(((rgb - cor) ** 2).sum(axis=2))
    estrito = ndimage.binary_closing(ndimage.binary_opening(dist < tol, iterations=2), iterations=3)
    relaxado = dist < tol * 1.6                       # "talvez água" (sombra, reflexo): só vale para fechar passagens
    if base is not None:
        permitido = _disco_dist(base, max(1, int(round(expansao_max_m / mpx))))     # LIMITE MÁXIMO de expansão
        estrito &= permitido; relaxado &= permitido
        if estrito[base].mean() < 0.5:                # a cor não descreve bem o lago: confia no OSM, mas recortado
            notas.append("A cor da água variou muito neste lago; usei o contorno do OpenStreetMap. "
                         "Use adicionar/remover por cor para acertar a margem.")
            final = base.copy()
        else:
            final = estrito
    else:
        final = estrito
    if manter_base and base is not None:
        final = final | base                          # REFINAR: o contorno de partida nunca perde área (ponte, sombra...); a cor só ACRESCENTA
    if ponte_m > 0:                                   # une as seções do lago pelas passagens estreitas de água
        ponte = max(1, int(round(ponte_m / mpx)))
        final = final | (_fechamento(final, ponte) & relaxado)
    rot, _ = ndimage.label(final)
    if base is not None: ids = [i for i in np.unique(rot[base & final]) if i > 0]
    else: ids = [rot[sem_lin, sem_col]] if rot[sem_lin, sem_col] > 0 else []
    if not ids: return None, notas
    areas = {int(i): int((rot == i).sum()) for i in ids}
    maior_id = max(areas, key=areas.get)
    mask = ndimage.binary_fill_holes(rot == maior_id)
    separadas = [i for i, a in areas.items() if i != maior_id and a >= 0.02 * areas[maior_id]]
    if separadas:
        notas.append(f"Há mais {len(separadas)} parte(s) do lago SEM ligação por água na imagem (ficou só a maior). "
                     "Para incluí-la, use a ferramenta Adicionar água por cor clicando nela.")
    linhas = contourpy.contour_generator(z=np.pad(mask.astype(float), 1)).lines(0.5)
    if not linhas: return None, notas
    ring = max(linhas, key=len)
    lons, lats = pixel_para_lonlat(ring[:, 0] - 1, ring[:, 1] - 1, w, h, bbox)
    return simplificar(list(zip(lats, lons)), VERTICES_ROTA, 0.3), notas


def _mascara_para_poly(mask, w, h, bbox):
    linhas = contourpy.contour_generator(z=np.pad(mask.astype(float), 1)).lines(0.5)
    if not linhas: return None
    ring = max(linhas, key=len)
    lons, lats = pixel_para_lonlat(ring[:, 0] - 1, ring[:, 1] - 1, w, h, bbox)
    return simplificar(list(zip(lats, lons)), VERTICES_ROTA, 0.3)


def _textura(rgb, mpx, janela_m=3.0):
    """'Rugosidade' local da imagem (desvio padrão do brilho numa janela ~3 m). Água é lisa; floresta, telhado e rua são rugosos."""
    tam = int(min(15, max(3, round(janela_m / mpx)))) | 1
    lum = rgb @ np.array([0.299, 0.587, 0.114])
    m = ndimage.uniform_filter(lum, tam); m2 = ndimage.uniform_filter(lum * lum, tam)
    return np.sqrt(np.maximum(m2 - m * m, 0.0))


def _limiar_textura(tex, miolo):
    """Até que rugosidade ainda é água: 3x a mediana da água do próprio lago (com piso)."""
    return max(3.0 * float(np.median(tex[miolo])), 4.0)


def _abertura(X, r):
    """Mantém só as partes de X com largura maior que ~2r pixels (some o que é fino, como pontes e trilhas)."""
    E = ndimage.distance_transform_edt(np.pad(X, 1)) > r
    return (ndimage.distance_transform_edt(~E) <= r)[1:-1, 1:-1] & X


def limpar_contorno(img_arr, bbox, poly_ll, tol=TOL_PADRAO, largura_min_m=14.0):
    """O contrário de completar: olha DENTRO do contorno e tira o que claramente não é água (floresta, gramado, rua larga),
    pela cor E pela rugosidade. Só sai o que for largo (> largura_min_m): pontes e trilhas estreitas ficam.
    Devolve (contorno ou None, info com 'removido_m2' e 'removido' = lista de contornos do que saiu)."""
    h, w = img_arr.shape[:2]
    o, l, s, n = bbox
    lat_m = (s + n) / 2
    mx, my = (l - o) * m_lon(lat_m) / (w - 1), (n - s) * M_LAT / (h - 1)
    mpx = min(mx, my)
    base = _rasterizar_anel(poly_ll, w, h, bbox)
    if base.sum() < 50: return None, dict(motivo="Contorno pequeno demais.")
    rgb = img_arr[..., :3].astype(float)
    miolo = ndimage.binary_erosion(base, iterations=max(1, int(2 / mpx)))
    if miolo.sum() < 20: miolo = base
    cor = np.median(rgb[miolo], axis=0)
    tex = _textura(rgb, mpx)
    agua = (np.sqrt(((rgb - cor) ** 2).sum(axis=2)) < tol * 1.25) & (tex <= _limiar_textura(tex, miolo))
    agua = ndimage.binary_closing(agua, iterations=2)
    nao = base & ~agua
    tirar = _abertura(nao, max(1, int(round(largura_min_m / 2 / mpx))))
    area_px = mx * my
    rem_m2, base_m2 = float(tirar.sum() * area_px), float(base.sum() * area_px)
    if rem_m2 < 0.02 * base_m2: return None, dict(removido_m2=rem_m2, motivo="Não achei nada largo que não seja água dentro do contorno.")
    if rem_m2 > 0.6 * base_m2:
        return None, dict(removido_m2=rem_m2, motivo="Quase tudo parece 'não água' pela cor; não removi nada. Ajuste a sensibilidade.")
    final = base & ~tirar
    rot, _ = ndimage.label(final)
    if rot.max() == 0: return None, dict(motivo="Não sobrou água depois da limpeza.")
    manter = np.argmax(np.bincount(rot.ravel())[1:]) + 1                       # maior pedaço de água
    final = rot == manter
    poly = _mascara_para_poly(final, w, h, bbox)
    if poly is None: return None, dict(motivo="Não consegui traçar o contorno limpo.")
    removido = []
    for ring in contourpy.contour_generator(z=np.pad(tirar.astype(float), 1)).lines(0.5):
        if len(ring) < 12: continue
        lons, lats = pixel_para_lonlat(ring[::3, 0] - 1, ring[::3, 1] - 1, w, h, bbox)
        removido.append(list(zip(lats, lons)))
    ilhas = []                                                                  # não-água CERCADA de água = ilha (zona proibida)
    buracos = ndimage.binary_fill_holes(final) & ~final
    for ring in contourpy.contour_generator(z=np.pad(buracos.astype(float), 1)).lines(0.5):
        if len(ring) < 8: continue
        lons, lats = pixel_para_lonlat(ring[::2, 0] - 1, ring[::2, 1] - 1, w, h, bbox)
        anel_i = list(zip(lats, lons))
        if _area_ll_m2(anel_i) >= ILHA_MIN_M2: ilhas.append(anel_i)               # ruído pequeno não vira ilha
    return poly, dict(removido_m2=rem_m2, removido=removido, ilhas=ilhas)


def completar_contorno(img_arr, bbox, base_ll, tol=TOL_PADRAO, ponte_m=6.0, max_razao=10.0):
    """O contorno do site é o PONTO DE PARTIDA e nunca perde área. O programa então procura, na imagem, água que o mapa
    não tinha (ex.: um pedaço grande do lago) e ACRESCENTA, desde que ela seja ligada ao lago (inclusive por baixo de
    pontes de até ~2*ponte_m metros). Devolve (contorno ou None, info).
    Segurança: só vale água da MESMA cor da água do lago; se o acréscimo for maior que max_razao vezes o lago do site
    (provável vazamento para rio/campo), NÃO aplica e devolve só como 'sugestao'."""
    h, w = img_arr.shape[:2]
    o, l, s, n = bbox
    lat_m = (s + n) / 2
    mx, my = (l - o) * m_lon(lat_m) / (w - 1), (n - s) * M_LAT / (h - 1)
    base = _rasterizar_anel(base_ll, w, h, bbox)
    if base.sum() < 50: return None, dict(aplicado=False, motivo="Contorno base pequeno demais para completar.")
    rgb = img_arr[..., :3].astype(float)
    miolo = ndimage.binary_erosion(base, iterations=max(1, int(2 / min(mx, my))))
    if miolo.sum() < 20: miolo = base
    cor = np.median(rgb[miolo], axis=0)
    dist = np.sqrt(((rgb - cor) ** 2).sum(axis=2))
    tex = _textura(rgb, min(mx, my))                   # floresta escura tem a COR da água escura, mas é rugosa: não vale como água
    agua = (dist < tol) & (tex <= _limiar_textura(tex, miolo))
    estrito = ndimage.binary_closing(ndimage.binary_opening(agua, iterations=2), iterations=3)
    if estrito[base].mean() < 0.4:
        return None, dict(aplicado=False, motivo="A cor/textura da água dentro do contorno varia muito; não deu para completar pela imagem. "
                                                 "Tente aumentar a sensibilidade ou use Adicionar água por cor.")
    cand = estrito | base                              # o lago do site entra INTEIRO (sob pontes, sombras...)
    rot, _ = ndimage.label(cand)
    novo = _fechamento(cand, max(1, int(round(ponte_m / min(mx, my))))) & ~cand
    novo_rot, nn = ndimage.label(novo)
    if nn:                                             # vãos estreitos (pontes) SÓ se ligam duas águas diferentes
        for k, sl in enumerate(ndimage.find_objects(novo_rot), 1):
            if sl is None: continue
            sl2 = tuple(slice(max(0, t.start - 3), t.stop + 3) for t in sl)
            sub = novo_rot[sl2] == k
            viz = ndimage.binary_dilation(sub, iterations=2) & (rot[sl2] > 0)
            if len(np.unique(rot[sl2][viz])) >= 2: cand[sl2] |= sub
    rot, _ = ndimage.label(cand)
    ids = [i for i in np.unique(rot[base]) if i > 0]
    comp = ndimage.binary_fill_holes(np.isin(rot, ids))
    add = comp & ~base
    area_px = mx * my
    add_m2, base_m2 = float(add.sum() * area_px), float(base.sum() * area_px)
    if add_m2 < 0.02 * base_m2:
        return None, dict(aplicado=False, adicionado_m2=add_m2, motivo="O mapa já cobre toda a água que a imagem mostra.")
    borda = bool(add[0].any() or add[-1].any() or add[:, 0].any() or add[:, -1].any())
    razao = add_m2 / base_m2
    poly = _mascara_para_poly(comp, w, h, bbox)
    info = dict(adicionado_m2=add_m2, razao=razao, borda=borda)
    if poly is None: return None, dict(info, aplicado=False, motivo="Não consegui traçar o contorno completado.")
    if razao > max_razao:
        return None, dict(info, aplicado=False, sugestao=poly,
                          motivo=f"Achei água com {razao:.0f}x o tamanho do lago do mapa ligada a ele; parece vazamento (rio, campo) e NÃO apliquei.")
    return poly, dict(info, aplicado=True)


def refinar_area(img_arr, bbox, poly_ll, regiao_ll, tol=TOL_PADRAO):
    """Você circula uma área; o programa olha SÓ ela na imagem e cola a margem na água de verdade:
    dentro do círculo, o contorno passa a seguir a água que a imagem mostra (acrescenta o que faltava e tira terra que
    estava dentro). Fora do círculo nada muda. Devolve (contorno ou None, info)."""
    h, w = img_arr.shape[:2]
    o, l, s_, n = bbox
    lat_m = (s_ + n) / 2
    mx, my = (l - o) * m_lon(lat_m) / (w - 1), (n - s_) * M_LAT / (h - 1)
    mpx = min(mx, my); area_px = mx * my
    base = _rasterizar_anel(poly_ll, w, h, bbox)
    R = _rasterizar_anel(regiao_ll, w, h, bbox)
    if R.sum() * area_px < 10: return None, dict(motivo="A área circulada ficou pequena demais.")
    if base.sum() < 50: return None, dict(motivo="Contorno pequeno demais.")
    rgb = img_arr[..., :3].astype(float)
    miolo = ndimage.binary_erosion(base & ~R, iterations=max(1, int(2 / mpx)))      # cor da água medida FORA do círculo
    if miolo.sum() < 20: miolo = ndimage.binary_erosion(base, iterations=max(1, int(2 / mpx)))
    if miolo.sum() < 20: miolo = base
    cor = np.median(rgb[miolo], axis=0)
    tex = _textura(rgb, mpx)
    agua = (np.sqrt(((rgb - cor) ** 2).sum(axis=2)) < tol * 1.15) & (tex <= _limiar_textura(tex, miolo))
    r = max(1, int(round(1.0 / mpx)))
    agua = ndimage.binary_closing(_abertura(agua, r), iterations=2)                    # tira ruído, junta reflexos
    dentro = agua & R
    if dentro.sum() * area_px < 0.08 * R.sum() * area_px and dentro.sum() * area_px < 20:
        return None, dict(motivo="Não achei água (da cor do lago) dentro da área circulada. Circule uma área que tenha água visível, "
                                 "ou aumente a sensibilidade.")
    novo = (base & ~R) | dentro
    novo = ndimage.binary_fill_holes(novo) if False else novo
    rot, nr = ndimage.label(novo)
    if nr == 0: return None, dict(motivo="Não sobrou água depois do ajuste.")
    manter = np.argmax(np.bincount(rot.ravel())[1:]) + 1                               # o pedaço principal
    novo = rot == manter
    add_m2 = float((novo & ~base).sum() * area_px); rem_m2 = float((base & ~novo).sum() * area_px)
    if add_m2 < 2 and rem_m2 < 2: return None, dict(motivo="A margem já acompanha a água nessa área; nada a ajustar.")
    poly = _mascara_para_poly(novo, w, h, bbox)
    if poly is None: return None, dict(motivo="Não consegui traçar o contorno ajustado.")
    desconexo = float((dentro & ~novo).sum() * area_px)
    return poly, dict(adicionado_m2=add_m2, removido_m2=rem_m2, desconexo_m2=desconexo)


ILHA_MIN_M2 = 40.0           # menor ilha aceita (m², ~6 x 6 m). Menos que isso é tratado como ruído e ignorado.

ILHA_MAX_FRACAO = 0.35       # se as "ilhas" somarem mais que isso do lago, a detecção está errada: nada é aplicado


def detectar_ilhas(img_arr, bbox, poly_ll, ilhas_ll=(), tol=TOL_PADRAO, min_m2=ILHA_MIN_M2, largura_min_m=3.0):
    """Acha TERRA FIRME claramente visível, isolada, dentro do lago (ilhas e bancos de terra).
    Método em duas etapas (histerese): o 'núcleo' precisa ser bem diferente da água (cor muito diferente OU muito rugoso);
    a ilha então cresce até onde a terra continua (cor diferente E rugosa). Sem núcleo forte = ruído, descartado.
    Descarta: área < min_m2, encostada na margem, anel de margem (cerca água dentro), e tudo se somar demais do lago.
    Devolve (lista de contornos [(lat, lon)], info)."""
    h, w = img_arr.shape[:2]
    o, l, s_, n = bbox
    lat_m = (s_ + n) / 2
    mx, my = (l - o) * m_lon(lat_m) / (w - 1), (n - s_) * M_LAT / (h - 1)
    mpx = min(mx, my); area_px = mx * my
    base = _rasterizar_anel(poly_ll, w, h, bbox)
    if base.sum() < 50: return [], dict(motivo="Contorno pequeno demais.")
    rgb = img_arr[..., :3].astype(float)
    miolo = ndimage.binary_erosion(base, iterations=max(1, int(2 / mpx)))
    if miolo.sum() < 20: miolo = base
    cor = np.median(rgb[miolo], axis=0)
    tex = _textura(rgb, mpx, janela_m=2.5)
    lim = _limiar_textura(tex, miolo)
    dist = np.sqrt(((rgb - cor) ** 2).sum(axis=2))
    nucleo = base & (((dist > tol * 2.0) & (tex > lim * 0.8)) | (tex > lim * 2.0) | (dist > tol * 3.0))
    fraca = base & (dist > tol * 1.25) & (tex > lim * 0.6)
    r = max(1, int(round(largura_min_m / 2 / mpx)))
    nucleo = _abertura(nucleo, r)                                             # ruído fino não é núcleo
    if not nucleo.any(): return [], dict(descartadas_pequenas=0, total=0)
    terra = ndimage.binary_propagation(nucleo, mask=fraca | nucleo)           # cresce do núcleo só por terra de verdade
    terra = ndimage.binary_closing(terra, iterations=2)
    vazios, nv = ndimage.label(ndimage.binary_fill_holes(terra) & ~terra)     # só tapa buraquinhos (< 3 m²); nunca uma baía
    for i in range(1, nv + 1):
        v = vazios == i
        if v.sum() * area_px < 3.0: terra |= v
    rot, nrot = ndimage.label(terra)
    conhecidas = np.zeros_like(base)
    for ring in ilhas_ll or []:
        if len(ring) >= 3: conhecidas |= _rasterizar_anel(ring, w, h, bbox)
    anel = max(2, int(round(2.0 / mpx)))
    ilhas, descartadas, total_m2 = [], 0, 0.0
    for i in range(1, nrot + 1):
        comp = rot == i
        a_m2 = comp.sum() * area_px
        if a_m2 < min_m2: descartadas += 1; continue
        if (comp & conhecidas).sum() > 0.3 * comp.sum(): continue             # já é uma ilha conhecida
        cheio = ndimage.binary_fill_holes(comp)
        if comp.sum() < 0.5 * cheio.sum(): continue                           # é um anel (margem em volta de uma baía), não ilha
        cerca = ndimage.binary_dilation(comp, iterations=anel) & ~comp
        if cerca.sum() == 0 or (cerca & base).sum() < 0.9 * cerca.sum(): continue    # encostada na margem: não é ilha
        if (cerca & ~terra).sum() / max(cerca.sum(), 1) < 0.6: continue       # cercada de mais terra que água: é margem/mata
        for ring in contourpy.contour_generator(z=np.pad(cheio.astype(float), 1)).lines(0.5):
            if len(ring) < 8: continue
            lons, lats = pixel_para_lonlat(ring[::2, 0] - 1, ring[::2, 1] - 1, w, h, bbox)
            pts = list(zip(lats, lons))
            if len(pts) >= 3: ilhas.append(simplificar(pts, 80, 0.3)); total_m2 += a_m2
            break
    if total_m2 > ILHA_MAX_FRACAO * base.sum() * area_px:
        return [], dict(descartadas_pequenas=descartadas, total=0, motivo="As 'ilhas' somavam demais do lago (provável erro de cor); nada aplicado.")
    ilhas = sorted(ilhas, key=lambda g: -_area_aprox(g))[:40]
    return ilhas, dict(descartadas_pequenas=descartadas, total=len(ilhas))


def _area_aprox(anel):
    xs = [p[1] for p in anel]; ys = [p[0] for p in anel]
    return (max(xs) - min(xs)) * (max(ys) - min(ys))


def removidos_depois_de_editar(rem, op, anel_ll):
    """Se o usuário ACRESCENTA água por cima de uma área que tinha sido removida, ela deixa de ser zona proibida."""
    if op != "+" or not rem: return list(rem or [])
    b = _poligono(anel_ll); out = []
    for r in rem:
        try:
            p = _poligono(r)
            if p.area > 0 and p.intersection(b).area / p.area >= 0.5: continue
        except Exception: pass
        out.append(r)
    return out


def zonas_proibidas(M):
    """O que a rota NÃO pode pisar além da margem do lago: ilhas e as áreas removidas por 'não ser água' (floresta, gramado...).
    Subtrair as áreas removidas garante que elas nunca sejam 'engolidas', mesmo em mapas salvos antes das ilhas existirem."""
    rem = [r for r in (M.get("removido") or []) if len(r) >= 4 and _area_ll_m2(r) >= ILHA_MIN_ROTA_M2]
    return list(M.get("ilhas") or []) + rem


def _poligono(anel_ll):
    p = Polygon([(lo, la) for la, lo in anel_ll])
    return p if p.is_valid else p.buffer(0)


def editar_contorno(poly_ll, op, anel_ll):
    """op '+' junta a área ao lago; '-' tira a área do lago. Devolve (novo_contorno, [avisos])."""
    avisos = []
    a, b = _poligono(poly_ll), _poligono(anel_ll)
    r = a.union(b) if op == "+" else a.difference(b)
    pedacos = [g for g in getattr(r, "geoms", [r]) if g.geom_type == "Polygon" and not g.is_empty]
    if not pedacos: raise ValueError("Depois da edição não sobrou nenhuma água. Desfaça e tente de novo.")
    pedacos.sort(key=lambda g: g.area, reverse=True)
    r = pedacos[0]
    if len(pedacos) > 1:
        avisos.append("A edição criou pedaços separados; ficou só o maior. "
                      + ("A área adicionada precisa encostar no lago." if op == "+" else "Cuidado: a remoção cortou o lago em partes."))
    novas = [[(la, lo) for lo, la in i.coords] for i in r.interiors] if op == "-" else []
    if novas:
        avisos.append(f"A área removida ficou no MEIO do lago: virou ilha ({len(novas)}). A rota passa a contorná-la.")
    return simplificar([(la, lo) for lo, la in r.exterior.coords], VERTICES_ROTA, 0.3), avisos, novas


def ilhas_depois_de_editar(ilhas, op, anel_ll, novas):
    """'+' (água adicionada) apaga as ilhas que ela cobre; '-' acrescenta as ilhas novas."""
    if op == "-": return list(ilhas) + list(novas)
    b = _poligono(anel_ll); out = []
    for r in ilhas:
        resto = _poligono(r).difference(b)
        for g in getattr(resto, "geoms", [resto]):
            if g.geom_type == "Polygon" and g.area > 1e-9: out.append([(la, lo) for lo, la in g.exterior.coords])
    return out


def ilhas_do_geojson(g, area_min_m2=20.0):
    """Buracos do contorno do OSM (ilhas dentro do lago), como [[(lat, lon), ...], ...]."""
    if not g: return []
    polis = [g["coordinates"]] if g.get("type") == "Polygon" else (g["coordinates"] if g.get("type") == "MultiPolygon" else [])
    out = []
    for p in polis:
        for r in p[1:]:
            if len(r) < 4: continue
            pts = [(la, lo) for lo, la in r]
            lat0 = float(np.mean([q[0] for q in pts]))
            if abs(_poligono(pts).area) * m_lon(lat0) * M_LAT >= area_min_m2: out.append(simplificar(pts, 60, 0.3))
    return out


ILHA_MIN_ROTA_M2 = 20.0       # ilhas menores que isso não entram no cálculo da rota


def _area_ll_m2(anel_ll):
    lat0 = float(np.mean([p[0] for p in anel_ll])); kx = m_lon(lat0)
    P = [(p[1] * kx, p[0] * M_LAT) for p in anel_ll]
    return abs(sum(x1 * y2 - x2 * y1 for (x1, y1), (x2, y2) in zip(P, P[1:] + P[:1]))) / 2


# ---------- Busca de lugar e imagem de satélite ----------
def buscar_lugar(consulta, limite=5):
    url = "https://nominatim.openstreetmap.org/search?" + urllib.parse.urlencode({
        "q": consulta, "format": "jsonv2", "limit": limite,
        "polygon_geojson": 1, "polygon_threshold": 0.00005, "accept-language": "pt-BR"})
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=15) as r:
        return json.load(r)


def _area_anel(a):
    x = np.array([p[0] for p in a]); y = np.array([p[1] for p in a])
    return 0.5 * abs(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))


def anel_do_geojson(g, juntar_m=12.0):
    """Contorno do OSM como [(lat, lon), ...]. Se o OSM mandar o lago em VÁRIOS pedaços (ex.: separados por uma ponte),
    os pedaços a até ~2*juntar_m metros um do outro são juntados em um contorno só (sem cortar nada)."""
    if not g: return None
    if g.get("type") == "Polygon": aneis = [g["coordinates"][0]]
    elif g.get("type") == "MultiPolygon": aneis = [p[0] for p in g["coordinates"]]
    else: return None
    maior = max(aneis, key=_area_anel)
    if len(aneis) > 1:
        try:
            lat0 = float(np.mean([p[1] for p in maior])); lon0 = float(np.mean([p[0] for p in maior]))
            kx, ky = m_lon(lat0), M_LAT
            polis = [Polygon([((lo - lon0) * kx, (la - lat0) * ky) for lo, la in a]).buffer(0) for a in aneis if len(a) >= 4]
            uniao = unary_union(polis).buffer(juntar_m).buffer(-juntar_m)           # "fecha" o vão da ponte
            pedacos = [g2 for g2 in getattr(uniao, "geoms", [uniao]) if g2.geom_type == "Polygon" and not g2.is_empty]
            if pedacos:
                p = max(pedacos, key=lambda g2: g2.area)
                return [(lat0 + y / ky, lon0 + x / kx) for x, y in p.exterior.coords]
        except Exception:
            pass
    return [(lat, lon) for lon, lat in maior]


def _tile_frac(lon, lat, z):
    n = 2 ** z
    return (lon + 180.0) / 360.0 * n, (1.0 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2.0 * n


def _baixar_tile(z, x, y, pasta, fonte="sat"):
    caminho = os.path.join(pasta, f"{fonte}_{z}_{x}_{y}.img")
    if os.path.exists(caminho): return Image.open(caminho).convert("RGB")
    if fonte == "osm": url = f"https://tile.openstreetmap.org/{z}/{x}/{y}.png"
    else: url = f"https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}"
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=20) as r: dados = r.read()
    with open(caminho, "wb") as f: f.write(dados)
    time.sleep(0.1)
    return Image.open(io.BytesIO(dados)).convert("RGB")


def baixar_satelite(sul, norte, oeste, leste, max_tiles=64, pasta=None, fonte="sat"):
    pasta = str(pasta or TILES_DIR)
    for z in range(18, 8, -1):
        xw, yn = _tile_frac(oeste, norte, z)
        xe, ys = _tile_frac(leste, sul, z)
        tx0, tx1, ty0, ty1 = int(xw), int(xe), int(yn), int(ys)
        if (tx1 - tx0 + 1) * (ty1 - ty0 + 1) <= max_tiles: break
    os.makedirs(pasta, exist_ok=True)
    mosaico = Image.new("RGB", ((tx1 - tx0 + 1) * 256, (ty1 - ty0 + 1) * 256))
    for tx in range(tx0, tx1 + 1):
        for ty in range(ty0, ty1 + 1):
            mosaico.paste(_baixar_tile(z, tx, ty, pasta, fonte), ((tx - tx0) * 256, (ty - ty0) * 256))
    caixa = (int(round((xw - tx0) * 256)), int(round((yn - ty0) * 256)),
             int(round((xe - tx0) * 256)), int(round((ys - ty0) * 256)))
    return mosaico.crop(caixa)


# As buscas e downloads ficam em cache: clicar de novo no mesmo lugar não baixa nada outra vez.
@st.cache_data(ttl=3600, show_spinner=False)
def buscar_lugar_cache(consulta): return buscar_lugar(consulta)


@st.cache_data(show_spinner=False, max_entries=4)
def baixar_satelite_cache(s, n, o, l): return baixar_satelite(s, n, o, l)


def novo_mapa(raw, bbox, nome, poly, realce):
    """Monta o dicionário do mapa que o app guarda na memória."""
    return dict(raw=raw, img=realcar_imagem(raw, realce), bbox=bbox, nome=nome, poly=poly, poly0=list(poly) if poly else None,
                hist=[], pontos=[], wps=None, avisos=[], v=0, params=None, ilhas=[], ilhas0=[])


def preparar_mapa(lugar, realce):
    """Baixa a imagem do lugar escolhido, aplica o realce e acha o contorno inicial (OSM ou cor)."""
    s, n, o, l = map(float, lugar["boundingbox"])
    dlat = max((n - s) * 0.3, 0.0008); dlon = max((l - o) * 0.3, 0.0008)        # folga de 30% (mínimo ~90 m)
    s, n, o, l = s - dlat, n + dlat, o - dlon, l + dlon
    raw = baixar_satelite_cache(s, n, o, l)
    bbox = (o, l, s, n)
    anel = anel_do_geojson(lugar.get("geojson"))
    base_osm = None; removido = []; ilhas = []; ilhas_osm = []
    if anel:                                           # PONTO DE PARTIDA = contorno do mapa, INTEIRO; o programa só ACRESCENTA
        poly = base_osm = simplificar(anel, VERTICES_ROTA, 0.3)
        try: ilhas_osm = ilhas_do_geojson(lugar.get("geojson")) if lugar.get("geojson", {}).get("type") == "Polygon" else []
        except Exception: ilhas_osm = []
        ilhas = list(ilhas_osm)
        notas = ["Contorno do site usado como base (lago inteiro, inclusive sob pontes)."]
        try:
            novo, info = completar_contorno(np.asarray(realcar_imagem(raw, realce)), bbox, base_osm)
        except Exception as e:
            novo, info = None, dict(motivo=f"Não consegui completar pela imagem ({e}).")
        if novo:
            poly = novo
            notas = [f"+ {info['adicionado_m2']:,.0f} m² de água que o site não tinha, acrescentados pela imagem."
                     + (" Atenção: a área acrescentada encosta na borda da imagem; confira se não vazou." if info["borda"] else "")]
        elif info.get("motivo"): notas.append(info["motivo"])
        try:
            limpo, info2 = limpar_contorno(np.asarray(realcar_imagem(raw, realce)), bbox, poly)
        except Exception:
            limpo, info2 = None, {}
        if limpo:
            poly = limpo; removido = info2.get("removido", [])
            ilhas = ilhas_osm + info2.get("ilhas", [])
            if ilhas: notas.append(f"{len(ilhas)} ilha(s) dentro do lago detectada(s): a rota vai contorná-la(s) (contorno amarelo no mapa).")
            notas.append(f"− {info2['removido_m2']:,.0f} m² dentro do contorno que não são água (floresta, gramado ou rua) foram "
                         f"retirados; aparecem em vermelho.")
        notas.append("A linha branca tracejada é o contorno original do site. Não gostou? Toque em “Contorno do site”.")
    else:                                              # sem contorno no mapa: aí sim detecta pela cor
        img = np.asarray(realcar_imagem(raw, realce))
        poly, notas = contorno_hibrido(img, bbox, semente=(float(lugar["lon"]), float(lugar["lat"])))
    try:
        extra, _ = detectar_ilhas(np.asarray(realcar_imagem(raw, realce)), bbox, poly, ilhas)
        ilhas = ilhas + extra
    except Exception:
        pass
    if ilhas and not any("ilha(s)" in x for x in notas): notas.append(f"{len(ilhas)} ilha(s) dentro do lago detectada(s): a rota vai contorná-la(s) (contorno amarelo no mapa).")
    M = novo_mapa(raw, bbox, lugar.get("display_name", "lago"), poly, realce)
    if base_osm: M["poly0"] = list(base_osm)           # "Contorno do site" = o do mapa, antes do programa melhorar
    M["removido"] = removido
    M["ilhas"] = ilhas; M["ilhas0"] = list(ilhas_osm)
    M["notas"] = notas
    return M


# =====================================================================
#   PARTE D - DESENHO DO MAPA (vira uma imagem PNG; o clique é traduzido para lat/lon)
# =====================================================================
VERDE = LinearSegmentedColormap.from_list("bioglow", ["#d8f5d0", "#4caf50", "#0b3d0b"])


def barra_escala(ax, lim):
    e, d, b, c = lim                                  # (oeste, leste, sul, norte) do trecho visível
    lat_m = (b + c) / 2
    alvo = (d - e) * m_lon(lat_m) / 5
    comp = max([v for v in (0.5, 1, 2, 5, 10, 20, 50, 100, 200, 500, 1000) if v <= alvo] or [0.5])
    graus = comp / m_lon(lat_m)
    x0 = e + (d - e) * 0.03; y0 = b + (c - b) * 0.05
    ax.plot([x0, x0 + graus], [y0, y0], color="white", lw=5, solid_capstyle="butt")
    ax.plot([x0, x0 + graus], [y0, y0], color="black", lw=2, solid_capstyle="butt")
    ax.text(x0 + graus / 2, y0 + (c - b) * 0.02, f"{comp:g} m", color="white", ha="center", fontsize=9, fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.15", fc="black", alpha=0.5, lw=0))


def janela_de_visao(M, zoom):
    """(oeste, leste, sul, norte) a mostrar: a imagem toda, ou só o lago (com folga) se zoom=True."""
    o, l, s, n = M["bbox"]
    if not (zoom and M.get("poly")): return o, l, s, n
    la = [p[0] for p in M["poly"]]; lo = [p[1] for p in M["poly"]]
    dlat = max((max(la) - min(la)) * 0.12, 0.0002); dlon = max((max(lo) - min(lo)) * 0.12, 0.0002)
    return max(o, min(lo) - dlon), min(l, max(lo) + dlon), max(s, min(la) - dlat), min(n, max(la) + dlat)


def renderizar_mapa(M, view, poly=None, wps=None, pontos=(), pos=None, leituras=None, largura_px=1350, base=None, removido=None,
                    rota_alpha=None, algas=None):
    """Desenha o mapa ocupando a figura INTEIRA (sem margens) para que pixel -> lat/lon seja uma regra de três.
    rota_alpha (0.05 a 1): opacidade da rota; algas: liga o mapa de calor 'Algas ativas'. Se None, valem os controles da barra lateral."""
    if rota_alpha is None: rota_alpha = _ss("rota_op", 0.9)
    if algas is None: algas = bool(_ss("algas_on", False))
    rota_alpha = min(1.0, max(0.05, float(rota_alpha)))
    o, l, s, n = view
    lat_m = (s + n) / 2
    wm, hm = (l - o) * m_lon(lat_m), (n - s) * M_LAT
    altura = int(min(max(largura_px * hm / wm, 200), 2600))
    fig = Figure(figsize=(largura_px / 100, altura / 100), dpi=100)
    ax = fig.add_axes([0, 0, 1, 1])
    bo, bl, bs, bn = M["bbox"]
    ax.imshow(M["img"], extent=[bo, bl, bs, bn], aspect="auto")
    if poly:
        ax.plot([p[1] for p in poly] + [poly[0][1]], [p[0] for p in poly] + [poly[0][0]], "y-", lw=2, label="Parede virtual")
    if base and poly and list(base) != list(poly):
        ax.plot([p[1] for p in base] + [base[0][1]], [p[0] for p in base] + [base[0][0]], "--", color="white", lw=1.3, label="Contorno do site")
    for i, ring in enumerate(M.get("ilhas") or []):
        ax.plot([p[1] for p in ring] + [ring[0][1]], [p[0] for p in ring] + [ring[0][0]], "y-", lw=1.5,
                label="Ilha (a rota contorna)" if i == 0 else None)
    for i, ring in enumerate(removido or []):
        ax.plot([p[1] for p in ring] + [ring[0][1]], [p[0] for p in ring] + [ring[0][0]], "-", color="#ff2d2d", lw=1.6,
                label="Removido (não é água)" if i == 0 else None)
    calor = None
    if algas and M.get("poly"):
        try:
            calor = mapa_de_calor_algas(M, leituras)
            if calor is not None:
                ax.imshow(calor["rgba"], extent=[bo, bl, bs, bn], aspect="auto", zorder=2)
                ax.plot([], [], "s", color="#ff5a00", label=calor["legenda"])
        except Exception:
            calor = None                                                                  # o mapa de calor nunca derruba o mapa
    if wps:
        ax.plot([w[1] for w in wps], [w[0] for w in wps], "-", color="#00e5ff", lw=0.9, alpha=rota_alpha, label="Rota")
    if pontos:
        ax.plot([p[1] for p in pontos], [p[0] for p in pontos], "-o", color="#ff3b30", ms=6, lw=1.5, label="Pontos que você marcou")
        for i, p in enumerate(pontos, 1):
            ax.text(p[1], p[0], f" {i}", color="white", fontsize=8, fontweight="bold")
    d = np.array(leituras) if leituras else np.empty((0, 5))
    if len(d) >= 4:
        try:
            gx, gy = np.meshgrid(np.linspace(o, l, 120), np.linspace(s, n, 120))
            gz = griddata((d[:, 1], d[:, 0]), d[:, 2], (gx, gy), method="linear")
            ax.contourf(gx, gy, gz, 15, cmap=VERDE, alpha=0.6)
        except Exception:
            pass
    if len(d):
        ax.scatter(d[:, 1], d[:, 0], c="white", edgecolors="k", s=14)
        f = d[d[:, 4] == 1]
        if len(f): ax.scatter(f[:, 1], f[:, 0], c="red", marker="x", s=55, label="Anomalia confirmada (re-teste do robô)")
    if pos: ax.plot(pos[1], pos[0], "c^", ms=12, label="Robô")
    barra_escala(ax, view)
    ax.set_xlim(o, l); ax.set_ylim(s, n); ax.axis("off")
    ax.text(0.995, 0.005, CREDITOS, transform=ax.transAxes, ha="right", va="bottom", fontsize=6, color="white",
            bbox=dict(boxstyle="round,pad=0.2", fc="black", alpha=0.45, lw=0))
    if poly or wps or len(d) or pos: ax.legend(loc="upper right", fontsize=8)
    buf = io.BytesIO(); fig.savefig(buf, format="png", dpi=100); buf.seek(0)
    return buf.getvalue()


def _ss(chave, padrao):
    """Lê um controle da barra lateral (st.session_state) sem quebrar fora do Streamlit."""
    try: return st.session_state.get(chave, padrao)
    except Exception: return padrao


def mapa_de_calor_algas(M, leituras=None, escala_m=6.0):
    """Mapa de calor 'Algas ativas'. As algas se acumulam nas margens (vento e correnteza empurram para lá), então:
    - sem leituras do robô: mostra a ZONA PROVÁVEL de acúmulo = faixa junto à margem e às ilhas (cai com a distância, ~escala_m);
    - com leituras (turbidez): soma a turbidez medida, espalhada em volta de cada ponto, à zona provável (50% / 50%).
    Devolve dict(rgba=matriz RGBA do tamanho da imagem, legenda=texto) ou None."""
    img = M["img"]; W, H = img.size
    f = max(1, int(max(W, H) / 1100))                                    # trabalha em resolução menor (mais rápido)
    w, h = W // f, H // f
    o, l, s_, n = M["bbox"]
    mpx = min((l - o) * m_lon((s_ + n) / 2) / (w - 1), (n - s_) * M_LAT / (h - 1))
    agua = _rasterizar_anel(M["poly"], w, h, M["bbox"])
    for ring in M.get("ilhas") or []:
        if len(ring) >= 3: agua &= ~_rasterizar_anel(ring, w, h, M["bbox"])
    if agua.sum() < 20: return None
    dist = ndimage.distance_transform_edt(agua) * mpx                    # metros até a terra mais próxima (margem ou ilha)
    calor = np.exp(-dist / escala_m) * agua
    legenda = "Algas ativas: zona provável (margens)"
    d = np.array(leituras) if leituras else np.empty((0, 5))
    if len(d) >= 1:
        med = np.zeros((h, w))
        cx = np.clip(((d[:, 1] - o) / (l - o) * (w - 1)).astype(int), 0, w - 1)
        cy = np.clip(((n - d[:, 0]) / (n - s_) * (h - 1)).astype(int), 0, h - 1)
        np.add.at(med, (cy, cx), np.clip(d[:, 2], 0, None))
        med = ndimage.gaussian_filter(med, max(1.0, 8.0 / mpx))
        if med.max() > 0: calor = 0.5 * calor + 0.5 * (med / med.max()) * agua
        legenda = "Algas ativas: leituras + zona provável"
    if calor.max() <= 0: return None
    calor = calor / calor.max()
    rgba = np.zeros((h, w, 4))
    rgba[..., 0] = 1.0
    rgba[..., 1] = np.clip(0.95 - 0.8 * calor, 0.1, 0.95)                # amarelo (pouco) -> vermelho (muito)
    rgba[..., 2] = 0.0
    rgba[..., 3] = np.where(agua, 0.7 * np.power(calor, 0.8), 0.0)
    return dict(rgba=rgba, legenda=legenda)


# ---------- simulação da rota (antes de enviar ao robô) ----------
def posicao_na_rota(wps, frac):
    """Ponto (lat, lon, rumo_graus, distancia_m) a 'frac' (0 a 1) do percurso, andando em metros (movimento suave)."""
    if len(wps) < 2: return None
    lat0 = float(np.mean([w[0] for w in wps])); kx = m_lon(lat0)
    xy = [((w[1]) * kx, w[0] * M_LAT) for w in wps]
    seg = [math.dist(a, b) for a, b in zip(xy[:-1], xy[1:])]
    total = sum(seg)
    if total <= 0: return (wps[0][0], wps[0][1], 0.0, 0.0)
    alvo = min(max(frac, 0.0), 1.0) * total
    acum = 0.0
    for i, d in enumerate(seg):
        if acum + d >= alvo or i == len(seg) - 1:
            t = 0.0 if d <= 0 else min(1.0, (alvo - acum) / d)
            la = wps[i][0] + (wps[i + 1][0] - wps[i][0]) * t
            lo = wps[i][1] + (wps[i + 1][1] - wps[i][1]) * t
            dx, dy = xy[i + 1][0] - xy[i][0], xy[i + 1][1] - xy[i][1]
            rumo = (math.degrees(math.atan2(dx, dy)) + 360) % 360       # 0 = norte, 90 = leste
            return (la, lo, rumo, alvo)
        acum += d


def quadro_simulacao(png, view, wps, frac, cor_rastro=(255, 255, 255)):
    """Desenha, por cima do PNG do mapa, o rastro já percorrido e um barquinho (casco pontudo, virado para onde vai)
    em 'frac' da rota. Rápido (só PIL): serve para animar sem redesenhar o mapa. Devolve PNG em bytes."""
    p = posicao_na_rota(wps, frac)
    im = Image.open(io.BytesIO(png)).convert("RGBA")
    if p is None: return png
    W, H = im.size; o, l, s_, n = view
    px = lambda la, lo: ((lo - o) / (l - o) * W, (n - la) / (n - s_) * H)
    cam = Image.new("RGBA", im.size, (0, 0, 0, 0)); d = ImageDraw.Draw(cam)
    # rastro: pontos da rota até a posição atual
    la, lo, rumo, dist = p
    lat0 = float(np.mean([w[0] for w in wps])); kx = m_lon(lat0)
    pts, acum = [px(*wps[0])], 0.0
    for a, b in zip(wps[:-1], wps[1:]):
        dd = math.dist((a[1] * kx, a[0] * M_LAT), (b[1] * kx, b[0] * M_LAT))
        if acum + dd >= dist: break
        pts.append(px(*b)); acum += dd
    pts.append(px(la, lo))
    if len(pts) >= 2: d.line(pts, fill=cor_rastro + (230,), width=max(2, W // 450), joint="curve")
    # barquinho
    cx, cy = px(la, lo); r = max(9, W // 90); a = math.radians(rumo)
    fx, fy = math.sin(a), -math.cos(a)                                    # frente (y da tela cresce para baixo)
    lx, ly = -fy, fx
    casco = [(cx + fx * r * 1.6, cy + fy * r * 1.6), (cx + lx * r * 0.8 - fx * r, cy + ly * r * 0.8 - fy * r),
             (cx - fx * r * 0.6, cy - fy * r * 0.6), (cx - lx * r * 0.8 - fx * r, cy - ly * r * 0.8 - fy * r)]
    d.polygon(casco, fill=(0, 200, 255, 255), outline=(255, 255, 255, 255))
    d.line(casco + [casco[0]], fill=(255, 255, 255, 255), width=max(2, r // 4))
    d.ellipse([cx - r * 0.25, cy - r * 0.25, cx + r * 0.25, cy + r * 0.25], fill=(255, 255, 255, 255))
    out = io.BytesIO(); Image.alpha_composite(im, cam).convert("RGB").save(out, "PNG")
    return out.getvalue()


def relatorio(leituras, M, view):
    """Devolve (texto, csv_em_bytes, png_em_bytes) ou None se não há leituras."""
    d = np.array(leituras)
    if not len(d): return None
    sb = io.StringIO()
    w = csv.writer(sb); w.writerow(["lat", "lon", "turbidez", "ph", "bloom"]); w.writerows(d.tolist())
    png = renderizar_mapa(M, view, poly=M.get("poly"), wps=M.get("wps"), leituras=leituras)
    lat0 = d[:, 0].mean(); kx, ky = m_lon(lat0), M_LAT
    cel = {}
    for la, lo, tu, ph, bl in d:
        cel.setdefault((int(lo * kx // CELULA_M), int(la * ky // CELULA_M)), []).append((la, lo, tu, ph, bl))
    ranking = []
    for pts in cel.values():
        a = np.array(pts)
        ranking.append((a[:, 2].mean(), a[:, 4].mean(), a[:, 0].mean(), a[:, 1].mean(), len(a)))
    ranking.sort(reverse=True)
    linhas = ["RELATÓRIO BIOGLOW - pontos prioritários para limpeza",
              "(ranqueados por turbidez média; anomalia% = leituras confirmadas no re-teste do robô)\n"]
    for i, (tu, bl, la, lo, n) in enumerate(ranking[:5], 1):
        linhas.append(f"{i}. turbidez média {tu:.0f} | anomalia {bl*100:.0f}% | {n} leituras | "
                      f"https://maps.google.com/?q={la:.6f},{lo:.6f}")
    return "\n".join(linhas), sb.getvalue().encode("utf-8"), png


CHAVES_MAPA = dict(pontos=list, hist=list, ilhas=list, ilhas0=list, avisos=list, notas=list, removido=list, wps=None, v=0, params=None)


def garantir_mapa(M):
    """Deixa o dicionário do mapa sempre completo e coerente (mapas antigos ou salvos por versões anteriores não quebram a tela)."""
    for k, padrao in CHAVES_MAPA.items():
        if M.get(k) is None: M[k] = padrao() if callable(padrao) else padrao
    if not isinstance(M.get("v"), int): M["v"] = 0
    for k in ("poly", "poly0", "wps"):                                   # formatos sempre iguais, mesmo vindo do disco (pickle) ou de JSON
        if M.get(k): M[k] = [tuple(p) for p in M[k]]
    M["ilhas"] = [[tuple(p) for p in r] for r in M["ilhas"] if r and len(r) >= 3]
    M["ilhas0"] = [[tuple(p) for p in r] for r in M["ilhas0"] if r and len(r) >= 3]
    M["pontos"] = [tuple(p) for p in M["pontos"]]
    M["hist"] = [h if (isinstance(h, tuple) and len(h) == 2) else (list(h), []) for h in M["hist"] if h]   # formato antigo: só o contorno
    return M


def _arquivo_mapa():
    return PASTA / "mapas" / (hashlib.sha256(hardware_id().encode()).hexdigest()[:24] + ".pkl")


def salvar_mapa(M):
    """Guarda o mapa em disco (por navegador). Se o tablet dormir e a página recarregar, o mapa volta sozinho."""
    try:
        import pickle
        assinatura = (id(M), M.get("v"), len(M.get("hist") or []), len(M.get("ilhas") or []), len(M.get("poly") or []), len(M.get("wps") or []))
        if st.session_state.get("_mapa_salvo") == assinatura: return
        arq = _arquivo_mapa(); arq.parent.mkdir(parents=True, exist_ok=True)
        tmp = arq.with_suffix(".tmp")
        with open(tmp, "wb") as f: pickle.dump(M, f, protocol=4)
        os.replace(tmp, arq)
        st.session_state["_mapa_salvo"] = assinatura
        limite = time.time() - 7 * 86400
        for velho in arq.parent.glob("*.pkl"):
            if velho != arq and velho.stat().st_mtime < limite: velho.unlink(missing_ok=True)
    except Exception:
        pass                                                                  # salvar é um extra: nunca derruba a tela


def restaurar_mapa():
    if st.session_state.get("M"): return
    try:
        import pickle
        arq = _arquivo_mapa()
        if arq.exists():
            with open(arq, "rb") as f: M = pickle.load(f)      # arquivo escrito só por este app, com nome derivado do navegador
            if isinstance(M, dict) and M.get("img") is not None and M.get("bbox"):
                st.session_state["M"] = garantir_mapa(M)
    except Exception:
        pass


def _png_simples(M, view, largura_px=1100):
    """Plano B do mapa: só a imagem de satélite recortada, sem camadas (funciona mesmo se o contorno estiver com problema)."""
    o, l, s_, n = M["bbox"]; im = M["img"].convert("RGB")
    w, h = im.size
    vo, vl, vs, vn = view
    box = (max(0, int((vo - o) / (l - o) * w)), max(0, int((n - vn) / (n - s_) * h)),
           min(w, int((vl - o) / (l - o) * w)), min(h, int((n - vs) / (n - s_) * h)))
    if box[2] - box[0] > 8 and box[3] - box[1] > 8: im = im.crop(box)
    im.thumbnail((largura_px, largura_px)); b = io.BytesIO(); im.save(b, "PNG")
    return b.getvalue()


def mapa_em_cache(M, view, largura_px=1100):
    """Desenhar o mapa é a parte lenta. Guardamos os últimos desenhos: tocar num botão que não muda o mapa não redesenha nada."""
    poly, wps = M.get("poly"), M.get("wps")
    base = M.get("poly0")
    chave = (id(M["img"]), tuple(view), hash(tuple(poly)) if poly else 0, hash(tuple(wps)) if wps else 0,
             hash(tuple(M["pontos"])), hash(tuple(base)) if base else 0, len(M.get("removido") or []), hash(tuple(tuple(r) for r in M.get("ilhas") or [])), largura_px,
             round(float(_ss("rota_op", 0.9)), 2), bool(_ss("algas_on", False)))
    cache = st.session_state.setdefault("_rc", {})
    if chave not in cache:
        try:
            png = renderizar_mapa(M, view, poly=poly, wps=wps, pontos=M["pontos"], largura_px=largura_px, base=base, removido=M.get("removido"),
                                  rota_alpha=_ss("rota_op", 0.9), algas=bool(_ss("algas_on", False)))
        except Exception as e:                                                # falhou ao desenhar: mantém o último mapa bom
            st.session_state["msg3"] = ("error", f"Não consegui redesenhar o mapa ({e}). Mostrando o último desenho.")
            if cache: return st.session_state.get("_ultimo_png") or cache[next(reversed(cache))]
            return st.session_state.get("_ultimo_png") or _png_simples(M, view)       # nunca devolve "nada": a tela não pode sumir
        while len(cache) >= 4: cache.pop(next(iter(cache)))
        cache[chave] = png; st.session_state["_ultimo_png"] = png
    return cache[chave]
