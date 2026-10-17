# =====================================================================
# BioGlow - CENTRAL WEB (Streamlit) - VERSÃO 6
#
# O que é: a Central do robô AquaSentry transformada em aplicativo web, com
#   - contas de usuário (e-mail + senha), chave de ativação e limite de 3 computadores;
#   - Passo 1: conta | Passo 2: busca do lago + realce da imagem
#     Passo 3: contorno + rota de varredura | Passo 4: painel do robô em tempo real (UDP).
#
# Como rodar (no terminal do VS Code, na pasta do arquivo):
#     pip install streamlit streamlit-image-coordinates numpy matplotlib shapely scipy pillow
#     streamlit run app.py          (se "streamlit" não for reconhecido:  python -m streamlit run app.py)
#
# Gerar chaves de ativação novas (vendedor/professor):
#     python app.py gerar-chaves 5
#
# IMPORTANTE: o servidor do Streamlit tem que rodar NO computador que está na mesma rede Wi-Fi do robô
# (a comunicação com o robô é UDP local). O navegador só mostra a tela.
#
# Mini-glossário: variável = "caixinha" com nome | função = trecho de código com nome (def) |
#   hash = "impressão digital" de um texto (não dá para voltar ao original) | SQLite = banco de dados em um arquivo |
#   session_state = memória do Streamlit para guardar coisas entre cliques | UDP = mensagens curtas pelo Wi-Fi.
# =====================================================================

import socket, threading, time, math, csv, urllib.request, urllib.parse, json, io, os, sys, heapq
import re, uuid, platform, hashlib, hmac, secrets, sqlite3, stat
from contextlib import contextmanager
from pathlib import Path

import numpy as np
import streamlit as st
from matplotlib.figure import Figure                   # Figure (sem pyplot) é seguro dentro do Streamlit
from matplotlib.colors import LinearSegmentedColormap
from PIL import Image, ImageEnhance, ImageOps
from shapely.geometry import Polygon, LineString
from shapely.affinity import rotate
from shapely.prepared import prep
from scipy.interpolate import griddata
from scipy import ndimage
import contourpy

try:                                                   # biblioteca que devolve o lugar clicado na imagem
    from streamlit_image_coordinates import streamlit_image_coordinates
except ImportError:
    streamlit_image_coordinates = None

# ---------------- CONFIGURAÇÃO (o que você pode ajustar) ----------------
# --- Rota de varredura: tudo calculado a partir da LARGURA REAL do robô (em metros no lago, não em pixels) ---
LARGURA_ROBO_M = 0.50   # largura do barco
SOBREPOSICAO = 0.10     # 10% de sobreposição entre faixas vizinhas
ESPACAMENTO_M = round(LARGURA_ROBO_M * (1 - SOBREPOSICAO), 3)   # = 0,45 m
MARGEM_M = 3.0          # distância mínima da "parede" (GPS comum erra alguns metros)
COMPRIMENTO_MIN_FAIXA_M = 0.3
ANGULO_PASSO = 5        # direção das faixas testada de 5 em 5 graus
CELULA_M = 10.0         # célula para ranquear focos no relatório
PORTA_CENTRAL = 5005    # o computador escuta aqui
PORTA_ROBO = 5006       # o robô escuta aqui
MAX_VERTICES = 200      # cerca virtual enviada ao robô (= MAX_V do firmware)
VERTICES_ROTA = 1500    # contorno usado para CALCULAR a rota (bem mais fiel)
MAX_WAYPOINTS = 4000    # = MAX_W do firmware
USER_AGENT = "BioGlow-FLL/1.0 (projeto escolar; contato: SEU_EMAIL@exemplo.com)"   # troque pelo seu e-mail!
TOL_PADRAO = 45         # sensibilidade inicial da detecção da água por cor

# --- Realce automático da imagem (1.0 = sem mudança) ---
REALCE_PADRAO = dict(ativo=True, auto=1, brilho=1.10, contraste=1.25, cor=1.60, nitidez=1.40)

# --- Contas e licenças ---
APP_NOME = "BioGlow"
PREFIXO_CHAVE = "BIOGLOW-FLL2026"      # começo de toda chave de ativação
MAX_DISPOSITIVOS = 3                   # computadores por conta
SESSAO_DIAS = 30                       # quanto tempo o login "lembrado" vale
MAX_FALHAS_LOGIN = 5                   # erros de senha seguidos até bloquear
BLOQUEIO_LOGIN_S = 300                 # tempo do bloqueio (5 min)
PBKDF2_ITER = 200_000                  # "dificuldade" do hash da senha (maior = mais seguro e mais lento)
# Modo demonstração: se não existir nenhuma chave, o app cria 3 e MOSTRA na tela de chave onde achá-las.
# Para uso comercial real: BIOGLOW_DEMO=0 (variável de ambiente) e entregue as chaves só aos clientes.
MODO_DEMO = os.environ.get("BIOGLOW_DEMO", "1") == "1"

# Pasta onde ficam banco de dados, sessão e cache de mapas (pode trocar com a variável BIOGLOW_DIR)
PASTA = Path(os.environ.get("BIOGLOW_DIR", Path.home() / ".bioglow"))
DB_PATH = Path(os.environ.get("BIOGLOW_DB", PASTA / "bioglow_contas.db"))
TOKEN_PATH = PASTA / "sessao.token"
TILES_DIR = PASTA / "tiles"
CREDITOS = "Imagens © Esri e colaboradores  |  Dados de lugares © OpenStreetMap contributors"
# ------------------------------------------------------------------------

M_LAT = 110540.0                                                   # metros por grau de latitude
def m_lon(lat0): return 111320.0 * math.cos(math.radians(lat0))   # metros por grau de longitude


# =====================================================================
#   PARTE A - CONTAS, CHAVES, DISPOSITIVOS E SESSÃO  (SQLite)
# =====================================================================
@contextmanager
def transacao():
    """Abre o banco, executa tudo como UMA operação (ou tudo ou nada) e fecha."""
    PASTA.mkdir(parents=True, exist_ok=True)
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    con = sqlite3.connect(str(DB_PATH), timeout=10, isolation_level=None)
    con.row_factory = sqlite3.Row
    try:
        con.execute("BEGIN IMMEDIATE")
        yield con
        con.execute("COMMIT")
    except Exception:
        try: con.execute("ROLLBACK")
        except sqlite3.Error: pass
        raise
    finally:
        con.close()

def agora(): return int(time.time())

def init_db():
    """Cria as tabelas (se não existirem). Em modo demonstração, cria 3 chaves de teste na primeira vez."""
    with transacao() as c:
        c.executescript if False else None
        c.execute("""CREATE TABLE IF NOT EXISTS usuarios(
            id INTEGER PRIMARY KEY AUTOINCREMENT, email TEXT UNIQUE NOT NULL, sal TEXT NOT NULL, hash TEXT NOT NULL,
            criado INTEGER NOT NULL, falhas INTEGER NOT NULL DEFAULT 0, bloqueado_ate INTEGER NOT NULL DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS chaves(
            chave TEXT PRIMARY KEY, criada INTEGER NOT NULL, usuario_id INTEGER, resgatada_em INTEGER)""")
        c.execute("""CREATE TABLE IF NOT EXISTS dispositivos(
            id INTEGER PRIMARY KEY AUTOINCREMENT, usuario_id INTEGER NOT NULL, hwid TEXT NOT NULL, nome TEXT,
            primeiro_uso INTEGER NOT NULL, ultimo_uso INTEGER NOT NULL, UNIQUE(usuario_id, hwid))""")
        c.execute("""CREATE TABLE IF NOT EXISTS sessoes(
            token_hash TEXT PRIMARY KEY, usuario_id INTEGER NOT NULL, hwid TEXT NOT NULL,
            criada INTEGER NOT NULL, expira INTEGER NOT NULL)""")
    if MODO_DEMO:
        with transacao() as c:
            vazio = c.execute("SELECT COUNT(*) AS n FROM chaves").fetchone()["n"] == 0
        if vazio:
            novas = gerar_chaves(3)
            PASTA.mkdir(parents=True, exist_ok=True)
            (PASTA / "chaves_de_teste.txt").write_text("\n".join(novas) + "\n", encoding="utf-8")
            print("CHAVES DE TESTE CRIADAS:\n  " + "\n  ".join(novas))

# ---------- senha ----------
def hash_senha(senha, sal=None):
    """Transforma a senha em uma 'impressão digital' lenta de calcular (PBKDF2). Nunca guardamos a senha em si."""
    sal = sal or secrets.token_bytes(16)
    h = hashlib.pbkdf2_hmac("sha256", senha.encode("utf-8"), sal, PBKDF2_ITER)
    return sal.hex(), h.hex()

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]{2,}$")

def criar_conta(email, senha):
    """Devolve (id, mensagem). id = None se deu erro."""
    email = email.strip().lower()
    if not EMAIL_RE.match(email): return None, "E-mail inválido."
    if len(senha) < 8: return None, "A senha precisa ter pelo menos 8 caracteres."
    sal, h = hash_senha(senha)
    try:
        with transacao() as c:
            cur = c.execute("INSERT INTO usuarios(email, sal, hash, criado) VALUES(?,?,?,?)", (email, sal, h, agora()))
            return cur.lastrowid, "Conta criada!"
    except sqlite3.IntegrityError:
        return None, "Já existe uma conta com esse e-mail."

def autenticar(email, senha):
    """Confere e-mail e senha. Devolve (id, mensagem). Bloqueia por 5 min após 5 erros seguidos."""
    email = email.strip().lower()
    with transacao() as c:
        u = c.execute("SELECT * FROM usuarios WHERE email=?", (email,)).fetchone()
        if u is None:
            hash_senha(senha)                                      # gasta o mesmo tempo, para não revelar se o e-mail existe
            return None, "E-mail ou senha incorretos."
        if u["bloqueado_ate"] > agora():
            falta = (u["bloqueado_ate"] - agora()) // 60 + 1
            return None, f"Muitas tentativas erradas. Tente de novo em cerca de {falta} min."
        _, h = hash_senha(senha, bytes.fromhex(u["sal"]))
        if hmac.compare_digest(h, u["hash"]):                      # comparação segura (tempo constante)
            c.execute("UPDATE usuarios SET falhas=0, bloqueado_ate=0 WHERE id=?", (u["id"],))
            return u["id"], "ok"
        falhas = u["falhas"] + 1
        if falhas >= MAX_FALHAS_LOGIN:
            c.execute("UPDATE usuarios SET falhas=0, bloqueado_ate=? WHERE id=?", (agora() + BLOQUEIO_LOGIN_S, u["id"]))
            return None, "Muitas tentativas erradas. Conta bloqueada por 5 minutos."
        c.execute("UPDATE usuarios SET falhas=? WHERE id=?", (falhas, u["id"]))
        return None, "E-mail ou senha incorretos."

# ---------- chaves de ativação ----------
ALFABETO = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"        # sem 0/O/1/I para não confundir ao digitar

def _digito_verificador(corpo):
    """4 letras calculadas a partir do corpo da chave: pegam erros de digitação (não são segredo)."""
    d = hashlib.sha256(("bioglow|" + corpo).encode()).digest()
    return "".join(ALFABETO[b % len(ALFABETO)] for b in d[:4])

def nova_chave():
    corpo = "".join(secrets.choice(ALFABETO) for _ in range(8))
    corpo = corpo[:4] + "-" + corpo[4:]
    return f"{PREFIXO_CHAVE}-{corpo}-{_digito_verificador(corpo)}"      # ex.: BIOGLOW-FLL2026-K7QM-4XTD-ABCD

def normalizar_chave(texto):
    return re.sub(r"\s+", "", texto or "").upper()

def formato_chave_ok(chave):
    m = re.fullmatch(re.escape(PREFIXO_CHAVE) + r"-([A-Z0-9]{4}-[A-Z0-9]{4})-([A-Z0-9]{4})", chave)
    return bool(m) and hmac.compare_digest(m.group(2), _digito_verificador(m.group(1)))

def gerar_chaves(n):
    """Cria n chaves novas no banco e devolve a lista."""
    novas = []
    with transacao() as c:
        while len(novas) < n:
            k = nova_chave()
            if c.execute("SELECT 1 FROM chaves WHERE chave=?", (k,)).fetchone(): continue
            c.execute("INSERT INTO chaves(chave, criada) VALUES(?,?)", (k, agora()))
            novas.append(k)
    return novas

def chave_do_usuario(uid):
    with transacao() as c:
        r = c.execute("SELECT chave FROM chaves WHERE usuario_id=?", (uid,)).fetchone()
    return r["chave"] if r else None

def resgatar_chave(uid, texto):
    """Liga uma chave (ainda livre) à conta. Devolve (ok, mensagem)."""
    chave = normalizar_chave(texto)
    if not formato_chave_ok(chave):
        return False, f"Chave inválida. O formato é {PREFIXO_CHAVE}-XXXX-XXXX-XXXX. Confira a digitação."
    with transacao() as c:
        if c.execute("SELECT 1 FROM chaves WHERE usuario_id=?", (uid,)).fetchone():
            return False, "Esta conta já tem uma chave ativada."
        r = c.execute("SELECT * FROM chaves WHERE chave=?", (chave,)).fetchone()
        if r is None: return False, "Essa chave não existe."
        if r["usuario_id"] is not None: return False, "Essa chave já foi usada em outra conta."
        c.execute("UPDATE chaves SET usuario_id=?, resgatada_em=? WHERE chave=?", (uid, agora(), chave))
    return True, "Chave ativada! Sua licença está liberada."

# ---------- dispositivos (computadores) ----------
def hardware_id():
    """ID estável deste computador: mistura do endereço de rede (MAC), sistema e nome da máquina."""
    mac = uuid.getnode()
    if (mac >> 40) & 1:                                   # bit "aleatório": o Python não achou um MAC de verdade
        arq = PASTA / "hwid.txt"                          # então guardamos um número aleatório fixo neste computador
        PASTA.mkdir(parents=True, exist_ok=True)
        if not arq.exists(): arq.write_text(uuid.uuid4().hex, encoding="utf-8")
        mac = arq.read_text(encoding="utf-8").strip()
    bruto = "|".join([str(mac), platform.system(), platform.machine(), platform.node()])
    return hashlib.sha256(bruto.encode()).hexdigest()[:16].upper()

def nome_dispositivo(): return f"{platform.node() or 'computador'} ({platform.system()} {platform.release()})"

def registrar_dispositivo(uid, hwid, nome):
    """Registra este computador na conta. Devolve 'ok' (já era), 'novo' (registrado agora) ou 'cheio' (limite atingido)."""
    with transacao() as c:
        r = c.execute("SELECT id FROM dispositivos WHERE usuario_id=? AND hwid=?", (uid, hwid)).fetchone()
        if r:
            c.execute("UPDATE dispositivos SET ultimo_uso=?, nome=? WHERE id=?", (agora(), nome, r["id"]))
            return "ok"
        n = c.execute("SELECT COUNT(*) AS n FROM dispositivos WHERE usuario_id=?", (uid,)).fetchone()["n"]
        if n >= MAX_DISPOSITIVOS: return "cheio"
        c.execute("INSERT INTO dispositivos(usuario_id, hwid, nome, primeiro_uso, ultimo_uso) VALUES(?,?,?,?,?)",
                  (uid, hwid, nome, agora(), agora()))
        return "novo"

def listar_dispositivos(uid):
    with transacao() as c:
        return [dict(r) for r in c.execute("SELECT * FROM dispositivos WHERE usuario_id=? ORDER BY primeiro_uso", (uid,))]

def desvincular_dispositivo(uid, dev_id):
    """Remove um computador da conta (e as sessões lembradas dele)."""
    with transacao() as c:
        r = c.execute("SELECT hwid FROM dispositivos WHERE id=? AND usuario_id=?", (dev_id, uid)).fetchone()
        if r is None: return
        c.execute("DELETE FROM dispositivos WHERE id=?", (dev_id,))
        c.execute("DELETE FROM sessoes WHERE usuario_id=? AND hwid=?", (uid, r["hwid"]))

# ---------- sessão persistente (login "lembrado" neste computador) ----------
def _hash_token(tok): return hashlib.sha256(tok.encode()).hexdigest()

def criar_sessao(uid, hwid):
    """Cria um token aleatório. No banco guardamos só o hash; o token em si fica num arquivo deste computador."""
    tok = secrets.token_urlsafe(32)
    with transacao() as c:
        c.execute("DELETE FROM sessoes WHERE expira < ?", (agora(),))
        c.execute("INSERT INTO sessoes(token_hash, usuario_id, hwid, criada, expira) VALUES(?,?,?,?,?)",
                  (_hash_token(tok), uid, hwid, agora(), agora() + SESSAO_DIAS * 86400))
    return tok

def salvar_token(tok):
    PASTA.mkdir(parents=True, exist_ok=True)
    TOKEN_PATH.write_text(tok, encoding="utf-8")
    try: os.chmod(TOKEN_PATH, stat.S_IRUSR | stat.S_IWUSR)        # só o dono do arquivo lê (vale no Linux/macOS)
    except OSError: pass

def ler_token():
    try: return TOKEN_PATH.read_text(encoding="utf-8").strip() or None
    except OSError: return None

def apagar_token():
    tok = ler_token()
    if tok:
        with transacao() as c: c.execute("DELETE FROM sessoes WHERE token_hash=?", (_hash_token(tok),))
    try: TOKEN_PATH.unlink()
    except OSError: pass

def restaurar_sessao(tok, hwid):
    """Se o token é válido, é DESTE computador e o computador ainda está vinculado: devolve (id, e-mail)."""
    if not tok: return None
    with transacao() as c:
        s = c.execute("SELECT * FROM sessoes WHERE token_hash=? AND expira>?", (_hash_token(tok), agora())).fetchone()
        if s is None or s["hwid"] != hwid: return None
        if c.execute("SELECT 1 FROM dispositivos WHERE usuario_id=? AND hwid=?", (s["usuario_id"], hwid)).fetchone() is None:
            return None                                           # o computador foi desvinculado: exige login de novo
        u = c.execute("SELECT id, email FROM usuarios WHERE id=?", (s["usuario_id"],)).fetchone()
        if u is None: return None
        c.execute("UPDATE dispositivos SET ultimo_uso=? WHERE usuario_id=? AND hwid=?", (agora(), u["id"], hwid))
        return u["id"], u["email"]


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

# ---------- Edição do contorno (somar / tirar áreas) ----------
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
    if len(r.interiors) and op == "-":
        avisos.append("A área removida ficou no MEIO do lago (uma ilha). Ilhas ainda não são desviadas pela rota; "
                      "desenhe a remoção encostada na margem.")
    return simplificar([(la, lo) for lo, la in r.exterior.coords], VERTICES_ROTA, 0.3), avisos

# ---------- Rota de varredura (idêntica à Central v5) ----------
def _caminho_seguro(a, b, nos, livre_fn, cache, avisos):
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
    if dist[1] == float("inf"):
        avisos.append("Não achei caminho seguro entre dois pontos da rota; usei linha reta nesse trecho. Confira a rota no mapa.")
        return [tuple(a), tuple(b)]
    rota = []; k = 1
    while k != -1: rota.append(pontos[k]); k = ant[k]
    return rota[::-1]

def _com_desvios(pts, poly, avisos):
    if len(pts) < 2: return pts
    area_ok = prep(poly.buffer(0.1))
    livre_fn = lambda p, q: area_ok.covers(LineString([p, q]))
    nos = np.array(poly.simplify(1.5).exterior.coords)[:-1]
    cache = {}
    saida = [pts[0]]
    for p, q in zip(pts[:-1], pts[1:]):
        if math.dist(p, q) < 1e-6: continue
        if livre_fn(p, q): saida.append(q)
        else: saida += _caminho_seguro(p, q, nos, livre_fn, cache, avisos)[1:]
    return saida

def _faixas(poly, espac):
    minx, miny, maxx, maxy = poly.bounds
    altura = maxy - miny
    n = max(1, math.ceil(altura / espac))
    passo = altura / n
    pts, sentido = [], 1
    for i in range(n):
        y = miny + passo * (i + 0.5)
        inter = poly.intersection(LineString([(minx - 1, y), (maxx + 1, y)]))
        geoms = getattr(inter, "geoms", [inter])
        segs = [g for g in geoms if g.geom_type == "LineString" and g.length > COMPRIMENTO_MIN_FAIXA_M]
        if not segs: continue
        segs.sort(key=lambda s: min(s.coords[0][0], s.coords[-1][0]))
        if sentido < 0: segs = segs[::-1]
        for s in segs:
            a, b = sorted([s.coords[0], s.coords[-1]])
            pts += [(a[0], a[1]), (b[0], b[1])] if sentido > 0 else [(b[0], b[1]), (a[0], a[1])]
        sentido *= -1
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

def gerar_varredura(poly_ll, espac=ESPACAMENTO_M, margem=MARGEM_M, auto_angulo=True, parte=1, avisos=None):
    """Contorno (lat/lon) -> waypoints (lat, lon). Os avisos vão para a lista 'avisos' (em vez de variável global)."""
    avisos = avisos if avisos is not None else []
    lat0 = np.mean([p[0] for p in poly_ll]); lon0 = np.mean([p[1] for p in poly_ll])
    kx, ky = m_lon(lat0), M_LAT
    to_xy = lambda lat, lon: ((lon - lon0) * kx, (lat - lat0) * ky)
    to_ll = lambda x, y: (lat0 + y / ky, lon0 + x / kx)
    base = Polygon([to_xy(*p) for p in poly_ll])
    if not base.is_valid: base = base.buffer(0)
    encolhido = base.buffer(-margem)
    partes = sorted([g for g in getattr(encolhido, "geoms", [encolhido]) if g.geom_type == "Polygon" and g.area > 1.0],
                    key=lambda g: g.area, reverse=True)
    if not partes:
        raise ValueError("Contorno pequeno demais para a margem escolhida. Diminua a margem da parede.")
    if len(partes) > 1:
        areas = ", ".join(f"{g.area:.0f} m²" for g in partes[:6])
        avisos.append(f"O lago ficou dividido em {len(partes)} partes sem ligação por água (áreas: {areas}). "
                      f"Esta rota varre só a parte {min(max(parte, 1), len(partes))} (a 1 é a maior). "
                      f"Para varrer outra, mude 'Parte do lago' e calcule de novo; o barco precisa ser levado até lá.")
    poly = partes[min(max(parte, 1), len(partes)) - 1]
    ang = _melhor_angulo(poly, espac) if auto_angulo else 0
    pr = rotate(poly, -ang, origin=(0, 0))
    pts = _faixas(pr, espac)
    pts = _com_desvios(pts, pr, avisos)
    pts = _enxugar(pts)
    t = math.radians(ang); c, s = math.cos(t), math.sin(t)
    return [to_ll(x * c - y * s, x * s + y * c) for x, y in pts]

def comprimento_rota_m(wps):
    if len(wps) < 2: return 0.0
    lat0 = float(np.mean([w[0] for w in wps]))
    kx = m_lon(lat0)
    return sum(math.hypot((b[1] - a[1]) * kx, (b[0] - a[0]) * M_LAT) for a, b in zip(wps[:-1], wps[1:]))

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

def anel_do_geojson(g):
    if not g: return None
    if g.get("type") == "Polygon": aneis = [g["coordinates"][0]]
    elif g.get("type") == "MultiPolygon": aneis = [p[0] for p in g["coordinates"]]
    else: return None
    maior = max(aneis, key=_area_anel)
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
                hist=[], pontos=[], wps=None, avisos=[], v=0, params=None)

def preparar_mapa(lugar, realce):
    """Baixa a imagem do lugar escolhido, aplica o realce e acha o contorno inicial (OSM ou cor)."""
    s, n, o, l = map(float, lugar["boundingbox"])
    dlat = max((n - s) * 0.3, 0.0008); dlon = max((l - o) * 0.3, 0.0008)        # folga de 30% (mínimo ~90 m)
    s, n, o, l = s - dlat, n + dlat, o - dlon, l + dlon
    raw = baixar_satelite_cache(s, n, o, l)
    bbox = (o, l, s, n)
    anel = anel_do_geojson(lugar.get("geojson"))
    img = realcar_imagem(raw, realce)
    if anel: poly = simplificar(anel, VERTICES_ROTA, 0.3)
    else: poly = contorno_automatico(np.asarray(img), float(lugar["lon"]), float(lugar["lat"]), TOL_PADRAO, bbox)
    return novo_mapa(raw, bbox, lugar.get("display_name", "lago"), poly, realce)


# =====================================================================
#   PARTE C - ROBÔ (UDP)
# =====================================================================
class Robo:
    """Guarda o que sabemos do robô e envia/recebe mensagens UDP (uma thread escuta o tempo todo)."""
    def __init__(self):
        self.lock = threading.Lock()
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(("0.0.0.0", PORTA_CENTRAL))
        self.ip = None; self.ultimo_s = 0.0
        self.pos = None
        self.estado = "?"; self.wp = 0; self.sats = 0; self.bat = 0.0; self.rumo = 0.0; self.cal = False
        self.leituras = []                  # (lat, lon, turb, ph, bloom)
        self.ok = None; self.fim = False; self.nocal = False
        threading.Thread(target=self._rx, daemon=True).start()

    def _rx(self):
        while True:
            try: msg, (ip, _) = self.sock.recvfrom(256)
            except OSError: return
            with self.lock: self.ip = ip
            p = msg.decode(errors="ignore").strip().split(",")
            try:
                with self.lock:
                    if p[0] == "S":
                        self.pos = (float(p[1]), float(p[2])); self.wp = int(p[3]); self.estado = p[4]; self.sats = int(p[5])
                        if len(p) > 7: self.bat = float(p[6]); self.rumo = float(p[7])
                        if len(p) > 8: self.cal = (p[8] == "1")
                        self.ultimo_s = time.time()
                    elif p[0] == "T":
                        self.leituras.append(tuple(map(float, p[1:5])) + (int(p[5]),))
                    elif p[0] in ("OK", "ERR"): self.ok = (p[0] == "OK")
                    elif p[0] == "NOCAL": self.ok = False; self.nocal = True
                    elif p[0] == "FIM": self.fim = True
            except (ValueError, IndexError):
                pass

    def foto(self):
        """Cópia segura do estado atual (para a tela desenhar sem corrida com a thread)."""
        with self.lock:
            return dict(ip=self.ip, pos=self.pos, estado=self.estado, wp=self.wp, sats=self.sats, bat=self.bat,
                        rumo=self.rumo, cal=self.cal, leituras=list(self.leituras), fim=self.fim, nocal=self.nocal,
                        idade=(time.time() - self.ultimo_s) if self.ultimo_s else None)

    def enviar(self, texto):
        if self.ip: self.sock.sendto(texto.encode(), (self.ip, PORTA_ROBO))

    def enviar_missao(self, poly, wps):
        for _ in range(3):                                          # UDP pode perder pacotes
            self.ok = None
            self.enviar("CLR"); time.sleep(0.05)
            for i, (la, lo) in enumerate(poly): self.enviar(f"V,{i},{la:.7f},{lo:.7f}"); time.sleep(0.01)
            for i, (la, lo) in enumerate(wps):  self.enviar(f"W,{i},{la:.7f},{lo:.7f}"); time.sleep(0.01)
            self.enviar(f"GO,{len(poly)},{len(wps)}")
            t0 = time.time()
            while self.ok is None and time.time() - t0 < 3: time.sleep(0.1)
            if self.ok: return True
            if self.nocal: return False
        return False

@st.cache_resource
def obter_robo():
    """Só UM Robo (e uma porta UDP aberta) para todo o app, mesmo com o Streamlit recarregando a página."""
    return Robo()


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

def renderizar_mapa(M, view, poly=None, wps=None, pontos=(), pos=None, leituras=None, largura_px=1350):
    """Desenha o mapa ocupando a figura INTEIRA (sem margens) para que pixel -> lat/lon seja uma regra de três."""
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
    if wps:
        ax.plot([w[1] for w in wps], [w[0] for w in wps], "-", color="#00e5ff", lw=0.9, alpha=0.9, label="Rota")
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


# =====================================================================
#   PARTE E - INTERFACE STREAMLIT
# =====================================================================
PASSOS = ["1 · Conta", "2 · Lago e imagem", "3 · Contorno e rota", "4 · Robô ao vivo"]

def ir_para(i):
    """Usado em botões 'Continuar': muda o passo selecionado no menu lateral."""
    st.session_state["nav"] = PASSOS[i]

def usuario(): return st.session_state.get("usuario")

def licenciado():
    u = usuario()
    return bool(u and chave_do_usuario(u["id"]))

def exigir_licenca():
    """Para os passos 2-4: True se o usuário está logado E tem chave. Senão mostra o que falta."""
    if not usuario():
        st.warning("Entre na sua conta para usar este passo."); st.button("Ir para o Passo 1", on_click=ir_para, args=(0,)); return False
    if not licenciado():
        st.warning("Falta ativar sua chave de licença."); st.button("Ir para o Passo 1", on_click=ir_para, args=(0,)); return False
    return True

def ativar_sessao(uid, email):
    """Marca o usuário como logado e grava o login lembrado deste computador."""
    st.session_state["usuario"] = {"id": uid, "email": email}
    st.session_state.pop("pendente", None)
    salvar_token(criar_sessao(uid, hardware_id()))

def concluir_login(uid, email):
    """Depois da senha certa: registra o computador. Devolve True se entrou, False se bateu no limite de 3."""
    r = registrar_dispositivo(uid, hardware_id(), nome_dispositivo())
    if r == "cheio":
        st.session_state["pendente"] = {"uid": uid, "email": email}
        return False
    ativar_sessao(uid, email)
    return True

def tentar_restaurar_login():
    """Na primeira execução de cada aba do navegador: se este computador já tinha login lembrado, entra direto."""
    if st.session_state.get("_restaurou"): return
    st.session_state["_restaurou"] = True
    try:
        r = restaurar_sessao(ler_token(), hardware_id())
    except Exception:
        r = None
    if r: st.session_state["usuario"] = {"id": r[0], "email": r[1]}

def sair():
    apagar_token()
    for k in ("usuario", "pendente", "M", "relatorio", "busca"): st.session_state.pop(k, None)
    st.session_state["nav"] = PASSOS[0]

def tabela_dispositivos(uid, atual):
    return [{"Computador": d["nome"] or "?", "Primeiro uso": time.strftime("%d/%m/%Y", time.localtime(d["primeiro_uso"])),
             "Último uso": time.strftime("%d/%m/%Y %H:%M", time.localtime(d["ultimo_uso"])),
             "": "← este computador" if d["hwid"] == atual else ""} for d in listar_dispositivos(uid)]

# ---------------- PASSO 1: conta ----------------
def tela_limite_dispositivos():
    """Senha certa, mas já são 3 computadores: o usuário escolhe qual desvincular."""
    p = st.session_state["pendente"]
    st.error(f"Esta conta já está em {MAX_DISPOSITIVOS} computadores. Para usar ESTE, desvincule um dos anteriores.")
    for d in listar_dispositivos(p["uid"]):
        c1, c2 = st.columns([3, 1])
        c1.write(f"**{d['nome'] or '?'}**  \núltimo uso: {time.strftime('%d/%m/%Y %H:%M', time.localtime(d['ultimo_uso']))}")
        if c2.button("Desvincular e entrar aqui", key=f"desv_{d['id']}"):
            desvincular_dispositivo(p["uid"], d["id"])
            if concluir_login(p["uid"], p["email"]): st.rerun()
    if st.button("Cancelar"): st.session_state.pop("pendente", None); st.rerun()

def passo_conta():
    st.header("Passo 1 · Sua conta")
    if st.session_state.get("pendente"): tela_limite_dispositivos(); return
    u = usuario()
    t_entrar, t_criar, t_chave = st.tabs(["Entrar", "Criar conta", "Inserir chave"])

    with t_entrar:
        if u:
            st.success(f"Você está conectado como **{u['email']}**.")
            hw = hardware_id()
            st.caption(f"ID deste computador: {hw}  ·  Limite: {MAX_DISPOSITIVOS} computadores por conta.")
            st.dataframe(tabela_dispositivos(u["id"], hw), hide_index=True)
            for d in listar_dispositivos(u["id"]):
                if d["hwid"] != hw and st.button(f"Desvincular “{d['nome'] or '?'}”", key=f"d_{d['id']}"):
                    desvincular_dispositivo(u["id"], d["id"]); st.rerun()
            st.button("Sair da conta", on_click=sair)
        else:
            with st.form("form_login"):
                email = st.text_input("E-mail"); senha = st.text_input("Senha", type="password")
                enviar = st.form_submit_button("Entrar")
            if enviar:
                uid, msg = autenticar(email, senha)
                if uid is None: st.error(msg)
                elif concluir_login(uid, email.strip().lower()): st.rerun()
                else: st.rerun()                                    # caiu no limite: mostra a tela de desvincular

    with t_criar:
        if u: st.info("Você já está conectado.")
        else:
            with st.form("form_criar"):
                email = st.text_input("E-mail", key="c_email")
                senha = st.text_input("Senha (mínimo 8 caracteres)", type="password", key="c_s1")
                senha2 = st.text_input("Repita a senha", type="password", key="c_s2")
                enviar = st.form_submit_button("Criar conta")
            if enviar:
                if senha != senha2: st.error("As senhas não são iguais.")
                else:
                    uid, msg = criar_conta(email, senha)
                    if uid is None: st.error(msg)
                    else:
                        concluir_login(uid, email.strip().lower()); st.rerun()

    with t_chave:
        if not u: st.info("Entre ou crie uma conta primeiro; depois volte aqui para ativar sua chave.")
        else:
            chave = chave_do_usuario(u["id"])
            if chave:
                st.success(f"Licença ativa. Chave: {chave[:-9]}····-{chave[-4:]}")
                st.button("Continuar para o Passo 2 →", on_click=ir_para, args=(1,), type="primary")
            else:
                st.write("Digite a chave de ativação que você recebeu. Ela fica ligada à sua conta.")
                with st.form("form_chave"):
                    txt = st.text_input("Chave de ativação", placeholder=f"{PREFIXO_CHAVE}-XXXX-XXXX-XXXX")
                    enviar = st.form_submit_button("Ativar")
                if enviar:
                    ok, msg = resgatar_chave(u["id"], txt)
                    (st.success if ok else st.error)(msg)
                    if ok: st.rerun()
                if MODO_DEMO:
                    st.caption(f"Modo demonstração: chaves de teste em `{PASTA / 'chaves_de_teste.txt'}` "
                               f"(ou gere mais com `python app.py gerar-chaves 5`).")

# ---------------- PASSO 2: lago e imagem ----------------
def painel_realce(prefixo=""):
    """Sliders do realce. Devolve o dicionário de parâmetros escolhido."""
    p = dict(REALCE_PADRAO)
    p["ativo"] = st.toggle("Realce automático ligado", value=True, key=prefixo + "r_on")
    c1, c2 = st.columns(2)
    p["brilho"] = c1.slider("Brilho", 0.6, 1.6, REALCE_PADRAO["brilho"], 0.05, key=prefixo + "r_b")
    p["contraste"] = c2.slider("Contraste", 0.6, 2.0, REALCE_PADRAO["contraste"], 0.05, key=prefixo + "r_c")
    p["cor"] = c1.slider("Cor (saturação)", 0.0, 2.5, REALCE_PADRAO["cor"], 0.05, key=prefixo + "r_s")
    p["nitidez"] = c2.slider("Nitidez", 0.0, 3.0, REALCE_PADRAO["nitidez"], 0.05, key=prefixo + "r_n")
    p["auto"] = st.slider("Autocontraste (% de pixels extremos ignorados)", 0, 5, REALCE_PADRAO["auto"], key=prefixo + "r_a")
    return p

def passo_lago():
    st.header("Passo 2 · Escolha o lago")
    if not exigir_licenca(): return
    with st.form("form_busca"):
        q = st.text_input("Nome do lago", placeholder="Lago Igapó, Londrina  (inclua a cidade)")
        buscar = st.form_submit_button("Buscar")
    if buscar and q.strip():
        try:
            with st.spinner("Buscando..."): st.session_state["busca"] = buscar_lugar_cache(q.strip())
            if not st.session_state["busca"]: st.warning("Nada encontrado. Tente incluir a cidade.")
        except Exception as e:
            st.error(f"Não consegui buscar (internet?): {e}")

    with st.expander("Realce da imagem (já vem ligado e ajustado)"):
        realce = painel_realce()

    res = st.session_state.get("busca") or []
    if res:
        nomes = [f"{r.get('display_name', '?')}  [{r.get('type', '')}]" for r in res]
        i = st.radio("Resultados", range(len(res)), format_func=lambda k: nomes[k])
        if st.button("Usar este lugar →", type="primary"):
            try:
                with st.spinner("Baixando o satélite e aplicando o realce (pode levar alguns segundos)..."):
                    M = preparar_mapa(res[i], realce)
                st.session_state["M"] = M; st.session_state.pop("relatorio", None)
                if not M["poly"]:
                    st.warning("Não achei o contorno automaticamente. No passo 3 clique na água com o modo “Detectar água por cor”.")
                    M["poly"] = None
                ir_para(2); st.rerun()
            except Exception as e:
                st.error(f"Não consegui montar o mapa: {e}")

    with st.expander("Ou usar uma imagem sua (print de satélite)"):
        arq = st.file_uploader("Imagem (PNG/JPG)", type=["png", "jpg", "jpeg"])
        c1, c2 = st.columns(2)
        lon_e = c1.number_input("Longitude esquerda (oeste)", value=-51.1700, format="%.6f")
        lon_d = c2.number_input("Longitude direita (leste)", value=-51.1600, format="%.6f")
        lat_b = c1.number_input("Latitude de baixo (sul)", value=-23.3200, format="%.6f")
        lat_c = c2.number_input("Latitude de cima (norte)", value=-23.3100, format="%.6f")
        if arq is not None and st.button("Usar esta imagem"):
            if lon_e >= lon_d or lat_b >= lat_c: st.error("Confira os cantos: oeste < leste e sul < norte.")
            else:
                raw = Image.open(arq).convert("RGB")
                st.session_state["M"] = novo_mapa(raw, (lon_e, lon_d, lat_b, lat_c), arq.name, None, realce)
                st.session_state.pop("relatorio", None)
                ir_para(2); st.rerun()

    M = st.session_state.get("M")
    if M:
        st.divider(); st.subheader(f"Mapa atual: {M['nome'][:80]}")
        if st.button("Reaplicar o realce acima ao mapa atual"):
            M["img"] = realcar_imagem(M["raw"], realce); M["v"] += 1
        st.image(M["img"])
        st.caption(CREDITOS)
        st.button("Continuar para o Passo 3 →", on_click=ir_para, args=(2,), type="primary")

# ---------------- PASSO 3: contorno e rota ----------------
MODOS = {
    "auto":  "Detectar água por cor (clique na água) — troca o contorno",
    "mais":  "➕ Adicionar área desenhando (marque os cantos)",
    "menos": "➖ Remover área desenhando (marque os cantos)",
    "maisc": "➕ Adicionar água por cor (clique na água que faltou)",
    "menosc": "➖ Remover água por cor (clique no que deve sair)",
    "novo":  "✏️ Desenhar o contorno do zero (marque os cantos)",
}

def obter_clique(img_bytes, chave):
    """Mostra o mapa e devolve o clique como (fração_x, fração_y) entre 0 e 1, ou None."""
    pil = Image.open(io.BytesIO(img_bytes)).convert("RGB")
    if streamlit_image_coordinates is not None:
        try: r = streamlit_image_coordinates(pil, width=900, key=chave)
        except TypeError: r = streamlit_image_coordinates(pil, key=chave)
        if r and r.get("width") and r.get("height"): return r["x"] / r["width"], r["y"] / r["height"]
        return None
    # Plano B (sem a biblioteca de clique): escolher o ponto por porcentagem
    st.image(pil)
    st.warning("Instale `streamlit-image-coordinates` para clicar direto no mapa. Por enquanto, informe o ponto em %.")
    c1, c2 = st.columns(2)
    fx = c1.slider("Posição horizontal (%)", 0, 100, 50, key=chave + "x"); fy = c2.slider("Posição vertical (%)", 0, 100, 50, key=chave + "y")
    return (fx / 100, fy / 100) if st.button("Marcar este ponto", key=chave + "b") else None

def guardar_historico(M):
    if M.get("poly"): M["hist"].append(list(M["poly"])); M["hist"] = M["hist"][-20:]

def tratar_clique(M, view, fx, fy, modo, tol):
    """Faz o que o modo escolhido manda com o ponto clicado."""
    o, l, s, n = view
    lon, lat = o + fx * (l - o), n - fy * (n - s)
    aviso = []
    if modo in ("mais", "menos", "novo"):
        M["pontos"].append((lat, lon)); return
    img_arr = np.asarray(M["img"])
    anel = contorno_automatico(img_arr, lon, lat, tol, M["bbox"])
    if anel is None:
        st.session_state["msg3"] = ("warning", "Não achei água nesse ponto. Clique em um lugar de água e/ou aumente a sensibilidade."); return
    guardar_historico(M)
    if modo == "auto": M["poly"] = anel
    else:
        if not M.get("poly"): M["poly"] = anel
        else: M["poly"], aviso = editar_contorno(M["poly"], "+" if modo == "maisc" else "-", anel)
    M["wps"] = None
    if aviso: st.session_state["msg3"] = ("warning", " ".join(aviso))

def aplicar_pontos(M, modo):
    pts = M["pontos"]
    if len(pts) < 3: st.session_state["msg3"] = ("warning", "Marque pelo menos 3 pontos."); return
    guardar_historico(M)
    if modo == "novo": M["poly"] = simplificar(pts, VERTICES_ROTA, 0.3); aviso = []
    elif not M.get("poly"): M["poly"] = simplificar(pts, VERTICES_ROTA, 0.3); aviso = []
    else: M["poly"], aviso = editar_contorno(M["poly"], "+" if modo == "mais" else "-", pts)
    M["pontos"] = []; M["wps"] = None
    if aviso: st.session_state["msg3"] = ("warning", " ".join(aviso))

def passo_contorno():
    st.header("Passo 3 · Contorno e rota de varredura")
    if not exigir_licenca(): return
    M = st.session_state.get("M")
    if not M:
        st.info("Escolha um lago no Passo 2 primeiro."); st.button("Ir para o Passo 2", on_click=ir_para, args=(1,)); return
    msg = st.session_state.pop("msg3", None)
    if msg: getattr(st, msg[0])(msg[1])

    col_mapa, col_ctl = st.columns([3, 2])
    with col_ctl:
        st.subheader("Contorno")
        modo = st.selectbox("Ferramenta", list(MODOS), format_func=lambda k: MODOS[k], key="modo3")
        tol = st.slider("Sensibilidade da detecção por cor", 10, 120, TOL_PADRAO, 1,
                        help="Maior = considera mais pixels como água. Aumente se o lago ficou incompleto; diminua se vazou para a terra.")
        zoom = st.toggle("Zoom no lago", value=True)
        if modo in ("mais", "menos", "novo"):
            st.caption(f"Pontos marcados: {len(M['pontos'])}. Clique no mapa para marcar os cantos, depois aplique.")
            b1, b2, b3 = st.columns(3)
            if b1.button("Aplicar"): aplicar_pontos(M, modo); M["v"] += 1; st.rerun()
            if b2.button("Desfazer ponto") and M["pontos"]: M["pontos"].pop(); M["v"] += 1; st.rerun()
            if b3.button("Limpar") and M["pontos"]: M["pontos"] = []; M["v"] += 1; st.rerun()
        b1, b2 = st.columns(2)
        if b1.button("↩ Desfazer edição") and M["hist"]:
            M["poly"] = M["hist"].pop(); M["wps"] = None; M["v"] += 1; st.rerun()
        if b2.button("Voltar ao contorno original") and M.get("poly0"):
            guardar_historico(M); M["poly"] = list(M["poly0"]); M["wps"] = None; M["v"] += 1; st.rerun()
        if M.get("poly"): st.caption(f"Contorno com {len(M['poly'])} pontos (o robô recebe no máximo {MAX_VERTICES}).")
        else: st.warning("Ainda não há contorno. Use “Detectar água por cor” e clique na água.")

        st.subheader("Rota")
        espac = st.number_input("Espaçamento entre faixas (m)", 0.10, 5.0, float(ESPACAMENTO_M), 0.05,
                                help=f"Robô de {LARGURA_ROBO_M*100:.0f} cm com {SOBREPOSICAO*100:.0f}% de sobreposição = {ESPACAMENTO_M} m.")
        margem = st.number_input("Margem da parede (m)", 0.0, 30.0, float(MARGEM_M), 0.5,
                                 help="O barco não chega mais perto da margem que isso (o GPS erra alguns metros).")
        auto = st.checkbox("Escolher sozinho a melhor direção das faixas", value=True)
        parte = st.number_input("Parte do lago (1 = a maior)", 1, 9, 1, 1)
        if st.button("Calcular rota", type="primary", disabled=not M.get("poly")):
            avisos = []
            try:
                with st.spinner("Calculando a rota..."):
                    M["wps"] = gerar_varredura(M["poly"], espac, margem, auto, int(parte), avisos)
                M["avisos"] = avisos; M["params"] = (espac, margem)
            except Exception as e:
                M["wps"] = None; st.error(str(e))
            M["v"] += 1; st.rerun()
        for a in M.get("avisos", []): st.warning(a)
        if M.get("wps"):
            w = M["wps"]; comp = comprimento_rota_m(w)
            m1, m2 = st.columns(2); m1.metric("Waypoints", len(w)); m2.metric("Percurso", f"{comp:.0f} m")
            if len(w) > MAX_WAYPOINTS:
                sug = espac * len(w) / MAX_WAYPOINTS * 1.05
                st.error(f"São {len(w)} waypoints e o robô aceita {MAX_WAYPOINTS}. Aumente o espaçamento para cerca de {sug:.2f} m.")
            else:
                st.success("Rota pronta.")
                st.button("Continuar para o Passo 4 (robô) →", on_click=ir_para, args=(3,), type="primary")

    with col_mapa:
        view = janela_de_visao(M, zoom)
        png = renderizar_mapa(M, view, poly=M.get("poly"), wps=M.get("wps"), pontos=M["pontos"])
        clique = obter_clique(png, f"mapa_{M['v']}")
        if clique:
            try: tratar_clique(M, view, clique[0], clique[1], modo, tol)
            except Exception as e: st.session_state["msg3"] = ("error", f"Erro na edição: {e}")
            M["v"] += 1; st.rerun()                       # troca a chave do componente: o clique antigo não é lido de novo
        st.caption("Dica: ➕/➖ por cor é o jeito mais rápido de consertar um pedaço. Amarelo = parede virtual, ciano = rota.")

# ---------------- PASSO 4: robô ao vivo ----------------
def log_robo(texto):
    st.session_state.setdefault("log4", []).append(f"{time.strftime('%H:%M:%S')}  {texto}")
    st.session_state["log4"] = st.session_state["log4"][-30:]

def controles_robo(robo, M):
    st.subheader("Comandos")
    f = robo.foto()
    tem_rota = bool(M.get("wps")) and len(M["wps"]) <= MAX_WAYPOINTS
    if f["ip"] is None: st.warning("Ainda não achei o robô na rede (ligue o robô e confira o Wi-Fi).")
    if not tem_rota: st.warning("Falta uma rota válida (Passo 3).")

    if st.button("▶ INICIAR varredura", type="primary", disabled=not (tem_rota and f["ip"])):
        if not f["cal"] or f["estado"] in ("CALIBRANDO", "CALIBRATING"):
            log_robo("Espere a calibração da bússola terminar (ou calibre abaixo)."); st.error("Bússola não calibrada.")
        else:
            robo.nocal = False; robo.fim = False
            with st.spinner("Enviando a missão ao robô..."):
                ok = robo.enviar_missao(simplificar(M["poly"], MAX_VERTICES, 0.5), M["wps"])
            if ok: log_robo("Varredura iniciada!"); st.success("Varredura iniciada!")
            else:
                log_robo("Falha ao enviar a missão."); st.error(f"O robô não confirmou. Confira o Wi-Fi, a calibração e se o MAX_W do firmware é {MAX_WAYPOINTS}.")
    c1, c2 = st.columns(2)
    if c1.button("■ PARAR", disabled=not f["ip"]): robo.enviar("STOP"); log_robo("STOP enviado.")
    if c2.button("⌂ VOLTAR", disabled=not f["ip"]): robo.enviar("HOME"); log_robo("Pedi ao robô para voltar ao início.")

    with st.expander("Calibrar bússola"):
        modo = st.radio("Como calibrar", [0, 1], format_func=lambda m: "O barco gira sozinho" if m == 0 else "Eu giro o barco devagar em círculo por 20 s")
        ok = st.checkbox("O barco está na água, em espaço livre, e posso soltá-lo")
        if st.button("Calibrar agora", disabled=not (ok and f["ip"])):
            robo.enviar(f"CAL,{modo}"); log_robo(f"Calibração iniciada (CAL,{modo}).")

    with st.expander("Varredura densa (foco crítico)"):
        raio = st.number_input("Raio (m)", 2.0, 50.0, 15.0, 1.0); esp = st.number_input("Espaçamento (m)", 0.5, 10.0, 3.0, 0.5)
        d1, d2 = st.columns(2)
        if d1.button("Ligar", disabled=not f["ip"]): robo.enviar(f"DENSO,1,{raio:.1f},{esp:.1f}"); log_robo("DENSO ligado.")
        if d2.button("Desligar", disabled=not f["ip"]): robo.enviar(f"DENSO,0,{raio:.1f},{esp:.1f}"); log_robo("DENSO desligado.")

    st.subheader("Relatório")
    if st.button("Gerar relatório"):
        r = relatorio(robo.foto()["leituras"], M, janela_de_visao(M, True))
        if r is None: st.info("Ainda não há leituras do robô.")
        else: st.session_state["relatorio"] = r
    r = st.session_state.get("relatorio")
    if r:
        st.text(r[0])
        a, b, c = st.columns(3)
        a.download_button("CSV", r[1], "bioglow_leituras.csv", "text/csv")
        b.download_button("Mapa PNG", r[2], "bioglow_mapa.png", "image/png")
        c.download_button("Texto", r[0].encode("utf-8"), "bioglow_relatorio.txt", "text/plain")
    for linha in reversed(st.session_state.get("log4", [])[-6:]): st.caption(linha)

def _painel_vivo(robo, M):
    f = robo.foto()
    if f["idade"] is None: st.info("Aguardando o primeiro sinal do robô...")
    elif f["idade"] > 5: st.warning(f"Sem sinal do robô há {f['idade']:.0f} s.")
    if f["fim"]: st.success("O robô avisou: missão concluída (FIM).")
    a, b, c, d = st.columns(4)
    a.metric("Estado", f["estado"]); b.metric("Bateria", f"{f['bat']:.1f} V")
    c.metric("Rumo", f"{f['rumo']:.0f}°"); d.metric("Satélites GPS", f["sats"])
    e, g, h, i = st.columns(4)
    n_w = len(M["wps"] or [])
    e.metric("Waypoint", f"{f['wp']}/{n_w}")
    e.progress(min(f["wp"] / n_w, 1.0) if n_w else 0.0)
    g.metric("Bússola", "calibrada" if f["cal"] else "NÃO calibrada")
    ult = f["leituras"][-1] if f["leituras"] else None
    h.metric("Turbidez", f"{ult[2]:.0f}" if ult else "—"); i.metric("pH", f"{ult[3]:.2f}" if ult else "—")
    if f["pos"]: st.caption(f"GPS: {f['pos'][0]:.6f}, {f['pos'][1]:.6f}")
    png = renderizar_mapa(M, janela_de_visao(M, True), poly=M.get("poly"), wps=M.get("wps"), pos=f["pos"],
                          leituras=f["leituras"], largura_px=1100)
    st.image(png)
    anom = [x for x in f["leituras"] if x[4] == 1]
    st.caption(f"{len(f['leituras'])} leituras · {len(anom)} anomalias confirmadas")
    if anom:
        st.dataframe([{"lat": x[0], "lon": x[1], "turbidez": x[2], "pH": x[3]} for x in anom[-10:]], hide_index=True)

_fragmento = getattr(st, "fragment", None)
if _fragmento:
    painel_vivo = _fragmento(run_every=1.5)(_painel_vivo)       # só esta parte se atualiza sozinha a cada 1,5 s
else:
    painel_vivo = _painel_vivo                                   # Streamlit antigo: atualiza com o botão abaixo

def passo_robo():
    st.header("Passo 4 · Robô em tempo real")
    if not exigir_licenca(): return
    M = st.session_state.get("M")
    if not M or not M.get("poly"):
        st.info("Faça o contorno e a rota (Passos 2 e 3) primeiro."); st.button("Ir para o Passo 3", on_click=ir_para, args=(2,)); return
    try: robo = obter_robo()
    except OSError as e:
        st.error(f"Não consegui abrir a porta UDP {PORTA_CENTRAL} (outra Central aberta?): {e}"); return
    col_ctl, col_live = st.columns([1, 2])
    with col_ctl: controles_robo(robo, M)
    with col_live:
        painel_vivo(robo, M)
        if not _fragmento: st.button("Atualizar agora")

# ---------------- app principal ----------------
def main():
    st.set_page_config(page_title="BioGlow · Central", page_icon="🌿", layout="wide")
    init_db()
    tentar_restaurar_login()
    st.session_state.setdefault("nav", PASSOS[0])
    with st.sidebar:
        st.title("🌿 BioGlow")
        st.caption("Central do robô AquaSentry")
        st.radio("Passos", PASSOS, key="nav")
        st.divider()
        u = usuario()
        if u:
            st.write(f"👤 {u['email']}")
            st.write("🔑 Licença ativa" if licenciado() else "🔑 Sem chave ativada")
            st.button("Sair", on_click=sair, key="sair_lateral")
        else: st.write("Você não está conectado.")
        st.caption(f"Computador: {hardware_id()}")
    {PASSOS[0]: passo_conta, PASSOS[1]: passo_lago, PASSOS[2]: passo_contorno, PASSOS[3]: passo_robo}[st.session_state["nav"]]()


def _fora_do_streamlit():
    try:
        from streamlit.runtime.scriptrunner import get_script_run_ctx
        try: return get_script_run_ctx(suppress_warning=True) is None
        except TypeError: return get_script_run_ctx() is None
    except Exception:
        return True

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "gerar-chaves":          # python app.py gerar-chaves 5
        init_db()
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 1
        print("Chaves criadas no banco:", DB_PATH)
        for k in gerar_chaves(n): print("  ", k)
    elif _fora_do_streamlit():
        print("Este arquivo é um app Streamlit. Rode:  streamlit run app.py   (ou: python -m streamlit run app.py)")
    else:
        main()
