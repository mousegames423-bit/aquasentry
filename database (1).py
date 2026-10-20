"""database.py - Banco de dados e contas (SQLite).

Contas com senha PBKDF2, chaves de ativação, limite de dispositivos, identidade do navegador (cookies), fuso horário
e sessões persistentes. Não depende dos outros módulos do projeto.
"""

import hashlib
import hmac
import json
import os
import platform
import re
import secrets
import sqlite3
import stat
import time
import uuid
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from pathlib import Path
try:
    from zoneinfo import ZoneInfo
except ImportError:
    ZoneInfo = None

import streamlit as st
import streamlit.components.v1 as components

# --- Contas e licenças ---
APP_NOME = "BioGlow"

PREFIXO_CHAVE = "BIOGLOW-FLL2026"      # começo de toda chave de ativação

MAX_DISPOSITIVOS = 3                   # computadores por conta

SESSAO_DIAS = 30                       # quanto tempo o login "lembrado" vale

MAX_FALHAS_LOGIN = 5                   # erros de senha seguidos até bloquear

BLOQUEIO_LOGIN_S = 300                 # tempo do bloqueio (5 min)

PBKDF2_ITER = 200_000                  # "dificuldade" do hash da senha (maior = mais seguro e mais lento)

# MODO HOSPEDADO (Railway, Render, etc.): o servidor atende VÁRIAS pessoas ao mesmo tempo.
# Então NADA de login/computador pode ficar guardado em arquivo do servidor: cada navegador guarda o seu
# próprio "crachá" (cookie). Liga sozinho no Railway; para forçar: BIOGLOW_HOSTED=1.
HOSTED = (os.environ.get("BIOGLOW_HOSTED") == "1" or "RAILWAY_ENVIRONMENT" in os.environ
          or "RAILWAY_PROJECT_ID" in os.environ)

# O robô está no Wi-Fi do lago; um servidor na internet NÃO alcança ele por UDP. Painel do robô só no modo local
# (ou BIOGLOW_ROBO=1 se o servidor estiver na mesma rede do robô).
ROBO_DISPONIVEL = (not HOSTED) or os.environ.get("BIOGLOW_ROBO") == "1"

# Modo demonstração: se não existir nenhuma chave, o app cria 3 e MOSTRA onde achá-las (só no modo local).
# Para uso comercial real: BIOGLOW_DEMO=0 e entregue as chaves só aos clientes.
MODO_DEMO = os.environ.get("BIOGLOW_DEMO", "0" if HOSTED else "1") == "1"


# Pasta onde ficam banco de dados, sessão e cache de mapas (pode trocar com a variável BIOGLOW_DIR)
_VOLUME = os.environ.get("RAILWAY_VOLUME_MOUNT_PATH")            # o Railway preenche isto sozinho quando há um Volume

PASTA = Path(os.environ.get("BIOGLOW_DIR") or _VOLUME or Path.home() / ".bioglow")

ARMAZENAMENTO_PERMANENTE = bool(os.environ.get("BIOGLOW_DIR") or _VOLUME or not HOSTED)   # sem volume, o Railway apaga tudo a cada deploy

DB_PATH = Path(os.environ.get("BIOGLOW_DB") or PASTA / "bioglow_contas.db")

TOKEN_PATH = PASTA / "sessao.token"

TILES_DIR = PASTA / "tiles"

CREDITOS = "Imagens © Esri e colaboradores  |  Dados de lugares © OpenStreetMap contributors"


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
        c.execute("""CREATE TABLE IF NOT EXISTS usuarios(
            id INTEGER PRIMARY KEY AUTOINCREMENT, email TEXT UNIQUE NOT NULL, sal TEXT NOT NULL, hash TEXT NOT NULL,
            criado INTEGER NOT NULL, falhas INTEGER NOT NULL DEFAULT 0, bloqueado_ate INTEGER NOT NULL DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS chaves(
            chave TEXT PRIMARY KEY, criada INTEGER NOT NULL, usuario_id INTEGER, resgatada_em INTEGER)""")
        c.execute("""CREATE TABLE IF NOT EXISTS dispositivos(
            id INTEGER PRIMARY KEY AUTOINCREMENT, usuario_id INTEGER NOT NULL, hwid TEXT NOT NULL, nome TEXT,
            primeiro_uso INTEGER NOT NULL, ultimo_uso INTEGER NOT NULL, UNIQUE(usuario_id, hwid))""")
        if "renomeado" not in [r["name"] for r in c.execute("PRAGMA table_info(dispositivos)")]:
            c.execute("ALTER TABLE dispositivos ADD COLUMN renomeado INTEGER NOT NULL DEFAULT 0")   # nome escolhido pelo usuário
        c.execute("""CREATE TABLE IF NOT EXISTS sessoes(
            token_hash TEXT PRIMARY KEY, usuario_id INTEGER NOT NULL, hwid TEXT NOT NULL,
            criada INTEGER NOT NULL, expira INTEGER NOT NULL)""")
    # Chaves entregues pela variável de ambiente BIOGLOW_CHAVES (separadas por vírgula). Útil no Railway, onde
    # não há terminal: o app cadastra no banco as chaves que ainda não existem (as já usadas ficam como estão).
    with transacao() as c:
        for k in re.split(r"[,\s;]+", os.environ.get("BIOGLOW_CHAVES", "")):
            k = normalizar_chave(k)
            if k and formato_chave_ok(k): c.execute("INSERT OR IGNORE INTO chaves(chave, criada) VALUES(?,?)", (k, agora()))
    if MODO_DEMO and not HOSTED:
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
def ler_cookie(nome):
    """Cookie que o NAVEGADOR deste visitante mandou (st.context.cookies existe no Streamlit >= 1.37)."""
    try: return st.context.cookies.get(nome)
    except Exception: return None


def pedir_cookie(nome, valor, dias):
    """Anota que este navegador deve gravar o cookie (dias=0 apaga). Quem grava é emitir_cookies()."""
    st.session_state.setdefault("_cookies", {})[nome] = (valor, dias)


def emitir_cookies():
    """Grava os cookies pedidos no navegador de QUEM está usando (pequeno JavaScript invisível)."""
    pend = st.session_state.get("_cookies")
    if not pend: return
    cmds = "".join(
        f'd.cookie = {json.dumps(nome)} + "=" + {json.dumps(valor)} + "; max-age={int(dias * 86400)}; path=/; SameSite=Lax"'
        f' + (window.parent.location.protocol === "https:" ? "; Secure" : "");'
        for nome, (valor, dias) in pend.items())
    components.html(f"<script>try {{ const d = window.parent.document; {cmds} }} catch (e) {{}}</script>", height=0)


def iniciar_identidade():
    """Modo hospedado: cada navegador recebe um ID aleatório próprio (cookie). Ele faz o papel de 'computador'."""
    if not HOSTED or "_dev" in st.session_state: return
    d = ler_cookie("bioglow_dev")
    if not (d and re.fullmatch(r"[0-9A-F]{16}", d)): d = secrets.token_hex(8).upper()
    st.session_state["_dev"] = d
    pedir_cookie("bioglow_dev", d, 3650)


def hardware_id():
    """ID estável deste computador (local) ou deste navegador (hospedado)."""
    if HOSTED: return "WEB-" + (st.session_state.get("_dev") or "SEM-ID")
    mac = uuid.getnode()
    if (mac >> 40) & 1:                                   # bit "aleatório": o Python não achou um MAC de verdade
        arq = PASTA / "hwid.txt"                          # então guardamos um número aleatório fixo neste computador
        PASTA.mkdir(parents=True, exist_ok=True)
        if not arq.exists(): arq.write_text(uuid.uuid4().hex, encoding="utf-8")
        mac = arq.read_text(encoding="utf-8").strip()
    bruto = "|".join([str(mac), platform.system(), platform.machine(), platform.node()])
    return hashlib.sha256(bruto.encode()).hexdigest()[:16].upper()


def descrever_aparelho(ua, ch_mobile="", ch_plataforma=""):
    """Texto tipo 'Tablet Android · Chrome' a partir do User-Agent (e das dicas Sec-CH-UA, quando o navegador manda)."""
    plat = (ch_plataforma or "").strip('"')
    movel = ch_mobile == "?1"
    if "iPad" in ua: tipo, so = "Tablet", "iPadOS"
    elif "iPhone" in ua or "iPod" in ua: tipo, so = "Celular", "iOS"
    elif "Android" in ua or plat == "Android":
        so = "Android"; tipo = "Celular" if ("Mobile" in ua or movel) else "Tablet"      # Android sem "Mobile" = tablet
    elif "CrOS" in ua: tipo, so = "Computador", "ChromeOS"
    elif "Windows" in ua: tipo, so = "Computador", "Windows"
    elif "Macintosh" in ua or "Mac OS" in ua: tipo, so = "Mac ou iPad", ""       # o iPad em "site para computador" se disfarça de Mac
    elif "Linux" in ua or "X11" in ua: tipo, so = ("Celular" if movel else "Computador"), "Linux"
    else: tipo, so = "Aparelho", "?"
    nav = next((nome for chave, nome in (("Edg", "Edge"), ("OPR", "Opera"), ("SamsungBrowser", "Samsung Internet"),
                                         ("Firefox", "Firefox"), ("FxiOS", "Firefox"), ("CriOS", "Chrome"),
                                         ("Chrome", "Chrome"), ("Safari", "Safari")) if chave in ua), "navegador")
    return f"{tipo} {so} · {nav}".replace("  ", " ")


def nome_dispositivo():
    if HOSTED:
        try:
            h = st.context.headers
            return descrever_aparelho(h.get("User-Agent", ""), h.get("Sec-CH-UA-Mobile", ""), h.get("Sec-CH-UA-Platform", ""))
        except Exception:
            return "Aparelho · navegador"
    return f"Computador {platform.system()} · {platform.node() or '?'}"


# ---------- horário LOCAL de quem está usando (o servidor do Railway fica em UTC) ----------
def fuso_do_usuario():
    """Fuso do navegador do visitante (st.context.timezone). Plano B: BIOGLOW_TZ, depois Brasília (UTC-3)."""
    try:
        nome = st.context.timezone
        if nome and ZoneInfo: return ZoneInfo(nome)
    except Exception: pass
    try:
        off = st.context.timezone_offset                  # minutos, no estilo do JavaScript: Brasília = 180
        if off is not None: return timezone(timedelta(minutes=-int(off)))
    except Exception: pass
    try: return ZoneInfo(os.environ.get("BIOGLOW_TZ", "America/Sao_Paulo"))
    except Exception: return timezone(timedelta(hours=-3))


def hora_local(ts, fmt="%d/%m/%Y %H:%M"):
    return datetime.fromtimestamp(ts, fuso_do_usuario()).strftime(fmt)


def registrar_dispositivo(uid, hwid, nome):
    """Registra este computador na conta. Devolve 'ok' (já era), 'novo' (registrado agora) ou 'cheio' (limite atingido)."""
    with transacao() as c:
        r = c.execute("SELECT id FROM dispositivos WHERE usuario_id=? AND hwid=?", (uid, hwid)).fetchone()
        if r:
            c.execute("UPDATE dispositivos SET ultimo_uso=?, nome=CASE WHEN renomeado=1 THEN nome ELSE ? END WHERE id=?",
                      (agora(), nome, r["id"]))                      # nome escolhido pelo usuário não é sobrescrito
            return "ok"
        n = c.execute("SELECT COUNT(*) AS n FROM dispositivos WHERE usuario_id=?", (uid,)).fetchone()["n"]
        if n >= MAX_DISPOSITIVOS: return "cheio"
        c.execute("INSERT INTO dispositivos(usuario_id, hwid, nome, primeiro_uso, ultimo_uso) VALUES(?,?,?,?,?)",
                  (uid, hwid, nome, agora(), agora()))
        return "novo"


def listar_dispositivos(uid):
    with transacao() as c:
        return [dict(r) for r in c.execute("SELECT * FROM dispositivos WHERE usuario_id=? ORDER BY primeiro_uso", (uid,))]


def renomear_dispositivo(uid, dev_id, novo):
    novo = " ".join((novo or "").split())[:40]
    if not novo: return False
    with transacao() as c:
        c.execute("UPDATE dispositivos SET nome=?, renomeado=1 WHERE id=? AND usuario_id=?", (novo, dev_id, uid))
    return True


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
    if HOSTED:                                                    # nunca em arquivo do servidor: seria de todos os visitantes
        st.session_state["_tok"] = tok; pedir_cookie("bioglow_tok", tok, SESSAO_DIAS); return
    PASTA.mkdir(parents=True, exist_ok=True)
    TOKEN_PATH.write_text(tok, encoding="utf-8")
    try: os.chmod(TOKEN_PATH, stat.S_IRUSR | stat.S_IWUSR)        # só o dono do arquivo lê (vale no Linux/macOS)
    except OSError: pass


def ler_token():
    if HOSTED:
        if "_tok" in st.session_state: return st.session_state["_tok"] or None
        return ler_cookie("bioglow_tok")
    try: return TOKEN_PATH.read_text(encoding="utf-8").strip() or None
    except OSError: return None


def apagar_token():
    tok = ler_token()
    if tok:
        with transacao() as c: c.execute("DELETE FROM sessoes WHERE token_hash=?", (_hash_token(tok),))
    if HOSTED:
        st.session_state["_tok"] = ""; pedir_cookie("bioglow_tok", "", 0); return
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
