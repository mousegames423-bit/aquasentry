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
#
# Estrutura do projeto (5 arquivos na mesma pasta):
#   app.py       - esta interface (Streamlit): main(), barra lateral, passos 1-4 e botões (callbacks)
#   database.py  - SQLite: contas, chaves de ativação, dispositivos, sessões e identidade do navegador
#   robo_udp.py  - comunicação UDP com o robô (classe Robo e obter_robo)
#   geo_mapa.py  - imagem, contorno do lago, ilhas, shapely, desenho do mapa, relatório
#   rotas.py     - Dijkstra, varredura, borda + meio, divisão por waypoints, rota manual, estimativa de tempo
# =====================================================================

import io
import sys
import time
from pathlib import Path

from PIL import Image
import numpy as np
import streamlit as st
try:                                                   # biblioteca que devolve o lugar clicado na imagem
    from streamlit_image_coordinates import streamlit_image_coordinates
except ImportError:
    streamlit_image_coordinates = None

from database import (
    ARMAZENAMENTO_PERMANENTE, CREDITOS, DB_PATH, HOSTED, MAX_DISPOSITIVOS, MODO_DEMO,
    PASTA, PREFIXO_CHAVE, ROBO_DISPONIVEL, apagar_token, autenticar, chave_do_usuario,
    criar_conta, criar_sessao, desvincular_dispositivo, emitir_cookies, fuso_do_usuario, gerar_chaves,
    hardware_id, hora_local, iniciar_identidade, init_db, ler_token, listar_dispositivos,
    nome_dispositivo, registrar_dispositivo, renomear_dispositivo, resgatar_chave, restaurar_sessao, salvar_token,
)
from robo_udp import PORTA_CENTRAL, obter_robo
from geo_mapa import (
    ILHA_MIN_M2, MAX_VERTICES, M_LAT, REALCE_PADRAO, TOL_PADRAO, VERTICES_ROTA,
    _png_simples, buscar_lugar_cache, completar_contorno, contorno_automatico, contorno_hibrido, detectar_ilhas,
    editar_contorno, garantir_mapa, ilhas_depois_de_editar, janela_de_visao, limpar_contorno, m_lon,
    mapa_em_cache, novo_mapa, preparar_mapa, realcar_imagem, refinar_area, relatorio,
    removidos_depois_de_editar, renderizar_mapa, restaurar_mapa, salvar_mapa, simplificar, zonas_proibidas,
)
from rotas import (
    ESPACAMENTO_M, LARGURA_ROBO_M, MARGEM_M, MAX_WAYPOINTS, SOBREPOSICAO, dividir_rota,
    estimar_missao, formatar_duracao, gerar_borda_e_miolo, gerar_varredura, rota_manual, varredura_que_cabe,
)

# =====================================================================
#   PARTE E - INTERFACE STREAMLIT
# =====================================================================
PASSOS = ["1 · Conta", "2 · Lago e imagem", "3 · Contorno e rota", "4 · Robô ao vivo"]


def ir_para(i):
    """Pede para trocar de passo. O Streamlit só deixa mexer no menu ANTES dele ser desenhado,
    então só anotamos o pedido; a função main() aplica no começo da próxima execução."""
    st.session_state["_ir"] = i


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
    st.session_state["_ir"] = 0


def tabela_dispositivos(uid, atual):
    return [{"Aparelho": d["nome"] or "?", "Primeiro uso": hora_local(d["primeiro_uso"], "%d/%m/%Y"),
             "Último uso": hora_local(d["ultimo_uso"]),
             "": "← este aparelho" if d["hwid"] == atual else ""} for d in listar_dispositivos(uid)]


# ---------------- PASSO 1: conta ----------------
def tela_limite_dispositivos():
    """Senha certa, mas já são 3 computadores: o usuário escolhe qual desvincular."""
    p = st.session_state["pendente"]
    st.error(f"Esta conta já está em {MAX_DISPOSITIVOS} aparelhos. Para usar ESTE, desvincule um dos anteriores.")
    for d in listar_dispositivos(p["uid"]):
        c1, c2 = st.columns([3, 1])
        c1.write(f"**{d['nome'] or '?'}**  \núltimo uso: {hora_local(d['ultimo_uso'])}")
        if c2.button("Desvincular e entrar aqui", key=f"desv_{d['id']}"):
            desvincular_dispositivo(p["uid"], d["id"])
            if concluir_login(p["uid"], p["email"]): st.rerun()
    if st.button("Cancelar"): st.session_state.pop("pendente", None); st.rerun()


def passo_conta():
    st.header("Passo 1 · Sua conta")
    if not ARMAZENAMENTO_PERMANENTE:
        st.warning("Aviso para o administrador: este servidor está sem armazenamento permanente. As contas e chaves SOMEM a cada "
                   "novo deploy. No Railway, crie um Volume (Settings → Volumes); o app usa ele automaticamente.")
    if st.session_state.get("pendente"): tela_limite_dispositivos(); return
    u = usuario()
    t_entrar, t_criar, t_chave = st.tabs(["Entrar", "Criar conta", "Inserir chave"])

    with t_entrar:
        if u:
            st.success(f"Você está conectado como **{u['email']}**.")
            hw = hardware_id()
            st.caption(f"ID deste aparelho: {hw}  ·  Limite: {MAX_DISPOSITIVOS} aparelhos por conta. Entre com o mesmo e-mail e senha em qualquer outro aparelho.")
            st.dataframe(tabela_dispositivos(u["id"], hw), hide_index=True)
            with st.expander("Renomear aparelhos (ex.: “Tablet do laboratório”)"):
                for d in listar_dispositivos(u["id"]):
                    c1, c2 = st.columns([3, 1])
                    novo = c1.text_input("Nome", value=d["nome"] or "", key=f"nm_{d['id']}", label_visibility="collapsed")
                    if c2.button("Salvar", key=f"sv_{d['id']}") and renomear_dispositivo(u["id"], d["id"], novo): st.rerun()
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
                else:
                    concluir_login(uid, email.strip().lower())      # se caiu no limite de 3, a próxima tela pede para desvincular
                    st.rerun()

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
                if MODO_DEMO and not HOSTED:
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
    "refinar": "🎯 Circular uma área que ficou errada (o programa cola a margem na água)",
    "novo":  "✏️ Desenhar o contorno do zero (marque os cantos)",
    "rota":  "🧭 Desenhar a ROTA à mão (marque por onde o robô passa)",
}


def obter_clique(png, chave):
    """Mostra o mapa (ocupando a largura da tela, bom para tablet) e devolve o toque como (fração_x, fração_y) ou None."""
    pil = Image.open(io.BytesIO(png)).convert("RGB")
    if streamlit_image_coordinates is not None:
        r = None
        for extra in ({"use_column_width": "always"}, {"use_column_width": True}, {"width": 700}, {}):   # cada versão da biblioteca aceita um jeito
            try: r = streamlit_image_coordinates(pil, key=chave, **extra); break
            except TypeError: continue
        if r and r.get("width") and r.get("height"): return r["x"] / r["width"], r["y"] / r["height"]
        return None
    # Plano B (sem a biblioteca de clique): escolher o ponto por porcentagem
    st.image(pil)
    st.warning("Instale `streamlit-image-coordinates` para tocar direto no mapa. Por enquanto, informe o ponto em %.")
    c1, c2 = st.columns(2)
    fx = c1.slider("Posição horizontal (%)", 0, 100, 50, key=chave + "x"); fy = c2.slider("Posição vertical (%)", 0, 100, 50, key=chave + "y")
    return (fx / 100, fy / 100) if st.button("Marcar este ponto", key=chave + "b") else None


# ---------- Visual limpo (sem imagem de fundo): só um cartão discreto para o painel de ambiente ----------
ESTILO_TEMA = """<style>
.glass { background: rgba(128,128,128,.08); border: 1px solid rgba(128,128,128,.28); border-radius: 12px; padding: .8rem 1rem; margin: .3rem 0 .8rem; }
.glass h4 { margin: 0 0 .5rem; }
.glass .linha { display: flex; justify-content: space-between; gap: 1rem; padding: .15rem 0; border-bottom: 1px dashed rgba(128,128,128,.3); }
.glass .linha:last-child { border-bottom: 0; }
.glass .faixa { height: 14px; border-radius: 7px; background: linear-gradient(90deg, #00e5ff, #00bcd4); margin: .25rem 0 .1rem; }
.glass .margem { height: 14px; border-radius: 7px; background: repeating-linear-gradient(45deg, #6aa84f, #6aa84f 6px, #93c47d 6px, #93c47d 12px); margin: .25rem 0 .1rem; }
</style>"""


def area_m2(anel_ll):
    """Área de um contorno (lat, lon) em m² (fórmula do cadarço no plano local)."""
    if not anel_ll or len(anel_ll) < 3: return 0.0
    lat0 = float(np.mean([p[0] for p in anel_ll])); kx = m_lon(lat0)
    P = [(p[1] * kx, p[0] * M_LAT) for p in anel_ll]
    return abs(sum(x1 * y2 - x2 * y1 for (x1, y1), (x2, y2) in zip(P, P[1:] + P[:1]))) / 2


def painel_ambiente(M, espac=None, margem=None):
    """Cartão de vidro com o 'ambiente de medição': faixa de varredura, margem (vegetação) e dimensões do lago.
    O nível da água NÃO é medido (o robô não tem sensor para isso), por isso não aparece."""
    ss = st.session_state
    espac = espac if espac is not None else ss.get("esp_in", ESPACAMENTO_M)
    margem = margem if margem is not None else ss.get("margem_in", MARGEM_M)
    a = area_m2(M.get("poly")); ilhas = M.get("ilhas") or []
    a_i = sum(area_m2(r) for r in ilhas)
    esc = 28                                              # px por metro nas barras desenhadas
    html = (f'<div class="glass"><h4>🌊 Ambiente de medição</h4>'
            f'<div class="linha"><span>Faixa de varredura (entre faixas)</span><b>{espac:.2f} m</b></div>'
            f'<div class="faixa" style="width:{min(espac * esc, 260):.0f}px" title="largura entre faixas"></div>'
            f'<div class="linha"><span>Margem da parede (vegetação e barranco)</span><b>{margem:.1f} m</b></div>'
            f'<div class="margem" style="width:{min(margem * esc, 260):.0f}px"></div>'
            f'<div class="linha"><span>Água navegável</span><b>{max(a - a_i, 0):,.0f} m²</b></div>'
            f'<div class="linha"><span>Ilhas (zona proibida)</span><b>{len(ilhas)} · {a_i:,.0f} m²</b></div>'
            f'<div class="linha"><span>Largura do barco</span><b>{LARGURA_ROBO_M:.2f} m</b></div></div>')
    st.markdown(html, unsafe_allow_html=True)


ESTILO_TOQUE = """<style>
html, body { touch-action: manipulation; }                     /* sem zoom de toque duplo atrapalhando os cliques */
.stButton > button, .stDownloadButton > button { min-height: 3.1rem; font-size: 1.02rem; }
div[data-testid="stRadio"] label { padding: .35rem .2rem; }
div[data-testid="stSlider"] { padding: .5rem .3rem; }
</style>"""


def guardar_historico(M):
    if M.get("poly"): M["hist"].append((list(M["poly"]), list(M.get("ilhas") or []))); M["hist"] = M["hist"][-20:]


def tratar_clique(M, view, fx, fy, modo, tol):
    """Faz o que o modo escolhido manda com o ponto clicado."""
    o, l, s, n = view
    lon, lat = o + fx * (l - o), n - fy * (n - s)
    aviso = []
    if modo in ("mais", "menos", "novo", "rota", "refinar"):
        M["pontos"].append((lat, lon)); return
    img_arr = np.asarray(M["img"])
    if modo == "auto": anel, M["notas"] = contorno_hibrido(img_arr, M["bbox"], semente=(lon, lat), tol=tol)
    else: anel = contorno_automatico(img_arr, lon, lat, tol, M["bbox"])
    if anel is None:
        st.session_state["msg3"] = ("warning", "Não achei água nesse ponto. Clique em um lugar de água e/ou aumente a sensibilidade."); return
    guardar_historico(M)
    if modo == "auto": M["poly"] = anel; M["ilhas"] = []
    else:
        if not M.get("poly"): M["poly"] = anel
        else:
            op = "+" if modo == "maisc" else "-"
            M["poly"], aviso, novas = editar_contorno(M["poly"], op, anel); M["ilhas"] = ilhas_depois_de_editar(M.get("ilhas") or [], op, anel, novas); M["removido"] = removidos_depois_de_editar(M.get("removido") or [], op, anel)
    M["wps"] = None
    if aviso: st.session_state["msg3"] = ("warning", " ".join(aviso))


def aplicar_pontos(M, modo):
    pts = M["pontos"]
    if modo == "rota":                                                   # rota à mão -> waypoints válidos
        if not M.get("poly"): st.session_state["msg3"] = ("warning", "Faça o contorno antes de desenhar a rota."); return
        if len(pts) < 2: st.session_state["msg3"] = ("warning", "Marque pelo menos 2 pontos."); return
        avisos = []
        M["info_rota"] = None
        try: M["wps"] = rota_manual(M["poly"], pts, st.session_state.get("margem_in", MARGEM_M), avisos, zonas_proibidas(M))
        except Exception as e: st.session_state["msg3"] = ("error", f"Não consegui criar a rota: {e}"); return
        M["avisos"] = avisos; M["pontos"] = []; return
    if len(pts) < 3: st.session_state["msg3"] = ("warning", "Marque pelo menos 3 pontos."); return
    if modo == "refinar":                                                # círculo à mão -> margem colada na água dessa área
        if not M.get("poly"): st.session_state["msg3"] = ("warning", "Faça o contorno antes."); return
        novo, info = refinar_area(np.asarray(M["img"]), M["bbox"], M["poly"], pts, st.session_state.get("tol_in", TOL_PADRAO))
        if novo is None: st.session_state["msg3"] = ("info", info.get("motivo", "Nada a ajustar.")); return
        guardar_historico(M); M["poly"] = novo; M["wps"] = None; M["pontos"] = []
        txt = f"Margem ajustada na área circulada: +{info['adicionado_m2']:,.0f} m² de água, −{info['removido_m2']:,.0f} m² de terra."
        if info.get("desconexo_m2", 0) > 20:
            txt += f" Havia mais {info['desconexo_m2']:,.0f} m² de água sem ligação com o lago; para pegá-la, circule também um pedaço que encoste no lago."
        st.session_state["msg3"] = ("success", txt + " Se não gostou, toque em Desfazer."); return
    guardar_historico(M)
    try:
        if modo == "novo" or not M.get("poly"): M["poly"] = simplificar(pts, VERTICES_ROTA, 0.3); aviso = []; M["ilhas"] = []
        else:
            op = "+" if modo == "mais" else "-"
            M["poly"], aviso, novas = editar_contorno(M["poly"], op, pts); M["ilhas"] = ilhas_depois_de_editar(M.get("ilhas") or [], op, pts, novas); M["removido"] = removidos_depois_de_editar(M.get("removido") or [], op, pts)
    except Exception as e:
        M["hist"].pop(); st.session_state["msg3"] = ("error", f"Não consegui aplicar: {e}"); return
    M["pontos"] = []; M["wps"] = None
    if aviso: st.session_state["msg3"] = ("warning", " ".join(aviso))


# Botões do passo 3 usam "callbacks" (on_click): o Streamlit executa a ação ANTES de redesenhar a tela,
# em uma única passada. Antes, cada toque fazia duas passadas pesadas, e no tablet parecia travado.
def _M(): return st.session_state.get("M")


def _seguro(f):
    """Um botão nunca derruba a tela: se a ação falhar, o mapa fica como estava e o erro vira mensagem."""
    import functools
    @functools.wraps(f)
    def interno(*a, **k):
        M = _M(); antes = None
        if M:
            antes = {c: (list(M[c]) if isinstance(M.get(c), list) else M.get(c)) for c in ("poly", "ilhas", "wps", "hist", "pontos", "removido")}
        try: return f(*a, **k)
        except Exception as e:
            if M and antes:
                for c, v in antes.items(): M[c] = v
                M["v"] = M.get("v", 0) + 1
            st.session_state["msg3"] = ("error", f"Não consegui concluir essa ação ({e}). O mapa foi mantido como estava.")
    return interno


@_seguro
def cb_detectar_ilhas():
    M = _M()
    if not M or not M.get("poly"): return
    ss = st.session_state
    novas, info = detectar_ilhas(np.asarray(M["img"]), M["bbox"], M["poly"], M.get("ilhas") or [],
                                 tol=ss.get("tol_in", TOL_PADRAO), min_m2=float(ss.get("ilha_min_in", ILHA_MIN_M2)))
    if not novas:
        ss["msg3"] = ("info", f"Nenhuma ilha nova com pelo menos {ss.get('ilha_min_in', ILHA_MIN_M2):g} m² "
                              f"({info.get('descartadas_pequenas', 0)} pedaço(s) menor(es) ignorado(s)). Diminua a área mínima para ser mais sensível.")
        return
    guardar_historico(M); M["ilhas"] = list(M.get("ilhas") or []) + novas; M["wps"] = None; M["v"] += 1
    ss["msg3"] = ("success", f"{len(novas)} ilha(s) nova(s) acrescentada(s) (contorno amarelo). A rota vai contorná-las. Desfazer reverte.")


@_seguro
def cb_limpar_ilhas():
    M = _M()
    if M and M.get("ilhas"): guardar_historico(M); M["ilhas"] = []; M["wps"] = None; M["v"] += 1


@_seguro
def cb_desfazer_edicao():
    M = _M()
    if M and M["hist"]: M["poly"], M["ilhas"] = M["hist"].pop(); M["wps"] = None; M["v"] += 1


@_seguro
def cb_contorno_original():
    M = _M()
    if M and M.get("poly0"): guardar_historico(M); M["poly"] = list(M["poly0"]); M["ilhas"] = list(M.get("ilhas0") or []); M["wps"] = None; M["v"] += 1


@_seguro
def cb_aplicar_pontos():
    M = _M()
    if M: aplicar_pontos(M, st.session_state.get("modo3", "auto")); M["v"] += 1


@_seguro
def cb_desfazer_ponto():
    M = _M()
    if M and M["pontos"]: M["pontos"].pop(); M["v"] += 1


@_seguro
def cb_limpar_pontos():
    M = _M()
    if M: M["pontos"] = []; M["v"] += 1


@_seguro
def cb_refinar():
    """Procura água que falta no contorno ATUAL (mesma cor, ligada ao lago) e acrescenta. Nunca corta."""
    M = _M()
    if not M or not M.get("poly"): return
    try:
        novo, info = completar_contorno(np.asarray(M["img"]), M["bbox"], M["poly"], tol=st.session_state.get("tol_in", TOL_PADRAO))
    except Exception as e:
        st.session_state["msg3"] = ("error", f"Não consegui completar: {e}"); return
    if novo is None:
        st.session_state["msg3"] = ("info", info.get("motivo", "Nada a acrescentar.")); return
    guardar_historico(M); M["poly"] = novo; M["wps"] = None; M["v"] += 1
    st.session_state["msg3"] = ("success", f"Acrescentei {info['adicionado_m2']:,.0f} m² de água. Se não gostou, toque em Desfazer.")


TIPOS_ROTA = ["Varredura completa (faixas lado a lado)", "Borda + meio (inteligente, gasta menos)"]


@_seguro
def cb_limpar_nao_agua():
    """Tira de DENTRO do contorno o que não é água (floresta, gramado...), mostrando em vermelho o que saiu."""
    M = _M()
    if not M or not M.get("poly"): return
    try:
        novo, info = limpar_contorno(np.asarray(M["img"]), M["bbox"], M["poly"], tol=st.session_state.get("tol_in", TOL_PADRAO))
    except Exception as e:
        st.session_state["msg3"] = ("error", f"Não consegui limpar: {e}"); return
    if novo is None: st.session_state["msg3"] = ("info", info.get("motivo", "Nada a remover.")); return
    guardar_historico(M); M["poly"] = novo; M["wps"] = None; M["removido"] = info["removido"]
    M["ilhas"] = list(M.get("ilhas") or []) + info.get("ilhas", []); M["v"] += 1
    st.session_state["msg3"] = ("success", f"Retirei {info['removido_m2']:,.0f} m² que não são água (em vermelho). Se não gostou, toque em Desfazer.")


@_seguro
def cb_melhorar():
    """Completa (acrescenta água que faltava) e limpa (tira o que não é água): os dois, em sequência."""
    cb_refinar()
    msg1 = st.session_state.pop("msg3", None)
    cb_limpar_nao_agua()
    msg2 = st.session_state.get("msg3")
    txt = " ".join(m[1] for m in (msg1, msg2) if m)
    if txt: st.session_state["msg3"] = ("success" if any(m and m[0] == "success" for m in (msg1, msg2)) else "info", txt)


@_seguro
def cb_calcular_rota(ajustar=False):
    M = _M()
    if not M or not M.get("poly"): return
    ss = st.session_state
    espac, margem = ss.get("esp_in", ESPACAMENTO_M), ss.get("margem_in", MARGEM_M)
    avisos = []
    try:
        if ajustar:
            M["wps"], novo_esp = varredura_que_cabe(M["poly"], espac, margem, ss.get("auto_in", True), int(ss.get("parte_in", 0)), avisos, ilhas_ll=zonas_proibidas(M))
            ss["esp_in"] = float(min(novo_esp, 5.0)); espac = novo_esp
            if espac > LARGURA_ROBO_M:
                avisos.append(f"Com {espac:.2f} m entre as faixas e um barco de {LARGURA_ROBO_M:.2f} m, ficam faixas SEM cobertura. "
                              f"Para varrer tudo com {ESPACAMENTO_M} m, divida a rota em missões (Passo 4).")
        elif ss.get("tipo_in", TIPOS_ROTA[0]) == TIPOS_ROTA[1]:                # borda + meio
            M["wps"], M["info_rota"] = gerar_borda_e_miolo(
                M["poly"], margem, int(ss.get("voltas_in", 2)), float(ss.get("voltaesp_in", 2.0)),
                float(ss.get("meio_in", 10.0)), bool(ss.get("usar_meio_in", True)), int(ss.get("parte_in", 0)), avisos, zonas_proibidas(M))
        else:
            M["wps"] = gerar_varredura(M["poly"], espac, margem, ss.get("auto_in", True), int(ss.get("parte_in", 0)), avisos, zonas_proibidas(M))
            M["info_rota"] = None
        M["avisos"] = avisos; M["params"] = (espac, margem)
    except Exception as e:
        M["wps"] = None; ss["msg3"] = ("error", str(e))
    M["v"] += 1


def cb_ajustar_espacamento(): cb_calcular_rota(ajustar=True)


def _controles_contorno(M):
    """Tudo que fica fora do mapa. Devolve (modo, tol, zoom), que o mapa precisa."""
    painel_ambiente(M)
    with st.expander("✏️ Contorno do lago", expanded=True):
        modo = st.selectbox("Ferramenta", list(MODOS), format_func=lambda k: MODOS[k], key="modo3")
        tol = st.slider("Sensibilidade da detecção por cor", 10, 120, TOL_PADRAO, 1, key="tol_in",
                        help="Maior = considera mais pixels como água. Aumente se o lago ficou incompleto; diminua se vazou para a terra.")
        visao = st.radio("Visão do mapa", ["🔍 Só o lago", "🗺️ Imagem toda"], horizontal=True, key="visao3")
        if modo in ("mais", "menos", "novo", "rota", "refinar"):
            st.caption(f"Pontos marcados: {len(M['pontos'])}. Toque no mapa para marcar, depois toque em Aplicar.")
            b1, b2, b3 = st.columns(3)
            b1.button("Aplicar", on_click=cb_aplicar_pontos, key="b_aplicar", type="primary")
            b2.button("Desfazer ponto", on_click=cb_desfazer_ponto, key="b_dponto")
            b3.button("Limpar pontos", on_click=cb_limpar_pontos, key="b_limpar")
        st.button("✨ Melhorar automaticamente (completa e limpa)", on_click=cb_melhorar, key="b_melhorar", type="primary", disabled=not M.get("poly"))
        b1, b2 = st.columns(2)
        b1.button("🎯 Só completar (acrescenta água)", on_click=cb_refinar, key="b_refinar", disabled=not M.get("poly"))
        b2.button("🧹 Só limpar (tira o que não é água)", on_click=cb_limpar_nao_agua, key="b_limpar_na", disabled=not M.get("poly"))
        b1, b2 = st.columns(2)
        i1, i2 = st.columns([2, 1])
        i1.number_input("Menor ilha a detectar (m²)", 10.0, 2000.0, float(ILHA_MIN_M2), 5.0, key="ilha_min_in",
                        help="Pedaços de terra menores que isso são ruído e ficam de fora. Padrão 40 m² (~6 × 6 m).")
        b1, b2 = st.columns(2)
        b1.button("🏝️ Detectar ilhas (terra isolada)", on_click=cb_detectar_ilhas, key="b_ilhas", disabled=not M.get("poly"))
        b2.button("Apagar ilhas", on_click=cb_limpar_ilhas, key="b_apagar_ilhas", disabled=not M.get("ilhas"))
        b1, b2 = st.columns(2)
        b1.button("↩ Desfazer edição", on_click=cb_desfazer_edicao, key="b_desfazer", disabled=not M["hist"])
        b2.button("⟲ Contorno do site", on_click=cb_contorno_original, key="b_original", disabled=not M.get("poly0"))
        if M.get("poly"): st.caption(f"Contorno com {len(M['poly'])} pontos (o robô recebe no máximo {MAX_VERTICES}).")
        else: st.warning("Ainda não há contorno. Use “Detectar água por cor” e toque na água.")

    for k_ in ("esp_in", "meio_in", "voltas_in", "voltaesp_in", "usar_meio_in", "auto_in", "parte_in", "vel_in", "margem_in"):
        if k_ in st.session_state: st.session_state[k_] = st.session_state[k_]    # mantém o valor ao trocar de tipo de rota
    with st.expander("🧭 Rota de varredura", expanded=True):
        st.caption("Mudou espaçamento, margem ou tipo? Toque em “Calcular rota” para refazer a rota e o tempo estimado.")
        tipo = st.radio("Tipo de rota", TIPOS_ROTA, key="tipo_in",
                        help="As algas se acumulam mais nas bordas: a rota inteligente dá voltas na margem e cruza o meio só de vez em quando.")
        if tipo == TIPOS_ROTA[1]:
            st.number_input("Voltas na borda", 1, 5, 2, 1, key="voltas_in", help="Cada volta acompanha a margem, uma dentro da outra.")
            st.number_input("Distância entre as voltas (m)", 0.5, 20.0, 2.0, 0.5, key="voltaesp_in")
            st.checkbox("Cruzar o meio do lago", value=True, key="usar_meio_in")
            st.number_input("Espaçamento das faixas no meio (m)", 1.0, 100.0, 10.0, 1.0, key="meio_in",
                            help=f"Quanto MAIOR, menos faixas no meio e menos bateria. 10 m = triagem; a varredura completa usa {ESPACAMENTO_M} m.")
        else:
            st.slider("Espaçamento entre faixas (m)", 0.10, 5.0, float(ESPACAMENTO_M), 0.05, key="esp_in",
                            help=f"Robô de {LARGURA_ROBO_M*100:.0f} cm com {SOBREPOSICAO*100:.0f}% de sobreposição = {ESPACAMENTO_M} m.")
        st.number_input("Margem da parede (m)", 0.0, 30.0, float(MARGEM_M), 0.5, key="margem_in",
                        help="O barco não chega mais perto da margem que isso (o GPS erra alguns metros).")
        if tipo != TIPOS_ROTA[1]: st.checkbox("Escolher sozinho a melhor direção das faixas", value=True, key="auto_in")
        st.number_input("Parte do lago (0 = TODAS, recomendado)", 0, 9, 0, 1, key="parte_in",
                        help="0 varre o lago inteiro, ligando pela água os pedaços separados por pontes, estreitos e ilhas. 1 = só o maior pedaço.")
        st.number_input("Velocidade do barco (m/s) para estimar o tempo", 0.05, 3.0, 0.40, 0.05, key="vel_in")
        st.button("Calcular rota", type="primary", on_click=cb_calcular_rota, key="b_rota", disabled=not M.get("poly"))
        for a in M.get("avisos", []): st.warning(a)
        w = M.get("wps")
        if w:
            est = estimar_missao(w, float(st.session_state.get("vel_in", 0.4)))
            m1, m2, m3 = st.columns(3); m1.metric("Waypoints", len(w)); m2.metric("Percurso", f"{est['comprimento_m']:.0f} m")
            m3.metric("Tempo estimado", formatar_duracao(est["tempo_s"]))
            if M.get("ilhas"): st.caption(f"{len(M['ilhas'])} ilha(s) tratadas como zona proibida.")
            ir_ = M.get("info_rota")
            if ir_:
                st.info(f"Borda: {ir_['voltas']} volta(s) de {ir_['perimetro_m']:.0f} m cada · meio: {ir_['faixas_meio']} faixa(s). "
                        f"Economia estimada de percurso (bateria e tempo) em relação à varredura completa: {ir_['economia_pct']:.0f}%.")
            if len(w) > MAX_WAYPOINTS and ir_:
                st.error(f"A rota tem {len(w)} pontos e o robô guarda {MAX_WAYPOINTS}. Diminua as voltas ou aumente o espaçamento do meio.")
            elif len(w) > MAX_WAYPOINTS:
                n = len(dividir_rota(w))
                st.error(f"A rota tem {len(w)} pontos e o robô guarda {MAX_WAYPOINTS}. Duas saídas:")
                st.button("A) Aumentar o espaçamento automaticamente (perde cobertura)", on_click=cb_ajustar_espacamento, key="b_ajusta")
                st.button(f"B) Manter tudo e dividir em {n} missões (Passo 4)", on_click=ir_para, args=(3,), key="b_dividir")
            if len(w) <= MAX_WAYPOINTS:
                st.success("Rota pronta.")
                st.button("Continuar para o Passo 4 (robô) →", on_click=ir_para, args=(3,), type="primary", key="b_p4")
    return st.session_state.get("modo3", "auto"), st.session_state.get("tol_in", TOL_PADRAO), \
        st.session_state.get("visao3", "🔍 Só o lago").startswith("🔍")


def passo_contorno():
    st.header("Passo 3 · Contorno e rota de varredura")
    if not exigir_licenca(): return
    M = st.session_state.get("M")
    if not M:
        st.info("Escolha um lago no Passo 2 primeiro."); st.button("Ir para o Passo 2", on_click=ir_para, args=(1,)); return
    garantir_mapa(M)
    st.markdown(ESTILO_TOQUE, unsafe_allow_html=True)
    msg = st.session_state.pop("msg3", None)
    if msg: getattr(st, msg[0])(msg[1])
    for nota in M.get("notas", []): st.info(nota)

    # Modo tablet (padrão): mapa grande em cima, controles embaixo. Desligado: mapa e controles lado a lado.
    if st.session_state.get("tablet", True):
        cont_mapa = st.container(); cont_ctl = st.container()
    else:
        cont_mapa, cont_ctl = st.columns([3, 2])
    with cont_ctl:
        try: modo, tol, zoom = _controles_contorno(M)  # roda primeiro (precisa do modo e da sensibilidade), mas aparece embaixo
        except Exception as e:                         # erro num controle NÃO pode impedir o mapa de aparecer
            st.error(f"Um controle falhou ({e}). O mapa continua abaixo; recarregue a página se o painel não voltar.")
            modo, tol, zoom = st.session_state.get("modo3", "auto"), st.session_state.get("tol_in", TOL_PADRAO), True
    with cont_mapa:
        view = janela_de_visao(M, zoom)
        try: clique = obter_clique(mapa_em_cache(M, view), f"mapa_{M['v']}")
        except Exception as e:
            st.warning(f"Não consegui desenhar o mapa completo ({e}). Mostrando só a imagem; seus dados estão guardados.")
            st.image(_png_simples(M, view)); clique = None
        if clique:
            try: tratar_clique(M, view, clique[0], clique[1], modo, tol)
            except Exception as e: st.session_state["msg3"] = ("error", f"Erro na edição: {e}")
            M["v"] += 1; st.rerun()                    # troca a chave do componente: o toque antigo não é lido de novo
        st.caption("Amarelo = parede virtual, ciano = rota. Dica: ➕/➖ por cor é o jeito mais rápido de consertar um pedaço.")


# ---------------- PASSO 4: robô ao vivo ----------------
def log_robo(texto):
    st.session_state.setdefault("log4", []).append(f"{hora_local(time.time(), '%H:%M:%S')}  {texto}")
    st.session_state["log4"] = st.session_state["log4"][-30:]


def controles_robo(robo, M):
    st.subheader("Comandos")
    f = robo.foto()
    tem_rota = bool(M.get("wps"))
    partes = dividir_rota(M["wps"]) if tem_rota and len(M["wps"]) > MAX_WAYPOINTS else ([M["wps"]] if tem_rota else [])
    k = 0
    if len(partes) > 1:
        st.info(f"A rota tem {len(M['wps'])} pontos e o robô guarda {MAX_WAYPOINTS}: ela foi dividida em {len(partes)} missões. "
                f"Faça uma de cada vez; o robô volta ao início ao terminar cada uma.")
        k = st.selectbox("Missão", range(len(partes)), key="parte_missao",
                         format_func=lambda i: f"Parte {i + 1} de {len(partes)} ({len(partes[i])} pontos)")
    if tem_rota:
        est = estimar_missao(partes[k], float(st.session_state.get("vel_in", 0.4)))
        st.caption(f"⏱ Estimativa desta missão: {formatar_duracao(est['tempo_s'])} · {est['comprimento_m']:.0f} m · {len(partes[k])} pontos "
                   f"(a {float(st.session_state.get('vel_in', 0.4)):.2f} m/s; sem paradas de re-teste).")
    if f["ip"] is None: st.warning("Ainda não achei o robô na rede (ligue o robô e confira o Wi-Fi).")
    if not tem_rota: st.warning("Falta uma rota válida (Passo 3).")

    if st.button("▶ INICIAR varredura", type="primary", disabled=not (tem_rota and f["ip"])):
        if not f["cal"] or f["estado"] in ("CALIBRANDO", "CALIBRATING"):
            log_robo("Espere a calibração da bússola terminar (ou calibre abaixo)."); st.error("Bússola não calibrada.")
        else:
            robo.nocal = False; robo.fim = False
            lista = list(partes[k])
            if f["pos"]:                                  # caminho SEGURO (pela água) de onde o barco está até o início da parte
                try:
                    lista = rota_manual(M["poly"], [f["pos"], lista[0]], st.session_state.get("margem_in", MARGEM_M), [], zonas_proibidas(M))[:-1] + lista
                except Exception:
                    pass
            if len(lista) > MAX_WAYPOINTS:
                st.error(f"Missão com {len(lista)} pontos passa do limite de {MAX_WAYPOINTS}.")
            else:
                st.session_state["n_wp_missao"] = len(lista)
                with st.spinner("Enviando a missão ao robô..."):
                    ok = robo.enviar_missao(simplificar(M["poly"], MAX_VERTICES, 0.5), lista)
                if ok: log_robo(f"Varredura iniciada ({len(lista)} pontos)!"); st.success("Varredura iniciada!")
                else:
                    log_robo("Falha ao enviar a missão.")
                    st.error(f"O robô não confirmou. Confira o Wi-Fi, a calibração e se o MAX_W do firmware é {MAX_WAYPOINTS}.")
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
    n_w = st.session_state.get("n_wp_missao") or len(M["wps"] or [])
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
    if not ROBO_DISPONIVEL:
        st.info("Este servidor está na internet e não alcança o robô (o robô fala por Wi-Fi local, em UDP). "
                "Para controlar o robô, rode este app no computador que está na rede do robô: `streamlit run app.py`. "
                "Aqui você pode fazer os Passos 1 a 3 (mapa, contorno e rota).")
        return
    M = st.session_state.get("M")
    if M: garantir_mapa(M)
    if not M or not M.get("poly"):
        st.info("Faça o contorno e a rota (Passos 2 e 3) primeiro."); st.button("Ir para o Passo 3", on_click=ir_para, args=(2,)); return
    try: robo = obter_robo()
    except OSError as e:
        st.error(f"Não consegui abrir a porta UDP {PORTA_CENTRAL} (outra Central aberta?): {e}"); return
    painel_ambiente(M)
    col_ctl, col_live = st.columns([1, 2])
    with col_ctl: controles_robo(robo, M)
    with col_live:
        painel_vivo(robo, M)
        if not _fragmento: st.button("Atualizar agora")


# ---------------- app principal ----------------
# ---------- Logo: gota d'água com ondas de lago (arquivos em static/) ----------
PASTA_STATIC = Path(__file__).resolve().parent / "static"

def _icone_pagina():
    """Ícone da aba do navegador: a gota (static/favicon.png); se o arquivo faltar, usa o emoji 💧."""
    try:
        arq = PASTA_STATIC / "favicon.png"
        if arq.exists(): return Image.open(arq)
    except Exception:
        pass
    return "💧"

def _logo_lateral():
    """Logo + nome no topo da barra lateral. Sem o arquivo da logo, mostra só 💧 e o nome."""
    arq = PASTA_STATIC / "logo.png"
    try:
        if arq.exists():
            c1, c2 = st.columns([1, 2.4], vertical_alignment="center")
            c1.image(str(arq), width=56)
            c2.markdown("### BioGlow")
            return
    except Exception:
        pass
    st.title("💧 BioGlow")

def main():
    st.set_page_config(page_title="BioGlow · Central", page_icon=_icone_pagina(), layout="wide")
    st.markdown(ESTILO_TEMA, unsafe_allow_html=True)
    init_db()
    iniciar_identidade()
    tentar_restaurar_login()
    restaurar_mapa()
    st.session_state.setdefault("nav", PASSOS[0])
    if "_ir" in st.session_state:                                    # pedido de troca de passo (ver ir_para)
        st.session_state["nav"] = PASSOS[st.session_state.pop("_ir")]
    with st.sidebar:
        _logo_lateral()
        st.caption("Central do robô AquaSentry")
        st.radio("Passos", PASSOS, key="nav")
        st.toggle("Modo tablet (mapa grande)", value=True, key="tablet")
        st.divider()
        u = usuario()
        if u:
            st.write(f"👤 {u['email']}")
            st.write("🔑 Licença ativa" if licenciado() else "🔑 Sem chave ativada")
            st.button("Sair", on_click=sair, key="sair_lateral")
        else: st.write("Você não está conectado.")
        st.caption(f"Aparelho: {hardware_id()}  ·  fuso: {getattr(fuso_do_usuario(), 'key', None) or fuso_do_usuario()}")
    {PASSOS[0]: passo_conta, PASSOS[1]: passo_lago, PASSOS[2]: passo_contorno, PASSOS[3]: passo_robo}[st.session_state["nav"]]()
    if st.session_state.get("M"): salvar_mapa(st.session_state["M"])
    emitir_cookies()


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
