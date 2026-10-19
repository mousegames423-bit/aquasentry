"""robo_udp.py - Comunicação com o robô por UDP.

Classe Robo (thread de escuta em segundo plano, envio de comandos e de missões) e obter_robo(), que a mantém viva
entre as execuções do Streamlit.
"""

import socket
import threading
import time

import streamlit as st

PORTA_CENTRAL = 5005    # o computador escuta aqui

PORTA_ROBO = 5006       # o robô escuta aqui


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
