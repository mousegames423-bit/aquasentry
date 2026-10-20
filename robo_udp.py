"""robo_udp.py - Comunicação com o robô por UDP.

Classe Robo (thread de escuta em segundo plano, envio de comandos e de missões) e obter_robo(), que a mantém viva
entre as execuções do Streamlit.
"""

import collections
import csv
import io
import socket
import threading
import time

import streamlit as st

PORTA_CENTRAL = 5005    # o computador escuta aqui

PORTA_ROBO = 5006       # o robô escuta aqui

# Qualidade do link (o robô manda um pacote de estado "S" a cada ~1 s):
ATRASO_INSTAVEL_S = 3.0    # sem pacote há mais que isso -> "instável"
ATRASO_SEM_SINAL_S = 8.0   # sem pacote há mais que isso -> "sem sinal"


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
        self.intervalos = collections.deque(maxlen=20)       # segundos entre pacotes de estado consecutivos
        self.telemetria = collections.deque(maxlen=5000)     # (tempo, lat, lon, bat, sats, rumo, wp, estado)
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
                        agora = time.time()
                        if self.ultimo_s: self.intervalos.append(agora - self.ultimo_s)
                        self.ultimo_s = agora
                        self.telemetria.append((agora, self.pos[0], self.pos[1], self.bat, self.sats, self.rumo, self.wp, self.estado))
                    elif p[0] == "T":
                        self.leituras.append(tuple(map(float, p[1:5])) + (int(p[5]),))
                        self.telemetria.append((time.time(), float(p[1]), float(p[2]), self.bat, self.sats, self.rumo, self.wp, "LEITURA"))
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

    def conexao(self):
        """Qualidade do link UDP: ('sem_robo' | 'sem_sinal' | 'instavel' | 'ok', segundos desde o último pacote).
        'instavel' = pacote atrasado agora OU intervalo recente muito maior que o normal (pacotes sendo perdidos)."""
        with self.lock:
            if not self.ultimo_s: return ("sem_robo", None)
            idade = time.time() - self.ultimo_s
            maior_intervalo = max(list(self.intervalos)[-8:] or [0.0])
        if idade > ATRASO_SEM_SINAL_S: return ("sem_sinal", idade)
        if idade > ATRASO_INSTAVEL_S or maior_intervalo > ATRASO_INSTAVEL_S: return ("instavel", idade)
        return ("ok", idade)

    def exportar_csv(self):
        """CSV (bytes UTF-8) com a telemetria (estado do robô) e as leituras de turbidez e pH, em ordem de tempo."""
        return gerar_csv_telemetria(self.foto_telemetria(), self.foto()["leituras"])

    def foto_telemetria(self):
        with self.lock: return list(self.telemetria)

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


def gerar_csv_telemetria(telemetria, leituras):
    """Junta telemetria [(tempo, lat, lon, bat, sats, rumo, wp, estado)] e leituras [(lat, lon, turbidez, ph, anomalia)]
    num CSV só. As leituras não têm horário próprio: ficam em 'leitura' com o horário do pacote, quando há telemetria dele."""
    sb = io.StringIO(); w = csv.writer(sb)
    w.writerow(["horario_utc", "tipo", "lat", "lon", "bateria_v", "satelites", "rumo_graus", "waypoint", "estado", "turbidez", "ph", "anomalia"])
    leit = list(leituras or [])
    for t, la, lo, bat, sats, rumo, wp, est in telemetria or []:
        hora = time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime(t))
        if est == "LEITURA":
            # procura a leitura correspondente (mesma posição) para preencher turbidez/pH
            k = next((i for i, r in enumerate(leit) if abs(r[0] - la) < 1e-9 and abs(r[1] - lo) < 1e-9), None)
            r = leit.pop(k) if k is not None else (la, lo, "", "", "")
            w.writerow([hora, "leitura", f"{la:.7f}", f"{lo:.7f}", f"{bat:.2f}", sats, f"{rumo:.0f}", wp, "", r[2], r[3], r[4]])
        else:
            w.writerow([hora, "telemetria", f"{la:.7f}", f"{lo:.7f}", f"{bat:.2f}", sats, f"{rumo:.0f}", wp, est, "", "", ""])
    for r in leit:                                        # leituras sem telemetria correspondente (ex.: pacote T sem S antes)
        w.writerow(["", "leitura", f"{r[0]:.7f}", f"{r[1]:.7f}", "", "", "", "", "", r[2], r[3], r[4]])
    return sb.getvalue().encode("utf-8")


@st.cache_resource
def obter_robo():
    """Só UM Robo (e uma porta UDP aberta) para todo o app, mesmo com o Streamlit recarregando a página."""
    return Robo()
