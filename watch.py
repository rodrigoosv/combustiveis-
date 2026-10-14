#!/usr/bin/env python3
"""
Vigilante de precos de combustiveis (DGEG + Plenergy) com notificacoes no iPhone via ntfy.

Uso:
  py watch.py --teste       envia uma notificacao de teste
  py watch.py --inspect     mostra os postos encontrados e a resposta crua de 2 deles
  py watch.py --procurar X  lista os postos da DGEG que contem o texto X
  py watch.py --plenergy    mostra os precos lidos do site da Plenergy
  py watch.py --resumo      envia (ou mostra) o resumo dos gasoleos mais baratos
  py watch.py --extremos    mostra preco atual, minimo e maximo historicos de cada posto (gasoleo; 'todos' para tudo)
  py watch.py --grafico     (re)gera o grafico.svg, o index.html (interativo) e o dados.json a partir do estado.json e do historico.csv
  py watch.py --isp         mostra os artigos 'ATUALIZACAO ISP' do Contas Poupanca e a previsao do ultimo
  py watch.py               execucao normal: compara com estado.json e avisa se algo mudou

Variavel de ambiente necessaria para as notificacoes: NTFY_TOPIC (o teu topico no ntfy)
"""
import csv
import hashlib
import html
import json
import os
import re
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import urljoin

import requests

BASE = "https://precoscombustiveis.dgeg.gov.pt/api/PrecoComb"
TOPICO = os.environ.get("NTFY_TOPIC", "").strip()
ESTADO = Path(__file__).with_name("estado.json")
HISTORICO = Path(__file__).with_name("historico.csv")
GRAFICO = Path(__file__).with_name("grafico.svg")
DADOS_JSON = Path(__file__).with_name("dados.json")  # resumo pequeno para Atalhos/widget do iPhone
PAGINA = Path(__file__).with_name("index.html")  # grafico interativo (serve para GitHub Pages)
HEADERS = {"User-Agent": "vigilante-combustiveis-pessoal/1.0"}

# Que postos seguir: o municipio tem de ser exatamente este;
# se "marcas" tiver itens, so entram postos de uma dessas marcas.
REGRAS = [
    {"municipio": "marinha grande", "marcas": []},
    {"municipio": "leiria", "marcas": ["prio", "pingo doce"]},
]

# Postos a ignorar (por Id): PRIO Coimbrao e todos os da Vieira
EXCLUIR_IDS = {
    71069,  # PRIO Coimbrao (Salgueira)
    93219,  # CEPSA Vieira de Leiria
    65417,  # GALP Cunha e Monteiro (Vieira de Leiria)
    75757,  # Intermarche Supervieira (Praia da Vieira)
}

# Nomes personalizados nos avisos (por Id). Os restantes usam a marca.
NOMES_POSTOS = {
    66596: "REPSOL (R. Mc)",
    66582: "REPSOL (R. Videiro)",
    93762: "PRIO (Marinha Grande)",
    93310: "TRANSOGÁS",
}

# Plenergy: os precos vem da pagina deles (variavel datosPrecio), indexados por idalvic.
PLENERGY_URL = "https://plenergy.pt/estacoes-de-servico/"
PLENERGY_POSTOS = {"404": "Marinha Grande"}  # idalvic -> localidade
PLENERGY_COORDS = {"404": (39.74173, -8.935447, "Avenida Dr. José Henriques Vareda, nº 32")}  # lat, lon, morada
PLENERGY_CAMPOS = {
    "diesel": "Gasóleo simples",
    "goa_add": "Gasóleo plus",
    "splomo": "Gasolina 95 simples",
    "sp95_add": "Gasolina 95 plus",
}

# So avisa de combustiveis cujo nome contenha um destes textos (minusculas).
# Todos os tipos de gasoleo: simples, especial/plus, colorido...
COMBUSTIVEIS_AVISO = ("gasóleo", "gasoleo")

# Contas Poupanca: avisa quando sai um novo artigo de previsao semanal (ATUALIZACAO ISP)
CP_URL = "https://contaspoupanca.pt/carro/combustiveis"
CP_HEADERS = {  # o site bloqueia pedidos sem cabecalhos de browser (erro 403)
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "pt-PT,pt;q=0.9,en;q=0.8",
    "Referer": "https://contaspoupanca.pt/carro",
}
GN_RSS = "https://news.google.com/rss/search"  # alternativa quando o site bloqueia o script
CP_TITULOS = ("atualizacao isp", "preco dos combustiveis na proxima semana")  # sem acentos

DIAS_MIN_RECORDE = 7  # so assinala "minimo/maximo historico" depois de tantos dias de registo
HORA_RESUMO = 8      # resumo diario a partir desta hora (hora de Portugal)
FALHAS_ALERTA = 3    # avisa quando uma fonte falha este numero de vezes seguidas

NOMES = ("TipoCombustivel", "Combustivel", "NomeCombustivel")
PRECOS = ("Preco", "PrecoCombustivel", "Valor")


# ---------------------------------------------------------------- DGEG
def pedir(caminho, params=None):
    r = requests.get(f"{BASE}/{caminho}", params=params, headers=HEADERS, timeout=60)
    r.raise_for_status()
    j = r.json()
    if isinstance(j, dict) and j.get("status") is False:
        raise RuntimeError(f"DGEG devolveu erro: {j.get('mensagem')}")
    return j.get("resultado") if isinstance(j, dict) else j


def listar_postos():
    res = pedir("PesquisarPostos", {"qtdPorPagina": 999999, "pagina": 1, "orderDesc": 0})
    if isinstance(res, dict):  # caso a lista venha dentro de um objeto
        res = next((v for v in res.values() if isinstance(v, list)), [])
    return res or []


def filtrar(postos):
    """Filtra por municipio/marca e remove duplicados (a lista repete o posto por combustivel)."""
    unicos = {}
    for p in postos:
        if p.get("Id") in EXCLUIR_IDS:
            continue
        if any(x in str(p.get("Marca", "")).lower() for x in ("plenergy", "plenoil")):
            continue  # a Plenergy e lida do site deles (evita avisos duplicados)
        mun = str(p.get("Municipio", "")).strip().lower()
        marca = str(p.get("Marca", "")).strip().lower()
        for r in REGRAS:
            if mun == r["municipio"] and (not r["marcas"] or any(m in marca for m in r["marcas"])):
                unicos[p.get("Id")] = p
                break
    return list(unicos.values())


def extrair_precos(obj, saida=None):
    """Procura, em qualquer parte da resposta, pares combustivel/preco."""
    if saida is None:
        saida = {}
    if isinstance(obj, dict):
        nome = next((obj[k] for k in NOMES if isinstance(obj.get(k), str) and obj[k].strip()), None)
        preco = next((obj[k] for k in PRECOS if obj.get(k) not in (None, "")), None)
        if nome and preco is not None:
            saida[nome.strip()] = str(preco).strip()
        for v in obj.values():
            extrair_precos(v, saida)
    elif isinstance(obj, list):
        for v in obj:
            extrair_precos(v, saida)
    return saida


def rotulo(p):
    marca = p.get("Marca") or ""
    nome = p.get("Nome") or ""
    local = p.get("Localidade") or p.get("Municipio") or ""
    if marca and nome.lower().startswith(marca.lower()):
        marca = ""  # evita "PRIO PRIO Guia"
    return " ".join(x for x in (marca, nome, f"({local})" if local else "") if x).strip()


# ------------------------------------------------------------- Plenergy
def precos_plenergy():
    """Le a variavel datosPrecio da pagina da Plenergy. Devolve {idalvic: {combustivel: preco}}."""
    r = requests.get(PLENERGY_URL, headers=HEADERS, timeout=60)
    r.raise_for_status()
    m = re.search(r"var\s+datosPrecio\s*=\s*", r.text)
    if not m:
        raise RuntimeError("datosPrecio nao encontrado na pagina da Plenergy")
    dados, _ = json.JSONDecoder().raw_decode(r.text, m.end())
    saida = {}
    for idalvic in PLENERGY_POSTOS:
        d = dados.get(idalvic)
        if not isinstance(d, dict):
            continue
        precos = {}
        for campo, nome in PLENERGY_CAMPOS.items():
            try:
                v = float(str(d.get(campo, "")).strip())
            except ValueError:
                continue
            if v > 0:
                precos[nome] = f"{v:.3f}".replace(".", ",") + " €/litro"
        if precos:
            saida[idalvic] = precos
    return saida


# ------------------------------------------------------- Contas Poupanca
def sem_acentos(t):
    return "".join(c for c in unicodedata.normalize("NFKD", t) if not unicodedata.combining(c)).lower()


def limpar_html(h):
    h = re.sub(r"(?is)<(script|style).*?</\1>", " ", h)
    h = re.sub(r"(?s)<[^>]+>", " ", h)
    return re.sub(r"\s+", " ", html.unescape(h)).strip()


def artigos_isp():
    """Artigos de previsao semanal na pagina de combustiveis. Devolve [(titulo, url)], mais recente primeiro."""
    r = requests.get(CP_URL, headers=CP_HEADERS, timeout=60)
    r.raise_for_status()
    vistos, saida = set(), []
    for href, interior in re.findall(r'(?is)<a\b[^>]*?\bhref="([^"]+)"[^>]*>(.*?)</a>', r.text):
        titulo = limpar_html(interior)
        if not titulo or not any(x in sem_acentos(titulo) for x in CP_TITULOS):
            continue
        url = urljoin(CP_URL, href.split("?")[0])
        if "contaspoupanca.pt" in url and url not in vistos:
            vistos.add(url)
            saida.append((titulo, url))
    return saida


def artigos_isp_rss():
    """Alternativa: feed de pesquisa do Google Noticias (nao tem os numeros da previsao, so titulo e link)."""
    q = 'site:contaspoupanca.pt "preço dos combustíveis na próxima semana" when:14d'
    r = requests.get(GN_RSS, params={"q": q, "hl": "pt-PT", "gl": "PT", "ceid": "PT:pt-150"},
                     headers=HEADERS, timeout=60)
    r.raise_for_status()
    itens = []
    for it in ET.fromstring(r.content).iter("item"):
        titulo = (it.findtext("title") or "").strip()
        link = (it.findtext("link") or "").strip()
        fonte = it.find("source")
        fonte_txt = ((fonte.text or "") if fonte is not None else "").strip()
        origem = sem_acentos(fonte_txt + (fonte.get("url", "") if fonte is not None else "")).replace(" ", "")
        if "contaspoupanca" not in origem:
            continue
        if fonte_txt and titulo.endswith(" - " + fonte_txt):
            titulo = titulo[: -len(" - " + fonte_txt)].strip()
        if not any(x in sem_acentos(titulo) for x in CP_TITULOS):
            continue
        try:
            data = parsedate_to_datetime(it.findtext("pubDate") or "")
        except Exception:
            data = datetime.fromtimestamp(0, timezone.utc)
        itens.append((data, titulo, link))
    itens.sort(key=lambda x: x[0], reverse=True)
    return [(t, u) for _, t, u in itens]


def obter_artigos_isp():
    """Tenta o site; se bloquear (403), usa o feed do Google Noticias. Devolve (artigos, origem)."""
    try:
        return artigos_isp(), "site"
    except Exception as e:
        print(f"Contas Poupança bloqueou o acesso direto ({e}); a tentar o Google Noticias")
        return artigos_isp_rss(), "google"


def previsao_isp(url):
    """Le a previsao (em centimos) do artigo. Devolve linhas de texto; vazio se nao conseguir."""
    if "contaspoupanca.pt" not in url:
        return []  # links do Google Noticias nao permitem ler o artigo
    r = requests.get(url, headers=CP_HEADERS, timeout=60)
    r.raise_for_status()
    texto = limpar_html(r.text)
    linhas = []
    for nome, chave in (("Gasóleo", r"Gas[óo]leo"), ("Gasolina", r"Gasolina")):
        m = re.search(chave + r"\s*\(.{0,80}?\)\s*=\s*([+\-−–]?\s*\d+(?:[.,]\d+)?)\s*c[eê]ntimos", texto, re.I)
        if not m:
            continue
        valor = re.sub(r"[\s]", "", m.group(1)).replace("−", "-").replace("–", "-")
        n = float(valor.lstrip("+-").replace(",", "."))
        emoji = "" if n == 0 else ("⬇️ " if valor.startswith("-") else "⬆️ ")
        linhas.append(f"{emoji}{nome}: {valor} cêntimos")
    return linhas


# ------------------------------------------------------------ formatacao
def hora_local():
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("Europe/Lisbon"))
    except Exception:
        return datetime.now(timezone.utc)


def numero(preco):
    """'2,209 €/litro' -> 2.209"""
    m = re.search(r"\d+[.,]\d+", str(preco))
    return float(m.group().replace(",", ".")) if m else None


def num3(preco):
    """'2,100 €/litro' -> '2.100' (para o CSV)"""
    n = numero(preco)
    return f"{n:.3f}" if n is not None else ""


def curto(preco):
    """'2,209 €/litro' -> '2,209 €'"""
    return str(preco).replace("/litro", "").strip()


def quer_aviso(comb):
    c = comb.lower()
    return any(x in c for x in COMBUSTIVEIS_AVISO)


def tipo_gasoleo(comb):
    c = comb.lower()
    if not quer_aviso(c):
        return None
    if "simples" in c:
        return "simples"
    if "especial" in c or "plus" in c:
        return "especial"
    return None


def nome_posto(p, repetida=False):
    if p.get("Id") in NOMES_POSTOS:
        return NOMES_POSTOS[p.get("Id")]
    marca = p.get("Marca") or p.get("Nome") or "Posto"
    if repetida:  # varios postos da mesma marca: junta a localidade
        local = (p.get("Localidade") or p.get("Municipio") or "").strip()
        if local:
            marca = f"{marca} ({local})"
    return marca


def linha_aviso(p, comb, antes, atual, repetida=False, recorde=None):
    nome = nome_posto(p, repetida)
    if antes is None:
        return f"{nome}: {comb} {curto(atual)}"
    na, nb = numero(atual), numero(antes)
    if na is not None and nb is not None and na != nb:
        emoji, verbo = ("⬇️", "desceu") if na < nb else ("⬆️", "subiu")
    else:
        emoji, verbo = "", "mudou"
    texto = f"{nome}: {comb} {verbo} para {curto(atual)} (ultimo {curto(antes)})"
    if recorde == "min":
        texto += " 🏆 mínimo histórico"
    elif recorde == "max":
        texto += " 📈 máximo histórico"
    return f"{emoji} {texto}" if emoji else texto


def resumo(estado):
    """Gasoleos mais baratos entre os postos seguidos."""
    grupos = {"simples": [], "especial": []}
    for pid, v in estado.items():
        if pid == "_meta":
            continue
        nome = v.get("aviso") or v.get("nome")
        for comb, (preco, _) in v.get("precos", {}).items():
            t, n = tipo_gasoleo(comb), numero(preco)
            if t and n is not None:
                grupos[t].append((n, nome, preco))
    blocos = []
    for t, titulo, topo in (("simples", "Gasóleo simples", 3), ("especial", "Gasóleo especial/plus", 2)):
        lista = sorted(grupos[t])[:topo]
        if lista:
            linhas = [f"{titulo}:"]
            for i, (_, nome, preco) in enumerate(lista, 1):
                linhas.append(f"{i}. {nome} {curto(preco)}")
            blocos.append("\n".join(linhas))
    return "\n\n".join(blocos)  # linha em branco entre os grupos


CABECALHO = ["data_hora", "posto", "combustivel", "preco_anterior", "preco_novo",
             "variacao_cent", "direcao", "minimo_historico", "data_minimo",
             "maximo_historico", "data_maximo"]


def fmt3(x):
    return f"{x:.3f}" if isinstance(x, (int, float)) else ""


def variacao(antes, depois):
    """Devolve (variacao em centimos com sinal, direcao). Precos como numeros ou None."""
    if antes is None or depois is None:
        return "", "novo"
    v = round((depois - antes) * 100, 1)
    if v == 0:
        return "", "mudou"
    return f"{v:+.1f}", ("subiu" if v > 0 else "desceu")


def normalizar_data(d, fallback):
    """'09-10-2026 00:00' -> '2026-10-09 00:00' (se nao der, usa o fallback)."""
    d = str(d or "").strip()
    for formato in ("%d-%m-%Y %H:%M", "%Y-%m-%d %H:%M"):
        try:
            return datetime.strptime(d, formato).strftime("%Y-%m-%d %H:%M")
        except ValueError:
            pass
    return fallback


def atualizar_extremos(ext_posto, comb, n, data):
    """Guarda o preco mais baixo e mais alto ja visto (e quando). Empates mantem a data mais antiga."""
    e = ext_posto.setdefault(comb, {})
    novo = "min" not in e
    recorde = None
    if novo or n < e["min"][0]:
        e["min"] = [n, data]
        recorde = None if novo else "min"
    if novo or n > e["max"][0]:
        e["max"] = [n, data]
        recorde = None if novo else "max"
    return recorde  # "min"/"max" se bateu um recorde (nao conta a primeira vez que o preco e visto)


def migrar_historico():
    """Se o historico.csv for de uma versao antiga (5 colunas), acrescenta as colunas novas."""
    if not HISTORICO.exists():
        return
    with HISTORICO.open(newline="", encoding="utf-8") as f:
        linhas = list(csv.reader(f))
    if not linhas or linhas[0] == CABECALHO:
        return
    novas = [CABECALHO]
    for l in linhas[1:]:
        l = (l + [""] * 5)[:5]
        antes = numero(l[3]) if l[3] else None
        depois = numero(l[4]) if l[4] else None
        var, direcao = variacao(antes, depois)
        novas.append(l + [var, direcao, "", "", "", ""])
    with HISTORICO.open("w", newline="", encoding="utf-8") as f:
        csv.writer(f).writerows(novas)


def registar_historico(linhas):
    if not linhas:
        return
    novo = not HISTORICO.exists()
    with HISTORICO.open("a", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        if novo:
            w.writerow(CABECALHO)
        w.writerows(linhas)


def pt(x):
    return fmt3(x).replace(".", ",")


PALETA = ["#e6194b", "#3cb44b", "#4363d8", "#f58231", "#911eb4", "#008080", "#9a6324", "#800000",
          "#808000", "#000075", "#d4a000", "#46a0c8", "#f032e6", "#555555", "#2e8b57", "#b8860b"]


def series_grafico(estado, desde, agora, agrupar=None):
    """{tipo: [(nome, [(datetime, preco), ...], preco_atual)]} a partir do historico.csv e do estado."""
    linhas = []
    if HISTORICO.exists():
        with HISTORICO.open(newline="", encoding="utf-8") as f:
            linhas = list(csv.DictReader(f))
    por_posto, instantes = {}, [desde]
    for l in linhas:
        try:
            t = datetime.strptime(l["data_hora"], "%Y-%m-%d %H:%M")
            novo = float(l["preco_novo"])
            ant = float(l["preco_anterior"]) if l["preco_anterior"] else None
        except (ValueError, KeyError, TypeError):
            continue
        por_posto.setdefault((l["posto"], l["combustivel"]), []).append((t, ant, novo))
        instantes.append(t)
    x0 = min(instantes)
    agrupar = agrupar or tipo_gasoleo
    res = {}
    for pid, v in estado.items():
        if pid == "_meta":
            continue
        nome = v.get("aviso") or v.get("nome")
        for comb, (preco, _) in v.get("precos", {}).items():
            tipo, atual = agrupar(comb), numero(preco)
            if not tipo or atual is None:
                continue
            rows = sorted(por_posto.get((v.get("nome"), comb), []))
            pts = []
            if rows:
                if rows[0][1] is not None:
                    pts.append((x0, rows[0][1]))  # preco antes da primeira mudanca registada
                pts += [(t, novo) for t, _, novo in rows]
            else:
                pts.append((x0, atual))
            pts.append((agora, atual))
            res.setdefault(tipo, []).append((nome, pts, atual))
    return res, x0


def vc(x):
    return f"{x:.3f}".replace(".", ",")


def desenhar_grafico(res, x0, x1, atualizado):
    """Grafico SVG (sem dependencias): preco ao longo do tempo, uma linha por posto."""
    W, PH, ML, MR, MT, MB = 940, 340, 64, 260, 62, 44
    paineis = [(t, titulo) for t, titulo in (("simples", "Gasóleo simples"), ("especial", "Gasóleo especial / plus"))
               if res.get(t)]
    H = 56 + PH * max(1, len(paineis))
    if x1 <= x0:
        x1 = x0 + timedelta(hours=24)
    span = (x1 - x0).total_seconds()
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
         'font-family="Segoe UI, Arial, sans-serif">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
         f'<text x="{ML}" y="30" font-size="20" font-weight="bold" fill="#222">Preço dos combustíveis</text>',
         f'<text x="{ML}" y="48" font-size="12" fill="#666">Atualizado em {html.escape(atualizado)}</text>']
    if not paineis:
        o.append(f'<text x="{ML}" y="100" font-size="14" fill="#666">Ainda não há dados de gasóleo.</text>')
    for i, (tipo, titulo) in enumerate(paineis):
        series = sorted(res[tipo], key=lambda x: (x[2], x[0]))
        yo = 56 + i * PH
        top, bot, left, right = yo + MT, yo + PH - MB, ML, W - MR
        valores = [p for _, pts, _ in series for _, p in pts]
        vmin, vmax = min(valores), max(valores)
        pad = max(0.02, (vmax - vmin) * 0.12)
        lo, hi = vmin - pad, vmax + pad

        def X(t):
            return left + (t - x0).total_seconds() / span * (right - left)

        def Y(v):
            return bot - (v - lo) / (hi - lo) * (bot - top)

        # titulo + extremos do painel
        mn = min(((p, n, t) for n, pts, _ in series for t, p in pts), key=lambda z: z[0])
        mx = max(((p, n, t) for n, pts, _ in series for t, p in pts), key=lambda z: z[0])
        o.append(f'<text x="{left}" y="{yo + 24}" font-size="16" font-weight="bold" fill="#222">{titulo} (€/litro)</text>')
        o.append(f'<text x="{left}" y="{yo + 42}" font-size="12" fill="#666">'
                 f'Mais baixo: {vc(mn[0])} € ({html.escape(mn[1])}, {mn[2]:%d/%m}) · '
                 f'Mais alto: {vc(mx[0])} € ({html.escape(mx[1])}, {mx[2]:%d/%m})</text>')
        # grelha
        for k in range(5):
            v = lo + (hi - lo) * k / 4
            y = Y(v)
            o.append(f'<line x1="{left}" y1="{y:.1f}" x2="{right}" y2="{y:.1f}" stroke="#e5e5e5"/>')
            o.append(f'<text x="{left - 8}" y="{y + 4:.1f}" font-size="11" fill="#666" text-anchor="end">'
                     f'{vc(v)}</text>')
        for k in range(5):
            t = x0 + timedelta(seconds=span * k / 4)
            x = X(t)
            fmt = "%d/%m %Hh" if span < 2 * 86400 else "%d/%m"
            o.append(f'<line x1="{x:.1f}" y1="{top}" x2="{x:.1f}" y2="{bot}" stroke="#f0f0f0"/>')
            o.append(f'<text x="{x:.1f}" y="{bot + 18}" font-size="11" fill="#666" text-anchor="middle">{t.strftime(fmt)}</text>')
        o.append(f'<rect x="{left}" y="{top}" width="{right - left}" height="{bot - top}" fill="none" stroke="#bbb"/>')
        # linhas em degrau + legenda
        for j, (nome, pts, atual) in enumerate(series):
            cor = PALETA[j % len(PALETA)]
            d = f"M{X(pts[0][0]):.1f},{Y(pts[0][1]):.1f}"
            for (_, pa), (t, p) in zip(pts, pts[1:]):
                d += f" H{X(t):.1f} V{Y(p):.1f}"
            o.append(f'<path d="{d}" fill="none" stroke="{cor}" stroke-width="2"/>')
            for t, p in pts[1:-1]:
                o.append(f'<circle cx="{X(t):.1f}" cy="{Y(p):.1f}" r="3" fill="{cor}"/>')
            o.append(f'<circle cx="{X(pts[-1][0]):.1f}" cy="{Y(atual):.1f}" r="4" fill="{cor}" stroke="#fff"/>')
            ly = top + 12 + j * 19
            o.append(f'<line x1="{right + 16}" y1="{ly - 4}" x2="{right + 36}" y2="{ly - 4}" stroke="{cor}" stroke-width="3"/>')
            o.append(f'<text x="{right + 42}" y="{ly}" font-size="12" fill="#222">{html.escape(nome[:24])}</text>')
            o.append(f'<text x="{W - 8}" y="{ly}" font-size="12" fill="#222" text-anchor="end">'
                     f'{vc(atual)}</text>')
    o.append("</svg>")
    return "\n".join(o)


ORDEM_GRUPOS = ["Gasóleo simples", "Gasóleo especial / plus", "Gasolina 95 simples",
                "Gasolina 95 especial / plus", "Gasolina 98", "GPL"]


def grupo_combustivel(comb):
    c = sem_acentos(comb)
    if "gasoleo" in c:
        if "simples" in c:
            return "Gasóleo simples"
        if "especial" in c or "plus" in c:
            return "Gasóleo especial / plus"
        return None  # colorido, etc.
    if "gasolina" in c and "95" in c:
        if "simples" in c:
            return "Gasolina 95 simples"
        if "especial" in c or "plus" in c:
            return "Gasolina 95 especial / plus"
    if "gasolina" in c and "98" in c:
        return "Gasolina 98"
    if "gpl" in c:
        return "GPL"
    return None


def _ms(t):
    return int((t - datetime(1970, 1, 1)).total_seconds() * 1000)


def linhas_historico(estado, limite=800):
    """Ultimas mudancas de preco, para a pagina Historico: [ms, posto, grupo, combustivel, anterior, novo]."""
    if not HISTORICO.exists():
        return []
    aviso = {v.get("nome"): (v.get("aviso") or v.get("nome")) for k, v in estado.items() if k != "_meta"}
    saida = []
    with HISTORICO.open(newline="", encoding="utf-8") as f:
        for l in csv.DictReader(f):
            try:
                t = datetime.strptime(l["data_hora"], "%Y-%m-%d %H:%M")
                novo = float(l["preco_novo"])
                ant = float(l["preco_anterior"]) if l.get("preco_anterior") else None
            except (ValueError, KeyError, TypeError):
                continue
            saida.append([_ms(t), aviso.get(l["posto"], l["posto"]), grupo_combustivel(l["combustivel"]) or "",
                          l["combustivel"], ant, novo])
    return saida[-limite:]


def escrever_dados_json(estado, desde, agora):
    """dados.json: preco mais barato de cada combustivel (para Atalhos e widgets)."""
    res, _ = series_grafico(estado, desde, agora, agrupar=grupo_combustivel)
    grupos = {}
    for g in ORDEM_GRUPOS:
        lst = res.get(g)
        if not lst:
            continue
        ordenados = sorted(lst, key=lambda x: (x[2], x[0]))
        melhor = ordenados[0]
        grupos[g] = {
            "mais_barato": {"posto": melhor[0], "preco": melhor[2], "preco_texto": f"{melhor[2]:.3f}".replace(".", ",")},
            "media": round(sum(x[2] for x in lst) / len(lst), 3),
            "postos": [{"posto": n, "preco": a, "preco_texto": f"{a:.3f}".replace(".", ",")} for n, _, a in ordenados],
        }
    DADOS_JSON.write_text(json.dumps({"atualizado": agora.strftime("%Y-%m-%d %H:%M"), "grupos": grupos},
                                     ensure_ascii=False, indent=1), encoding="utf-8")


def dados_pagina(estado, desde, agora):
    res, x0 = series_grafico(estado, desde, agora, agrupar=grupo_combustivel)
    nomes = sorted({n for lst in res.values() for n, _, _ in lst})
    cores = {n: PALETA[i % len(PALETA)] for i, n in enumerate(nomes)}

    def ms(t):
        return int((t - datetime(1970, 1, 1)).total_seconds() * 1000)

    info = {}
    for pid, v in estado.items():
        if pid != "_meta":
            info[v.get("aviso") or v.get("nome")] = v

    def extra(n):
        v = info.get(n, {})
        return {"lat": v.get("lat"), "lon": v.get("lon"), "m": v.get("morada")}

    grupos = {g: [{"n": n, "c": cores[n], "a": atual, "p": [[ms(t), p] for t, p in pts], **extra(n)}
                  for n, pts, atual in res[g]] for g in ORDEM_GRUPOS if g in res}
    todos = [{"n": n, "g": [g for g in ORDEM_GRUPOS if any(x[0] == n for x in res.get(g, []))]} for n in nomes]
    return {"atualizado": agora.strftime("%d/%m/%Y %H:%M"), "x0": ms(x0), "x1": ms(agora), "grupos": grupos,
            "hist": linhas_historico(estado), "todos": todos}


PAGINA_HTML = r"""<!doctype html>
<html lang="pt"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Combustíveis · Marinha Grande e Leiria</title>
<meta name="theme-color" content="#f2f2f7" media="(prefers-color-scheme: light)">
<meta name="theme-color" content="#000000" media="(prefers-color-scheme: dark)">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Combustíveis">
<link rel="icon" href="data:image/svg+xml,<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 100 100%22><text y=%22.9em%22 font-size=%2290%22>⛽</text></svg>">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.css">
<style>
:root{--bg:#f2f2f7;--card:#fff;--fill:rgba(118,118,128,.12);--segon:#fff;--fg:#1c1c1e;--mut:#6e6e73;--line:rgba(60,60,67,.14);--grid:rgba(60,60,67,.10);--grid2:rgba(60,60,67,.05);--up:#d70015;--down:#248a3d;--ok:#34c759;--accent:#007aff;--glass:rgba(242,242,247,.8);--shadow:0 1px 2px rgba(0,0,0,.04),0 6px 24px rgba(0,0,0,.05)}
@media(prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#000;--card:#1c1c1e;--fill:rgba(118,118,128,.28);--segon:#636366;--fg:#f5f5f7;--mut:#98989f;--line:rgba(84,84,88,.55);--grid:rgba(84,84,88,.45);--grid2:rgba(84,84,88,.2);--up:#ff453a;--down:#30d158;--ok:#30d158;--accent:#0a84ff;--glass:rgba(0,0,0,.72);--shadow:none}}
:root[data-theme="dark"]{--bg:#000;--card:#1c1c1e;--fill:rgba(118,118,128,.28);--segon:#636366;--fg:#f5f5f7;--mut:#98989f;--line:rgba(84,84,88,.55);--grid:rgba(84,84,88,.45);--grid2:rgba(84,84,88,.2);--up:#ff453a;--down:#30d158;--ok:#30d158;--accent:#0a84ff;--glass:rgba(0,0,0,.72);--shadow:none}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
[hidden]{display:none!important}
html{background:var(--bg)}
body{margin:0;background:var(--bg);color:var(--fg);font-family:-apple-system,BlinkMacSystemFont,"SF Pro Text","SF Pro Display","Segoe UI",Roboto,Helvetica,Arial,sans-serif;-webkit-font-smoothing:antialiased;font-variant-numeric:tabular-nums;line-height:1.35}
main{max-width:680px;margin:0 auto;padding:max(22px,env(safe-area-inset-top)) 18px calc(96px + env(safe-area-inset-bottom))}
header.top{margin:6px 2px 12px}
h1{margin:0;font-size:34px;font-weight:700;letter-spacing:-.03em;line-height:1.1}
h2{margin:22px 6px 8px;font-size:13px;font-weight:600;letter-spacing:.02em;text-transform:uppercase;color:var(--mut)}
.sub{color:var(--mut);font-size:14px;margin-top:4px}
button,input{font:inherit;color:var(--fg)}
.bar{position:sticky;top:0;z-index:20;margin:0 -18px 16px;padding:8px 18px;background:var(--glass);-webkit-backdrop-filter:saturate(180%) blur(20px);backdrop-filter:saturate(180%) blur(20px)}
.seg{display:flex;gap:2px;background:var(--fill);padding:2px;border-radius:10px;overflow-x:auto;scrollbar-width:none}
.seg::-webkit-scrollbar{display:none}
.seg button{flex:1 0 auto;white-space:nowrap;border:0;background:transparent;padding:7px 14px;border-radius:8px;font-size:14px;font-weight:500;cursor:pointer}
.seg button.on{background:var(--segon);font-weight:600;box-shadow:0 3px 8px rgba(0,0,0,.12),0 0 0 .5px rgba(0,0,0,.04)}
.hero{background:var(--card);border-radius:26px;padding:24px 22px 22px;margin-bottom:22px;box-shadow:var(--shadow)}
.eyebrow{font-size:13px;font-weight:600;color:var(--mut)}
.big{font-size:clamp(58px,16vw,92px);font-weight:700;letter-spacing:-.05em;line-height:1;margin:8px 0 8px}
.big small{font-size:.26em;font-weight:600;color:var(--mut);letter-spacing:0;margin-left:6px}
.quem{font-size:17px;font-weight:600;display:flex;align-items:center;flex-wrap:wrap;gap:7px}
.quem a{font-weight:500;color:var(--accent);text-decoration:none;font-size:15px}
.hint{margin-top:10px;font-size:14px;color:var(--mut)}
.list{background:var(--card);border-radius:20px;overflow:hidden;box-shadow:var(--shadow)}
details.row{border-top:.5px solid var(--line)}
details.row:first-child{border-top:0}
summary{list-style:none;display:flex;align-items:center;gap:12px;padding:14px 16px;cursor:pointer}
summary::-webkit-details-marker{display:none}
summary:active{background:var(--fill)}
.dot{width:10px;height:10px;border-radius:50%;flex:none;display:inline-block}
.info{flex:1;min-width:0;display:flex;flex-direction:column;gap:2px}
.nm{font-size:17px;font-weight:600}
.s2{font-size:13px;color:var(--mut)}
.pr{font-size:21px;font-weight:600;letter-spacing:-.02em;text-align:right}
.pr small{font-size:12px;font-weight:500;color:var(--mut);margin-left:2px}
.chev{color:var(--mut);font-size:20px;transition:transform .2s;flex:none;width:10px;text-align:center;opacity:.7}
details[open] .chev{transform:rotate(90deg)}
.det{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px 14px;padding:2px 16px 16px 38px}
.det div>span:first-child{display:block;font-size:12px;color:var(--mut);margin-bottom:1px}
.det b{font-size:15px;font-weight:600}
.det a{color:var(--accent);text-decoration:none;font-size:15px;font-weight:500;align-self:end}
.blk{background:var(--card);border-radius:20px;padding:16px;margin-bottom:18px;box-shadow:var(--shadow)}
.tb{display:flex;gap:10px;flex-wrap:wrap;align-items:center;justify-content:space-between;margin-bottom:12px}
.lnk{background:none;border:0;color:var(--accent);font-size:14px;cursor:pointer;padding:4px 2px}
.sw{display:flex;align-items:center;gap:8px;font-size:14px;color:var(--mut);cursor:pointer}
.sw input{position:absolute;opacity:0;pointer-events:none}
.sw i{width:42px;height:26px;border-radius:13px;background:var(--fill);position:relative;transition:background .2s;flex:none}
.sw i::after{content:"";position:absolute;left:2px;top:2px;width:22px;height:22px;border-radius:50%;background:#fff;box-shadow:0 2px 4px rgba(0,0,0,.25);transition:transform .2s}
.sw input:checked+i{background:var(--ok)}.sw input:checked+i::after{transform:translateX(16px)}
.up{color:var(--up)}.down{color:var(--down)}.mut{color:var(--mut)}
.chips{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:10px}
.chips div{background:var(--bg);border-radius:14px;padding:9px 13px;font-size:12px;color:var(--mut);min-width:150px;flex:1}
.chips b{display:block;font-size:19px;font-weight:600;color:var(--fg);margin:2px 0}
#box{position:relative}
#svg{display:block;width:100%;touch-action:pan-y}
.g{stroke:var(--grid)}.g2{stroke:var(--grid2)}.t{fill:var(--mut);font-size:11px}
.cur{stroke:var(--mut);stroke-dasharray:3 3}
#tip{position:absolute;display:none;pointer-events:none;background:var(--card);border:.5px solid var(--line);border-radius:14px;padding:10px 12px;font-size:12.5px;box-shadow:0 10px 30px rgba(0,0,0,.2);min-width:210px;z-index:500}
#tip div{display:flex;align-items:center;margin-top:3px}
#tip span{margin-left:auto;padding-left:12px}
#tip i,.lg i{width:9px;height:9px;border-radius:50%;flex:none;display:inline-block;margin-right:7px}
#tip .med{border-top:.5px solid var(--line);margin-top:6px;padding-top:5px;color:var(--mut)}
#legend{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
.lg{display:flex;align-items:center;font-size:13px;background:var(--bg);border:0;border-radius:999px;padding:6px 12px;cursor:pointer}
.lg span{color:var(--mut);margin-left:7px}
.lg.off{opacity:.38}
#mapa{height:calc(100vh - 300px);min-height:340px;border-radius:14px;overflow:hidden;background:var(--bg)}
.pin div{color:#fff;font-weight:700;font-size:11px;text-align:center;padding:2px 0;border-radius:11px;border:2px solid #fff;box-shadow:0 1px 4px rgba(0,0,0,.4);width:58px}
.escala{height:8px;border-radius:4px;background:linear-gradient(90deg,hsl(120,65%,38%),hsl(60,65%,38%),hsl(0,65%,38%));width:160px;display:inline-block;vertical-align:middle;margin:0 6px}
.nota{color:var(--mut);font-size:12.5px;line-height:1.5;margin:10px 2px 0}
.grp{background:var(--card);border-radius:16px;overflow:hidden;box-shadow:var(--shadow)}
.gr{display:flex;justify-content:space-between;align-items:center;gap:12px;padding:13px 16px;border-top:.5px solid var(--line);font-size:16px}
.gr:first-child{border-top:0}
.gr .v{color:var(--mut);font-size:15px;text-align:right}
.gr a{color:var(--accent);text-decoration:none}
.gr .seg{min-width:210px}
input[type=number]{width:70px;text-align:center;font-size:16px;padding:6px 8px;border-radius:9px;border:0;background:var(--fill)}
.tabs{position:fixed;left:0;right:0;bottom:0;z-index:30;display:flex;justify-content:center;background:var(--glass);-webkit-backdrop-filter:saturate(180%) blur(20px);backdrop-filter:saturate(180%) blur(20px);border-top:.5px solid var(--line);padding:6px 10px calc(6px + env(safe-area-inset-bottom))}
.tabs a{flex:1;max-width:130px;display:flex;flex-direction:column;align-items:center;gap:2px;text-decoration:none;color:var(--mut);font-size:10.5px;font-weight:500;padding:4px 0}
.tabs a.on{color:var(--accent)}
.tabs svg{width:25px;height:25px;fill:none;stroke:currentColor;stroke-width:1.7;stroke-linecap:round;stroke-linejoin:round}
@media(prefers-reduced-motion:reduce){*{transition:none!important}}
@media(max-width:520px){main{padding-left:14px;padding-right:14px}.bar{margin-left:-14px;margin-right:-14px;padding-left:14px;padding-right:14px}.hero{padding:20px 18px 18px;border-radius:24px}.gr .seg{min-width:170px}}

.btn{border:0;background:var(--accent);color:#fff;padding:10px 16px;border-radius:12px;font-size:15px;font-weight:600;cursor:pointer}
.dv{padding:18px 18px 16px;margin-bottom:22px}
.dv .big2{font-size:23px;font-weight:700;letter-spacing:-.02em;margin:4px 0 8px;display:flex;align-items:center;gap:8px}
.dv p{margin:6px 0 0;color:var(--mut);font-size:14.5px;line-height:1.45}
.dv p b{color:var(--fg)}.dv p b.down{color:var(--down)}.dv p.up{color:var(--up)}
.dv .peq{font-size:12px}
.sec2{display:flex;justify-content:space-between;align-items:center;gap:10px;margin:22px 0 8px}
.sec2 h2{margin:0 6px}
.seg.mini{min-width:0}.seg.mini button{padding:5px 12px;font-size:13px}
.star{border:0;background:none;font-size:21px;line-height:1;color:var(--mut);cursor:pointer;padding:4px 2px;flex:none}
.star.on{color:#ff9f0a}
select.sel{font:inherit;font-size:15px;padding:8px 10px;border-radius:10px;border:0;background:var(--fill);color:var(--fg);max-width:62%}
.dia{padding:12px 16px 4px;font-size:12px;font-weight:600;color:var(--mut);text-transform:uppercase;letter-spacing:.03em}
.hr{display:flex;justify-content:space-between;align-items:center;gap:12px;padding:11px 16px;border-top:.5px solid var(--line)}
.hr .l b{display:block;font-size:16px;font-weight:600}
.hr .l span{font-size:13px;color:var(--mut)}
.hr .r{font-size:15px;font-weight:600;text-align:right;white-space:nowrap}
.vazio{padding:24px 16px;color:var(--mut);font-size:14px;text-align:center}
.gr .v{margin-right:8px}
.gr .ac{display:flex;align-items:center;gap:6px}
</style></head><body>
<main>
<header class="top"><h1 id="titulo">Hoje</h1><div class="sub" id="subt"></div></header>
<div class="bar" id="barra"><nav class="seg" id="pills"></nav></div>

<section class="page" id="p-hoje">
  <div class="hero" id="hero"></div>
  <div id="desvio"></div>
  <div class="sec2"><h2>Postos</h2><nav class="seg mini" id="filtroLista"><button data-f="todos" class="on">Todos</button><button data-f="favs">★ Favoritos</button></nav></div>
  <nav class="seg" id="ordem" hidden style="margin-bottom:10px"><button data-o="preco" class="on">Preço</button><button data-o="total">Custo total</button><button data-o="perto">Mais perto</button></nav>
  <div class="list" id="cards"></div>
  <p class="nota" id="semComb"></p>
</section>

<section class="page" id="p-grafico" hidden>
  <div class="blk">
    <div class="tb"><nav class="seg" style="min-width:230px"><button data-p="7">7 dias</button><button data-p="30">30 dias</button><button data-p="tudo">Tudo</button></nav>
    <label class="sw"><input type="checkbox" id="media" checked><i></i>Média</label></div>
    <div class="chips" id="chips"></div>
    <div id="box"><svg id="svg"></svg><div id="tip"></div></div>
    <div id="legend"></div>
    <div class="tb" style="margin:8px 0 0;justify-content:flex-start;gap:14px"><button class="lnk" id="todos">Mostrar todos</button><button class="lnk" id="nenhum">Ocultar todos</button></div>
  </div>
  <p class="nota">Passa o rato (ou o dedo) sobre o gráfico para ver o preço de cada posto; em cima da linha de um posto vês só os dados desse posto. Cada degrau é uma mudança de preço.</p>
</section>

<section class="page" id="p-mapa" hidden>
  <div class="blk"><div id="mapa"></div>
  <p class="nota">Barato<span class="escala"></span>caro (dentro do combustível escolhido). Toca num posto para ver os detalhes.</p></div>
</section>

<section class="page" id="p-historico" hidden>
  <div class="tb"><select class="sel" id="hPosto"></select><button class="lnk" id="hCsv">Exportar CSV</button></div>
  <div class="list" id="hLista"></div>
  <p class="nota">Mudanças de preço registadas pelo vigilante, para o combustível escolhido no topo. O CSV inclui todos os combustíveis.</p>
</section>

<section class="page" id="p-ajustes" hidden>
  <h2>O teu carro</h2>
  <div class="grp">
    <div class="gr"><span>Depósito</span><span><input type="number" id="litros" min="1" max="200" step="1"> litros</span></div>
    <div class="gr"><span>Consumo</span><span><input type="number" id="consumo" min="1" max="30" step="0.1"> L/100 km</span></div>
    <div class="gr"><span>A minha localização</span><span class="ac"><span class="v" id="locEstado"></span><button class="lnk" id="locBtn2">Usar</button></span></div>
  </div>
  <p class="nota">A localização fica só neste dispositivo e serve apenas para calcular distâncias e ver se compensa o desvio.</p>
  <h2>Aspeto</h2>
  <div class="grp">
    <div class="gr"><span>Tema</span><nav class="seg" id="temaSeg"><button data-t="auto">Automático</button><button data-t="claro">Claro</button><button data-t="escuro">Escuro</button></nav></div>
  </div>
  <h2>Sobre</h2>
  <div class="grp">
    <div class="gr"><span>Atualizado em</span><span class="v" id="upd"></span></div>
    <div class="gr"><span>Fonte dos preços</span><span class="v">DGEG e Plenergy</span></div>
    <div class="gr"><span>Mapa</span><span class="v">© OpenStreetMap</span></div>
    <div class="gr"><span>Código</span><a href="https://github.com/rodrigoosv/combustiveis-" target="_blank" rel="noopener">GitHub ↗</a></div>
  </div>
  <p class="nota">As variações a 24 horas e a 7 dias contam desde que o vigilante começou a registar (até lá aparece «—»). A poupança compara com o posto mais caro da lista.</p>
</section>
</main>

<nav class="tabs">
  <a href="#/hoje" data-p="hoje"><svg viewBox="0 0 24 24"><path d="M3 11.5 12 4l9 7.5"/><path d="M5.5 10v9.5h13V10"/></svg>Hoje</a>
  <a href="#/grafico" data-p="grafico"><svg viewBox="0 0 24 24"><path d="M4 19V5"/><path d="M4 19h16"/><path d="M7 15l4-5 3 3 5-7"/></svg>Gráfico</a>
  <a href="#/mapa" data-p="mapa"><svg viewBox="0 0 24 24"><path d="M12 21s-6.5-5.6-6.5-10.5a6.5 6.5 0 0 1 13 0C18.5 15.4 12 21 12 21z"/><circle cx="12" cy="10.5" r="2.4"/></svg>Mapa</a>
  <a href="#/historico" data-p="historico"><svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="8.5"/><path d="M12 7.5V12l3 2"/></svg>Histórico</a>
  <a href="#/ajustes" data-p="ajustes"><svg viewBox="0 0 24 24"><path d="M4 7h10"/><path d="M18 7h2"/><circle cx="16" cy="7" r="2"/><path d="M4 17h2"/><path d="M10 17h10"/><circle cx="8" cy="17" r="2"/></svg>Ajustes</a>
</nav>
<script src="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.js"></script>
<script>
const D = __DADOS__;
const $ = id => document.getElementById(id);
const pad = n => String(n).padStart(2, '0');
const fd = (ms, h) => { const d = new Date(ms); return pad(d.getUTCDate()) + '/' + pad(d.getUTCMonth() + 1) + (h ? ' ' + pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes()) : ''); };
const vc = v => v.toFixed(3).replace('.', ',');
const eur = v => vc(v) + ' €';
const eur2 = v => v.toFixed(2).replace('.', ',') + ' €';
const DIA = 864e5, NOW = D.x1;
let grupo = D.grupos['Gasóleo simples'] ? 'Gasóleo simples' : Object.keys(D.grupos)[0];
let periodo = 'tudo', litros = 40, geo = null, map = null, camada = null;
const hidden = new Set();
try { litros = parseFloat(localStorage.getItem('litros')) || 40; } catch (e) {}
const valorEm = (s, t) => { let v = s.p[0][1]; for (const q of s.p) { if (q[0] <= t) v = q[1]; else break; } return v; };
const delta = (s, dias) => { const t = NOW - dias * DIA; return t < D.x0 ? null : s.a - valorEm(s, t); };
const sorted = g => D.grupos[g].slice().sort((a, b) => a.a - b.a || a.n.localeCompare(b.n));
const maps = s => 'https://www.google.com/maps/search/?api=1&query=' + s.lat + ',' + s.lon;

function dl(d) {
  if (d === null) return '<span class="mut">—</span>';
  const c = Math.round(d * 1000) / 10;
  if (c === 0) return '<span class="mut">=</span>';
  return '<span class="' + (c > 0 ? 'up' : 'down') + '">' + (c > 0 ? '⬆️ +' : '⬇️ ') + c.toFixed(1).replace('.', ',') + ' cênt.</span>';
}

const ROT = {'Gasóleo simples': 'Gasóleo', 'Gasóleo especial / plus': 'Gasóleo plus', 'Gasolina 95 simples': 'Gasolina 95', 'Gasolina 95 especial / plus': 'Gasolina 95 plus', 'Gasolina 98': 'Gasolina 98', 'GPL': 'GPL'};
const rotulo = g => ROT[g] || g;
const MES = ['janeiro', 'fevereiro', 'março', 'abril', 'maio', 'junho', 'julho', 'agosto', 'setembro', 'outubro', 'novembro', 'dezembro'];
const PAGS = ['hoje', 'grafico', 'mapa', 'historico', 'ajustes'];
const TIT = {hoje: 'Hoje', grafico: 'Gráfico', mapa: 'Mapa', historico: 'Histórico', ajustes: 'Ajustes'};
const SUB = {hoje: () => 'Marinha Grande e Leiria', grafico: () => 'Evolução dos preços', mapa: () => 'Postos e preços', historico: () => 'Mudanças de preço', ajustes: () => 'O teu carro, aspeto e informação'};
const FATOR = 1.3;
let pagina = 'hoje', pos = null, consumo = 6.5, ordem = 'preco', soFavs = false, locErro = '', hPosto = '';
let favs = new Set();
try { const g = localStorage.getItem('grupo'); if (g && D.grupos[g]) grupo = g; } catch (e) {}
try { pos = JSON.parse(localStorage.getItem('pos') || 'null'); } catch (e) {}
try { consumo = parseFloat(localStorage.getItem('consumo')) || 6.5; } catch (e) {}
try { favs = new Set(JSON.parse(localStorage.getItem('favs') || '[]')); } catch (e) {}
const guardar = (k, v) => { try { localStorage.setItem(k, typeof v === 'string' ? v : JSON.stringify(v)); } catch (e) {} };

function hav(a, b, c, d) { const R = 6371, r = Math.PI / 180, x = Math.sin((c - a) * r / 2) ** 2 + Math.cos(a * r) * Math.cos(c * r) * Math.sin((d - b) * r / 2) ** 2; return 2 * R * Math.asin(Math.sqrt(x)); }
const distKm = s => (pos && s.lat != null && s.lon != null) ? hav(pos.lat, pos.lon, s.lat, s.lon) * FATOR : null;
const viagem = s => { const d = distKm(s); return d === null ? null : 2 * d * consumo / 100 * s.a; };
const totalS = s => { const v = viagem(s); return v === null ? null : litros * s.a + v; };
const km1 = d => d < 10 ? d.toFixed(1).replace('.', ',') + ' km' : Math.round(d) + ' km';

function renderPills() {
  $('pills').innerHTML = Object.keys(D.grupos).map(g => '<button class="' + (g === grupo ? 'on' : '') + '" data-g="' + g + '">' + rotulo(g) + '</button>').join('');
  document.querySelectorAll('#pills button').forEach(b => b.onclick = () => { grupo = b.dataset.g; guardar('grupo', grupo); renderPills(); renderTudo(); });
}

function renderHero() {
  const el = $('hero'), ss = sorted(grupo);
  if (!ss.length) { el.innerHTML = '<p class="mut">Ainda não há dados para este combustível.</p>'; return; }
  const b = ss[0], dif = ss[ss.length - 1].a - b.a;
  el.innerHTML = '<div class="eyebrow">Mais barato agora</div>' +
    '<div class="big">' + vc(b.a) + '<small>€/litro</small></div>' +
    '<div class="quem"><span class="dot" style="background:' + b.c + '"></span>' + b.n + (b.lat != null ? ' <a href="' + maps(b) + '" target="_blank" rel="noopener">Mapa ↗</a>' : '') + '</div>' +
    (dif > 0.0004 ? '<div class="hint">Poupas até <b class="down">' + eur2(litros * dif) + '</b> num depósito de ' + litros + ' L, face ao posto mais caro.</div>' : '');
}

function renderDesvio() {
  const el = $('desvio'), ss = sorted(grupo).filter(s => s.lat != null && s.lon != null);
  if (!ss.length) { el.innerHTML = ''; return; }
  if (!pos) {
    el.innerHTML = '<div class="blk dv"><div class="eyebrow">Compensa o desvio?</div><div class="big2">Descobre o posto que mais compensa</div>' +
      '<p>Tem em conta a distância e o consumo do teu carro. A localização fica só neste dispositivo.</p>' +
      '<div style="margin-top:12px"><button class="btn" id="locBtn">Usar a minha localização</button></div>' + (locErro ? '<p class="up">' + locErro + '</p>' : '') + '</div>';
    $('locBtn').onclick = pedirLocal; return;
  }
  const melhor = ss.slice().sort((a, b) => totalS(a) - totalS(b))[0];
  const perto = ss.slice().sort((a, b) => distKm(a) - distKm(b))[0], barato = ss[0];
  let h = '<div class="blk dv"><div class="eyebrow">Melhor opção para ti</div>' +
    '<div class="big2"><span class="dot" style="background:' + melhor.c + '"></span>' + melhor.n + '</div>' +
    '<p>' + km1(distKm(melhor)) + ' · depósito ' + eur2(litros * melhor.a) + ' + viagem ' + eur2(viagem(melhor)) + ' = <b>' + eur2(totalS(melhor)) + '</b></p>';
  if (melhor !== perto) h += '<p>Face ao posto mais perto (' + perto.n + ', ' + km1(distKm(perto)) + ') poupas <b class="down">' + eur2(totalS(perto) - totalS(melhor)) + '</b>.</p>';
  else h += '<p>É também o posto mais perto de ti.</p>';
  if (barato !== melhor) h += '<p>O mais barato (' + barato.n + ', ' + eur(barato.a) + ') fica a ' + km1(distKm(barato)) + ': só a viagem custa ' + eur2(viagem(barato)) + ', e o desvio anula a vantagem.</p>';
  h += '<p class="peq">Estimativa: distância em linha reta × 1,3, ida e volta, com ' + String(consumo).replace('.', ',') + ' L/100 km. <button class="lnk" id="locRem">Remover localização</button></p></div>';
  el.innerHTML = h; $('locRem').onclick = removerLocal;
}

function pedirLocal() {
  locErro = '';
  if (!navigator.geolocation) { locErro = 'Este browser não permite obter a localização.'; renderDesvio(); return; }
  navigator.geolocation.getCurrentPosition(
    p => { pos = {lat: p.coords.latitude, lon: p.coords.longitude}; guardar('pos', pos); atualizarLoc(); renderTudo(); },
    () => { locErro = 'Não consegui obter a localização. Confirma a permissão no browser.'; atualizarLoc(); renderDesvio(); },
    {timeout: 10000, maximumAge: 600000});
}
function removerLocal() { pos = null; ordem = 'preco'; try { localStorage.removeItem('pos'); } catch (e) {} atualizarLoc(); renderTudo(); }
function atualizarLoc() {
  $('locEstado').textContent = pos ? 'Ativa' : 'Desligada';
  $('locBtn2').textContent = pos ? 'Remover' : 'Usar';
  $('ordem').hidden = !pos;
  document.querySelectorAll('#ordem button').forEach(b => b.classList.toggle('on', b.dataset.o === ordem));
}

function resumoVar(s) {
  const d1 = delta(s, 1), d7 = delta(s, 7);
  if (d1 !== null && Math.round(d1 * 1000) !== 0) return dl(d1) + ' em 24 h';
  if (d7 !== null && Math.round(d7 * 1000) !== 0) return dl(d7) + ' em 7 dias';
  return 'Sem alterações recentes';
}

function renderCards() {
  const el = $('cards');
  let ss = sorted(grupo);
  if (!ss.length) { el.innerHTML = ''; return; }
  const maxA = ss[ss.length - 1].a;
  if (soFavs) ss = ss.filter(s => favs.has(s.n));
  if (pos && ordem === 'total') ss = ss.slice().sort((a, b) => (totalS(a) ?? 1e9) - (totalS(b) ?? 1e9));
  if (pos && ordem === 'perto') ss = ss.slice().sort((a, b) => (distKm(a) ?? 1e9) - (distKm(b) ?? 1e9));
  if (!ss.length) { el.innerHTML = '<div class="vazio">' + (soFavs ? 'Ainda não tens favoritos. Toca na ☆ de um posto para o fixar aqui.' : 'Sem postos.') + '</div>'; return; }
  const aberto = new Set([...el.querySelectorAll('details[open]')].map(d => d.dataset.n));
  el.innerHTML = ss.map(s => {
    const vals = s.p.map(q => q[1]), mn = Math.min(...vals), mx = Math.max(...vals), poupa = litros * (maxA - s.a), f = favs.has(s.n), d = distKm(s);
    return '<details class="row" data-n="' + s.n + '"' + (aberto.has(s.n) ? ' open' : '') + '><summary>' +
      '<span class="dot" style="background:' + s.c + '"></span>' +
      '<span class="info"><span class="nm">' + s.n + '</span><span class="s2">' + resumoVar(s) + (d !== null ? ' · ' + km1(d) : '') + '</span></span>' +
      '<button class="star' + (f ? ' on' : '') + '" data-n="' + s.n + '" aria-label="Favorito">' + (f ? '★' : '☆') + '</button>' +
      '<span class="pr">' + vc(s.a) + '<small>€</small></span><span class="chev">›</span></summary>' +
      '<div class="det">' +
      '<div><span>24 horas</span><b>' + dl(delta(s, 1)) + '</b></div>' +
      '<div><span>7 dias</span><b>' + dl(delta(s, 7)) + '</b></div>' +
      '<div><span>Mínimo</span><b>' + eur(mn) + '</b></div>' +
      '<div><span>Máximo</span><b>' + eur(mx) + '</b></div>' +
      '<div><span>Depósito de ' + litros + ' L</span><b>' + eur2(litros * s.a) + '</b></div>' +
      '<div><span>Poupas face ao mais caro</span><b>' + (poupa > 0.004 ? '<span class="down">' + eur2(poupa) + '</span>' : '—') + '</b></div>' +
      (d !== null ? '<div><span>Distância (estimada)</span><b>' + km1(d) + '</b></div><div><span>Viagem ida e volta</span><b>' + eur2(viagem(s)) + '</b></div><div><span>Total com viagem</span><b>' + eur2(totalS(s)) + '</b></div>' : '') +
      (s.lat != null ? '<a href="' + maps(s) + '" target="_blank" rel="noopener">Google Maps ↗</a>' : '') +
      '</div></details>';
  }).join('');
}

function renderSemComb() {
  const el = $('semComb'), tem = new Set((D.grupos[grupo] || []).map(s => s.n));
  const falta = (D.todos || []).filter(p => !tem.has(p.n));
  el.innerHTML = falta.length ? 'Não vendem ' + rotulo(grupo) + ': ' + falta.map(p => '<b>' + p.n + '</b>' + (p.g.length ? ' (tem ' + p.g.map(rotulo).join(', ') + ')' : '')).join('; ') + '.' : '';
}

const hh = ms => { const d = new Date(ms); return pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes()); };
const diaTxt = ms => { const d = new Date(ms); return d.getUTCDate() + ' de ' + MES[d.getUTCMonth()] + ' de ' + d.getUTCFullYear(); };

function renderHistorico() {
  const rows = D.hist.filter(r => r[2] === grupo);
  const postos = [...new Set(rows.map(r => r[1]))].sort((a, b) => a.localeCompare(b));
  if (!postos.includes(hPosto)) hPosto = '';
  $('hPosto').innerHTML = '<option value="">Todos os postos</option>' + postos.map(n => '<option' + (n === hPosto ? ' selected' : '') + '>' + n + '</option>').join('');
  const vis = rows.filter(r => !hPosto || r[1] === hPosto).sort((a, b) => b[0] - a[0]).slice(0, 300);
  if (!vis.length) { $('hLista').innerHTML = '<div class="vazio">Ainda sem mudanças de preço registadas para este combustível.</div>'; return; }
  let h = '', dia = '';
  vis.forEach(r => {
    const d = diaTxt(r[0]); if (d !== dia) { dia = d; h += '<div class="dia">' + d + '</div>'; }
    const ant = r[4], novo = r[5];
    h += '<div class="hr"><div class="l"><b>' + r[1] + '</b><span>' + (ant === null ? eur(novo) : vc(ant) + ' → ' + eur(novo)) + ' · ' + hh(r[0]) + '</span></div><div class="r">' + (ant === null ? '<span class="mut">novo</span>' : dl(novo - ant)) + '</div></div>';
  });
  $('hLista').innerHTML = h;
}

function exportarCsv() {
  const linhas = [['data_hora', 'posto', 'combustivel', 'preco_anterior', 'preco_novo', 'variacao_cent']];
  D.hist.slice().sort((a, b) => a[0] - b[0]).forEach(r => {
    const d = new Date(r[0]), ts = d.getUTCFullYear() + '-' + pad(d.getUTCMonth() + 1) + '-' + pad(d.getUTCDate()) + ' ' + pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes());
    const v = r[4] === null ? '' : ((r[5] - r[4]) * 100).toFixed(1).replace('.', ',');
    linhas.push([ts, r[1], r[3], r[4] === null ? '' : r[4].toFixed(3).replace('.', ','), r[5].toFixed(3).replace('.', ','), v]);
  });
  const csv = '\ufeff' + linhas.map(l => l.map(c => '"' + String(c).replace(/"/g, '""') + '"').join(';')).join('\r\n');
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([csv], {type: 'text/csv;charset=utf-8'})); a.download = 'historico-combustiveis.csv';
  document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 1500);
}

function renderGrafico() {
  const svg = $('svg'), box = $('box');
  const todas = sorted(grupo), x0 = periodo === 'tudo' ? D.x0 : Math.max(D.x0, NOW - periodo * DIA);
  const x1 = Math.max(NOW, x0 + DIA), span = x1 - x0;
  const win = s => [[x0, valorEm(s, x0)]].concat(s.p.filter(q => q[0] > x0));
  const vis = todas.filter(s => !hidden.has(s.n)).map(s => Object.assign({}, s, {w: win(s)}));
  const base = vis.length ? vis : todas.map(s => Object.assign({}, s, {w: win(s)}));
  const W = Math.max(320, box.clientWidth), H = Math.max(300, Math.min(480, Math.round(W * 0.55)));
  const m = {l: 58, r: 30, t: 12, b: 28};
  const vals = base.flatMap(s => s.w.map(q => q[1]));
  let lo = Math.min(...vals), hi = Math.max(...vals);
  const pd = Math.max(0.02, (hi - lo) * 0.12); lo -= pd; hi += pd;
  const X = t => m.l + (t - x0) / span * (W - m.l - m.r);
  const Y = v => H - m.b - (v - lo) / (hi - lo) * (H - m.t - m.b);
  const mediaEm = t => vis.reduce((a, s) => a + valorEm(s, t), 0) / vis.length;
  geo = {W, H, m, x0, span, vis, mediaEm, Y};
  svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H); svg.setAttribute('height', H);
  let o = '';
  for (let k = 0; k < 5; k++) { const v = lo + (hi - lo) * k / 4, y = Y(v);
    o += '<line x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y + '" y2="' + y + '" class="g"/><text x="' + (m.l - 8) + '" y="' + (y + 4) + '" text-anchor="end" class="t">' + vc(v) + '</text>'; }
  for (let k = 0; k < 5; k++) { const t = x0 + span * k / 4, x = X(t);
    o += '<line x1="' + x + '" x2="' + x + '" y1="' + m.t + '" y2="' + (H - m.b) + '" class="g2"/><text x="' + x + '" y="' + (H - 8) + '" text-anchor="middle" class="t">' + fd(t, span < 2 * DIA) + '</text>'; }
  for (const s of vis) {
    let d = ''; s.w.forEach((q, i) => { d += i ? ' H' + X(q[0]) + ' V' + Y(q[1]) : 'M' + X(q[0]) + ',' + Y(q[1]); });
    d += ' H' + X(x1);
    o += '<path d="' + d + '" fill="none" stroke="' + s.c + '" stroke-width="2.2" stroke-linejoin="round" data-i="' + vis.indexOf(s) + '"/>';
    s.w.slice(1).forEach(q => { o += '<circle cx="' + X(q[0]) + '" cy="' + Y(q[1]) + '" r="3" fill="' + s.c + '"/>'; });
    o += '<circle cx="' + X(x1) + '" cy="' + Y(s.a) + '" r="4.5" fill="' + s.c + '" stroke="var(--card)" stroke-width="1.5"/>';
  }
  if ($('media').checked && vis.length > 1) {
    const ts = [...new Set([x0].concat(vis.flatMap(s => s.w.map(q => q[0]))))].sort((a, b) => a - b);
    let d = ''; ts.forEach((t, i) => { const y = Y(mediaEm(t)); d += i ? ' H' + X(t) + ' V' + y : 'M' + X(t) + ',' + y; });
    d += ' H' + X(x1);
    o += '<path d="' + d + '" fill="none" stroke="var(--fg)" stroke-width="1.8" stroke-dasharray="6 4" opacity=".65"/>';
  }
  o += '<line id="cur" y1="' + m.t + '" y2="' + (H - m.b) + '" class="cur" style="display:none"/>';
  svg.innerHTML = o;

  const lg = $('legend'); lg.innerHTML = '';
  todas.forEach(s => {
    const b = document.createElement('button'); b.className = 'lg' + (hidden.has(s.n) ? ' off' : '');
    b.innerHTML = '<i style="background:' + s.c + '"></i>' + s.n + '<span>' + eur(s.a) + '</span>';
    b.onclick = () => { hidden.has(s.n) ? hidden.delete(s.n) : hidden.add(s.n); renderGrafico(); };
    lg.appendChild(b);
  });
  let mn = null, mx = null;
  for (const s of vis) for (const q of s.w) {
    if (!mn || q[1] < mn.v) mn = {v: q[1], n: s.n, t: q[0]};
    if (!mx || q[1] > mx.v) mx = {v: q[1], n: s.n, t: q[0]};
  }
  $('chips').innerHTML = mn ? '<div>Mais baixo<b>' + eur(mn.v) + '</b><small>' + mn.n + ' · ' + fd(mn.t) + '</small></div><div>Mais alto<b>' + eur(mx.v) + '</b><small>' + mx.n + ' · ' + fd(mx.t) + '</small></div>' : '';
  document.querySelectorAll('button[data-p]').forEach(b => b.classList.toggle('on', b.dataset.p === String(periodo)));
}

function linhasEstilo(foco) {
  document.querySelectorAll('#svg path[data-i]').forEach(pth => {
    const on = foco < 0 || +pth.dataset.i === foco;
    pth.setAttribute('stroke-width', foco >= 0 && on ? 4 : 2.2);
    pth.setAttribute('opacity', on ? 1 : 0.2);
  });
}

function onMove(ev) {
  if (!geo || !geo.vis.length) return;
  const svg = $('svg'), box = $('box'), tip = $('tip');
  const r = svg.getBoundingClientRect(), px = (ev.clientX - r.left) * geo.W / r.width, py = (ev.clientY - r.top) * geo.H / r.height;
  const m = geo.m, f = Math.min(1, Math.max(0, (px - m.l) / (geo.W - m.l - m.r)));
  const t = geo.x0 + f * geo.span, x = m.l + f * (geo.W - m.l - m.r);
  const cur = $('cur'); cur.setAttribute('x1', x); cur.setAttribute('x2', x); cur.style.display = '';
  // o rato esta em cima da linha de um posto?
  let foco = -1, melhor = 12;
  geo.vis.forEach((s, j) => { const dy = Math.abs(py - geo.Y(valorEm(s, t))); if (dy < melhor) { melhor = dy; foco = j; } });
  linhasEstilo(foco);
  let h;
  if (foco >= 0) {
    const s = geo.vis[foco];
    let i0 = 0, i1 = 0;
    s.p.forEach((q, i) => { if (q[1] < s.p[i0][1]) i0 = i; if (q[1] > s.p[i1][1]) i1 = i; });
    const mud = s.p.length > 2 ? 'Última mudança<span>' + fd(s.p[s.p.length - 2][0], true) + '</span>' : 'Sem mudanças<span>desde o início</span>';
    h = '<b><i style="background:' + s.c + '"></i>' + s.n + '</b>' +
      '<div>' + fd(t, true) + '<span>' + eur(valorEm(s, t)) + '</span></div>' +
      '<div class="med">Preço atual<span>' + eur(s.a) + '</span></div>' +
      '<div>Mínimo<span>' + eur(s.p[i0][1]) + ' · ' + fd(s.p[i0][0]) + '</span></div>' +
      '<div>Máximo<span>' + eur(s.p[i1][1]) + ' · ' + fd(s.p[i1][0]) + '</span></div>' +
      '<div>' + mud + '</div>';
  } else {
    const rows = geo.vis.map(s => [s, valorEm(s, t)]).sort((a, b) => a[1] - b[1]);
    h = '<b>' + fd(t, true) + '</b>' + rows.map(q => '<div><i style="background:' + q[0].c + '"></i>' + q[0].n + '<span>' + eur(q[1]) + '</span></div>').join('');
    if ($('media').checked && geo.vis.length > 1) h += '<div class="med">Média<span>' + eur(geo.mediaEm(t)) + '</span></div>';
  }
  tip.innerHTML = h; tip.style.display = 'block';
  const bx = box.getBoundingClientRect(); let left = ev.clientX - bx.left + 14;
  if (left + tip.offsetWidth > bx.width) left = ev.clientX - bx.left - tip.offsetWidth - 14;
  tip.style.left = Math.max(0, left) + 'px'; tip.style.top = Math.max(0, ev.clientY - bx.top - 10) + 'px';
}

function renderMapa() {
  const el = $('mapa');
  if (typeof L === 'undefined') { el.innerHTML = '<p class="nota" style="padding:14px">Mapa indisponível (não foi possível carregar o Leaflet / OpenStreetMap).</p>'; return; }
  const ss = D.grupos[grupo].filter(s => s.lat != null && s.lon != null);
  if (!map) {
    map = L.map('mapa');
    L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {maxZoom: 19, attribution: '© OpenStreetMap'}).addTo(map);
    camada = L.layerGroup().addTo(map);
  }
  camada.clearLayers();
  if (!ss.length) { map.setView([39.74, -8.93], 11); return; }
  const lo = Math.min(...ss.map(s => s.a)), hi = Math.max(...ss.map(s => s.a)), pts = [];
  ss.forEach(s => {
    const f = hi > lo ? (s.a - lo) / (hi - lo) : 0, cor = 'hsl(' + Math.round(120 - 120 * f) + ',65%,38%)';
    const icon = L.divIcon({className: 'pin', html: '<div style="background:' + cor + '">' + vc(s.a) + '</div>', iconSize: [58, 22], iconAnchor: [29, 11]});
    const pop = '<b>' + s.n + '</b><br>' + eur(s.a) + (s.m ? '<br>' + s.m : '') + '<br><a href="' + maps(s) + '" target="_blank" rel="noopener">Abrir no Google Maps ↗</a>';
    L.marker([s.lat, s.lon], {icon: icon}).bindPopup(pop).addTo(camada);
    pts.push([s.lat, s.lon]);
  });
  map.fitBounds(pts, {padding: [30, 30], maxZoom: 14});
  setTimeout(() => map.invalidateSize(), 0);
}

function renderTudo() {
  renderHero(); renderDesvio(); renderCards(); renderSemComb();
  if (pagina === 'grafico') renderGrafico();
  if (pagina === 'mapa') renderMapa();
  if (pagina === 'historico') renderHistorico();
}

function mostrar() {
  const h = location.hash.replace(/^#\/?/, '') || 'hoje';
  pagina = PAGS.includes(h) ? h : 'hoje';
  PAGS.forEach(p => { $('p-' + p).hidden = p !== pagina; });
  document.querySelectorAll('.tabs a').forEach(a => a.classList.toggle('on', a.dataset.p === pagina));
  $('titulo').textContent = TIT[pagina]; $('subt').textContent = SUB[pagina]();
  $('barra').hidden = pagina === 'ajustes';
  document.title = TIT[pagina] + ' · Combustíveis';
  window.scrollTo(0, 0);
  if (pagina === 'grafico') renderGrafico();
  if (pagina === 'mapa') renderMapa();
  if (pagina === 'historico') renderHistorico();
}

function aplicarTema(t) {
  if (t === 'auto') document.documentElement.removeAttribute('data-theme'); else document.documentElement.dataset.theme = t === 'claro' ? 'light' : 'dark';
  document.querySelectorAll('#temaSeg button').forEach(b => b.classList.toggle('on', b.dataset.t === t));
}
let tema = 'auto';
try { tema = localStorage.getItem('tema') || 'auto'; } catch (e) {}
aplicarTema(tema);
document.querySelectorAll('#temaSeg button').forEach(b => b.onclick = () => { tema = b.dataset.t; guardar('tema', tema); aplicarTema(tema); });

$('upd').textContent = D.atualizado;
$('litros').value = litros; $('consumo').value = consumo;
$('litros').oninput = e => { const v = parseFloat(e.target.value); if (v > 0) { litros = v; guardar('litros', String(v)); renderHero(); renderDesvio(); renderCards(); } };
$('consumo').oninput = e => { const v = parseFloat(e.target.value); if (v > 0) { consumo = v; guardar('consumo', String(v)); renderDesvio(); renderCards(); } };
$('locBtn2').onclick = () => pos ? removerLocal() : pedirLocal();
document.querySelectorAll('#filtroLista button').forEach(b => b.onclick = () => { soFavs = b.dataset.f === 'favs'; document.querySelectorAll('#filtroLista button').forEach(x => x.classList.toggle('on', x === b)); renderCards(); });
document.querySelectorAll('#ordem button').forEach(b => b.onclick = () => { ordem = b.dataset.o; atualizarLoc(); renderCards(); });
$('cards').addEventListener('click', e => {
  const st = e.target.closest('.star'); if (!st) return;
  e.preventDefault(); const n = st.dataset.n;
  favs.has(n) ? favs.delete(n) : favs.add(n); guardar('favs', [...favs]); renderCards();
});
$('hPosto').onchange = e => { hPosto = e.target.value; renderHistorico(); };
$('hCsv').onclick = exportarCsv;
document.querySelectorAll('button[data-p]').forEach(b => b.onclick = () => { periodo = b.dataset.p === 'tudo' ? 'tudo' : parseInt(b.dataset.p); renderGrafico(); });
$('media').onchange = renderGrafico;
$('todos').onclick = () => { hidden.clear(); renderGrafico(); };
$('nenhum').onclick = () => { (D.grupos[grupo] || []).forEach(s => hidden.add(s.n)); renderGrafico(); };
$('svg').addEventListener('pointermove', onMove);
$('svg').addEventListener('pointerleave', () => { $('tip').style.display = 'none'; const c = $('cur'); if (c) c.style.display = 'none'; linhasEstilo(-1); });
window.addEventListener('resize', () => { if (pagina === 'grafico') renderGrafico(); });
window.addEventListener('hashchange', mostrar);
atualizarLoc();
if (grupo) { renderPills(); renderTudo(); } else { $('hero').innerHTML = '<p class="mut">Ainda não há dados.</p>'; }
mostrar();
</script></body></html>
"""


def escrever_grafico(estado, hora, desde_txt):
    agora = hora.replace(tzinfo=None)
    try:
        desde = datetime.strptime(desde_txt, "%Y-%m-%d")
    except ValueError:
        desde = agora
    res, x0 = series_grafico(estado, desde, agora)
    GRAFICO.write_text(desenhar_grafico(res, x0, agora, agora.strftime("%d/%m/%Y %H:%M")), encoding="utf-8")
    escrever_dados_json(estado, desde, agora)
    dados = json.dumps(dados_pagina(estado, desde, agora), ensure_ascii=False).replace("</", "<\\/")
    PAGINA.write_text(PAGINA_HTML.replace("__DADOS__", dados), encoding="utf-8")


def mostrar_extremos(estado, so_gasoleo=True):
    """Imprime preco atual, minimo e maximo historicos (e quando) de cada posto."""
    ext = estado.get("_meta", {}).get("extremos", {})
    if not ext:
        print("Ainda nao ha extremos guardados (corre o vigilante uma vez).")
        return
    globais = {"simples": {"min": None, "max": None}, "especial": {"min": None, "max": None}}
    for pid, v in estado.items():
        if pid == "_meta":
            continue
        nome = v.get("aviso") or v.get("nome")
        linhas = []
        for comb, e in sorted(ext.get(pid, {}).items()):
            if so_gasoleo and not quer_aviso(comb):
                continue
            atual = v.get("precos", {}).get(comb, ["", ""])[0]
            linhas.append(f"  {comb}: atual {curto(atual)} | min {pt(e['min'][0])} € ({e['min'][1]}) "
                          f"| max {pt(e['max'][0])} € ({e['max'][1]})")
            t = tipo_gasoleo(comb)
            if t:
                for k, f_ in (("min", min), ("max", max)):
                    g = globais[t][k]
                    if g is None or f_(e[k][0], g[0]) != g[0]:
                        globais[t][k] = (e[k][0], nome, e[k][1])
        if linhas:
            print(nome)
            print("\n".join(linhas))
    print("\nEntre todos os postos seguidos:")
    for t, titulo in (("simples", "Gasóleo simples"), ("especial", "Gasóleo especial/plus")):
        g = globais[t]
        if g["min"] and g["max"]:
            print(f"  {titulo}: mais baixo {pt(g['min'][0])} € ({g['min'][1]}, {g['min'][2]}) | "
                  f"mais alto {pt(g['max'][0])} € ({g['max'][1]}, {g['max'][2]})")
    print("\n(Valores desde que o vigilante comecou a registar.)")


def enviar(titulo, mensagem, click=None):
    mensagem = mensagem[:3800]
    if not TOPICO:
        print(f"[sem NTFY_TOPIC] {titulo}: {mensagem}" + (f"\n  -> {click}" if click else ""))
        return
    headers = {"Title": titulo, "Tags": "fuelpump", "Priority": "high"}  # titulo so em ASCII
    if click:
        headers["Click"] = click  # tocar na notificacao abre o artigo
    r = requests.post(
        f"https://ntfy.sh/{TOPICO}",
        data=mensagem.encode("utf-8"),
        headers=headers,
        timeout=30,
    )
    r.raise_for_status()


# ------------------------------------------------------------------ main
def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(errors="replace")  # evita erros com emojis na consola do Windows
    args = set(sys.argv[1:])

    if "--teste" in args:
        enviar("Combustiveis", "Teste: as notificacoes estao a funcionar.")
        return

    if "--plenergy" in args:
        for idalvic, precos in precos_plenergy().items():
            print(f"PLENERGY ({PLENERGY_POSTOS[idalvic]}):")
            for comb, preco in precos.items():
                print(f"  {comb}: {preco}")
        return

    if "--grafico" in args:
        estado = json.loads(ESTADO.read_text(encoding="utf-8"))
        hora = hora_local()
        escrever_grafico(estado, hora, estado.get("_meta", {}).get("extremos_desde") or hora.strftime("%Y-%m-%d"))
        print(f"Grafico guardado em {GRAFICO}, {PAGINA} e {DADOS_JSON}")
        return

    if "--extremos" in args:
        mostrar_extremos(json.loads(ESTADO.read_text(encoding="utf-8")), so_gasoleo="todos" not in args)
        return

    if "--isp" in args:
        artigos, origem = obter_artigos_isp()
        print(f"{len(artigos)} artigos de previsao semanal (fonte: {origem}):")
        for titulo, url in artigos:
            print(f"- {titulo}\n  {url}")
        if artigos:
            print("\nPrevisao do mais recente:")
            print("\n".join(previsao_isp(artigos[0][1])) or "(nao consegui ler a previsao)")
        return

    if "--resumo" in args:
        texto = resumo(json.loads(ESTADO.read_text(encoding="utf-8")))
        enviar("Resumo combustiveis", texto or "Sem dados de gasoleo no estado.json")
        return

    if "--procurar" in sys.argv:
        termo = " ".join(sys.argv[sys.argv.index("--procurar") + 1:]).strip().lower()
        vistos = {}
        for p in listar_postos():
            texto = " ".join(str(v) for v in p.values() if isinstance(v, (str, int, float))).lower()
            if termo in texto:
                vistos[p.get("Id")] = p
        print(f"{len(vistos)} postos com '{termo}':")
        for pid, p in vistos.items():
            print(f"- Id {pid} | {p.get('Marca')} | {p.get('Nome')} | "
                  f"{p.get('Localidade')} | Municipio: {p.get('Municipio')}")
        return

    if "--inspect" in args:
        postos = filtrar(listar_postos())
        print(f"{len(postos)} postos encontrados")
        for p in postos[:2]:
            print("\n--- registo da lista ---")
            print(json.dumps(p, ensure_ascii=False, indent=1)[:1500])
            print("--- detalhe ---")
            print(json.dumps(pedir("GetDadosPostoMapa", {"id": p.get("Id"), "f": "json"}),
                             ensure_ascii=False, indent=1)[:3000])
        for p in postos:
            print("-", rotulo(p), "| Id", p.get("Id"))
        return

    # ---------------- execucao normal ----------------
    migrar_historico()
    hora = hora_local()
    antigo_estado = json.loads(ESTADO.read_text(encoding="utf-8")) if ESTADO.exists() else None
    meta_antiga = (antigo_estado or {}).get("_meta", {})
    falhas_antigas = meta_antiga.get("falhas", {})
    falhas, alertas = {}, []

    def falhou(chave, erro):
        n = falhas_antigas.get(chave, 0) + 1
        falhas[chave] = n
        print(f"Falhou {chave}: {erro}")
        if n == FALHAS_ALERTA:
            alertas.append(f"Falha repetida ({n}x seguidas): {chave}")

    dgeg_ok = True
    try:
        postos = filtrar(listar_postos())
    except Exception as e:
        if antigo_estado is None:
            raise
        falhou("DGEG (lista de postos)", e)
        postos, dgeg_ok = [], False
    print(f"{len(postos)} postos encontrados")

    novo_estado, mudancas, historico = {}, [], []
    stamp = hora.strftime("%Y-%m-%d %H:%M")

    extremos = json.loads(json.dumps(meta_antiga.get("extremos", {})))  # copia
    desde = meta_antiga.get("extremos_desde") or hora.strftime("%Y-%m-%d")
    dias_registo = (hora.date() - datetime.strptime(desde, "%Y-%m-%d").date()).days
    marcar_recordes = dias_registo >= DIAS_MIN_RECORDE

    def comparar(p, pid, precos, repetida, nome_hist, data_posto=""):
        ext_posto = extremos.setdefault(pid, {})
        ref = normalizar_data(data_posto, stamp)
        recordes = {}
        for comb, (preco, _) in precos.items():
            n = numero(preco)
            if n is not None:
                antes_preco = antigo_estado.get(pid, {}).get("precos", {}).get(comb) if antigo_estado else None
                r = atualizar_extremos(ext_posto, comb, n, ref)
                if r and antes_preco and antes_preco[0] != preco:
                    recordes[comb] = r
        if antigo_estado is None:
            return
        antes = antigo_estado.get(pid, {}).get("precos", {})
        for comb, (preco, _) in precos.items():
            a = antes.get(comb)
            if a is not None and a[0] == preco:
                continue
            var, direcao = variacao(numero(a[0]) if a else None, numero(preco))
            e = ext_posto.get(comb, {})
            mn, mx = e.get("min", ["", ""]), e.get("max", ["", ""])
            historico.append([stamp, nome_hist, comb,
                              num3(a[0]) if a else "", num3(preco), var, direcao,
                              fmt3(mn[0]), mn[1], fmt3(mx[0]), mx[1]])
            if quer_aviso(comb):
                mudancas.append(linha_aviso(p, comb, a[0] if a else None, preco, repetida,
                                            recordes.get(comb) if marcar_recordes else None))

    contagem_marcas = {}
    for p in postos:
        m = str(p.get("Marca"))
        contagem_marcas[m] = contagem_marcas.get(m, 0) + 1

    for p in postos:
        pid = str(p.get("Id"))
        try:
            detalhe = pedir("GetDadosPostoMapa", {"id": pid, "f": "json"})
        except Exception as e:
            falhou(f"Posto {rotulo(p)}", e)
            if antigo_estado and pid in antigo_estado:
                novo_estado[pid] = antigo_estado[pid]  # mantem o estado antigo
            continue

        data = str(detalhe.get("DataAtualizacao", "")) if isinstance(detalhe, dict) else ""
        precos = {k: [v, data] for k, v in extrair_precos(detalhe).items()}
        repetida = contagem_marcas[str(p.get("Marca"))] > 1
        novo_estado[pid] = {"nome": rotulo(p), "aviso": nome_posto(p, repetida), "precos": precos,
                            "lat": p.get("Latitude"), "lon": p.get("Longitude"), "morada": p.get("Morada")}
        time.sleep(0.5)  # nao sobrecarregar o servidor da DGEG
        comparar(p, pid, precos, repetida, rotulo(p), data)

    if not dgeg_ok:  # lista da DGEG falhou: mantem os postos DGEG antigos
        for pid, v in antigo_estado.items():
            if pid != "_meta" and not pid.startswith("plenergy-"):
                novo_estado[pid] = v

    # --- Plenergy (site deles) ---
    try:
        dados_pl = precos_plenergy()
    except Exception as e:
        falhou("Plenergy (site)", e)
        dados_pl = None
    for idalvic, localidade in PLENERGY_POSTOS.items():
        pid = f"plenergy-{idalvic}"
        p = {"Id": pid, "Marca": "PLENERGY", "Localidade": localidade}
        if dados_pl is not None and idalvic not in dados_pl:
            falhou(f"Plenergy ({localidade})", "posto sem precos no site")
        if dados_pl is None or idalvic not in dados_pl:
            if antigo_estado and pid in antigo_estado:
                novo_estado[pid] = antigo_estado[pid]  # mantem o estado antigo
            continue
        precos = {k: [v, ""] for k, v in dados_pl[idalvic].items()}
        lat, lon, morada = PLENERGY_COORDS.get(idalvic, (None, None, None))
        novo_estado[pid] = {"nome": f"PLENERGY ({localidade})", "aviso": "PLENERGY", "precos": precos,
                            "lat": lat, "lon": lon, "morada": morada}
        comparar(p, pid, precos, False, f"PLENERGY ({localidade})")

    for chave, n in falhas_antigas.items():
        if n >= FALHAS_ALERTA and chave not in falhas:
            alertas.append(f"Recuperou: {chave}")

    # --- Contas Poupanca: novos artigos de previsao semanal ---
    isp_vistos = meta_antiga.get("isp_vistos")  # None = ainda nao inicializado (nao avisa dos antigos)
    avisos_isp = []
    try:
        artigos, origem_isp = obter_artigos_isp()
        print(f"Contas Poupança: {len(artigos)} artigos de previsao (fonte: {origem_isp})")
        chaves = [sem_acentos(t) for t, _ in artigos]  # o titulo identifica a semana (igual em qualquer fonte)
        if isp_vistos is None:
            isp_vistos = chaves
        else:
            novos = [(t, u) for t, u in artigos if sem_acentos(t) not in isp_vistos]
            for titulo, url in reversed(novos):  # do mais antigo para o mais recente
                try:
                    linhas = previsao_isp(url)
                except Exception as e:
                    print(f"Nao consegui ler a previsao de {url}: {e}")
                    linhas = []
                avisos_isp.append((titulo, "\n".join([titulo] + ([""] + linhas if linhas else [])), url))
            isp_vistos = (isp_vistos + [sem_acentos(t) for t, _ in novos])[-60:]
    except Exception as e:
        falhou("Contas Poupança (site)", e)

    # --- resumo diario ---
    meta = {"falhas": falhas, "ultimo_resumo": meta_antiga.get("ultimo_resumo", "")}
    if isp_vistos is not None:
        meta["isp_vistos"] = isp_vistos
    meta["extremos_desde"] = desde
    meta["extremos"] = {pid: v for pid, v in extremos.items() if pid in novo_estado}
    hoje = hora.strftime("%Y-%m-%d")
    texto_resumo = ""
    if antigo_estado is not None and hora.hour >= HORA_RESUMO and meta["ultimo_resumo"] != hoje:
        texto_resumo = resumo(novo_estado)
        if texto_resumo:
            meta["ultimo_resumo"] = hoje
    versao_pagina = hashlib.md5(PAGINA_HTML.encode("utf-8")).hexdigest()[:8]
    gerar_grafico = ((not GRAFICO.exists()) or (not PAGINA.exists()) or (not DADOS_JSON.exists()) or bool(historico)
                     or meta_antiga.get("ultimo_grafico") != hoje
                     or meta_antiga.get("pagina_versao") != versao_pagina)  # pagina mudou: regenerar
    meta["pagina_versao"] = versao_pagina
    if gerar_grafico:
        meta["ultimo_grafico"] = hoje
    novo_estado["_meta"] = meta

    # --- enviar (antes de gravar: se o envio falhar, tenta de novo na proxima execucao) ---
    total = len(postos) + len(PLENERGY_POSTOS)
    if antigo_estado is None:
        enviar("Combustiveis", f"A vigiar {total} postos. Aviso-te quando houver atualizacoes.")
    else:
        if mudancas:
            enviar("Combustiveis", "\n".join(mudancas[:25]))
        if alertas:
            enviar("Combustiveis ALERTA", "\n".join(alertas))
        if texto_resumo:
            enviar("Resumo combustiveis", texto_resumo)
        for _, mensagem, url in avisos_isp:
            enviar("ISP - previsao semanal", mensagem, click=url)

    ESTADO.write_text(json.dumps(novo_estado, ensure_ascii=False, indent=1), encoding="utf-8")
    registar_historico(historico)
    if gerar_grafico:
        try:
            escrever_grafico(novo_estado, hora, desde)
        except Exception as e:  # o grafico nunca deve estragar a execucao
            print(f"Nao consegui gerar o grafico: {e}")
    print(f"{len(mudancas)} avisos, {len(historico)} alteracoes no historico")


if __name__ == "__main__":
    main()
