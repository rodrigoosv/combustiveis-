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
  py watch.py --grafico     (re)gera o grafico.svg e o index.html (interativo) a partir do estado.json e do historico.csv
  py watch.py --isp         mostra os artigos 'ATUALIZACAO ISP' do Contas Poupanca e a previsao do ultimo
  py watch.py               execucao normal: compara com estado.json e avisa se algo mudou

Variavel de ambiente necessaria para as notificacoes: NTFY_TOPIC (o teu topico no ntfy)
"""
import csv
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


def dados_pagina(estado, desde, agora):
    res, x0 = series_grafico(estado, desde, agora, agrupar=grupo_combustivel)
    nomes = sorted({n for lst in res.values() for n, _, _ in lst})
    cores = {n: PALETA[i % len(PALETA)] for i, n in enumerate(nomes)}

    def ms(t):
        return int((t - datetime(1970, 1, 1)).total_seconds() * 1000)

    grupos = {g: [{"n": n, "c": cores[n], "a": atual, "p": [[ms(t), p] for t, p in pts]}
                  for n, pts, atual in res[g]] for g in ORDEM_GRUPOS if g in res}
    return {"atualizado": agora.strftime("%d/%m/%Y %H:%M"), "x0": ms(x0), "x1": ms(agora), "grupos": grupos}


PAGINA_HTML = r"""<!doctype html>
<html lang="pt"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Preços dos combustíveis</title>
<style>
:root{--bg:#fff;--fg:#1d1d1f;--mut:#6b6b70;--grid:#e6e6e8;--grid2:#f1f1f2;--card:#f4f4f6;--line:#d8d8dc}
@media(prefers-color-scheme:dark){:root{--bg:#121316;--fg:#ececec;--mut:#9a9aa0;--grid:#2c2e33;--grid2:#202226;--card:#1c1e22;--line:#34363b}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font-family:system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif}
main{max-width:1100px;margin:0 auto;padding:20px 16px 40px}
h1{margin:0 0 2px;font-size:22px}
.sub{color:var(--mut);font-size:13px;margin-bottom:16px}
.bar{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin-bottom:14px}
select,button.act{font:inherit;font-size:14px;padding:7px 10px;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--fg)}
.chips{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:12px}
.chips div{background:var(--card);border-radius:10px;padding:8px 12px;font-size:12px;color:var(--mut);min-width:190px}
.chips b{display:block;font-size:18px;color:var(--fg);margin:2px 0}
.chips small{font-size:12px}
#box{position:relative}
svg{display:block;width:100%;touch-action:pan-y}
.g{stroke:var(--grid)}.g2{stroke:var(--grid2)}.t{fill:var(--mut);font-size:11px}
.cur{stroke:var(--mut);stroke-dasharray:3 3}
#tip{position:absolute;display:none;pointer-events:none;background:var(--card);border:1px solid var(--line);border-radius:8px;padding:8px 10px;font-size:12px;box-shadow:0 4px 14px rgba(0,0,0,.18);min-width:190px;z-index:2}
#tip div{display:flex;align-items:center;gap:6px;margin-top:3px}
#tip span{margin-left:auto;font-variant-numeric:tabular-nums;padding-left:12px}
#tip i,.lg i{width:10px;height:10px;border-radius:50%;flex:none;display:inline-block}
#legend{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
.lg{display:flex;align-items:center;gap:7px;font:inherit;font-size:13px;color:var(--fg);background:var(--card);border:1px solid var(--line);border-radius:999px;padding:5px 11px;cursor:pointer}
.lg span{color:var(--mut);font-variant-numeric:tabular-nums}
.lg.off{opacity:.38}
.nota{color:var(--mut);font-size:12px;margin-top:18px;line-height:1.5}
</style></head><body><main>
<h1>Preços dos combustíveis</h1>
<div class="sub" id="sub"></div>
<div class="bar"><select id="sel"></select>
<button class="act" id="todos">Mostrar todos</button><button class="act" id="nenhum">Ocultar todos</button></div>
<div class="chips" id="chips"></div>
<div id="box"><svg id="svg"></svg><div id="tip"></div></div>
<div id="legend"></div>
<p class="nota">Passa o rato (ou o dedo) sobre o gráfico para ver o preço de cada posto nesse momento. Clica num posto da legenda para o esconder ou mostrar.
Os valores são os que o vigilante registou desde que começou; cada degrau é uma mudança de preço. Fonte: DGEG e Plenergy.</p>
</main>
<script>
const D = __DADOS__;
const $ = id => document.getElementById(id);
const pad = n => String(n).padStart(2, '0');
const fd = (ms, h) => { const d = new Date(ms); return pad(d.getUTCDate()) + '/' + pad(d.getUTCMonth() + 1) + (h ? ' ' + pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes()) : ''); };
const eur = v => v.toFixed(3).replace('.', ',') + ' €';
let grupo = D.grupos['Gasóleo simples'] ? 'Gasóleo simples' : Object.keys(D.grupos)[0];
const hidden = new Set();
let geo = null;
const valorEm = (s, t) => { let v = s.p[0][1]; for (const q of s.p) { if (q[0] <= t) v = q[1]; else break; } return v; };

function render() {
  const svg = $('svg'), box = $('box');
  if (!grupo) { $('sub').textContent = 'Ainda não há dados.'; return; }
  const todas = D.grupos[grupo].slice().sort((a, b) => a.a - b.a || a.n.localeCompare(b.n));
  const vis = todas.filter(s => !hidden.has(s.n));
  const W = Math.max(320, box.clientWidth), H = Math.max(300, Math.min(480, Math.round(W * 0.55)));
  const m = {l: 58, r: 30, t: 12, b: 28};
  const x0 = D.x0, x1 = Math.max(D.x1, D.x0 + 864e5), span = x1 - x0;
  const base = vis.length ? vis : todas;
  const vals = base.flatMap(s => s.p.map(q => q[1]));
  let lo = Math.min(...vals), hi = Math.max(...vals);
  const pd = Math.max(0.02, (hi - lo) * 0.12); lo -= pd; hi += pd;
  const X = t => m.l + (t - x0) / span * (W - m.l - m.r);
  const Y = v => H - m.b - (v - lo) / (hi - lo) * (H - m.t - m.b);
  geo = {W, H, m, x0, span, vis};
  svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H); svg.setAttribute('height', H);
  let o = '';
  for (let k = 0; k < 5; k++) { const v = lo + (hi - lo) * k / 4, y = Y(v);
    o += '<line x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y + '" y2="' + y + '" class="g"/><text x="' + (m.l - 8) + '" y="' + (y + 4) + '" text-anchor="end" class="t">' + v.toFixed(3).replace('.', ',') + '</text>'; }
  for (let k = 0; k < 5; k++) { const t = x0 + span * k / 4, x = X(t);
    o += '<line x1="' + x + '" x2="' + x + '" y1="' + m.t + '" y2="' + (H - m.b) + '" class="g2"/><text x="' + x + '" y="' + (H - 8) + '" text-anchor="middle" class="t">' + fd(t, span < 2 * 864e5) + '</text>'; }
  for (const s of vis) {
    let d = ''; s.p.forEach((q, i) => { d += i ? ' H' + X(q[0]) + ' V' + Y(q[1]) : 'M' + X(q[0]) + ',' + Y(q[1]); });
    o += '<path d="' + d + '" fill="none" stroke="' + s.c + '" stroke-width="2.2"/>';
    s.p.slice(1, -1).forEach(q => { o += '<circle cx="' + X(q[0]) + '" cy="' + Y(q[1]) + '" r="3" fill="' + s.c + '"/>'; });
    const e = s.p[s.p.length - 1]; o += '<circle cx="' + X(e[0]) + '" cy="' + Y(e[1]) + '" r="4.5" fill="' + s.c + '" stroke="var(--bg)" stroke-width="1.5"/>';
  }
  o += '<line id="cur" y1="' + m.t + '" y2="' + (H - m.b) + '" class="cur" style="display:none"/>';
  svg.innerHTML = o;

  const lg = $('legend'); lg.innerHTML = '';
  todas.forEach(s => {
    const b = document.createElement('button'); b.className = 'lg' + (hidden.has(s.n) ? ' off' : '');
    b.innerHTML = '<i style="background:' + s.c + '"></i>' + s.n + '<span>' + eur(s.a) + '</span>';
    b.onclick = () => { hidden.has(s.n) ? hidden.delete(s.n) : hidden.add(s.n); render(); };
    lg.appendChild(b);
  });
  let mn = null, mx = null;
  for (const s of vis) for (const q of s.p) {
    if (!mn || q[1] < mn.v) mn = {v: q[1], n: s.n, t: q[0]};
    if (!mx || q[1] > mx.v) mx = {v: q[1], n: s.n, t: q[0]};
  }
  $('chips').innerHTML = mn ? '<div>Mais baixo<b>' + eur(mn.v) + '</b><small>' + mn.n + ' · ' + fd(mn.t) + '</small></div><div>Mais alto<b>' + eur(mx.v) + '</b><small>' + mx.n + ' · ' + fd(mx.t) + '</small></div>' : '';
}

function onMove(ev) {
  if (!geo || !geo.vis.length) return;
  const svg = $('svg'), box = $('box'), tip = $('tip');
  const r = svg.getBoundingClientRect(), px = (ev.clientX - r.left) * geo.W / r.width;
  const m = geo.m, f = Math.min(1, Math.max(0, (px - m.l) / (geo.W - m.l - m.r)));
  const t = geo.x0 + f * geo.span, x = m.l + f * (geo.W - m.l - m.r);
  const cur = $('cur'); cur.setAttribute('x1', x); cur.setAttribute('x2', x); cur.style.display = '';
  const rows = geo.vis.map(s => [s, valorEm(s, t)]).sort((a, b) => a[1] - b[1]);
  tip.innerHTML = '<b>' + fd(t, true) + '</b>' + rows.map(q => '<div><i style="background:' + q[0].c + '"></i>' + q[0].n + '<span>' + eur(q[1]) + '</span></div>').join('');
  tip.style.display = 'block';
  const bx = box.getBoundingClientRect(); let left = ev.clientX - bx.left + 14;
  if (left + tip.offsetWidth > bx.width) left = ev.clientX - bx.left - tip.offsetWidth - 14;
  tip.style.left = Math.max(0, left) + 'px'; tip.style.top = Math.max(0, ev.clientY - bx.top - 10) + 'px';
}

$('sub').textContent = 'Atualizado em ' + D.atualizado;
Object.keys(D.grupos).forEach(g => { const op = document.createElement('option'); op.value = op.textContent = g; if (g === grupo) op.selected = true; $('sel').appendChild(op); });
$('sel').onchange = e => { grupo = e.target.value; render(); };
$('todos').onclick = () => { hidden.clear(); render(); };
$('nenhum').onclick = () => { (D.grupos[grupo] || []).forEach(s => hidden.add(s.n)); render(); };
$('svg').addEventListener('pointermove', onMove);
$('svg').addEventListener('pointerleave', () => { $('tip').style.display = 'none'; const c = $('cur'); if (c) c.style.display = 'none'; });
window.addEventListener('resize', render);
render();
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
        print(f"Grafico guardado em {GRAFICO} e {PAGINA}")
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
        novo_estado[pid] = {"nome": rotulo(p), "aviso": nome_posto(p, repetida), "precos": precos}
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
        novo_estado[pid] = {"nome": f"PLENERGY ({localidade})", "aviso": "PLENERGY", "precos": precos}
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
    gerar_grafico = (not GRAFICO.exists()) or (not PAGINA.exists()) or bool(historico) or meta_antiga.get("ultimo_grafico") != hoje
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
