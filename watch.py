#!/usr/bin/env python3
"""
Vigilante de precos de combustiveis (DGEG + Plenergy) com notificacoes no iPhone via ntfy.

Uso:
  py watch.py --teste       envia uma notificacao de teste
  py watch.py --inspect     mostra os postos encontrados e a resposta crua de 2 deles
  py watch.py --procurar X  lista os postos da DGEG que contem o texto X
  py watch.py --plenergy    mostra os precos lidos do site da Plenergy
  py watch.py --resumo      envia (ou mostra) o resumo dos gasoleos mais baratos
  py watch.py               execucao normal: compara com estado.json e avisa se algo mudou

Variavel de ambiente necessaria para as notificacoes: NTFY_TOPIC (o teu topico no ntfy)
"""
import csv
import json
import os
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests

BASE = "https://precoscombustiveis.dgeg.gov.pt/api/PrecoComb"
TOPICO = os.environ.get("NTFY_TOPIC", "").strip()
ESTADO = Path(__file__).with_name("estado.json")
HISTORICO = Path(__file__).with_name("historico.csv")
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


def linha_aviso(p, comb, antes, atual, repetida=False):
    nome = nome_posto(p, repetida)
    if antes is None:
        return f"{nome}: {comb} {curto(atual)}"
    na, nb = numero(atual), numero(antes)
    if na is not None and nb is not None and na != nb:
        emoji, verbo = ("⬇️", "desceu") if na < nb else ("⬆️", "subiu")
    else:
        emoji, verbo = "", "mudou"
    texto = f"{nome}: {comb} {verbo} para {curto(atual)} (ultimo {curto(antes)})"
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


def registar_historico(linhas):
    if not linhas:
        return
    novo = not HISTORICO.exists()
    with HISTORICO.open("a", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        if novo:
            w.writerow(["data_hora", "posto", "combustivel", "preco_anterior", "preco_novo"])
        w.writerows(linhas)


def enviar(titulo, mensagem):
    mensagem = mensagem[:3800]
    if not TOPICO:
        print(f"[sem NTFY_TOPIC] {titulo}: {mensagem}")
        return
    r = requests.post(
        f"https://ntfy.sh/{TOPICO}",
        data=mensagem.encode("utf-8"),
        headers={"Title": titulo, "Tags": "fuelpump", "Priority": "high"},  # titulo so em ASCII
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

    def comparar(p, pid, precos, repetida, nome_hist):
        if antigo_estado is None:
            return
        antes = antigo_estado.get(pid, {}).get("precos", {})
        for comb, (preco, _) in precos.items():
            a = antes.get(comb)
            if a is not None and a[0] == preco:
                continue
            historico.append([stamp, nome_hist, comb,
                              num3(a[0]) if a else "", num3(preco)])
            if quer_aviso(comb):
                mudancas.append(linha_aviso(p, comb, a[0] if a else None, preco, repetida))

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
        comparar(p, pid, precos, repetida, rotulo(p))

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

    # --- resumo diario ---
    meta = {"falhas": falhas, "ultimo_resumo": meta_antiga.get("ultimo_resumo", "")}
    hoje = hora.strftime("%Y-%m-%d")
    texto_resumo = ""
    if antigo_estado is not None and hora.hour >= HORA_RESUMO and meta["ultimo_resumo"] != hoje:
        texto_resumo = resumo(novo_estado)
        if texto_resumo:
            meta["ultimo_resumo"] = hoje
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

    ESTADO.write_text(json.dumps(novo_estado, ensure_ascii=False, indent=1), encoding="utf-8")
    registar_historico(historico)
    print(f"{len(mudancas)} avisos, {len(historico)} alteracoes no historico")


if __name__ == "__main__":
    main()
