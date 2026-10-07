#!/usr/bin/env python3
"""
Vigilante de precos de combustiveis (DGEG) com notificacoes no iPhone via ntfy.

Uso:
  py watch.py --teste     envia uma notificacao de teste
  py watch.py --inspect   mostra os postos encontrados e a resposta crua de 2 deles
  py watch.py             execucao normal: compara com estado.json e avisa se algo mudou

Variavel de ambiente necessaria para as notificacoes: NTFY_TOPIC (o teu topico no ntfy)
"""
import json
import os
import sys
import time
from pathlib import Path

import requests

BASE = "https://precoscombustiveis.dgeg.gov.pt/api/PrecoComb"
TOPICO = os.environ.get("NTFY_TOPIC", "").strip()
ESTADO = Path(__file__).with_name("estado.json")
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

NOMES = ("TipoCombustivel", "Combustivel", "NomeCombustivel")
PRECOS = ("Preco", "PrecoCombustivel", "Valor")


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


def main():
    args = set(sys.argv[1:])
    if "--teste" in args:
        enviar("Combustiveis", "Teste: as notificacoes estao a funcionar.")
        return

    postos = filtrar(listar_postos())
    print(f"{len(postos)} postos encontrados")

    if "--inspect" in args:
        for p in postos[:2]:
            print("\n--- registo da lista ---")
            print(json.dumps(p, ensure_ascii=False, indent=1)[:1500])
            print("--- detalhe ---")
            print(json.dumps(pedir("GetDadosPostoMapa", {"id": p.get("Id"), "f": "json"}),
                             ensure_ascii=False, indent=1)[:3000])
        for p in postos:
            print("-", rotulo(p), "| Id", p.get("Id"))
        return

    antigo_estado = json.loads(ESTADO.read_text(encoding="utf-8")) if ESTADO.exists() else None
    novo_estado, mudancas = {}, []

    for p in postos:
        pid = str(p.get("Id"))
        try:
            detalhe = pedir("GetDadosPostoMapa", {"id": pid, "f": "json"})
        except Exception as e:
            print(f"Falhou posto {pid}: {e}")
            if antigo_estado and pid in antigo_estado:
                novo_estado[pid] = antigo_estado[pid]  # mantem o estado antigo
            continue

        data = str(detalhe.get("DataAtualizacao", "")) if isinstance(detalhe, dict) else ""
        precos = {k: [v, data] for k, v in extrair_precos(detalhe).items()}
        novo_estado[pid] = {"nome": rotulo(p), "precos": precos}
        time.sleep(0.5)  # nao sobrecarregar o servidor da DGEG

        if antigo_estado is None:
            continue
        antes = antigo_estado.get(pid, {}).get("precos", {})
        for comb, (preco, _) in precos.items():
            a = antes.get(comb)
            if a is None or a[0] != preco:  # so avisa se o preco mudou
                de = f"{a[0]} -> " if a else ""
                mudancas.append(f"{rotulo(p)}: {comb} {de}{preco}")

    ESTADO.write_text(json.dumps(novo_estado, ensure_ascii=False, indent=1), encoding="utf-8")

    if antigo_estado is None:
        enviar("Combustiveis", f"A vigiar {len(postos)} postos. Aviso-te quando houver atualizacoes.")
    elif mudancas:
        enviar("Combustiveis", "\n".join(mudancas[:25]))
    print(f"{len(mudancas)} alteracoes")


if __name__ == "__main__":
    main()
