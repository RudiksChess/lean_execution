#!/usr/bin/env python3
"""Genera CursoLean.tex a partir de CursoLean.tex.in y compila el PDF.

Los fragmentos de código y los estados de prueba no se copian a mano:
se extraen del código Lean del repositorio y de los estados exportados
en artifacts/explorer/*.json. Directivas reconocidas (cada una en su propia
línea de la plantilla):

  %%CODE: ruta.lean :: nombre_declaracion%%
  %%EXCERPT: ruta.lean :: texto_inicial :: texto_final%%
  %%STATE: ruta.json :: id_paso :: before|after%%
  %%STEP: ruta.json :: id_paso%%          (antes, táctica y después)

Uso:  python3 reports/curso-lean/build.py [--no-pdf]
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

AQUI = Path(__file__).resolve().parent
RAIZ = AQUI.parents[1]
PLANTILLA = AQUI / "CursoLean.tex.in"
SALIDA = AQUI / "CursoLean.tex"
ANCHO = 88  # caracteres por línea en los bloques de código

PALABRAS_CLAVE = {
    "theorem", "lemma", "def", "abbrev", "inductive", "structure", "where",
    "by", "with", "fun", "match", "let", "have", "show", "from", "at", "in",
    "if", "then", "else", "termination_by", "decreasing_by", "namespace",
    "open", "variable", "end", "deriving", "notation", "infixr", "infixl",
    "infix", "prefix", "noncomputable", "import", "section", "example",
    "omit", "attribute", "instance", "scoped", "local",
}
TACTICAS = {
    "intro", "intros", "exact", "apply", "refine", "constructor", "cases",
    "rcases", "obtain", "rintro", "induction", "by_cases", "by_contra",
    "rw", "simp", "simpa", "subst", "change", "calc", "unfold", "omega",
    "decide", "rfl", "ext", "use", "exfalso", "contradiction", "trivial",
    "all_goals", "only", "using", "generalizing", "assumption", "left",
    "right", "specialize", "exists",
}
CARACTER_ID = r"[\w'!?ₐ-ₜ₀-₉]"
PATRON_PALABRA = re.compile(rf"(?<![\w.'@]){CARACTER_ID}+")


def escapar(texto: str) -> str:
    """Escapa texto para un Verbatim con commandchars=\\\\\\{\\}."""
    salida = []
    for c in texto:
        if c == "\\":
            salida.append(r"\textbackslash{}")
        elif c == "{":
            salida.append(r"\{")
        elif c == "}":
            salida.append(r"\}")
        else:
            salida.append(c)
    return "".join(salida)


def tokenizar_linea(linea: str, en_bloque: bool):
    """Devuelve (lista de (tipo, texto), sigue_en_bloque)."""
    tokens: list[tuple[str, str]] = []
    i = 0
    while i < len(linea):
        if en_bloque:
            fin = linea.find("-/", i)
            if fin == -1:
                tokens.append(("com", linea[i:]))
                return tokens, True
            tokens.append(("com", linea[i:fin + 2]))
            i = fin + 2
            en_bloque = False
            continue
        if linea.startswith("/-", i):
            en_bloque = True
            continue
        if linea.startswith("--", i):
            tokens.append(("com", linea[i:]))
            break
        m = PATRON_PALABRA.match(linea, i)
        if m and (i == 0 or not re.match(r"[\w.'@]", linea[i - 1])):
            palabra = m.group(0)
            if palabra in PALABRAS_CLAVE:
                tipo = "kw"
            elif palabra in TACTICAS:
                tipo = "tac"
            else:
                tipo = "txt"
            tokens.append((tipo, palabra))
            i = m.end()
            continue
        tokens.append(("txt", linea[i]))
        i += 1
    return tokens, en_bloque


def fusionar(tokens):
    fusion: list[list[str]] = []
    for tipo, texto in tokens:
        if fusion and fusion[-1][0] == tipo:
            fusion[-1][1] += texto
        else:
            fusion.append([tipo, texto])
    return [(t, x) for t, x in fusion]


def partir(tokens, ancho: int):
    """Corta una línea tokenizada en varias de a lo sumo `ancho` caracteres."""
    texto = "".join(x for _, x in tokens)
    if len(texto) <= ancho:
        return [tokens]
    sangria = len(texto) - len(texto.lstrip(" "))
    prefijo_cont = " " * (sangria + 4)
    # Expandir a caracteres con tipo, elegir cortes en espacios.
    chars = [(t, c) for t, x in tokens for c in x]
    lineas = []
    actual = chars
    primera = True
    while True:
        limite = ancho if primera else ancho - len(prefijo_cont) - 2
        if len(actual) <= limite:
            lineas.append(actual)
            break
        corte = None
        for k in range(limite, max(limite // 3, 1), -1):
            if actual[k][1] == " ":
                corte = k
                break
        if corte is None:
            corte = limite
        lineas.append(actual[:corte])
        resto = actual[corte:]
        while resto and resto[0][1] == " ":
            resto = resto[1:]
        tipo_resto = resto[0][0] if resto else "txt"
        actual = [("txt", c) for c in prefijo_cont] + [("cont", "↪ ")] + resto
        if tipo_resto == "com" and resto:
            pass
        primera = False
    salida = []
    for linea in lineas:
        toks = []
        for t, c in linea:
            if toks and toks[-1][0] == t:
                toks[-1] = (t, toks[-1][1] + c)
            else:
                toks.append((t, c))
        salida.append(toks)
    return salida


MACRO = {"kw": "LKw", "tac": "LTac", "com": "LCom", "cont": "LCont"}


def resaltar(codigo: str, ancho: int = ANCHO) -> str:
    salida = []
    en_bloque = False
    for linea in codigo.split("\n"):
        tokens, en_bloque = tokenizar_linea(linea, en_bloque)
        for trozo in partir(fusionar(tokens), ancho):
            partes = []
            for tipo, texto in trozo:
                esc = escapar(texto)
                if tipo in MACRO and texto.strip():
                    partes.append(f"\\{MACRO[tipo]}{{{esc}}}")
                else:
                    partes.append(esc)
            salida.append("".join(partes))
    return "\n".join(salida)


def bloque_codigo(codigo: str, titulo: str) -> str:
    cuerpo = resaltar(codigo.rstrip("\n"))
    return (
        f"\\begin{{codigolean}}{{{titulo}}}\n"
        "\\begin{Verbatim}[commandchars=\\\\\\{\\}]\n"
        f"{cuerpo}\n"
        "\\end{Verbatim}\n"
        "\\end{codigolean}"
    )


def leer_lineas(ruta: str) -> list[str]:
    return (RAIZ / ruta).read_text(encoding="utf-8").split("\n")


def extraer_declaracion(ruta: str, nombre: str) -> tuple[str, int]:
    lineas = leer_lineas(ruta)
    patron = re.compile(
        rf"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|inductive)\s+{re.escape(nombre)}(?![\w'.])"
    )
    for i, linea in enumerate(lineas):
        if patron.match(linea):
            fin = i + 1
            while fin < len(lineas):
                actual = lineas[fin]
                if actual == "" or actual[0] in " |":
                    fin += 1
                    continue
                # Un docstring entre constructores pertenece a la declaración.
                if actual.startswith("/--"):
                    k = fin
                    while k < len(lineas) and "-/" not in lineas[k]:
                        k += 1
                    if k + 1 < len(lineas) and lineas[k + 1][:1] in (" ", "|"):
                        fin = k + 1
                        continue
                break
            bloque = lineas[i:fin]
            while bloque and bloque[-1].strip() == "":
                bloque.pop()
            return "\n".join(bloque), i + 1
    raise SystemExit(f"No se encontró la declaración {nombre} en {ruta}")


def extraer_fragmento(ruta: str, inicio: str, final: str) -> tuple[str, int]:
    lineas = leer_lineas(ruta)
    for i, linea in enumerate(lineas):
        if inicio in linea:
            excluir = final.startswith("!")
            final_txt = final[1:] if excluir else final
            for j in range(i + 1 if excluir else i, len(lineas)):
                if final_txt in lineas[j]:
                    bloque = lineas[i:j] if excluir else lineas[i:j + 1]
                    while bloque and bloque[-1].strip() == "":
                        bloque.pop()
                    sangria = min(
                        (len(l) - len(l.lstrip(" ")) for l in bloque if l.strip()),
                        default=0,
                    )
                    bloque = [l[sangria:] for l in bloque]
                    return "\n".join(bloque), i + 1
            raise SystemExit(f"Fin «{final}» no encontrado tras «{inicio}» en {ruta}")
    raise SystemExit(f"Inicio «{inicio}» no encontrado en {ruta}")


_JSON: dict[str, dict] = {}


def paso(ruta_json: str, id_paso: str) -> dict:
    if ruta_json not in _JSON:
        datos = json.loads((RAIZ / ruta_json).read_text(encoding="utf-8"))
        _JSON[ruta_json] = {
            s["id"]: s for p in datos["proofs"] for s in p["steps"]
        }
    try:
        return _JSON[ruta_json][id_paso]
    except KeyError:
        raise SystemExit(f"Paso {id_paso} no encontrado en {ruta_json}")


def texto_metas(metas: list[dict], solo: set[str] | None = None) -> str:
    if not metas:
        return "No quedan metas: la rama está cerrada."
    bloques = []
    for k, meta in enumerate(metas):
        lineas = []
        if len(metas) > 1:
            lineas.append(f"-- meta {k + 1}: case {meta.get('id', '')}")
        omitidas = 0
        for h in meta["hypotheses"]:
            if "✝" in h["name"]:
                continue
            if solo is not None and h["name"] not in solo:
                omitidas += 1
                continue
            if omitidas:
                lineas.append(f"-- (… {omitidas} hipótesis omitidas …)")
                omitidas = 0
            lineas.append(f"{h['name']} : {h['type']}")
        if omitidas:
            lineas.append(f"-- (… {omitidas} hipótesis omitidas …)")
        lineas.append(f"⊢ {meta['target']}")
        bloques.append("\n".join(lineas))
    return "\n\n".join(bloques)


def bloque_estado(metas: list[dict], titulo: str, solo: set[str] | None = None) -> str:
    cuerpo = resaltar(texto_metas(metas, solo), ANCHO - 2)
    return (
        f"\\begin{{estadolean}}{{{titulo}}}\n"
        "\\begin{Verbatim}[commandchars=\\\\\\{\\}]\n"
        f"{cuerpo}\n"
        "\\end{Verbatim}\n"
        "\\end{estadolean}"
    )


def procesar(plantilla: str) -> str:
    salida = []
    plantilla_lean: list[str] | None = None
    titulo_plantilla = ""
    for linea in plantilla.split("\n"):
        if plantilla_lean is not None:
            if linea.strip() == "%%ENDLEAN%%":
                salida.append(bloque_codigo("\n".join(plantilla_lean), titulo_plantilla))
                plantilla_lean = None
            else:
                plantilla_lean.append(linea)
            continue
        m = re.fullmatch(r"\s*%%LEAN:(.*?)(?:%%)?\s*", linea)
        if m:
            plantilla_lean = []
            titulo_plantilla = m.group(1).strip()
            continue
        m = re.fullmatch(r"\s*%%(CODE|EXCERPT|STATE|STEP):(.*)%%\s*", linea)
        if not m:
            salida.append(linea)
            continue
        tipo = m.group(1)
        args = [a.strip() for a in m.group(2).split("::")]
        if tipo == "CODE":
            ruta, nombre = args
            codigo, n = extraer_declaracion(ruta, nombre)
            salida.append(bloque_codigo(codigo, f"\\ruta{{{ruta}}}{{{n}}}"))
        elif tipo == "EXCERPT":
            ruta, inicio, final = args
            codigo, n = extraer_fragmento(ruta, inicio, final)
            salida.append(bloque_codigo(codigo, f"\\ruta{{{ruta}}}{{{n}}} (fragmento)"))
        elif tipo == "STATE":
            ruta, id_paso, cuando, *resto = args
            solo = leer_solo(resto)
            s = paso(ruta, id_paso)
            titulo = "Estado antes de" if cuando == "before" else "Estado después de"
            salida.append(
                bloque_estado(
                    s[cuando], f"{titulo} \\texttt{{{escapar_titulo(s['label'])}}}", solo
                )
            )
        elif tipo == "STEP":
            ruta, id_paso, *resto = args
            solo = leer_solo(resto)
            s = paso(ruta, id_paso)
            salida.append(bloque_estado(s["before"], "Estado antes", solo))
            salida.append(
                f"\\tacticaentre{{{escapar_titulo(s['sourceText'].splitlines()[0])}}}"
            )
            salida.append(bloque_estado(s["after"], "Estado después", solo))
    return "\n".join(salida)


def leer_solo(resto: list[str]) -> set[str] | None:
    """Opción `solo=h1,h2`: muestra únicamente esas hipótesis."""
    for opcion in resto:
        if opcion.startswith("solo="):
            return {n.strip() for n in opcion[5:].split(",") if n.strip()}
    return None


def escapar_titulo(texto: str) -> str:
    reemplazos = {
        "\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "_": r"\_",
        "#": r"\#", "%": r"\%", "&": r"\&", "$": r"\$", "^": r"\^{}",
        "~": r"\textasciitilde{}",
    }
    return "".join(reemplazos.get(c, c) for c in texto)


def main() -> None:
    SALIDA.write_text(procesar(PLANTILLA.read_text(encoding="utf-8")), encoding="utf-8")
    print(f"Escrito {SALIDA.relative_to(RAIZ)}")
    if "--no-pdf" in sys.argv:
        return
    for _ in range(2):
        r = subprocess.run(
            ["lualatex", "-interaction=nonstopmode", "-halt-on-error", SALIDA.name],
            cwd=AQUI, capture_output=True, text=True,
        )
        if r.returncode != 0:
            print(r.stdout[-4000:])
            raise SystemExit("lualatex falló")
    print(f"PDF: {(AQUI / 'CursoLean.pdf').relative_to(RAIZ)}")


if __name__ == "__main__":
    main()
