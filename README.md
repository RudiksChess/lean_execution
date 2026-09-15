# Deducción natural y Quicksort verificados en Lean 4

[![CI](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml/badge.svg)](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml)

Dos desarrollos comprobados por el núcleo de Lean:

- **Completitud:** toda tautología del lenguaje proposicional {¬, →} es derivable desde el contexto vacío. La prueba usa el lema de Kalmár y la descarga de literales, sin postular un oráculo.
- **Quicksort:** la salida es una permutación ordenada de la entrada, con disminución explícita de las llamadas recursivas.

## Código en español

Los nombres propios de definiciones, resultados y variables descriptivas, así como los comentarios de `Thesis/`, están en español. Por ejemplo:

| Concepto | Nombre en Lean |
|---|---|
| Valuación e interpretación | `Valuacion`, `evaluar` |
| Contexto de literales | `contextoLiterales` |
| Debilitamiento | `debilitamiento` |
| Análisis por casos | `analisis_por_casos` |
| Corrección y completitud | `correccion`, `completitud_ND`, `correccion_completitud` |
| Permutación y ordenamiento | `quicksort_permutacion`, `quicksort_ordenada` |
| Hipótesis inductiva | `hipInd`, con sufijos para distinguir sus instancias |
| Particiones del pivote | `menoresIguales`, `mayores` |

Se conservan las palabras reservadas y tácticas de Lean (`theorem`, `intro`, `exact`, `rw`), las APIs externas (`List.filter`, `List.Perm`, `LinearOrder`, Foundation), los símbolos matemáticos y las abreviaturas de reglas (`ND.impI`, `ND.negE`). `quicksort` conserva el nombre del algoritmo. Los módulos y rutas existentes no se renombran, para mantener las importaciones y los enlaces.

La correspondencia de nombres anteriores y actuales está en [tools/nombres_es.json](tools/nombres_es.json). La comprobación de migración contrasta con la revisión anterior y exige que el código, salvo identificadores autorizados y comentarios, sea el mismo:

```sh
python3 tools/spanish_migration.py
```

Los archivos de `aristotle/` son reconstrucciones históricas independientes y se conservan **sin traducir** como evidencia original. Tampoco se traducen dependencias, comandos de herramientas, claves del formato de exportación ni salidas literales de Lean. La infraestructura de desarrollo no forma parte de la notación matemática.

## Organización

| Ruta | Contenido |
|---|---|
| `Thesis/Prop/` | Sintaxis, semántica, reglas de ND, corrección y completitud |
| `Thesis/Sort/` | Quicksort, pruebas auxiliares, permutación y ordenamiento |
| `Thesis.lean` | Módulo raíz de los dos desarrollos |
| `Thesis/Prop/CompletenessViaFoundation.lean` | Validación independiente con Foundation |
| `Thesis/VerificationOutput.lean` | Tipos, ejemplos ejecutados y transcripción de axiomas |
| `Thesis/Prop/Audit.lean`, `Thesis/Sort/Audit.lean` | Auditorías de axiomas |
| `artifacts/explorer/proofs.json` | Código y estados reales para el explorador |
| `aristotle/` | Reconstrucciones históricas independientes |
| `reports/` | Informes de deducción natural, Quicksort y Aristotle |
| `web/` | Guías complementarias y evidencia pública de verificación |
| `docbuild/` | Configuración de doc-gen4 para la documentación de API |

## Reproducir la verificación

Se requiere [elan](https://github.com/leanprover/elan). La versión de Lean está fijada en `lean-toolchain` y las dependencias en `lake-manifest.json`.

```sh
lake exe cache get
lake build
make check
make proof-explorer
```

`make check` compila ambos desarrollos, comprueba la validación con Foundation y las tres reconstrucciones de Aristotle, regenera los certificados y compara la transcripción pública. Un cambio de nombres obliga a regenerar los estados: no se traducen estados a mano.

Foundation se compila como un objetivo separado porque Foundation y la clausura completa de Mathlib definen `Matrix.map`; no se combinan en el mismo módulo raíz.

GitHub Codespaces permite explorar el desarrollo sin instalar Lean localmente: **Code ▸ Codespaces ▸ Create codespace**. La primera preparación descarga la caché de Mathlib y puede consumir varios gigabytes. Una precompilación de Codespaces permite adelantar ese trabajo.

## Axiomas y alcance

`python3 tools/check_axioms.py` rechaza dependencias ajenas a `propext`, `Classical.choice` y `Quot.sound`, incluidas pruebas admitidas mediante `sorryAx`. También rechaza resultados ausentes, duplicados o salidas inesperadas.

La completitud usa los tres axiomas permitidos. Las pruebas de Quicksort usan `propext` y `Quot.sound`, sin `Classical.choice`. Los certificados literales se conservan en `reports/natural-deduction/audit.txt` y `reports/quicksort/audit.txt`.

```sh
make audit audit-quicksort verification-output
```

Lean comprueba los términos de prueba. La correspondencia pedagógica y la bibliografía requieren una revisión separada; una compilación correcta no certifica la redacción.

## Estados del explorador

El ejecutable separado `proofExplorerExport` lee los registros `TacticInfo` del elaborador y utiliza SubVerso, fijado a una revisión compatible con Lean 4.29.0. Exporta las hipótesis y metas reales antes y después de cada táctica.

Los 27 resultados cubren deducción natural, completitud, el puente con Foundation y Quicksort, incluidas las obligaciones de terminación de su definición. Los identificadores de navegación se mantienen separados de los nombres visibles en Lean.

`make proof-explorer-check` vuelve a elaborar los módulos originales y exige coincidencia exacta con el artefacto versionado. Rechaza cambios de fuentes o dependencias, errores de elaboración y ausencia de estados. Los cierres locales de una rama no se presentan como cierre de toda la prueba.

## Informes y documentación

```sh
make pdf
make pdf-quicksort
make pdf-aristotle
make docs
```

Los informes compilan en `reports/<tema>/`; sus listados se toman de los módulos de Lean. `make docs` genera la API con doc-gen4 y puede requerir una compilación extensa.

- [Explorador en español](https://tesis.rudiks.com/explorador)
- [Documentación de API](https://rudikschess.github.io/lean_execution/)
- [Guía de verificación](https://rudikschess.github.io/lean_execution/verification.html)
- [Transcripción literal de Lean](https://rudikschess.github.io/lean_execution/lean-output.txt)
- [Recorrido complementario matemática y código](https://rudikschess.github.io/lean_execution/overview.html)
- [Guía paso a paso](https://rudikschess.github.io/lean_execution/thesis.html)
- [Informes publicados](https://github.com/RudiksChess/lean_execution/releases)
