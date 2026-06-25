# Completeness of Propositional Natural Deduction in Lean 4

[![CI](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml/badge.svg)](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml)

A machine-checked proof that classical propositional natural deduction (over
`{¬, →}`) is **complete**: every tautology is derivable from the empty context.
Completeness is proved *internally*, via Kalmár's lemma — no oracle, no
`sorry`. The accompanying thesis report renders its code listings directly from
this verified source.

> **Read it:** the latest compiled PDF is attached to each
> [release](https://github.com/RudiksChess/lean_execution/releases).
>
> **Mathematical overview** (no Lean needed): a side-by-side "maths ↔ code"
> tour of **both developments** is at
> <https://rudikschess.github.io/lean_execution/overview.html> — written for
> readers who want the mathematics, with the verified code shown alongside. A
> deeper, step-by-step companion covering **both developments** (prerequisites,
> a "how Lean works" primer, every case of the completeness proof, and the full
> quicksort correctness argument) is at
> <https://rudikschess.github.io/lean_execution/thesis.html>.
>
> **Browse the proofs:** generated API docs (hover for types, click to jump to
> definitions) are published at
> <https://rudikschess.github.io/lean_execution/> — see `Thesis/Prop/` for this
> development. Built by doc-gen4 on each release.

## Repository layout

This repo holds **two independent, machine-checked developments**, both built by
`lake build` and verified in CI:

| Path | |
|------|--|
| **`Thesis/Prop/`** | **Development 1 — propositional natural deduction:** syntax, semantics, the ND calculus, soundness, and Kalmár completeness |
| **`Thesis/Sort/`** | **Development 2 — quicksort:** the recursive definition and proofs that it is a sorted permutation of its input |
| `Thesis.lean` | library root; imports both developments |
| `Thesis/Prop/Audit.lean` | emits the axiom certificate (→ `reports/natural-deduction/audit.txt`) |
| `aristotle/` | AI cross-validation: ND proofs reconstructed cold by Harmonic Aristotle |
| `reports/natural-deduction/` | the ND thesis report (`ThesisReport_ND.tex`, Spanish edition, generated `audit.txt`); listings are pulled from `Thesis/Prop/` |
| `reports/quicksort/` | the quicksort report (`QuicksortReport.tex`) |
| `web/` | hosted explainer pages (overview + step-by-step) |
| `docbuild/` | doc-gen4 configuration for the API docs site |

## Reproduce it

**In the cloud, no install** — open the repo in a GitHub Codespace
(**Code ▸ Codespaces ▸ Create**). The devcontainer installs the toolchain and
primes the Mathlib cache automatically; then in the terminal run `lake build`
(or `make check`). Already compiled? CI does exactly this on every push — the
badge above is the proof.

**Locally** — requires [`elan`](https://github.com/leanprover/elan) (the
toolchain version is pinned in `lean-toolchain`).

```sh
lake exe cache get   # fetch the prebuilt Mathlib (skips a multi-hour build)
lake build           # kernel-checks every proof
make check           # build + regenerate the axiom audit + verify the Aristotle proofs
```

`make check` is exactly what CI runs. It fails if any proof breaks, if a
`sorry` sneaks in (it would surface as `sorryAx`), or if `audit.txt` drifts.

## The axiom certificate

The main results depend only on Lean/Mathlib's three standard classical axioms —
no admitted gaps, no postulated rules:

```
'completeness_ND' depends on axioms: [propext, Classical.choice, Quot.sound]
'soundComplete'   depends on axioms: [propext, Classical.choice, Quot.sound]
'ex_id'           does not depend on any axioms
```

Regenerate with `make audit`.

## Build the PDFs

```sh
make pdf            # natural-deduction report (regenerates audit.txt first)
make pdf-quicksort  # quicksort report
```

Each report lives under `reports/<topic>/` and compiles in place.
