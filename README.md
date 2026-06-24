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
> **Browse the proofs:** generated API docs (hover for types, click to jump to
> definitions) are published at
> <https://rudikschess.github.io/lean_execution/> — see `Thesis/Prop/` for this
> development. Built by doc-gen4 on each release.

## What's here

| Path | |
|------|--|
| `Thesis/Prop/` | the development: syntax, the ND calculus, soundness, Kalmár completeness |
| `Thesis/Prop/Audit.lean` → `audit.txt` | the generated axiom certificate |
| `aristotle/` | AI cross-validation: proofs reconstructed cold by Harmonic Aristotle |
| `ThesisReport_ND.tex` | the thesis report (listings pulled from the source above) |

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

## Build the PDF

```sh
make pdf   # regenerates audit.txt, then runs latexmk on ThesisReport_ND.tex
```
