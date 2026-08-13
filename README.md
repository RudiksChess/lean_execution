# Completeness of Propositional Natural Deduction in Lean 4

[![CI](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml/badge.svg)](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml)

A machine-checked proof that classical propositional natural deduction (over
`{¬, →}`) is **complete**: every tautology is derivable from the empty context.
Completeness is proved *internally*, via Kalmár's lemma — no oracle, no
`sorry`. The accompanying thesis report renders its code listings directly from
this verified source.

> **Read it:** both compiled reports — natural-deduction completeness and
> quicksort — plus an *AI-Reconstructed Proofs* reference (the full Aristotle
> outputs) are attached to each
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
>
> **Verify the result:** the public
> [verification page](https://rudikschess.github.io/lean_execution/verification.html)
> explains the CI checks, axiom certificates, trust boundary, and exact local
> reproduction commands.

## Repository layout

This repo holds **two independent, machine-checked developments**, both built by
`lake build` and verified in CI:

| Path | |
|------|--|
| **`Thesis/Prop/`** | **Development 1 — propositional natural deduction:** syntax, semantics, the ND calculus, soundness, and Kalmár completeness |
| **`Thesis/Sort/`** | **Development 2 — quicksort:** the recursive definition and proofs that it is a sorted permutation of its input |
| `Thesis.lean` | library root; imports both developments |
| `Thesis/Prop/Audit.lean` | emits the axiom certificate (→ `reports/natural-deduction/audit.txt`) |
| `aristotle/` | AI cross-validation: proofs reconstructed cold by Harmonic Aristotle (both developments) |
| `reports/aristotle/` | the *AI-Reconstructed Proofs* reference report (`make pdf-aristotle`) |
| `reports/natural-deduction/` | the ND thesis report (`ThesisReport_ND.tex`, Spanish edition, generated `audit.txt`); listings are pulled from `Thesis/Prop/` |
| `reports/quicksort/` | the quicksort report (`QuicksortReport.tex`) |
| `web/` | hosted overview, step-by-step walkthrough, and verification guide |
| `docbuild/` | doc-gen4 configuration for the API docs site |

## Reproduce it

**Public evidence** — the [CI workflow](https://github.com/RudiksChess/lean_execution/actions/workflows/ci.yml)
runs on every push and pull request. A green badge means GitHub built the Lean
sources, regenerated and compared both axiom certificates, and compiled the
Foundation bridge plus the three standalone Aristotle reconstructions. See the
[verification guide](https://rudikschess.github.io/lean_execution/verification.html)
for what each check establishes and the limits of the claim.

**Independent local reproduction** — requires
[`elan`](https://github.com/leanprover/elan). The Lean toolchain is pinned in
`lean-toolchain`, and package revisions are locked in `lake-manifest.json`.

```sh
lake exe cache get   # fetch the prebuilt Mathlib (skips a multi-hour build)
lake build           # kernel-checks every proof
make check           # build + audits + Foundation and Aristotle cross-checks
```

`make check` mirrors the substantive CI checks. It fails if a proof no longer
type-checks or either committed audit changes. An admitted gap or a newly
postulated axiom used by an audited result would appear in its transitive axiom
list (for example as `sorryAx`) and make that comparison fail.

**Optional interactive exploration** — GitHub Codespaces can provide the same
toolchain without a local Lean installation. It is not the fastest way to see
whether the proofs pass: the first launch must provision and unpack the pinned
Mathlib dependency cache, which can consume several gigabytes and take a while.
Use **Code ▸ Codespaces ▸ Create codespace** if you want to edit and inspect the
proofs interactively; repository maintainers can enable a Codespaces prebuild
to move most of that first-use setup out of a visitor's session.

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
