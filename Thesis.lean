-- Two developments, built and verified together:
--   Thesis.Prop.*  — completeness of propositional natural deduction (oracle-free)
--   Thesis.Sort.*  — correctness of quicksort
import Thesis.Prop.Syntax
import Thesis.Prop.NaturalDeduction
import Thesis.Prop.Completeness
import Thesis.Prop.Main
import Thesis.Sort.Quicksort
import Thesis.Sort.Examples

/-!
# Verified developments — Rudik Rompich (UVG)

This Lean library bundles two independent, machine-checked developments:

* **`Thesis.Prop`** — an oracle-free, internal proof that classical propositional
  natural deduction (over `{¬, →}`) is **complete**: every tautology is derivable
  from the empty context, via Kalmár's lemma.
* **`Thesis.Sort`** — a proof that **quicksort** is correct: its output is a sorted
  permutation of its input.

Both are `sorry`-free and depend only on Lean/Mathlib's standard classical axioms.

**Author:** Rudik Rompich, Universidad del Valle de Guatemala
(`rom19857@uvg.edu.gt`). Undergraduate thesis.

Repository and compiled reports (PDF): <https://github.com/RudiksChess/lean_execution>.
-/

-- The Foundation cross-validation builds as the separate target
-- `Thesis.Prop.CompletenessViaFoundation`. It cannot share one root module
-- with the full Mathlib closure because both dependencies define Matrix.map.
