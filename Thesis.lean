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

-- Appendix (cross-validation against the Foundation library) builds as a
-- separate target `Thesis.Prop.CompletenessViaFoundation`; it is intentionally
-- not imported here because the full Mathlib + Foundation closures clash on a
-- duplicate `Matrix.map` declaration.
