-- Main result: internal completeness of natural deduction (oracle-free).
import Thesis.Prop.Syntax
import Thesis.Prop.NaturalDeduction
import Thesis.Prop.Completeness
import Thesis.Prop.Main

/-!
# Completeness of Propositional Natural Deduction in Lean 4

An oracle-free, internal proof that classical propositional natural deduction
(over `{¬, →}`) is **complete** — every tautology is derivable from the empty
context — established via Kalmár's lemma.

**Author:** Rudik Rompich, Universidad del Valle de Guatemala
(`rom19857@uvg.edu.gt`). Undergraduate thesis.

Repository and compiled report (PDF): <https://github.com/RudiksChess/lean_execution>.
-/

-- Appendix (cross-validation against the Foundation library) builds as a
-- separate target `Thesis.Prop.CompletenessViaFoundation`; it is intentionally
-- not imported here because the full Mathlib + Foundation closures clash on a
-- duplicate `Matrix.map` declaration.
