import Thesis.Prop.BridgeLemma

namespace Thesis.Prop

abbrev Theory : Type := LO.Propositional.Theory String

abbrev Provable (T : Theory) (ψ : F) : Prop :=
  T ⊢ ψ

-- ANCHOR: provableTr
theorem provable_tr_of_tautology (φ : Formula) :
    IsTautology φ → Provable (∅ : Theory) (tr φ) := by
  intro hTaut
  -- Foundation completeness: semantic consequence ⇒ provability.
  -- This theorem is in Foundation/Propositional/ClassicalSemantics/Tait.lean.
  -- 
  apply LO.Propositional.ClassicalSemantics.completeness!
  intro v hvT
  have : eval v φ := hTaut v
  exact (eval_tr v φ).1 this
-- ANCHOREND: provableTr

end Thesis.Prop
