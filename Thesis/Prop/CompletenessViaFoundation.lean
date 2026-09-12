import Thesis.Prop.BridgeLemma

namespace Thesis.Prop

abbrev Theory : Type := LO.Propositional.Theory String

abbrev Provable (T : Theory) (ψ : F) : Prop :=
  T ⊢ ψ

-- ANCHOR: provableTr
theorem provable_tr_of_tautology (φ : Formula) :
    IsTautology φ → Provable (∅ : Theory) (tr φ) := by
  -- A probar: derivabilidad en Foundation, no en el cálculo ND.
  -- Método: preservación semántica y completitud de Foundation.
  intro hTaut
  -- La completitud de Foundation exige consecuencia semántica desde la teoría vacía.
  apply LO.Propositional.Boolean.completeness!
  intro v hvT
  -- hvT expresa satisfacción de la teoría vacía; hTaut vale sin usarla.
  have hEval : eval v φ := hTaut v
  have hBridge : eval v φ ↔ Sat v (tr φ) := eval_tr v φ
  have hSat : Sat v (tr φ) := hBridge.mp hEval
  exact hSat
-- ANCHOREND: provableTr

end Thesis.Prop
