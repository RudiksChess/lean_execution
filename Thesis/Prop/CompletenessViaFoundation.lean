import Thesis.Prop.BridgeLemma

namespace Thesis.Prop

abbrev Teoria : Type := LO.Propositional.Theory String

abbrev Derivable (T : Teoria) (ψ : F) : Prop :=
  T ⊢ ψ

-- ANCHOR: provableTr
theorem traduccion_derivable_de_tautologia (φ : Formula) :
    EsTautologia φ → Derivable (∅ : Teoria) (traducir φ) := by
  -- A probar: derivabilidad en Foundation, no en el cálculo ND.
  -- Método: preservación semántica y completitud de Foundation.
  intro hTautologia
  -- La completitud de Foundation exige consecuencia semántica desde la teoría vacía.
  apply LO.Propositional.Boolean.completeness!
  intro v hvT
  -- hvT expresa satisfacción de la teoría vacía; hTautologia vale sin usarla.
  have hEvaluacion : evaluar v φ := hTautologia v
  have hPuente : evaluar v φ ↔ Satisface v (traducir φ) := evaluar_traduccion v φ
  have hSatisfaccion : Satisface v (traducir φ) := hPuente.mp hEvaluacion
  exact hSatisfaccion
-- ANCHOREND: provableTr

end Thesis.Prop
