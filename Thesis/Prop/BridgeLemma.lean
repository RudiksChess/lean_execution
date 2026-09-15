import Thesis.Prop.BridgeToFoundation

namespace Thesis.Prop

-- ANCHOR: evalTr
theorem evaluar_traduccion (v : Valuacion) : ∀ φ : Formula, evaluar v φ ↔ Satisface v (traducir φ) := by
  -- A probar: equivalencia de ambas semánticas. Método: inducción sobre φ.
  intro φ
  induction φ with
  | atom s =>
      -- Ambas semánticas interpretan el átomo s como v s.
      simp only [evaluar, traducir, Satisface, LO.Propositional.NNFormula.models_atom]
  | neg p hipInd =>
      have hNeg : Satisface v (traducir (~p)) ↔ ¬ Satisface v (traducir p) := by
        simp only [traducir, Satisface, LO.Semantics.Not.models_not]
      change (¬ evaluar v p) ↔ Satisface v (traducir (~p))
      rw [hNeg]
      constructor
      · intro hNoEvaluacion hSatisfaccion
        exact hNoEvaluacion (hipInd.mpr hSatisfaccion)
      · intro hNoSatisfaccion hEvaluacion
        exact hNoSatisfaccion (hipInd.mp hEvaluacion)
  | impl p q hipIndP hipIndQ =>
      have hImp : Satisface v (traducir (p ⟶ q)) ↔ (¬ Satisface v (traducir p) ∨ Satisface v (traducir q)) := by
        simp only [traducir, Satisface, LO.Semantics.Or.models_or, LO.Semantics.Not.models_not]
      change (evaluar v p → evaluar v q) ↔ Satisface v (traducir (p ⟶ q))
      rw [hImp]
      constructor
      · intro hEvaluacionImp
        -- Tercero excluido metateórico para construir la disyunción.
        by_cases hP : evaluar v p
        · have hQ : evaluar v q := hEvaluacionImp hP
          exact Or.inr (hipIndQ.mp hQ)
        · have hNoSatisfaccion : ¬ Satisface v (traducir p) := by
            intro hSatisfaccion
            exact hP (hipIndP.mpr hSatisfaccion)
          exact Or.inl hNoSatisfaccion
      · intro hCasos hP
        rcases hCasos with hNoP | hQ
        · have hSatisfaccionP : Satisface v (traducir p) := hipIndP.mp hP
          exact False.elim (hNoP hSatisfaccionP)
        · exact hipIndQ.mpr hQ
-- ANCHOREND: evalTr

end Thesis.Prop
