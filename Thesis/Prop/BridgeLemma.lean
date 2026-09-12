import Thesis.Prop.BridgeToFoundation

namespace Thesis.Prop

-- ANCHOR: evalTr
theorem eval_tr (v : Valuation) : ∀ φ : Formula, eval v φ ↔ Sat v (tr φ) := by
  -- A probar: equivalencia de ambas semánticas. Método: inducción sobre φ.
  intro φ
  induction φ with
  | atom s =>
      -- Ambas semánticas interpretan el átomo s como v s.
      simp only [eval, tr, Sat, LO.Propositional.NNFormula.models_atom]
  | neg p ih =>
      have hNeg : Sat v (tr (~p)) ↔ ¬ Sat v (tr p) := by
        simp only [tr, Sat, LO.Semantics.Not.models_not]
      change (¬ eval v p) ↔ Sat v (tr (~p))
      rw [hNeg]
      constructor
      · intro hNotEval hSat
        exact hNotEval (ih.mpr hSat)
      · intro hNotSat hEval
        exact hNotSat (ih.mp hEval)
  | impl p q ihp ihq =>
      have hImp : Sat v (tr (p ⟶ q)) ↔ (¬ Sat v (tr p) ∨ Sat v (tr q)) := by
        simp only [tr, Sat, LO.Semantics.Or.models_or, LO.Semantics.Not.models_not]
      change (eval v p → eval v q) ↔ Sat v (tr (p ⟶ q))
      rw [hImp]
      constructor
      · intro hEvalImp
        -- Tercero excluido metateórico para construir la disyunción.
        by_cases hP : eval v p
        · have hQ : eval v q := hEvalImp hP
          exact Or.inr (ihq.mp hQ)
        · have hNotSat : ¬ Sat v (tr p) := by
            intro hSat
            exact hP (ihp.mpr hSat)
          exact Or.inl hNotSat
      · intro hCases hP
        rcases hCases with hNotP | hQ
        · have hSatP : Sat v (tr p) := ihp.mp hP
          exact False.elim (hNotP hSatP)
        · exact ihq.mpr hQ
-- ANCHOREND: evalTr

end Thesis.Prop
