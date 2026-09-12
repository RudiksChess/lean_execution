import Thesis.Prop.Syntax
import Mathlib.Data.Set.Insert
import Mathlib.Tactic

namespace Thesis.Prop

open Set

-- ANCHOR: bot
/--
Falsity ⊥ is encoded *inside* the {¬, →}-only surface language as ¬(P → P).
This is semantically always false (for any valuation), so it behaves as falsity.
-/
def Bot : Formula := ~(.atom "⊥" ⟶ .atom "⊥")

theorem eval_Bot (v : Valuation) : eval v Bot ↔ False := by
  -- A probar: las dos implicaciones de eval v Bot ↔ False.
  -- Método: desplegar la semántica y aplicar la identidad P → P.
  constructor
  · intro h
    have hNotIdentity : ¬ (v "⊥" → v "⊥") := h
    have hIdentity : v "⊥" → v "⊥" := by
      intro hAtom
      exact hAtom
    exact hNotIdentity hIdentity
  · intro hFalse
    exact False.elim hFalse
-- ANCHOREND: bot

-- ANCHOR: ndType
/--
Natural Deduction with contexts (Γ : Set Formula) and discharge.

This is a *genuine* classical natural deduction system: there is no oracle.
Completeness is proved internally (see `Completeness.lean`) via Kalmár's lemma.
-/
inductive ND : Set Formula → Formula → Prop
| hyp {Γ φ} : φ ∈ Γ → ND Γ φ
| impI {Γ φ ψ} : ND (insert φ Γ) ψ → ND Γ (φ ⟶ ψ)
| impE {Γ φ ψ} : ND Γ (φ ⟶ ψ) → ND Γ φ → ND Γ ψ
| negI {Γ φ} : ND (insert φ Γ) Bot → ND Γ (~φ)
| negE {Γ φ} : ND Γ (~φ) → ND Γ φ → ND Γ Bot
| botE {Γ φ} : ND Γ Bot → ND Γ φ
/-- Classical reductio: from Γ,¬φ ⊢ ⊥ infer Γ ⊢ φ. -/
| classical {Γ φ} : ND (insert (~φ) Γ) Bot → ND Γ φ
-- ANCHOREND: ndType

/-! ### Structural lemma: weakening (monotonicity in the context) -/

-- ANCHOR: weakening
theorem weakening {Γ φ} (d : ND Γ φ) : ∀ {Δ}, Γ ⊆ Δ → ND Δ φ := by
  -- A probar: la misma conclusión bajo cualquier contexto mayor Δ.
  -- Método: inducción sobre d; Δ permanece cuantificado en cada hipótesis inductiva.
  induction d with
  | @hyp Γ φ hmem =>
      intro Δ hsub
      have hInDelta : φ ∈ Δ := hsub hmem
      exact ND.hyp hInDelta
  | @impI Γ φ ψ _ ih =>
      intro Δ hsub
      have hExtended : insert φ Γ ⊆ insert φ Δ := insert_subset_insert hsub
      have dBody : ND (insert φ Δ) ψ := ih hExtended
      -- impI descarga φ; las fórmulas de Δ permanecen.
      exact ND.impI dBody
  | @impE Γ φ ψ _ _ ihImp ihArg =>
      intro Δ hsub
      have dImp : ND Δ (φ ⟶ ψ) := ihImp hsub
      have dArg : ND Δ φ := ihArg hsub
      exact ND.impE dImp dArg
  | @negI Γ φ _ ih =>
      intro Δ hsub
      have hExtended : insert φ Γ ⊆ insert φ Δ := insert_subset_insert hsub
      have dFalse : ND (insert φ Δ) Bot := ih hExtended
      exact ND.negI dFalse
  | @negE Γ φ _ _ ihNeg ihPos =>
      intro Δ hsub
      have dNeg : ND Δ (~φ) := ihNeg hsub
      have dPos : ND Δ φ := ihPos hsub
      exact ND.negE dNeg dPos
  | @botE Γ φ _ ih =>
      intro Δ hsub
      have dFalse : ND Δ Bot := ih hsub
      exact ND.botE dFalse
  | @classical Γ φ _ ih =>
      intro Δ hsub
      have hExtended : insert (~φ) Γ ⊆ insert (~φ) Δ := insert_subset_insert hsub
      have dFalse : ND (insert (~φ) Δ) Bot := ih hExtended
      -- Por RAA objeto, se descarga ~φ y se concluye φ bajo Δ.
      exact ND.classical dFalse
-- ANCHOREND: weakening

/-! ### Derived rules -/

-- ANCHOR: dni
/-- Double negation introduction: `Γ ⊢ φ` ⟹ `Γ ⊢ ¬¬φ`. -/
theorem dni {Γ φ} (d : ND Γ φ) : ND Γ (~~φ) := by
  -- A probar: ND Γ (~~φ). Método: introducción de negación, no RAA.
  let Δ := insert (~φ) Γ
  have hNeg : (~φ) ∈ Δ := Set.mem_insert _ _
  have hSubset : Γ ⊆ Δ := Set.subset_insert _ _
  have dNeg : ND Δ (~φ) := ND.hyp hNeg
  have dPos : ND Δ φ := weakening d hSubset
  have dFalse : ND Δ Bot := ND.negE dNeg dPos
  -- negI descarga el supuesto ~φ, no la premisa d.
  exact ND.negI dFalse
-- ANCHOREND: dni

-- ANCHOR: byCases
/-- Classical proof by cases on an arbitrary formula `φ` (no disjunction needed):
    if `χ` follows both from `φ` and from `¬φ`, then `χ` holds outright. -/
theorem byCases {Γ φ χ} (d1 : ND (insert φ Γ) χ) (d2 : ND (insert (~φ) Γ) χ) :
    ND Γ χ := by
  -- A probar: ND Γ χ. Método: Por RAA objeto, basta Bot bajo Γ, ~χ.
  let Δ := insert (~χ) Γ
  have dNeg : ND Δ (~φ) := by
    let Θ := insert φ Δ
    have hNotChi : (~χ) ∈ Θ :=
      Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hSubset : insert φ Γ ⊆ Θ :=
      Set.insert_subset_insert (Set.subset_insert _ _)
    have dNotChi : ND Θ (~χ) := ND.hyp hNotChi
    have dChi : ND Θ χ := weakening d1 hSubset
    have dFalse : ND Θ Bot := ND.negE dNotChi dChi
    -- Se descarga φ; ~χ permanece en Δ.
    exact ND.negI dFalse
  have dDoubleNeg : ND Δ (~~φ) := by
    let Θ := insert (~φ) Δ
    have hNotChi : (~χ) ∈ Θ :=
      Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hSubset : insert (~φ) Γ ⊆ Θ :=
      Set.insert_subset_insert (Set.subset_insert _ _)
    have dNotChi : ND Θ (~χ) := ND.hyp hNotChi
    have dChi : ND Θ χ := weakening d2 hSubset
    have dFalse : ND Θ Bot := ND.negE dNotChi dChi
    -- Se descarga ~φ; ~χ permanece en Δ.
    exact ND.negI dFalse
  have dFalse : ND Δ Bot := ND.negE dDoubleNeg dNeg
  -- Por RAA, se descarga únicamente el supuesto adicional ~χ.
  exact ND.classical dFalse
-- ANCHOREND: byCases

/-! ### Soundness and consistency -/

-- ANCHOR: soundness
/-- Every assumption in `insert χ Γ` is satisfied if `χ` is and every assumption in `Γ` is. -/
theorem sat_insert {v : Valuation} {Γ : Set Formula} {χ : Formula}
    (hχ : eval v χ) (hΓ : ∀ ψ ∈ Γ, eval v ψ) :
    ∀ ψ ∈ insert χ Γ, eval v ψ := by
  -- A probar: cada fórmula del contexto extendido es verdadera bajo v.
  -- Método: casos de pertenencia; ψ = χ o ψ ∈ Γ.
  intro ψ hψ
  have hCases : ψ = χ ∨ ψ ∈ Γ := Set.mem_insert_iff.mp hψ
  rcases hCases with hEq | hInGamma
  · subst ψ
    exact hχ
  · exact hΓ ψ hInGamma

/-- **Soundness.** Every ND derivation is semantically valid. -/
theorem soundness {Γ φ} (d : ND Γ φ) :
    ∀ v, (∀ ψ ∈ Γ, eval v ψ) → eval v φ := by
  -- A probar: verdad semántica de la conclusión bajo toda valuación del contexto.
  -- Método: inducción sobre d, con v y la satisfacción aún cuantificados.
  induction d with
  | @hyp Γ φ hmem =>
      intro v hv
      exact hv φ hmem
  | @impI Γ φ ψ _ ih =>
      intro v hv
      change eval v φ → eval v ψ
      intro hPhi
      have hExtended : ∀ θ ∈ insert φ Γ, eval v θ := sat_insert hPhi hv
      have hPsi : eval v ψ := ih v hExtended
      exact hPsi
  | @impE Γ φ ψ _ _ ihImp ihArg =>
      intro v hv
      have hImp : eval v φ → eval v ψ := ihImp v hv
      have hPhi : eval v φ := ihArg v hv
      exact hImp hPhi
  | @negI Γ φ _ ih =>
      intro v hv
      change ¬ eval v φ
      intro hPhi
      have hExtended : ∀ θ ∈ insert φ Γ, eval v θ := sat_insert hPhi hv
      have hBot : eval v Bot := ih v hExtended
      exact (eval_Bot v).mp hBot
  | @negE Γ φ _ _ ihNeg ihPos =>
      intro v hv
      have hNeg : ¬ eval v φ := ihNeg v hv
      have hPos : eval v φ := ihPos v hv
      have hFalse : False := hNeg hPos
      -- Dirección inversa: False → eval v Bot.
      exact (eval_Bot v).mpr hFalse
  | @botE Γ φ _ ih =>
      intro v hv
      have hBot : eval v Bot := ih v hv
      have hFalse : False := (eval_Bot v).mp hBot
      exact False.elim hFalse
  | @classical Γ φ _ ih =>
      intro v hv
      -- Por RAA metateórica, se supone ¬ eval v φ, no ND Γ (~φ).
      by_contra hnp
      have hNeg : eval v (~φ) := hnp
      have hExtended : ∀ θ ∈ insert (~φ) Γ, eval v θ := sat_insert hNeg hv
      have hBot : eval v Bot := ih v hExtended
      exact (eval_Bot v).mp hBot

/-- Soundness specialized to the empty context: theorems are tautologies. -/
theorem isTautology_of_provable {φ} (d : ND (∅ : Set Formula) φ) : IsTautology φ := by
  -- A probar: ∀ v, eval v φ. Método: corrección con contexto vacío.
  intro v
  have hEmpty : ∀ ψ ∈ (∅ : Set Formula), eval v ψ := by
    intro ψ hψ
    have hFalse : False := hψ
    exact False.elim hFalse
  exact soundness d v hEmpty

/-- **Consistency.** `⊥` is not derivable from no assumptions. -/
theorem not_provable_Bot : ¬ ND (∅ : Set Formula) Bot := by
  -- A probar: la inexistencia de una derivación cerrada de Bot.
  -- Método: introducción de negación; una tautología no puede ser siempre falsa.
  intro d
  let v : Valuation := fun _ => True
  have hTaut : IsTautology Bot := isTautology_of_provable d
  have hBot : eval v Bot := hTaut v
  exact (eval_Bot v).mp hBot
-- ANCHOREND: soundness

end Thesis.Prop
