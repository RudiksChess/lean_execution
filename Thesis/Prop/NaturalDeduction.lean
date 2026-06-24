import Thesis.Prop.Syntax
import Mathlib.Data.Set.Insert
import Mathlib.Tactic

namespace Thesis.Prop

open Set

-- ANCHOR: bot
/--
We encode ⊥ *inside* the {¬, →}-only surface language as ¬(P → P).
This is semantically always false (for any valuation), so it behaves as falsity.
-/
def Bot : Formula := ~(.atom "⊥" ⟶ .atom "⊥")

theorem eval_Bot (v : Valuation) : eval v Bot ↔ False := by
  constructor
  · intro h
    have hp : eval v (.atom "⊥" ⟶ .atom "⊥") := by intro hP; exact hP
    exact h hp
  · intro h; exact False.elim h
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
  induction d with
  | hyp hmem => intro Δ hsub; exact ND.hyp (hsub hmem)
  | impI _ ih => intro Δ hsub; exact ND.impI (ih (insert_subset_insert hsub))
  | impE _ _ ih1 ih2 => intro Δ hsub; exact ND.impE (ih1 hsub) (ih2 hsub)
  | negI _ ih => intro Δ hsub; exact ND.negI (ih (insert_subset_insert hsub))
  | negE _ _ ih1 ih2 => intro Δ hsub; exact ND.negE (ih1 hsub) (ih2 hsub)
  | botE _ ih => intro Δ hsub; exact ND.botE (ih hsub)
  | classical _ ih => intro Δ hsub; exact ND.classical (ih (insert_subset_insert hsub))
-- ANCHOREND: weakening

/-! ### Derived rules -/

-- ANCHOR: dni
/-- Double negation introduction: `Γ ⊢ φ` ⟹ `Γ ⊢ ¬¬φ`. -/
theorem dni {Γ φ} (d : ND Γ φ) : ND Γ (~~φ) := by
  apply ND.negI
  exact ND.negE (ND.hyp (Set.mem_insert _ _)) (weakening d (Set.subset_insert _ _))
-- ANCHOREND: dni

-- ANCHOR: byCases
/-- Classical proof by cases on an arbitrary formula `φ` (no disjunction needed):
    if `χ` follows both from `φ` and from `¬φ`, then `χ` holds outright. -/
theorem byCases {Γ φ χ} (d1 : ND (insert φ Γ) χ) (d2 : ND (insert (~φ) Γ) χ) :
    ND Γ χ := by
  apply ND.classical
  have e1 : ND (insert (~χ) Γ) (~φ) := by
    apply ND.negI
    refine ND.negE (ND.hyp ?_) (weakening d1 ?_)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.insert_subset_insert (Set.subset_insert _ _)
  have e2 : ND (insert (~χ) Γ) (~~φ) := by
    apply ND.negI
    refine ND.negE (ND.hyp ?_) (weakening d2 ?_)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.insert_subset_insert (Set.subset_insert _ _)
  exact ND.negE e2 e1
-- ANCHOREND: byCases

/-! ### Soundness and consistency -/

-- ANCHOR: soundness
/-- Every assumption in `insert χ Γ` is satisfied if `χ` is and every assumption in `Γ` is. -/
theorem sat_insert {v : Valuation} {Γ : Set Formula} {χ : Formula}
    (hχ : eval v χ) (hΓ : ∀ ψ ∈ Γ, eval v ψ) :
    ∀ ψ ∈ insert χ Γ, eval v ψ := by
  intro ψ hψ
  rcases Set.mem_insert_iff.1 hψ with h | h
  · subst h; exact hχ
  · exact hΓ ψ h

/-- **Soundness.** Every ND derivation is semantically valid. -/
theorem soundness {Γ φ} (d : ND Γ φ) :
    ∀ v, (∀ ψ ∈ Γ, eval v ψ) → eval v φ := by
  induction d with
  | hyp hmem => intro v hv; exact hv _ hmem
  | impI _ ih => intro v hv hp; exact ih v (sat_insert hp hv)
  | impE _ _ ih1 ih2 => intro v hv; exact (ih1 v hv) (ih2 v hv)
  | negI _ ih => intro v hv hp; exact (eval_Bot v).1 (ih v (sat_insert hp hv))
  | negE _ _ ih1 ih2 => intro v hv; exact (eval_Bot v).2 ((ih1 v hv) (ih2 v hv))
  | botE _ ih => intro v hv; exact ((eval_Bot v).1 (ih v hv)).elim
  | classical _ ih =>
      intro v hv
      by_contra hnp
      exact (eval_Bot v).1 (ih v (sat_insert hnp hv))

/-- Soundness specialized to the empty context: theorems are tautologies. -/
theorem isTautology_of_provable {φ} (d : ND (∅ : Set Formula) φ) : IsTautology φ := by
  intro v; refine soundness d v ?_; intro ψ hψ; simp at hψ

/-- **Consistency.** `⊥` is not derivable from no assumptions. -/
theorem not_provable_Bot : ¬ ND (∅ : Set Formula) Bot := by
  intro d
  exact (eval_Bot (fun _ => True)).1 (isTautology_of_provable d (fun _ => True))
-- ANCHOREND: soundness

end Thesis.Prop
