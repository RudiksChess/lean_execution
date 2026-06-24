import Mathlib.Data.Set.Insert
import Mathlib.Tactic

namespace Thesis.Prop

open Set

inductive Formula : Type
| atom : String → Formula
| neg  : Formula → Formula
| impl : Formula → Formula → Formula
deriving DecidableEq, Repr

prefix:60 "~" => Formula.neg
infixr:55 " ⟶ " => Formula.impl

def Bot : Formula := ~(.atom "⊥" ⟶ .atom "⊥")

inductive ND : Set Formula → Formula → Prop
| hyp {Γ φ} : φ ∈ Γ → ND Γ φ
| impI {Γ φ ψ} : ND (insert φ Γ) ψ → ND Γ (φ ⟶ ψ)
| impE {Γ φ ψ} : ND Γ (φ ⟶ ψ) → ND Γ φ → ND Γ ψ
| negI {Γ φ} : ND (insert φ Γ) Bot → ND Γ (~φ)
| negE {Γ φ} : ND Γ (~φ) → ND Γ φ → ND Γ Bot
| botE {Γ φ} : ND Γ Bot → ND Γ φ
| classical {Γ φ} : ND (insert (~φ) Γ) Bot → ND Γ φ

theorem weakening {Γ φ} (d : ND Γ φ) : ∀ {Δ}, Γ ⊆ Δ → ND Δ φ := by
  induction d with
  | hyp hmem => intro Δ hsub; exact ND.hyp (hsub hmem)
  | impI _ ih => intro Δ hsub; exact ND.impI (ih (insert_subset_insert hsub))
  | impE _ _ ih1 ih2 => intro Δ hsub; exact ND.impE (ih1 hsub) (ih2 hsub)
  | negI _ ih => intro Δ hsub; exact ND.negI (ih (insert_subset_insert hsub))
  | negE _ _ ih1 ih2 => intro Δ hsub; exact ND.negE (ih1 hsub) (ih2 hsub)
  | botE _ ih => intro Δ hsub; exact ND.botE (ih hsub)
  | classical _ ih => intro Δ hsub; exact ND.classical (ih (insert_subset_insert hsub))

/-- Classical proof by cases on an arbitrary formula `φ` (no disjunction needed):
    if `χ` follows both from `φ` and from `¬φ`, then `χ` holds outright.
    TASK: replace the `sorry` with a complete proof. -/
theorem byCases {Γ φ χ} (d1 : ND (insert φ Γ) χ) (d2 : ND (insert (~φ) Γ) χ) :
    ND Γ χ := by
  apply ND.classical
  have hnegφ : ND (insert (~χ) Γ) (~φ) := by
    apply ND.negI
    have hχ : ND (insert φ (insert (~χ) Γ)) χ :=
      weakening d1 (insert_subset_insert (subset_insert _ _))
    have hnχ : ND (insert φ (insert (~χ) Γ)) (~χ) :=
      ND.hyp (mem_insert_of_mem _ (mem_insert _ _))
    exact ND.negE hnχ hχ
  have hnnφ : ND (insert (~χ) Γ) (~(~φ)) := by
    apply ND.negI
    have hχ : ND (insert (~φ) (insert (~χ) Γ)) χ :=
      weakening d2 (insert_subset_insert (subset_insert _ _))
    have hnχ : ND (insert (~φ) (insert (~χ) Γ)) (~χ) :=
      ND.hyp (mem_insert_of_mem _ (mem_insert _ _))
    exact ND.negE hnχ hχ
  exact ND.negE hnnφ hnegφ

end Thesis.Prop
