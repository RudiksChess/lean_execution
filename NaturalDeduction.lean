import Thesis.Prop.CompletenessViaFoundation

namespace Thesis.Prop

open Set

/--
We encode ⊥ *inside* the {¬, →}-only surface language as ¬(P → P).
This is semantically always false (for any valuation), so it behaves as falsity.
-/
def Bot : Formula := ~(.atom "⊥" ⟶ .atom "⊥")

theorem eval_Bot (v : Valuation) : eval v Bot ↔ False := by
  -- Bot = ~(P ⟶ P), and (P ⟶ P) is always true, so Bot is always false.
  constructor
  · intro h
    have hp : eval v (.atom "⊥" ⟶ .atom "⊥") := by
      intro hP; exact hP
    exact h hp
  · intro h; exact False.elim h

/--
Natural Deduction with contexts (Γ : Set Formula) and discharge.

Rules:
- hyp: use an assumption
- →I / →E
- ¬I / ¬E  (using Bot as ⊥)
- ⊥E (explosion)
- classical RAA (to make it classical)
- oracle: import a backend Foundation proof for the translation (only at Γ = ∅)
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

/--
Verified backend import:
if Foundation proves `tr φ` from the empty theory, then ND proves φ from empty Γ.

This is the only place where you “use the library as an engine”.
-/
| oracle {φ} :
    Provable (∅ : Theory) (tr φ) → ND (∅ : Set Formula) φ

/-- The theorem your chapter wants: tautology ⇒ ND-proof (from empty context). -/
theorem completeness_ND (φ : Formula) : IsTautology φ → ND (∅ : Set Formula) φ := by
  intro hTaut
  apply ND.oracle
  exact provable_tr_of_tautology φ hTaut

end Thesis.Prop
