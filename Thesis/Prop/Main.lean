import Thesis.Prop.Completeness

namespace Thesis.Prop

open Set

def P : Formula := .atom "P"
def Q : Formula := .atom "Q"
def taut1 : Formula := P ⟶ P

theorem taut1_is_taut : IsTautology taut1 := by
  -- A probar: P → P bajo toda valuación. Método: introducción de →.
  intro v
  change eval v P → eval v P
  intro hP
  exact hP

/-- Completeness gives a derivation of `P → P` from the empty context,
    proved internally via Kalmár's lemma (no oracle). -/
theorem taut1_complete_ND : ND (∅ : Set Formula) taut1 :=
  completeness_ND taut1 taut1_is_taut

/-! ### The genuine rules are usable: hand-built derivations -/

/-- `⊢ P → P` built directly with `impI` and `hyp` (not via completeness). -/
theorem ex_id : ND (∅ : Set Formula) (P ⟶ P) := by
  -- A probar: ⊢ P → P. Método: hipótesis y descarga por impI.
  have hP : P ∈ insert P (∅ : Set Formula) := Set.mem_insert _ _
  have dP : ND (insert P (∅ : Set Formula)) P := ND.hyp hP
  exact ND.impI dP

/-- `⊢ P → (Q → P)` (a K-combinator style tautology), built by hand. -/
theorem ex_k : ND (∅ : Set Formula) (P ⟶ (Q ⟶ P)) := by
  -- A probar: ⊢ P → (Q → P). Método: dos introducciones de →.
  let Γ := insert P (∅ : Set Formula)
  let Δ := insert Q Γ
  have hP : P ∈ Γ := Set.mem_insert _ _
  have hPDelta : P ∈ Δ := Set.mem_insert_of_mem Q hP
  have dP : ND Δ P := ND.hyp hPDelta
  have dQP : ND Γ (Q ⟶ P) := ND.impI dP
  -- Se descarga Q primero, y P después.
  exact ND.impI dQP

/-- Double-negation elimination `⊢ ¬¬P → P`, using the classical rule. -/
theorem ex_dne : ND (∅ : Set Formula) ((~~P) ⟶ P) := by
  -- A probar: ⊢ ~~P → P. Método: impI y RAA objeto bajo ~~P.
  let Γ := insert (~~P) (∅ : Set Formula)
  let Δ := insert (~P) Γ
  have hDouble : (~~P) ∈ Γ := Set.mem_insert _ _
  have hDoubleDelta : (~~P) ∈ Δ := Set.mem_insert_of_mem _ hDouble
  have hNeg : (~P) ∈ Δ := Set.mem_insert _ _
  have dDouble : ND Δ (~~P) := ND.hyp hDoubleDelta
  have dNeg : ND Δ (~P) := ND.hyp hNeg
  have dFalse : ND Δ Bot := ND.negE dDouble dNeg
  have dP : ND Γ P := ND.classical dFalse
  -- RAA descarga ~P; impI descarga después ~~P.
  exact ND.impI dP

end Thesis.Prop
