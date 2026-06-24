import Thesis.Prop.Completeness

namespace Thesis.Prop

open Set

def P : Formula := .atom "P"
def Q : Formula := .atom "Q"
def taut1 : Formula := P ⟶ P

theorem taut1_is_taut : IsTautology taut1 := by
  intro v
  simp [taut1, eval]

/-- Completeness gives a derivation of `P → P` from the empty context,
    proved internally via Kalmár's lemma (no oracle). -/
theorem taut1_complete_ND : ND (∅ : Set Formula) taut1 :=
  completeness_ND taut1 taut1_is_taut

/-! ### The genuine rules are usable: hand-built derivations -/

/-- `⊢ P → P` built directly with `impI` and `hyp` (not via completeness). -/
theorem ex_id : ND (∅ : Set Formula) (P ⟶ P) :=
  ND.impI (ND.hyp (Set.mem_insert _ _))

/-- `⊢ P → (Q → P)` (a K-combinator style tautology), built by hand. -/
theorem ex_k : ND (∅ : Set Formula) (P ⟶ (Q ⟶ P)) :=
  ND.impI (ND.impI (ND.hyp (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))

/-- Double-negation elimination `⊢ ¬¬P → P`, using the classical rule. -/
theorem ex_dne : ND (∅ : Set Formula) ((~~P) ⟶ P) := by
  apply ND.impI
  apply ND.classical
  exact ND.negE (ND.hyp (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (ND.hyp (Set.mem_insert _ _))

end Thesis.Prop
