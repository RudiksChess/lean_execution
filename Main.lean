import Thesis.Prop.NaturalDeduction

namespace Thesis.Prop

def P : Formula := .atom "P"
def taut1 : Formula := P ⟶ P

theorem taut1_is_taut : IsTautology taut1 := by
  intro v
  simp [taut1, eval]

theorem taut1_complete_ND : ND (∅ : Set Formula) taut1 :=
  completeness_ND taut1 taut1_is_taut

end Thesis.Prop
