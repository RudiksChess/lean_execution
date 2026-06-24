namespace Thesis.Prop

inductive Formula : Type
| atom : String → Formula
| neg  : Formula → Formula
| impl : Formula → Formula → Formula
deriving DecidableEq, Repr

prefix:60 "~" => Formula.neg
infixr:55 " ⟶ " => Formula.impl

abbrev Valuation : Type := String → Prop

def eval (v : Valuation) : Formula → Prop
| .atom s   => v s
| .neg p    => ¬ eval v p
| .impl p q => eval v p → eval v q

def IsTautology (φ : Formula) : Prop :=
  ∀ v : Valuation, eval v φ

end Thesis.Prop
