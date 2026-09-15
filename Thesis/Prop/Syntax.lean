namespace Thesis.Prop

inductive Formula : Type
| atom : String → Formula
| neg  : Formula → Formula
| impl : Formula → Formula → Formula
deriving DecidableEq, Repr

prefix:60 "~" => Formula.neg
infixr:55 " ⟶ " => Formula.impl

abbrev Valuacion : Type := String → Prop

def evaluar (v : Valuacion) : Formula → Prop
| .atom s   => v s
| .neg p    => ¬ evaluar v p
| .impl p q => evaluar v p → evaluar v q

def EsTautologia (φ : Formula) : Prop :=
  ∀ v : Valuacion, evaluar v φ

end Thesis.Prop
