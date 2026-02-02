import Foundation.Propositional.ClassicalSemantics.Tait
import Thesis.Prop.Syntax

open Classical

namespace Thesis.Prop

abbrev F : Type := LO.Propositional.NNFormula String

def tr : Formula → F
| .atom s   => LO.Propositional.NNFormula.atom s
| .neg p    => (∼ (tr p))
| .impl p q => (∼ (tr p)) ⋎ (tr q)

abbrev Sat (v : Valuation) (ψ : F) : Prop :=
  v ⊧ ψ

end Thesis.Prop
