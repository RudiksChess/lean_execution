import Foundation.Propositional.Boolean.Tait
import Thesis.Prop.Syntax

open Classical

namespace Thesis.Prop

-- ANCHOR: tr
abbrev F : Type := LO.Propositional.NNFormula String

def traducir : Formula → F
| .atom s   => LO.Propositional.NNFormula.atom s
| .neg p    => (∼ (traducir p))
| .impl p q => (∼ (traducir p)) ⋎ (traducir q)

abbrev Satisface (v : Valuacion) (ψ : F) : Prop :=
  v ⊧ ψ
-- ANCHOREND: tr

end Thesis.Prop
