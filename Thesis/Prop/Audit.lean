import Thesis.Prop.Main

/-!
# Axiom audit

Reproducible certificate for the thesis. Running this file with
`lake env lean Thesis/Prop/Audit.lean` prints the complete set of axioms each
main result transitively depends on. Regenerate `audit.txt` with `make audit`
(see Makefile); CI fails if the committed `audit.txt` drifts.

A `sorryAx` here would mean an admitted gap; a postulated `oracle` constant
would mean completeness was smuggled in. Neither appears.
-/

namespace Thesis.Prop

#print axioms completeness_ND
#print axioms soundComplete
#print axioms soundness
#print axioms ex_id
#print axioms ex_dne

end Thesis.Prop
