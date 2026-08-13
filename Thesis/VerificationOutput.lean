import Thesis.Prop.Main
import Thesis.Sort.Quicksort

/-!
# Public verification transcript

This file deliberately emits a compact, human-readable sample of what Lean has
accepted. It is not a substitute for `lake build`: CI runs the complete build
first, then runs this file and checks its output against `web/lean-output.txt`.
-/

-- Exact types of the principal natural-deduction results.
#check Thesis.Prop.soundness
#check Thesis.Prop.completeness_ND
#check Thesis.Prop.soundComplete

-- Exact types of the principal quicksort results.
#check Thesis.Sort.quicksort_perm
#check Thesis.Sort.quicksort_sorted
#check Thesis.Sort.quicksort_correct

-- An executable result: the verified quicksort definition is ordinary code.
#eval Thesis.Sort.quicksort [3, 1, 2]
#eval Thesis.Sort.quicksort [5, 5, 1, 4, 1, 3]
#eval Thesis.Sort.quicksort ([] : List Nat)
#eval Thesis.Sort.quicksort [2, 1, 2, 1]

-- Transitive logical assumptions of the named results.
#print axioms Thesis.Prop.soundness
#print axioms Thesis.Prop.completeness_ND
#print axioms Thesis.Prop.soundComplete
#print axioms Thesis.Prop.ex_id
#print axioms Thesis.Prop.ex_dne
#print axioms Thesis.Sort.quicksort_perm
#print axioms Thesis.Sort.quicksort_sorted
#print axioms Thesis.Sort.quicksort_correct
