import Thesis.Sort.Quicksort

/-!
# Axiom audit (quicksort)

Reproducible certificate for the quicksort report. Running this file with
`lake env lean Thesis/Sort/Audit.lean` prints the axioms each correctness result
transitively depends on. Regenerate `reports/quicksort/audit.txt` with
`make audit-quicksort`; CI fails if the committed copy drifts.
-/

namespace Thesis.Sort

#print axioms quicksort_correct
#print axioms quicksort_perm
#print axioms quicksort_sorted

end Thesis.Sort
