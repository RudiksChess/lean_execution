import Thesis.Sort.Quicksort

/-!
# Quicksort: worked examples

`quicksort` is an ordinary computable function, so we can both *run* it with `#eval`
and *prove* facts about concrete inputs using the general correctness theorems
(no `decide` is needed, and no extra axioms are incurred).
-/

namespace Thesis.Sort

-- ANCHOR: examples
open List

-- Running quicksort on concrete inputs (evaluated by the compiler).
#eval quicksort [3, 1, 2]            -- [1, 2, 3]
#eval quicksort [5, 5, 1, 4, 1, 3]   -- [1, 1, 3, 4, 5, 5]
#eval quicksort ([] : List Nat)      -- []
#eval quicksort [2, 1, 2, 1]         -- [1, 1, 2, 2]  (duplicates kept)

-- The general theorems specialise to any concrete list, with no extra work.
example : quicksort [3, 1, 2] ~ [3, 1, 2] := quicksort_perm _
example : Sorted (quicksort [5, 5, 1, 4, 1, 3]) := quicksort_sorted _

-- Both halves of the specification at once, on an already-sorted input.
example : quicksort [1, 2, 3, 4] ~ [1, 2, 3, 4] ∧ Sorted (quicksort [1, 2, 3, 4]) :=
  quicksort_correct _
-- ANCHOREND: examples

end Thesis.Sort
