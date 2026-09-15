import Thesis.Sort.Quicksort

/-! # Quicksort: ejemplos resueltos

quicksort es computable: #eval ejecuta ejemplos concretos.



Los teoremas generales prueban sus propiedades sin añadir axiomas. -/

namespace Thesis.Sort

-- ANCHOR: examples
open List

-- Ejecución de Quicksort con entradas concretas.
#eval quicksort [3, 1, 2]            -- [1, 2, 3]
#eval quicksort [5, 5, 1, 4, 1, 3]   -- [1, 1, 3, 4, 5, 5]
#eval quicksort ([] : List Nat)      -- []
#eval quicksort [2, 1, 2, 1]         -- [1, 1, 2, 2]  (se conservan las repeticiones)

-- Los teoremas generales se instancian en listas concretas.
example : quicksort [3, 1, 2] ~ [3, 1, 2] := quicksort_permutacion _
example : Ordenada (quicksort [5, 5, 1, 4, 1, 3]) := quicksort_ordenada _

-- Las dos propiedades de la especificación para una entrada ya ordenada.
example : quicksort [1, 2, 3, 4] ~ [1, 2, 3, 4] ∧ Ordenada (quicksort [1, 2, 3, 4]) :=
  quicksort_correcto _
-- ANCHOREND: examples

end Thesis.Sort
