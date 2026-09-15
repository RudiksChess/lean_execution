import Thesis.Sort.Quicksort

/-! # Auditoría de axiomas de Quicksort

Se ejecuta lake env lean Thesis/Sort/Audit.lean para obtener los axiomas
de los resultados de corrección. make audit-quicksort regenera el certificado.



La integración continua comprueba que coincide con la salida de Lean. -/

namespace Thesis.Sort

#print axioms quicksort_correcto
#print axioms quicksort_permutacion
#print axioms quicksort_ordenada

end Thesis.Sort
