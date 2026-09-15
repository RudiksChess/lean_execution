import Thesis.Prop.Main
import Thesis.Sort.Quicksort

/-! # Transcripción pública de la verificación

Este archivo muestra tipos, resultados ejecutados y axiomas emitidos por Lean.
No sustituye lake build: la integración continua compila primero el desarrollo


y compara después esta salida con web/lean-output.txt. -/

-- Tipos de los resultados principales de deducción natural.
#check Thesis.Prop.correccion
#check Thesis.Prop.completitud_ND
#check Thesis.Prop.correccion_completitud

-- Tipos de los resultados principales de Quicksort.
#check Thesis.Sort.quicksort_permutacion
#check Thesis.Sort.quicksort_ordenada
#check Thesis.Sort.quicksort_correcto

-- Ejecución de la definición verificada de Quicksort.
#eval Thesis.Sort.quicksort [3, 1, 2]
#eval Thesis.Sort.quicksort [5, 5, 1, 4, 1, 3]
#eval Thesis.Sort.quicksort ([] : List Nat)
#eval Thesis.Sort.quicksort [2, 1, 2, 1]

-- Axiomas de los que depende cada resultado, incluidas sus dependencias.
#print axioms Thesis.Prop.correccion
#print axioms Thesis.Prop.completitud_ND
#print axioms Thesis.Prop.correccion_completitud
#print axioms Thesis.Prop.ej_identidad
#print axioms Thesis.Prop.ej_eliminacion_doble_negacion
#print axioms Thesis.Sort.quicksort_permutacion
#print axioms Thesis.Sort.quicksort_ordenada
#print axioms Thesis.Sort.quicksort_correcto
