import Thesis.Prop.Main

/-! # Auditoría de axiomas

Se ejecuta lake env lean Thesis/Prop/Audit.lean para obtener los axiomas
de cada resultado. make audit regenera audit.txt.
La integración continua compara el certificado con la salida de Lean.

sorryAx indicaría una prueba admitida. La política rechaza ese axioma



y cualquier dependencia ajena a los axiomas permitidos. -/

namespace Thesis.Prop

#print axioms completitud_ND
#print axioms correccion_completitud
#print axioms correccion
#print axioms ej_identidad
#print axioms ej_eliminacion_doble_negacion

end Thesis.Prop
