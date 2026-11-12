-- Formalización de las demostraciones de los capítulos teóricos de la tesis
-- (7, 8 y 9). Cada módulo es autocontenido y define su propia sintaxis.
import Thesis.Teoria.Lambda
import Thesis.Teoria.Sustitucion
import Thesis.Teoria.TiposSimples
import Thesis.Teoria.Cubo
import Thesis.Teoria.DeduccionNatural

/-! # Capítulos teóricos de la tesis

* `Thesis.Teoria.Lambda`: Lemas 7.6, 7.31 y 7.32; Corolarios 7.43 y 7.44
  (estos dos, con la confluencia del Teorema 7.37 como hipótesis explícita).
* `Thesis.Teoria.Sustitucion`: Lema 7.23, como igualdad literal bajo la
  convención de variables (no módulo α).
* `Thesis.Teoria.TiposSimples`: Ejemplos 7.52 y 7.53; Lema 7.57.
* `Thesis.Teoria.Cubo`: Ejemplos 8.5, 8.13, 8.15 y 8.20.
* `Thesis.Teoria.DeduccionNatural`: Proposiciones 9.6 y 9.9.

No se emplea `sorry` ni se añaden axiomas. `Thesis/Teoria/Audit.lean`
registra los axiomas de cada resultado. -/
