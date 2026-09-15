-- Dos desarrollos compilados y verificados conjuntamente:
--   Thesis.Prop.* — completitud de la deducción natural proposicional.
--   Thesis.Sort.* — corrección de Quicksort.
import Thesis.Prop.Syntax
import Thesis.Prop.NaturalDeduction
import Thesis.Prop.Completeness
import Thesis.Prop.Main
import Thesis.Sort.Quicksort
import Thesis.Sort.Examples

/-! # Desarrollos verificados — Rudik Rompich (UVG)

La biblioteca contiene dos desarrollos comprobados por Lean:

* Thesis.Prop: completitud de la deducción natural proposicional clásica
  sobre {¬, →}, mediante Kalmár y descarga de literales.
* Thesis.Sort: Quicksort produce una permutación ordenada de la entrada.

No se emplea sorry ni se postulan reglas de corrección.
La auditoría registra por separado los axiomas de ambos desarrollos.

Autor: Rudik Rompich, Universidad del Valle de Guatemala.
Tesis de licenciatura. Contacto: rom19857@uvg.edu.gt.




Repositorio e informes: https://github.com/RudiksChess/lean_execution. -/

-- La validación con Foundation se compila como un objetivo separado:
-- Thesis.Prop.CompletenessViaFoundation no comparte el módulo raíz
-- con Mathlib, porque ambas dependencias definen Matrix.map.
