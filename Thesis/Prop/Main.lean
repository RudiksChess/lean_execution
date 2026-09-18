import Thesis.Prop.Completeness

namespace Thesis.Prop

open Set

def P : Formula := .atom "P"
def Q : Formula := .atom "Q"
def tautologiaIdentidad : Formula := P ⟶ P

theorem identidad_es_tautologia : EsTautologia tautologiaIdentidad := by
  -- A probar: P → P bajo toda valuación. Método: introducción de →.
  intro v
  change evaluar v P → evaluar v P
  intro hP
  exact hP

/-- La completitud proporciona una derivación de P → P desde el contexto vacío.
Se aplica el teorema demostrado mediante Kalmár. -/
theorem identidad_por_completitud : ND (∅ : Set Formula) tautologiaIdentidad :=
  completitud_ND tautologiaIdentidad identidad_es_tautologia

/-! ### Derivaciones construidas directamente con las reglas -/

/-- ⊢ P → P, por impI e hyp, sin recurrir a completitud. -/
theorem ej_identidad : ND (∅ : Set Formula) (P ⟶ P) := by
  -- A probar: ⊢ P → P. Método: hipótesis y descarga por impI.
  have hP : P ∈ insert P (∅ : Set Formula) := Set.mem_insert _ _
  have dP : ND (insert P (∅ : Set Formula)) P := ND.hyp hP
  exact ND.impI dP

/-- ⊢ P → (Q → P), correspondiente al combinador K, por dos introducciones de →. -/
theorem ej_k : ND (∅ : Set Formula) (P ⟶ (Q ⟶ P)) := by
  -- A probar: ⊢ P → (Q → P). Método: dos introducciones de →.
  let Γ := insert P (∅ : Set Formula)
  let Δ := insert Q Γ
  have hP : P ∈ Γ := Set.mem_insert _ _
  have hPDelta : P ∈ Δ := Set.mem_insert_of_mem Q hP
  have dP : ND Δ P := ND.hyp hPDelta
  have dQP : ND Γ (Q ⟶ P) := ND.impI dP
  -- Se descarga Q primero, y P después.
  exact ND.impI dQP

/-- Eliminación de doble negación: ⊢ ¬¬P → P, mediante RAA. -/
theorem ej_eliminacion_doble_negacion : ND (∅ : Set Formula) ((~~P) ⟶ P) := by
  -- A probar: ⊢ ~~P → P. Método: impI y RAA objeto bajo ~~P.
  let Γ := insert (~~P) (∅ : Set Formula)
  let Δ := insert (~P) Γ
  have hDoble : (~~P) ∈ Γ := Set.mem_insert _ _
  have hDobleDelta : (~~P) ∈ Δ := Set.mem_insert_of_mem _ hDoble
  have hNeg : (~P) ∈ Δ := Set.mem_insert _ _
  have dDoble : ND Δ (~~P) := ND.hyp hDobleDelta
  have dNeg : ND Δ (~P) := ND.hyp hNeg
  have dFalsedad : ND Δ Falsedad := ND.negE dDoble dNeg
  have dP : ND Γ P := ND.classical dFalsedad
  -- RAA descarga ~P; impI descarga después ~~P.
  exact ND.impI dP

end Thesis.Prop
