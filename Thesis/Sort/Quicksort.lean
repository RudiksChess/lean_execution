import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Corrección de Quicksort

Se prueban permutación, ordenamiento y su conjunción para un tipo con orden lineal.
Las pruebas siguen la definición recursiva, sin `sorry` ni axiomas añadidos.
Los lemas locales `longitud_filtro_le`, `particion_filtros_permutacion`,
`relacion_pares_cons_iff` y `relacion_pares_concatenacion_iff` desarrollan las pruebas auxiliares
con la misma estructura que el capítulo. Se reutilizan las ecuaciones de listas,
los constructores de Pairwise y las reglas elementales de permutación.
No se importa un teorema de corrección de Quicksort.
-/

namespace Thesis.Sort

open List

variable {α : Type _} [LinearOrder α]

/-- Cada elemento anterior es menor o igual que cada elemento posterior. -/
-- ANCHOR: sortedDef
def Ordenada (l : List α) : Prop := l.Pairwise (· ≤ ·)
-- ANCHOREND: sortedDef

-- ANCHOR: filterBound
omit [LinearOrder α] in
theorem longitud_filtro_le (q : α → Bool) (l : List α) :
    (l.filter q).length ≤ l.length := by
  -- A probar: el filtro no aumenta la longitud.
  -- Por inducción sobre l; hipInd es la cota para la cola.
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a cola hipInd =>
      cases hq : q a with
      | true =>
          -- Se conserva a: sumar 1 a ambos lados de hipInd.
          simp only [List.filter_cons, hq, ↓reduceIte, List.length_cons]
          exact Nat.succ_le_succ hipInd
      | false =>
          -- Se descarta a: longitud del filtro ≤ longitud de cola < longitud de a :: cola.
          simp only [List.filter_cons, hq, Bool.false_eq_true, ↓reduceIte]
          exact le_of_lt (lt_of_le_of_lt hipInd (Nat.lt_succ_self cola.length))
-- ANCHOREND: filterBound

-- ANCHOR: filterPartition
omit [LinearOrder α] in
theorem particion_filtros_permutacion (q : α → Bool) (l : List α) :
    l.filter q ++ l.filter (fun x => !q x) ~ l := by
  -- A probar: los filtros complementarios forman una permutación de l.
  -- Por inducción sobre l y casos sobre q a.
  induction l with
  | nil => exact List.Perm.refl []
  | cons a cola hipInd =>
      have hCons := hipInd.cons a
      -- hCons añade a al inicio de ambos lados de la permutación inductiva.
      cases hq : q a with
      | true =>
          -- a queda en el filtro izquierdo; cons_append permite aplicar hCons.
          simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, List.cons_append]
          exact hCons
      | false =>
          -- a queda en el derecho; perm_middle lo lleva al inicio y trans compone.
          simp only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true,
            ↓reduceIte]
          exact List.perm_middle.trans hCons
-- ANCHOREND: filterPartition

-- ANCHOR: pairwiseRules
omit [LinearOrder α] in
theorem relacion_pares_cons_iff (R : α → α → Prop) (a : α) (l : List α) :
    List.Pairwise R (a :: l) ↔ (∀ b ∈ l, R a b) ∧ List.Pairwise R l := by
  -- A probar: equivalencia entre Pairwise y las dos premisas del constructor cons.
  -- Por eliminación del constructor en una dirección e introducción en la otra.
  constructor
  · intro h
    -- Se extraen la relación de la cabeza con la cola y Pairwise de la cola.
    cases h with
    | cons hCabeza hCola => exact ⟨hCabeza, hCola⟩
  · rintro ⟨hCabeza, hCola⟩
    -- Las mismas premisas reconstruyen Pairwise para a :: l.
    exact List.Pairwise.cons hCabeza hCola

omit [LinearOrder α] in
theorem relacion_pares_concatenacion_iff (R : α → α → Prop) (l₁ l₂ : List α) :
    List.Pairwise R (l₁ ++ l₂) ↔
      List.Pairwise R l₁ ∧ List.Pairwise R l₂ ∧
        (∀ a ∈ l₁, ∀ b ∈ l₂, R a b) := by
  -- A probar: Pairwise de la concatenación equivale a las tres condiciones.
  -- Por inducción sobre l₁, con l₂ fija.
  induction l₁ with
  | nil =>
      -- [] ++ l₂ = l₂; Pairwise [] y la condición cruzada vacía se satisfacen.
      constructor
      · intro h
        exact ⟨List.Pairwise.nil, h, fun a ha => False.elim (List.not_mem_nil ha)⟩
      · rintro ⟨_, h, _⟩
        exact h
  | cons a cola hipInd =>
      -- H expresa la relación de a con una lista; C, la relación entre dos listas.
      let H := fun s : List α => ∀ z ∈ s, R a z
      let C := fun s t : List α => ∀ x ∈ s, ∀ y ∈ t, R x y
      have hCabeza : H (cola ++ l₂) ↔ H cola ∧ H l₂ := by
        -- Pertenecer a cola ++ l₂ equivale a pertenecer a uno de los dos bloques.
        constructor
        · intro h
          exact ⟨fun z hz => h z (List.mem_append_left l₂ hz),
            fun z hz => h z (List.mem_append_right cola hz)⟩
        · rintro ⟨hCola, hUltima⟩ z hz
          rcases List.mem_append.mp hz with hr | hl
          · exact hCola z hr
          · exact hUltima z hl
      have hCruce : C (a :: cola) l₂ ↔ H l₂ ∧ C cola l₂ := by
        -- Se separan la cabeza a y los elementos de cola, en ambas direcciones.
        constructor
        · intro h
          exact ⟨fun y hy => h a List.mem_cons_self y hy,
            fun x hx y hy => h x (List.mem_cons_of_mem a hx) y hy⟩
        · rintro ⟨hA, hCola⟩ x hx y hy
          rcases List.mem_cons.mp hx with ha | hr
          · subst x
            exact hA y hy
          · exact hCola x hr y hy
      -- Se despliegan la concatenación y las dos apariciones de Pairwise sobre ::.
      change List.Pairwise R ((a :: cola) ++ l₂) ↔
        List.Pairwise R (a :: cola) ∧ List.Pairwise R l₂ ∧ C (a :: cola) l₂
      rw [List.cons_append, relacion_pares_cons_iff, relacion_pares_cons_iff]
      change (H (cola ++ l₂) ∧ List.Pairwise R (cola ++ l₂)) ↔
        (H cola ∧ List.Pairwise R cola) ∧ List.Pairwise R l₂ ∧ C (a :: cola) l₂
      rw [hCabeza, hipInd, hCruce]
      -- Tras sustituir las tres equivalencias, solo se reagrupan las conjunciones.
      constructor
      · rintro ⟨⟨hr, hl⟩, hp, hq, hc⟩
        exact ⟨⟨hr, hp⟩, hq, hl, hc⟩
      · rintro ⟨⟨hr, hp⟩, hq, hl, hc⟩
        exact ⟨⟨hr, hl⟩, hp, hq, hc⟩
-- ANCHOREND: pairwiseRules

-- ANCHOR: filterDecrease
omit [LinearOrder α] in
/-- Obligación común a las dos llamadas recursivas. -/
theorem longitud_filtro_lt_cons (q : α → Bool) (p : α) (cola : List α) :
    (cola.filter q).length < (p :: cola).length := by
  -- A probar: longitud del filtro < longitud de la lista con pivote.
  -- Método: cota del filtro, seguida de n < n + 1.
  have hFiltro : (cola.filter q).length ≤ cola.length :=
    longitud_filtro_le q cola
  have hCola : cola.length < (p :: cola).length := by
    -- La longitud de p :: cola es cola.length + 1.
    change cola.length < cola.length + 1
    exact Nat.lt_succ_self cola.length
  exact lt_of_le_of_lt hFiltro hCola
-- ANCHOREND: filterDecrease

/-- El pivote es la cabeza; las particiones contienen los elementos ≤ p y > p. -/
-- ANCHOR: qsdef
def quicksort : List α → List α
  | [] => []
  | p :: cola =>
      quicksort (cola.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (cola.filter (fun x => ! decide (x ≤ p)))
  termination_by l => l.length
  decreasing_by
    -- Cada meta compara una partición con p :: cola, no con cola.
    -- Lean añade pruebas de pertenencia con attach; se eliminan de las listas.
    · rw [List.unattach_filter (l := cola.attach)
          (f := fun x => decide (x.val ≤ p))
          (g := fun x => decide (x ≤ p)) (hf := fun _ _ => rfl),
          List.unattach_attach]
      exact longitud_filtro_lt_cons (fun x => decide (x ≤ p)) p cola
    · rw [List.unattach_filter (l := cola.attach)
          (f := fun x => ! decide (x.val ≤ p))
          (g := fun x => ! decide (x ≤ p)) (hf := fun _ _ => rfl),
          List.unattach_attach]
      exact longitud_filtro_lt_cons (fun x => ! decide (x ≤ p)) p cola
-- ANCHOREND: qsdef

-- ANCHOR: qsequations
@[simp] theorem quicksort_vacia : quicksort ([] : List α) = [] := by
  -- A probar: la ecuación del caso vacío. Se despliega quicksort.
  rw [quicksort]

/-- Ecuación de reescritura para la lista no vacía. -/
theorem quicksort_cons (p : α) (cola : List α) :
    quicksort (p :: cola) =
      quicksort (cola.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (cola.filter (fun x => ! decide (x ≤ p))) := by
  rw [quicksort]
-- ANCHOREND: qsequations

/-- La salida conserva los elementos y sus multiplicidades. -/
-- ANCHOR: perm
theorem quicksort_permutacion : ∀ l : List α, quicksort l ~ l
  | [] => by
      -- A probar: quicksort [] ~ []. Reescritura y reflexividad.
      simpa only [quicksort_vacia] using (List.Perm.refl ([] : List α))
  | p :: cola => by
      -- A probar: quicksort (p :: cola) ~ p :: cola.
      -- Método: inducción por longitud; las particiones son menores.
      let menoresIguales := cola.filter (fun x => decide (x ≤ p))
      let mayores := cola.filter (fun x => ! decide (x ≤ p))
      have hMenoresIgualesLt : menoresIguales.length < (p :: cola).length :=
        longitud_filtro_lt_cons (fun x => decide (x ≤ p)) p cola
      have hMayoresLt : mayores.length < (p :: cola).length :=
        longitud_filtro_lt_cons (fun x => ! decide (x ≤ p)) p cola
      -- Las cotas anteriores legitiman estas dos instancias inductivas.
      have hipIndMenoresIguales : quicksort menoresIguales ~ menoresIguales := quicksort_permutacion menoresIguales
      have hipIndMayores : quicksort mayores ~ mayores := quicksort_permutacion mayores
      have hParticion : menoresIguales ++ mayores ~ cola :=
        particion_filtros_permutacion (fun x => decide (x ≤ p)) cola
      -- 1. Añadir el mismo pivote conserva la permutación derecha.
      have hDerecha : p :: quicksort mayores ~ p :: mayores := hipIndMayores.cons p
      -- 2. Concatenar las dos permutaciones conserva ambas listas.
      have hConcatenacion : quicksort menoresIguales ++ (p :: quicksort mayores)
          ~ menoresIguales ++ (p :: mayores) := hipIndMenoresIguales.append hDerecha
      -- 3. perm_middle desplaza el pivote al principio.
      have hPivote : menoresIguales ++ (p :: mayores) ~ p :: (menoresIguales ++ mayores) :=
        List.perm_middle
      -- 4. La congruencia de :: se aplica a la partición anterior.
      have hCons : p :: (menoresIguales ++ mayores) ~ p :: cola := hParticion.cons p
      -- Reescritura de quicksort, seguida de las tres permutaciones.
      rw [quicksort_cons]
      change quicksort menoresIguales ++ (p :: quicksort mayores) ~ p :: cola
      calc
        quicksort menoresIguales ++ (p :: quicksort mayores)
            ~ menoresIguales ++ (p :: mayores) := hConcatenacion
        _ ~ p :: (menoresIguales ++ mayores) := hPivote
        _ ~ p :: cola := hCons
  termination_by l => l.length
  decreasing_by
    · exact hMenoresIgualesLt
    · exact hMayoresLt

/-- La pertenencia es invariante bajo la permutación ya demostrada. -/
theorem pertenencia_quicksort {a : α} {l : List α} : a ∈ quicksort l ↔ a ∈ l := by
  -- A probar: las dos direcciones de la equivalencia de pertenencia.
  -- Método: aplicar mem_iff a quicksort_permutacion, sin nueva inducción.
  have hPermutacion : quicksort l ~ l := quicksort_permutacion l
  have hPertenencia : a ∈ quicksort l ↔ a ∈ l := hPermutacion.mem_iff
  constructor
  · intro hEnSalida
    exact hPertenencia.mp hEnSalida
  · intro hEnEntrada
    exact hPertenencia.mpr hEnEntrada
-- ANCHOREND: perm

/-- La salida está ordenada de forma no decreciente. -/
-- ANCHOR: sorted_thm
theorem quicksort_ordenada : ∀ l : List α, Ordenada (quicksort l)
  | [] => by
      -- A probar: Ordenada (quicksort []). La lista vacía no tiene pares.
      rw [quicksort_vacia]
      change List.Pairwise (· ≤ ·) ([] : List α)
      exact List.Pairwise.nil
  | p :: cola => by
      -- A probar: Ordenada (quicksort (p :: cola)).
      -- Método: inducción por longitud, cotas del pivote y concatenación.
      let menoresIguales := cola.filter (fun x => decide (x ≤ p))
      let mayores := cola.filter (fun x => ! decide (x ≤ p))
      have hMenoresIgualesLt : menoresIguales.length < (p :: cola).length :=
        longitud_filtro_lt_cons (fun x => decide (x ≤ p)) p cola
      have hMayoresLt : mayores.length < (p :: cola).length :=
        longitud_filtro_lt_cons (fun x => ! decide (x ≤ p)) p cola
      have hipIndMenoresIguales : Ordenada (quicksort menoresIguales) := quicksort_ordenada menoresIguales
      have hipIndMayores : Ordenada (quicksort mayores) := quicksort_ordenada mayores
      -- Cota izquierda: pertenencia en la salida → filtro → a ≤ p.
      have hCotaMenoresIguales : ∀ a ∈ quicksort menoresIguales, a ≤ p := by
        intro a hEnSalida
        have hEnFiltro : a ∈ menoresIguales := pertenencia_quicksort.mp hEnSalida
        have hPartes : a ∈ cola ∧ decide (a ≤ p) = true :=
          List.mem_filter.mp hEnFiltro
        have hDecision : decide (a ≤ p) = true := hPartes.right
        exact of_decide_eq_true hDecision
      -- Cota derecha: pertenencia → ¬(b ≤ p) → p < b → p ≤ b.
      have hCotaMayores : ∀ b ∈ quicksort mayores, p ≤ b := by
        intro b hEnSalida
        have hEnFiltro : b ∈ mayores := pertenencia_quicksort.mp hEnSalida
        have hPartes : b ∈ cola ∧ (! decide (b ≤ p)) = true :=
          List.mem_filter.mp hEnFiltro
        have hNegado : (! decide (b ≤ p)) = true := hPartes.right
        have hFalso : decide (b ≤ p) = false := by
          simpa only [Bool.not_eq_true'] using hNegado
        have hNoLe : ¬ (b ≤ p) := of_decide_eq_false hFalso
        have hEstricto : p < b := lt_of_not_ge hNoLe
        exact le_of_lt hEstricto
      -- Ordenada se despliega para cambiar a su predicado Pairwise.
      have hParesMenoresIguales : List.Pairwise (· ≤ ·) (quicksort menoresIguales) := hipIndMenoresIguales
      have hParesMayores : List.Pairwise (· ≤ ·) (quicksort mayores) := hipIndMayores
      -- pairwise_cons: cabeza ≤ cada elemento de la cola, y cola ordenada.
      -- Se usa la dirección que construye Pairwise para p :: quicksort mayores.
      have hParesDerecha : List.Pairwise (· ≤ ·) (p :: quicksort mayores) := by
        apply (relacion_pares_cons_iff _ _ _).mpr
        constructor
        · exact hCotaMayores
        · exact hParesMayores
      -- Condición cruzada: salida izquierda frente a todo el bloque derecho.
      have hCruce : ∀ a ∈ quicksort menoresIguales,
          ∀ b ∈ p :: quicksort mayores, a ≤ b := by
        intro a hEnMenoresIguales b hEnDerecha
        have hCasos : b = p ∨ b ∈ quicksort mayores := List.mem_cons.mp hEnDerecha
        rcases hCasos with hEsPivote | hEnMayores
        · -- b es el pivote: se sustituye b por p en la meta.
          subst b
          exact hCotaMenoresIguales a hEnMenoresIguales
        · -- b está en la salida derecha: a ≤ p y p ≤ b.
          have hAP : a ≤ p := hCotaMenoresIguales a hEnMenoresIguales
          have hPB : p ≤ b := hCotaMayores b hEnMayores
          exact le_trans hAP hPB
      -- pairwise_append exige tres pruebas: izquierda, derecha y cruce.
      have hTodosPares : List.Pairwise (· ≤ ·)
          (quicksort menoresIguales ++ (p :: quicksort mayores)) := by
        apply (relacion_pares_concatenacion_iff _ _ _).mpr
        exact ⟨hParesMenoresIguales, hParesDerecha, hCruce⟩
      -- La ecuación de quicksort identifica esta concatenación con la salida.
      rw [quicksort_cons]
      change List.Pairwise (· ≤ ·) (quicksort menoresIguales ++ (p :: quicksort mayores))
      exact hTodosPares
  termination_by l => l.length
  decreasing_by
    · exact hMenoresIgualesLt
    · exact hMayoresLt
-- ANCHOREND: sorted_thm

/-- La salida satisface simultáneamente permutación y ordenamiento. -/
-- ANCHOR: correct
theorem quicksort_correcto (l : List α) :
    quicksort l ~ l ∧ Ordenada (quicksort l) := by
  -- A probar: permutación ∧ ordenamiento para la misma lista l.
  -- Método: introducción de la conjunción a partir de los dos teoremas.
  have hPermutacion : quicksort l ~ l := quicksort_permutacion l
  have hOrdenada : Ordenada (quicksort l) := quicksort_ordenada l
  exact And.intro hPermutacion hOrdenada
-- ANCHOREND: correct

end Thesis.Sort
