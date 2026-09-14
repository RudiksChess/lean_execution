import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Corrección de Quicksort

Se prueban permutación, ordenamiento y su conjunción para un tipo con orden lineal.
Las pruebas siguen la definición recursiva, sin `sorry` ni axiomas añadidos.
Los lemas locales `filter_length_le`, `filter_partition_perm`,
`pairwise_cons_iff` y `pairwise_append_iff` desarrollan las pruebas auxiliares
con la misma estructura que el capítulo. Se reutilizan las ecuaciones de listas,
los constructores de Pairwise y las reglas elementales de permutación.
No se importa un teorema de corrección de Quicksort.
-/

namespace Thesis.Sort

open List

variable {α : Type _} [LinearOrder α]

/-- Cada elemento anterior es menor o igual que cada elemento posterior. -/
-- ANCHOR: sortedDef
def Sorted (l : List α) : Prop := l.Pairwise (· ≤ ·)
-- ANCHOREND: sortedDef

-- ANCHOR: filterBound
omit [LinearOrder α] in
theorem filter_length_le (q : α → Bool) (l : List α) :
    (l.filter q).length ≤ l.length := by
  -- A probar: el filtro no aumenta la longitud.
  -- Por inducción sobre l; ih es la cota para la cola.
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
      cases hq : q a with
      | true =>
          -- Se conserva a: sumar 1 a ambos lados de ih.
          simp only [List.filter_cons, hq, ↓reduceIte, List.length_cons]
          exact Nat.succ_le_succ ih
      | false =>
          -- Se descarta a: longitud del filtro ≤ longitud de rest < longitud de a :: rest.
          simp only [List.filter_cons, hq, Bool.false_eq_true, ↓reduceIte]
          exact le_of_lt (lt_of_le_of_lt ih (Nat.lt_succ_self rest.length))
-- ANCHOREND: filterBound

-- ANCHOR: filterPartition
omit [LinearOrder α] in
theorem filter_partition_perm (q : α → Bool) (l : List α) :
    l.filter q ++ l.filter (fun x => !q x) ~ l := by
  -- A probar: los filtros complementarios forman una permutación de l.
  -- Por inducción sobre l y casos sobre q a.
  induction l with
  | nil => exact List.Perm.refl []
  | cons a rest ih =>
      have hCons := ih.cons a
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
theorem pairwise_cons_iff (R : α → α → Prop) (a : α) (l : List α) :
    List.Pairwise R (a :: l) ↔ (∀ b ∈ l, R a b) ∧ List.Pairwise R l := by
  -- A probar: equivalencia entre Pairwise y las dos premisas del constructor cons.
  -- Por eliminación del constructor en una dirección e introducción en la otra.
  constructor
  · intro h
    -- Se extraen la relación de la cabeza con la cola y Pairwise de la cola.
    cases h with
    | cons hHead hTail => exact ⟨hHead, hTail⟩
  · rintro ⟨hHead, hTail⟩
    -- Las mismas premisas reconstruyen Pairwise para a :: l.
    exact List.Pairwise.cons hHead hTail

omit [LinearOrder α] in
theorem pairwise_append_iff (R : α → α → Prop) (l₁ l₂ : List α) :
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
  | cons a rest ih =>
      -- H expresa la relación de a con una lista; C, la relación entre dos listas.
      let H := fun s : List α => ∀ z ∈ s, R a z
      let C := fun s t : List α => ∀ x ∈ s, ∀ y ∈ t, R x y
      have hHead : H (rest ++ l₂) ↔ H rest ∧ H l₂ := by
        -- Pertenecer a rest ++ l₂ equivale a pertenecer a uno de los dos bloques.
        constructor
        · intro h
          exact ⟨fun z hz => h z (List.mem_append_left l₂ hz),
            fun z hz => h z (List.mem_append_right rest hz)⟩
        · rintro ⟨hRest, hLast⟩ z hz
          rcases List.mem_append.mp hz with hr | hl
          · exact hRest z hr
          · exact hLast z hl
      have hCross : C (a :: rest) l₂ ↔ H l₂ ∧ C rest l₂ := by
        -- Se separan la cabeza a y los elementos de rest, en ambas direcciones.
        constructor
        · intro h
          exact ⟨fun y hy => h a List.mem_cons_self y hy,
            fun x hx y hy => h x (List.mem_cons_of_mem a hx) y hy⟩
        · rintro ⟨hA, hRest⟩ x hx y hy
          rcases List.mem_cons.mp hx with ha | hr
          · subst x
            exact hA y hy
          · exact hRest x hr y hy
      -- Se despliegan la concatenación y las dos apariciones de Pairwise sobre ::.
      change List.Pairwise R ((a :: rest) ++ l₂) ↔
        List.Pairwise R (a :: rest) ∧ List.Pairwise R l₂ ∧ C (a :: rest) l₂
      rw [List.cons_append, pairwise_cons_iff, pairwise_cons_iff]
      change (H (rest ++ l₂) ∧ List.Pairwise R (rest ++ l₂)) ↔
        (H rest ∧ List.Pairwise R rest) ∧ List.Pairwise R l₂ ∧ C (a :: rest) l₂
      rw [hHead, ih, hCross]
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
theorem filter_length_lt_cons (q : α → Bool) (p : α) (rest : List α) :
    (rest.filter q).length < (p :: rest).length := by
  -- A probar: longitud del filtro < longitud de la lista con pivote.
  -- Método: cota del filtro, seguida de n < n + 1.
  have hfilter : (rest.filter q).length ≤ rest.length :=
    filter_length_le q rest
  have htail : rest.length < (p :: rest).length := by
    -- La longitud de p :: rest es rest.length + 1.
    change rest.length < rest.length + 1
    exact Nat.lt_succ_self rest.length
  exact lt_of_le_of_lt hfilter htail
-- ANCHOREND: filterDecrease

/-- El pivote es la cabeza; las particiones contienen los elementos ≤ p y > p. -/
-- ANCHOR: qsdef
def quicksort : List α → List α
  | [] => []
  | p :: rest =>
      quicksort (rest.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (rest.filter (fun x => ! decide (x ≤ p)))
  termination_by l => l.length
  decreasing_by
    -- Cada meta compara una partición con p :: rest, no con rest.
    -- Lean añade pruebas de pertenencia con attach; se eliminan de las listas.
    · rw [List.unattach_filter (l := rest.attach)
          (f := fun x => decide (x.val ≤ p))
          (g := fun x => decide (x ≤ p)) (hf := fun _ _ => rfl),
          List.unattach_attach]
      exact filter_length_lt_cons (fun x => decide (x ≤ p)) p rest
    · rw [List.unattach_filter (l := rest.attach)
          (f := fun x => ! decide (x.val ≤ p))
          (g := fun x => ! decide (x ≤ p)) (hf := fun _ _ => rfl),
          List.unattach_attach]
      exact filter_length_lt_cons (fun x => ! decide (x ≤ p)) p rest
-- ANCHOREND: qsdef

-- ANCHOR: qsequations
@[simp] theorem quicksort_nil : quicksort ([] : List α) = [] := by
  -- A probar: la ecuación del caso vacío. Se despliega quicksort.
  rw [quicksort]

/-- Ecuación de reescritura para la lista no vacía. -/
theorem quicksort_cons (p : α) (rest : List α) :
    quicksort (p :: rest) =
      quicksort (rest.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (rest.filter (fun x => ! decide (x ≤ p))) := by
  rw [quicksort]
-- ANCHOREND: qsequations

/-- La salida conserva los elementos y sus multiplicidades. -/
-- ANCHOR: perm
theorem quicksort_perm : ∀ l : List α, quicksort l ~ l
  | [] => by
      -- A probar: quicksort [] ~ []. Reescritura y reflexividad.
      simpa only [quicksort_nil] using (List.Perm.refl ([] : List α))
  | p :: rest => by
      -- A probar: quicksort (p :: rest) ~ p :: rest.
      -- Método: inducción por longitud; las particiones son menores.
      let small := rest.filter (fun x => decide (x ≤ p))
      let large := rest.filter (fun x => ! decide (x ≤ p))
      have hSmallLt : small.length < (p :: rest).length :=
        filter_length_lt_cons (fun x => decide (x ≤ p)) p rest
      have hLargeLt : large.length < (p :: rest).length :=
        filter_length_lt_cons (fun x => ! decide (x ≤ p)) p rest
      -- Las cotas anteriores legitiman estas dos instancias inductivas.
      have ihSmall : quicksort small ~ small := quicksort_perm small
      have ihLarge : quicksort large ~ large := quicksort_perm large
      have hPartition : small ++ large ~ rest :=
        filter_partition_perm (fun x => decide (x ≤ p)) rest
      -- 1. Añadir el mismo pivote conserva la permutación derecha.
      have hRight : p :: quicksort large ~ p :: large := ihLarge.cons p
      -- 2. Concatenar las dos permutaciones conserva ambas listas.
      have hAppend : quicksort small ++ (p :: quicksort large)
          ~ small ++ (p :: large) := ihSmall.append hRight
      -- 3. perm_middle desplaza el pivote al principio.
      have hPivot : small ++ (p :: large) ~ p :: (small ++ large) :=
        List.perm_middle
      -- 4. La congruencia de :: se aplica a la partición anterior.
      have hCons : p :: (small ++ large) ~ p :: rest := hPartition.cons p
      -- Reescritura de quicksort, seguida de las tres permutaciones.
      rw [quicksort_cons]
      change quicksort small ++ (p :: quicksort large) ~ p :: rest
      calc
        quicksort small ++ (p :: quicksort large)
            ~ small ++ (p :: large) := hAppend
        _ ~ p :: (small ++ large) := hPivot
        _ ~ p :: rest := hCons
  termination_by l => l.length
  decreasing_by
    · exact hSmallLt
    · exact hLargeLt

/-- La pertenencia es invariante bajo la permutación ya demostrada. -/
theorem mem_quicksort {a : α} {l : List α} : a ∈ quicksort l ↔ a ∈ l := by
  -- A probar: las dos direcciones de la equivalencia de pertenencia.
  -- Método: aplicar mem_iff a quicksort_perm, sin nueva inducción.
  have hPerm : quicksort l ~ l := quicksort_perm l
  have hMembership : a ∈ quicksort l ↔ a ∈ l := hPerm.mem_iff
  constructor
  · intro hInOutput
    exact hMembership.mp hInOutput
  · intro hInInput
    exact hMembership.mpr hInInput
-- ANCHOREND: perm

/-- La salida está ordenada de forma no decreciente. -/
-- ANCHOR: sorted_thm
theorem quicksort_sorted : ∀ l : List α, Sorted (quicksort l)
  | [] => by
      -- A probar: Sorted (quicksort []). La lista vacía no tiene pares.
      rw [quicksort_nil]
      change List.Pairwise (· ≤ ·) ([] : List α)
      exact List.Pairwise.nil
  | p :: rest => by
      -- A probar: Sorted (quicksort (p :: rest)).
      -- Método: inducción por longitud, cotas del pivote y concatenación.
      let small := rest.filter (fun x => decide (x ≤ p))
      let large := rest.filter (fun x => ! decide (x ≤ p))
      have hSmallLt : small.length < (p :: rest).length :=
        filter_length_lt_cons (fun x => decide (x ≤ p)) p rest
      have hLargeLt : large.length < (p :: rest).length :=
        filter_length_lt_cons (fun x => ! decide (x ≤ p)) p rest
      have ihSmall : Sorted (quicksort small) := quicksort_sorted small
      have ihLarge : Sorted (quicksort large) := quicksort_sorted large
      -- Cota izquierda: pertenencia en la salida → filtro → a ≤ p.
      have hSmallBound : ∀ a ∈ quicksort small, a ≤ p := by
        intro a hInOutput
        have hInFilter : a ∈ small := mem_quicksort.mp hInOutput
        have hParts : a ∈ rest ∧ decide (a ≤ p) = true :=
          List.mem_filter.mp hInFilter
        have hDecision : decide (a ≤ p) = true := hParts.right
        exact of_decide_eq_true hDecision
      -- Cota derecha: pertenencia → ¬(b ≤ p) → p < b → p ≤ b.
      have hLargeBound : ∀ b ∈ quicksort large, p ≤ b := by
        intro b hInOutput
        have hInFilter : b ∈ large := mem_quicksort.mp hInOutput
        have hParts : b ∈ rest ∧ (! decide (b ≤ p)) = true :=
          List.mem_filter.mp hInFilter
        have hNegated : (! decide (b ≤ p)) = true := hParts.right
        have hFalse : decide (b ≤ p) = false := by
          simpa only [Bool.not_eq_true'] using hNegated
        have hNotLe : ¬ (b ≤ p) := of_decide_eq_false hFalse
        have hStrict : p < b := lt_of_not_ge hNotLe
        exact le_of_lt hStrict
      -- Sorted se despliega para cambiar a su predicado Pairwise.
      have hSmallPairs : List.Pairwise (· ≤ ·) (quicksort small) := ihSmall
      have hLargePairs : List.Pairwise (· ≤ ·) (quicksort large) := ihLarge
      -- pairwise_cons: cabeza ≤ cada elemento de la cola, y cola ordenada.
      -- Se usa la dirección que construye Pairwise para p :: quicksort large.
      have hRightPairs : List.Pairwise (· ≤ ·) (p :: quicksort large) := by
        apply (pairwise_cons_iff _ _ _).mpr
        constructor
        · exact hLargeBound
        · exact hLargePairs
      -- Condición cruzada: salida izquierda frente a todo el bloque derecho.
      have hCross : ∀ a ∈ quicksort small,
          ∀ b ∈ p :: quicksort large, a ≤ b := by
        intro a hInSmall b hInRight
        have hCases : b = p ∨ b ∈ quicksort large := List.mem_cons.mp hInRight
        rcases hCases with hIsPivot | hInLarge
        · -- b es el pivote: se sustituye b por p en la meta.
          subst b
          exact hSmallBound a hInSmall
        · -- b está en la salida derecha: a ≤ p y p ≤ b.
          have hAP : a ≤ p := hSmallBound a hInSmall
          have hPB : p ≤ b := hLargeBound b hInLarge
          exact le_trans hAP hPB
      -- pairwise_append exige tres pruebas: izquierda, derecha y cruce.
      have hAllPairs : List.Pairwise (· ≤ ·)
          (quicksort small ++ (p :: quicksort large)) := by
        apply (pairwise_append_iff _ _ _).mpr
        exact ⟨hSmallPairs, hRightPairs, hCross⟩
      -- La ecuación de quicksort identifica esta concatenación con la salida.
      rw [quicksort_cons]
      change List.Pairwise (· ≤ ·) (quicksort small ++ (p :: quicksort large))
      exact hAllPairs
  termination_by l => l.length
  decreasing_by
    · exact hSmallLt
    · exact hLargeLt
-- ANCHOREND: sorted_thm

/-- La salida satisface simultáneamente permutación y ordenamiento. -/
-- ANCHOR: correct
theorem quicksort_correct (l : List α) :
    quicksort l ~ l ∧ Sorted (quicksort l) := by
  -- A probar: permutación ∧ ordenamiento para la misma lista l.
  -- Método: introducción de la conjunción a partir de los dos teoremas.
  have hPerm : quicksort l ~ l := quicksort_perm l
  have hSorted : Sorted (quicksort l) := quicksort_sorted l
  exact And.intro hPerm hSorted
-- ANCHOREND: correct

end Thesis.Sort
