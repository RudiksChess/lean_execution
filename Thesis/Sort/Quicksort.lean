import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Corrección de Quicksort

Se prueban permutación, ordenamiento y su conjunción para un tipo con orden lineal.
Las pruebas siguen la definición recursiva, sin `sorry` ni axiomas añadidos.
Se reutilizan propiedades de biblioteca ya demostradas:
* `length_filter_le`: el filtro no aumenta la longitud;
* `filter_append_perm`: los filtros complementarios forman una permutación;
* `pairwise_cons` y `pairwise_append`: descomposición de la relación por pares.
No se importa un teorema de corrección de Quicksort.
-/

namespace Thesis.Sort

open List

variable {α : Type _} [LinearOrder α]

/-- Cada elemento anterior es menor o igual que cada elemento posterior. -/
-- ANCHOR: sortedDef
def Sorted (l : List α) : Prop := l.Pairwise (· ≤ ·)
-- ANCHOREND: sortedDef

-- ANCHOR: filterDecrease
omit [LinearOrder α] in
/-- Obligación común a las dos llamadas recursivas. -/
theorem filter_length_lt_cons (q : α → Bool) (p : α) (rest : List α) :
    (rest.filter q).length < (p :: rest).length := by
  -- A probar: longitud del filtro < longitud de la lista con pivote.
  -- Método: cota del filtro, seguida de n < n + 1.
  have hfilter : (rest.filter q).length ≤ rest.length :=
    List.length_filter_le q rest
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
      -- Estas llamadas son las hipótesis inductivas sobre small y large.
      -- Su legitimidad se comprueba al final en decreasing_by.
      have ihSmall : quicksort small ~ small := quicksort_perm small
      have ihLarge : quicksort large ~ large := quicksort_perm large
      -- 1. Añadir el mismo pivote conserva la permutación derecha.
      have hRight : p :: quicksort large ~ p :: large := ihLarge.cons p
      -- 2. Concatenar las dos permutaciones conserva ambas listas.
      have hAppend : quicksort small ++ (p :: quicksort large)
          ~ small ++ (p :: large) := ihSmall.append hRight
      -- 3. perm_middle desplaza el pivote al principio.
      have hPivot : small ++ (p :: large) ~ p :: (small ++ large) :=
        List.perm_middle
      -- 4. Se aplica filter_append_perm a x ≤ p y su complemento.
      have hPartition : small ++ large ~ rest :=
        List.filter_append_perm (fun x => decide (x ≤ p)) rest
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
    · exact filter_length_lt_cons (fun x => decide (x ≤ p)) p rest
    · exact filter_length_lt_cons (fun x => ! decide (x ≤ p)) p rest

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
        apply List.pairwise_cons.mpr
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
        apply List.pairwise_append.mpr
        exact ⟨hSmallPairs, hRightPairs, hCross⟩
      -- La ecuación de quicksort identifica esta concatenación con la salida.
      rw [quicksort_cons]
      change List.Pairwise (· ≤ ·) (quicksort small ++ (p :: quicksort large))
      exact hAllPairs
  termination_by l => l.length
  decreasing_by
    · exact filter_length_lt_cons (fun x => decide (x ≤ p)) p rest
    · exact filter_length_lt_cons (fun x => ! decide (x ≤ p)) p rest
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
