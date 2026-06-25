import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Correctness of Quicksort

We define functional quicksort over a linearly ordered type and prove it correct:

* `quicksort_perm`   : the output is a permutation of the input (nothing lost or invented);
* `quicksort_sorted` : the output is sorted in nondecreasing order;
* `quicksort_correct`: the conjunction — the specification of a sorting function.

Everything is proved internally from the recursive definition, with no `sorry` and no
postulated lemma.  The only axioms used are Lean's standard classical foundations.
-/

namespace Thesis.Sort

open List

variable {α : Type _} [LinearOrder α]

/-- A list is **sorted** when its elements appear in pairwise nondecreasing order.
This is exactly `List.Pairwise (· ≤ ·)`: every earlier element is `≤` every later one. -/
-- ANCHOR: sortedDef
def Sorted (l : List α) : Prop := l.Pairwise (· ≤ ·)
-- ANCHOREND: sortedDef

/--
Functional quicksort. The head `p` of a nonempty list is the **pivot**; the tail is
partitioned into the elements `≤ p` and the elements `> p` (encoded as `¬ (· ≤ p)`),
each recursively sorted, and the results concatenated around the pivot.

Termination is by the length of the list: each `filter` cannot increase the length, and
the tail is strictly shorter than `p :: rest`.
-/
-- ANCHOR: qsdef
def quicksort : List α → List α
  | [] => []
  | p :: rest =>
      quicksort (rest.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (rest.filter (fun x => ! decide (x ≤ p)))
  termination_by l => l.length
  decreasing_by
    all_goals simp_wf
    all_goals exact le_trans (length_filter_le _ _) (le_of_eq (by simp))
-- ANCHOREND: qsdef

-- ANCHOR: qsequations
@[simp] theorem quicksort_nil : quicksort ([] : List α) = [] := by rw [quicksort]

/-- The defining equation for a nonempty list, with the pivot exposed. -/
theorem quicksort_cons (p : α) (rest : List α) :
    quicksort (p :: rest) =
      quicksort (rest.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (rest.filter (fun x => ! decide (x ≤ p))) := by
  rw [quicksort]
-- ANCHOREND: qsequations

/-- **Permutation.** Quicksort outputs a rearrangement of its input. -/
-- ANCHOR: perm
theorem quicksort_perm : ∀ l : List α, quicksort l ~ l
  | [] => by simp
  | p :: rest => by
      rw [quicksort_cons]
      -- the recursive calls permute the two partition halves
      have ih1 : quicksort (rest.filter (fun x => decide (x ≤ p)))
            ~ rest.filter (fun x => decide (x ≤ p)) := quicksort_perm _
      have ih2 : quicksort (rest.filter (fun x => ! decide (x ≤ p)))
            ~ rest.filter (fun x => ! decide (x ≤ p)) := quicksort_perm _
      -- glue the halves around the pivot, then recombine the two filters
      refine (ih1.append (ih2.cons p)).trans ?_
      refine (perm_middle).trans ?_
      exact (filter_append_perm (fun x => decide (x ≤ p)) rest).cons p
  termination_by l => l.length
  decreasing_by
    all_goals simp_wf
    all_goals exact le_trans (length_filter_le _ _) (le_of_eq (by simp))

/-- Membership is preserved (an immediate corollary of the permutation). -/
theorem mem_quicksort {a : α} {l : List α} : a ∈ quicksort l ↔ a ∈ l :=
  (quicksort_perm l).mem_iff
-- ANCHOREND: perm

/-- **Sortedness.** Quicksort outputs a nondecreasing list. -/
-- ANCHOR: sorted_thm
theorem quicksort_sorted : ∀ l : List α, Sorted (quicksort l)
  | [] => by simp [Sorted]
  | p :: rest => by
      have ih1 : Sorted (quicksort (rest.filter (fun x => decide (x ≤ p)))) :=
        quicksort_sorted _
      have ih2 : Sorted (quicksort (rest.filter (fun x => ! decide (x ≤ p)))) :=
        quicksort_sorted _
      simp only [Sorted] at ih1 ih2 ⊢
      rw [quicksort_cons]
      -- every element of the "small" half is ≤ p
      have hsmall : ∀ a ∈ quicksort (rest.filter (fun x => decide (x ≤ p))), a ≤ p := by
        intro a ha
        have hmem : a ∈ rest.filter (fun x => decide (x ≤ p)) := mem_quicksort.1 ha
        simp only [mem_filter, decide_eq_true_eq] at hmem
        exact hmem.2
      -- every element of the "large" half is ≥ p (indeed > p)
      have hlarge : ∀ b ∈ quicksort (rest.filter (fun x => ! decide (x ≤ p))), p ≤ b := by
        intro b hb
        have hmem : b ∈ rest.filter (fun x => ! decide (x ≤ p)) := mem_quicksort.1 hb
        simp only [mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hmem
        exact le_of_lt (not_le.1 hmem.2)
      rw [pairwise_append]
      refine ⟨ih1, ?_, ?_⟩
      · -- the right block `p :: large` is sorted
        rw [pairwise_cons]
        exact ⟨hlarge, ih2⟩
      · -- cross condition: every small element ≤ everything in `p :: large`
        intro a ha b hb
        rcases List.mem_cons.1 hb with hbp | hb'
        · subst hbp; exact hsmall a ha
        · exact le_trans (hsmall a ha) (hlarge b hb')
  termination_by l => l.length
  decreasing_by
    all_goals simp_wf
    all_goals exact le_trans (length_filter_le _ _) (le_of_eq (by simp))
-- ANCHOREND: sorted_thm

/-- **Correctness of quicksort.** The output is a sorted permutation of the input —
i.e. quicksort meets the specification of a sorting algorithm. -/
-- ANCHOR: correct
theorem quicksort_correct (l : List α) :
    quicksort l ~ l ∧ Sorted (quicksort l) :=
  ⟨quicksort_perm l, quicksort_sorted l⟩
-- ANCHOREND: correct

end Thesis.Sort
