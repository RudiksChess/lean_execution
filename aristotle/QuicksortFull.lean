import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace Thesis.Sort

open List

variable {α : Type _} [LinearOrder α]

/-- A list is sorted when its elements are pairwise nondecreasing. -/
def Sorted (l : List α) : Prop := l.Pairwise (· ≤ ·)

/-- Functional quicksort: pivot on the head, recurse on the two partitions. -/
def quicksort : List α → List α
  | [] => []
  | p :: rest =>
      quicksort (rest.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (rest.filter (fun x => ! decide (x ≤ p)))
  termination_by l => l.length
  decreasing_by
    all_goals simp_wf
    all_goals exact le_trans (length_filter_le _ _) (le_of_eq (by simp))

/-- Defining equation for a nonempty list. -/
theorem quicksort_cons (p : α) (rest : List α) :
    quicksort (p :: rest) =
      quicksort (rest.filter (fun x => decide (x ≤ p)))
        ++ p :: quicksort (rest.filter (fun x => ! decide (x ≤ p))) := by
  rw [quicksort]

/-
quicksort produces a permutation of its input.
-/
-- ANCHOR: qaperm
theorem quicksort_perm (l : List α) : quicksort l ~ l := by
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  rcases l with ( _ | ⟨ p, l ⟩ ) <;> simp_all +decide [ List.perm_iff_count ];
  · unfold quicksort; aesop;
  · intro a; rw [ quicksort_cons ] ; simp +decide [ List.count_append, List.count_cons ] ;
    grind +suggestions
-- ANCHOREND: qaperm

/-
membership in quicksort is the same as in the input.
-/
theorem mem_quicksort (a : α) (l : List α) : a ∈ quicksort l ↔ a ∈ l := by
  convert ( quicksort_perm l ).mem_iff using 1

/-
quicksort produces a sorted list.
-/
-- ANCHOR: qasorted
theorem quicksort_sorted (l : List α) : Sorted (quicksort l) := by
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  rcases l with ( _ | ⟨ p, l ⟩ ) <;> simp_all +decide [ Sorted ];
  · simp +decide [ quicksort ];
  · rw [ quicksort_cons ];
    rw [ List.pairwise_append, List.pairwise_cons ];
    refine' ⟨ ih _ _ _ rfl, ⟨ _, ih _ _ _ rfl ⟩, _ ⟩;
    · exact lt_of_le_of_lt ( List.length_filter_le _ _ ) ( by linarith );
    · intro a' ha'; have := mem_quicksort a' ( filter ( fun x => !decide ( x ≤ p ) ) l ) |>.1 ha'; simp_all +decide [ List.mem_filter ] ;
      exact le_of_lt this.2;
    · exact lt_of_le_of_lt ( List.length_filter_le _ _ ) ( by linarith );
    · simp_all +decide [ mem_quicksort ];
      exact fun a ha₁ ha₂ b hb₁ hb₂ => le_trans ha₂ hb₂.le
-- ANCHOREND: qasorted

/-- **Correctness of quicksort.** The output is a sorted permutation of the input.
    TASK: replace the `sorry` with a complete proof. You may add auxiliary lemmas
    (e.g. permutation, sortedness), but do not change the definitions or this
    statement, and introduce no axioms and no `sorry`. -/
-- ANCHOR: qamain
theorem quicksort_correct (l : List α) :
    quicksort l ~ l ∧ Sorted (quicksort l) :=
  ⟨quicksort_perm l, quicksort_sorted l⟩
-- ANCHOREND: qamain

end Thesis.Sort