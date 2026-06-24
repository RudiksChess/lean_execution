import Mathlib.Data.Set.Insert
import Mathlib.Tactic

namespace Thesis.Prop

open Set

/-! ## Surface syntax and semantics -/

inductive Formula : Type
| atom : String → Formula
| neg  : Formula → Formula
| impl : Formula → Formula → Formula
deriving DecidableEq, Repr

prefix:60 "~" => Formula.neg
infixr:55 " ⟶ " => Formula.impl

abbrev Valuation : Type := String → Prop

def eval (v : Valuation) : Formula → Prop
| .atom s   => v s
| .neg p    => ¬ eval v p
| .impl p q => eval v p → eval v q

def IsTautology (φ : Formula) : Prop :=
  ∀ v : Valuation, eval v φ

/-! ## The natural-deduction calculus -/

def Bot : Formula := ~(.atom "⊥" ⟶ .atom "⊥")

theorem eval_Bot (v : Valuation) : eval v Bot ↔ False := by
  constructor
  · intro h
    have hp : eval v (.atom "⊥" ⟶ .atom "⊥") := by intro hP; exact hP
    exact h hp
  · intro h; exact False.elim h

inductive ND : Set Formula → Formula → Prop
| hyp {Γ φ} : φ ∈ Γ → ND Γ φ
| impI {Γ φ ψ} : ND (insert φ Γ) ψ → ND Γ (φ ⟶ ψ)
| impE {Γ φ ψ} : ND Γ (φ ⟶ ψ) → ND Γ φ → ND Γ ψ
| negI {Γ φ} : ND (insert φ Γ) Bot → ND Γ (~φ)
| negE {Γ φ} : ND Γ (~φ) → ND Γ φ → ND Γ Bot
| botE {Γ φ} : ND Γ Bot → ND Γ φ
| classical {Γ φ} : ND (insert (~φ) Γ) Bot → ND Γ φ

theorem weakening {Γ φ} (d : ND Γ φ) : ∀ {Δ}, Γ ⊆ Δ → ND Δ φ := by
  induction d with
  | hyp hmem => intro Δ hsub; exact ND.hyp (hsub hmem)
  | impI _ ih => intro Δ hsub; exact ND.impI (ih (insert_subset_insert hsub))
  | impE _ _ ih1 ih2 => intro Δ hsub; exact ND.impE (ih1 hsub) (ih2 hsub)
  | negI _ ih => intro Δ hsub; exact ND.negI (ih (insert_subset_insert hsub))
  | negE _ _ ih1 ih2 => intro Δ hsub; exact ND.negE (ih1 hsub) (ih2 hsub)
  | botE _ ih => intro Δ hsub; exact ND.botE (ih hsub)
  | classical _ ih => intro Δ hsub; exact ND.classical (ih (insert_subset_insert hsub))

theorem dni {Γ φ} (d : ND Γ φ) : ND Γ (~~φ) := by
  apply ND.negI
  exact ND.negE (ND.hyp (Set.mem_insert _ _)) (weakening d (Set.subset_insert _ _))

theorem byCases {Γ φ χ} (d1 : ND (insert φ Γ) χ) (d2 : ND (insert (~φ) Γ) χ) :
    ND Γ χ := by
  apply ND.classical
  have e1 : ND (insert (~χ) Γ) (~φ) := by
    apply ND.negI
    refine ND.negE (ND.hyp ?_) (weakening d1 ?_)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.insert_subset_insert (Set.subset_insert _ _)
  have e2 : ND (insert (~χ) Γ) (~~φ) := by
    apply ND.negI
    refine ND.negE (ND.hyp ?_) (weakening d2 ?_)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.insert_subset_insert (Set.subset_insert _ _)
  exact ND.negE e2 e1

theorem sat_insert {v : Valuation} {Γ : Set Formula} {χ : Formula}
    (hχ : eval v χ) (hΓ : ∀ ψ ∈ Γ, eval v ψ) :
    ∀ ψ ∈ insert χ Γ, eval v ψ := by
  intro ψ hψ
  rcases Set.mem_insert_iff.1 hψ with h | h
  · subst h; exact hχ
  · exact hΓ ψ h

theorem soundness {Γ φ} (d : ND Γ φ) :
    ∀ v, (∀ ψ ∈ Γ, eval v ψ) → eval v φ := by
  induction d with
  | hyp hmem => intro v hv; exact hv _ hmem
  | impI _ ih => intro v hv hp; exact ih v (sat_insert hp hv)
  | impE _ _ ih1 ih2 => intro v hv; exact (ih1 v hv) (ih2 v hv)
  | negI _ ih => intro v hv hp; exact (eval_Bot v).1 (ih v (sat_insert hp hv))
  | negE _ _ ih1 ih2 => intro v hv; exact (eval_Bot v).2 ((ih1 v hv) (ih2 v hv))
  | botE _ ih => intro v hv; exact ((eval_Bot v).1 (ih v hv)).elim
  | classical _ ih =>
      intro v hv
      by_contra hnp
      exact (eval_Bot v).1 (ih v (sat_insert hnp hv))

theorem isTautology_of_provable {φ} (d : ND (∅ : Set Formula) φ) : IsTautology φ := by
  intro v; refine soundness d v ?_; intro ψ hψ; simp at hψ

/-! ## Completeness via Kalmár's method -/

-- ANCHOR: adefs
open Classical in
noncomputable def sat (v : Valuation) (s : String) : Formula :=
  if v s then .atom s else ~ .atom s

def occ : Formula → Finset String
| .atom s => {s}
| .neg p => occ p
| .impl p q => occ p ∪ occ q

def litset (v : Valuation) : List String → Set Formula
| [] => ∅
| s :: rest => insert (sat v s) (litset v rest)
-- ANCHOREND: adefs

@[simp] lemma sat_true {v : Valuation} {s} (h : v s) : sat v s = .atom s := by
  unfold sat; rw [if_pos h]

@[simp] lemma sat_false {v : Valuation} {s} (h : ¬ v s) : sat v s = ~ .atom s := by
  unfold sat; rw [if_neg h]

lemma sat_mem_litset {v : Valuation} {s : String} {L : List String}
    (h : s ∈ L) : sat v s ∈ litset v L := by
  induction L <;> simp_all +decide [ litset ];
  grind

lemma litset_eq_of_agree {v w : Valuation} {L : List String}
    (h : ∀ s ∈ L, (v s ↔ w s)) : litset v L = litset w L := by
  induction' L with s L ih <;> simp_all +decide [ litset ];
  unfold sat; aesop;

/-
Kalmár's lemma: from the signed literals of the atoms occurring in `φ`
we can derive `φ` (if `φ` is true under `v`) or `~φ` (if false).
-/
-- ANCHOR: akalmarsig
lemma kalmar (v : Valuation) :
    ∀ (φ : Formula) (Γ : Set Formula), (∀ s ∈ occ φ, sat v s ∈ Γ) →
      (eval v φ → ND Γ φ) ∧ (¬ eval v φ → ND Γ (~φ)) := by
-- ANCHOREND: akalmarsig
  -- Consider the case where $\phi$ is an atom $p$.
  intro φ
  induction' φ with p ih generalizing v;
  · intro Γ hΓ; by_cases h : v p <;> simp_all +decide [ occ ] ;
    · exact ⟨ fun _ => ND.hyp hΓ, fun _ => False.elim <| ‹¬eval v ( Formula.atom p ) › <| by tauto ⟩;
    · exact ⟨ fun _ => by tauto, fun _ => ND.hyp hΓ ⟩;
  · rename_i h; simp_all +decide [ eval ] ;
    intro Γ hΓ;
    exact ⟨ h v Γ hΓ |>.2, fun h' => by have := h v Γ hΓ |>.1 h'; exact dni this ⟩;
  · rename_i p q hp hq; intro Γ hΓ; simp_all +decide [ occ ] ;
    constructor;
    · intro hvq
      by_cases hp : eval v p;
      · apply ND.impI;
        convert hq v ( insert p Γ ) _ |>.1 _ using 1;
        · exact fun s hs => Set.mem_insert_of_mem _ ( hΓ s <| Or.inr hs );
        · exact hvq hp;
      · apply ND.impI;
        have h_neg_p : ND (insert p Γ) p.neg := by
          rename_i h; specialize h v ( insert p Γ ) ; simp_all +decide ;
        exact ND.botE ( ND.negE h_neg_p ( ND.hyp ( Set.mem_insert _ _ ) ) );
    · intro h;
      -- Since $\neg (eval v p \rightarrow eval v q)$, we have $eval v p$ and $\neg eval v q$.
      have hp_true : eval v p := by
        exact Classical.not_not.1 fun hp => h <| by tauto;
      have hq_false : ¬eval v q := by
        exact fun hq_true => h <| by tauto;
      apply ND.negI;
      apply ND.negE;
      convert hq v ( insert ( p.impl q ) Γ ) ( fun s hs => by
        exact Set.mem_insert_of_mem _ ( hΓ s ( Or.inr hs ) ) ) |>.2 hq_false using 1;
      exact by apply ND.impE; exact ND.hyp ( Set.mem_insert _ _ ) ; exact hp v ( insert ( p.impl q ) Γ ) ( fun s hs => by
        exact Set.mem_insert_of_mem _ ( hΓ s ( Or.inl hs ) ) ) |>.1 hp_true;

/-
Eliminate the signed-literal hypotheses one atom at a time using the law of
excluded middle (`byCases`).
-/
-- ANCHOR: aelimsig
lemma elim (φ : Formula) :
    ∀ (L : List String), L.Nodup →
      ∀ (Γ : Set Formula), (∀ v, ND (Γ ∪ litset v L) φ) → ND Γ φ := by
-- ANCHOREND: aelimsig
  intro L hL Γ hΓ
  induction' L with s rest ih generalizing Γ;
  · simpa [ litset ] using hΓ ( fun _ => True );
  · apply ih (List.nodup_cons.mp hL).right Γ;
    intro v;
    -- Define updated valuations `vt` and `vf` where `s` is true and false, respectively.
    set vt : Valuation := fun x => if x = s then True else v x
    set vf : Valuation := fun x => if x = s then False else v x;
    -- By the properties of `litset`, we have `litset vt rest = litset v rest` and `litset vf rest = litset v rest`.
    have h_litset_vt : litset vt rest = litset v rest := by
      apply litset_eq_of_agree;
      grind
    have h_litset_vf : litset vf rest = litset v rest := by
      apply litset_eq_of_agree;
      grind;
    convert byCases _ _ using 1;
    exact .atom s;
    · convert hΓ vt using 1;
      simp +decide [ litset, h_litset_vt ];
      rw [ show sat vt s = Formula.atom s from by rw [ sat_true ] ; aesop ];
    · convert hΓ vf using 1;
      simp +decide [ ← h_litset_vf, litset ];
      simp +decide [ sat, vf ]

/-! ## TASK

Prove the completeness theorem below: every tautology is derivable from the
empty context. Replace the `sorry` with a complete Lean 4 proof. You may add
any auxiliary definitions and lemmas you need. Do not modify the definitions
or statements above, and do not introduce new axioms or `sorry`. -/

-- ANCHOR: amain
theorem completeness_ND (φ : Formula) (h : IsTautology φ) : ND (∅ : Set Formula) φ := by
  have key : ∀ v, ND ((∅ : Set Formula) ∪ litset v (occ φ).toList) φ := by
    intro v
    have hΓ : ∀ s ∈ occ φ, sat v s ∈ litset v (occ φ).toList := by
      intro s hs
      exact sat_mem_litset (Finset.mem_toList.2 hs)
    have hd : ND (litset v (occ φ).toList) φ :=
      (kalmar v φ (litset v (occ φ).toList) hΓ).1 (h v)
    simpa using hd
  exact elim φ (occ φ).toList (Finset.nodup_toList _) ∅ key
-- ANCHOREND: amain

end Thesis.Prop