import Thesis.Prop.NaturalDeduction

namespace Thesis.Prop

open Set Classical

attribute [local instance] Classical.propDecidable

/-! ## Internal completeness of ND via Kalmár's lemma

This file proves `IsTautology φ → ND ∅ φ` *without* any oracle, using the
classical finitary argument: for a fixed valuation `v` we build a derivation
from the literal context determined by `v`, then discharge the (finitely many)
atoms by classical case analysis. -/

-- ANCHOR: atomsLits
/-- The list of atoms occurring in a formula (with possible repetitions). -/
def atoms : Formula → List String
| .atom s   => [s]
| .neg p    => atoms p
| .impl p q => atoms p ++ atoms q

/-- The literal chosen for atom `p` under valuation `v`: `p` if true, `¬p` if false. -/
noncomputable def lit (v : Valuation) (p : String) : Formula :=
  if v p then .atom p else ~(.atom p)

/-- The literal context for `v` over a list of atoms. -/
noncomputable def litCtx (v : Valuation) : List String → Set Formula
| []        => ∅
| p :: rest => insert (lit v p) (litCtx v rest)

theorem lit_mem {v : Valuation} {p : String} {ats : List String}
    (h : p ∈ ats) : lit v p ∈ litCtx v ats := by
  induction ats with
  | nil => simp at h
  | cons a rest ih =>
      rcases List.mem_cons.1 h with rfl | h
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (ih h)
-- ANCHOREND: atomsLits

-- ANCHOR: kalmar
/-- **Kalmár's lemma.** For a fixed valuation `v` and an atom list `ats` covering
`φ`, the literal context proves `φ` if `v ⊨ φ`, and proves `¬φ` otherwise. -/
theorem kalmar (v : Valuation) (ats : List String) :
    ∀ φ : Formula, atoms φ ⊆ ats →
      (eval v φ → ND (litCtx v ats) φ) ∧ (¬ eval v φ → ND (litCtx v ats) (~φ)) := by
  intro φ
  induction φ with
  | atom s =>
      intro hsub
      have hs : s ∈ ats := hsub (by simp [atoms])
      refine ⟨?_, ?_⟩
      · intro hev
        have hvs : v s := hev
        have hmem := lit_mem (v := v) hs
        rw [lit, if_pos hvs] at hmem
        exact ND.hyp hmem
      · intro hev
        have hvs : ¬ v s := hev
        have hmem := lit_mem (v := v) hs
        rw [lit, if_neg hvs] at hmem
        exact ND.hyp hmem
  | neg p ih =>
      intro hsub
      have hsub' : atoms p ⊆ ats := hsub
      obtain ⟨ihpos, ihneg⟩ := ih hsub'
      refine ⟨?_, ?_⟩
      · intro hev; exact ihneg hev
      · intro hev; exact dni (ihpos (not_not.1 hev))
  | impl p q ihp ihq =>
      intro hsub
      have hsp : atoms p ⊆ ats := by
        intro a ha; exact hsub (by simp only [atoms, List.mem_append]; exact Or.inl ha)
      have hsq : atoms q ⊆ ats := by
        intro a ha; exact hsub (by simp only [atoms, List.mem_append]; exact Or.inr ha)
      obtain ⟨ihp_pos, ihp_neg⟩ := ihp hsp
      obtain ⟨ihq_pos, ihq_neg⟩ := ihq hsq
      refine ⟨?_, ?_⟩
      · intro hev
        by_cases hp : eval v p
        · exact ND.impI (weakening (ihq_pos (hev hp)) (Set.subset_insert _ _))
        · apply ND.impI
          have h1 : ND (insert p (litCtx v ats)) (~p) :=
            weakening (ihp_neg hp) (Set.subset_insert _ _)
          have h2 : ND (insert p (litCtx v ats)) p := ND.hyp (Set.mem_insert _ _)
          exact ND.botE (ND.negE h1 h2)
      · intro hev
        have hp : eval v p := by by_contra h; exact hev (fun hpp => absurd hpp h)
        have hq : ¬ eval v q := fun hq => hev (fun _ => hq)
        apply ND.negI
        have hpq : ND (insert (p ⟶ q) (litCtx v ats)) (p ⟶ q) := ND.hyp (Set.mem_insert _ _)
        have hpp : ND (insert (p ⟶ q) (litCtx v ats)) p :=
          weakening (ihp_pos hp) (Set.subset_insert _ _)
        have hnq : ND (insert (p ⟶ q) (litCtx v ats)) (~q) :=
          weakening (ihq_neg hq) (Set.subset_insert _ _)
        exact ND.negE hnq (ND.impE hpq hpp)
-- ANCHOREND: kalmar

/-! ## Discharging the atoms -/

-- ANCHOR: congr
/-- Literals depend only on the truth value, so valuations that agree on `ats`
yield the same literal context. -/
theorem lit_congr {w1 w2 : Valuation} {x : String} (h : w1 x ↔ w2 x) :
    lit w1 x = lit w2 x := by
  by_cases hx : w1 x
  · rw [lit, lit, if_pos hx, if_pos (h.1 hx)]
  · rw [lit, lit, if_neg hx, if_neg (fun hc => hx (h.2 hc))]

theorem litCtx_congr {w1 w2 : Valuation} :
    ∀ (ats : List String), (∀ x ∈ ats, (w1 x ↔ w2 x)) → litCtx w1 ats = litCtx w2 ats := by
  intro ats
  induction ats with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      have ha : w1 a ↔ w2 a := h a (List.mem_cons.2 (Or.inl rfl))
      have hr : litCtx w1 rest = litCtx w2 rest :=
        ih (fun x hx => h x (List.mem_cons.2 (Or.inr hx)))
      simp only [litCtx, lit_congr ha, hr]
-- ANCHOREND: congr

-- ANCHOR: discharge
/-- If `φ` is provable from the literal context for *every* valuation over `ats`,
then `φ` is provable outright. We discharge one atom at a time by classical cases. -/
theorem discharge {φ : Formula} :
    ∀ (ats : List String), ats.Nodup → (∀ v, ND (litCtx v ats) φ) → ND (∅ : Set Formula) φ := by
  intro ats
  induction ats with
  | nil =>
      intro _ H
      have h := H (fun _ => True)
      simpa only [litCtx] using h
  | cons p rest ih =>
      intro hnd H
      obtain ⟨hpr, hrest⟩ := List.nodup_cons.1 hnd
      apply ih hrest
      intro v
      have hp_true : (Function.update v p True) p := by simp
      have hp_false : ¬ (Function.update v p False) p := by simp
      have hlit_t : lit (Function.update v p True) p = Formula.atom p := by
        rw [lit, if_pos hp_true]
      have hlit_f : lit (Function.update v p False) p = ~(Formula.atom p) := by
        rw [lit, if_neg hp_false]
      have hctx_t : litCtx (Function.update v p True) rest = litCtx v rest := by
        apply litCtx_congr
        intro x hx
        have hxp : x ≠ p := fun h => hpr (h ▸ hx)
        simp [hxp]
      have hctx_f : litCtx (Function.update v p False) rest = litCtx v rest := by
        apply litCtx_congr
        intro x hx
        have hxp : x ≠ p := fun h => hpr (h ▸ hx)
        simp [hxp]
      have d1 : ND (insert (Formula.atom p) (litCtx v rest)) φ := by
        have h := H (Function.update v p True)
        simp only [litCtx, hlit_t, hctx_t] at h
        exact h
      have d2 : ND (insert (~(Formula.atom p)) (litCtx v rest)) φ := by
        have h := H (Function.update v p False)
        simp only [litCtx, hlit_f, hctx_f] at h
        exact h
      exact byCases d1 d2
-- ANCHOREND: discharge

/-! ## Internal completeness theorem -/

-- ANCHOR: completeness
/-- **Completeness of ND** (internal, no oracle): every tautology is derivable
from the empty context. -/
theorem completeness_ND (φ : Formula) (h : IsTautology φ) : ND (∅ : Set Formula) φ := by
  refine discharge (atoms φ).dedup (List.nodup_dedup _) ?_
  intro v
  exact (kalmar v (atoms φ).dedup φ (fun a ha => List.mem_dedup.2 ha)).1 (h v)
-- ANCHOREND: completeness

-- ANCHOR: soundComplete
/-- **Soundness + completeness.** Derivability from the empty context coincides
exactly with being a tautology. -/
theorem soundComplete (φ : Formula) : IsTautology φ ↔ ND (∅ : Set Formula) φ :=
  ⟨completeness_ND φ, isTautology_of_provable⟩
-- ANCHOREND: soundComplete

end Thesis.Prop
