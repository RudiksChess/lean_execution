import Thesis.Prop.NaturalDeduction

namespace Thesis.Prop

open Set Classical

attribute [local instance] Classical.propDecidable

/-! ## Internal completeness of ND via Kalmár's lemma

This file proves `IsTautology φ → ND ∅ φ` *without* any oracle, using the
classical finitary argument: for a fixed valuation `v` a derivation is built
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
  -- A probar: pertenencia del literal correspondiente al átomo p.
  -- Método: inducción en ats; la premisa p ∈ ats se conserva en la hipótesis inductiva.
  induction ats with
  | nil =>
      have hFalse : False := List.not_mem_nil h
      exact False.elim hFalse
  | cons a rest ih =>
      have hCases : p = a ∨ p ∈ rest := List.mem_cons.mp h
      rcases hCases with hEq | hTail
      · subst p
        exact Set.mem_insert _ _
      · have hLiteralTail : lit v p ∈ litCtx v rest := ih hTail
        exact Set.mem_insert_of_mem (lit v a) hLiteralTail
-- ANCHOREND: atomsLits

-- ANCHOR: kalmar
/-- **Kalmár's lemma.** For a fixed valuation `v` and an atom list `ats` covering
`φ`, the literal context proves `φ` if `v ⊨ φ`, and proves `¬φ` otherwise. -/
theorem kalmar (v : Valuation) (ats : List String) :
    ∀ φ : Formula, atoms φ ⊆ ats →
      (eval v φ → ND (litCtx v ats) φ) ∧ (¬ eval v φ → ND (litCtx v ats) (~φ)) := by
  -- A probar: las conclusiones positiva y negativa, bajo cobertura de átomos.
  -- Método: inducción en la fórmula; v y ats están fijos, la cobertura no.
  intro φ
  induction φ with
  | atom s =>
      intro hsub
      have hAtom : s ∈ atoms (.atom s) := List.mem_singleton_self s
      have hs : s ∈ ats := hsub hAtom
      refine ⟨?_, ?_⟩
      · intro hev
        have hvs : v s := hev
        have hmem : lit v s ∈ litCtx v ats := lit_mem (v := v) hs
        rw [lit, if_pos hvs] at hmem
        exact ND.hyp hmem
      · intro hev
        have hvs : ¬ v s := hev
        have hmem : lit v s ∈ litCtx v ats := lit_mem (v := v) hs
        rw [lit, if_neg hvs] at hmem
        exact ND.hyp hmem
  | neg p ih =>
      intro hsub
      have hsub' : atoms p ⊆ ats := hsub
      obtain ⟨ihpos, ihneg⟩ := ih hsub'
      refine ⟨?_, ?_⟩
      · intro hev
        have hNotP : ¬ eval v p := hev
        exact ihneg hNotP
      · intro hev
        have hDoubleNeg : ¬ ¬ eval v p := hev
        -- Eliminación de doble negación metateórica, mediante lógica clásica.
        have hP : eval v p := Classical.byContradiction hDoubleNeg
        have dP : ND (litCtx v ats) p := ihpos hP
        -- Introducción de doble negación objeto; no es la eliminación anterior.
        exact dni dP
  | impl p q ihp ihq =>
      intro hsub
      have hsp : atoms p ⊆ ats := by
        intro a ha
        have hUnion : a ∈ atoms p ++ atoms q := List.mem_append.mpr (Or.inl ha)
        exact hsub hUnion
      have hsq : atoms q ⊆ ats := by
        intro a ha
        have hUnion : a ∈ atoms p ++ atoms q := List.mem_append.mpr (Or.inr ha)
        exact hsub hUnion
      obtain ⟨ihp_pos, ihp_neg⟩ := ihp hsp
      obtain ⟨ihq_pos, ihq_neg⟩ := ihq hsq
      refine ⟨?_, ?_⟩
      · intro hev
        -- Casos semánticos sobre eval v p; no se usa el lema objeto byCases.
        by_cases hp : eval v p
        · have hq : eval v q := hev hp
          have dQ : ND (litCtx v ats) q := ihq_pos hq
          have hSubset : litCtx v ats ⊆ insert p (litCtx v ats) := Set.subset_insert _ _
          have dQExtended : ND (insert p (litCtx v ats)) q := weakening dQ hSubset
          -- Se descarga p, aunque esta rama no necesita usarlo.
          exact ND.impI dQExtended
        · have dNotP : ND (litCtx v ats) (~p) := ihp_neg hp
          have hSubset : litCtx v ats ⊆ insert p (litCtx v ats) := Set.subset_insert _ _
          have h1 : ND (insert p (litCtx v ats)) (~p) :=
            weakening dNotP hSubset
          have h2 : ND (insert p (litCtx v ats)) p := ND.hyp (Set.mem_insert _ _)
          have dFalse : ND (insert p (litCtx v ats)) Bot := ND.negE h1 h2
          have dQ : ND (insert p (litCtx v ats)) q := ND.botE dFalse
          exact ND.impI dQ
      · intro hev
        have hNotImp : ¬ (eval v p → eval v q) := hev
        have hp : eval v p := by
          -- Por RAA metateórica, se supone que eval v p es falsa.
          by_contra hNotP
          have hImp : eval v p → eval v q := by
            intro hP
            have hFalse : False := hNotP hP
            exact False.elim hFalse
          exact hNotImp hImp
        have hq : ¬ eval v q := by
          intro hQ
          have hImp : eval v p → eval v q := by
            intro _
            exact hQ
          exact hNotImp hImp
        have dP : ND (litCtx v ats) p := ihp_pos hp
        have dNotQ : ND (litCtx v ats) (~q) := ihq_neg hq
        have hSubset : litCtx v ats ⊆ insert (p ⟶ q) (litCtx v ats) :=
          Set.subset_insert _ _
        have hpq : ND (insert (p ⟶ q) (litCtx v ats)) (p ⟶ q) := ND.hyp (Set.mem_insert _ _)
        have hpp : ND (insert (p ⟶ q) (litCtx v ats)) p :=
          weakening dP hSubset
        have hnq : ND (insert (p ⟶ q) (litCtx v ats)) (~q) :=
          weakening dNotQ hSubset
        have dQ : ND (insert (p ⟶ q) (litCtx v ats)) q := ND.impE hpq hpp
        have dFalse : ND (insert (p ⟶ q) (litCtx v ats)) Bot := ND.negE hnq dQ
        -- negI descarga p ⟶ q y concluye su negación bajo el contexto original.
        exact ND.negI dFalse
-- ANCHOREND: kalmar

/-! ## Discharging the atoms -/

-- ANCHOR: congr
/-- Literals depend only on the truth value, so valuations that agree on `ats`
yield the same literal context. -/
theorem lit_congr {w1 w2 : Valuation} {x : String} (h : w1 x ↔ w2 x) :
    lit w1 x = lit w2 x := by
  -- A probar: igualdad de literales. Método: casos sobre w1 x.
  by_cases hx : w1 x
  · have hx2 : w2 x := h.mp hx
    rw [lit, lit, if_pos hx, if_pos hx2]
  · have hx2 : ¬ w2 x := by
      intro hTrue
      have hx1 : w1 x := h.mpr hTrue
      exact hx hx1
    rw [lit, lit, if_neg hx, if_neg hx2]

theorem litCtx_congr {w1 w2 : Valuation} :
    ∀ (ats : List String), (∀ x ∈ ats, (w1 x ↔ w2 x)) → litCtx w1 ats = litCtx w2 ats := by
  -- A probar: igualdad de contextos. Método: inducción sobre ats.
  intro ats
  induction ats with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      have hHead : a ∈ a :: rest := List.mem_cons.mpr (Or.inl rfl)
      have ha : w1 a ↔ w2 a := h a hHead
      have hLiteral : lit w1 a = lit w2 a := lit_congr ha
      have hTail : ∀ x ∈ rest, w1 x ↔ w2 x := by
        intro x hx
        have hInList : x ∈ a :: rest := List.mem_cons.mpr (Or.inr hx)
        exact h x hInList
      have hr : litCtx w1 rest = litCtx w2 rest :=
        ih hTail
      -- Las igualdades de la cabeza y de la cola se sustituyen en insert.
      change insert (lit w1 a) (litCtx w1 rest) = insert (lit w2 a) (litCtx w2 rest)
      rw [hLiteral, hr]
-- ANCHOREND: congr

-- ANCHOR: discharge
/-- If `φ` is provable from the literal context for *every* valuation over `ats`,
then `φ` is provable outright. One atom is discharged at a time by classical cases. -/
theorem discharge {φ : Formula} :
    ∀ (ats : List String), ats.Nodup → (∀ v, ND (litCtx v ats) φ) → ND (∅ : Set Formula) φ := by
  -- A probar: ND ∅ φ. Método: inducción en ats con Nodup y la premisa universal.
  intro ats
  induction ats with
  | nil =>
      intro _ H
      let v : Valuation := fun _ => True
      have h : ND (litCtx v []) φ := H v
      simpa only [litCtx] using h
  | cons p rest ih =>
      intro hnd H
      have hParts : p ∉ rest ∧ rest.Nodup := List.nodup_cons.mp hnd
      have hpr : p ∉ rest := hParts.left
      have hrest : rest.Nodup := hParts.right
      -- La hipótesis inductiva exige una derivación para TODA valuación de rest.
      have hAll : ∀ v, ND (litCtx v rest) φ := by
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
          have hxp : x ≠ p := by
            intro hEq
            have hpInRest : p ∈ rest := hEq ▸ hx
            exact hpr hpInRest
          -- Fuera de p, Function.update conserva v x.
          simp only [Function.update_of_ne hxp]
        have hctx_f : litCtx (Function.update v p False) rest = litCtx v rest := by
          apply litCtx_congr
          intro x hx
          have hxp : x ≠ p := by
            intro hEq
            have hpInRest : p ∈ rest := hEq ▸ hx
            exact hpr hpInRest
          simp only [Function.update_of_ne hxp]
        have d1 : ND (insert (Formula.atom p) (litCtx v rest)) φ := by
          have h : ND (litCtx (Function.update v p True) (p :: rest)) φ :=
            H (Function.update v p True)
          -- Se reescribe primero la cabeza y después el contexto de rest.
          rw [litCtx, hlit_t, hctx_t] at h
          exact h
        have d2 : ND (insert (~(Formula.atom p)) (litCtx v rest)) φ := by
          have h : ND (litCtx (Function.update v p False) (p :: rest)) φ :=
            H (Function.update v p False)
          rw [litCtx, hlit_f, hctx_f] at h
          exact h
        -- byCases se instancia con Γ := litCtx v rest, fórmula := atom p, conclusión := φ.
        -- Su RAA interno descarga ~φ; el resultado no contiene el literal de p.
        exact byCases (Γ := litCtx v rest) (φ := Formula.atom p) (χ := φ) d1 d2
      -- Se aplica la hipótesis inductiva después de construir su premisa universal.
      exact ih hrest hAll
-- ANCHOREND: discharge

/-! ## Internal completeness theorem -/

-- ANCHOR: completeness
/-- **Completeness of ND** (internal, no oracle): every tautology is derivable
from the empty context. -/
theorem completeness_ND (φ : Formula) (h : IsTautology φ) : ND (∅ : Set Formula) φ := by
  -- A probar: ND ∅ φ. Método: Kalmár para cada valuación, seguido de descarga.
  let ats := (atoms φ).dedup
  have hNoDup : ats.Nodup := List.nodup_dedup _
  have hCover : atoms φ ⊆ ats := by
    intro a ha
    exact List.mem_dedup.mpr ha
  have hAll : ∀ v, ND (litCtx v ats) φ := by
    intro v
    have hTrue : eval v φ := h v
    have hPositive : eval v φ → ND (litCtx v ats) φ :=
      (kalmar v ats φ hCover).left
    exact hPositive hTrue
  exact discharge ats hNoDup hAll
-- ANCHOREND: completeness

-- ANCHOR: soundComplete
/-- **Soundness + completeness.** Derivability from the empty context coincides
exactly with being a tautology. -/
theorem soundComplete (φ : Formula) : IsTautology φ ↔ ND (∅ : Set Formula) φ := by
  -- A probar: ambas direcciones. Método: introducción del bicondicional.
  constructor
  · intro hTaut
    exact completeness_ND φ hTaut
  · intro d
    exact isTautology_of_provable d
-- ANCHOREND: soundComplete

end Thesis.Prop
