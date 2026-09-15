import Thesis.Prop.NaturalDeduction

namespace Thesis.Prop

open Set Classical

attribute [local instance] Classical.propDecidable

/-! ## Completitud de ND mediante el lema de Kalmár

Se demuestra EsTautologia φ → ND ∅ φ sin postular la conclusión.
Para cada valuación se construye una derivación desde su contexto de literales.

Los átomos se descargan uno por uno mediante análisis clásico por casos. -/

-- ANCHOR: atomsLits
/-- The list of atomos occurring in a formula (with possible repetitions). -/
def atomos : Formula → List String
| .atom s   => [s]
| .neg p    => atomos p
| .impl p q => atomos p ++ atomos q

/-- Literal del átomo p bajo v: p si v(p), y ¬p en caso contrario. -/
noncomputable def literal (v : Valuacion) (p : String) : Formula :=
  if v p then .atom p else ~(.atom p)

/-- Contexto de literales determinado por v y una lista de átomos. -/
noncomputable def contextoLiterales (v : Valuacion) : List String → Set Formula
| []        => ∅
| p :: cola => insert (literal v p) (contextoLiterales v cola)

theorem pertenencia_literal {v : Valuacion} {p : String} {listaAtomos : List String}
    (h : p ∈ listaAtomos) : literal v p ∈ contextoLiterales v listaAtomos := by
  -- A probar: pertenencia del literal correspondiente al átomo p.
  -- Método: inducción en listaAtomos; la premisa p ∈ listaAtomos se conserva en la hipótesis inductiva.
  induction listaAtomos with
  | nil =>
      have hFalso : False := List.not_mem_nil h
      exact False.elim hFalso
  | cons a cola hipInd =>
      have hCasos : p = a ∨ p ∈ cola := List.mem_cons.mp h
      rcases hCasos with hIgualdad | hCola
      · subst p
        exact Set.mem_insert _ _
      · have hLiteralCola : literal v p ∈ contextoLiterales v cola := hipInd hCola
        exact Set.mem_insert_of_mem (literal v a) hLiteralCola
-- ANCHOREND: atomsLits

-- ANCHOR: kalmar
/-- Lema de Kalmár: para v fija y una lista que contiene los átomos de φ,
el contexto de literales deriva φ si v ⊨ φ, y ¬φ si v ⊭ φ. -/
theorem kalmar (v : Valuacion) (listaAtomos : List String) :
    ∀ φ : Formula, atomos φ ⊆ listaAtomos →
      (evaluar v φ → ND (contextoLiterales v listaAtomos) φ) ∧ (¬ evaluar v φ → ND (contextoLiterales v listaAtomos) (~φ)) := by
  -- A probar: las conclusiones positiva y negativa, bajo cobertura de átomos.
  -- Método: inducción en la fórmula; v y listaAtomos están fijos, la cobertura no.
  intro φ
  induction φ with
  | atom s =>
      intro hsub
      have hAtomo : s ∈ atomos (.atom s) := List.mem_singleton_self s
      have hs : s ∈ listaAtomos := hsub hAtomo
      refine ⟨?_, ?_⟩
      · intro hev
        have hvs : v s := hev
        have hmem : literal v s ∈ contextoLiterales v listaAtomos := pertenencia_literal (v := v) hs
        rw [literal, if_pos hvs] at hmem
        exact ND.hyp hmem
      · intro hev
        have hvs : ¬ v s := hev
        have hmem : literal v s ∈ contextoLiterales v listaAtomos := pertenencia_literal (v := v) hs
        rw [literal, if_neg hvs] at hmem
        exact ND.hyp hmem
  | neg p hipInd =>
      intro hsub
      have hsub' : atomos p ⊆ listaAtomos := hsub
      obtain ⟨hipIndPos, hipIndNeg⟩ := hipInd hsub'
      refine ⟨?_, ?_⟩
      · intro hev
        have hNoP : ¬ evaluar v p := hev
        exact hipIndNeg hNoP
      · intro hev
        have hDobleNeg : ¬ ¬ evaluar v p := hev
        -- Eliminación de doble negación metateórica, mediante lógica clásica.
        have hP : evaluar v p := Classical.byContradiction hDobleNeg
        have dP : ND (contextoLiterales v listaAtomos) p := hipIndPos hP
        -- Introducción de doble negación objeto; no es la eliminación anterior.
        exact introduccion_doble_negacion dP
  | impl p q hipIndP hipIndQ =>
      intro hsub
      have hsp : atomos p ⊆ listaAtomos := by
        intro a ha
        have hUnion : a ∈ atomos p ++ atomos q := List.mem_append.mpr (Or.inl ha)
        exact hsub hUnion
      have hsq : atomos q ⊆ listaAtomos := by
        intro a ha
        have hUnion : a ∈ atomos p ++ atomos q := List.mem_append.mpr (Or.inr ha)
        exact hsub hUnion
      obtain ⟨hipIndPPos, hipIndPNeg⟩ := hipIndP hsp
      obtain ⟨hipIndQPos, hipIndQNeg⟩ := hipIndQ hsq
      refine ⟨?_, ?_⟩
      · intro hev
        -- Casos semánticos sobre evaluar v p; no se usa el lema objeto analisis_por_casos.
        by_cases hp : evaluar v p
        · have hq : evaluar v q := hev hp
          have dQ : ND (contextoLiterales v listaAtomos) q := hipIndQPos hq
          have hInclusion : contextoLiterales v listaAtomos ⊆ insert p (contextoLiterales v listaAtomos) := Set.subset_insert _ _
          have dQAmpliada : ND (insert p (contextoLiterales v listaAtomos)) q := debilitamiento dQ hInclusion
          -- Se descarga p, aunque esta rama no necesita usarlo.
          exact ND.impI dQAmpliada
        · have dNoP : ND (contextoLiterales v listaAtomos) (~p) := hipIndPNeg hp
          have hInclusion : contextoLiterales v listaAtomos ⊆ insert p (contextoLiterales v listaAtomos) := Set.subset_insert _ _
          have h1 : ND (insert p (contextoLiterales v listaAtomos)) (~p) :=
            debilitamiento dNoP hInclusion
          have h2 : ND (insert p (contextoLiterales v listaAtomos)) p := ND.hyp (Set.mem_insert _ _)
          have dFalsedad : ND (insert p (contextoLiterales v listaAtomos)) Falsedad := ND.negE h1 h2
          have dQ : ND (insert p (contextoLiterales v listaAtomos)) q := ND.botE dFalsedad
          exact ND.impI dQ
      · intro hev
        have hNoImp : ¬ (evaluar v p → evaluar v q) := hev
        have hp : evaluar v p := by
          -- Por RAA metateórica, se supone que evaluar v p es falsa.
          by_contra hNoP
          have hImp : evaluar v p → evaluar v q := by
            intro hP
            have hFalso : False := hNoP hP
            exact False.elim hFalso
          exact hNoImp hImp
        have hq : ¬ evaluar v q := by
          intro hQ
          have hImp : evaluar v p → evaluar v q := by
            intro _
            exact hQ
          exact hNoImp hImp
        have dP : ND (contextoLiterales v listaAtomos) p := hipIndPPos hp
        have dNoQ : ND (contextoLiterales v listaAtomos) (~q) := hipIndQNeg hq
        have hInclusion : contextoLiterales v listaAtomos ⊆ insert (p ⟶ q) (contextoLiterales v listaAtomos) :=
          Set.subset_insert _ _
        have hpq : ND (insert (p ⟶ q) (contextoLiterales v listaAtomos)) (p ⟶ q) := ND.hyp (Set.mem_insert _ _)
        have hpp : ND (insert (p ⟶ q) (contextoLiterales v listaAtomos)) p :=
          debilitamiento dP hInclusion
        have hnq : ND (insert (p ⟶ q) (contextoLiterales v listaAtomos)) (~q) :=
          debilitamiento dNoQ hInclusion
        have dQ : ND (insert (p ⟶ q) (contextoLiterales v listaAtomos)) q := ND.impE hpq hpp
        have dFalsedad : ND (insert (p ⟶ q) (contextoLiterales v listaAtomos)) Falsedad := ND.negE hnq dQ
        -- negI descarga p ⟶ q y concluye su negación bajo el contexto original.
        exact ND.negI dFalsedad
-- ANCHOREND: kalmar

/-! ## Discharging the atomos -/

-- ANCHOR: congr
/-- El literal de x depende solo de su valor de verdad.
El acuerdo de las valuaciones sobre una lista implica igualdad de sus contextos. -/
theorem congruencia_literal {w1 w2 : Valuacion} {x : String} (h : w1 x ↔ w2 x) :
    literal w1 x = literal w2 x := by
  -- A probar: igualdad de literales. Método: casos sobre w1 x.
  by_cases hx : w1 x
  · have hx2 : w2 x := h.mp hx
    rw [literal, literal, if_pos hx, if_pos hx2]
  · have hx2 : ¬ w2 x := by
      intro hVerdadero
      have hx1 : w1 x := h.mpr hVerdadero
      exact hx hx1
    rw [literal, literal, if_neg hx, if_neg hx2]

theorem congruencia_contextoLiterales {w1 w2 : Valuacion} :
    ∀ (listaAtomos : List String), (∀ x ∈ listaAtomos, (w1 x ↔ w2 x)) → contextoLiterales w1 listaAtomos = contextoLiterales w2 listaAtomos := by
  -- A probar: igualdad de contextos. Método: inducción sobre listaAtomos.
  intro listaAtomos
  induction listaAtomos with
  | nil => intro _; rfl
  | cons a cola hipInd =>
      intro h
      have hCabeza : a ∈ a :: cola := List.mem_cons.mpr (Or.inl rfl)
      have ha : w1 a ↔ w2 a := h a hCabeza
      have hLiteral : literal w1 a = literal w2 a := congruencia_literal ha
      have hCola : ∀ x ∈ cola, w1 x ↔ w2 x := by
        intro x hx
        have hEnLista : x ∈ a :: cola := List.mem_cons.mpr (Or.inr hx)
        exact h x hEnLista
      have hr : contextoLiterales w1 cola = contextoLiterales w2 cola :=
        hipInd hCola
      -- Las igualdades de la cabeza y de la cola se sustituyen en insert.
      change insert (literal w1 a) (contextoLiterales w1 cola) = insert (literal w2 a) (contextoLiterales w2 cola)
      rw [hLiteral, hr]
-- ANCHOREND: congr

-- ANCHOR: discharge
/-- Si la lista no tiene repeticiones y todo contexto de literales deriva φ,
entonces ∅ ⊢ φ. Se descarga un átomo por vez mediante análisis clásico por casos. -/
theorem descarga {φ : Formula} :
    ∀ (listaAtomos : List String), listaAtomos.Nodup → (∀ v, ND (contextoLiterales v listaAtomos) φ) → ND (∅ : Set Formula) φ := by
  -- A probar: ND ∅ φ. Método: inducción en listaAtomos con Nodup y la premisa universal.
  intro listaAtomos
  induction listaAtomos with
  | nil =>
      intro _ H
      let v : Valuacion := fun _ => True
      have h : ND (contextoLiterales v []) φ := H v
      simpa only [contextoLiterales] using h
  | cons p cola hipInd =>
      intro hnd H
      have hPartes : p ∉ cola ∧ cola.Nodup := List.nodup_cons.mp hnd
      have hpr : p ∉ cola := hPartes.left
      have hColaSinRepeticiones : cola.Nodup := hPartes.right
      -- La hipótesis inductiva exige una derivación para TODA valuación de cola.
      have hUniversal : ∀ v, ND (contextoLiterales v cola) φ := by
        intro v
        have hp_verdadero : (Function.update v p True) p := by simp
        have hp_falso : ¬ (Function.update v p False) p := by simp
        have hLiteralVerdadero : literal (Function.update v p True) p = Formula.atom p := by
          rw [literal, if_pos hp_verdadero]
        have hLiteralFalso : literal (Function.update v p False) p = ~(Formula.atom p) := by
          rw [literal, if_neg hp_falso]
        have hContextoVerdadero : contextoLiterales (Function.update v p True) cola = contextoLiterales v cola := by
          apply congruencia_contextoLiterales
          intro x hx
          have hxp : x ≠ p := by
            intro hIgualdad
            have hpEnCola : p ∈ cola := hIgualdad ▸ hx
            exact hpr hpEnCola
          -- Fuera de p, Function.update conserva v x.
          simp only [Function.update_of_ne hxp]
        have hContextoFalso : contextoLiterales (Function.update v p False) cola = contextoLiterales v cola := by
          apply congruencia_contextoLiterales
          intro x hx
          have hxp : x ≠ p := by
            intro hIgualdad
            have hpEnCola : p ∈ cola := hIgualdad ▸ hx
            exact hpr hpEnCola
          simp only [Function.update_of_ne hxp]
        have d1 : ND (insert (Formula.atom p) (contextoLiterales v cola)) φ := by
          have h : ND (contextoLiterales (Function.update v p True) (p :: cola)) φ :=
            H (Function.update v p True)
          -- Se reescribe primero la cabeza y después el contexto de cola.
          rw [contextoLiterales, hLiteralVerdadero, hContextoVerdadero] at h
          exact h
        have d2 : ND (insert (~(Formula.atom p)) (contextoLiterales v cola)) φ := by
          have h : ND (contextoLiterales (Function.update v p False) (p :: cola)) φ :=
            H (Function.update v p False)
          rw [contextoLiterales, hLiteralFalso, hContextoFalso] at h
          exact h
        -- analisis_por_casos se instancia con Γ := contextoLiterales v cola, fórmula := atom p, conclusión := φ.
        -- Su RAA interno descarga ~φ; el resultado no contiene el literal de p.
        exact analisis_por_casos (Γ := contextoLiterales v cola) (φ := Formula.atom p) (χ := φ) d1 d2
      -- Se aplica la hipótesis inductiva después de construir su premisa universal.
      exact hipInd hColaSinRepeticiones hUniversal
-- ANCHOREND: discharge

/-! ## Teorema de completitud -/

-- ANCHOR: completeness
/-- Completitud de ND: toda tautología se deriva desde el contexto vacío.
La demostración usa Kalmár y descarga, sin postular un oráculo. -/
theorem completitud_ND (φ : Formula) (h : EsTautologia φ) : ND (∅ : Set Formula) φ := by
  -- A probar: ND ∅ φ. Método: Kalmár para cada valuación, seguido de descarga.
  let listaAtomos := (atomos φ).dedup
  have hSinRepeticiones : listaAtomos.Nodup := List.nodup_dedup _
  have hCobertura : atomos φ ⊆ listaAtomos := by
    intro a ha
    exact List.mem_dedup.mpr ha
  have hUniversal : ∀ v, ND (contextoLiterales v listaAtomos) φ := by
    intro v
    have hVerdadero : evaluar v φ := h v
    have hPositiva : evaluar v φ → ND (contextoLiterales v listaAtomos) φ :=
      (kalmar v listaAtomos φ hCobertura).left
    exact hPositiva hVerdadero
  exact descarga listaAtomos hSinRepeticiones hUniversal
-- ANCHOREND: completeness

-- ANCHOR: soundComplete
/-- Corrección y completitud: una fórmula es derivable desde el contexto vacío
si y solo si es una tautología. -/
theorem correccion_completitud (φ : Formula) : EsTautologia φ ↔ ND (∅ : Set Formula) φ := by
  -- A probar: ambas direcciones. Método: introducción del bicondicional.
  constructor
  · intro hTautologia
    exact completitud_ND φ hTautologia
  · intro d
    exact tautologia_de_derivable d
-- ANCHOREND: soundComplete

end Thesis.Prop
