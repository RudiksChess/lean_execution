import Thesis.Prop.NaturalDeduction
import Mathlib.Data.Set.Insert

/-!
# Deducción natural clásica con todos los conectivos (capítulo 9 de la tesis)

Este archivo formaliza el cálculo de deducción natural al estilo de Huth y Ryan
(con cajas) que la tesis presenta en el capítulo 9, y las dos proposiciones que
allí se demuestran con derivaciones en cajas:

* «Proposición 9.6 de la tesis»: `p ∧ (q ∨ r) ⊢ (p ∧ q) ∨ (p ∧ r)`.
* «Proposición 9.9 de la tesis»: `p → q ⊣⊢ ¬q → ¬p`.

## Cómo se leen las cajas

Un juicio `Γ ⊢ₚ φ` dice que `φ` se deriva con las premisas y suposiciones
abiertas reunidas en `Γ : Set Formula`. Una caja que se abre con la suposición
`φ` es una subderivación en el contexto `insert φ Γ` (es decir, `Γ ∪ {φ}`); la
regla que cierra la caja descarga `φ` y vuelve al contexto `Γ`.

## Reglas primitivas y derivadas (como en la tesis)

* Núcleo intuicionista (primitivas): `∧i`, `∧e₁`, `∧e₂`, `→e`, `→i`, `∨i₁`,
  `∨i₂`, `∨e`, `¬e`, `⊥e`, `¬i`, más la regla de premisa/suposición.
* Principio clásico (primitiva): `RAA`. La tesis indica que RAA, LEM y `¬¬e`
  son inter-derivables y que basta añadir una; aquí se toma RAA, que es la que
  usa la Proposición 9.9 y la que formaliza el capítulo de completitud.
* Derivadas (teoremas de este archivo): `MT`, `LEM` y `¬¬e`.

El debilitamiento no es una regla del cálculo: se demuestra por inducción
(`debilitamiento`). Es lo que justifica, en la lectura por secuentes, que una
línea exterior a una caja pueda citarse dentro de ella (disciplina de cajas).
-/

namespace Thesis.Teoria.DeduccionNatural

open Set

/-! ### Fórmulas -/

/-- Fórmulas proposicionales del capítulo 9: átomos, `⊥`, `¬`, `∧`, `∨`, `→`. -/
inductive Formula : Type
/-- Proposición atómica. -/
| atomo : String → Formula
/-- Contradicción `⊥` («falsum»). -/
| falso : Formula
/-- Negación `¬φ`. -/
| neg   : Formula → Formula
/-- Conjunción `φ ∧ ψ`. -/
| conj  : Formula → Formula → Formula
/-- Disyunción `φ ∨ ψ`. -/
| disy  : Formula → Formula → Formula
/-- Implicación `φ → ψ`. -/
| impl  : Formula → Formula → Formula
deriving DecidableEq, Repr

@[inherit_doc] scoped notation "⊥ₚ" => Formula.falso
@[inherit_doc] scoped prefix:75 "¬ₚ" => Formula.neg
@[inherit_doc] scoped infixl:65 " ∧ₚ " => Formula.conj
@[inherit_doc] scoped infixl:60 " ∨ₚ " => Formula.disy
@[inherit_doc] scoped infixr:55 " →ₚ " => Formula.impl

/-! ### El cálculo -/

/-- Derivabilidad en deducción natural clásica (capítulo 9 de la tesis).
`Derivable Γ φ` es el secuente `Γ ⊢ φ`. Cada constructor es una regla del
capítulo; el orden de las premisas es el de la tesis. -/
inductive Derivable : Set Formula → Formula → Prop
/-- Premisa o suposición abierta: si `φ ∈ Γ`, entonces `Γ ⊢ φ`. -/
| hip {Γ φ} : φ ∈ Γ → Derivable Γ φ
/-- `∧i`: de `φ` y `ψ` se concluye `φ ∧ ψ`. -/
| conjI {Γ φ ψ} : Derivable Γ φ → Derivable Γ ψ → Derivable Γ (φ ∧ₚ ψ)
/-- `∧e₁`: de `φ ∧ ψ` se concluye `φ`. -/
| conjE1 {Γ φ ψ} : Derivable Γ (φ ∧ₚ ψ) → Derivable Γ φ
/-- `∧e₂`: de `φ ∧ ψ` se concluye `ψ`. -/
| conjE2 {Γ φ ψ} : Derivable Γ (φ ∧ₚ ψ) → Derivable Γ ψ
/-- `→e` (modus ponens): de `φ` y `φ → ψ` se concluye `ψ`. -/
| implE {Γ φ ψ} : Derivable Γ φ → Derivable Γ (φ →ₚ ψ) → Derivable Γ ψ
/-- `→i`: una caja que supone `φ` y llega a `ψ` da `φ → ψ`. -/
| implI {Γ φ ψ} : Derivable (insert φ Γ) ψ → Derivable Γ (φ →ₚ ψ)
/-- `∨i₁`: de `φ` se concluye `φ ∨ ψ`. -/
| disyI1 {Γ φ ψ} : Derivable Γ φ → Derivable Γ (φ ∨ₚ ψ)
/-- `∨i₂`: de `ψ` se concluye `φ ∨ ψ`. -/
| disyI2 {Γ φ ψ} : Derivable Γ ψ → Derivable Γ (φ ∨ₚ ψ)
/-- `∨e` (prueba por casos): de `φ ∨ ψ`, una caja `φ … χ` y una caja `ψ … χ`
se concluye `χ`. -/
| disyE {Γ φ ψ χ} : Derivable Γ (φ ∨ₚ ψ) → Derivable (insert φ Γ) χ →
    Derivable (insert ψ Γ) χ → Derivable Γ χ
/-- `¬e`: de `φ` y `¬φ` se concluye `⊥`. -/
| negE {Γ φ} : Derivable Γ φ → Derivable Γ (¬ₚφ) → Derivable Γ ⊥ₚ
/-- `⊥e` (explosión): de `⊥` se concluye cualquier `φ`. -/
| falsoE {Γ φ} : Derivable Γ ⊥ₚ → Derivable Γ φ
/-- `¬i`: una caja que supone `φ` y llega a `⊥` da `¬φ`. -/
| negI {Γ φ} : Derivable (insert φ Γ) ⊥ₚ → Derivable Γ (¬ₚφ)
/-- `RAA` (reducción al absurdo clásica): una caja que supone `¬φ` y llega a
`⊥` da `φ`. Es la única regla clásica primitiva. -/
| raa {Γ φ} : Derivable (insert (¬ₚφ) Γ) ⊥ₚ → Derivable Γ φ

@[inherit_doc] scoped infix:50 " ⊢ₚ " => Derivable

/-- Equivalencia demostrable `φ ⊣⊢ ψ` (Definición del capítulo 9): los
secuentes `φ ⊢ ψ` y `ψ ⊢ φ` son ambos válidos. -/
def EquivalenciaDemostrable (φ ψ : Formula) : Prop :=
  ({φ} : Set Formula) ⊢ₚ ψ ∧ ({ψ} : Set Formula) ⊢ₚ φ

@[inherit_doc] scoped infix:50 " ⊣⊢ₚ " => EquivalenciaDemostrable

/-! ### Debilitamiento (admisible, no primitivo) -/

/-- Debilitamiento: si `Γ ⊢ φ` y `Γ ⊆ Δ`, entonces `Δ ⊢ φ`. En las cajas es el
derecho a citar, dentro de una caja, líneas obtenidas fuera de ella. -/
theorem debilitamiento {Γ φ} (d : Γ ⊢ₚ φ) : ∀ {Δ}, Γ ⊆ Δ → Δ ⊢ₚ φ := by
  -- Método: inducción sobre la derivación, con Δ cuantificado.
  induction d with
  | hip hmem =>
      intro Δ hsub
      exact Derivable.hip (hsub hmem)
  | conjI _ _ hi1 hi2 =>
      intro Δ hsub
      exact Derivable.conjI (hi1 hsub) (hi2 hsub)
  | conjE1 _ hi =>
      intro Δ hsub
      exact Derivable.conjE1 (hi hsub)
  | conjE2 _ hi =>
      intro Δ hsub
      exact Derivable.conjE2 (hi hsub)
  | implE _ _ hi1 hi2 =>
      intro Δ hsub
      exact Derivable.implE (hi1 hsub) (hi2 hsub)
  | implI _ hi =>
      intro Δ hsub
      exact Derivable.implI (hi (Set.insert_subset_insert hsub))
  | disyI1 _ hi =>
      intro Δ hsub
      exact Derivable.disyI1 (hi hsub)
  | disyI2 _ hi =>
      intro Δ hsub
      exact Derivable.disyI2 (hi hsub)
  | disyE _ _ _ hi hi1 hi2 =>
      intro Δ hsub
      exact Derivable.disyE (hi hsub) (hi1 (Set.insert_subset_insert hsub))
        (hi2 (Set.insert_subset_insert hsub))
  | negE _ _ hi1 hi2 =>
      intro Δ hsub
      exact Derivable.negE (hi1 hsub) (hi2 hsub)
  | falsoE _ hi =>
      intro Δ hsub
      exact Derivable.falsoE (hi hsub)
  | negI _ hi =>
      intro Δ hsub
      exact Derivable.negI (hi (Set.insert_subset_insert hsub))
  | raa _ hi =>
      intro Δ hsub
      exact Derivable.raa (hi (Set.insert_subset_insert hsub))

/-- Reiteración dentro de una caja: una línea válida fuera de la caja sigue
siendo válida tras abrir la suposición `ψ`. -/
theorem reiterar {Γ φ} (ψ : Formula) (d : Γ ⊢ₚ φ) : insert ψ Γ ⊢ₚ φ :=
  debilitamiento d (Set.subset_insert ψ Γ)

/-! ### Proposición 9.6: distributividad -/

/-- «Proposición 9.6 de la tesis»: `p ∧ (q ∨ r) ⊢ (p ∧ q) ∨ (p ∧ r)`.

La tesis la enuncia para letras proposicionales; aquí `p`, `q`, `r` son
fórmulas arbitrarias (generalización inocua: la derivación no inspecciona su
forma). Cada `have` es una línea numerada de la derivación en cajas. -/
theorem distributividad_conj_disy (p q r : Formula) :
    ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ (p ∧ₚ q) ∨ₚ (p ∧ₚ r) := by
  -- Línea 1: p ∧ (q ∨ r) — premisa.
  have l1 : ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ p ∧ₚ (q ∨ₚ r) :=
    Derivable.hip (Set.mem_singleton _)
  -- Línea 2: p — ∧e₁ 1.
  have l2 : ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ p := Derivable.conjE1 l1
  -- Línea 3: q ∨ r — ∧e₂ 1.
  have l3 : ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ q ∨ₚ r := Derivable.conjE2 l1
  -- Línea 4 (abre la caja del caso 1): q — suposición para ∨e.
  have l4 : insert q ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ q :=
    Derivable.hip (Set.mem_insert _ _)
  -- Línea 5: p ∧ q — ∧i 2, 4. La línea 2 es exterior a la caja: se reitera.
  have l5 : insert q ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ p ∧ₚ q :=
    Derivable.conjI (reiterar q l2) l4
  -- Línea 6 (cierra la caja del caso 1): (p ∧ q) ∨ (p ∧ r) — ∨i₁ 5.
  have l6 : insert q ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ (p ∧ₚ q) ∨ₚ (p ∧ₚ r) :=
    Derivable.disyI1 l5
  -- Línea 7 (abre la caja del caso 2): r — suposición para ∨e.
  have l7 : insert r ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ r :=
    Derivable.hip (Set.mem_insert _ _)
  -- Línea 8: p ∧ r — ∧i 2, 7. De nuevo se reitera la línea 2.
  have l8 : insert r ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ p ∧ₚ r :=
    Derivable.conjI (reiterar r l2) l7
  -- Línea 9 (cierra la caja del caso 2): (p ∧ q) ∨ (p ∧ r) — ∨i₂ 8.
  have l9 : insert r ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ (p ∧ₚ q) ∨ₚ (p ∧ₚ r) :=
    Derivable.disyI2 l8
  -- Línea 10: (p ∧ q) ∨ (p ∧ r) — ∨e 3, 4–6, 7–9; descarga q y r.
  have l10 : ({p ∧ₚ (q ∨ₚ r)} : Set Formula) ⊢ₚ (p ∧ₚ q) ∨ₚ (p ∧ₚ r) :=
    Derivable.disyE l3 l6 l9
  exact l10

/-! ### Proposición 9.9: contrapositiva -/

/-- «Proposición 9.9 de la tesis», primera dirección:
`p → q ⊢ ¬q → ¬p`, con las reglas de implicación y negación (sin RAA). -/
theorem contrapositiva_ida (p q : Formula) :
    ({p →ₚ q} : Set Formula) ⊢ₚ ¬ₚq →ₚ ¬ₚp := by
  -- Línea 1: p → q — premisa (citada dentro de las dos cajas abiertas).
  have l1 : insert p (insert (¬ₚq) ({p →ₚ q} : Set Formula)) ⊢ₚ p →ₚ q :=
    Derivable.hip (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  -- Línea 2 (abre la caja exterior): ¬q — suposición para →i.
  have l2 : insert p (insert (¬ₚq) ({p →ₚ q} : Set Formula)) ⊢ₚ ¬ₚq :=
    Derivable.hip (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  -- Línea 3 (abre la caja interior): p — suposición para ¬i.
  have l3 : insert p (insert (¬ₚq) ({p →ₚ q} : Set Formula)) ⊢ₚ p :=
    Derivable.hip (Set.mem_insert _ _)
  -- Línea 4: q — →e 1, 3.
  have l4 : insert p (insert (¬ₚq) ({p →ₚ q} : Set Formula)) ⊢ₚ q :=
    Derivable.implE l3 l1
  -- Línea 5: ⊥ — ¬e 4, 2.
  have l5 : insert p (insert (¬ₚq) ({p →ₚ q} : Set Formula)) ⊢ₚ ⊥ₚ :=
    Derivable.negE l4 l2
  -- Línea 6 (cierra la caja interior): ¬p — ¬i 3–5; descarga p.
  have l6 : insert (¬ₚq) ({p →ₚ q} : Set Formula) ⊢ₚ ¬ₚp := Derivable.negI l5
  -- Línea 7 (cierra la caja exterior): ¬q → ¬p — →i 2–6; descarga ¬q.
  have l7 : ({p →ₚ q} : Set Formula) ⊢ₚ ¬ₚq →ₚ ¬ₚp := Derivable.implI l6
  exact l7

/-- «Proposición 9.9 de la tesis», segunda dirección:
`¬q → ¬p ⊢ p → q`, usando RAA para deducir `q`. -/
theorem contrapositiva_vuelta (p q : Formula) :
    ({¬ₚq →ₚ ¬ₚp} : Set Formula) ⊢ₚ p →ₚ q := by
  -- Línea 1: ¬q → ¬p — premisa (citada dentro de las dos cajas abiertas).
  have l1 : insert (¬ₚq) (insert p ({¬ₚq →ₚ ¬ₚp} : Set Formula)) ⊢ₚ ¬ₚq →ₚ ¬ₚp :=
    Derivable.hip (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  -- Línea 2 (abre la caja exterior): p — suposición para →i.
  have l2 : insert (¬ₚq) (insert p ({¬ₚq →ₚ ¬ₚp} : Set Formula)) ⊢ₚ p :=
    Derivable.hip (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  -- Línea 3 (abre la caja interior): ¬q — suposición para RAA.
  have l3 : insert (¬ₚq) (insert p ({¬ₚq →ₚ ¬ₚp} : Set Formula)) ⊢ₚ ¬ₚq :=
    Derivable.hip (Set.mem_insert _ _)
  -- Línea 4: ¬p — →e 1, 3.
  have l4 : insert (¬ₚq) (insert p ({¬ₚq →ₚ ¬ₚp} : Set Formula)) ⊢ₚ ¬ₚp :=
    Derivable.implE l3 l1
  -- Línea 5: ⊥ — ¬e 2, 4.
  have l5 : insert (¬ₚq) (insert p ({¬ₚq →ₚ ¬ₚp} : Set Formula)) ⊢ₚ ⊥ₚ :=
    Derivable.negE l2 l4
  -- Línea 6 (cierra la caja interior): q — RAA 3–5; descarga ¬q.
  have l6 : insert p ({¬ₚq →ₚ ¬ₚp} : Set Formula) ⊢ₚ q := Derivable.raa l5
  -- Línea 7 (cierra la caja exterior): p → q — →i 2–6; descarga p.
  have l7 : ({¬ₚq →ₚ ¬ₚp} : Set Formula) ⊢ₚ p →ₚ q := Derivable.implI l6
  exact l7

/-- «Proposición 9.9 de la tesis»: `p → q ⊣⊢ ¬q → ¬p`. -/
theorem contrapositiva (p q : Formula) : (p →ₚ q) ⊣⊢ₚ (¬ₚq →ₚ ¬ₚp) :=
  ⟨contrapositiva_ida p q, contrapositiva_vuelta p q⟩

/-! ### Reglas derivadas del capítulo 9: MT, LEM y ¬¬e -/

/-- Modus tollens (MT): de `φ → ψ` y `¬ψ` se concluye `¬φ`. Se deriva del
núcleo intuicionista, como afirma la tesis (no usa RAA). -/
theorem modus_tollens {Γ φ ψ} (dImp : Γ ⊢ₚ φ →ₚ ψ) (dNeg : Γ ⊢ₚ ¬ₚψ) : Γ ⊢ₚ ¬ₚφ := by
  -- Caja: se supone φ.
  have hSup : insert φ Γ ⊢ₚ φ := Derivable.hip (Set.mem_insert _ _)
  -- ψ por →e, con φ → ψ reiterada.
  have hPsi : insert φ Γ ⊢ₚ ψ := Derivable.implE hSup (reiterar φ dImp)
  -- ⊥ por ¬e, con ¬ψ reiterada.
  have hFalso : insert φ Γ ⊢ₚ ⊥ₚ := Derivable.negE hPsi (reiterar φ dNeg)
  -- ¬φ por ¬i; descarga φ.
  exact Derivable.negI hFalso

/-- Eliminación de la doble negación (`¬¬e`), derivada de RAA. -/
theorem eliminacion_doble_negacion {Γ φ} (d : Γ ⊢ₚ ¬ₚ¬ₚφ) : Γ ⊢ₚ φ := by
  -- Caja: se supone ¬φ.
  have hSup : insert (¬ₚφ) Γ ⊢ₚ ¬ₚφ := Derivable.hip (Set.mem_insert _ _)
  -- ⊥ por ¬e entre ¬φ y ¬¬φ (reiterada).
  have hFalso : insert (¬ₚφ) Γ ⊢ₚ ⊥ₚ := Derivable.negE hSup (reiterar (¬ₚφ) d)
  -- φ por RAA; descarga ¬φ.
  exact Derivable.raa hFalso

/-- Ley del medio excluido (LEM): `φ ∨ ¬φ` es derivable en cualquier contexto;
se deriva de RAA. -/
theorem medio_excluido (Γ : Set Formula) (φ : Formula) : Γ ⊢ₚ φ ∨ₚ ¬ₚφ := by
  -- Caja exterior: se supone ¬(φ ∨ ¬φ). Caja interior: se supone φ.
  have hNoLem : insert φ (insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ) ⊢ₚ ¬ₚ(φ ∨ₚ ¬ₚφ) :=
    Derivable.hip (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hPhi : insert φ (insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ) ⊢ₚ φ :=
    Derivable.hip (Set.mem_insert _ _)
  -- φ ∨ ¬φ por ∨i₁.
  have hLem1 : insert φ (insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ) ⊢ₚ φ ∨ₚ ¬ₚφ := Derivable.disyI1 hPhi
  -- ⊥ por ¬e.
  have hFalso1 : insert φ (insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ) ⊢ₚ ⊥ₚ := Derivable.negE hLem1 hNoLem
  -- ¬φ por ¬i; cierra la caja interior.
  have hNoPhi : insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ ⊢ₚ ¬ₚφ := Derivable.negI hFalso1
  -- φ ∨ ¬φ por ∨i₂.
  have hLem2 : insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ ⊢ₚ φ ∨ₚ ¬ₚφ := Derivable.disyI2 hNoPhi
  -- ⊥ por ¬e con la suposición de la caja exterior.
  have hFalso2 : insert (¬ₚ(φ ∨ₚ ¬ₚφ)) Γ ⊢ₚ ⊥ₚ :=
    Derivable.negE hLem2 (Derivable.hip (Set.mem_insert _ _))
  -- φ ∨ ¬φ por RAA; cierra la caja exterior.
  exact Derivable.raa hFalso2

/-! ### La Proposición 9.9 en el cálculo `ND` del capítulo 11

El fragmento `{¬, →}` de la Proposición 9.9 coincide con el lenguaje del
cálculo `Thesis.Prop.ND`. Las mismas siete líneas se transcriben allí; `⊥` es
la fórmula definida `Falsedad`, y `ND.impE`/`ND.negE` reciben sus premisas en
el orden (implicación, antecedente) y (negación, afirmación). -/

section Capitulo11

open Thesis.Prop

/-- «Proposición 9.9 de la tesis», primera dirección, en `Thesis.Prop.ND`:
`p → q ⊢ ¬q → ¬p`. -/
theorem contrapositiva_ida_ND (p q : Thesis.Prop.Formula) :
    ND ({p ⟶ q} : Set Thesis.Prop.Formula) (~q ⟶ ~p) := by
  -- Línea 1: p → q — premisa.
  have l1 : ND (insert p (insert (~q) ({p ⟶ q} : Set Thesis.Prop.Formula))) (p ⟶ q) :=
    ND.hyp (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  -- Línea 2: ¬q — suposición para →i.
  have l2 : ND (insert p (insert (~q) ({p ⟶ q} : Set Thesis.Prop.Formula))) (~q) :=
    ND.hyp (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  -- Línea 3: p — suposición para ¬i.
  have l3 : ND (insert p (insert (~q) ({p ⟶ q} : Set Thesis.Prop.Formula))) p :=
    ND.hyp (Set.mem_insert _ _)
  -- Línea 4: q — →e 1, 3.
  have l4 : ND (insert p (insert (~q) ({p ⟶ q} : Set Thesis.Prop.Formula))) q :=
    ND.impE l1 l3
  -- Línea 5: ⊥ — ¬e 4, 2.
  have l5 : ND (insert p (insert (~q) ({p ⟶ q} : Set Thesis.Prop.Formula))) Falsedad :=
    ND.negE l2 l4
  -- Línea 6: ¬p — ¬i 3–5.
  have l6 : ND (insert (~q) ({p ⟶ q} : Set Thesis.Prop.Formula)) (~p) := ND.negI l5
  -- Línea 7: ¬q → ¬p — →i 2–6.
  have l7 : ND ({p ⟶ q} : Set Thesis.Prop.Formula) (~q ⟶ ~p) := ND.impI l6
  exact l7

/-- «Proposición 9.9 de la tesis», segunda dirección, en `Thesis.Prop.ND`:
`¬q → ¬p ⊢ p → q`; RAA es `ND.classical`. -/
theorem contrapositiva_vuelta_ND (p q : Thesis.Prop.Formula) :
    ND ({~q ⟶ ~p} : Set Thesis.Prop.Formula) (p ⟶ q) := by
  -- Línea 1: ¬q → ¬p — premisa.
  have l1 : ND (insert (~q) (insert p ({~q ⟶ ~p} : Set Thesis.Prop.Formula))) (~q ⟶ ~p) :=
    ND.hyp (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  -- Línea 2: p — suposición para →i.
  have l2 : ND (insert (~q) (insert p ({~q ⟶ ~p} : Set Thesis.Prop.Formula))) p :=
    ND.hyp (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  -- Línea 3: ¬q — suposición para RAA.
  have l3 : ND (insert (~q) (insert p ({~q ⟶ ~p} : Set Thesis.Prop.Formula))) (~q) :=
    ND.hyp (Set.mem_insert _ _)
  -- Línea 4: ¬p — →e 1, 3.
  have l4 : ND (insert (~q) (insert p ({~q ⟶ ~p} : Set Thesis.Prop.Formula))) (~p) :=
    ND.impE l1 l3
  -- Línea 5: ⊥ — ¬e 2, 4.
  have l5 : ND (insert (~q) (insert p ({~q ⟶ ~p} : Set Thesis.Prop.Formula))) Falsedad :=
    ND.negE l4 l2
  -- Línea 6: q — RAA 3–5.
  have l6 : ND (insert p ({~q ⟶ ~p} : Set Thesis.Prop.Formula)) q := ND.classical l5
  -- Línea 7: p → q — →i 2–6.
  have l7 : ND ({~q ⟶ ~p} : Set Thesis.Prop.Formula) (p ⟶ q) := ND.impI l6
  exact l7

end Capitulo11

end Thesis.Teoria.DeduccionNatural

#print axioms Thesis.Teoria.DeduccionNatural.distributividad_conj_disy
#print axioms Thesis.Teoria.DeduccionNatural.contrapositiva_ida
#print axioms Thesis.Teoria.DeduccionNatural.contrapositiva_vuelta
#print axioms Thesis.Teoria.DeduccionNatural.contrapositiva
#print axioms Thesis.Teoria.DeduccionNatural.contrapositiva_ida_ND
#print axioms Thesis.Teoria.DeduccionNatural.contrapositiva_vuelta_ND
