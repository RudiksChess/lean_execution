import Thesis.Prop.Syntax
import Mathlib.Data.Set.Insert
import Mathlib.Tactic

namespace Thesis.Prop

open Set

-- ANCHOR: bot
/-- La falsedad ⊥ se representa en el lenguaje {¬, →} mediante ¬(P → P).


Su interpretación es falsa bajo toda valuación. -/
def Falsedad : Formula := ~(.atom "⊥" ⟶ .atom "⊥")

theorem evaluar_falsedad (v : Valuacion) : evaluar v Falsedad ↔ False := by
  -- A probar: las dos implicaciones de evaluar v Falsedad ↔ False.
  -- Método: desplegar la semántica y aplicar la identidad P → P.
  have hIdentidad : v "⊥" → v "⊥" := by
    intro hAtomo
    exact hAtomo
  constructor
  · intro h
    have hNoIdentidad : ¬ (v "⊥" → v "⊥") := h
    exact hNoIdentidad hIdentidad
  · intro hFalso
    exact False.elim hFalso
-- ANCHOREND: bot

-- ANCHOR: ndType
/-- Deducción natural clásica con contextos Γ : Set Formula y descarga de supuestos.
La completitud se demuestra con las reglas del cálculo, mediante el lema de Kalmár.



No se postula un oráculo de derivabilidad. -/
inductive ND : Set Formula → Formula → Prop
| hyp {Γ φ} : φ ∈ Γ → ND Γ φ
| impI {Γ φ ψ} : ND (insert φ Γ) ψ → ND Γ (φ ⟶ ψ)
| impE {Γ φ ψ} : ND Γ (φ ⟶ ψ) → ND Γ φ → ND Γ ψ
| negI {Γ φ} : ND (insert φ Γ) Falsedad → ND Γ (~φ)
| negE {Γ φ} : ND Γ (~φ) → ND Γ φ → ND Γ Falsedad
| botE {Γ φ} : ND Γ Falsedad → ND Γ φ
/-- Por RAA: de Γ, ¬φ ⊢ ⊥ se concluye Γ ⊢ φ, descargando ¬φ. -/
| classical {Γ φ} : ND (insert (~φ) Γ) Falsedad → ND Γ φ
-- ANCHOREND: ndType

/-! ### Lema estructural: debilitamiento (monotonía del contexto) -/

-- ANCHOR: weakening
theorem debilitamiento {Γ φ} (d : ND Γ φ) : ∀ {Δ}, Γ ⊆ Δ → ND Δ φ := by
  -- A probar: la misma conclusión bajo cualquier contexto mayor Δ.
  -- Método: inducción sobre d; Δ permanece cuantificado en cada hipótesis inductiva.
  induction d with
  | @hyp Γ φ hmem =>
      intro Δ hsub
      have hEnDelta : φ ∈ Δ := hsub hmem
      exact ND.hyp hEnDelta
  | @impI Γ φ ψ _ hipInd =>
      intro Δ hsub
      have hAmpliado : insert φ Γ ⊆ insert φ Δ := Set.insert_subset_insert hsub
      have dCuerpo : ND (insert φ Δ) ψ := hipInd hAmpliado
      -- impI descarga φ; las fórmulas de Δ permanecen.
      exact ND.impI dCuerpo
  | @impE Γ φ ψ _ _ hipIndImp hipIndAntecedente =>
      intro Δ hsub
      have dImp : ND Δ (φ ⟶ ψ) := hipIndImp hsub
      have dAntecedente : ND Δ φ := hipIndAntecedente hsub
      exact ND.impE dImp dAntecedente
  | @negI Γ φ _ hipInd =>
      intro Δ hsub
      have hAmpliado : insert φ Γ ⊆ insert φ Δ := Set.insert_subset_insert hsub
      have dFalsedad : ND (insert φ Δ) Falsedad := hipInd hAmpliado
      exact ND.negI dFalsedad
  | @negE Γ φ _ _ hipIndNeg hipIndPos =>
      intro Δ hsub
      have dNeg : ND Δ (~φ) := hipIndNeg hsub
      have dPos : ND Δ φ := hipIndPos hsub
      exact ND.negE dNeg dPos
  | @botE Γ φ _ hipInd =>
      intro Δ hsub
      have dFalsedad : ND Δ Falsedad := hipInd hsub
      exact ND.botE dFalsedad
  | @classical Γ φ _ hipInd =>
      intro Δ hsub
      have hAmpliado : insert (~φ) Γ ⊆ insert (~φ) Δ := Set.insert_subset_insert hsub
      have dFalsedad : ND (insert (~φ) Δ) Falsedad := hipInd hAmpliado
      -- Por RAA objeto, se descarga ~φ y se concluye φ bajo Δ.
      exact ND.classical dFalsedad
-- ANCHOREND: weakening

/-! ### Reglas derivadas -/

-- ANCHOR: dni
/-- Introducción de doble negación: Γ ⊢ φ ⇒ Γ ⊢ ¬¬φ. -/
theorem introduccion_doble_negacion {Γ φ} (d : ND Γ φ) : ND Γ (~~φ) := by
  -- A probar: ND Γ (~~φ). Método: introducción de negación, no RAA.
  let Δ := insert (~φ) Γ
  have hNeg : (~φ) ∈ Δ := Set.mem_insert _ _
  have hInclusion : Γ ⊆ Δ := Set.subset_insert _ _
  have dNeg : ND Δ (~φ) := ND.hyp hNeg
  have dPos : ND Δ φ := debilitamiento d hInclusion
  have dFalsedad : ND Δ Falsedad := ND.negE dNeg dPos
  -- negI descarga el supuesto ~φ, no la premisa d.
  exact ND.negI dFalsedad
-- ANCHOREND: dni

-- ANCHOR: byCases
/-- Análisis clásico por casos, sin usar disyunción:
Γ, φ ⊢ χ y Γ, ¬φ ⊢ χ ⇒ Γ ⊢ χ. -/
theorem analisis_por_casos {Γ φ χ} (d1 : ND (insert φ Γ) χ) (d2 : ND (insert (~φ) Γ) χ) :
    ND Γ χ := by
  -- A probar: ND Γ χ. Método: Por RAA objeto, basta Falsedad bajo Γ, ~χ.
  let Δ := insert (~χ) Γ
  have dNeg : ND Δ (~φ) := by
    let Θ := insert φ Δ
    have hNoChi : (~χ) ∈ Θ :=
      Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hInclusion : insert φ Γ ⊆ Θ :=
      Set.insert_subset_insert (Set.subset_insert _ _)
    have dNoChi : ND Θ (~χ) := ND.hyp hNoChi
    have dChi : ND Θ χ := debilitamiento d1 hInclusion
    have dFalsedad : ND Θ Falsedad := ND.negE dNoChi dChi
    -- Se descarga φ; ~χ permanece en Δ.
    exact ND.negI dFalsedad
  have dDobleNeg : ND Δ (~~φ) := by
    let Θ := insert (~φ) Δ
    have hNoChi : (~χ) ∈ Θ :=
      Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hInclusion : insert (~φ) Γ ⊆ Θ :=
      Set.insert_subset_insert (Set.subset_insert _ _)
    have dNoChi : ND Θ (~χ) := ND.hyp hNoChi
    have dChi : ND Θ χ := debilitamiento d2 hInclusion
    have dFalsedad : ND Θ Falsedad := ND.negE dNoChi dChi
    -- Se descarga ~φ; ~χ permanece en Δ.
    exact ND.negI dFalsedad
  have dFalsedad : ND Δ Falsedad := ND.negE dDobleNeg dNeg
  -- Por RAA, se descarga únicamente el supuesto adicional ~χ.
  exact ND.classical dFalsedad
-- ANCHOREND: byCases

/-! ### Corrección y consistencia -/

-- ANCHOR: soundness
/-- Si v satisface Γ y χ, entonces satisface insert χ Γ. -/
theorem satisfaccion_insertar {v : Valuacion} {Γ : Set Formula} {χ : Formula}
    (hχ : evaluar v χ) (hΓ : ∀ ψ ∈ Γ, evaluar v ψ) :
    ∀ ψ ∈ insert χ Γ, evaluar v ψ := by
  -- A probar: cada fórmula del contexto extendido es verdadera bajo v.
  -- Método: casos de pertenencia; ψ = χ o ψ ∈ Γ.
  intro ψ hψ
  have hCasos : ψ = χ ∨ ψ ∈ Γ := Set.mem_insert_iff.mp hψ
  rcases hCasos with hIgualdad | hEnGamma
  · subst ψ
    exact hχ
  · exact hΓ ψ hEnGamma

/-- Corrección: toda derivación de ND es semánticamente válida. -/
theorem correccion {Γ φ} (d : ND Γ φ) :
    ∀ v, (∀ ψ ∈ Γ, evaluar v ψ) → evaluar v φ := by
  -- A probar: verdad semántica de la conclusión bajo toda valuación del contexto.
  -- Método: inducción sobre d, con v y la satisfacción aún cuantificados.
  induction d with
  | @hyp Γ φ hmem =>
      intro v hv
      exact hv φ hmem
  | @impI Γ φ ψ _ hipInd =>
      intro v hv
      change evaluar v φ → evaluar v ψ
      intro hPhi
      have hAmpliado : ∀ θ ∈ insert φ Γ, evaluar v θ := satisfaccion_insertar hPhi hv
      have hPsi : evaluar v ψ := hipInd v hAmpliado
      exact hPsi
  | @impE Γ φ ψ _ _ hipIndImp hipIndAntecedente =>
      intro v hv
      have hImp : evaluar v φ → evaluar v ψ := hipIndImp v hv
      have hPhi : evaluar v φ := hipIndAntecedente v hv
      exact hImp hPhi
  | @negI Γ φ _ hipInd =>
      intro v hv
      change ¬ evaluar v φ
      intro hPhi
      have hAmpliado : ∀ θ ∈ insert φ Γ, evaluar v θ := satisfaccion_insertar hPhi hv
      have hFalsedad : evaluar v Falsedad := hipInd v hAmpliado
      exact (evaluar_falsedad v).mp hFalsedad
  | @negE Γ φ _ _ hipIndNeg hipIndPos =>
      intro v hv
      have hNeg : ¬ evaluar v φ := hipIndNeg v hv
      have hPos : evaluar v φ := hipIndPos v hv
      have hFalso : False := hNeg hPos
      -- Dirección inversa: False → evaluar v Falsedad.
      exact (evaluar_falsedad v).mpr hFalso
  | @botE Γ φ _ hipInd =>
      intro v hv
      have hFalsedad : evaluar v Falsedad := hipInd v hv
      have hFalso : False := (evaluar_falsedad v).mp hFalsedad
      exact False.elim hFalso
  | @classical Γ φ _ hipInd =>
      intro v hv
      -- Por RAA metateórica, se supone ¬ evaluar v φ, no ND Γ (~φ).
      by_contra hnp
      have hNeg : evaluar v (~φ) := hnp
      have hAmpliado : ∀ θ ∈ insert (~φ) Γ, evaluar v θ := satisfaccion_insertar hNeg hv
      have hFalsedad : evaluar v Falsedad := hipInd v hAmpliado
      exact (evaluar_falsedad v).mp hFalsedad

/-- Corrección para el contexto vacío: los teoremas son tautologías. -/
theorem tautologia_de_derivable {φ} (d : ND (∅ : Set Formula) φ) : EsTautologia φ := by
  -- A probar: ∀ v, evaluar v φ. Método: corrección con contexto vacío.
  intro v
  have hVacio : ∀ ψ ∈ (∅ : Set Formula), evaluar v ψ := by
    intro ψ hψ
    have hFalso : False := hψ
    exact False.elim hFalso
  exact correccion d v hVacio

/-- Consistencia: ⊥ no es derivable desde el contexto vacío. -/
theorem no_derivable_falsedad : ¬ ND (∅ : Set Formula) Falsedad := by
  -- A probar: la inexistencia de una derivación cerrada de Falsedad.
  -- Método: introducción de negación; una tautología no puede ser siempre falsa.
  intro d
  let v : Valuacion := fun _ => True
  have hTautologia : EsTautologia Falsedad := tautologia_de_derivable d
  have hFalsedad : evaluar v Falsedad := hTautologia v
  exact (evaluar_falsedad v).mp hFalsedad
-- ANCHOREND: soundness

end Thesis.Prop
