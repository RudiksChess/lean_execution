import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Cálculo λ simplemente tipado (λ→ à la Church)

Formalización del Capítulo 7 de la tesis: tipos simples, λ-términos pre-tipados,
contextos (Definición 7.51), las tres reglas de derivación (variable), (aplicación)
y (abstracción), las derivaciones de los Ejemplos 7.52 y 7.53, y el Lema 7.57
(Variables libres).

Representación de los contextos. La tesis define un contexto como «una lista de
declaraciones con sujetos distintos». Aquí un `Contexto` es una lista de
declaraciones `(x, σ)` y la condición de sujetos distintos es el predicado
`BienFormado`. Esa condición se exige en la regla (variable), que es la única hoja
de un árbol de derivación; por tanto todo juicio derivable tiene un contexto bien
formado (`Deriva.bienFormado`). En particular, en la regla (abstracción) la premisa
`Γ, x : σ ⊢ M : τ` ya obliga a que `x` no esté declarada en `Γ`.

El archivo es autocontenido: no usa `sorry` ni axiomas añadidos.
-/

namespace Thesis.Teoria.TiposSimples

open Set

/-! ### Sintaxis -/

/-- Las variables de término son nombres. -/
abbrev Variable := String

/-- Tipos simples 𝕋 de la tesis: variables de tipo y tipos flecha. -/
inductive Tipo : Type
  | var : String → Tipo
  | flecha : Tipo → Tipo → Tipo
  deriving DecidableEq, Repr

/-- Notación `σ ⟶ τ` para el tipo flecha. -/
infixr:60 " ⟶ " => Tipo.flecha

/-- λ-términos pre-tipados Λ_𝕋 de la tesis: `V | (Λ_𝕋 Λ_𝕋) | (λ V : 𝕋 . Λ_𝕋)`. -/
inductive Termino : Type
  | var : Variable → Termino
  | app : Termino → Termino → Termino
  | abs : Variable → Tipo → Termino → Termino
  deriving DecidableEq, Repr

/-- Variables libres de un término pre-tipado (Definición de FV de la tesis):
`FV(x) = {x}`, `FV(M N) = FV(M) ∪ FV(N)`, `FV(λx:σ. M) = FV(M) \ {x}`. -/
def variablesLibres : Termino → Set Variable
  | .var x => {x}
  | .app M N => variablesLibres M ∪ variablesLibres N
  | .abs x _ M => variablesLibres M \ {x}

/-! ### Contextos (Definición 7.51 de la tesis) -/

/-- Una declaración `x : σ` es un par (sujeto, tipo). Un contexto es una lista de
declaraciones; la condición «con sujetos distintos» es `BienFormado`. -/
abbrev Contexto := List (Variable × Tipo)

/-- Los sujetos del contexto son distintos dos a dos (Definición 7.51, inciso 3). -/
def BienFormado (Γ : Contexto) : Prop := (Γ.map Prod.fst).Nodup

/-- Dominio de un contexto: el conjunto de las variables declaradas en él. -/
def dominio (Γ : Contexto) : Set Variable := {x | ∃ σ, (x, σ) ∈ Γ}

/-- Contexto extendido `Γ, x : σ`: la nueva declaración se agrega al final. -/
def extender (Γ : Contexto) (x : Variable) (σ : Tipo) : Contexto := Γ ++ [(x, σ)]

/-- `dom(Γ, x:σ) = dom(Γ) ∪ {x}`, hecho usado en el caso (abstracción) del Lema 7.57. -/
theorem dominio_extender (Γ : Contexto) (x : Variable) (σ : Tipo) :
    dominio (extender Γ x σ) = dominio Γ ∪ {x} := by
  ext y
  constructor
  · rintro ⟨ρ, hmem⟩
    rcases List.mem_append.mp hmem with hΓ | hNueva
    · exact Or.inl ⟨ρ, hΓ⟩
    · have hIgual : (y, ρ) = (x, σ) := List.mem_singleton.mp hNueva
      exact Or.inr (congrArg Prod.fst hIgual)
  · rintro (⟨ρ, hΓ⟩ | hyx)
    · exact ⟨ρ, List.mem_append.mpr (Or.inl hΓ)⟩
    · have hyx' : y = x := hyx
      exact ⟨σ, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr (by rw [hyx'])))⟩

/-! ### Reglas de derivación de λ→ -/

/-- Juicio `Γ ⊢ M : σ` de λ→, con las tres reglas de la tesis.

* (variable): `Γ ⊢ x : σ` si `x : σ ∈ Γ` (y `Γ` es un contexto, es decir, sus
  sujetos son distintos).
* (aplicación): de `Γ ⊢ M : σ → τ` y `Γ ⊢ N : σ` se obtiene `Γ ⊢ M N : τ`.
* (abstracción): de `Γ, x : σ ⊢ M : τ` se obtiene `Γ ⊢ λx:σ. M : σ → τ`. -/
inductive Deriva : Contexto → Termino → Tipo → Prop
  | var {Γ : Contexto} {x : Variable} {σ : Tipo} :
      BienFormado Γ → (x, σ) ∈ Γ → Deriva Γ (.var x) σ
  | apl {Γ : Contexto} {M N : Termino} {σ τ : Tipo} :
      Deriva Γ M (σ ⟶ τ) → Deriva Γ N σ → Deriva Γ (.app M N) τ
  | abst {Γ : Contexto} {x : Variable} {σ τ : Tipo} {M : Termino} :
      Deriva (extender Γ x σ) M τ → Deriva Γ (.abs x σ M) (σ ⟶ τ)

/-- Notación `Γ ⊢ M : σ` para el juicio de tipado. -/
notation:50 Γ " ⊢ " M " : " σ => Deriva Γ M σ

/-- Un contexto bien formado sigue siéndolo al quitar su última declaración. -/
theorem bienFormado_de_extender {Γ : Contexto} {x : Variable} {σ : Tipo}
    (h : BienFormado (extender Γ x σ)) : BienFormado Γ := by
  unfold BienFormado extender at h
  rw [List.map_append] at h
  exact (List.nodup_append.mp h).1

/-- Todo juicio derivable tiene como contexto una lista con sujetos distintos:
la codificación respeta la Definición 7.51 de la tesis. -/
theorem Deriva.bienFormado {Γ : Contexto} {M : Termino} {σ : Tipo}
    (d : Γ ⊢ M : σ) : BienFormado Γ := by
  induction d with
  | var hBien _ => exact hBien
  | apl _ _ hipIndM _ => exact hipIndM
  | abst _ hipInd => exact bienFormado_de_extender hipInd

/-! ### Ejemplo 7.52: la función «constante» -/

/-- Ejemplo 7.52 de la tesis (derivación simbólica de la función «constante»):
`⊢ λx:σ. λy:τ. x : σ → (τ → σ)`. -/
theorem ejemplo_constante (σ τ : Tipo) :
    [] ⊢ .abs "x" σ (.abs "y" τ (.var "x")) : σ ⟶ (τ ⟶ σ) := by
  -- Contexto inicial x:σ, y:τ; sus sujetos son distintos.
  have hContexto : BienFormado [("x", σ), ("y", τ)] := by
    simp [BienFormado]
  -- Paso (1), regla (variable): x:σ, y:τ ⊢ x : σ, pues (x:σ) está en el contexto.
  have paso1 : [("x", σ), ("y", τ)] ⊢ .var "x" : σ :=
    Deriva.var hContexto (List.mem_cons_self)
  -- Paso (2), regla (abstracción) sobre (1): x:σ ⊢ λy:τ. x : τ → σ.
  have paso2 : [("x", σ)] ⊢ .abs "y" τ (.var "x") : τ ⟶ σ :=
    Deriva.abst (Γ := [("x", σ)]) paso1
  -- Paso (3), regla (abstracción) sobre (2): ⊢ λx:σ. λy:τ. x : σ → (τ → σ).
  exact Deriva.abst (Γ := []) paso2

/-! ### Ejemplo 7.53 -/

/-- Ejemplo 7.53 de la tesis:
`⊢ λy:α→β. λz:α. y z : (α → β) → (α → β)`. -/
theorem ejemplo_aplicacion (α β : Tipo) :
    [] ⊢ .abs "y" (α ⟶ β) (.abs "z" α (.app (.var "y") (.var "z"))) :
      (α ⟶ β) ⟶ (α ⟶ β) := by
  -- Contexto Γ₁ = y:α→β, z:α; sus sujetos son distintos.
  have hContexto : BienFormado [("y", α ⟶ β), ("z", α)] := by
    simp [BienFormado]
  -- Paso (1), regla (variable): Γ₁ ⊢ y : α → β.
  have paso1 : [("y", α ⟶ β), ("z", α)] ⊢ .var "y" : α ⟶ β :=
    Deriva.var hContexto (List.mem_cons_self)
  -- Paso (2), regla (variable): Γ₁ ⊢ z : α.
  have paso2 : [("y", α ⟶ β), ("z", α)] ⊢ .var "z" : α :=
    Deriva.var hContexto (List.mem_cons_of_mem _ List.mem_cons_self)
  -- Paso (3), regla (aplicación) sobre (1) y (2): Γ₁ ⊢ y z : β.
  have paso3 : [("y", α ⟶ β), ("z", α)] ⊢ .app (.var "y") (.var "z") : β :=
    Deriva.apl paso1 paso2
  -- Paso (4), regla (abstracción) sobre (3): y:α→β ⊢ λz:α. y z : α → β.
  have paso4 : [("y", α ⟶ β)] ⊢ .abs "z" α (.app (.var "y") (.var "z")) : α ⟶ β :=
    Deriva.abst (Γ := [("y", α ⟶ β)]) paso3
  -- Paso (5), regla (abstracción) sobre (4): contexto vacío y tipo final.
  exact Deriva.abst (Γ := []) paso4

/-! ### Lema 7.57: variables libres -/

/-- Lema 7.57 de la tesis (Variables libres): si `Γ ⊢ L : σ`, entonces
`FV(L) ⊆ dom(Γ)`. -/
theorem variables_libres {Γ : Contexto} {L : Termino} {σ : Tipo}
    (d : Γ ⊢ L : σ) : variablesLibres L ⊆ dominio Γ := by
  -- A probar: FV(L) ⊆ dom(Γ). Por inducción sobre la derivación de Γ ⊢ L : σ.
  induction d with
  | @var Γ x σ _ hmem =>
      -- Caso (variable): L ≡ x y la regla exige (x:σ) ∈ Γ.
      -- Por definición de dominio, x ∈ dom(Γ).
      have hDominio : x ∈ dominio Γ := ⟨σ, hmem⟩
      -- FV(x) = {x}.
      have hFV : variablesLibres (.var x) = {x} := rfl
      rw [hFV]
      exact Set.singleton_subset_iff.mpr hDominio
  | @apl Γ M N σ τ _ _ hipIndM hipIndN =>
      -- Caso (aplicación): L ≡ M N, con premisas Γ ⊢ M : σ → τ y Γ ⊢ N : σ.
      -- Hipótesis inductivas: FV(M) ⊆ dom(Γ) y FV(N) ⊆ dom(Γ).
      -- FV(M N) = FV(M) ∪ FV(N) ⊆ dom(Γ) ∪ dom(Γ) = dom(Γ).
      have hFV : variablesLibres (.app M N) = variablesLibres M ∪ variablesLibres N := rfl
      rw [hFV]
      exact Set.union_subset hipIndM hipIndN
  | @abst Γ x σ τ M _ hipInd =>
      -- Caso (abstracción): L ≡ λx:σ. M, con premisa Γ, x:σ ⊢ M : τ.
      -- Hipótesis inductiva: FV(M) ⊆ dom(Γ, x:σ) = dom(Γ) ∪ {x}.
      have hCuerpo : variablesLibres M ⊆ dominio Γ ∪ {x} := by
        rw [← dominio_extender Γ x σ]
        exact hipInd
      -- FV(λx:σ. M) = FV(M) \ {x} ⊆ (dom(Γ) ∪ {x}) \ {x} ⊆ dom(Γ).
      have hFV : variablesLibres (.abs x σ M) = variablesLibres M \ {x} := rfl
      rw [hFV]
      intro y hy
      have hyCuerpo : y ∈ dominio Γ ∪ {x} := hCuerpo hy.1
      rcases hyCuerpo with hyDominio | hyx
      · exact hyDominio
      · exact absurd hyx hy.2

end Thesis.Teoria.TiposSimples

#print axioms Thesis.Teoria.TiposSimples.ejemplo_constante
#print axioms Thesis.Teoria.TiposSimples.ejemplo_aplicacion
#print axioms Thesis.Teoria.TiposSimples.variables_libres
#print axioms Thesis.Teoria.TiposSimples.Deriva.bienFormado
