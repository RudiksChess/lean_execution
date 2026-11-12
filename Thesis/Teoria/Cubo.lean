/-!
# Sistemas del cubo-λ: derivaciones formales del capítulo 8

Se codifican como predicados inductivos de derivabilidad los dos sistemas que la tesis
presenta en el capítulo 8 y se reconstruyen, regla por regla, las derivaciones en papel:

* `Lambda2`: el sistema λ2 (tipos Π sobre variables de tipo) y el Ejemplo 8.5 de la tesis
  (identidad polimórfica).
* `LambdaOmega`: el sistema λω̲ con los sorts ∗ y □ y las reglas (sort), (variable),
  (debilitamiento), (formación), (aplicación), (abstracción) y (conversión); Ejemplos 8.13,
  8.15 y 8.20 de la tesis (derivación completa y derivación abreviada).

Cada paso numerado de la tesis es un lema con el juicio de esa línea y cita la regla usada.
No se usa búsqueda automática de derivaciones: `simp` y `decide` solo descargan las
condiciones laterales decidibles (`x ∉ Γ`, pertenencia de una declaración al contexto).

## Decisiones de codificación (diferencias con el texto)

* Las variables son cadenas (`String`); variables de término y de tipo comparten el mismo
  conjunto de nombres, como en λω̲ de la tesis.
* Un contexto es una lista que crece por la derecha: `Γ ,, x ∶ A` es «Γ, x : A».
* En λω̲ la condición «x ∉ Γ» se lee como «x no es sujeto de ninguna declaración de Γ»
  (`x ∉ Γ.dominio`).
* En λ2 la tesis no da una regla que construya contextos; dice (Nota previa a las reglas) que
  los sujetos son distintos y que toda variable de tipo se declara antes de usarse. Esa
  condición se codifica como `Contexto.Valido` y se pide como premisa de la regla (variable),
  que es la única regla sin premisas de derivación.
* La sustitución (`Tipo.sust`, `Expr.sust`) es la ingenua, sin renombrar variables ligadas.
  Para que sea correcta, las reglas que sustituyen ((aplicación₂) en λ2 y el paso β de λω̲)
  llevan la condición lateral explícita de que ninguna variable ligada del cuerpo ocurra
  libre en el argumento. No se identifica módulo α-equivalencia.
* `=β` es la clausura reflexiva, simétrica, transitiva y compatible del paso β.
-/

namespace Thesis.Teoria.Cubo

/-- Nombres de variables (de término y de tipo). -/
abbrev Variable := String

/-! ## Sistema λ2 -/

namespace Lambda2

/-- Tipos de λ2: 𝕋2 = 𝕍 | (𝕋2 → 𝕋2) | (Π 𝕍 : ∗ . 𝕋2). -/
inductive Tipo : Type
  | var : Variable → Tipo
  | flecha : Tipo → Tipo → Tipo
  | pi : Variable → Tipo → Tipo
  deriving DecidableEq

/-- Términos pre-tipados de λ2: variable, aplicación a término, aplicación a tipo,
abstracción de término `λ x : A . M` y abstracción de tipo `Λ α : ∗ . M`. -/
inductive Termino : Type
  | var : Variable → Termino
  | apl : Termino → Termino → Termino
  | aplTipo : Termino → Tipo → Termino
  | abs : Variable → Tipo → Termino → Termino
  | absTipo : Variable → Termino → Termino
  deriving DecidableEq

/-- Declaraciones de un contexto de λ2: `x : A` o `α : ∗`. -/
inductive Declaracion : Type
  | termino : Variable → Tipo → Declaracion
  | tipo : Variable → Declaracion
  deriving DecidableEq

/-- Sujeto de una declaración. -/
def Declaracion.sujeto : Declaracion → Variable
  | .termino x _ => x
  | .tipo α => α

/-- Variables de tipo libres de un tipo. -/
def Tipo.libres : Tipo → List Variable
  | .var α => [α]
  | .flecha A B => A.libres ++ B.libres
  | .pi α A => A.libres.filter (· ≠ α)

/-- Variables ligadas (por Π) de un tipo. -/
def Tipo.ligadas : Tipo → List Variable
  | .var _ => []
  | .flecha A B => A.ligadas ++ B.ligadas
  | .pi α A => α :: A.ligadas

/-- Sustitución ingenua `A[α := B]` (no renombra variables ligadas). -/
def Tipo.sust : Tipo → Variable → Tipo → Tipo
  | .var β, α, B => if β = α then B else .var β
  | .flecha A₁ A₂, α, B => .flecha (A₁.sust α B) (A₂.sust α B)
  | .pi β A, α, B => if β = α then .pi β A else .pi β (A.sust α B)

/-- Contextos de λ2: lista de declaraciones que crece por la derecha. -/
inductive Contexto : Type
  | vacio : Contexto
  | ext : Contexto → Declaracion → Contexto

/-- Lista de declaraciones de un contexto (la más reciente primero). -/
def Contexto.lista : Contexto → List Declaracion
  | .vacio => []
  | .ext Γ d => d :: Γ.lista

/-- Sujetos declarados en un contexto. -/
def Contexto.sujetos (Γ : Contexto) : List Variable := Γ.lista.map Declaracion.sujeto

/-- `Γ ⊢ B : ∗` por la regla (formación) de λ2: todas las variables de tipo libres de `B`
están declaradas en `Γ`. -/
def Formado (Γ : Contexto) (B : Tipo) : Prop :=
  ∀ α ∈ B.libres, Declaracion.tipo α ∈ Γ.lista

/-- Contexto válido de λ2: sujetos distintos y toda variable de tipo declarada antes de su
primer uso (Nota previa a las reglas de λ2 en la tesis). -/
def Contexto.Valido : Contexto → Prop
  | .vacio => True
  | .ext Γ (.tipo α) => Γ.Valido ∧ α ∉ Γ.sujetos
  | .ext Γ (.termino x A) => Γ.Valido ∧ x ∉ Γ.sujetos ∧ Formado Γ A

/-- Juicios `Γ ⊢ M : A` de λ2. Reglas (variable), (aplicación) y (abstracción) de λ→ y las
reglas (abstracción₂) y (aplicación₂) de la tesis; la segunda premisa de (aplicación₂) es la
regla (formación), `Formado`. -/
inductive Deriva : Contexto → Termino → Tipo → Prop
  /-- (variable): `Γ ⊢ x : A` si `x : A ∈ Γ` (con `Γ` un contexto de λ2). -/
  | variable {Γ : Contexto} {x : Variable} {A : Tipo} :
      Γ.Valido → Declaracion.termino x A ∈ Γ.lista → Deriva Γ (.var x) A
  /-- (aplicación): de `Γ ⊢ M : A → B` y `Γ ⊢ N : A` se obtiene `Γ ⊢ M N : B`. -/
  | aplicacion {Γ : Contexto} {M N : Termino} {A B : Tipo} :
      Deriva Γ M (.flecha A B) → Deriva Γ N A → Deriva Γ (.apl M N) B
  /-- (abstracción): de `Γ, x : A ⊢ M : B` se obtiene `Γ ⊢ λ x : A . M : A → B`. -/
  | abstraccion {Γ : Contexto} {x : Variable} {M : Termino} {A B : Tipo} :
      Deriva (Γ.ext (.termino x A)) M B → Deriva Γ (.abs x A M) (.flecha A B)
  /-- (abstracción₂): de `Γ, α : ∗ ⊢ M : A` se obtiene `Γ ⊢ Λ α : ∗ . M : Π α : ∗ . A`. -/
  | abstraccion2 {Γ : Contexto} {α : Variable} {M : Termino} {A : Tipo} :
      Deriva (Γ.ext (.tipo α)) M A → Deriva Γ (.absTipo α M) (.pi α A)
  /-- (aplicación₂): de `Γ ⊢ M : Π α : ∗ . A` y `Γ ⊢ B : ∗` se obtiene `Γ ⊢ M B : A[α := B]`.
  Condición lateral añadida: la sustitución ingenua no captura variables de `B`. -/
  | aplicacion2 {Γ : Contexto} {α : Variable} {M : Termino} {A B : Tipo} :
      Deriva Γ M (.pi α A) → Formado Γ B → (∀ β ∈ A.ligadas, β ∉ B.libres) →
      Deriva Γ (.aplTipo M B) (A.sust α B)

/-! ### Ejemplo 8.5 de la tesis: la identidad polimórfica -/

/-- El contexto `α : ∗`. -/
abbrev ctxAlfa : Contexto := Contexto.vacio.ext (.tipo "α")

/-- El contexto `Γ₁ = α : ∗, x : α`. -/
abbrev ctxAlfaX : Contexto := ctxAlfa.ext (.termino "x" (.var "α"))

/-- `Γ₁ = α : ∗, x : α` es un contexto válido de λ2. -/
theorem ctxAlfaX_valido : ctxAlfaX.Valido := by
  -- Sujetos distintos y `α` declarada antes de usarse en `x : α`.
  simp [Contexto.Valido, Contexto.sujetos, Contexto.lista, Declaracion.sujeto, Formado,
    Tipo.libres]

/-- Ejemplo 8.5 de la tesis, paso (1): `α : ∗, x : α ⊢ x : α`, por (variable). -/
theorem identidad_paso1 : Deriva ctxAlfaX (.var "x") (.var "α") := by
  -- Paso (1): (variable), pues `x : α` es miembro de Γ₁.
  have hMiembro : Declaracion.termino "x" (.var "α") ∈ ctxAlfaX.lista := by
    simp [Contexto.lista]
  exact Deriva.variable ctxAlfaX_valido hMiembro

/-- Ejemplo 8.5 de la tesis, paso (2): `α : ∗ ⊢ λ x : α . x : α → α`, por (abstracción). -/
theorem identidad_paso2 :
    Deriva ctxAlfa (.abs "x" (.var "α") (.var "x")) (.flecha (.var "α") (.var "α")) := by
  -- Paso (2): (abstracción) con el juicio (1) como premisa.
  exact Deriva.abstraccion identidad_paso1

/-- Ejemplo 8.5 de la tesis, paso (3) y juicio final:
`⊢ Λ α : ∗ . λ x : α . x : Π α : ∗ . α → α`, por (abstracción₂). -/
theorem identidad_polimorfica :
    Deriva Contexto.vacio
      (.absTipo "α" (.abs "x" (.var "α") (.var "x")))
      (.pi "α" (.flecha (.var "α") (.var "α"))) := by
  -- Paso (3): (abstracción₂) con el juicio (2) como premisa.
  exact Deriva.abstraccion2 identidad_paso2

end Lambda2

/-! ## Sistema λω̲ -/

namespace LambdaOmega

/-- Los sorts de λω̲: `∗` y `□`. -/
inductive Clase : Type
  | estrella : Clase
  | caja : Clase
  deriving DecidableEq

/-- Pseudo-expresiones de λω̲: variables, sorts, aplicación, abstracción `λ x : A . M` y
flecha `A → B`. Términos, constructores y kinds comparten esta sintaxis. -/
inductive Expr : Type
  | var : Variable → Expr
  | sort : Clase → Expr
  | apl : Expr → Expr → Expr
  | abs : Variable → Expr → Expr → Expr
  | flecha : Expr → Expr → Expr
  deriving DecidableEq

/-- El sort `∗`. -/
scoped notation "★" => Expr.sort Clase.estrella
/-- El sort `□`. -/
scoped notation "□" => Expr.sort Clase.caja
/-- La flecha `A → B`. -/
scoped infixr:60 " ⇒ " => Expr.flecha

/-- Variables libres de una pseudo-expresión. -/
def Expr.libres : Expr → List Variable
  | .var x => [x]
  | .sort _ => []
  | .apl M N => M.libres ++ N.libres
  | .abs x A M => A.libres ++ M.libres.filter (· ≠ x)
  | .flecha A B => A.libres ++ B.libres

/-- Variables ligadas (por λ) de una pseudo-expresión. -/
def Expr.ligadas : Expr → List Variable
  | .var _ => []
  | .sort _ => []
  | .apl M N => M.ligadas ++ N.ligadas
  | .abs x A M => x :: (A.ligadas ++ M.ligadas)
  | .flecha A B => A.ligadas ++ B.ligadas

/-- Sustitución ingenua `M[x := N]` (no renombra variables ligadas). -/
def Expr.sust : Expr → Variable → Expr → Expr
  | .var y, x, N => if y = x then N else .var y
  | .sort s, _, _ => .sort s
  | .apl M₁ M₂, x, N => .apl (M₁.sust x N) (M₂.sust x N)
  | .abs y A M, x, N => .abs y (A.sust x N) (if y = x then M else M.sust x N)
  | .flecha A B, x, N => .flecha (A.sust x N) (B.sust x N)

/-- Paso de β-reducción, compatible con todos los constructores:
`(λ x : A . M) N →β M[x := N]`. Condición lateral explícita: ninguna variable ligada de `M`
ocurre libre en `N`, de modo que la sustitución ingenua no captura. -/
inductive PasoBeta : Expr → Expr → Prop
  | beta {x : Variable} {A M N : Expr} :
      (∀ y ∈ M.ligadas, y ∉ N.libres) → PasoBeta (.apl (.abs x A M) N) (M.sust x N)
  | aplIzq {M M' N : Expr} : PasoBeta M M' → PasoBeta (.apl M N) (.apl M' N)
  | aplDer {M N N' : Expr} : PasoBeta N N' → PasoBeta (.apl M N) (.apl M N')
  | absTipo {x : Variable} {A A' M : Expr} : PasoBeta A A' → PasoBeta (.abs x A M) (.abs x A' M)
  | absCuerpo {x : Variable} {A M M' : Expr} :
      PasoBeta M M' → PasoBeta (.abs x A M) (.abs x A M')
  | flechaIzq {A A' B : Expr} : PasoBeta A A' → PasoBeta (A ⇒ B) (A' ⇒ B)
  | flechaDer {A B B' : Expr} : PasoBeta B B' → PasoBeta (A ⇒ B) (A ⇒ B')

/-- β-conversión `B =β B'`: clausura reflexiva, simétrica y transitiva de `PasoBeta`. -/
inductive BetaEq : Expr → Expr → Prop
  | paso {B B' : Expr} : PasoBeta B B' → BetaEq B B'
  | refl (B : Expr) : BetaEq B B
  | simetria {B B' : Expr} : BetaEq B B' → BetaEq B' B
  | transitividad {B B' B'' : Expr} : BetaEq B B' → BetaEq B' B'' → BetaEq B B''

/-- Contextos de λω̲: lista de declaraciones `x : A` que crece por la derecha. -/
inductive Contexto : Type
  | vacio : Contexto
  | ext : Contexto → Variable → Expr → Contexto

/-- Extensión de contexto «Γ, x : A». -/
scoped notation:55 Γ:55 " ,, " x:max " ∶ " A:56 => Contexto.ext Γ x A

/-- Variables declaradas en un contexto; «x ∉ Γ» es `x ∉ Γ.dominio`. -/
def Contexto.dominio : Contexto → List Variable
  | .vacio => []
  | .ext Γ x _ => x :: Γ.dominio

/-- Juicios `Γ ⊢ A : B` de λω̲, con las siete reglas del resumen de la tesis. -/
inductive Deriva : Contexto → Expr → Expr → Prop
  /-- (sort): `∅ ⊢ ∗ : □`. -/
  | sort : Deriva .vacio ★ □
  /-- (variable): de `Γ ⊢ A : s` se obtiene `Γ, x : A ⊢ x : A`, si `x ∉ Γ`. -/
  | variable {Γ : Contexto} {A : Expr} {s : Clase} {x : Variable} :
      Deriva Γ A (.sort s) → x ∉ Γ.dominio → Deriva (Γ ,, x ∶ A) (.var x) A
  /-- (debilitamiento): de `Γ ⊢ A : B` y `Γ ⊢ C : s` se obtiene `Γ, x : C ⊢ A : B`,
  si `x ∉ Γ`. -/
  | debilitamiento {Γ : Contexto} {A B C : Expr} {s : Clase} {x : Variable} :
      Deriva Γ A B → Deriva Γ C (.sort s) → x ∉ Γ.dominio → Deriva (Γ ,, x ∶ C) A B
  /-- (formación): de `Γ ⊢ A : s` y `Γ ⊢ B : s` se obtiene `Γ ⊢ A → B : s`. -/
  | formacion {Γ : Contexto} {A B : Expr} {s : Clase} :
      Deriva Γ A (.sort s) → Deriva Γ B (.sort s) → Deriva Γ (A ⇒ B) (.sort s)
  /-- (aplicación): de `Γ ⊢ M : A → B` y `Γ ⊢ N : A` se obtiene `Γ ⊢ M N : B`. -/
  | aplicacion {Γ : Contexto} {M N A B : Expr} :
      Deriva Γ M (A ⇒ B) → Deriva Γ N A → Deriva Γ (.apl M N) B
  /-- (abstracción): de `Γ, x : A ⊢ M : B` y `Γ ⊢ A → B : s` se obtiene
  `Γ ⊢ λ x : A . M : A → B`. -/
  | abstraccion {Γ : Contexto} {x : Variable} {M A B : Expr} {s : Clase} :
      Deriva (Γ ,, x ∶ A) M B → Deriva Γ (A ⇒ B) (.sort s) → Deriva Γ (.abs x A M) (A ⇒ B)
  /-- (conversión): de `Γ ⊢ A : B` y `Γ ⊢ B' : s` se obtiene `Γ ⊢ A : B'`, si `B =β B'`. -/
  | conversion {Γ : Contexto} {A B B' : Expr} {s : Clase} :
      Deriva Γ A B → Deriva Γ B' (.sort s) → BetaEq B B' → Deriva Γ A B'

open Contexto (vacio)

/-- La variable de tipo `α`. -/
abbrev α : Expr := .var "α"
/-- La variable de tipo `β`. -/
abbrev β : Expr := .var "β"

/-! ### Ejemplo 8.13 de la tesis: `α : ∗, x : α ⊢ x : α` -/

/-- Ejemplo 8.13 de la tesis, paso 1: `∅ ⊢ ∗ : □`, por (sort). -/
theorem variable_paso1 : Deriva vacio ★ □ :=
  -- Paso 1: (sort).
  Deriva.sort

/-- Ejemplo 8.13 de la tesis, paso 2: `α : ∗ ⊢ α : ∗`, por (variable) en 1. -/
theorem variable_paso2 : Deriva (vacio ,, "α" ∶ ★) α ★ := by
  -- Condición lateral: α ∉ ∅.
  have hFresca : "α" ∉ vacio.dominio := by simp [Contexto.dominio]
  -- Paso 2: (variable) en el paso 1.
  exact Deriva.variable variable_paso1 hFresca

/-- Ejemplo 8.13 de la tesis, paso 3 y juicio final: `α : ∗, x : α ⊢ x : α`,
por (variable) en 2. -/
theorem variable_termino : Deriva (vacio ,, "α" ∶ ★ ,, "x" ∶ α) (.var "x") α := by
  -- Condición lateral: x ∉ (α : ∗).
  have hFresca : "x" ∉ (vacio ,, "α" ∶ ★).dominio := by simp [Contexto.dominio]
  -- Paso 3: (variable) en el paso 2.
  exact Deriva.variable variable_paso2 hFresca

/-! ### Ejemplo 8.15 de la tesis: cuatro juicios con (debilitamiento) -/

/-- Ejemplo 8.15 de la tesis, paso 1: `∅ ⊢ ∗ : □`, por (sort). -/
theorem debilitamiento_paso1 : Deriva vacio ★ □ :=
  -- Paso 1: (sort).
  Deriva.sort

/-- Ejemplo 8.15 de la tesis, paso 2: `α : ∗ ⊢ α : ∗`, por (variable) de 1. -/
theorem debilitamiento_paso2 : Deriva (vacio ,, "α" ∶ ★) α ★ := by
  have hFresca : "α" ∉ vacio.dominio := by simp [Contexto.dominio]
  -- Paso 2: (variable) de 1.
  exact Deriva.variable debilitamiento_paso1 hFresca

/-- Ejemplo 8.15 de la tesis, paso 3: `α : ∗ ⊢ ∗ : □`, por (debilitamiento) de 1, 1. -/
theorem debilitamiento_paso3 : Deriva (vacio ,, "α" ∶ ★) ★ □ := by
  have hFresca : "α" ∉ vacio.dominio := by simp [Contexto.dominio]
  -- Paso 3: (debilitamiento); se preserva el paso 1 y el paso 1 valida la suposición α : ∗.
  exact Deriva.debilitamiento debilitamiento_paso1 debilitamiento_paso1 hFresca

/-- Ejemplo 8.15 de la tesis, paso 4: `α : ∗, x : α ⊢ α : ∗`, por (debilitamiento) de 2, 2. -/
theorem debilitamiento_paso4 : Deriva (vacio ,, "α" ∶ ★ ,, "x" ∶ α) α ★ := by
  have hFresca : "x" ∉ (vacio ,, "α" ∶ ★).dominio := by simp [Contexto.dominio]
  -- Paso 4: (debilitamiento); se preserva el paso 2 y el paso 2 valida la suposición x : α.
  exact Deriva.debilitamiento debilitamiento_paso2 debilitamiento_paso2 hFresca

/-- Ejemplo 8.15 de la tesis, paso 5: `α : ∗, β : ∗ ⊢ α : ∗`, por (debilitamiento) de 2, 3. -/
theorem debilitamiento_paso5 : Deriva (vacio ,, "α" ∶ ★ ,, "β" ∶ ★) α ★ := by
  have hFresca : "β" ∉ (vacio ,, "α" ∶ ★).dominio := by simp [Contexto.dominio]
  -- Paso 5: (debilitamiento); se preserva el paso 2 y el paso 3 valida la suposición β : ∗.
  exact Deriva.debilitamiento debilitamiento_paso2 debilitamiento_paso3 hFresca

/-- Ejemplo 8.15 de la tesis, paso 6: `α : ∗, β : ∗ ⊢ β : ∗`, por (variable) de 3. -/
theorem debilitamiento_paso6 : Deriva (vacio ,, "α" ∶ ★ ,, "β" ∶ ★) β ★ := by
  have hFresca : "β" ∉ (vacio ,, "α" ∶ ★).dominio := by simp [Contexto.dominio]
  -- Paso 6: (variable) de 3.
  exact Deriva.variable debilitamiento_paso3 hFresca

/-- Ejemplo 8.15 (a) de la tesis: `α : ∗, x : α ⊢ α : ∗` (paso 4). -/
theorem debilitamiento_a : Deriva (vacio ,, "α" ∶ ★ ,, "x" ∶ α) α ★ :=
  debilitamiento_paso4

/-- Ejemplo 8.15 (b) de la tesis: `α : ∗, β : ∗ ⊢ α : ∗` (paso 5). -/
theorem debilitamiento_b : Deriva (vacio ,, "α" ∶ ★ ,, "β" ∶ ★) α ★ :=
  debilitamiento_paso5

/-- Ejemplo 8.15 (c) de la tesis: `α : ∗, β : ∗ ⊢ β : ∗` (paso 6). -/
theorem debilitamiento_c : Deriva (vacio ,, "α" ∶ ★ ,, "β" ∶ ★) β ★ :=
  debilitamiento_paso6

/-- Ejemplo 8.15 (d) de la tesis: `α : ∗ ⊢ ∗ : □` (paso 3). -/
theorem debilitamiento_d : Deriva (vacio ,, "α" ∶ ★) ★ □ :=
  debilitamiento_paso3

/-! ### Ejemplo 8.20 de la tesis: derivación formal completa -/

/-- El contexto `β : ∗` (bandera (a) del Ejemplo 8.20). -/
abbrev ctxBeta : Contexto := vacio ,, "β" ∶ ★

/-- El constructor `λ α : ∗ . α → α`. -/
abbrev constructorFlecha : Expr := .abs "α" ★ (α ⇒ α)

/-- Ejemplo 8.20 de la tesis, paso 1: `β : ∗ ⊢ ∗ : □`, por (debilitamiento) de (sort). -/
theorem completa_paso1 : Deriva ctxBeta ★ □ := by
  have hFresca : "β" ∉ vacio.dominio := by simp [Contexto.dominio]
  -- Paso 1: (debilitamiento); ambas premisas son ∅ ⊢ ∗ : □, de (sort).
  exact Deriva.debilitamiento Deriva.sort Deriva.sort hFresca

/-- Ejemplo 8.20 de la tesis, paso 2: `β : ∗, α : ∗ ⊢ α : ∗`, por (variable) de 1. -/
theorem completa_paso2 : Deriva (ctxBeta ,, "α" ∶ ★) α ★ := by
  -- Condición lateral: α ∉ (β : ∗), es decir, α y β son nombres distintos.
  have hFresca : "α" ∉ ctxBeta.dominio := by simp [Contexto.dominio]
  -- Paso 2: (variable) de 1.
  exact Deriva.variable completa_paso1 hFresca

/-- Ejemplo 8.20 de la tesis, paso 3: `β : ∗, α : ∗ ⊢ α → α : ∗`, por (formación) de 2, 2. -/
theorem completa_paso3 : Deriva (ctxBeta ,, "α" ∶ ★) (α ⇒ α) ★ :=
  -- Paso 3: (formación) de 2, 2.
  Deriva.formacion completa_paso2 completa_paso2

/-- Ejemplo 8.20 de la tesis, paso 4: `β : ∗ ⊢ ∗ → ∗ : □`, por (formación) de 1, 1. -/
theorem completa_paso4 : Deriva ctxBeta (★ ⇒ ★) □ :=
  -- Paso 4: (formación) de 1, 1.
  Deriva.formacion completa_paso1 completa_paso1

/-- Ejemplo 8.20 de la tesis, paso 5: `β : ∗ ⊢ λ α : ∗ . α → α : ∗ → ∗`,
por (abstracción) de 3, 4. -/
theorem completa_paso5 : Deriva ctxBeta constructorFlecha (★ ⇒ ★) :=
  -- Paso 5: (abstracción) de 3, 4.
  Deriva.abstraccion completa_paso3 completa_paso4

/-- Ejemplo 8.20 de la tesis, paso 6: `β : ∗ ⊢ β : ∗`, por (variable) de (sort). -/
theorem completa_paso6 : Deriva ctxBeta β ★ := by
  have hFresca : "β" ∉ vacio.dominio := by simp [Contexto.dominio]
  -- Paso 6: (variable) de (sort).
  exact Deriva.variable Deriva.sort hFresca

/-- Ejemplo 8.20 de la tesis, paso 7 y juicio final de la derivación completa:
`β : ∗ ⊢ (λ α : ∗ . α → α) β : ∗`, por (aplicación) de 5, 6. -/
theorem derivacion_completa : Deriva ctxBeta (.apl constructorFlecha β) ★ :=
  -- Paso 7: (aplicación) de 5, 6.
  Deriva.aplicacion completa_paso5 completa_paso6

/-! ### Ejemplo 8.20 de la tesis: derivación abreviada

La derivación abreviada tiene tres líneas. Cada una enuncia literalmente el mismo juicio que
una línea de la derivación completa (1 ↦ 3, 2 ↦ 5, 3 ↦ 7) y se obtiene con la misma regla;
las premisas que la versión abreviada deja implícitas —banderas (a), (b) y los pasos 1, 2, 4
y 6 omitidos— se toman de la derivación completa. Que «abreviada» y «completa» se
correspondan es una afirmación de metanivel sobre dos presentaciones; aquí se refleja en que
los enunciados coinciden como proposiciones de Lean (los tres `example` finales lo comprueban
por identidad de tipos) y en que el teorema final es el mismo. -/

/-- Ejemplo 8.20 de la tesis, paso 1 abreviado (= paso 3 completo):
`β : ∗, α : ∗ ⊢ α → α : ∗`, por (formación) de (b), (b). -/
theorem abreviada_paso1 : Deriva (ctxBeta ,, "α" ∶ ★) (α ⇒ α) ★ := by
  -- La bandera (b) `α : ∗`, leída como juicio, es el paso 2 omitido de la derivación completa.
  have hBanderaB : Deriva (ctxBeta ,, "α" ∶ ★) α ★ := completa_paso2
  -- Paso 1 abreviado: (formación) de (b), (b).
  exact Deriva.formacion hBanderaB hBanderaB

/-- Ejemplo 8.20 de la tesis, paso 2 abreviado (= paso 5 completo):
`β : ∗ ⊢ λ α : ∗ . α → α : ∗ → ∗`, por (abstracción) de 1. -/
theorem abreviada_paso2 : Deriva ctxBeta constructorFlecha (★ ⇒ ★) := by
  -- Segunda premisa de (abstracción), implícita en la versión abreviada: paso 4 omitido.
  have hKind : Deriva ctxBeta (★ ⇒ ★) □ := completa_paso4
  -- Paso 2 abreviado: (abstracción) de 1.
  exact Deriva.abstraccion abreviada_paso1 hKind

/-- Ejemplo 8.20 de la tesis, paso 3 abreviado (= paso 7 completo) y juicio final:
`β : ∗ ⊢ (λ α : ∗ . α → α) β : ∗`, por (aplicación) de 2 y (a). -/
theorem derivacion_abreviada : Deriva ctxBeta (.apl constructorFlecha β) ★ := by
  -- La bandera (a) `β : ∗`, leída como juicio, es el paso 6 omitido de la derivación completa.
  have hBanderaA : Deriva ctxBeta β ★ := completa_paso6
  -- Paso 3 abreviado: (aplicación) de 2 y (a).
  exact Deriva.aplicacion abreviada_paso2 hBanderaA

/-- Paso 1 abreviado y paso 3 completo enuncian el mismo juicio. -/
example : Deriva (ctxBeta ,, "α" ∶ ★) (α ⇒ α) ★ := (abreviada_paso1 : type_of% completa_paso3)
/-- Paso 2 abreviado y paso 5 completo enuncian el mismo juicio. -/
example : Deriva ctxBeta constructorFlecha (★ ⇒ ★) := (abreviada_paso2 : type_of% completa_paso5)
/-- Paso 3 abreviado y paso 7 completo enuncian el mismo juicio. -/
example : Deriva ctxBeta (.apl constructorFlecha β) ★ :=
  (derivacion_abreviada : type_of% derivacion_completa)

/-! ### Complemento: el ejemplo de la regla (conversión)

No forma parte de los cinco ejemplos pedidos; se incluye para ejercitar la regla (conversión),
la β-conversión y la sustitución, que las derivaciones anteriores no usan. -/

/-- `(λ α : ∗ . α → α) β =β β → β`, por un paso β. -/
theorem constructor_beta : BetaEq (.apl constructorFlecha β) (β ⇒ β) := by
  -- Condición lateral del paso β: `α → α` no tiene variables ligadas.
  have hSinCaptura : ∀ y ∈ (α ⇒ α).ligadas, y ∉ β.libres := by simp [Expr.ligadas]
  have hPaso : PasoBeta (.apl (.abs "α" ★ (α ⇒ α)) β) ((α ⇒ α).sust "α" β) :=
    PasoBeta.beta hSinCaptura
  -- `(α → α)[α := β]` es `β → β`.
  have hSust : (α ⇒ α).sust "α" β = (β ⇒ β) := by simp [Expr.sust]
  rw [hSust] at hPaso
  exact BetaEq.paso hPaso

/-- Ejemplo de la regla (conversión) de la tesis: con `Γ ≡ β : ∗, x : (λ α : ∗ . α → α) β`
se deriva `Γ ⊢ x : β → β`. -/
theorem conversion_ejemplo :
    Deriva (ctxBeta ,, "x" ∶ .apl constructorFlecha β) (.var "x") (β ⇒ β) := by
  have hFresca : "x" ∉ ctxBeta.dominio := by simp [Contexto.dominio]
  -- Línea 19: Γ ⊢ x : (λ α : ∗ . α → α) β, por (variable) sobre el Ejemplo 8.20.
  have hVariable : Deriva (ctxBeta ,, "x" ∶ .apl constructorFlecha β) (.var "x")
      (.apl constructorFlecha β) := Deriva.variable derivacion_completa hFresca
  -- Segunda premisa de (conversión): Γ ⊢ β → β : ∗, por (formación) y (debilitamiento).
  have hFlecha : Deriva ctxBeta (β ⇒ β) ★ := Deriva.formacion completa_paso6 completa_paso6
  have hBienFormado : Deriva (ctxBeta ,, "x" ∶ .apl constructorFlecha β) (β ⇒ β) ★ :=
    Deriva.debilitamiento hFlecha derivacion_completa hFresca
  -- Línea 20: (conversión), ya que (λ α : ∗ . α → α) β =β β → β.
  exact Deriva.conversion hVariable hBienFormado constructor_beta

end LambdaOmega

end Thesis.Teoria.Cubo

#print axioms Thesis.Teoria.Cubo.Lambda2.identidad_polimorfica
#print axioms Thesis.Teoria.Cubo.LambdaOmega.variable_termino
#print axioms Thesis.Teoria.Cubo.LambdaOmega.debilitamiento_a
#print axioms Thesis.Teoria.Cubo.LambdaOmega.debilitamiento_b
#print axioms Thesis.Teoria.Cubo.LambdaOmega.debilitamiento_c
#print axioms Thesis.Teoria.Cubo.LambdaOmega.debilitamiento_d
#print axioms Thesis.Teoria.Cubo.LambdaOmega.derivacion_completa
#print axioms Thesis.Teoria.Cubo.LambdaOmega.derivacion_abreviada
#print axioms Thesis.Teoria.Cubo.LambdaOmega.conversion_ejemplo
