import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Lema de Sustitución (Lema 7.23 de la tesis)

Para λ-términos `M`, `N`, `L` y variables `x ≢ y` con `x ∉ FV(L)`:

  `M[x := N][y := L] ≡ M[y := L][x := N[y := L]]`.

## Representación elegida

Se usan **variables con nombre**, como en la tesis. En la tesis, `≡` identifica
términos α-equivalentes y la cláusula (3) de la Definición 7.20 renombra la
variable ligada. La demostración en papel comienza el caso de la abstracción con
«se puede renombrar `z` para que `z ≢ x`, `z ≢ y` y `z ∉ FV(N) ∪ FV(L)`»: es la
convención de variables de Barendregt.

Aquí esa convención se vuelve una **hipótesis explícita** (`ConvencionVariables`):
toda variable ligada de `M` es distinta de `x` y de `y` y no es libre en `N` ni en
`L`. Bajo esa hipótesis ningún renombramiento es necesario, la sustitución coincide
con la cláusula sin renombramiento de la nota que sigue a la Definición 7.20,

  `(λ z . P)[x := N] ≡ λ z . (P[x := N])`  si `z ≢ x` y `z ∉ FV(N)`,
  `(λ x . P)[x := N] ≡ λ x . P`,

y `≡` se formaliza como la **igualdad sintáctica literal** de Lean (`=`).
No se formaliza la α-equivalencia ni el cociente por ella.
-/

namespace Thesis.Teoria.Sustitucion

/-- λ-términos con variables con nombre: variable, aplicación y abstracción. -/
inductive Termino : Type
  | var (nombre : String) : Termino
  | app (funcion argumento : Termino) : Termino
  | lam (ligada : String) (cuerpo : Termino) : Termino
  deriving DecidableEq, Repr

open Termino

/-- Variables libres `FV(M)`. -/
def libres : Termino → Finset String
  | var z => {z}
  | app P Q => libres P ∪ libres Q
  | lam z P => (libres P).erase z

/-- Variables de enlace (ligadas) de `M`: las `z` de cada `λ z` que aparece en `M`. -/
def ligadas : Termino → Finset String
  | var _ => ∅
  | app P Q => ligadas P ∪ ligadas Q
  | lam z P => insert z (ligadas P)

/-- Sustitución `M[x := N]` sin renombramiento (Definición 7.20 de la tesis, con la
cláusula (3) en la forma de la nota posterior: si `z ≢ x` se sustituye bajo el
ligador sin renombrar; si `z ≡ x` la sustitución no actúa). Coincide con la
sustitución de la tesis cuando ninguna variable ligada de `M` es libre en `N`. -/
def sust (M : Termino) (x : String) (N : Termino) : Termino :=
  match M with
  | var z => if z = x then N else var z
  | app P Q => app (sust P x N) (sust Q x N)
  | lam z P => if z = x then lam z P else lam z (sust P x N)

@[inherit_doc] notation:max M "⟦" x " := " N "⟧" => sust M x N

/-- Cláusula (1a): `x[x := N] ≡ N`. -/
theorem sust_var_igual (x : String) (N : Termino) : (var x)⟦x := N⟧ = N := by
  simp [sust]

/-- Cláusula (1b): `z[x := N] ≡ z` si `z ≢ x`. -/
theorem sust_var_distinta {z x : String} (h : z ≠ x) (N : Termino) :
    (var z)⟦x := N⟧ = var z := by
  simp [sust, h]

/-- Cláusula (2): la sustitución se distribuye en la aplicación. -/
theorem sust_app (P Q : Termino) (x : String) (N : Termino) :
    (app P Q)⟦x := N⟧ = app (P⟦x := N⟧) (Q⟦x := N⟧) := by
  simp [sust]

/-- Cláusula (3) sin renombramiento: `(λ z . P)[x := N] ≡ λ z . (P[x := N])` si `z ≢ x`. -/
theorem sust_abs_distinta {z x : String} (h : z ≠ x) (P N : Termino) :
    (lam z P)⟦x := N⟧ = lam z (P⟦x := N⟧) := by
  simp [sust, h]

/-- Cláusula (3) cuando la variable ligada es la sustituida: `(λ x . P)[x := N] ≡ λ x . P`. -/
theorem sust_abs_igual (x : String) (P N : Termino) :
    (lam x P)⟦x := N⟧ = lam x P := by
  simp [sust]

/-- Si `x ∉ FV(L)`, entonces `L[x := N] ≡ L`. Es el hecho que la tesis usa en el
subcaso `z ≡ y` del caso base del Lema 7.23. -/
theorem sust_no_libre {x : String} (N : Termino) :
    ∀ {L : Termino}, x ∉ libres L → L⟦x := N⟧ = L := by
  -- Inducción sobre la estructura de L.
  intro L
  induction L with
  | var z =>
      intro hx
      have hzx : z ≠ x := by
        intro h
        exact hx (by simp [libres, h])
      exact sust_var_distinta hzx N
  | app P Q hipP hipQ =>
      intro hx
      have hxP : x ∉ libres P := fun h => hx (by simp [libres, h])
      have hxQ : x ∉ libres Q := fun h => hx (by simp [libres, h])
      rw [sust_app, hipP hxP, hipQ hxQ]
  | lam z P hipP =>
      intro hx
      by_cases hzx : z = x
      · -- La variable ligada es x: la sustitución no actúa.
        subst hzx
        exact sust_abs_igual z P N
      · -- z ≢ x: como x ∉ FV(λ z . P), se tiene x ∉ FV(P).
        have hxP : x ∉ libres P := by
          intro h
          exact hx (by simp [libres, h, Ne.symm hzx])
        rw [sust_abs_distinta hzx, hipP hxP]

/-- Convención de variables (Barendregt) que invoca la demostración del Lema 7.23:
toda variable ligada `z` de `M` cumple `z ≢ x`, `z ≢ y` y `z ∉ FV(N) ∪ FV(L)`.
En la tesis esto se consigue renombrando las variables ligadas de `M` (α-conversión);
aquí es una hipótesis sobre el representante `M`. -/
def ConvencionVariables (M N L : Termino) (x y : String) : Prop :=
  ∀ z ∈ ligadas M, z ≠ x ∧ z ≠ y ∧ z ∉ libres N ∧ z ∉ libres L

/-- **Lema 7.23 de la tesis (Lema de Sustitución).** Si `x ≢ y`, `x ∉ FV(L)` y el
representante `M` cumple la convención de variables, entonces

  `M[x := N][y := L] = M[y := L][x := N[y := L]]`

como igualdad sintáctica literal. -/
theorem lema_sustitucion (M N L : Termino) {x y : String}
    (hxy : x ≠ y) (hxL : x ∉ libres L)
    (hConv : ConvencionVariables M N L x y) :
    M⟦x := N⟧⟦y := L⟧ = M⟦y := L⟧⟦x := N⟦y := L⟧⟧ := by
  -- Se procede por inducción sobre la estructura de M.
  induction M with
  | var z =>
      -- Caso base: M ≡ z (variable). Tres subcasos según z.
      by_cases hzx : z = x
      · -- Subcaso z ≡ x: ambos lados son N[y := L].
        subst hzx
        -- Lado izquierdo: x[x := N][y := L] ≡ N[y := L].
        have hIzq : (var z)⟦z := N⟧⟦y := L⟧ = N⟦y := L⟧ := by
          rw [sust_var_igual]
        -- Lado derecho: x[y := L] ≡ x (pues x ≢ y) y x[x := N[y := L]] ≡ N[y := L].
        have hDer : (var z)⟦y := L⟧⟦z := N⟦y := L⟧⟧ = N⟦y := L⟧ := by
          rw [sust_var_distinta hxy, sust_var_igual]
        rw [hIzq, hDer]
      · by_cases hzy : z = y
        · -- Subcaso z ≡ y: ambos lados son L.
          subst hzy
          -- Lado izquierdo: y[x := N][y := L] ≡ y[y := L] ≡ L.
          have hIzq : (var z)⟦x := N⟧⟦z := L⟧ = L := by
            rw [sust_var_distinta hzx, sust_var_igual]
          -- Lado derecho: y[y := L][x := N[y := L]] ≡ L[x := N[y := L]] ≡ L (pues x ∉ FV(L)).
          have hDer : (var z)⟦z := L⟧⟦x := N⟦z := L⟧⟧ = L := by
            rw [sust_var_igual, sust_no_libre _ hxL]
          rw [hIzq, hDer]
        · -- Subcaso z ≢ x y z ≢ y: ambos lados son z.
          have hIzq : (var z)⟦x := N⟧⟦y := L⟧ = var z := by
            rw [sust_var_distinta hzx, sust_var_distinta hzy]
          have hDer : (var z)⟦y := L⟧⟦x := N⟦y := L⟧⟧ = var z := by
            rw [sust_var_distinta hzy, sust_var_distinta hzx]
          rw [hIzq, hDer]
  | app P Q hipP hipQ =>
      -- Caso inductivo: M ≡ P Q (aplicación).
      -- La convención de variables se hereda a los subtérminos P y Q.
      have hConvP : ConvencionVariables P N L x y := fun z hz =>
        hConv z (by simp [ligadas, hz])
      have hConvQ : ConvencionVariables Q N L x y := fun z hz =>
        hConv z (by simp [ligadas, hz])
      -- Definición de sustitución en la aplicación, hipótesis inductivas en P y Q,
      -- y de nuevo la definición (dos veces) en sentido inverso.
      calc (app P Q)⟦x := N⟧⟦y := L⟧
          = app (P⟦x := N⟧⟦y := L⟧) (Q⟦x := N⟧⟦y := L⟧) := by
            rw [sust_app, sust_app]
        _ = app (P⟦y := L⟧⟦x := N⟦y := L⟧⟧) (Q⟦y := L⟧⟦x := N⟦y := L⟧⟧) := by
            rw [hipP hConvP, hipQ hConvQ]
        _ = (app (P⟦y := L⟧) (Q⟦y := L⟧))⟦x := N⟦y := L⟧⟧ := by
            rw [sust_app]
        _ = (app P Q)⟦y := L⟧⟦x := N⟦y := L⟧⟧ := by
            rw [sust_app P Q y L]
  | lam z P hipP =>
      -- Caso inductivo: M ≡ λ z . P (abstracción).
      -- «Se puede renombrar z para que z ≢ x, z ≢ y y z ∉ FV(N) ∪ FV(L)»:
      -- aquí lo garantiza la convención de variables.
      obtain ⟨hzx, hzy, _hzN, _hzL⟩ := hConv z (by simp [ligadas])
      have hConvP : ConvencionVariables P N L x y := fun w hw =>
        hConv w (by simp [ligadas, hw])
      calc (lam z P)⟦x := N⟧⟦y := L⟧
          = lam z (P⟦x := N⟧⟦y := L⟧) := by
            -- (Sustitución)
            rw [sust_abs_distinta hzx, sust_abs_distinta hzy]
        _ = lam z (P⟦y := L⟧⟦x := N⟦y := L⟧⟧) := by
            -- (Por hipótesis inductiva en P)
            rw [hipP hConvP]
        _ = (lam z P)⟦y := L⟧⟦x := N⟦y := L⟧⟧ := by
            -- (Sustitución)
            rw [sust_abs_distinta hzy, sust_abs_distinta hzx]

/-- Observación sobre el Lema 7.23 de la tesis: para la igualdad literal con la
sustitución sin renombramiento basta que `y` no sea variable de enlace de `M`.
Las condiciones restantes de la convención (`z ≢ x`, `z ∉ FV(N) ∪ FV(L)`) no se
usan en el cálculo; sirven para que la sustitución sin renombramiento coincida
con la sustitución que evita capturas de la Definición 7.20. -/
theorem lema_sustitucion_hipotesis_minima (M N L : Termino) {x y : String}
    (hxy : x ≠ y) (hxL : x ∉ libres L) (hy : y ∉ ligadas M) :
    M⟦x := N⟧⟦y := L⟧ = M⟦y := L⟧⟦x := N⟦y := L⟧⟧ := by
  induction M with
  | var z =>
      -- Los mismos tres subcasos del caso base.
      by_cases hzx : z = x
      · subst hzx
        rw [sust_var_igual, sust_var_distinta hxy, sust_var_igual]
      · by_cases hzy : z = y
        · subst hzy
          rw [sust_var_distinta hzx, sust_var_igual, sust_no_libre _ hxL]
        · rw [sust_var_distinta hzx, sust_var_distinta hzy, sust_var_distinta hzx]
  | app P Q hipP hipQ =>
      have hyP : y ∉ ligadas P := fun h => hy (by simp [ligadas, h])
      have hyQ : y ∉ ligadas Q := fun h => hy (by simp [ligadas, h])
      rw [sust_app, sust_app, sust_app, sust_app, hipP hyP, hipQ hyQ]
  | lam z P hipP =>
      have hzy : z ≠ y := fun h => hy (by simp [ligadas, h])
      have hyP : y ∉ ligadas P := fun h => hy (by simp [ligadas, h])
      by_cases hzx : z = x
      · -- La variable ligada es x: ninguna sustitución de x actúa.
        subst hzx
        rw [sust_abs_igual, sust_abs_distinta hzy, sust_abs_igual]
      · rw [sust_abs_distinta hzx, sust_abs_distinta hzy, sust_abs_distinta hzy,
          sust_abs_distinta hzx, hipP hyP]

/-- La hipótesis sobre las variables ligadas no puede eliminarse para la igualdad
literal: con `M ≡ λ y . x`, `N ≡ y`, `L ≡ z` los dos lados difieren (sin renombrar,
`N` queda capturado). En la tesis este caso se resuelve renombrando la `y` ligada. -/
example :
    (lam "y" (var "x"))⟦"x" := var "y"⟧⟦"y" := var "z"⟧
      ≠ (lam "y" (var "x"))⟦"y" := var "z"⟧⟦"x" := (var "y")⟦"y" := var "z"⟧⟧ := by
  decide

#print axioms lema_sustitucion
#print axioms lema_sustitucion_hipotesis_minima

end Thesis.Teoria.Sustitucion
