import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Lema de Sustitución módulo α-equivalencia (Lema 7.23 de la tesis)

Para λ-términos `M`, `N`, `L` y variables `x ≢ y` con `x ∉ FV(L)`:

  `M[x := N][y := L] ≡α M[y := L][x := N[y := L]]`.

El archivo `Thesis/Teoria/Sustitucion.lean` demuestra esta ecuación como igualdad
literal, con una sustitución que no renombra y bajo una hipótesis adicional de
frescura (`ConvencionVariables`). Aquí se demuestra la **versión fiel a la tesis**:
sin hipótesis sobre las variables ligadas de `M`, con una sustitución que evita
capturas renombrando, y con la conclusión módulo α-equivalencia. Las únicas
hipótesis son `x ≠ y` y `x ∉ FV(L)`.

## Correspondencia con la tesis

* `Termino`, `libres`, `ligadas`: λ-términos con **variables con nombre**, `FV(M)`
  y las variables de enlace de `M`.
* `renombrar M x y`: el renombramiento `M^{x → y}` de la Definición 7.15 (cada
  ocurrencia libre de `x` se reemplaza por `y`, sin más precauciones).
* `fresca S`: una variable que no pertenece al conjunto finito `S` (una cadena más
  larga que todas las de `S`). Es la elección de la «variante α» de la cláusula (3).
* `sustitucion M x N`: la sustitución `M[x := N]` de la Definición 7.20, que evita
  capturas. En la abstracción `(λ z . P)[x := N]`:
  - si `z ≡ x`, el resultado es `λ z . P` (nota posterior a la definición);
  - si `z ≢ x` y no hay captura posible (`z ∉ FV(N)` o `x ∉ FV(P)`), el resultado es
    `λ z . P[x := N]` (nota posterior a la definición);
  - en otro caso se renombra `z` a una variable fresca `w` (que no aparece en `P`,
    `w ∉ FV(N)`, `w ≢ x`) y el resultado es `λ w . (P^{z → w})[x := N]` (cláusula (3)).
  La recursión se justifica por el tamaño del término: `renombrar` lo preserva.
* `AlfaEq` (`≡α`): la α-equivalencia de la Definición 7.16. Se define como la
  igualdad de las traducciones a una representación sin nombres para las variables
  ligadas (`aDeBruijn`); es una relación de equivalencia (`alfaEq_equivalencia`),
  valida la regla de renombramiento de la tesis (`alfa_renombre`) y las reglas de
  compatibilidad (`alfa_app`, `alfa_lam`). Coincide exactamente con la relación
  `AlfaTesis` generada por las reglas de la Definición 7.16
  (`alfaEq_iff_alfaTesis`), de modo que el lema también se enuncia con `AlfaTesis`
  (`lema_sustitucion_tesis`).

## Estrategia

Se traduce cada término a `TerminoDB`: las variables ligadas son índices de
De Bruijn y las libres conservan su nombre. Dos términos con nombre son
α-equivalentes cuando tienen la misma traducción. La cadena de lemas es:

1. `aDeBruijn_renombrar`: renombrar la variable ligada no cambia la traducción.
2. `aDeBruijn_sustitucion`: la traducción convierte `sustitucion` (con sus
   renombramientos) en la sustitución `sustLibre` de `TerminoDB`, que es puramente
   estructural porque allí no hay nombres ligados que capturar.
3. `sustLibre_conmuta`: el Lema de Sustitución para `TerminoDB`, por inducción
   estructural (los tres subcasos de la variable son los de la tesis).
4. `lema_sustitucion_alfa`: se transporta (3) a los términos con nombre mediante (2).
-/

namespace Thesis.Teoria.SustitucionAlfa

/-! ## Términos con nombre -/

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

/-- Variables de enlace de `M`: las `z` de cada `λ z` que aparece en `M`. -/
def ligadas : Termino → Finset String
  | var _ => ∅
  | app P Q => ligadas P ∪ ligadas Q
  | lam z P => insert z (ligadas P)

/-- Tamaño de un término (número de constructores). Mide la recursión de la
sustitución. -/
def tamano : Termino → ℕ
  | var _ => 1
  | app P Q => tamano P + tamano Q + 1
  | lam _ P => tamano P + 1

/-- Renombramiento `M^{x → y}` (Definición 7.15 de la tesis): cada ocurrencia libre
de `x` en `M` se reemplaza por `y`. -/
def renombrar : Termino → String → String → Termino
  | var z, x, y => if z = x then var y else var z
  | app P Q, x, y => app (renombrar P x y) (renombrar Q x y)
  | lam z P, x, y => if z = x then lam z P else lam z (renombrar P x y)

/-- El renombramiento preserva el tamaño. -/
theorem tamano_renombrar (M : Termino) (x y : String) :
    tamano (renombrar M x y) = tamano M := by
  induction M with
  | var z => by_cases h : z = x <;> simp [renombrar, tamano, h]
  | app P Q hipP hipQ => simp [renombrar, tamano, hipP, hipQ]
  | lam z P hipP => by_cases h : z = x <;> simp [renombrar, tamano, h, hipP]

/-! ## Variables frescas -/

/-- Una variable que no pertenece al conjunto finito `S`: una cadena estrictamente
más larga que todas las de `S`. -/
def fresca (S : Finset String) : String :=
  String.ofList (List.replicate (S.sup String.length + 1) 'a')

/-- `fresca S` no pertenece a `S`. -/
theorem fresca_no_pertenece (S : Finset String) : fresca S ∉ S := by
  intro hPertenece
  have hCota : (fresca S).length ≤ S.sup String.length := Finset.le_sup hPertenece
  have hLongitud : (fresca S).length = S.sup String.length + 1 := by
    simp [fresca]
  omega

/-! ## Sustitución que evita capturas -/

/-- La variable fresca que usa la cláusula (3) de la Definición 7.20 al sustituir
en `λ z . P`: no aparece en `P` (ni libre ni de enlace), no es libre en `N` y es
distinta de `x`. -/
def variableFresca (P : Termino) (x : String) (N : Termino) : String :=
  fresca (libres N ∪ libres P ∪ ligadas P ∪ {x})

/-- Sustitución `M[x := N]` que evita capturas (Definición 7.20 de la tesis).
En la abstracción `λ z . P`: no actúa si `z ≡ x`; entra bajo el ligador sin
renombrar si `z ≢ x` y no hay captura posible (`z ∉ FV(N)` o `x ∉ FV(P)`); en otro
caso renombra `z` a una variable fresca `w` y produce `λ w . (P^{z → w})[x := N]`. -/
def sustitucion : Termino → String → Termino → Termino
  | var z, x, N => if z = x then N else var z
  | app P Q, x, N => app (sustitucion P x N) (sustitucion Q x N)
  | lam z P, x, N =>
      if z = x then lam z P
      else if z ∉ libres N ∨ x ∉ libres P then lam z (sustitucion P x N)
      else lam (variableFresca P x N)
        (sustitucion (renombrar P z (variableFresca P x N)) x N)
termination_by M => tamano M
decreasing_by
  all_goals simp only [tamano, tamano_renombrar]
  all_goals omega

@[inherit_doc] notation:max M "⟦" x " := " N "⟧" => sustitucion M x N

/-- Cláusula (1a): `x[x := N] ≡ N`. -/
theorem sust_var_igual (x : String) (N : Termino) : (var x)⟦x := N⟧ = N := by
  simp [sustitucion]

/-- Cláusula (1b): `z[x := N] ≡ z` si `z ≢ x`. -/
theorem sust_var_distinta {z x : String} (h : z ≠ x) (N : Termino) :
    (var z)⟦x := N⟧ = var z := by
  simp [sustitucion, h]

/-- Cláusula (2): la sustitución se distribuye en la aplicación. -/
theorem sust_app (P Q : Termino) (x : String) (N : Termino) :
    (app P Q)⟦x := N⟧ = app (P⟦x := N⟧) (Q⟦x := N⟧) := by
  simp [sustitucion]

/-- Abstracción cuya variable ligada es la sustituida: `(λ x . P)[x := N] ≡ λ x . P`. -/
theorem sust_abs_igual (x : String) (P N : Termino) :
    (lam x P)⟦x := N⟧ = lam x P := by
  simp [sustitucion]

/-- Abstracción sin captura posible: `(λ z . P)[x := N] ≡ λ z . P[x := N]` si
`z ≢ x` y (`z ∉ FV(N)` o `x ∉ FV(P)`). -/
theorem sust_abs_sin_captura {z x : String} {P N : Termino} (hzx : z ≠ x)
    (hSinCaptura : z ∉ libres N ∨ x ∉ libres P) :
    (lam z P)⟦x := N⟧ = lam z (P⟦x := N⟧) := by
  rw [sustitucion, if_neg hzx, if_pos hSinCaptura]

/-- Cláusula (3) con renombramiento: si `z ≢ x`, `z ∈ FV(N)` y `x ∈ FV(P)`, entonces
`(λ z . P)[x := N] ≡ λ w . (P^{z → w})[x := N]` con `w` fresca. -/
theorem sust_abs_renombra {z x : String} {P N : Termino} (hzx : z ≠ x)
    (hzN : z ∈ libres N) (hxP : x ∈ libres P) :
    (lam z P)⟦x := N⟧
      = lam (variableFresca P x N) ((renombrar P z (variableFresca P x N))⟦x := N⟧) := by
  have hCaptura : ¬ (z ∉ libres N ∨ x ∉ libres P) := by
    intro h
    rcases h with h | h
    · exact h hzN
    · exact h hxP
  rw [sustitucion, if_neg hzx, if_neg hCaptura]

/-- Propiedades de la variable fresca de la cláusula (3). -/
theorem variableFresca_spec (P : Termino) (x : String) (N : Termino) :
    variableFresca P x N ∉ libres N ∧ variableFresca P x N ∉ libres P ∧
      variableFresca P x N ∉ ligadas P ∧ variableFresca P x N ≠ x := by
  have h := fresca_no_pertenece (libres N ∪ libres P ∪ ligadas P ∪ {x})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Si `x ∉ FV(M)`, entonces `M[x := N] ≡ M` (igualdad literal: no se renombra). -/
theorem sust_no_libre {x : String} (N : Termino) :
    ∀ {M : Termino}, x ∉ libres M → M⟦x := N⟧ = M := by
  intro M
  induction M with
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
      · subst hzx
        exact sust_abs_igual z P N
      · have hxP : x ∉ libres P := by
          intro h
          exact hx (by simp [libres, h, Ne.symm hzx])
        rw [sust_abs_sin_captura hzx (Or.inr hxP), hipP hxP]

/-! ## Traducción a términos sin nombres ligados -/

/-- Términos con índices de De Bruijn para las variables ligadas y nombres para las
libres. Aquí dos términos α-equivalentes son literalmente iguales. -/
inductive TerminoDB : Type
  | ligada (indice : ℕ) : TerminoDB
  | libre (nombre : String) : TerminoDB
  | app (funcion argumento : TerminoDB) : TerminoDB
  | lam (cuerpo : TerminoDB) : TerminoDB
  deriving DecidableEq, Repr

/-- Traducción de un término con nombres. El contexto `Γ` lista las variables
ligadas por las abstracciones que rodean al término, de la más interna a la más
externa: una variable que está en `Γ` se traduce a su posición; las demás quedan
libres con su nombre. -/
def aDeBruijn : List String → Termino → TerminoDB
  | Γ, var z => if z ∈ Γ then .ligada (Γ.idxOf z) else .libre z
  | Γ, app P Q => .app (aDeBruijn Γ P) (aDeBruijn Γ Q)
  | Γ, lam z P => .lam (aDeBruijn (z :: Γ) P)

/-- Sustitución de una variable libre en `TerminoDB`. Es estructural: no hay
nombres ligados, de modo que no hay capturas que evitar. (Solo se aplica a
términos `u` sin índices sueltos, por lo que no se necesita desplazar índices.) -/
def sustLibre : TerminoDB → String → TerminoDB → TerminoDB
  | .ligada n, _, _ => .ligada n
  | .libre v, x, u => if v = x then u else .libre v
  | .app s t, x, u => .app (sustLibre s x u) (sustLibre t x u)
  | .lam t, x, u => .lam (sustLibre t x u)

/-- Si toda ocurrencia libre de `x` en `P` está ligada por el contexto `Γ`, la
traducción de `P` no contiene a `x` como variable libre y `sustLibre` no actúa. -/
theorem sustLibre_aDeBruijn_sin_libre {x : String} (u : TerminoDB) :
    ∀ (P : Termino) (Γ : List String), (x ∈ libres P → x ∈ Γ) →
      sustLibre (aDeBruijn Γ P) x u = aDeBruijn Γ P := by
  intro P
  induction P with
  | var z =>
      intro Γ h
      by_cases hz : z ∈ Γ
      · simp [aDeBruijn, hz, sustLibre]
      · have hzx : z ≠ x := by
          intro hIgual
          exact hz (hIgual ▸ h (by simp [libres, hIgual]))
        simp [aDeBruijn, hz, sustLibre, hzx]
  | app P Q hipP hipQ =>
      intro Γ h
      have hP : x ∈ libres P → x ∈ Γ := fun hx => h (by simp [libres, hx])
      have hQ : x ∈ libres Q → x ∈ Γ := fun hx => h (by simp [libres, hx])
      simp [aDeBruijn, sustLibre, hipP Γ hP, hipQ Γ hQ]
  | lam z P hipP =>
      intro Γ h
      have hP : x ∈ libres P → x ∈ z :: Γ := by
        intro hx
        by_cases hxz : x = z
        · simp [hxz]
        · exact List.mem_cons_of_mem _ (h (by simp [libres, hx, hxz]))
      simp [aDeBruijn, sustLibre, hipP (z :: Γ) hP]

/-- Las variables del contexto que no son libres en `N` (o que ya están ligadas
por un contexto más interno `Δ`) no influyen en la traducción. -/
theorem aDeBruijn_contexto_irrelevante :
    ∀ (N : Termino) (Δ Γ : List String), (∀ v ∈ Γ, v ∈ libres N → v ∈ Δ) →
      aDeBruijn (Δ ++ Γ) N = aDeBruijn Δ N := by
  intro N
  induction N with
  | var z =>
      intro Δ Γ h
      by_cases hz : z ∈ Δ
      · simp [aDeBruijn, hz, List.idxOf_append_of_mem hz]
      · have hzΓ : z ∉ Γ := fun hEn => hz (h z hEn (by simp [libres]))
        simp [aDeBruijn, hz, hzΓ]
  | app P Q hipP hipQ =>
      intro Δ Γ h
      have hP : ∀ v ∈ Γ, v ∈ libres P → v ∈ Δ := fun v hv hx =>
        h v hv (by simp [libres, hx])
      have hQ : ∀ v ∈ Γ, v ∈ libres Q → v ∈ Δ := fun v hv hx =>
        h v hv (by simp [libres, hx])
      simp [aDeBruijn, hipP Δ Γ hP, hipQ Δ Γ hQ]
  | lam z P hipP =>
      intro Δ Γ h
      have hP : ∀ v ∈ Γ, v ∈ libres P → v ∈ z :: Δ := by
        intro v hv hx
        by_cases hvz : v = z
        · simp [hvz]
        · exact List.mem_cons_of_mem _ (h v hv (by simp [libres, hx, hvz]))
      have hip := hipP (z :: Δ) Γ hP
      simp only [List.cons_append] at hip
      simp [aDeBruijn, hip]

/-- Si ni `z` ni `w` aparecen libres en `P` fuera del alcance de `Δ`, da igual cuál
de las dos ocupe una posición del contexto situada detrás de `Δ`. -/
theorem aDeBruijn_cambio_oculto {z w : String} (Γ : List String) :
    ∀ (P : Termino) (Δ : List String), (z ∈ Δ ∨ z ∉ libres P) → (w ∈ Δ ∨ w ∉ libres P) →
      aDeBruijn (Δ ++ w :: Γ) P = aDeBruijn (Δ ++ z :: Γ) P := by
  intro P
  induction P with
  | var v =>
      intro Δ hz hw
      by_cases hv : v ∈ Δ
      · simp [aDeBruijn, hv, List.idxOf_append_of_mem hv]
      · have hvz : v ≠ z := by
          intro hIgual
          rcases hz with hz | hz
          · exact hv (hIgual ▸ hz)
          · exact hz (by simp [libres, hIgual])
        have hvw : v ≠ w := by
          intro hIgual
          rcases hw with hw | hw
          · exact hv (hIgual ▸ hw)
          · exact hw (by simp [libres, hIgual])
        simp [aDeBruijn, hv, hvz, hvw, List.idxOf_append_of_notMem hv,
          List.idxOf_cons_ne _ (Ne.symm hvz), List.idxOf_cons_ne _ (Ne.symm hvw)]
  | app P Q hipP hipQ =>
      intro Δ hz hw
      have hzP : z ∈ Δ ∨ z ∉ libres P := hz.imp id (fun h hx => h (by simp [libres, hx]))
      have hzQ : z ∈ Δ ∨ z ∉ libres Q := hz.imp id (fun h hx => h (by simp [libres, hx]))
      have hwP : w ∈ Δ ∨ w ∉ libres P := hw.imp id (fun h hx => h (by simp [libres, hx]))
      have hwQ : w ∈ Δ ∨ w ∉ libres Q := hw.imp id (fun h hx => h (by simp [libres, hx]))
      simp [aDeBruijn, hipP Δ hzP hwP, hipQ Δ hzQ hwQ]
  | lam v P hipP =>
      intro Δ hz hw
      have hzP : z ∈ v :: Δ ∨ z ∉ libres P := by
        by_cases hzv : z = v
        · exact Or.inl (by simp [hzv])
        · exact hz.imp (List.mem_cons_of_mem _) (fun h hx => h (by simp [libres, hx, hzv]))
      have hwP : w ∈ v :: Δ ∨ w ∉ libres P := by
        by_cases hwv : w = v
        · exact Or.inl (by simp [hwv])
        · exact hw.imp (List.mem_cons_of_mem _) (fun h hx => h (by simp [libres, hx, hwv]))
      have hip := hipP (v :: Δ) hzP hwP
      simp only [List.cons_append] at hip
      simp [aDeBruijn, hip]

/-- Renombrar la variable ligada no cambia la traducción: si `w` no aparece en `P`
(ni libre ni de enlace), traducir `P^{z → w}` con `w` en el contexto equivale a
traducir `P` con `z` en la misma posición. -/
theorem aDeBruijn_renombrar {z w : String} (Γ : List String) :
    ∀ (P : Termino) (Δ : List String), z ∉ Δ → w ∉ Δ → w ∉ libres P → w ∉ ligadas P →
      aDeBruijn (Δ ++ w :: Γ) (renombrar P z w) = aDeBruijn (Δ ++ z :: Γ) P := by
  intro P
  induction P with
  | var v =>
      intro Δ hz hw hwLibre _
      have hvw : v ≠ w := by
        intro hIgual
        exact hwLibre (by simp [libres, hIgual])
      by_cases hvz : v = z
      · -- La variable renombrada: ambas ocupan la posición `|Δ|`.
        subst hvz
        simp [renombrar, aDeBruijn, List.idxOf_append_of_notMem hz,
          List.idxOf_append_of_notMem hw]
      · by_cases hv : v ∈ Δ
        · simp [renombrar, hvz, aDeBruijn, hv, List.idxOf_append_of_mem hv]
        · simp [renombrar, hvz, aDeBruijn, hv, hvw, List.idxOf_append_of_notMem hv,
            List.idxOf_cons_ne _ (Ne.symm hvz), List.idxOf_cons_ne _ (Ne.symm hvw)]
  | app P Q hipP hipQ =>
      intro Δ hz hw hwLibre hwLigada
      have hwP : w ∉ libres P := fun h => hwLibre (by simp [libres, h])
      have hwQ : w ∉ libres Q := fun h => hwLibre (by simp [libres, h])
      have hwP' : w ∉ ligadas P := fun h => hwLigada (by simp [ligadas, h])
      have hwQ' : w ∉ ligadas Q := fun h => hwLigada (by simp [ligadas, h])
      simp [renombrar, aDeBruijn, hipP Δ hz hw hwP hwP', hipQ Δ hz hw hwQ hwQ']
  | lam v P hipP =>
      intro Δ hz hw hwLibre hwLigada
      have hwv : w ≠ v := fun h => hwLigada (by simp [ligadas, h])
      have hwP : w ∉ libres P := fun h => hwLibre (by simp [libres, h, hwv])
      have hwP' : w ∉ ligadas P := fun h => hwLigada (by simp [ligadas, h])
      by_cases hvz : v = z
      · -- `λ z` oculta a `z`: el renombramiento no entra y el contexto es indiferente.
        subst hvz
        have hip := aDeBruijn_cambio_oculto (z := v) (w := w) Γ P (v :: Δ)
          (Or.inl (by simp)) (Or.inr hwP)
        simp only [List.cons_append] at hip
        simp [renombrar, aDeBruijn, hip]
      · have hzv : z ∉ v :: Δ := by
          simp [List.mem_cons, Ne.symm hvz, hz]
        have hwv' : w ∉ v :: Δ := by
          simp [List.mem_cons, hwv, hw]
        have hip := hipP (v :: Δ) hzv hwv' hwP hwP'
        simp only [List.cons_append] at hip
        simp [renombrar, hvz, aDeBruijn, hip]

/-- La traducción convierte la sustitución que evita capturas en la sustitución
estructural de `TerminoDB`, siempre que el contexto `Γ` no contenga a `x` ni a
variables libres de `N`. Inducción sobre el tamaño de `M`, porque la cláusula (3)
sustituye en `P^{z → w}`, que no es un subtérmino. -/
theorem aDeBruijn_sustitucion_aux (x : String) (N : Termino) :
    ∀ (n : ℕ) (M : Termino), tamano M < n → ∀ (Γ : List String), x ∉ Γ →
      (∀ v ∈ Γ, v ∉ libres N) →
      aDeBruijn Γ (M⟦x := N⟧) = sustLibre (aDeBruijn Γ M) x (aDeBruijn [] N) := by
  intro n
  induction n with
  | zero =>
      intro M hTam
      omega
  | succ n hipInd =>
      intro M hTam Γ hxΓ hΓN
      cases M with
      | var z =>
          by_cases hzx : z = x
          · -- `x[x := N] ≡ N`, y el contexto no liga variables libres de `N`.
            subst hzx
            have hCtx := aDeBruijn_contexto_irrelevante N [] Γ
              (fun v hv hLibre => absurd hLibre (hΓN v hv))
            simp only [List.nil_append] at hCtx
            simp [sust_var_igual, aDeBruijn, hxΓ, sustLibre, hCtx]
          · by_cases hz : z ∈ Γ
            · simp [sust_var_distinta hzx, aDeBruijn, hz, sustLibre]
            · simp [sust_var_distinta hzx, aDeBruijn, hz, sustLibre, hzx]
      | app P Q =>
          simp only [tamano] at hTam
          have hP := hipInd P (by omega) Γ hxΓ hΓN
          have hQ := hipInd Q (by omega) Γ hxΓ hΓN
          simp [sust_app, aDeBruijn, sustLibre, hP, hQ]
      | lam z P =>
          simp only [tamano] at hTam
          by_cases hzx : z = x
          · -- `λ x` oculta a `x`: ninguna de las dos sustituciones actúa.
            subst hzx
            have hSin := sustLibre_aDeBruijn_sin_libre (x := z) (aDeBruijn [] N) P (z :: Γ)
              (fun _ => by simp)
            simp [sust_abs_igual, aDeBruijn, sustLibre, hSin]
          · by_cases hxP : x ∈ libres P
            · by_cases hzN : z ∈ libres N
              · -- Cláusula (3): se renombra `z` a la variable fresca `w`.
                obtain ⟨hwN, hwP, hwP', hwx⟩ := variableFresca_spec P x N
                rw [sust_abs_renombra hzx hzN hxP]
                generalize variableFresca P x N = w at hwN hwP hwP' hwx
                have hxw : x ∉ w :: Γ := by
                  simp [List.mem_cons, Ne.symm hwx, hxΓ]
                have hwΓN : ∀ v ∈ w :: Γ, v ∉ libres N := by
                  intro v hv
                  rcases List.mem_cons.mp hv with hv | hv
                  · exact hv ▸ hwN
                  · exact hΓN v hv
                have hip := hipInd (renombrar P z w)
                  (by rw [tamano_renombrar]; omega) (w :: Γ) hxw hwΓN
                have hRen := aDeBruijn_renombrar (z := z) (w := w) Γ P []
                  (by simp) (by simp) hwP hwP'
                simp only [List.nil_append] at hRen
                simp [aDeBruijn, sustLibre, hip, hRen]
              · -- Sin captura: `z ∉ FV(N)`.
                have hxz : x ∉ z :: Γ := by
                  simp [List.mem_cons, Ne.symm hzx, hxΓ]
                have hzΓN : ∀ v ∈ z :: Γ, v ∉ libres N := by
                  intro v hv
                  rcases List.mem_cons.mp hv with hv | hv
                  · exact hv ▸ hzN
                  · exact hΓN v hv
                have hip := hipInd P (by omega) (z :: Γ) hxz hzΓN
                simp [sust_abs_sin_captura hzx (Or.inl hzN), aDeBruijn, sustLibre, hip]
            · -- Sin captura: `x ∉ FV(P)`; ninguna de las dos sustituciones actúa.
              have hSin := sustLibre_aDeBruijn_sin_libre (x := x) (aDeBruijn [] N) P (z :: Γ)
                (fun h => absurd h hxP)
              simp [sust_abs_sin_captura hzx (Or.inr hxP), sust_no_libre N hxP, aDeBruijn,
                sustLibre, hSin]

/-- La traducción de `M[x := N]` es la sustitución estructural de la traducción de
`N` en la traducción de `M`. -/
theorem aDeBruijn_sustitucion (M : Termino) (x : String) (N : Termino) :
    aDeBruijn [] (M⟦x := N⟧) = sustLibre (aDeBruijn [] M) x (aDeBruijn [] N) :=
  aDeBruijn_sustitucion_aux x N (tamano M + 1) M (Nat.lt_succ_self _) []
    (by simp) (by simp)

/-- Lema de Sustitución para `TerminoDB`: si `x ≢ y` y `x` no es libre en `l`
(esto es, `l[x := u] = l` para todo `u`), entonces
`m[x := n][y := l] = m[y := l][x := n[y := l]]`. Inducción estructural sobre `m`;
los subcasos de la variable libre son los tres de la demostración de la tesis. -/
theorem sustLibre_conmuta {x y : String} (hxy : x ≠ y) (n l : TerminoDB)
    (hxl : ∀ u, sustLibre l x u = l) :
    ∀ m : TerminoDB,
      sustLibre (sustLibre m x n) y l
        = sustLibre (sustLibre m y l) x (sustLibre n y l) := by
  intro m
  induction m with
  | ligada k => simp [sustLibre]
  | libre v =>
      by_cases hvx : v = x
      · -- Subcaso `v ≡ x`: ambos lados son `n[y := l]`.
        subst hvx
        simp [sustLibre, hxy]
      · by_cases hvy : v = y
        · -- Subcaso `v ≡ y`: ambos lados son `l`, pues `x` no es libre en `l`.
          subst hvy
          simp [sustLibre, hvx, hxl]
        · -- Subcaso `v ≢ x` y `v ≢ y`: ambos lados son `v`.
          simp [sustLibre, hvx, hvy]
  | app s t hipS hipT => simp [sustLibre, hipS, hipT]
  | lam t hipT => simp [sustLibre, hipT]

/-! ## α-equivalencia -/

/-- α-equivalencia (Definición 7.16 de la tesis): dos términos son α-equivalentes
cuando tienen la misma traducción, es decir, cuando solo difieren en los nombres
de sus variables ligadas. -/
def AlfaEq (M N : Termino) : Prop :=
  aDeBruijn [] M = aDeBruijn [] N

@[inherit_doc] infix:50 " ≡α " => AlfaEq

/-- Reflexividad de la α-equivalencia. -/
theorem alfa_refl (M : Termino) : M ≡α M := rfl

/-- Simetría de la α-equivalencia. -/
theorem alfa_simm {M N : Termino} (h : M ≡α N) : N ≡α M := Eq.symm h

/-- Transitividad de la α-equivalencia. -/
theorem alfa_trans {L M N : Termino} (h₁ : L ≡α M) (h₂ : M ≡α N) : L ≡α N :=
  Eq.trans h₁ h₂

/-- La α-equivalencia es una relación de equivalencia (Definición 7.16, punto 3). -/
theorem alfaEq_equivalencia : Equivalence AlfaEq :=
  ⟨alfa_refl, alfa_simm, alfa_trans⟩

/-- **Regla de renombramiento** (Definiciones 7.15 y 7.16, punto 1):
`λ x . M =α λ y . M^{x → y}` siempre que `y ∉ FV(M)` y `y` no sea una variable de
enlace en `M`. -/
theorem alfa_renombre (x y : String) (M : Termino)
    (hLibre : y ∉ libres M) (hLigada : y ∉ ligadas M) :
    lam x M ≡α lam y (renombrar M x y) := by
  have hRen := aDeBruijn_renombrar (z := x) (w := y) [] M [] (by simp) (by simp)
    hLibre hLigada
  simp only [List.nil_append] at hRen
  simp [AlfaEq, aDeBruijn, hRen]

/-- Cierre de un `TerminoDB` respecto de un contexto: las variables libres que
están en `Γ` pasan a ser índices, contados a partir de la profundidad `k`. -/
def cerrar : ℕ → List String → TerminoDB → TerminoDB
  | _, _, .ligada n => .ligada n
  | k, Γ, .libre v => if v ∈ Γ then .ligada (k + Γ.idxOf v) else .libre v
  | k, Γ, .app s t => .app (cerrar k Γ s) (cerrar k Γ t)
  | k, Γ, .lam t => .lam (cerrar (k + 1) Γ t)

/-- La traducción en un contexto ampliado se obtiene cerrando la traducción en el
contexto original. -/
theorem aDeBruijn_append (Γ : List String) :
    ∀ (M : Termino) (Δ : List String),
      aDeBruijn (Δ ++ Γ) M = cerrar Δ.length Γ (aDeBruijn Δ M) := by
  intro M
  induction M with
  | var z =>
      intro Δ
      by_cases hz : z ∈ Δ
      · simp [aDeBruijn, hz, cerrar, List.idxOf_append_of_mem hz]
      · by_cases hzΓ : z ∈ Γ
        · simp [aDeBruijn, hz, hzΓ, cerrar, List.idxOf_append_of_notMem hz]
        · simp [aDeBruijn, hz, hzΓ, cerrar]
  | app P Q hipP hipQ =>
      intro Δ
      simp [aDeBruijn, cerrar, hipP Δ, hipQ Δ]
  | lam z P hipP =>
      intro Δ
      have hip := hipP (z :: Δ)
      simp only [List.cons_append, List.length_cons] at hip
      simp [aDeBruijn, cerrar, hip]

/-- Dos términos α-equivalentes tienen la misma traducción en todo contexto. -/
theorem alfa_en_contexto {M N : Termino} (h : M ≡α N) (Γ : List String) :
    aDeBruijn Γ M = aDeBruijn Γ N := by
  have hM := aDeBruijn_append Γ M []
  have hN := aDeBruijn_append Γ N []
  simp only [List.nil_append, List.length_nil] at hM hN
  rw [hM, hN, h]

/-- Compatibilidad con la aplicación (Definición 7.16, punto 2). -/
theorem alfa_app {M M' N N' : Termino} (hM : M ≡α M') (hN : N ≡α N') :
    app M N ≡α app M' N' := by
  unfold AlfaEq at hM hN ⊢
  simp [aDeBruijn, hM, hN]

/-- Compatibilidad con la abstracción (Definición 7.16, punto 2):
si `M =α N`, entonces `λ z . M =α λ z . N`. -/
theorem alfa_lam (z : String) {M N : Termino} (h : M ≡α N) : lam z M ≡α lam z N := by
  have hCtx := alfa_en_contexto h [z]
  simp [AlfaEq, aDeBruijn, hCtx]

/-- La relación generada literalmente por las reglas de la Definición 7.16 de la
tesis: renombramiento, compatibilidad, reflexividad, simetría y transitividad. -/
inductive AlfaTesis : Termino → Termino → Prop
  | renombre (x y : String) (M : Termino) :
      y ∉ libres M → y ∉ ligadas M → AlfaTesis (lam x M) (lam y (renombrar M x y))
  | appIzq {M N : Termino} (L : Termino) : AlfaTesis M N → AlfaTesis (app M L) (app N L)
  | appDer {M N : Termino} (L : Termino) : AlfaTesis M N → AlfaTesis (app L M) (app L N)
  | abs {M N : Termino} (z : String) : AlfaTesis M N → AlfaTesis (lam z M) (lam z N)
  | refl (M : Termino) : AlfaTesis M M
  | simm {M N : Termino} : AlfaTesis M N → AlfaTesis N M
  | trans {L M N : Termino} : AlfaTesis L M → AlfaTesis M N → AlfaTesis L N

/-- Toda α-conversión derivable con las reglas de la Definición 7.16 es una
α-equivalencia en el sentido de `AlfaEq`. -/
theorem alfaTesis_implica_alfaEq {M N : Termino} (h : AlfaTesis M N) : M ≡α N := by
  induction h with
  | renombre x y M hLibre hLigada => exact alfa_renombre x y M hLibre hLigada
  | appIzq L _ hip => exact alfa_app hip (alfa_refl L)
  | appDer L _ hip => exact alfa_app (alfa_refl L) hip
  | abs z _ hip => exact alfa_lam z hip
  | refl M => exact alfa_refl M
  | simm _ hip => exact alfa_simm hip
  | trans _ _ hip₁ hip₂ => exact alfa_trans hip₁ hip₂

/-- La α-equivalencia distingue términos que no son variantes α: `λ x . y` no es
α-equivalente a `λ y . y` (el renombramiento `x ↦ y` capturaría a `y`). -/
example : ¬ (lam "x" (var "y") ≡α lam "y" (var "y")) := by
  simp [AlfaEq, aDeBruijn]

/-- La sustitución renombra cuando hay captura: `(λ y . x)[x := y]` es
α-equivalente a `λ z . y`, y no a `λ y . y`. -/
example : (lam "y" (var "x"))⟦"x" := var "y"⟧ ≡α lam "z" (var "y") := by
  unfold AlfaEq
  rw [aDeBruijn_sustitucion]
  simp [aDeBruijn, sustLibre]

/-! ### Recíproco: `≡α` no es más gruesa que la Definición 7.16 -/

/-- El renombramiento no cambia las variables de enlace. -/
theorem ligadas_renombrar (M : Termino) (x y : String) :
    ligadas (renombrar M x y) = ligadas M := by
  induction M with
  | var z => by_cases h : z = x <;> simp [renombrar, ligadas, h]
  | app P Q hipP hipQ => simp [renombrar, ligadas, hipP, hipQ]
  | lam z P hipP => by_cases h : z = x <;> simp [renombrar, ligadas, h, hipP]

/-- Apertura de un `TerminoDB`: el índice que apunta a la profundidad `k` se
convierte en la variable libre `w`. Es la operación inversa de añadir `w` al final
del contexto de la traducción. -/
def abrir : ℕ → String → TerminoDB → TerminoDB
  | k, w, .ligada n => if n = k then .libre w else .ligada n
  | _, _, .libre v => .libre v
  | k, w, .app s t => .app (abrir k w s) (abrir k w t)
  | k, w, .lam t => .lam (abrir (k + 1) w t)

/-- Abrir la traducción hecha con `w` al final del contexto devuelve la traducción
sin `w`, siempre que `w` no esté ya en el contexto ni sea variable de enlace. -/
theorem abrir_aDeBruijn {w : String} :
    ∀ (A : Termino) (Δ : List String), w ∉ Δ → w ∉ ligadas A →
      abrir Δ.length w (aDeBruijn (Δ ++ [w]) A) = aDeBruijn Δ A := by
  intro A
  induction A with
  | var v =>
      intro Δ hw _
      by_cases hv : v ∈ Δ
      · have hMenor : Δ.idxOf v < Δ.length := List.idxOf_lt_length_of_mem hv
        have hDistinto : Δ.idxOf v ≠ Δ.length := by omega
        simp [aDeBruijn, hv, List.idxOf_append_of_mem hv, abrir, hDistinto]
      · by_cases hvw : v = w
        · subst hvw
          simp [aDeBruijn, hv, List.idxOf_append_of_notMem hv, abrir]
        · simp [aDeBruijn, hv, hvw, abrir]
  | app P Q hipP hipQ =>
      intro Δ hw hLig
      have hP : w ∉ ligadas P := fun h => hLig (by simp [ligadas, h])
      have hQ : w ∉ ligadas Q := fun h => hLig (by simp [ligadas, h])
      simp [aDeBruijn, abrir, hipP Δ hw hP, hipQ Δ hw hQ]
  | lam z P hipP =>
      intro Δ hw hLig
      have hwz : w ≠ z := fun h => hLig (by simp [ligadas, h])
      have hP : w ∉ ligadas P := fun h => hLig (by simp [ligadas, h])
      have hwΔ : w ∉ z :: Δ := by simp [List.mem_cons, hwz, hw]
      have hip := hipP (z :: Δ) hwΔ hP
      simp only [List.cons_append, List.length_cons] at hip
      simp [aDeBruijn, abrir, hip]

/-- Versión con cota de tamaño del recíproco: inducción sobre el tamaño de `M`,
porque en el caso de la abstracción se pasa a los cuerpos renombrados. -/
theorem alfaEq_implica_alfaTesis_aux :
    ∀ (n : ℕ) (M N : Termino), tamano M < n → M ≡α N → AlfaTesis M N := by
  intro n
  induction n with
  | zero =>
      intro M N hTam
      omega
  | succ n hipInd =>
      intro M N hTam h
      unfold AlfaEq at h
      cases M with
      | var z =>
          cases N with
          | var z' =>
              have hIgual : z = z' := by simpa [aDeBruijn] using h
              subst hIgual
              exact AlfaTesis.refl _
          | app P' Q' => simp [aDeBruijn] at h
          | lam y Q => simp [aDeBruijn] at h
      | app P Q =>
          cases N with
          | var z' => simp [aDeBruijn] at h
          | app P' Q' =>
              simp only [tamano] at hTam
              simp only [aDeBruijn, TerminoDB.app.injEq] at h
              -- Compatibilidad a izquierda y a derecha, y transitividad.
              have hP : AlfaTesis P P' := hipInd P P' (by omega) h.1
              have hQ : AlfaTesis Q Q' := hipInd Q Q' (by omega) h.2
              exact AlfaTesis.trans (AlfaTesis.appIzq Q hP) (AlfaTesis.appDer P' hQ)
          | lam y Q => simp [aDeBruijn] at h
      | lam x P =>
          cases N with
          | var z' => simp [aDeBruijn] at h
          | app P' Q' => simp [aDeBruijn] at h
          | lam y Q =>
              simp only [tamano] at hTam
              simp only [aDeBruijn, TerminoDB.lam.injEq] at h
              -- Se elige `w` fresca para ambos cuerpos.
              have hFresca := fresca_no_pertenece
                (libres P ∪ ligadas P ∪ libres Q ∪ ligadas Q)
              generalize fresca (libres P ∪ ligadas P ∪ libres Q ∪ ligadas Q) = w at hFresca
              simp only [Finset.mem_union, not_or] at hFresca
              obtain ⟨⟨⟨hwP, hwP'⟩, hwQ⟩, hwQ'⟩ := hFresca
              -- Los cuerpos renombrados tienen la misma traducción con `w` en el contexto…
              have hRenP := aDeBruijn_renombrar (z := x) (w := w) [] P []
                (by simp) (by simp) hwP hwP'
              have hRenQ := aDeBruijn_renombrar (z := y) (w := w) [] Q []
                (by simp) (by simp) hwQ hwQ'
              simp only [List.nil_append] at hRenP hRenQ
              have hCtx : aDeBruijn [w] (renombrar P x w) = aDeBruijn [w] (renombrar Q y w) := by
                rw [hRenP, hRenQ, h]
              -- … y por tanto también en el contexto vacío.
              have hAbrirP := abrir_aDeBruijn (w := w) (renombrar P x w) []
                (by simp) (by rw [ligadas_renombrar]; exact hwP')
              have hAbrirQ := abrir_aDeBruijn (w := w) (renombrar Q y w) []
                (by simp) (by rw [ligadas_renombrar]; exact hwQ')
              simp only [List.nil_append, List.length_nil] at hAbrirP hAbrirQ
              have hCuerpos : renombrar P x w ≡α renombrar Q y w := by
                unfold AlfaEq
                rw [← hAbrirP, ← hAbrirQ, hCtx]
              have hip : AlfaTesis (renombrar P x w) (renombrar Q y w) :=
                hipInd _ _ (by rw [tamano_renombrar]; omega) hCuerpos
              -- `λ x . P =α λ w . P^{x → w} =α λ w . Q^{y → w} =α λ y . Q`.
              exact AlfaTesis.trans (AlfaTesis.renombre x w P hwP hwP')
                (AlfaTesis.trans (AlfaTesis.abs w hip)
                  (AlfaTesis.simm (AlfaTesis.renombre y w Q hwQ hwQ')))

/-- Recíproco: toda α-equivalencia en el sentido de `AlfaEq` es derivable con las
reglas de la Definición 7.16 de la tesis. -/
theorem alfaEq_implica_alfaTesis {M N : Termino} (h : M ≡α N) : AlfaTesis M N :=
  alfaEq_implica_alfaTesis_aux (tamano M + 1) M N (Nat.lt_succ_self _) h

/-- `≡α` coincide exactamente con la α-equivalencia de la Definición 7.16. -/
theorem alfaEq_iff_alfaTesis {M N : Termino} : M ≡α N ↔ AlfaTesis M N :=
  ⟨alfaEq_implica_alfaTesis, alfaTesis_implica_alfaEq⟩

/-! ## Lema de Sustitución -/

/-- **Lema 7.23 de la tesis (Lema de Sustitución).** Si `x ≢ y` y `x ∉ FV(L)`,
entonces

  `M[x := N][y := L] ≡α M[y := L][x := N[y := L]]`

para la sustitución que evita capturas de la Definición 7.20, módulo
α-equivalencia y sin ninguna hipótesis sobre las variables ligadas de `M`. -/
theorem lema_sustitucion_alfa (M N L : Termino) {x y : String}
    (hxy : x ≠ y) (hxL : x ∉ libres L) :
    M⟦x := N⟧⟦y := L⟧ ≡α M⟦y := L⟧⟦x := N⟦y := L⟧⟧ := by
  -- `x ∉ FV(L)`: en la traducción de `L` no hay ninguna `x` que sustituir.
  have hxl : ∀ u, sustLibre (aDeBruijn [] L) x u = aDeBruijn [] L := fun u =>
    sustLibre_aDeBruijn_sin_libre u L [] (fun h => absurd h hxL)
  -- Se traducen las cuatro sustituciones y se aplica el lema para `TerminoDB`.
  calc aDeBruijn [] (M⟦x := N⟧⟦y := L⟧)
      = sustLibre (sustLibre (aDeBruijn [] M) x (aDeBruijn [] N)) y (aDeBruijn [] L) := by
        rw [aDeBruijn_sustitucion, aDeBruijn_sustitucion]
    _ = sustLibre (sustLibre (aDeBruijn [] M) y (aDeBruijn [] L)) x
          (sustLibre (aDeBruijn [] N) y (aDeBruijn [] L)) :=
        sustLibre_conmuta hxy _ _ hxl _
    _ = aDeBruijn [] (M⟦y := L⟧⟦x := N⟦y := L⟧⟧) := by
        rw [aDeBruijn_sustitucion, aDeBruijn_sustitucion, aDeBruijn_sustitucion]

/-- **Lema 7.23 de la tesis**, con la conclusión expresada en la relación generada
por las reglas de la Definición 7.16 (`AlfaTesis`). -/
theorem lema_sustitucion_tesis (M N L : Termino) {x y : String}
    (hxy : x ≠ y) (hxL : x ∉ libres L) :
    AlfaTesis (M⟦x := N⟧⟦y := L⟧) (M⟦y := L⟧⟦x := N⟦y := L⟧⟧) :=
  alfaEq_implica_alfaTesis (lema_sustitucion_alfa M N L hxy hxL)

#print axioms lema_sustitucion_alfa
#print axioms alfaEq_iff_alfaTesis
#print axioms lema_sustitucion_tesis

end Thesis.Teoria.SustitucionAlfa
