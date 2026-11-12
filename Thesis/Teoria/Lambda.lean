import Mathlib.Data.Set.Insert

/-!
# Cálculo λ no tipado: subtérminos, reducción β y conversión β (capítulo 7)

Se formalizan, siguiendo las demostraciones en papel de la tesis:

* **Lema 7.6**: la relación de subtérmino `Sub` es reflexiva y transitiva.
* **Lema 7.31**: `↠β` extiende `→β` y es reflexiva y transitiva.
* **Lema 7.32**: `=β` extiende `↠β` en ambas direcciones y es una relación de equivalencia.
* **Corolario 7.43**: Church–Rosser para la conversión.
* **Corolario 7.44**: unicidad de la forma normal β.

Decisiones de representación:

* Los λ-términos son los de la Definición 7.1, con variables con nombre. No se toma el
  cociente módulo α; ninguno de los cinco resultados lo necesita.
* La reducción β de un paso es paramétrica en una función de sustitución
  `sust M x N` (léase `M[x := N]`). Ninguno de los cinco resultados usa propiedades de
  la sustitución, que se formaliza en otro archivo.
* `↠β` y `=β` se definen, como en la tesis, por la existencia de una cadena finita de
  `n ≥ 0` pasos (`Cadena R n M N`), y las pruebas manipulan esas cadenas (concatenación,
  inversión, inducción sobre la longitud).
* El Teorema 7.37 (Church–Rosser, confluencia de `↠β`) se cita en la tesis sin
  demostración. Aquí es la proposición `Confluente` y entra como hipótesis explícita de
  los Corolarios 7.43 y 7.44. No se añade ningún axioma.
-/

namespace Thesis.Teoria.Lambda

/-! ### λ-términos y subtérminos -/

/-- Las variables `V = {x, y, z, …}` de la Definición 7.1 de la tesis. -/
abbrev Var := String

/-- El conjunto `Λ` de los λ-términos (Definición 7.1 de la tesis): variables,
aplicaciones `(M N)` y abstracciones `(λ x . M)`. -/
inductive Termino : Type
  | var (x : Var) : Termino
  | app (M N : Termino) : Termino
  | abs (x : Var) (M : Termino) : Termino

open Termino

/-- El conjunto `Sub(P)` de los subtérminos de `P`, por recursión estructural
(Definición 7.3 de la tesis). -/
def Sub : Termino → Set Termino
  | var x => {var x}
  | app M N => Sub M ∪ Sub N ∪ {app M N}
  | abs x M => Sub M ∪ {abs x M}

/-- **Lema 7.6 (1) de la tesis.** Reflexividad: `M ∈ Sub(M)`. -/
theorem sub_reflexiva (M : Termino) : M ∈ Sub M := by
  -- Se revisa cada forma de `M`, como en la tesis.
  cases M with
  | var x =>
      -- `M = x`: `x ∈ Sub(x) = {x}`.
      show var x ∈ ({var x} : Set Termino)
      exact Set.mem_singleton (var x)
  | app P Q =>
      -- `M = (P Q)`: `(P Q) ∈ Sub(P) ∪ Sub(Q) ∪ {(P Q)}`.
      show (app P Q ∈ Sub P ∨ app P Q ∈ Sub Q) ∨ app P Q ∈ ({app P Q} : Set Termino)
      exact Or.inr (Set.mem_singleton (app P Q))
  | abs x P =>
      -- `M = (λ x . P)`: `(λ x . P) ∈ Sub(P) ∪ {(λ x . P)}`.
      show abs x P ∈ Sub P ∨ abs x P ∈ ({abs x P} : Set Termino)
      exact Or.inr (Set.mem_singleton (abs x P))

/-- **Lema 7.6 (2) de la tesis.** Transitividad: si `L ∈ Sub(M)` y `M ∈ Sub(N)`,
entonces `L ∈ Sub(N)`. -/
theorem sub_transitiva {L M N : Termino} (hLM : L ∈ Sub M) (hMN : M ∈ Sub N) :
    L ∈ Sub N := by
  -- Inducción estructural sobre `N`.
  induction N with
  | var x =>
      -- Caso variable: `Sub(N) = {x}`, luego `M = x`.
      have hM : M = var x := hMN
      -- Como `M = x`, `Sub(M) = {x}` y por tanto `L = x`.
      rw [hM] at hLM
      have hL : L = var x := hLM
      -- Así `L = x ∈ {x} = Sub(N)`.
      rw [hL]
      exact sub_reflexiva (var x)
  | app P Q hipIndP hipIndQ =>
      -- Caso aplicación: `M ∈ Sub(P) ∨ M ∈ Sub(Q) ∨ M ≡ (P Q)`.
      have hCasos : (M ∈ Sub P ∨ M ∈ Sub Q) ∨ M = app P Q := hMN
      show (L ∈ Sub P ∨ L ∈ Sub Q) ∨ L ∈ ({app P Q} : Set Termino)
      rcases hCasos with (hMP | hMQ) | hMigual
      · -- `M ∈ Sub(P)`: hipótesis de inducción sobre `P` y `Sub(P) ⊆ Sub(N)`.
        exact Or.inl (Or.inl (hipIndP hMP))
      · -- `M ∈ Sub(Q)`: hipótesis de inducción sobre `Q` y `Sub(Q) ⊆ Sub(N)`.
        exact Or.inl (Or.inr (hipIndQ hMQ))
      · -- `M ≡ (P Q) ≡ N`: `L ∈ Sub(M)` es directamente `L ∈ Sub(N)`.
        rw [hMigual] at hLM
        exact hLM
  | abs x P hipIndP =>
      -- Caso abstracción: `M ∈ Sub(P) ∨ M ≡ (λ x . P)`.
      have hCasos : M ∈ Sub P ∨ M = abs x P := hMN
      show L ∈ Sub P ∨ L ∈ ({abs x P} : Set Termino)
      rcases hCasos with hMP | hMigual
      · -- `M ∈ Sub(P)`: hipótesis de inducción sobre `P` y `Sub(P) ⊆ Sub(N)`.
        exact Or.inl (hipIndP hMP)
      · -- `M ≡ (λ x . P) ≡ N`: `L ∈ Sub(M)` es directamente `L ∈ Sub(N)`.
        rw [hMigual] at hLM
        exact hLM

/-- **Lema 7.6 de la tesis.** La relación de subtérmino es reflexiva y transitiva. -/
theorem lema_7_6 :
    (∀ M : Termino, M ∈ Sub M) ∧
    (∀ L M N : Termino, L ∈ Sub M → M ∈ Sub N → L ∈ Sub N) :=
  ⟨sub_reflexiva, fun _ _ _ hLM hMN => sub_transitiva hLM hMN⟩

/-! ### Cadenas finitas de pasos -/

/-- `Cadena R n M N`: existen `M₀, …, Mₙ` con `M₀ ≡ M`, `Mₙ ≡ N` y `R Mᵢ Mᵢ₊₁` para
todo `0 ≤ i < n`. Es la forma común de las Definiciones 7.27 y 7.28 de la tesis. -/
inductive Cadena {α : Type} (R : α → α → Prop) : Nat → α → α → Prop
  /-- La cadena vacía (`n = 0`): el término inicial es idéntico al final. -/
  | cero (M : α) : Cadena R 0 M M
  /-- Una cadena de `n` pasos seguida de un paso más. -/
  | paso {n : Nat} {M P N : α} : Cadena R n M P → R P N → Cadena R (n + 1) M N

namespace Cadena

variable {α : Type} {R S : α → α → Prop}

/-- Un solo paso es una cadena de longitud `1`. -/
theorem unPaso {M N : α} (h : R M N) : Cadena R 1 M N :=
  Cadena.paso (Cadena.cero M) h

/-- Concatenación: una cadena de `r` pasos de `L` a `M` seguida de una de `s` pasos de
`M` a `N` es una cadena de `r + s` pasos de `L` a `N`. -/
theorem concatenar {r s : Nat} {L M N : α}
    (hLM : Cadena R r L M) (hMN : Cadena R s M N) : Cadena R (r + s) L N := by
  -- Inducción sobre la segunda cadena.
  induction hMN with
  | cero M => exact hLM
  | paso _ hUltimo hipInd => exact Cadena.paso (hipInd hLM) hUltimo

/-- Anteponer un paso a una cadena. -/
theorem anteponer {n : Nat} {M P N : α}
    (hPrimero : R M P) (hResto : Cadena R n P N) : Cadena R (n + 1) M N := by
  induction hResto with
  | cero P => exact Cadena.unPaso hPrimero
  | paso _ hUltimo hipInd => exact Cadena.paso (hipInd hPrimero) hUltimo

/-- Si cada paso de `R` es un paso de `S`, una cadena de `R` es una cadena de `S`. -/
theorem cambiar {n : Nat} {M N : α} (hRS : ∀ a b, R a b → S a b)
    (h : Cadena R n M N) : Cadena S n M N := by
  induction h with
  | cero M => exact Cadena.cero M
  | paso _ hUltimo hipInd => exact Cadena.paso hipInd (hRS _ _ hUltimo)

/-- Inversión: si cada paso de `R` leído al revés es un paso de `S`, una cadena de `R`
de `M` a `N` se invierte en una cadena de `S` de `N` a `M`. -/
theorem invertir {n : Nat} {M N : α} (hRS : ∀ a b, R a b → S b a)
    (h : Cadena R n M N) : Cadena S n N M := by
  induction h with
  | cero M => exact Cadena.cero M
  | paso _ hUltimo hipInd => exact Cadena.anteponer (hRS _ _ hUltimo) hipInd

end Cadena

/-! ### Reducción β -/

section Beta

-- La sustitución `M[x := N]`, que aquí es un parámetro: `sust M x N`.
variable (sust : Termino → Var → Termino → Termino)

/-- β-reducción de un paso `M →β N` (Definición 7.24 de la tesis): la regla base
`(λ x . M) N →β M[x := N]` y las tres reglas de compatibilidad. -/
inductive PasoBeta : Termino → Termino → Prop
  /-- Base: `(λ x . M) N →β M[x := N]`. -/
  | base (x : Var) (M N : Termino) : PasoBeta (app (abs x M) N) (sust M x N)
  /-- Compatibilidad: si `M →β N`, entonces `M L →β N L`. -/
  | appIzq {M N : Termino} (L : Termino) : PasoBeta M N → PasoBeta (app M L) (app N L)
  /-- Compatibilidad: si `M →β N`, entonces `L M →β L N`. -/
  | appDer {M N : Termino} (L : Termino) : PasoBeta M N → PasoBeta (app L M) (app L N)
  /-- Compatibilidad: si `M →β N`, entonces `λ x . M →β λ x . N`. -/
  | abs (x : Var) {M N : Termino} : PasoBeta M N → PasoBeta (abs x M) (abs x N)

/-- Reducción β en cero o más pasos `M ↠β N` (Definición 7.27 de la tesis): existe
`n ≥ 0` y una cadena `M ≡ M₀ →β M₁ →β ⋯ →β Mₙ ≡ N`. -/
def ReduceBeta (M N : Termino) : Prop :=
  ∃ n : Nat, Cadena (PasoBeta sust) n M N

/-- `M ↔β N`: `M →β N` o `N →β M` (Nota 7.29 de la tesis). -/
def PasoConversion (M N : Termino) : Prop :=
  PasoBeta sust M N ∨ PasoBeta sust N M

/-- Conversión β `M =β N` (Definición 7.28 de la tesis): existe `n ≥ 0` y una cadena
`M ≡ M₀ ↔β M₁ ↔β ⋯ ↔β Mₙ ≡ N`. -/
def IgualBeta (M N : Termino) : Prop :=
  ∃ n : Nat, Cadena (PasoConversion sust) n M N

variable {sust}

/-! #### Lema 7.31 -/

/-- **Lema 7.31 (1) de la tesis.** `↠β` extiende `→β`. -/
theorem reduceBeta_de_paso {M N : Termino} (h : PasoBeta sust M N) :
    ReduceBeta sust M N :=
  -- Un paso es una secuencia de reducción con `k = 1`.
  ⟨1, Cadena.unPaso h⟩

/-- **Lema 7.31 (2), reflexividad.** `M ↠β M`. -/
theorem reduceBeta_reflexiva (M : Termino) : ReduceBeta sust M M :=
  -- Secuencia vacía, `k = 0`: `M₀ = M_k = M`.
  ⟨0, Cadena.cero M⟩

/-- **Lema 7.31 (2), transitividad.** Si `L ↠β M` y `M ↠β N`, entonces `L ↠β N`. -/
theorem reduceBeta_transitiva {L M N : Termino}
    (hLM : ReduceBeta sust L M) (hMN : ReduceBeta sust M N) : ReduceBeta sust L N := by
  -- Secuencia de `r ≥ 0` reducciones de `L` a `M`.
  obtain ⟨r, hCadenaLM⟩ := hLM
  -- Secuencia de `s ≥ 0` reducciones de `M` a `N`.
  obtain ⟨s, hCadenaMN⟩ := hMN
  -- Se concatenan: una secuencia de `r + s` pasos de `L` a `N`.
  exact ⟨r + s, Cadena.concatenar hCadenaLM hCadenaMN⟩

/-- **Lema 7.31 de la tesis.** `↠β` extiende `→β` y es reflexiva y transitiva. -/
theorem lema_7_31 :
    (∀ M N : Termino, PasoBeta sust M N → ReduceBeta sust M N) ∧
    (∀ M : Termino, ReduceBeta sust M M) ∧
    (∀ L M N : Termino, ReduceBeta sust L M → ReduceBeta sust M N → ReduceBeta sust L N) :=
  ⟨fun _ _ h => reduceBeta_de_paso h, reduceBeta_reflexiva,
    fun _ _ _ hLM hMN => reduceBeta_transitiva hLM hMN⟩

/-! #### Lema 7.32 -/

/-- **Lema 7.32 (1) de la tesis.** `=β` extiende `↠β` en ambas direcciones. -/
theorem igualBeta_de_reduceBeta {M N : Termino}
    (h : ReduceBeta sust M N ∨ ReduceBeta sust N M) : IgualBeta sust M N := by
  rcases h with hMN | hNM
  · -- Caso 1: `M ↠β N`. La misma cadena es una cadena de conversión: cada paso
    -- `Mᵢ →β Mᵢ₊₁` está permitido por la disyunción.
    obtain ⟨r, hCadena⟩ := hMN
    exact ⟨r, Cadena.cambiar (fun _ _ hPaso => Or.inl hPaso) hCadena⟩
  · -- Caso 2: `N ↠β M`. Se invierte cada paso de la cadena de `N` a `M`; cada paso
    -- inverso está permitido por la disyunción.
    obtain ⟨k, hCadena⟩ := hNM
    exact ⟨k, Cadena.invertir (fun _ _ hPaso => Or.inr hPaso) hCadena⟩

/-- **Lema 7.32 (2), reflexividad.** `M =β M`. -/
theorem igualBeta_reflexiva (M : Termino) : IgualBeta sust M M :=
  -- La cadena vacía.
  ⟨0, Cadena.cero M⟩

/-- **Lema 7.32 (2), simetría.** Si `M =β N`, entonces `N =β M`. -/
theorem igualBeta_simetrica {M N : Termino} (h : IgualBeta sust M N) :
    IgualBeta sust N M := by
  -- `M = P₀ ↔β P₁ ↔β ⋯ ↔β P_k = N`.
  obtain ⟨k, hCadena⟩ := h
  -- Invertir la secuencia produce una conversión de `N` a `M`, pues `↔β` es simétrica.
  exact ⟨k, Cadena.invertir (fun _ _ hPaso => Or.symm hPaso) hCadena⟩

/-- **Lema 7.32 (2), transitividad.** Si `L =β M` y `M =β N`, entonces `L =β N`. -/
theorem igualBeta_transitiva {L M N : Termino}
    (hLM : IgualBeta sust L M) (hMN : IgualBeta sust M N) : IgualBeta sust L N := by
  -- `L = L₀ ↔β ⋯ ↔β L_r = M` y `M = M₀ ↔β ⋯ ↔β M_s = N`.
  obtain ⟨r, hCadenaLM⟩ := hLM
  obtain ⟨s, hCadenaMN⟩ := hMN
  -- Al concatenar ambas se obtiene una conversión de `L` a `N`.
  exact ⟨r + s, Cadena.concatenar hCadenaLM hCadenaMN⟩

/-- **Lema 7.32 de la tesis.** `=β` extiende `↠β` en ambas direcciones y es una relación
de equivalencia. -/
theorem lema_7_32 :
    (∀ M N : Termino, ReduceBeta sust M N ∨ ReduceBeta sust N M → IgualBeta sust M N) ∧
    (∀ M : Termino, IgualBeta sust M M) ∧
    (∀ M N : Termino, IgualBeta sust M N → IgualBeta sust N M) ∧
    (∀ L M N : Termino, IgualBeta sust L M → IgualBeta sust M N → IgualBeta sust L N) :=
  ⟨fun _ _ h => igualBeta_de_reduceBeta h, igualBeta_reflexiva,
    fun _ _ h => igualBeta_simetrica h,
    fun _ _ _ hLM hMN => igualBeta_transitiva hLM hMN⟩

/-! ### Formas normales y confluencia -/

/-- Un redex es un término de la forma `(λ x . M) N` (Definición 7.25 de la tesis). -/
def EsRedex (R : Termino) : Prop :=
  ∃ (x : Var) (M N : Termino), R = app (abs x M) N

/-- `M` está en forma normal β si no contiene ningún redex (Definición 7.33 (1) de la
tesis): ningún subtérmino de `M` es un redex. -/
def FormaNormalBeta (M : Termino) : Prop :=
  ∀ R : Termino, R ∈ Sub M → ¬ EsRedex R

variable (sust) in
/-- `N` es una forma normal β de `M` (Definición 7.33 (2) de la tesis): `N` está en
forma normal β y `M =β N`. -/
def EsFormaNormalDe (N M : Termino) : Prop :=
  FormaNormalBeta N ∧ IgualBeta sust M N

variable (sust) in
/-- El enunciado del Teorema 7.37 de la tesis (Church–Rosser o confluencia): si
`M ↠β N₁` y `M ↠β N₂`, existe `L` con `N₁ ↠β L` y `N₂ ↠β L`. La tesis lo cita sin
demostración; aquí es una proposición que se toma como hipótesis, no un axioma. -/
def Confluente : Prop :=
  ∀ M N₁ N₂ : Termino, ReduceBeta sust M N₁ → ReduceBeta sust M N₂ →
    ∃ L : Termino, ReduceBeta sust N₁ L ∧ ReduceBeta sust N₂ L

/-- «Es decir, no se le pueden aplicar más pasos de reducción β» (Definición 7.33 (1)):
un término sin redexes no admite ningún paso `→β`. -/
theorem formaNormal_sin_paso {M N : Termino} (hPaso : PasoBeta sust M N) :
    ¬ FormaNormalBeta M := by
  -- Inducción sobre la derivación de `M →β N`.
  induction hPaso with
  | base x M N =>
      -- `M` mismo es un redex, y `M ∈ Sub(M)` por el Lema 7.6 (1).
      intro hNormal
      exact hNormal _ (sub_reflexiva _) ⟨x, M, N, rfl⟩
  | @appIzq M N L _ hipInd =>
      -- Un redex de `M` es un redex de `(M L)`, porque `Sub(M) ⊆ Sub(M L)`.
      intro hNormal
      exact hipInd (fun R hR => hNormal R (Or.inl (Or.inl hR)))
  | @appDer M N L _ hipInd =>
      -- Un redex de `M` es un redex de `(L M)`, porque `Sub(M) ⊆ Sub(L M)`.
      intro hNormal
      exact hipInd (fun R hR => hNormal R (Or.inl (Or.inr hR)))
  | @abs x M N _ hipInd =>
      -- Un redex de `M` es un redex de `(λ x . M)`, porque `Sub(M) ⊆ Sub(λ x . M)`.
      intro hNormal
      exact hipInd (fun R hR => hNormal R (Or.inl hR))

/-- Recíproco de `formaNormal_sin_paso`: un término que contiene un redex admite un
paso `→β`. Con el anterior, las dos lecturas de la Definición 7.33 (1) coinciden. -/
theorem paso_de_redex {M R : Termino} (hSub : R ∈ Sub M) (hRedex : EsRedex R) :
    ∃ N : Termino, PasoBeta sust M N := by
  -- Inducción estructural sobre `M`.
  induction M with
  | var y =>
      -- `R = y` no es un redex.
      have hR : R = var y := hSub
      obtain ⟨x, P, Q, hForma⟩ := hRedex
      rw [hR] at hForma
      exact Termino.noConfusion hForma
  | app P Q hipIndP hipIndQ =>
      have hCasos : (R ∈ Sub P ∨ R ∈ Sub Q) ∨ R = app P Q := hSub
      rcases hCasos with (hP | hQ) | hIgual
      · obtain ⟨P', hPaso⟩ := hipIndP hP
        exact ⟨app P' Q, PasoBeta.appIzq Q hPaso⟩
      · obtain ⟨Q', hPaso⟩ := hipIndQ hQ
        exact ⟨app P Q', PasoBeta.appDer P hPaso⟩
      · -- El propio `(P Q)` es el redex: se contrae con la regla base.
        obtain ⟨x, A, B, hForma⟩ := hRedex
        rw [hIgual] at hForma
        rw [hForma]
        exact ⟨sust A x B, PasoBeta.base x A B⟩
  | abs y P hipIndP =>
      have hCasos : R ∈ Sub P ∨ R = abs y P := hSub
      rcases hCasos with hP | hIgual
      · obtain ⟨P', hPaso⟩ := hipIndP hP
        exact ⟨abs y P', PasoBeta.abs y hPaso⟩
      · -- Una abstracción no es un redex.
        obtain ⟨x, A, B, hForma⟩ := hRedex
        rw [hIgual] at hForma
        exact Termino.noConfusion hForma

/-- Una forma normal solo se reduce (en cero pasos) a sí misma: si `N` está en forma
normal β y `N ↠β L`, entonces `N ≡ L`. Es el paso final del Corolario 7.44. -/
theorem formaNormal_reduce_igual {N L : Termino} (hNormal : FormaNormalBeta N)
    (hRed : ReduceBeta sust N L) : N = L := by
  obtain ⟨n, hCadena⟩ := hRed
  -- Inducción sobre la longitud de la cadena `N ≡ N₀ →β ⋯ →β Nₙ ≡ L`.
  induction hCadena with
  | cero N => rfl
  | @paso n N P L _ hUltimo hipInd =>
      -- Por hipótesis de inducción `N ≡ Nₙ₋₁`, y entonces `N →β L` contradice que `N`
      -- carece de redexes.
      have hNP : N = P := hipInd hNormal
      rw [← hNP] at hUltimo
      exact absurd hNormal (formaNormal_sin_paso hUltimo)

/-- **Corolario 7.43 de la tesis (Church–Rosser para la conversión).** Si `M =β N`,
existe `L` con `M ↠β L` y `N ↠β L`. El Teorema 7.37 entra como la hipótesis `hCR`. -/
theorem church_rosser_conversion (hCR : Confluente sust) {M N : Termino}
    (h : IgualBeta sust M N) :
    ∃ L : Termino, ReduceBeta sust M L ∧ ReduceBeta sust N L := by
  obtain ⟨k, hCadena⟩ := h
  -- Inducción sobre la longitud `k` de la cadena `M ≡ M₀ ↔β M₁ ↔β ⋯ ↔β M_k ≡ N`.
  induction hCadena with
  | cero M =>
      -- `k = 0`: basta `L ≡ M`.
      exact ⟨M, reduceBeta_reflexiva M, reduceBeta_reflexiva M⟩
  | @paso k M Mk1 Mk _ hUltimo hipInd =>
      -- La hipótesis de inducción da `L'` con `M ↠β L'` y `M_{k-1} ↠β L'`.
      obtain ⟨L', hML', hMk1L'⟩ := hipInd
      rcases hUltimo with hDirecto | hInverso
      · -- `M_{k-1} →β M_k`: el Teorema 7.37 aplicado a `M_{k-1}`, que se reduce a `L'`
        -- y a `M_k`, da `L` con `L' ↠β L` y `M_k ↠β L`.
        obtain ⟨L, hL'L, hMkL⟩ := hCR Mk1 L' Mk hMk1L' (reduceBeta_de_paso hDirecto)
        -- Componiendo, `M ↠β L' ↠β L`.
        exact ⟨L, reduceBeta_transitiva hML' hL'L, hMkL⟩
      · -- `M_k →β M_{k-1}`: entonces `M_k ↠β L'` y se toma `L ≡ L'`.
        exact ⟨L', hML', reduceBeta_transitiva (reduceBeta_de_paso hInverso) hMk1L'⟩

/-- **Corolario 7.44 de la tesis (unicidad de la forma normal).** Un λ-término tiene como
máximo una forma normal β. El Teorema 7.37 entra como la hipótesis `hCR`. -/
theorem unicidad_forma_normal (hCR : Confluente sust) {M N₁ N₂ : Termino}
    (h₁ : EsFormaNormalDe sust N₁ M) (h₂ : EsFormaNormalDe sust N₂ M) : N₁ = N₂ := by
  -- `M =β N₁` y `M =β N₂` con `N₁`, `N₂` en forma normal β.
  obtain ⟨hNormal₁, hMN₁⟩ := h₁
  obtain ⟨hNormal₂, hMN₂⟩ := h₂
  -- Por simetría y transitividad (Lema 7.32), `N₁ =β N₂`.
  have hN₁N₂ : IgualBeta sust N₁ N₂ :=
    igualBeta_transitiva (igualBeta_simetrica hMN₁) hMN₂
  -- Por el Corolario 7.43 existe `L` con `N₁ ↠β L` y `N₂ ↠β L`.
  obtain ⟨L, hN₁L, hN₂L⟩ := church_rosser_conversion hCR hN₁N₂
  -- Una forma normal solo se reduce a sí misma: `N₁ ≡ L` y `N₂ ≡ L`.
  have hIgual₁ : N₁ = L := formaNormal_reduce_igual hNormal₁ hN₁L
  have hIgual₂ : N₂ = L := formaNormal_reduce_igual hNormal₂ hN₂L
  -- De `N₁ ≡ L ≡ N₂` se concluye `N₁ ≡ N₂`.
  rw [hIgual₁, hIgual₂]

end Beta

/-! ### Axiomas usados por los cinco resultados principales -/

#print axioms lema_7_6
#print axioms lema_7_31
#print axioms lema_7_32
#print axioms church_rosser_conversion
#print axioms unicidad_forma_normal

end Thesis.Teoria.Lambda
