/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointPositive
import Categorification.TwoRep.CyclicDot

/-!
# Rouquier's `sl₂` data, without grading

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1
(R. Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023, §4.1.3) for a single colour `i`, in an
arbitrary bicategory whose Hom categories are preadditive. No grading, no finiteness of Hom spaces
and no condition on `End(1_λ)` is assumed.

**Data at one weight** (`RouqLoc adj₁ adj₂ x₁ x₂ τ h`). An object `b` of weight `h` with
neighbours `a` and `c`; 1-morphisms `E₁ : a ⟶ b` (Brundan's `E_i 1_{λ-α_i}`) and `E₂ : b ⟶ c`
(`E_i 1_λ`) with right adjoints `R₁`, `R₂` (`F_i 1_λ`, `F_i 1_{λ+α_i}`) and adjunctions `adj₁`,
`adj₂` (Brundan (1.5)); dots `x₁`, `x₂`; an upward crossing `τ` on `E₁ ≫ E₂`; the dot slides
(Brundan (1.2) for `i = j`, normalized as in `StrongSl2` with `r_i = 1`: the left strand of
`E₁ ≫ E₂` is `E₂`); and two-sided inverses of Rouquier's maps at `b`, as explicit inverse
components (`SumInvTo`, `SumInvFrom`), so that no biproducts are needed:

* `(σ, capD 0, …, capD (h-1)) : E F 1_λ → F E 1_λ ⊕ 1_λ^{⊕ h}` if `h ≥ 0` (Brundan (1.8));
* `(σ, cupD 0, …, cupD (-h-1)) : E F 1_λ ⊕ 1_λ^{⊕ -h} → F E 1_λ` if `h ≤ 0` (Brundan (1.9)),

where `σ = sig : R₁ ≫ E₁ ⟶ E₂ ≫ R₂` is the rightward crossing (Brundan (1.6),
`RightwardCrossing.sigma`), `capD n` the counit of `adj₁` with `n` dots on the upward strand and
`cupD n` the unit of `adj₂` with `n` dots.

**Data along a weight string** (`RouqSl2 C`): objects `obj r` of weight `n₀ + 2 r`, 1-morphisms
`E r : obj r ⟶ obj (r + 1)` with right adjoints `F r`, dots and crossings with the nilHecke
relations (Brundan (1.3), (1.4) for `i = j = k`) and data `loc r` at every object `obj (r + 1)`.

**Composition order.** As everywhere in this library, composition is written in Mathlib's
diagrammatic order: Brundan's `E_i F_i 1_λ` (first `F_i`, then `E_i`) at `b` is `R₁ ≫ E₁`, and
`F_i E_i 1_λ` is `E₂ ≫ R₂`.

## Main definitions

* `SumInvTo f g n`, `SumInvFrom f g n`: explicit two-sided inverses of `(f, g 0, …, g (n-1))`
  into (resp. out of) a direct sum `Y ⊕ Z^{⊕ n}`;
* `RouqLoc`, `RouqSl2`: the data above;
* `RouqLoc.sig`, `capD`, `cupD`, `dotD₁`, `dotD₂` (the downward dots, Brundan (1.12): the right
  mates of the dots);
* `RouqLoc.sigL` (Brundan's leftward crossing `σ'`, (1.14)–(1.16)), `cupN` (the components `η'_n`
  of the inverse of (1.8), Brundan's `♠`-cups (3.1)), `capN` (the components `ε'_n` of the inverse
  of (1.9), Brundan's `♣`-caps (3.2)), `cupL` (the leftward cup `η'`, (1.14) and (1.18)), `capL`
  (the leftward cap `ε'`, (1.15) and (1.17));
* `RouqLoc.ccw`, `RouqLoc.cw`: the dotted bubbles of all integer degrees (Brundan (3.8), (3.9)).

## Main statements

* Brundan Lemma 2.1: `unit_dotD₂`, `dotD₁_counit` ((2.1)); `sig_counit_pitchfork`,
  `unit_sig_pitchfork` ((2.2)); `sig_dot_sub`, `sig_dotD_sub` ((2.3));
* Brundan (3.3): `cupL_of_pos`, `capL_of_neg`;
* Brundan Lemma 3.1: `sig_sigL_of_nonneg`, `sigL_sig_of_nonpos` ((3.5)), `sigL_sig_of_nonneg`,
  `sig_sigL_of_nonpos` (the other composite is `-1`), `cupN_sig`, `sigL_capD`, `cupN_capD`,
  `cupL_sig`, `cupL_capD` ((3.6)) and `sig_capN`, `cupD_sigL`, `cupD_capN`, `sig_capL`,
  `cupD_capL` ((3.7)); the resulting values of the bubbles of low degree, `ccw_of_lt`,
  `ccw_self`, `cw_of_lt`, `cw_self`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u

/-! ## Explicit inverses of maps into and out of direct sums -/

section SumInv

variable {D : Type*} [Category D] [Preadditive D]

/-- **An explicit two-sided inverse of `(f, g 0, …, g (n-1)) : X → Y ⊕ Z^{⊕ n}`**: a row vector
`(f', g' 0, …, g' (n-1))` with `f f' + ∑ g_m g'_m = 1` and `g'_m g_{m'} = δ_{m m'}` etc. (composition
in diagrammatic order). Stated without biproducts. -/
structure SumInvTo {X Y Z : D} (f : X ⟶ Y) (g : ℕ → (X ⟶ Z)) (n : ℕ) where
  /-- The component `Y ⟶ X` of the inverse. -/
  f' : Y ⟶ X
  /-- The components `Z ⟶ X` of the inverse. -/
  g' : ℕ → (Z ⟶ X)
  total : f ≫ f' + ∑ m ∈ Finset.range n, g m ≫ g' m = 𝟙 X
  ff : f' ≫ f = 𝟙 Y
  fg : ∀ m, m < n → f' ≫ g m = 0
  gf : ∀ m, m < n → g' m ≫ f = 0
  gg : ∀ m m', m < n → m' < n → g' m ≫ g m' = if m = m' then 𝟙 Z else 0

/-- **An explicit two-sided inverse of `(f, g 0, …, g (n-1)) : Y ⊕ Z^{⊕ n} → X`**: a column vector
`(f', g' 0, …, g' (n-1))` with `f' f + ∑ g'_m g_m = 1` and `g_m g'_{m'} = δ_{m m'}` etc. -/
structure SumInvFrom {X Y Z : D} (f : Y ⟶ X) (g : ℕ → (Z ⟶ X)) (n : ℕ) where
  /-- The component `X ⟶ Y` of the inverse. -/
  f' : X ⟶ Y
  /-- The components `X ⟶ Z` of the inverse. -/
  g' : ℕ → (X ⟶ Z)
  total : f' ≫ f + ∑ m ∈ Finset.range n, g' m ≫ g m = 𝟙 X
  ff : f ≫ f' = 𝟙 Y
  fg : ∀ m, m < n → f ≫ g' m = 0
  gf : ∀ m, m < n → g m ≫ f' = 0
  gg : ∀ m m', m < n → m' < n → g m ≫ g' m' = if m = m' then 𝟙 Z else 0

/-- With no summands `Z`, `f` and `f'` are inverse. -/
theorem SumInvTo.comp_f'_of_zero {X Y Z : D} {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)}
    (I : SumInvTo f g 0) : f ≫ I.f' = 𝟙 X := by
  simpa using I.total

/-- With no summands `Z`, `f'` and `f` are inverse. -/
theorem SumInvFrom.f'_comp_of_zero {X Y Z : D} {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)}
    (I : SumInvFrom f g 0) : I.f' ≫ f = 𝟙 X := by
  simpa using I.total

/-- An inverse component is determined by its composites with all the original components. -/
theorem SumInvTo.eq_g' {X Y Z : D} {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n k : ℕ}
    (I : SumInvTo f g n) (hk : k < n) (c : Z ⟶ X) (hf : c ≫ f = 0)
    (hg : ∀ m, m < n → c ≫ g m = if k = m then 𝟙 Z else 0) : c = I.g' k := by
  calc c = c ≫ (f ≫ I.f' + ∑ m ∈ Finset.range n, g m ≫ I.g' m) := by
        rw [I.total, Category.comp_id]
    _ = ∑ m ∈ Finset.range n, (if k = m then 𝟙 Z else 0) ≫ I.g' m := by
        rw [Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc, hf,
          Limits.zero_comp, zero_add]
        apply Finset.sum_congr rfl
        intro m hm
        rw [← Category.assoc, hg m (Finset.mem_range.mp hm)]
    _ = I.g' k := by
        simp only [ite_comp, Category.id_comp, Limits.zero_comp]
        rw [Finset.sum_eq_single k]
        · simp
        · intro m _ hmk
          simp [Ne.symm hmk]
        · intro hkn
          exact False.elim (hkn (Finset.mem_range.mpr hk))

end SumInv

/-! ## Generic relations for the rightward crossing -/

namespace RouqSl2Generic

open AdditiveWhiskering

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b}

/-- The rightward crossing with an arbitrary 2-morphism `φ` in place of the upward crossing, as a
function of `φ`: it is additive. -/
theorem sigma_sub (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (φ ψ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma η₂ (φ - ψ) ε₁ =
      RightwardCrossing.sigma η₂ φ ε₁ - RightwardCrossing.sigma η₂ ψ ε₁ := by
  have hR : (φ - ψ) ▷ R₂ = φ ▷ R₂ - ψ ▷ R₂ := map_sub (whiskerRightAddHom _ _ R₂) φ ψ
  have hL : R₁ ◁ (φ ▷ R₂ - ψ ▷ R₂) = R₁ ◁ (φ ▷ R₂) - R₁ ◁ (ψ ▷ R₂) :=
    map_sub (whiskerLeftAddHom R₁ _ _) _ _
  simp only [RightwardCrossing.sigma_eq, hR, hL, Preadditive.comp_sub, Preadditive.sub_comp]

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The rightward crossing of the identity is the counit followed by the unit. -/
theorem sigma_id (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma η₂ (𝟙 _) ε₁ = ε₁ ≫ η₂ := by
  rw [RightwardCrossing.sigma_def]
  calc _ = 𝟙 _ ⊗≫ ((R₁ ≫ E₁) ◁ η₂ ≫ ε₁ ▷ (E₂ ≫ R₂)) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (ε₁ ▷ 𝟙 b ≫ 𝟙 b ◁ η₂) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = ε₁ ≫ η₂ := by bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- A dot on the upward strand of `E₁` before the crossing moves to the bottom of the rightward
crossing. -/
theorem sigma_comp_left (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b)
    (x₁ : E₁ ⟶ E₁) :
    RightwardCrossing.sigma η₂ (x₁ ▷ E₂ ≫ τ) ε₁ = R₁ ◁ x₁ ≫ RightwardCrossing.sigma η₂ τ ε₁ := by
  simp only [RightwardCrossing.sigma_def]
  calc _ = 𝟙 _ ⊗≫ ((R₁ ≫ E₁) ◁ η₂ ≫ (R₁ ◁ x₁) ▷ (E₂ ≫ R₂)) ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ ((R₁ ◁ x₁) ▷ 𝟙 b ≫ (R₁ ≫ E₁) ◁ η₂) ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by rw [← whisker_exchange]
    _ = _ := by bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- A dot on the upward strand of `E₂` after the crossing moves to the top of the rightward
crossing. -/
theorem sigma_comp_right (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b)
    (x₂ : E₂ ⟶ E₂) :
    RightwardCrossing.sigma η₂ (τ ≫ E₁ ◁ x₂) ε₁ = RightwardCrossing.sigma η₂ τ ε₁ ≫ x₂ ▷ R₂ := by
  simp only [RightwardCrossing.sigma_def]
  calc _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        ((R₁ ≫ E₁) ◁ (x₂ ▷ R₂) ≫ ε₁ ▷ (E₂ ≫ R₂)) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        (ε₁ ▷ (E₂ ≫ R₂) ≫ 𝟙 b ◁ (x₂ ▷ R₂)) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- A downward dot (the right mate `x₂'` of `x₂`) on the top of the rightward crossing moves to
the upward strand of `E₂` before the crossing. -/
theorem sigma_comp_conj (B₂ : E₂ ⊣ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b)
    (x₂ : E₂ ⟶ E₂) :
    RightwardCrossing.sigma B₂.unit τ ε₁ ≫ E₂ ◁ conjugateEquiv B₂ B₂ x₂ =
      RightwardCrossing.sigma B₂.unit (E₁ ◁ x₂ ≫ τ) ε₁ := by
  simp only [RightwardCrossing.sigma_def]
  calc _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ B₂.unit ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        (ε₁ ▷ (E₂ ≫ R₂) ≫ 𝟙 b ◁ (E₂ ◁ conjugateEquiv B₂ B₂ x₂)) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ B₂.unit ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        ((R₁ ≫ E₁) ◁ (E₂ ◁ conjugateEquiv B₂ B₂ x₂) ≫ ε₁ ▷ (E₂ ≫ R₂)) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ B₂.unit ⊗≫ R₁ ◁ (τ ▷ R₂ ≫ (E₁ ≫ E₂) ◁ conjugateEquiv B₂ B₂ x₂) ⊗≫
        ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ B₂.unit ⊗≫ R₁ ◁ ((E₁ ≫ E₂) ◁ conjugateEquiv B₂ B₂ x₂ ≫ τ ▷ R₂) ⊗≫
        ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ (B₂.unit ≫ E₂ ◁ conjugateEquiv B₂ B₂ x₂) ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ (B₂.unit ≫ x₂ ▷ R₂) ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        ε₁ ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by rw [unit_whiskerLeft_conjugateEquiv]
    _ = _ := by bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- A downward dot (the right mate `x₁'` of `x₁`) on the bottom of the rightward crossing moves to
the upward strand of `E₁` after the crossing. -/
theorem conj_comp_sigma (B₁ : E₁ ⊣ R₁) (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (x₁ : E₁ ⟶ E₁) :
    conjugateEquiv B₁ B₁ x₁ ▷ E₁ ≫ RightwardCrossing.sigma η₂ τ B₁.counit =
      RightwardCrossing.sigma η₂ (τ ≫ x₁ ▷ E₂) B₁.counit := by
  simp only [RightwardCrossing.sigma_def]
  calc _ = 𝟙 _ ⊗≫ ((conjugateEquiv B₁ B₁ x₁ ▷ E₁) ▷ 𝟙 b ≫ (R₁ ≫ E₁) ◁ η₂) ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        B₁.counit ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ ((R₁ ≫ E₁) ◁ η₂ ≫ (conjugateEquiv B₁ B₁ x₁ ▷ E₁) ▷ (E₂ ≫ R₂)) ⊗≫
        R₁ ◁ τ ▷ R₂ ⊗≫ B₁.counit ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫
        (conjugateEquiv B₁ B₁ x₁ ▷ ((E₁ ≫ E₂) ≫ R₂) ≫ R₁ ◁ (τ ▷ R₂)) ⊗≫
        B₁.counit ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫
        (R₁ ◁ (τ ▷ R₂) ≫ conjugateEquiv B₁ B₁ x₁ ▷ ((E₁ ≫ E₂) ≫ R₂)) ⊗≫
        B₁.counit ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        (conjugateEquiv B₁ B₁ x₁ ▷ E₁ ≫ B₁.counit) ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (R₁ ≫ E₁) ◁ η₂ ⊗≫ R₁ ◁ τ ▷ R₂ ⊗≫
        (R₁ ◁ x₁ ≫ B₁.counit) ▷ (E₂ ≫ R₂) ⊗≫ 𝟙 _ := by
        rw [conjugateEquiv_whiskerRight_counit]
    _ = _ := by bicategory

end RouqSl2Generic

/-! ## Rouquier's data at one weight -/

section Loc

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}

/-- **Rouquier's data at one weight** `h` (Brundan, Definition 1.1, one colour): the object `b` of
weight `h` with its neighbours `a` (weight `h - 2`) and `c` (weight `h + 2`), right adjunctions
`adj₁ : E₁ ⊣ R₁` (`E₁ = E_i 1_{λ-α_i}`) and `adj₂ : E₂ ⊣ R₂` (`E₂ = E_i 1_λ`), dots `x₁`, `x₂`,
and an upward crossing `τ` on `E₁ ≫ E₂` (Brundan's `E_i E_i 1_{λ-α_i}`), subject to the dot slides
(Brundan (1.2)) and the invertibility of Rouquier's map at `b` ((1.8) if `h ≥ 0`, (1.9) if
`h ≤ 0`), given by explicit inverse components. -/
structure RouqLoc (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂) (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂)
    (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (h : ℤ) where
  slide_left : E₁ ◁ x₂ ≫ τ - τ ≫ x₁ ▷ E₂ = 𝟙 _
  slide_right : τ ≫ E₁ ◁ x₂ - x₁ ▷ E₂ ≫ τ = 𝟙 _
  /-- Brundan (1.8): an inverse of `(σ, capD 0, …, capD (h - 1))` if `h ≥ 0`. -/
  invPos : 0 ≤ h →
    SumInvTo (RightwardCrossing.sigma adj₂.unit τ adj₁.counit)
      (fun n => R₁ ◁ powComp x₁ n ≫ adj₁.counit) h.toNat
  /-- Brundan (1.9): an inverse of `(σ, cupD 0, …, cupD (-h - 1))` if `h ≤ 0`. -/
  invNeg : h ≤ 0 →
    SumInvFrom (RightwardCrossing.sigma adj₂.unit τ adj₁.counit)
      (fun n => adj₂.unit ≫ powComp x₂ n ▷ R₂) (-h).toNat

namespace RouqLoc

variable {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

section Defs

/-- The rightward crossing `σ : E_i F_i 1_λ → F_i E_i 1_λ` (Brundan (1.6)). -/
def sig (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) : R₁ ≫ E₁ ⟶ E₂ ≫ R₂ :=
  RightwardCrossing.sigma adj₂.unit τ adj₁.counit

/-- The rightward cap with `n` dots `E_i F_i 1_λ → 1_λ`. -/
def capD (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (n : ℕ) : R₁ ≫ E₁ ⟶ 𝟙 b :=
  R₁ ◁ powComp x₁ n ≫ adj₁.counit

/-- The rightward cup with `n` dots `1_λ → F_i E_i 1_λ`. -/
def cupD (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (n : ℕ) : 𝟙 b ⟶ E₂ ≫ R₂ :=
  adj₂.unit ≫ powComp x₂ n ▷ R₂

/-- The inverse (1.8), `h ≥ 0`. -/
def ip (hh : 0 ≤ h) : SumInvTo L.sig L.capD h.toNat := L.invPos hh

/-- The inverse (1.9), `h ≤ 0`. -/
def iN (hh : h ≤ 0) : SumInvFrom L.sig L.cupD (-h).toNat := L.invNeg hh

/-- **The leftward crossing** `σ' : F_i E_i 1_λ → E_i F_i 1_λ` (Brundan (1.14)–(1.16)): minus the
component `F E → E F` of the inverse of Rouquier's map. -/
def sigL : E₂ ≫ R₂ ⟶ R₁ ≫ E₁ :=
  if hh : 0 ≤ h then -(L.ip hh).f' else -(L.iN (le_of_lt (not_le.mp hh))).f'

/-- The `♠`-cups `η'_n : 1_λ → E_i F_i 1_λ` (Brundan (1.14), (3.1)): the components `1_λ → E F` of the
inverse of (1.8), for `0 ≤ n < h` (zero if `h < 0`). -/
def cupN (n : ℕ) : 𝟙 b ⟶ R₁ ≫ E₁ :=
  if hh : 0 ≤ h then (L.ip hh).g' n else 0

/-- The `♣`-caps `ε'_n : F_i E_i 1_λ → 1_λ` (Brundan (1.15), (3.2)): the components `F E → 1_λ` of the
inverse of (1.9), for `0 ≤ n < -h` (zero if `h > 0`). -/
def capN (n : ℕ) : E₂ ≫ R₂ ⟶ 𝟙 b :=
  if hh : h ≤ 0 then (L.iN hh).g' n else 0

/-- **The leftward cup** `η' : 1_λ → E_i F_i 1_λ`: the last `♠`-cup if `h > 0` (Brundan (1.14),
(3.3)), and `σ' ∘ (cup with -h dots)` if `h ≤ 0` (Brundan (1.18)). -/
def cupL : 𝟙 b ⟶ R₁ ≫ E₁ :=
  if 0 < h then L.cupN (h - 1).toNat else L.cupD (-h).toNat ≫ L.sigL

/-- **The leftward cap** `ε' : F_i E_i 1_λ → 1_λ`: the last `♣`-cap if `h < 0` (Brundan (1.15),
(3.3)), and `-(cap with h dots) ∘ σ'` if `h ≥ 0` (Brundan (1.17)). -/
def capL : E₂ ≫ R₂ ⟶ 𝟙 b :=
  if h < 0 then L.capN (-h - 1).toNat else -(L.sigL ≫ L.capD h.toNat)

/-- **The counter-clockwise bubble with `k` dots** (`k ∈ ℤ`), an endomorphism of `1_λ`: for `k ≥ 0`
the leftward cup followed by the rightward cap with `k` dots; for `k < 0`, Brundan (3.8). -/
def ccw (k : ℤ) : 𝟙 b ⟶ 𝟙 b :=
  if 0 ≤ k then L.cupL ≫ L.capD k.toNat
  else if h - 1 < k then -(L.cupD (-h).toNat ≫ L.capN (-k - 1).toNat)
  else if k = h - 1 then 𝟙 _ else 0

/-- **The clockwise bubble with `k` dots** (`k ∈ ℤ`): for `k ≥ 0` the rightward cup with `k` dots
followed by the leftward cap; for `k < 0`, Brundan (3.9). -/
def cw (k : ℤ) : 𝟙 b ⟶ 𝟙 b :=
  if 0 ≤ k then L.cupD k.toNat ≫ L.capL
  else if -h - 1 < k then -(L.cupN (-k - 1).toNat ≫ L.capD h.toNat)
  else if k = -h - 1 then 𝟙 _ else 0

end Defs

section Basic

variable {L}

theorem sigL_of_nonneg (hh : 0 ≤ h) : L.sigL = -(L.ip hh).f' := by
  rw [sigL, dite_eq_left hh]

theorem sigL_of_nonpos (hh : h ≤ 0) : L.sigL = -(L.iN hh).f' := by
  rw [sigL]
  split_ifs with h'
  · congr 1
    calc (L.ip h').f' = (L.ip h').f' ≫ (L.sig ≫ (L.iN hh).f') := by
          rw [(L.iN hh).ff, Category.comp_id]
      _ = ((L.ip h').f' ≫ L.sig) ≫ (L.iN hh).f' := (Category.assoc _ _ _).symm
      _ = (L.iN hh).f' := by rw [(L.ip h').ff, Category.id_comp]
  · rfl

theorem cupN_of_nonneg (hh : 0 ≤ h) (n : ℕ) : L.cupN n = (L.ip hh).g' n := by
  rw [cupN, dite_eq_left hh]

theorem cupN_of_neg (hh : h < 0) (n : ℕ) : L.cupN n = 0 := by
  rw [cupN, dite_eq_right (not_le.mpr hh)]

theorem capN_of_nonpos (hh : h ≤ 0) (n : ℕ) : L.capN n = (L.iN hh).g' n := by
  rw [capN, dite_eq_left hh]

theorem capN_of_pos (hh : 0 < h) (n : ℕ) : L.capN n = 0 := by
  rw [capN, dite_eq_right (not_le.mpr hh)]

/-- Brundan (3.3): for `h > 0` the leftward cup is the last `♠`-cup. -/
theorem cupL_of_pos (hh : 0 < h) : L.cupL = L.cupN (h - 1).toNat := by
  rw [cupL, ite_eq_left hh]

/-- Brundan (1.18). -/
theorem cupL_of_nonpos (hh : h ≤ 0) : L.cupL = L.cupD (-h).toNat ≫ L.sigL := by
  rw [cupL, ite_eq_right (not_lt.mpr hh)]

/-- Brundan (3.3): for `h < 0` the leftward cap is the last `♣`-cap. -/
theorem capL_of_neg (hh : h < 0) : L.capL = L.capN (-h - 1).toNat := by
  rw [capL, ite_eq_left hh]

/-- Brundan (1.17). -/
theorem capL_of_nonneg (hh : 0 ≤ h) : L.capL = -(L.sigL ≫ L.capD h.toNat) := by
  rw [capL, ite_eq_right (not_lt.mpr hh)]

theorem ccw_of_nonneg {k : ℤ} (hk : 0 ≤ k) : L.ccw k = L.cupL ≫ L.capD k.toNat := by
  rw [ccw, ite_eq_left hk]

/-- Brundan (3.8), first case. -/
theorem ccw_of_neg_of_gt {k : ℤ} (hk : k < 0) (hk' : h - 1 < k) :
    L.ccw k = -(L.cupD (-h).toNat ≫ L.capN (-k - 1).toNat) := by
  rw [ccw, ite_eq_right (not_le.mpr hk), ite_eq_left hk']

/-- Brundan (3.8), second case. -/
theorem ccw_of_neg_of_eq {k : ℤ} (hk : k < 0) (hk' : k = h - 1) : L.ccw k = 𝟙 _ := by
  rw [ccw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_left hk']

/-- Brundan (3.8), third case. -/
theorem ccw_of_neg_of_lt {k : ℤ} (hk : k < 0) (hk' : k < h - 1) : L.ccw k = 0 := by
  rw [ccw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem cw_of_nonneg {k : ℤ} (hk : 0 ≤ k) : L.cw k = L.cupD k.toNat ≫ L.capL := by
  rw [cw, ite_eq_left hk]

/-- Brundan (3.9), first case. -/
theorem cw_of_neg_of_gt {k : ℤ} (hk : k < 0) (hk' : -h - 1 < k) :
    L.cw k = -(L.cupN (-k - 1).toNat ≫ L.capD h.toNat) := by
  rw [cw, ite_eq_right (not_le.mpr hk), ite_eq_left hk']

/-- Brundan (3.9), second case. -/
theorem cw_of_neg_of_eq {k : ℤ} (hk : k < 0) (hk' : k = -h - 1) : L.cw k = 𝟙 _ := by
  rw [cw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_left hk']

/-- Brundan (3.9), third case. -/
theorem cw_of_neg_of_lt {k : ℤ} (hk : k < 0) (hk' : k < -h - 1) : L.cw k = 0 := by
  rw [cw, ite_eq_right (not_le.mpr hk), ite_eq_right (by omega), ite_eq_right (by omega)]

end Basic

/-! ### Brundan, Lemma 3.1 -/

section Lemma31

variable {L}

/-- Brundan (3.5), `h ≥ 0`: on `E F 1_λ`, `σ' ∘ σ = ∑_{n < h} η'_n ∘ (cap with n dots) - 1`
(composition written in diagrammatic order). -/
theorem sig_sigL_of_nonneg (hh : 0 ≤ h) :
    L.sig ≫ L.sigL = ∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cupN n - 𝟙 _ := by
  have hs : ∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cupN n =
      ∑ n ∈ Finset.range h.toNat, L.capD n ≫ (L.ip hh).g' n :=
    Finset.sum_congr rfl fun n _ => by rw [cupN_of_nonneg hh]
  rw [hs, sigL_of_nonneg hh, Preadditive.comp_neg, ← (L.ip hh).total]
  abel

/-- For `h ≥ 0`, `σ ∘ σ' = -1` on `F E 1_λ`. -/
theorem sigL_sig_of_nonneg (hh : 0 ≤ h) : L.sigL ≫ L.sig = -𝟙 _ := by
  rw [sigL_of_nonneg hh, Preadditive.neg_comp, (L.ip hh).ff]

/-- Brundan (3.5), `h ≤ 0`: on `F E 1_λ`, `σ ∘ σ' = ∑_{n < -h} (cup with n dots) ∘ ε'_n - 1`. -/
theorem sigL_sig_of_nonpos (hh : h ≤ 0) :
    L.sigL ≫ L.sig = ∑ n ∈ Finset.range (-h).toNat, L.capN n ≫ L.cupD n - 𝟙 _ := by
  have hs : ∑ n ∈ Finset.range (-h).toNat, L.capN n ≫ L.cupD n =
      ∑ n ∈ Finset.range (-h).toNat, (L.iN hh).g' n ≫ L.cupD n :=
    Finset.sum_congr rfl fun n _ => by rw [capN_of_nonpos hh]
  rw [hs, sigL_of_nonpos hh, Preadditive.neg_comp, ← (L.iN hh).total]
  abel

/-- For `h ≤ 0`, `σ' ∘ σ = -1` on `E F 1_λ`. -/
theorem sig_sigL_of_nonpos (hh : h ≤ 0) : L.sig ≫ L.sigL = -𝟙 _ := by
  rw [sigL_of_nonpos hh, Preadditive.comp_neg, (L.iN hh).ff]

/-- Brundan (3.6): `σ ∘ η'_n = 0` for `0 ≤ n < h`. -/
theorem cupN_sig (hh : 0 ≤ h) {n : ℕ} (hn : n < h.toNat) : L.cupN n ≫ L.sig = 0 := by
  rw [cupN_of_nonneg hh, (L.ip hh).gf n hn]

/-- Brundan (3.6): `(cap with n dots) ∘ σ' = 0` for `0 ≤ n < h`. -/
theorem sigL_capD (hh : 0 ≤ h) {n : ℕ} (hn : n < h.toNat) : L.sigL ≫ L.capD n = 0 := by
  rw [sigL_of_nonneg hh, Preadditive.neg_comp, (L.ip hh).fg n hn, neg_zero]

/-- Brundan (3.6): `(cap with n dots) ∘ η'_m = δ_{m n}` for `0 ≤ m, n < h`. -/
theorem cupN_capD (hh : 0 ≤ h) {m n : ℕ} (hm : m < h.toNat) (hn : n < h.toNat) :
    L.cupN m ≫ L.capD n = if m = n then 𝟙 _ else 0 := by
  rw [cupN_of_nonneg hh, (L.ip hh).gg m n hm hn]

/-- Brundan (3.6) for the leftward cup: `σ ∘ η' = 0` if `h > 0`. -/
theorem cupL_sig (hh : 0 < h) : L.cupL ≫ L.sig = 0 := by
  rw [cupL_of_pos hh, cupN_sig hh.le (by omega)]

/-- Brundan (3.6) for the leftward cup: the counter-clockwise bubble with `n` dots is `δ_{n, h-1}`
for `0 ≤ n < h`. -/
theorem cupL_capD (hh : 0 < h) {n : ℕ} (hn : n < h.toNat) :
    L.cupL ≫ L.capD n = if (h - 1).toNat = n then 𝟙 _ else 0 := by
  rw [cupL_of_pos hh, cupN_capD hh.le (by omega) hn]

/-- Brundan (3.7): `ε'_n ∘ σ = 0` for `0 ≤ n < -h`. -/
theorem sig_capN (hh : h ≤ 0) {n : ℕ} (hn : n < (-h).toNat) : L.sig ≫ L.capN n = 0 := by
  rw [capN_of_nonpos hh, (L.iN hh).fg n hn]

/-- Brundan (3.7): `σ' ∘ (cup with n dots) = 0` for `0 ≤ n < -h`. -/
theorem cupD_sigL (hh : h ≤ 0) {n : ℕ} (hn : n < (-h).toNat) : L.cupD n ≫ L.sigL = 0 := by
  rw [sigL_of_nonpos hh, Preadditive.comp_neg, (L.iN hh).gf n hn, neg_zero]

/-- Brundan (3.7): `ε'_n ∘ (cup with m dots) = δ_{m n}` for `0 ≤ m, n < -h`. -/
theorem cupD_capN (hh : h ≤ 0) {m n : ℕ} (hm : m < (-h).toNat) (hn : n < (-h).toNat) :
    L.cupD m ≫ L.capN n = if m = n then 𝟙 _ else 0 := by
  rw [capN_of_nonpos hh, (L.iN hh).gg m n hm hn]

/-- Brundan (3.7) for the leftward cap: `ε' ∘ σ = 0` if `h < 0`. -/
theorem sig_capL (hh : h < 0) : L.sig ≫ L.capL = 0 := by
  rw [capL_of_neg hh, sig_capN hh.le (by omega)]

/-- Brundan (3.7) for the leftward cap: the clockwise bubble with `n` dots is `δ_{n, -h-1}` for
`0 ≤ n < -h`. -/
theorem cupD_capL (hh : h < 0) {n : ℕ} (hn : n < (-h).toNat) :
    L.cupD n ≫ L.capL = if n = (-h - 1).toNat then 𝟙 _ else 0 := by
  rw [capL_of_neg hh, cupD_capN hh.le hn (by omega)]

/-- Brundan (3.6), (3.8): for `h > 0` the counter-clockwise bubble with `k < h - 1` dots
vanishes and the one with `h - 1` dots is `1`. -/
theorem ccw_of_lt (hh : 0 < h) {k : ℤ} (hk : k < h - 1) : L.ccw k = 0 := by
  rcases lt_or_ge k 0 with hk0 | hk0
  · exact ccw_of_neg_of_lt hk0 hk
  · rw [ccw_of_nonneg hk0, cupL_capD hh (by omega), ite_eq_right (by omega)]

theorem ccw_self (hh : 0 < h) : L.ccw (h - 1) = 𝟙 _ := by
  rw [ccw_of_nonneg (by omega), cupL_capD hh (by omega), ite_eq_left rfl]

/-- Brundan (3.7), (3.9): for `h < 0` the clockwise bubble with `k < -h - 1` dots vanishes and
the one with `-h - 1` dots is `1`. -/
theorem cw_of_lt (hh : h < 0) {k : ℤ} (hk : k < -h - 1) : L.cw k = 0 := by
  rcases lt_or_ge k 0 with hk0 | hk0
  · exact cw_of_neg_of_lt hk0 hk
  · rw [cw_of_nonneg hk0, cupD_capL hh (by omega), ite_eq_right (by omega)]

theorem cw_self (hh : h < 0) : L.cw (-h - 1) = 𝟙 _ := by
  rw [cw_of_nonneg (by omega), cupD_capL hh (by omega), ite_eq_left rfl]

end Lemma31

/-! ### Brundan, Lemma 2.1 -/

section Lemma21

open RouqSl2Generic

/-- The downward dot `x'` on `R₁ = F_i 1_λ` (Brundan (1.12)): the right mate of `x₁`. -/
def dotD₁ (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) : R₁ ⟶ R₁ := conjugateEquiv adj₁ adj₁ x₁

/-- The downward dot `x'` on `R₂ = F_i 1_{λ+α_i}`: the right mate of `x₂`. -/
def dotD₂ (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) : R₂ ⟶ R₂ := conjugateEquiv adj₂ adj₂ x₂

/-- Brundan (2.1): a downward dot slides around the rightward cup. -/
theorem unit_dotD₂ : adj₂.unit ≫ E₂ ◁ L.dotD₂ = adj₂.unit ≫ x₂ ▷ R₂ :=
  unit_whiskerLeft_conjugateEquiv _ _

/-- Brundan (2.1): a downward dot slides around the rightward cap. -/
theorem dotD₁_counit : L.dotD₁ ▷ E₁ ≫ adj₁.counit = R₁ ◁ x₁ ≫ adj₁.counit :=
  conjugateEquiv_whiskerRight_counit _ _

/-- Brundan (2.2), the pitchfork relation for the rightward cap. -/
theorem sig_counit_pitchfork :
    L.sig ▷ E₂ ⊗≫ E₂ ◁ adj₂.counit = 𝟙 _ ⊗≫ R₁ ◁ τ ⊗≫ adj₁.counit ▷ E₂ ⊗≫ 𝟙 _ :=
  RightwardCrossing.pitchfork_cap _ _ _ _ adj₂.left_triangle

/-- Brundan (2.2), the pitchfork relation for the rightward cup. -/
theorem unit_sig_pitchfork :
    adj₁.unit ▷ E₁ ⊗≫ E₁ ◁ L.sig = 𝟙 _ ⊗≫ E₁ ◁ adj₂.unit ⊗≫ τ ▷ R₂ ⊗≫ 𝟙 _ :=
  RightwardCrossing.pitchfork_cup _ _ _ _ adj₁.left_triangle

variable [AdditiveWhiskering C]

/-- Brundan (2.3), upward strand: a dot passes through the rightward crossing up to the cap–cup
`E_i F_i 1_λ → 1_λ → F_i E_i 1_λ`. -/
theorem sig_dot_sub : L.sig ≫ x₂ ▷ R₂ - R₁ ◁ x₁ ≫ L.sig = adj₁.counit ≫ adj₂.unit := by
  rw [sig, ← sigma_comp_right, ← sigma_comp_left, ← sigma_sub, L.slide_right, sigma_id]

/-- Brundan (2.3), downward strand: a downward dot passes through the rightward crossing up to the
cap–cup. -/
theorem sig_dotD_sub :
    L.sig ≫ E₂ ◁ L.dotD₂ - L.dotD₁ ▷ E₁ ≫ L.sig = adj₁.counit ≫ adj₂.unit := by
  rw [sig, dotD₂, dotD₁, sigma_comp_conj, conj_comp_sigma, ← sigma_sub, L.slide_left, sigma_id]

end Lemma21

end RouqLoc

end Loc

/-! ## Rouquier's data along a weight string -/

/-- **Rouquier's `sl₂` data along a weight string** (Brundan, Definition 1.1, one colour), in a
bicategory with preadditive Hom categories: objects `obj r` of weight `n₀ + 2 r`, 1-morphisms
`E r : obj r ⟶ obj (r + 1)` and `F r : obj (r + 1) ⟶ obj r`, right adjunctions `E r ⊣ F r`, dots,
upward crossings with the nilHecke relations, and Rouquier's data `loc r` at each object
`obj (r + 1)` (the dot slides and the invertibility of (1.8)/(1.9)). -/
structure RouqSl2 (C : Type u) [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] where
  /-- The weight of `obj 0`. -/
  n₀ : ℤ
  /-- The object of weight `n₀ + 2 r`. -/
  obj : ℤ → C
  /-- `E_i 1_λ` for `λ = n₀ + 2 r`. -/
  E : ∀ r : ℤ, obj r ⟶ obj (r + 1)
  /-- `F_i 1_{λ + α_i}` for `λ = n₀ + 2 r`. -/
  F : ∀ r : ℤ, obj (r + 1) ⟶ obj r
  /-- The right adjunction `E ⊣ F` (Brundan (1.5)). -/
  adj : ∀ r : ℤ, E r ⊣ F r
  /-- The dot. -/
  x : ∀ r : ℤ, E r ⟶ E r
  /-- The upward crossing. -/
  τ : ∀ r : ℤ, E r ≫ E (r + 1) ⟶ E r ≫ E (r + 1)
  /-- Brundan (1.3) for `i = j`. -/
  τ_sq : ∀ r : ℤ, τ r ≫ τ r = 0
  /-- Brundan (1.4) for `i = j = k`. -/
  braid : ∀ r : ℤ, E r ◁ τ (r + 1) ≫
      ((α_ (E r) (E (r + 1)) (E (r + 1 + 1))).inv ≫ τ r ▷ E (r + 1 + 1) ≫
        (α_ (E r) (E (r + 1)) (E (r + 1 + 1))).hom) ≫ E r ◁ τ (r + 1) =
    ((α_ (E r) (E (r + 1)) (E (r + 1 + 1))).inv ≫ τ r ▷ E (r + 1 + 1) ≫
        (α_ (E r) (E (r + 1)) (E (r + 1 + 1))).hom) ≫ E r ◁ τ (r + 1) ≫
      ((α_ (E r) (E (r + 1)) (E (r + 1 + 1))).inv ≫ τ r ▷ E (r + 1 + 1) ≫
        (α_ (E r) (E (r + 1)) (E (r + 1 + 1))).hom)
  /-- Rouquier's data at `obj (r + 1)`: the dot slides (Brundan (1.2)) and the invertibility of
  (1.8)/(1.9). -/
  loc : ∀ r : ℤ, RouqLoc (adj r) (adj (r + 1)) (x r) (x (r + 1)) (τ r) (n₀ + 2 * (r + 1))

namespace RouqSl2

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] (S : RouqSl2 C)

/-- The weight `n₀ + 2 r` of `obj r`. -/
def wt (r : ℤ) : ℤ := S.n₀ + 2 * r

theorem wt_succ (r : ℤ) : S.wt (r + 1) = S.wt r + 2 := by
  unfold wt; ring

end RouqSl2

end Categorification.TwoRep
