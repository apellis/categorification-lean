/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouquierMaps

/-!
# The adjoint induction step at the weights `n ≥ 1`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.3–3.4: Lemma 3.8, the cap (3.6) and the proof of Proposition 3.9.

At a weight `n ≥ 1`, assuming (3.2) at the weights `> n` and the numerical shadow of (3.2)
(`StrongSl2.NumAdj`) at the weights `≥ n`, the left adjoint of `E 1_n` is `1_n F ⟨-n-1⟩`
(`StrongSl2.adjHyp_of_wt_pos`). The unit is CL's left cup: the inclusion of the top summand
`1_{n+2}⟨n+1⟩` of `E F 1_{n+2}`. The counit is CL's cap (3.6): the inclusion of `F E 1_n` into
`E F 1_n`, then `n` dots, then the counit of `E 1_{n-2} ⊣ R_{n-2}`. The zigzag for `E 1_n` is a
nonzero multiple of the identity:

* CL Lemma 3.8: whiskered by `E 1_n`, the unit followed by the inclusion of `F E 1_n` is a nonzero
  multiple of `(R τ) ∘ (u_n E)`, where `u_n` is the left cup at the weight `n`. Both lie in the
  one-dimensional space of CL Corollary 3.3 (`cor2`).
* The nilHecke relation `τ x₁ⁿ = x₂ⁿ τ - ∑ x₂ⁱ x₁ⁿ⁻¹⁻ⁱ` (`tau_comp_powComp`) turns the zigzag into
  `x₂ⁿ` composed with an endomorphism of `E 1_n` of degree `-2n` (zero, CL Lemma 3.1), minus `E 1_n`
  whiskered with bubbles. The only bubble of degree `0` is the one of CL Corollary 3.7, and it is
  nonzero.

Together with the weight `0` (`RouquierMaps.lean`) this gives (3.2) at every weight `≥ 0` under
(BB_w) (`StrongSl2.BBw.adjHyp_of_nonneg`), and by duality at every weight `≤ -2`
(`StrongSl2.BBw.adjHyp_of_le_neg_two`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

/-! ## Powers of an endomorphism and the nilHecke relation -/

section Pow

variable {D : Type*} [Category D]

/-- The `n`-th power `f ≫ ⋯ ≫ f` of an endomorphism. -/
def powComp {X : D} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => powComp f n ≫ f

@[simp] theorem powComp_zero {X : D} (f : X ⟶ X) : powComp f 0 = 𝟙 X := rfl

theorem powComp_succ {X : D} (f : X ⟶ X) (n : ℕ) : powComp f (n + 1) = powComp f n ≫ f := rfl

theorem powComp_smul {k : Type*} [Field k] [Preadditive D] [Linear k D] {X : D} (c : k)
    (f : X ⟶ X) : ∀ n : ℕ, powComp (c • f) n = c ^ n • powComp f n
  | 0 => by simp
  | n + 1 => by
    rw [powComp_succ, powComp_succ, powComp_smul c f n, Linear.smul_comp, Linear.comp_smul,
      smul_smul, pow_succ]

/-- **The nilHecke relation for powers**: if `p τ - τ q = 1` (diagrammatic order), then
`τ qⁿ = pⁿ τ - ∑_{i<n} pⁱ qⁿ⁻¹⁻ⁱ`. -/
theorem tau_comp_powComp [Preadditive D] {X : D} (τ p q : X ⟶ X) (hs : p ≫ τ - τ ≫ q = 𝟙 X) :
    ∀ n : ℕ, τ ≫ powComp q n =
      powComp p n ≫ τ - ∑ i ∈ Finset.range n, powComp p i ≫ powComp q (n - 1 - i)
  | 0 => by simp
  | n + 1 => by
    have h1 : τ ≫ q = p ≫ τ - 𝟙 X := by rw [← hs]; abel
    have h2 : ∀ i ∈ Finset.range n, (powComp p i ≫ powComp q (n - 1 - i)) ≫ q =
        powComp p i ≫ powComp q (n + 1 - 1 - i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Category.assoc, ← powComp_succ, show n - 1 - i + 1 = n + 1 - 1 - i by omega]
    calc τ ≫ powComp q (n + 1) = (τ ≫ powComp q n) ≫ q := by
          rw [powComp_succ, Category.assoc]
      _ = powComp p n ≫ (τ ≫ q) -
            ∑ i ∈ Finset.range n, (powComp p i ≫ powComp q (n - 1 - i)) ≫ q := by
          rw [tau_comp_powComp τ p q hs n, Preadditive.sub_comp, Category.assoc,
            Preadditive.sum_comp]
      _ = _ := by
          rw [h1, Finset.sum_congr rfl h2, Finset.sum_range_succ, powComp_succ p n]
          simp only [Preadditive.comp_sub, Category.comp_id, Category.assoc, Nat.add_sub_cancel,
            Nat.sub_self, powComp_zero]
          abel

end Pow

namespace RightwardCrossing

section Whisker

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C}

theorem whiskerLeft_powComp (f : a ⟶ b) {g : b ⟶ c} (x : g ⟶ g) :
    ∀ n : ℕ, f ◁ powComp x n = powComp (f ◁ x) n
  | 0 => by simp
  | n + 1 => by
    rw [powComp_succ, powComp_succ, Bicategory.whiskerLeft_comp, whiskerLeft_powComp f x n]

theorem powComp_whiskerRight {f : a ⟶ b} (x : f ⟶ f) (g : b ⟶ c) :
    ∀ n : ℕ, powComp x n ▷ g = powComp (x ▷ g) n
  | 0 => by simp
  | n + 1 => by
    rw [powComp_succ, powComp_succ, Bicategory.comp_whiskerRight, powComp_whiskerRight x g n]

variable {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b}

/-- A 2-morphism `u₀ : 𝟙 ⟶ R₁ ≫ E₁`, whiskered by `E₂`, commutes with endomorphisms of `E₂`. -/
theorem unit_whisker_naturality (u₀ : 𝟙 b ⟶ R₁ ≫ E₁) (y : E₂ ⟶ E₂) :
    ((λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom) ≫ R₁ ◁ E₁ ◁ y =
      y ≫ (λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom := by
  rw [Category.assoc, Category.assoc, ← associator_naturality_right, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc]

/-- The zigzag of a unit `u` and a counit of the form `ι ≫ (R₁ ◁ y) ≫ ε₁`, with the coherence
isomorphisms made explicit. -/
theorem rightZigzag_eq_comp (u : 𝟙 c ⟶ R₂ ≫ E₂) (ι : E₂ ≫ R₂ ⟶ R₁ ≫ E₁) (y : E₁ ⟶ E₁)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    (ρ_ E₂).inv ≫ rightZigzag u (ι ≫ R₁ ◁ y ≫ ε₁) ≫ (λ_ E₂).hom =
      ((ρ_ E₂).inv ≫ E₂ ◁ u ≫ (α_ E₂ R₂ E₂).inv ≫ ι ▷ E₂) ≫ (R₁ ◁ y) ▷ E₂ ≫ ε₁ ▷ E₂ ≫
        (λ_ E₂).hom := by
  rw [rightZigzag]; bicategory

/-- `u ⊗ ι` whiskered by `E₂` is split by `ι' ⊗ u'`. -/
theorem split_whiskerLeft_unit {X : b ⟶ b} (u : 𝟙 c ⟶ R₂ ≫ E₂) (u' : R₂ ≫ E₂ ⟶ 𝟙 c)
    (huu' : u ≫ u' = 𝟙 _) (ι : E₂ ≫ R₂ ⟶ X) (ι' : X ⟶ E₂ ≫ R₂) (hιι' : ι ≫ ι' = 𝟙 _) :
    ((ρ_ E₂).inv ≫ E₂ ◁ u ≫ (α_ E₂ R₂ E₂).inv ≫ ι ▷ E₂) ≫
      (ι' ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ u' ≫ (ρ_ E₂).hom) = 𝟙 E₂ := by
  calc _ = (ρ_ E₂).inv ≫ E₂ ◁ u ≫ (α_ E₂ R₂ E₂).inv ≫ (ι ≫ ι') ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫
        E₂ ◁ u' ≫ (ρ_ E₂).hom := by
        simp only [Category.assoc, Bicategory.comp_whiskerRight]
    _ = (ρ_ E₂).inv ≫ E₂ ◁ (u ≫ u') ≫ (ρ_ E₂).hom := by rw [hιι']; bicategory
    _ = 𝟙 E₂ := by rw [huu']; bicategory

/-- `u₀` whiskered by `E₂` is split by `u₀'` whiskered by `E₂`. -/
theorem split_unit_whiskerRight (u₀ : 𝟙 b ⟶ R₁ ≫ E₁) (u₀' : R₁ ≫ E₁ ⟶ 𝟙 b)
    (h : u₀ ≫ u₀' = 𝟙 _) :
    ((λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom) ≫
      ((α_ R₁ E₁ E₂).inv ≫ u₀' ▷ E₂ ≫ (λ_ E₂).hom) = 𝟙 E₂ := by
  calc _ = (λ_ E₂).inv ≫ (u₀ ≫ u₀') ▷ E₂ ≫ (λ_ E₂).hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Bicategory.comp_whiskerRight]
    _ = 𝟙 E₂ := by rw [h]; bicategory

end Whisker

section Core

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a}

open AdditiveWhiskering

theorem whiskerLeft_sub'' {d : C} (f : d ⟶ a) {g h : a ⟶ b} (η θ : g ⟶ h) :
    f ◁ (η - θ) = f ◁ η - f ◁ θ :=
  map_sub (whiskerLeftAddHom f g h) η θ

/-- **The core of CL's proof of Proposition 3.9.** With `U = u₀ E₂` (a cup `u₀ : 𝟙 ⟶ R₁ E₁`
whiskered by `E₂`), the composite `U`, crossing, `n` dots on the strand `E₁`, counit `ε₁` equals
`x₂ⁿ` composed with `U`, crossing, `ε₁`, minus the bubbles `u₀ ≫ x₁^{n-1-i} ≫ ε₁` whiskered by
`E₂` and composed with `x₂ⁱ` (nilHecke relation `x₂ τ - τ x₁ = 1`). -/
theorem cup_cross_dots_counit (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (x₁ : E₁ ⟶ E₁)
    (x₂ : E₂ ⟶ E₂) (hNH : E₁ ◁ x₂ ≫ τ - τ ≫ x₁ ▷ E₂ = 𝟙 _) (u₀ : 𝟙 b ⟶ R₁ ≫ E₁) (n : ℕ) :
    ((λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ τ ≫ (α_ R₁ E₁ E₂).inv) ≫
        (R₁ ◁ powComp x₁ n) ▷ E₂ ≫ ε₁ ▷ E₂ ≫ (λ_ E₂).hom =
      powComp x₂ n ≫ ((λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ τ ≫
          (α_ R₁ E₁ E₂).inv ≫ ε₁ ▷ E₂ ≫ (λ_ E₂).hom) -
        ∑ i ∈ Finset.range n, powComp x₂ i ≫
          ((λ_ E₂).inv ≫ (u₀ ≫ R₁ ◁ powComp x₁ (n - 1 - i) ≫ ε₁) ▷ E₂ ≫ (λ_ E₂).hom) := by
  have hU : ∀ (y : E₂ ⟶ E₂) {Z : b ⟶ c} (h : R₁ ≫ E₁ ≫ E₂ ⟶ Z),
      (λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ E₁ ◁ y ≫ h =
        y ≫ (λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ h := by
    intro y Z h
    have := congrArg (· ≫ h) (unit_whisker_naturality u₀ y)
    simpa only [Category.assoc] using this
  have hT : ∀ k : ℕ, (λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫
      R₁ ◁ (powComp x₁ k ▷ E₂) ≫ (α_ R₁ E₁ E₂).inv ≫ ε₁ ▷ E₂ ≫ (λ_ E₂).hom =
        (λ_ E₂).inv ≫ (u₀ ≫ R₁ ◁ powComp x₁ k ≫ ε₁) ▷ E₂ ≫ (λ_ E₂).hom := by
    intro k; bicategory
  have hN := tau_comp_powComp τ (E₁ ◁ x₂) (x₁ ▷ E₂) hNH n
  simp only [← whiskerLeft_powComp, ← powComp_whiskerRight] at hN
  have hsub : ∀ (η θ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂), R₁ ◁ (η - θ) = R₁ ◁ η - R₁ ◁ θ :=
    fun η θ => map_sub (whiskerLeftAddHom R₁ (E₁ ≫ E₂) (E₁ ≫ E₂)) η θ
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → (E₁ ≫ E₂ ⟶ E₁ ≫ E₂)),
      R₁ ◁ (∑ i ∈ s, f i) = ∑ i ∈ s, R₁ ◁ f i :=
    fun s f => map_sum (whiskerLeftAddHom R₁ (E₁ ≫ E₂) (E₁ ≫ E₂)) f s
  calc ((λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ τ ≫ (α_ R₁ E₁ E₂).inv) ≫
        (R₁ ◁ powComp x₁ n) ▷ E₂ ≫ ε₁ ▷ E₂ ≫ (λ_ E₂).hom
      = (λ_ E₂).inv ≫ u₀ ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ (τ ≫ powComp x₁ n ▷ E₂) ≫
          (α_ R₁ E₁ E₂).inv ≫ ε₁ ▷ E₂ ≫ (λ_ E₂).hom := by
        bicategory
    _ = _ := by
        rw [hN, hsub, hsum]
        simp only [Bicategory.whiskerLeft_comp, Preadditive.sub_comp, Preadditive.comp_sub,
          Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc, hU, hT]

end Core

end RightwardCrossing

/-! ## Graded-Hom bicategory facts -/

section GradedHomFacts

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

open GradedHomBicat GradedHomCat

theorem GradedHomBicat.isHomogeneous_powComp {a b : B} {f : a ⟶ b} {x : of₁ f ⟶ of₁ f} {d : ℤ}
    (hx : IsHomogeneous x d) : ∀ n : ℕ, IsHomogeneous (powComp x n) ((n : ℤ) * d)
  | 0 => (isHomogeneous_id _).of_eq (by simp)
  | n + 1 => ((GradedHomBicat.isHomogeneous_powComp hx n).comp hx rfl).of_eq (by push_cast; ring)

theorem GradedHomBicat.incl₂_add' {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) :
    incl₂ (η + θ) = incl₂ η + incl₂ θ :=
  (incl (a ⟶ b)).map_add

theorem GradedHomBicat.incl₂_sum' {a b : B} {f g : a ⟶ b} {ι : Type*} (s : Finset ι)
    (η : ι → (f ⟶ g)) : incl₂ (∑ i ∈ s, η i) = ∑ i ∈ s, incl₂ (η i) :=
  (incl (a ⟶ b)).map_sum η s

theorem GradedHomBicat.of₂_mk₀ {a b : B} {f g : a ⟶ b} (m₀ : ℤ) (h : m₀ = 0) (η : f ⟶ g) :
    of₂ m₀ (ShiftedHom.mk₀ m₀ h η) = incl₂ η := by
  subst h; rfl

theorem GradedHomBicat.of₂_shPow {a b : B} {f : a ⟶ b} {d : ℤ} (x : ShiftedHom f f d) :
    ∀ n : ℕ, of₂ ((n : ℤ) * d) (shPow x n) = powComp (of₂ d x) n
  | 0 => by
    rw [shPow, GradedHomBicat.of₂_mk₀, incl₂_id]; rfl
  | n + 1 => by
    rw [shPow, ← of₂_comp_of₂, GradedHomBicat.of₂_shPow x n]; rfl

end GradedHomFacts

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat RightwardCrossing

variable (S : StrongSl2 k B) [GradedBicategory.IsLinear B k]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem rightZigzag_smul {a b : GradedHomBicat B} {f : a ⟶ b} {g : b ⟶ a} (η : 𝟙 a ⟶ f ≫ g)
    (c : k) (eps : g ≫ f ⟶ 𝟙 b) : rightZigzag η (c • eps) = c • rightZigzag η eps := by
  simp only [rightZigzag, bicategoricalComp, GradedHomBicat.smul_whiskerRight, Linear.comp_smul]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem id_ne_zero_of_not_isZero {a b : B} {f : a ⟶ b} (h : ¬ IsZero f) : 𝟙 (of₁ f) ≠ 0 := by
  intro h0
  apply h
  refine (IsZero.iff_id_eq_zero _).2 (incl₂_injective ?_)
  change incl₂ (𝟙 f) = (incl _).map 0
  rw [incl₂_id, Functor.map_zero]
  exact h0

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **The degree-zero bubble of CL Corollary 3.7 is nonzero**: at the object `q + 1 + 1` of
weight `n ≥ 1`, given (3.2) at the weights `> n` and its numerical shadow at the weights `≥ n`,
the inclusion of the top summand `1_n⟨n-1⟩` of `E F 1_n`, followed by `n - 1` dots on `E 1_{n-2}`
and the counit of `E 1_{n-2} ⊣ R_{n-2}`, is a nonzero endomorphism of `1_n`. -/
theorem topBubble_ne_zero [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {q : ℤ}
    (hn : 1 ≤ S.wt (q + 1 + 1)) (hyp : ∀ r', q + 1 + 1 < r' → S.AdjHyp r')
    (hnum : ∀ r', q + 1 < r' → S.NumAdj r') (h2 : ¬ IsZero (𝟙 (S.obj (q + 1 + 1))))
    (e' : S.EFDecomp (q + 1)) :
    ((shiftIso₁ (𝟙 (S.obj (q + 1 + 1)))
        (1 * (((S.wt (q + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))) :
          of₁ (S.oneShift (q + 1) 0) ≅ 𝟙 (of (S.obj (q + 1 + 1)))).inv ≫
        incl₂ (ι e' 0) ≫ (S.rhoSourceIso (q + 1)).inv) ≫
      S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) ((S.wt (q + 1 + 1)).toNat - 1) ≫
        S.grCounit (q + 1) ≠ 0 := by
  have hn0 : 0 ≤ S.wt (q + 1 + 1) := by omega
  have hN : ((S.wt (q + 1 + 1)).toNat : ℤ) = S.wt (q + 1 + 1) := Int.toNat_of_nonneg hn0
  have ha : S.n₀ + 2 * (q + 1) + 1 = S.wt (q + 1 + 1) - 1 := by simp only [wt]; ring
  let ψ' := S.rhoSourceIso (q + 1)
  let tb : ℤ := 1 * (((S.wt (q + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))
  let osb : of₁ (S.oneShift (q + 1) 0) ≅ 𝟙 (of (S.obj (q + 1 + 1))) :=
    shiftIso₁ (𝟙 (S.obj (q + 1 + 1))) tb
  let u₀ : 𝟙 (of (S.obj (q + 1 + 1))) ⟶ S.grR (q + 1) ≫ S.grE (q + 1) :=
    osb.inv ≫ incl₂ (ι e' 0) ≫ ψ'.inv
  show u₀ ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) ((S.wt (q + 1 + 1)).toNat - 1) ≫
    S.grCounit (q + 1) ≠ 0
  set N := (S.wt (q + 1 + 1)).toNat with hNdef
  intro h0
  -- `E 1_{n-2}` is nonzero, so its counit is nonzero
  have hE₁ : ¬ IsZero (S.E (q + 1)) := by
    intro hz
    have hFE : IsZero (S.F (q + 1) ≫ S.E (q + 1)) := isZero_comp_right _ hz
    have h1 : IsZero (S.oneShift (q + 1) 0) := by
      rw [IsZero.iff_id_eq_zero, ← ι_π_self e' (j := 0) (by omega),
        hFE.eq_of_tgt (ι e' 0) 0, zero_comp]
    apply h2
    exact ((shiftFunctor _ (-(1 * (((S.wt (q + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))))).map_isZero
      h1).of_iso ((shiftFunctorCompIsoId _ _ _ (add_neg_cancel _)).app _).symm
  have hε0 := S.grCounit_ne_zero hE₁
  -- the decomposition of the identity of `E F 1_n`
  have htotB := total e'
  have htot' : ∑ j ∈ Finset.range N, incl₂ (π e' j) ≫ incl₂ (ι e' j) +
      incl₂ (πFE e') ≫ incl₂ (ιFE e') = 𝟙 (of₁ (S.F (q + 1) ≫ S.E (q + 1))) := by
    rw [← incl₂_id, ← htotB, GradedHomBicat.incl₂_add', GradedHomBicat.incl₂_sum']
    simp only [incl₂_comp]
    rfl
  have hψi : IsHomogeneous ψ'.inv (-(S.n₀ + 2 * (q + 1) + 1)) :=
    S.isHomogeneous_rhoSourceIso_inv (q + 1)
  have hM : ∀ j : ℕ, j < N → j ≠ N - 1 →
      incl₂ (ι e' j) ≫ ψ'.inv ≫ S.grCounit (q + 1) = 0 := by
    intro j hj hjm
    refine GradedHomBicat.eq_zero_of_isHomogeneous (k := k) (d := -(S.n₀ + 2 * (q + 1) + 1))
      ((isHomogeneous_incl₂ _).comp (hψi.comp (isHomogeneous_incl₂ _) rfl) (by ring)) ?_
    rw [oneShift, finrank_hom_shift_shift k _ _ (c := -(S.n₀ + 2 * (q + 1) + 1) -
      1 * ((((S.wt (q + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))) (by ring)]
    exact S.hom_neg _ _ (by omega)
  have hMFE : incl₂ (ιFE e') ≫ ψ'.inv ≫ S.grCounit (q + 1) = 0 := by
    refine GradedHomBicat.eq_zero_of_isHomogeneous (k := k) (d := -(S.n₀ + 2 * (q + 1) + 1))
      ((isHomogeneous_incl₂ _).comp (hψi.comp (isHomogeneous_incl₂ _) rfl) (by ring)) ?_
    rw [S.finrank_FE_one_of_numAdj (hnum (q + 1 + 1) (by omega))]
    exact S.lem1_neg (r₀ := q + 1 + 1) hn0 hyp (q + 1 + 1) le_rfl _ (by omega)
  have hsplit : ∀ {W : of (S.obj (q + 1 + 1)) ⟶ of (S.obj (q + 1 + 1))}
      (X : W ⟶ of₁ (S.F (q + 1) ≫ S.E (q + 1))),
      X ≫ ψ'.inv ≫ S.grCounit (q + 1) =
        X ≫ incl₂ (π e' (N - 1)) ≫ incl₂ (ι e' (N - 1)) ≫ ψ'.inv ≫ S.grCounit (q + 1) := by
    intro W X
    calc X ≫ ψ'.inv ≫ S.grCounit (q + 1) = X ≫ 𝟙 _ ≫ ψ'.inv ≫ S.grCounit (q + 1) := by
          rw [Category.id_comp]
      _ = X ≫ (∑ j ∈ Finset.range N, incl₂ (π e' j) ≫ incl₂ (ι e' j) +
            incl₂ (πFE e') ≫ incl₂ (ιFE e')) ≫ ψ'.inv ≫ S.grCounit (q + 1) := by
          rw [htot']
      _ = ∑ j ∈ Finset.range N, X ≫ incl₂ (π e' j) ≫ incl₂ (ι e' j) ≫ ψ'.inv ≫
            S.grCounit (q + 1) +
          X ≫ incl₂ (πFE e') ≫ incl₂ (ιFE e') ≫ ψ'.inv ≫ S.grCounit (q + 1) := by
          simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
            Preadditive.comp_sum, Category.assoc]
      _ = _ := by
          rw [hMFE, comp_zero, comp_zero, add_zero, Finset.sum_eq_single (N - 1)]
          · intro j hj hne
            rw [hM j (Finset.mem_range.1 hj) hne, comp_zero, comp_zero]
          · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hMm : incl₂ (ι e' (N - 1)) ≫ ψ'.inv ≫ S.grCounit (q + 1) ≠ 0 := by
    intro h
    apply hε0
    have := hsplit ψ'.hom
    rw [Iso.hom_inv_id_assoc, h, comp_zero, comp_zero] at this
    exact this
  -- the bubble of CL Corollary 3.7
  have hx' : ψ'.inv ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) (N - 1) =
      of₁ (S.F (q + 1)) ◁ powComp (S.grDotN (q + 1)) (N - 1) ≫ ψ'.inv := by
    simp only [ψ', rhoSourceIso, whiskerRightIso_inv]
    exact (whisker_exchange _ _).symm
  have hpow : of₁ (S.F (q + 1)) ◁ powComp (S.grDotN (q + 1)) (N - 1) =
      (((S.rQ⁻¹ : kˣ) : k) ^ (N - 1)) •
        of₂ (((N - 1 : ℕ) : ℤ) * 2) (shPow (S.dotEF (q + 1)) (N - 1)) := by
    rw [whiskerLeft_powComp, show of₁ (S.F (q + 1)) ◁ S.grDotN (q + 1) =
        ((S.rQ⁻¹ : kˣ) : k) • of₂ 2 (S.dotEF (q + 1)) from ?_, powComp_smul,
      ← GradedHomBicat.of₂_shPow]
    rw [show S.grDotN (q + 1) = ((S.rQ⁻¹ : kˣ) : k) • S.grDot (q + 1) from rfl,
      GradedHomBicat.whiskerLeft_smul, whiskerLeft_of₂]
    rfl
  have hbub : incl₂ (ι e' 0) ≫ of₂ (((N - 1 : ℕ) : ℤ) * 2) (shPow (S.dotEF (q + 1)) (N - 1)) ≫
      incl₂ (π e' (N - 1)) = of₂ (((N - 1 : ℕ) : ℤ) * 2) (bubble e') := by
    rw [incl₂_eq_of₂, incl₂_eq_of₂, of₂_comp_of₂ (shPow (S.dotEF (q + 1)) (N - 1))
      (ShiftedHom.mk₀ (0 : ℤ) rfl (π e' (N - 1))) (zero_add _),
      of₂_comp_of₂ _ _ (add_zero _), ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
    simp only [bubble, cupDots, Category.assoc]
    rfl
  have hD : DotNondeg e' := by
    by_cases hn1 : S.wt (q + 1 + 1) = 1
    · intro i hi
      exfalso
      omega
    · exact lemXind_of_numAdj (r := q) (by have := S.wt_add_one (q + 1); omega) hnum h2 e'
  have hbI : IsIso (bubble e') := cor_degz_bubbles_of_dotNondeg e' (by omega) hyp hD
  have hbI' : IsIso (of₂ (((N - 1 : ℕ) : ℤ) * 2) (bubble e')) := isIso_of₂ _ _
  have hc0 : (((S.rQ⁻¹ : kˣ) : k) ^ (N - 1)) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have key : u₀ ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) (N - 1) ≫ S.grCounit (q + 1) =
      (((S.rQ⁻¹ : kˣ) : k) ^ (N - 1)) • (osb.inv ≫
        of₂ (((N - 1 : ℕ) : ℤ) * 2) (bubble e') ≫ incl₂ (ι e' (N - 1)) ≫ ψ'.inv ≫
          S.grCounit (q + 1)) := by
    simp only [u₀, Category.assoc]
    rw [reassoc_of% hx']
    have := hsplit (incl₂ (ι e' 0) ≫ Bicategory.whiskerLeft (B := GradedHomBicat B)
      (of₁ (S.F (q + 1)))
      (powComp (D := of (S.obj (q + 1)) ⟶ of (S.obj (q + 1 + 1))) (S.grDotN (q + 1)) (N - 1)))
    simp only [Category.assoc] at this
    rw [this, hpow]
    simp only [Linear.smul_comp, Linear.comp_smul, reassoc_of% hbub]
  have h1 := (smul_eq_zero.1 (key.symm.trans h0)).resolve_left hc0
  have h1' := (cancel_epi _).1 (h1.trans comp_zero.symm)
  exact hMm ((cancel_epi _).1 (h1'.trans comp_zero.symm))

/-- **(3.2) at a weight `n ≥ 1`** (CL Proposition 3.9, the induction step): at the object
`q + 1 + 1` of weight `n ≥ 1`, given (3.2) at the weights `> n` and its numerical shadow at the
weights `≥ n`, `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`. -/
theorem adjHyp_of_wt_pos [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {q : ℤ}
    (hn : 1 ≤ S.wt (q + 1 + 1)) (hyp : ∀ r', q + 1 + 1 < r' → S.AdjHyp r')
    (hnum : ∀ r', q + 1 < r' → S.NumAdj r') : S.AdjHyp (q + 1 + 1) := by
  by_cases h2 : IsZero (𝟙 (S.obj (q + 1 + 1)))
  · exact S.adjHyp_of_isZero (Or.inl h2)
  by_cases h3 : IsZero (𝟙 (S.obj (q + 1 + 1 + 1)))
  · exact S.adjHyp_of_isZero (Or.inr h3)
  have hn0 : 0 ≤ S.wt (q + 1 + 1) := by omega
  have hend : finrank k (S.E (q + 1 + 1) ⟶ S.E (q + 1 + 1)) = 1 :=
    S.lem1_zero (r₀ := q + 1 + 1) hn0 hyp le_rfl h3
  have hE₂ : ¬ IsZero (S.E (q + 1 + 1)) := fun hz => by
    rw [finrank_hom_of_isZero_left k hz] at hend; exact zero_ne_one hend
  have hid₂ : 𝟙 (S.grE (q + 1 + 1)) ≠ 0 := id_ne_zero_of_not_isZero hE₂
  have ha : S.n₀ + 2 * (q + 1) + 1 = S.wt (q + 1 + 1) - 1 := by simp only [wt]; ring
  have hb : S.n₀ + 2 * (q + 1 + 1) + 1 = S.wt (q + 1 + 1) + 1 := by simp only [wt]
  have hN : ((S.wt (q + 1 + 1)).toNat : ℤ) = S.wt (q + 1 + 1) := Int.toNat_of_nonneg hn0
  have hT : ((S.wt (q + 1 + 1 + 1)).toNat : ℤ) = S.wt (q + 1 + 1) + 2 := by
    rw [Int.toNat_of_nonneg (by rw [S.wt_add_one]; omega), S.wt_add_one]
  obtain ⟨e'⟩ := S.exists_EFDecomp (r := q + 1) hn0
  obtain ⟨e⟩ := S.exists_EFDecomp (r := q + 1 + 1) (by rw [S.wt_add_one]; omega)
  -- the data of CL's left adjunction
  let ψ' := S.rhoSourceIso (q + 1)
  let ψ := S.rhoSourceIso (q + 1 + 1)
  let θ := S.rhoTargetIso (q + 1)
  let ic : S.grE (q + 1 + 1) ≫ S.grR (q + 1 + 1) ⟶ S.grR (q + 1) ≫ S.grE (q + 1) :=
    θ.hom ≫ incl₂ (ιFE e') ≫ ψ'.inv
  let ic' : S.grR (q + 1) ≫ S.grE (q + 1) ⟶ S.grE (q + 1 + 1) ≫ S.grR (q + 1 + 1) :=
    ψ'.hom ≫ incl₂ (πFE e') ≫ θ.inv
  let tc : ℤ := 1 * (((S.wt (q + 1 + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))
  let tb : ℤ := 1 * (((S.wt (q + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))
  let osc : of₁ (S.oneShift (q + 1 + 1) 0) ≅ 𝟙 (of (S.obj (q + 1 + 1 + 1))) :=
    shiftIso₁ (𝟙 (S.obj (q + 1 + 1 + 1))) tc
  let osb : of₁ (S.oneShift (q + 1) 0) ≅ 𝟙 (of (S.obj (q + 1 + 1))) :=
    shiftIso₁ (𝟙 (S.obj (q + 1 + 1))) tb
  let u : 𝟙 (of (S.obj (q + 1 + 1 + 1))) ⟶ S.grR (q + 1 + 1) ≫ S.grE (q + 1 + 1) :=
    osc.inv ≫ incl₂ (ι e 0) ≫ ψ.inv
  let u' : S.grR (q + 1 + 1) ≫ S.grE (q + 1 + 1) ⟶ 𝟙 (of (S.obj (q + 1 + 1 + 1))) :=
    ψ.hom ≫ incl₂ (π e 0) ≫ osc.hom
  let u₀ : 𝟙 (of (S.obj (q + 1 + 1))) ⟶ S.grR (q + 1) ≫ S.grE (q + 1) :=
    osb.inv ≫ incl₂ (ι e' 0) ≫ ψ'.inv
  let u₀' : S.grR (q + 1) ≫ S.grE (q + 1) ⟶ 𝟙 (of (S.obj (q + 1 + 1))) :=
    ψ'.hom ≫ incl₂ (π e' 0) ≫ osb.hom
  have hιι' : ic ≫ ic' = 𝟙 _ := by
    have : ιFE e' ≫ πFE e' = 𝟙 _ := by simp [ιFE, πFE]
    simp only [ic, ic', Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (incl₂ (ιFE e')), ← incl₂_comp, this, incl₂_id, Category.id_comp,
      Iso.hom_inv_id]
  have huu' : u ≫ u' = 𝟙 _ := by
    have : ι e 0 ≫ π e 0 = 𝟙 _ := ι_π_self e (by have := hT; omega)
    have h' : incl₂ (ι e 0) ≫ incl₂ (π e 0) = 𝟙 _ := by rw [← incl₂_comp, this, incl₂_id]
    simp only [u, u', Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h', Iso.inv_hom_id]
  have hu₀u₀' : u₀ ≫ u₀' = 𝟙 _ := by
    have : ι e' 0 ≫ π e' 0 = 𝟙 _ := ι_π_self e' (by have := hN; omega)
    have h' : incl₂ (ι e' 0) ≫ incl₂ (π e' 0) = 𝟙 _ := by rw [← incl₂_comp, this, incl₂_id]
    simp only [u₀, u₀', Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h', Iso.inv_hom_id]
  -- degrees
  have hι : IsHomogeneous ic 2 :=
    ((S.isHomogeneous_rhoTargetIso_hom (q + 1)).comp ((isHomogeneous_incl₂ _).comp
      (S.isHomogeneous_rhoSourceIso_inv (q + 1)) rfl) rfl).of_eq (by omega)
  have hu : IsHomogeneous u (-(2 * S.wt (q + 1 + 1) + 2)) :=
    (((shiftIso₁_inv_isHomogeneous (𝟙 _) tc : IsHomogeneous osc.inv (-tc))).comp ((isHomogeneous_incl₂ _).comp
      (S.isHomogeneous_rhoSourceIso_inv (q + 1 + 1)) rfl) rfl).of_eq (by
        simp only [tc]; push_cast; omega)
  have hu₀ : IsHomogeneous u₀ (-(2 * S.wt (q + 1 + 1) - 2)) :=
    (((shiftIso₁_inv_isHomogeneous (𝟙 _) tb : IsHomogeneous osb.inv (-tb))).comp ((isHomogeneous_incl₂ _).comp
      (S.isHomogeneous_rhoSourceIso_inv (q + 1)) rfl) rfl).of_eq (by
        simp only [tb]; push_cast; omega)
  -- CL Lemma 3.8
  let A : S.grE (q + 1 + 1) ⟶ (S.grR (q + 1) ≫ S.grE (q + 1)) ≫ S.grE (q + 1 + 1) :=
    (ρ_ _).inv ≫ S.grE (q + 1 + 1) ◁ u ≫ (α_ _ _ _).inv ≫ ic ▷ S.grE (q + 1 + 1)
  let Bm : S.grE (q + 1 + 1) ⟶ (S.grR (q + 1) ≫ S.grE (q + 1)) ≫ S.grE (q + 1 + 1) :=
    (λ_ _).inv ≫ u₀ ▷ S.grE (q + 1 + 1) ≫ (α_ _ _ _).hom ≫ S.grR (q + 1) ◁ S.grCross (q + 1) ≫
      (α_ _ _ _).inv
  have hA : IsHomogeneous A (-(2 * S.wt (q + 1 + 1))) :=
    ((isHomogeneous_rightUnitor_inv _).comp ((isHomogeneous_whiskerLeft _ hu).comp
      ((isHomogeneous_associator_inv _ _ _).comp (isHomogeneous_whiskerRight hι _) rfl) rfl)
        rfl).of_eq (by ring)
  have hBm : IsHomogeneous Bm (-(2 * S.wt (q + 1 + 1))) :=
    ((isHomogeneous_leftUnitor_inv _).comp ((isHomogeneous_whiskerRight hu₀ _).comp
      ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _
        (isHomogeneous_of₂ _ _)).comp (isHomogeneous_associator_inv _ _ _) rfl) rfl) rfl)
          rfl).of_eq (by ring)
  have hA0 : A ≠ 0 := by
    intro h0
    apply hid₂
    have := split_whiskerLeft_unit u u' huu' ic ic' hιι'
    change A ≫ _ = _ at this
    rw [h0, zero_comp] at this
    exact this.symm
  set U : S.grE (q + 1 + 1) ⟶ S.grR (q + 1) ≫ S.grE (q + 1) ≫ S.grE (q + 1 + 1) :=
    (λ_ _).inv ≫ u₀ ▷ S.grE (q + 1 + 1) ≫ (α_ _ _ _).hom with hUdef
  have hUP : ∀ y : S.grE (q + 1 + 1) ⟶ S.grE (q + 1 + 1),
      U ≫ S.grR (q + 1) ◁ S.grE (q + 1) ◁ y = y ≫ U := fun y =>
    unit_whisker_naturality u₀ y
  have hτ0 : U ≫ S.grR (q + 1) ◁ S.grCross (q + 1) ≠ 0 := by
    intro h0
    apply hid₂
    have hPT : S.grR (q + 1) ◁ S.grE (q + 1) ◁ S.grDotN (q + 1 + 1) ≫
          S.grR (q + 1) ◁ S.grCross (q + 1) -
        S.grR (q + 1) ◁ S.grCross (q + 1) ≫
          S.grR (q + 1) ◁ (S.grDotN (q + 1) ▷ S.grE (q + 1 + 1)) = 𝟙 _ := by
      rw [← Bicategory.whiskerLeft_comp, ← Bicategory.whiskerLeft_comp, ← whiskerLeft_sub'',
        S.grDotN_slide (q + 1), Bicategory.whiskerLeft_id]
    have hU0 : U = 0 := by
      calc U = U ≫ (S.grR (q + 1) ◁ S.grE (q + 1) ◁ S.grDotN (q + 1 + 1) ≫
            S.grR (q + 1) ◁ S.grCross (q + 1) -
          S.grR (q + 1) ◁ S.grCross (q + 1) ≫
            S.grR (q + 1) ◁ (S.grDotN (q + 1) ▷ S.grE (q + 1 + 1))) := by
            rw [hPT, Category.comp_id]
        _ = (U ≫ S.grR (q + 1) ◁ S.grE (q + 1) ◁ S.grDotN (q + 1 + 1)) ≫
              S.grR (q + 1) ◁ S.grCross (q + 1) -
            (U ≫ S.grR (q + 1) ◁ S.grCross (q + 1)) ≫
              S.grR (q + 1) ◁ (S.grDotN (q + 1) ▷ S.grE (q + 1 + 1)) := by
            simp only [Preadditive.comp_sub, Category.assoc]
        _ = 0 := by
            rw [hUP, Category.assoc, h0, comp_zero, zero_comp, sub_zero]
    have : U ≫ ((α_ _ _ _).inv ≫ u₀' ▷ S.grE (q + 1 + 1) ≫ (λ_ _).hom) = 𝟙 _ :=
      split_unit_whiskerRight u₀ u₀' hu₀u₀'
    rw [← this, hU0, zero_comp]
  have hBm0 : Bm ≠ 0 := fun h0 => hτ0 (by
    have : Bm ≫ (α_ _ _ _).hom = U ≫ S.grR (q + 1) ◁ S.grCross (q + 1) := by
      simp only [Bm, hUdef, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← this, h0, zero_comp])
  -- the one-dimensional space of CL Corollary 3.3
  have hdim : finrank k (S.E (q + 1 + 1) ⟶ (((S.F (q + 1))⟦S.n₀ + 2 * (q + 1) + 1⟧ ≫
      S.E (q + 1)) ≫ S.E (q + 1 + 1))⟦-(2 * S.wt (q + 1 + 1))⟧) = 1 := by
    rw [finrank_hom_congr_right k _ ((shiftFunctor _ (-(2 * S.wt (q + 1 + 1)))).mapIso
      (whiskerRightIso (whiskerRightShiftIso _ _ _) _ ≪≫ whiskerRightShiftIso _ _ _ ≪≫
        (shiftFunctor _ _).mapIso (α_ _ _ _)) ≪≫
      ((shiftFunctorAdd' _ (S.n₀ + 2 * (q + 1) + 1) (-(2 * S.wt (q + 1 + 1)))
        (-(S.wt (q + 1 + 1) + 1)) (by omega)).app _).symm)]
    exact S.cor2 (r₀ := q + 1 + 1) hn0 hyp (r := q + 1) le_rfl h3
  obtain ⟨a', ha'⟩ := hA
  obtain ⟨b', hb'⟩ := hBm
  have hb0 : b' ≠ 0 := fun h => hBm0 (by rw [hb', h]; exact homOf_zero _)
  have ha0 : a' ≠ 0 := fun h => hA0 (by rw [ha', h]; exact homOf_zero _)
  obtain ⟨l, hl⟩ := (finrank_eq_one_iff_of_nonzero' b' hb0).1 hdim a'
  have hl0 : l ≠ 0 := by rintro rfl; rw [zero_smul] at hl; exact ha0 hl.symm
  have hAB : A = l • Bm := by rw [ha', hb', ← hl, homOf_smul]
  -- the endomorphism of `E 1_n` of degree `-2n` vanishes (CL Lemma 3.1)
  have hK : (λ_ _).inv ≫ u₀ ▷ S.grE (q + 1 + 1) ≫ (α_ _ _ _).hom ≫
      S.grR (q + 1) ◁ S.grCross (q + 1) ≫ (α_ _ _ _).inv ≫
        S.grCounit (q + 1) ▷ S.grE (q + 1 + 1) ≫ (λ_ _).hom = 0 :=
    GradedHomBicat.eq_zero_of_isHomogeneous (d := -(2 * S.wt (q + 1 + 1)))
      (((isHomogeneous_leftUnitor_inv _).comp ((isHomogeneous_whiskerRight hu₀ _).comp
        ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _
          (isHomogeneous_of₂ _ _)).comp ((isHomogeneous_associator_inv _ _ _).comp
            ((isHomogeneous_whiskerRight (isHomogeneous_incl₂ _) _).comp
              (isHomogeneous_leftUnitor_hom _) rfl) rfl) rfl) rfl) rfl) rfl).of_eq (by ring))
      (S.lem1_neg (r₀ := q + 1 + 1) hn0 hyp (q + 1 + 1) le_rfl _ (by omega))
  -- the bubbles
  set N := (S.wt (q + 1 + 1)).toNat with hNdef
  have hdotN : IsHomogeneous (S.grDotN (q + 1)) 2 := (isHomogeneous_of₂ _ _).smul _
  have hbubH : ∀ j : ℕ, IsHomogeneous (u₀ ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) j ≫
      S.grCounit (q + 1)) (-(2 * S.wt (q + 1 + 1) - 2) + (j : ℤ) * 2) := fun j =>
    (hu₀.comp ((isHomogeneous_whiskerLeft _ (GradedHomBicat.isHomogeneous_powComp hdotN j)).comp
      (isHomogeneous_incl₂ _) rfl) rfl).of_eq (by ring)
  have hbub_lt : ∀ j : ℕ, j + 1 < N →
      u₀ ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) j ≫ S.grCounit (q + 1) = 0 :=
    fun j hj => GradedHomBicat.eq_zero_of_isHomogeneous (hbubH j) (S.hom_neg _ _ (by omega))
  have hbub_ne : u₀ ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) (N - 1) ≫
      S.grCounit (q + 1) ≠ 0 :=
    S.topBubble_ne_zero hn hyp hnum h2 e'
  obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous ((hbubH (N - 1)).of_eq (by
    have : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    rw [this]; omega))
  have hid0 : (𝟙 (𝟙 (S.obj (q + 1 + 1))) : _) ≠ 0 := fun h => h2 ((IsZero.iff_id_eq_zero _).2 h)
  obtain ⟨β, hβ⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).1 (S.hom_zero _ h2) g
  have hβg : u₀ ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) (N - 1) ≫ S.grCounit (q + 1) =
      β • 𝟙 _ := by
    rw [hg, ← hβ]
    change (incl _).map (β • 𝟙 _) = _
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]; rfl
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_smul] at hβg; exact hbub_ne hβg
  -- the zigzag
  have hcore := cup_cross_dots_counit (S.grCounit (q + 1)) (S.grCross (q + 1))
    (S.grDotN (q + 1)) (S.grDotN (q + 1 + 1)) (S.grDotN_slide (q + 1)) u₀ N
  have hval : (ρ_ _).inv ≫ rightZigzag u
      (ic ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) N ≫ S.grCounit (q + 1)) ≫ (λ_ _).hom =
        (-(l * β)) • 𝟙 _ := by
    rw [rightZigzag_eq_comp]
    change A ≫ _ = _
    rw [hAB, Linear.smul_comp]
    change l • (((λ_ _).inv ≫ u₀ ▷ S.grE (q + 1 + 1) ≫ (α_ _ _ _).hom ≫
      S.grR (q + 1) ◁ S.grCross (q + 1) ≫ (α_ _ _ _).inv) ≫ _) = _
    rw [hcore, hK, comp_zero, zero_sub, Finset.sum_eq_single 0]
    · simp only [powComp_zero, Category.id_comp, Nat.sub_zero, hβg,
        GradedHomBicat.smul_whiskerRight, Bicategory.id_whiskerRight, Linear.smul_comp,
        Linear.comp_smul, Category.id_comp, Iso.inv_hom_id, smul_neg, smul_smul, neg_smul]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [hbub_lt _ (by omega), GradedHomBicat.zero_whiskerRight, zero_comp, comp_zero,
        comp_zero]
    · intro h; rw [Finset.mem_range] at h; omega
  have hcc : IsHomogeneous (ic ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) N ≫
      S.grCounit (q + 1)) (2 * S.wt (q + 1 + 1) + 2) :=
    (hι.comp ((isHomogeneous_whiskerLeft _ (GradedHomBicat.isHomogeneous_powComp hdotN N)).comp
      (isHomogeneous_incl₂ _) rfl) rfl).of_eq (by omega)
  have hlβ : -(l * β) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hl0 hβ0)
  refine S.adjHyp_of_rightZigzag (q + 1 + 1) u ((-(l * β))⁻¹ •
    (ic ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) N ≫ S.grCounit (q + 1))) hu
    (hcc.smul _) ?_ hend
  rw [rightZigzag_smul]
  have : rightZigzag u (ic ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) N ≫
      S.grCounit (q + 1)) = (ρ_ _).hom ≫ ((-(l * β)) • 𝟙 _) ≫ (λ_ _).inv := by
    rw [← hval]; simp
  rw [this, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
    inv_mul_cancel₀ hlβ, one_smul]

/-- **CL Proposition 3.9 at every weight `n ≥ 0` under (BB_w)**, by decreasing induction from the
highest weight (`adjoint_induction`): the weight `0` is `BBw.adjHyp_of_wt_eq_zero`, the weights
`n ≥ 1` are `adjHyp_of_wt_pos`, with the numerical shadow of (3.2) from `BBw.numAdj`. -/
theorem BBw.adjHyp_of_nonneg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {S : StrongSl2 k B}
    (hS : S.BBw) : ∀ r, 0 ≤ S.wt r → S.AdjHyp r := by
  refine S.adjoint_induction fun r hr hyp => ?_
  rcases eq_or_lt_of_le hr with h0 | hpos
  · exact hS.adjHyp_of_wt_eq_zero h0.symm
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 + 1 := ⟨r - 2, by ring⟩
  exact S.adjHyp_of_wt_pos (by omega) hyp fun r' _ => hS.numAdj r'

/-- **CL Proposition 3.9 at every weight `n ≤ -2` under (BB_w)**, by the weights `≥ 0` of the dual
2-representation (`dual_adjHyp_iff`). -/
theorem BBw.adjHyp_of_le_neg_two [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {S : StrongSl2 k B}
    (hS : S.BBw) : ∀ r, S.wt r ≤ -2 → S.AdjHyp r := by
  intro r hr
  have h := hS.dual.adjHyp_of_nonneg (-(r + 1)) (by
    rw [dual_wt, show -(-(r + 1)) = r + 1 by ring, S.wt_add_one]; omega)
  rwa [dual_adjHyp_iff, show -(-(r + 1) + 1) = r by ring] at h

/-- **CL Proposition 3.9 under (BB_w) at every weight other than `-1`.** -/
theorem BBw.adjHyp_of_wt_ne_neg_one [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    {S : StrongSl2 k B} (hS : S.BBw) {r : ℤ} (hr : S.wt r ≠ -1) : S.AdjHyp r := by
  rcases le_or_gt 0 (S.wt r) with h | h
  · exact hS.adjHyp_of_nonneg r h
  · exact hS.adjHyp_of_le_neg_two r (by omega)

/-- **CL Proposition 3.9 under (BB_w) for a string of even weights**: if the weights are even,
`(E 1_n)_L ≅ 1_n F ⟨-n-1⟩` at every weight. -/
theorem BBw.adjHyp_of_even [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {S : StrongSl2 k B}
    (hS : S.BBw) (he : Even S.n₀) (r : ℤ) : S.AdjHyp r := by
  refine hS.adjHyp_of_wt_ne_neg_one fun h => ?_
  obtain ⟨m, hm⟩ := he
  simp only [wt] at h
  omega

end StrongSl2

end Categorification.TwoRep
