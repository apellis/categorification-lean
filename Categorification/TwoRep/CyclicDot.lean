/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FixedAdjunctionNeg
import Categorification.TwoRep.LemMain
import Categorification.TwoRep.LemMainNeg

/-!
# Cyclicity of the dot (CL Lemma 4.1) away from the weight `-1`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §4.2, Lemma 4.1 (`lem:A`, eq. (4.4)): the downward dot defined as the right
mate of the dot (under `E 1_n ⊣ R_n`) equals the one defined as the left mate (under the
normalized left adjunction `R_n ⊣ E 1_n`).

In the graded-Hom bicategory, with `B = grAdj : E ⊣ R` and `A : R ⊣ E` the left adjunction,
the statement is `conjugateEquiv B B x = (conjugateEquiv A A).symm x` for the dot `x`, i.e.
`y := conjugateEquiv A A (conjugateEquiv B B x) = x`. CL's proof, made explicit:

* `y` is homogeneous of degree `2` (`GradedHomBicat.isHomogeneous_conjugateEquiv`), so by
  Lemma 3.14 in degree `2` (`exists_decomp_deg_two` for `n ≥ 0`, from `lemMain_surjective`;
  `exists_decomp_deg_two_neg` for `n ≤ -2`, from `lemMainNeg_surjective_of_dotNondeg` and the
  lower half of Lemma 3.6) it is `bub(γ₀) + bub(γ₁) x` for bubbles `γ₀` of degree `2` and `γ₁`
  of degree `0` (CL (4.5));
* closing `y x^m` into a bubble with the unit of `A` and the counit of `B` (clockwise, `n ≥ 0`)
  gives the bubble of `x^{m+1}` (`unit_whiskerLeft_conj_conj_counit`, from the unit and counit
  compatibilities of conjugates), and bubbles absorb `γ₀`, `γ₁`
  (`unit_whiskerLeft_rightBub_counit`): with `β_j` the bubble with `j` dots,
  `β_{m+1} = β_m γ₀ + β_{m+1} γ₁` (CL (4.7));
* `β_j = 0` in negative degree and `β_{n+1} = 1` by the normalization (4.1), so `m = n` gives
  `γ₁ = 1` and `m = n + 1` gives `γ₀ = 0`.

For `n ≤ -2` the same argument runs with counter-clockwise bubbles (the unit of `B` and the
counit of `A`; `unit_conj_conj_whiskerRight_counit`, `unit_leftBub_whiskerRight_counit`) and the
normalization (4.1) for `n < -1`. The weight `n = -1` (CL's curl argument) is in
`CyclicDotNegOne.lean`.

## Main declarations

* generic: `conjugateEquiv_whiskerRight_counit`, `unit_whiskerLeft_conjugateEquiv`,
  `unit_whiskerLeft_conj_conj_counit`, `unit_conj_conj_whiskerRight_counit`,
  `unit_whiskerLeft_rightBub_counit`, `unit_leftBub_whiskerRight_counit`;
* `StrongSl2.grAdj`, `rightBub`, `leftBub`, `of₂_cisBubSh`, `of₂_cisBubRSh`, `of₂_dotsBub`,
  `of₂_dotsBubN`;
* `StrongSl2.cyclic_dotN` (`n ≥ 0`), `StrongSl2.cyclic_dotN_neg` (`n ≤ -2`);
* `StrongSl2.exists_cyclic_leftAdj`: **CL Lemma 4.1 at every weight `n ≠ -1`**.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b : C}

/-- The counit compatibility of a conjugate: for `l ⊣ r` and `α : l ⟶ l`, with
`β = conjugateEquiv adj adj α : r ⟶ r`, `β ▷ l ≫ ε = r ◁ α ≫ ε`. -/
theorem conjugateEquiv_whiskerRight_counit {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    (α : l ⟶ l) : conjugateEquiv adj adj α ▷ l ≫ adj.counit = r ◁ α ≫ adj.counit := by
  rw [conjugateEquiv_apply']
  calc _ = 𝟙 _ ⊗≫ r ◁ adj.unit ▷ l ⊗≫ r ◁ α ▷ r ▷ l ⊗≫
        (adj.counit ▷ (r ≫ l) ≫ 𝟙 b ◁ adj.counit) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ r ◁ adj.unit ▷ l ⊗≫ r ◁ α ▷ r ▷ l ⊗≫
        ((r ≫ l) ◁ adj.counit ≫ adj.counit ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ r ◁ adj.unit ▷ l ⊗≫ r ◁ (α ▷ (r ≫ l) ≫ l ◁ adj.counit) ⊗≫
        adj.counit := by
        bicategory
    _ = 𝟙 _ ⊗≫ r ◁ adj.unit ▷ l ⊗≫ r ◁ (l ◁ adj.counit ≫ α ▷ 𝟙 b) ⊗≫ adj.counit := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ r ◁ leftZigzag adj.unit adj.counit ⊗≫ r ◁ α ⊗≫ adj.counit := by
        bicategory
    _ = r ◁ α ≫ adj.counit := by
        rw [adj.left_triangle]
        bicategory

/-- The unit compatibility of a conjugate: for `l ⊣ r` and `α : l ⟶ l`, with
`β = conjugateEquiv adj adj α : r ⟶ r`, `η ≫ l ◁ β = η ≫ α ▷ r`. -/
theorem unit_whiskerLeft_conjugateEquiv {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    (α : l ⟶ l) : adj.unit ≫ l ◁ conjugateEquiv adj adj α = adj.unit ≫ α ▷ r := by
  rw [conjugateEquiv_apply']
  calc _ = 𝟙 _ ⊗≫ (adj.unit ▷ 𝟙 a ≫ (l ≫ r) ◁ adj.unit) ⊗≫ l ◁ r ◁ α ▷ r ⊗≫
        l ◁ adj.counit ▷ r ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 a ◁ adj.unit ≫ adj.unit ▷ (l ≫ r)) ⊗≫ l ◁ r ◁ α ▷ r ⊗≫
        l ◁ adj.counit ▷ r ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ adj.unit ⊗≫ ((adj.unit ▷ l ≫ (l ≫ r) ◁ α) ▷ r) ⊗≫
        l ◁ adj.counit ▷ r ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ adj.unit ⊗≫ ((𝟙 a ◁ α ≫ adj.unit ▷ l) ▷ r) ⊗≫
        l ◁ adj.counit ▷ r ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ adj.unit ⊗≫ α ▷ r ⊗≫ leftZigzag adj.unit adj.counit ▷ r ⊗≫ 𝟙 _ := by
        bicategory
    _ = adj.unit ≫ α ▷ r := by
        rw [adj.left_triangle]
        bicategory

/-- **The bubble of the left mate of the right mate.** For adjunctions `A : R ⊣ E` and
`B : E ⊣ R` and `x z : E ⟶ E`, closing `conjugateEquiv A A (conjugateEquiv B B x) ≫ z` into a
bubble with the unit of `A` and the counit of `B` gives the bubble of `z ≫ x`. -/
theorem unit_whiskerLeft_conj_conj_counit {E : a ⟶ b} {R : b ⟶ a} (A : R ⊣ E) (B : E ⊣ R)
    (x z : E ⟶ E) :
    A.unit ≫ R ◁ (conjugateEquiv A A (conjugateEquiv B B x) ≫ z) ≫ B.counit =
      A.unit ≫ R ◁ (z ≫ x) ≫ B.counit := by
  calc _ = (A.unit ≫ R ◁ conjugateEquiv A A (conjugateEquiv B B x)) ≫ R ◁ z ≫ B.counit := by
        rw [Bicategory.whiskerLeft_comp]; simp only [Category.assoc]
    _ = (A.unit ≫ conjugateEquiv B B x ▷ E) ≫ R ◁ z ≫ B.counit := by
        rw [unit_whiskerLeft_conjugateEquiv]
    _ = A.unit ≫ R ◁ z ≫ conjugateEquiv B B x ▷ E ≫ B.counit := by
        rw [Category.assoc, ← Category.assoc (conjugateEquiv B B x ▷ E), ← whisker_exchange,
          Category.assoc]
    _ = A.unit ≫ R ◁ z ≫ R ◁ x ≫ B.counit := by
        rw [conjugateEquiv_whiskerRight_counit]
    _ = _ := by
        rw [Bicategory.whiskerLeft_comp]; simp only [Category.assoc]

/-- An endomorphism of the identity placed on the right of `E` commutes with every
endomorphism of `E` (interchange). -/
theorem rightBub_comm {E : a ⟶ b} (γ : 𝟙 b ⟶ 𝟙 b) (w : E ⟶ E) :
    ((ρ_ E).inv ≫ E ◁ γ ≫ (ρ_ E).hom) ≫ w = w ≫ ((ρ_ E).inv ≫ E ◁ γ ≫ (ρ_ E).hom) := by
  calc _ = 𝟙 _ ⊗≫ (E ◁ γ ≫ w ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (w ▷ 𝟙 b ≫ E ◁ γ) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        bicategory

/-- **Bubbles absorb endomorphisms of the identity on the outside**: for `u : 𝟙 ⟶ R ≫ E`,
`ε : R ≫ E ⟶ 𝟙`, `γ : 𝟙 b ⟶ 𝟙 b` and `w : E ⟶ E`, the bubble of `γ` placed on the right of `E`,
followed by `w`, is the bubble of `w` times `γ`. -/
theorem unit_whiskerLeft_rightBub_counit {E : a ⟶ b} {R : b ⟶ a} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) (γ : 𝟙 b ⟶ 𝟙 b) (w : E ⟶ E) :
    u ≫ R ◁ (((ρ_ E).inv ≫ E ◁ γ ≫ (ρ_ E).hom) ≫ w) ≫ eps = (u ≫ R ◁ w ≫ eps) ≫ γ := by
  rw [rightBub_comm]
  calc _ = 𝟙 _ ⊗≫ u ⊗≫ R ◁ w ⊗≫ ((R ≫ E) ◁ γ ≫ eps ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ u ⊗≫ R ◁ w ⊗≫ (eps ▷ 𝟙 b ≫ 𝟙 b ◁ γ) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = (u ≫ R ◁ w ≫ eps) ≫ γ := by
        bicategory

/-- An endomorphism of the identity placed on the left of `E` commutes with every
endomorphism of `E` (interchange). -/
theorem leftBub_comm {E : a ⟶ b} (γ : 𝟙 a ⟶ 𝟙 a) (w : E ⟶ E) :
    ((λ_ E).inv ≫ γ ▷ E ≫ (λ_ E).hom) ≫ w = w ≫ ((λ_ E).inv ≫ γ ▷ E ≫ (λ_ E).hom) := by
  calc _ = 𝟙 _ ⊗≫ (γ ▷ E ≫ 𝟙 a ◁ w) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 a ◁ w ≫ γ ▷ E) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = _ := by
        bicategory

/-- The mirror of `unit_whiskerLeft_rightBub_counit`: a counter-clockwise bubble absorbs an
endomorphism of the identity placed on the left of `E`. -/
theorem unit_leftBub_whiskerRight_counit {E : a ⟶ b} {R : b ⟶ a} (η : 𝟙 a ⟶ E ≫ R)
    (c : E ≫ R ⟶ 𝟙 a) (γ : 𝟙 a ⟶ 𝟙 a) (w : E ⟶ E) :
    η ≫ (((λ_ E).inv ≫ γ ▷ E ≫ (λ_ E).hom) ≫ w) ▷ R ≫ c = (η ≫ w ▷ R ≫ c) ≫ γ := by
  rw [leftBub_comm]
  calc _ = 𝟙 _ ⊗≫ η ⊗≫ w ▷ R ⊗≫ (γ ▷ (E ≫ R) ≫ 𝟙 a ◁ c) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ η ⊗≫ w ▷ R ⊗≫ (𝟙 a ◁ c ≫ γ ▷ 𝟙 a) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = (η ≫ w ▷ R ≫ c) ≫ γ := by
        bicategory

/-- The mirror of `unit_whiskerLeft_conj_conj_counit`: closing with the unit of `B : E ⊣ R` and
the counit of `A : R ⊣ E` (a counter-clockwise bubble). -/
theorem unit_conj_conj_whiskerRight_counit {E : a ⟶ b} {R : b ⟶ a} (A : R ⊣ E) (B : E ⊣ R)
    (x z : E ⟶ E) :
    B.unit ≫ (z ≫ conjugateEquiv A A (conjugateEquiv B B x)) ▷ R ≫ A.counit =
      B.unit ≫ (x ≫ z) ▷ R ≫ A.counit := by
  calc _ = B.unit ≫ z ▷ R ≫ conjugateEquiv A A (conjugateEquiv B B x) ▷ R ≫ A.counit := by
        rw [Bicategory.comp_whiskerRight]; simp only [Category.assoc]
    _ = B.unit ≫ z ▷ R ≫ E ◁ conjugateEquiv B B x ≫ A.counit := by
        rw [conjugateEquiv_whiskerRight_counit]
    _ = B.unit ≫ E ◁ conjugateEquiv B B x ≫ z ▷ R ≫ A.counit := by
        rw [← Category.assoc (z ▷ R), ← whisker_exchange, Category.assoc]
    _ = B.unit ≫ x ▷ R ≫ z ▷ R ≫ A.counit := by
        rw [← Category.assoc B.unit, unit_whiskerLeft_conjugateEquiv, Category.assoc]
    _ = _ := by
        rw [Bicategory.comp_whiskerRight]; simp only [Category.assoc]

end Generic

/-! ## Conjugates in the graded-Hom bicategory -/

section GradedHom

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

namespace GradedHomBicat

open GradedHomCat

/-- **Conjugation preserves homogeneity**, if the unit and the counit used are homogeneous of
opposite degrees. -/
theorem isHomogeneous_conjugateEquiv {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) {d : ℤ} (hu : IsHomogeneous adj₂.unit d)
    (hc : IsHomogeneous adj₁.counit (-d)) {α : l ⟶ l} {e : ℤ} (hα : IsHomogeneous α e) :
    IsHomogeneous (conjugateEquiv adj₁ adj₂ α) e := by
  rw [conjugateEquiv_apply']
  have h1 : IsHomogeneous (ρ_ r).inv 0 := isHomogeneous_incl₂ (ρ_ r.as).inv
  have h2 : IsHomogeneous (α_ r l r).inv 0 := isHomogeneous_incl₂ (α_ r.as l.as r.as).inv
  have h3 : IsHomogeneous (λ_ r).hom 0 := isHomogeneous_incl₂ (λ_ r.as).hom
  exact (h1.comp ((isHomogeneous_whiskerLeft r hu).comp ((isHomogeneous_whiskerLeft r
    (isHomogeneous_whiskerRight hα r)).comp (h2.comp ((isHomogeneous_whiskerRight hc r).comp h3
      rfl) rfl) rfl) rfl) rfl).of_eq (by ring)

end GradedHomBicat

end GradedHom

/-! ## Lemma 4.1 for `n ≥ 0` -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat Module
open KrullSchmidtCat (HomFinite)

variable (S : StrongSl2 k B)

/-- The adjunction `E 1_n ⊣ R_n` (`StrongSl2.adj`) in the graded-Hom bicategory, with unit
`grUnit` and counit `grCounit`. -/
def grAdj (r : ℤ) : S.grE r ⊣ S.grR r := GradedHomBicat.mapAdjunction (S.adj r)

@[simp] theorem grAdj_unit (r : ℤ) : (S.grAdj r).unit = S.grUnit r := rfl

@[simp] theorem grAdj_counit (r : ℤ) : (S.grAdj r).counit = S.grCounit r := rfl

/-- A bubble `γ : 𝟙 ⟶ 𝟙` placed on the right (target side) of `E 1_n`. -/
def rightBub {r : ℤ} (γ : 𝟙 (of (S.obj (r + 1))) ⟶ 𝟙 (of (S.obj (r + 1)))) :
    S.grE r ⟶ S.grE r :=
  (ρ_ (S.grE r)).inv ≫ S.grE r ◁ γ ≫ (ρ_ (S.grE r)).hom

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
/-- `cisBub` in the graded-Hom bicategory. -/
theorem of₂_cisBubSh {a b : B} (X : a ⟶ b) {d : ℤ} (g : 𝟙 b ⟶ (𝟙 b)⟦d⟧) :
    of₂ d (cisBubSh X g) =
      (ρ_ (of₁ X)).inv ≫ of₁ X ◁ (of₂ d g : 𝟙 (of b) ⟶ 𝟙 (of b)) ≫ (ρ_ (of₁ X)).hom := by
  rw [rightUnitor_inv_eq, rightUnitor_hom_eq, whiskerLeft_of₂, incl₂_eq_of₂,
    incl₂_eq_of₂, of₂_comp_of₂ _ _ (zero_add d), of₂_comp_of₂ _ _ (add_zero d),
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  congr 1
  simp only [cisBubSh, cisBub, compIdShiftIso, shWhiskerLeft, ShiftedHom.map]
  rw [Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.assoc]
  rfl

theorem comp_powComp {D : Type*} [Category D] {X : D} (f : X ⟶ X) :
    ∀ n : ℕ, f ≫ powComp f n = powComp f (n + 1)
  | 0 => by simp [powComp_succ]
  | n + 1 => by rw [powComp_succ, ← Category.assoc, comp_powComp f n, ← powComp_succ]

variable [GradedBicategory.IsLinear B k]

omit [GradedBicategory.IsLinear B k] in
theorem rightBub_zero {r : ℤ} : S.rightBub (r := r) 0 = 0 := by
  simp only [rightBub, GradedHomBicat.whiskerLeft_zero, zero_comp, comp_zero]

omit [GradedBicategory.IsLinear B k] in
theorem rightBub_id {r : ℤ} : S.rightBub (r := r) (𝟙 _) = 𝟙 _ := by
  simp only [rightBub, Bicategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

theorem rightBub_smul {r : ℤ} (c : k) (γ : 𝟙 (of (S.obj (r + 1))) ⟶ 𝟙 (of (S.obj (r + 1)))) :
    S.rightBub (c • γ) = c • S.rightBub γ := by
  simp only [rightBub, GradedHomBicat.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

omit [GradedBicategory.IsLinear B k] in
/-- `dotsBub` (CL's "bubble times dots", `LemMain.lean`) in the graded-Hom bicategory. -/
theorem of₂_dotsBub (q : ℤ) (m : ℤ) (i : ℕ)
    (g : 𝟙 (S.obj (q + 1 + 1)) ⟶ (𝟙 (S.obj (q + 1 + 1)))⟦m - 2 * (i : ℤ)⟧) :
    of₂ m (S.dotsBub q m i g) =
      S.rightBub (of₂ (m - 2 * (i : ℤ)) g) ≫ powComp (S.grDot (q + 1)) i := by
  rw [dotsBub, ← of₂_comp_of₂ _ _ (by ring), of₂_cisBubSh, GradedHomBicat.of₂_shPow]
  rfl

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **CL Lemma 3.14 in degree 2, in the graded-Hom bicategory**: for `n = wt (q + 1) ≥ 0`, given
(3.2) above `n`, a homogeneous degree-2 endomorphism of `E 1_n` is a bubble of degree 2 plus a
bubble of degree 0 times the dot. -/
theorem exists_decomp_deg_two [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {q : ℤ}
    (hn : 0 ≤ S.wt (q + 1)) (hyp : ∀ r', q + 1 < r' → S.AdjHyp r')
    {y : S.grE (q + 1) ⟶ S.grE (q + 1)} (hy : IsHomogeneous y 2) :
    ∃ γ₀ γ₁ : 𝟙 (of (S.obj (q + 1 + 1))) ⟶ 𝟙 (of (S.obj (q + 1 + 1))),
      IsHomogeneous γ₀ 2 ∧ IsHomogeneous γ₁ 0 ∧
        y = S.rightBub γ₀ + S.rightBub γ₁ ≫ S.grDot (q + 1) := by
  obtain ⟨y₀, rfl⟩ := hy
  change ∃ γ₀ γ₁ : 𝟙 (of (S.obj (q + 1 + 1))) ⟶ 𝟙 (of (S.obj (q + 1 + 1))),
    IsHomogeneous γ₀ 2 ∧ IsHomogeneous γ₁ 0 ∧
      of₂ (2 : ℤ) (y₀ : ShiftedHom (S.E (q + 1)) (S.E (q + 1)) (2 : ℤ)) =
        S.rightBub γ₀ + S.rightBub γ₁ ≫ S.grDot (q + 1)
  obtain ⟨f, hf⟩ := S.lemMain_surjective (r := q) (by omega) hyp (m := 2) (by omega) y₀
  have hN : 2 ≤ (S.wt (q + 1 + 1)).toNat := by rw [S.wt_add_one]; omega
  rw [← hf, Ψ_apply, Finset.sum_eq_add (⟨0, by omega⟩ : Fin _) ⟨1, by omega⟩
      (by simp [Fin.ext_iff]) ?_ (fun h => absurd (Finset.mem_univ _) h)
      (fun h => absurd (Finset.mem_univ _) h),
    of₂_add, of₂_dotsBub, of₂_dotsBub]
  · refine ⟨of₂ _ (f ⟨0, by omega⟩), of₂ _ (f ⟨1, by omega⟩),
      (isHomogeneous_of₂ _ _).of_eq (by simp), (isHomogeneous_of₂ _ _).of_eq (by simp), ?_⟩
    simp only [powComp_zero, Category.comp_id, powComp_succ, Category.id_comp]
  · intro i _ hi
    have hi2 : 2 ≤ (i : ℕ) := by
      have h0 : (i : ℕ) ≠ 0 := fun h => hi.1 (Fin.ext h)
      have h1 : (i : ℕ) ≠ 1 := fun h => hi.2 (Fin.ext h)
      omega
    have h0 : finrank k (𝟙 (S.obj (q + 1 + 1)) ⟶
        (𝟙 (S.obj (q + 1 + 1)))⟦2 - 2 * ((i : ℕ) : ℤ)⟧) = 0 := S.hom_neg _ _ (by omega)
    have : Subsingleton (𝟙 (S.obj (q + 1 + 1)) ⟶
        (𝟙 (S.obj (q + 1 + 1)))⟦2 - 2 * ((i : ℕ) : ℤ)⟧) := Module.finrank_zero_iff.1 h0
    rw [Subsingleton.elim (f i) 0]
    exact (S.dotsBubLin q 2 i).map_zero

/-- **CL Lemma 4.1 for `n ≥ 0`** (cyclicity of the dot, eq. (4.4)): at a weight `n = wt (q + 1) ≥ 0`,
for a left adjunction `R_n ⊣ E 1_n` normalized as in (4.1) (the clockwise degree-zero bubble at
`n + 2` is the identity), the right mate of the (normalized) dot under `E 1_n ⊣ R_n` equals its
left mate under `R_n ⊣ E 1_n`. -/
theorem cyclic_dotN [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {q : ℤ}
    (hn : 0 ≤ S.wt (q + 1)) (adjL : S.grR (q + 1) ⊣ S.grE (q + 1))
    (hu : IsHomogeneous adjL.unit (-(2 * S.wt (q + 1) + 2)))
    (hc : IsHomogeneous adjL.counit (2 * S.wt (q + 1) + 2))
    (hnorm : S.cwBubble adjL.unit = 𝟙 _) :
    conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) (S.grDotN (q + 1)) =
      (conjugateEquiv adjL adjL).symm (S.grDotN (q + 1)) := by
  rw [Equiv.eq_symm_apply]
  set x := S.grDotN (q + 1) with hx
  by_cases h2 : IsZero (𝟙 (S.obj (q + 1 + 1)))
  · have hE : IsZero (S.grE (q + 1)) :=
      (incl _).map_isZero (IsZero.of_iso (isZero_comp_right _ h2) (ρ_ (S.E (q + 1))).symm)
    exact hE.eq_of_src _ _
  set N := (S.wt (q + 1 + 1)).toNat with hNdef
  have hN : 2 ≤ N := by rw [hNdef, S.wt_add_one]; omega
  have hNw : (N : ℤ) = S.wt (q + 1) + 2 := by rw [hNdef, S.wt_add_one]; omega
  have hdN : IsHomogeneous x 2 := (isHomogeneous_of₂ _ _).smul _
  have hyH : IsHomogeneous (conjugateEquiv adjL adjL
      (conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) x)) 2 :=
    isHomogeneous_conjugateEquiv adjL adjL hu (hc.of_eq (by ring))
      (isHomogeneous_conjugateEquiv _ _ (d := 0) (isHomogeneous_incl₂ _)
        ((isHomogeneous_incl₂ _).of_eq (by simp)) hdN)
  obtain ⟨γ₀, γ₁, h0, h1, hdec⟩ := S.exists_decomp_deg_two hn (fun r' _ => S.adjHyp r') hyH
  set γ₁' := ((S.rQ : kˣ) : k) • γ₁ with hγ₁'
  have hdec' : conjugateEquiv adjL adjL (conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) x) =
      S.rightBub γ₀ + S.rightBub γ₁' ≫ x := by
    rw [hdec, hγ₁', rightBub_smul, Linear.smul_comp, ← Linear.comp_smul, hx, grDotN, smul_smul,
      Units.mul_inv, one_smul]
  let β : ℕ → (𝟙 (of (S.obj (q + 1 + 1))) ⟶ 𝟙 (of (S.obj (q + 1 + 1)))) := fun j =>
    adjL.unit ≫ S.grR (q + 1) ◁ powComp x j ≫ S.grCounit (q + 1)
  have hβ : ∀ m, β (m + 1) = β m ≫ γ₀ + β (m + 1) ≫ γ₁' := by
    intro m
    have e1 : β (m + 1) = adjL.unit ≫ S.grR (q + 1) ◁
        (conjugateEquiv adjL adjL (conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) x) ≫
          powComp x m) ≫ S.grCounit (q + 1) :=
      (unit_whiskerLeft_conj_conj_counit adjL (S.grAdj (q + 1)) x (powComp x m)).symm
    refine e1.trans ?_
    rw [hdec', Preadditive.add_comp, GradedHomBicat.whiskerLeft_add, Preadditive.add_comp,
      Preadditive.comp_add, Category.assoc (S.rightBub γ₁'), comp_powComp]
    exact congrArg₂ (· + ·) (unit_whiskerLeft_rightBub_counit _ _ γ₀ (powComp x m))
      (unit_whiskerLeft_rightBub_counit _ _ γ₁' (powComp x (m + 1)))
  have hneg : ∀ j, j + 1 < N → β j = 0 := by
    intro j hj
    have hβH : IsHomogeneous (β j) (-(2 * S.wt (q + 1) + 2) + (j : ℤ) * 2) :=
      (hu.comp ((isHomogeneous_whiskerLeft _ (GradedHomBicat.isHomogeneous_powComp hdN j)).comp
        (isHomogeneous_incl₂ _) rfl) rfl).of_eq (by ring)
    exact GradedHomBicat.eq_zero_of_isHomogeneous (k := k) hβH (S.hom_neg _ _ (by omega))
  have hone : β (N - 1) = 𝟙 _ := hnorm
  have hγ₁ : γ₁' = 𝟙 _ := by
    have h := hβ (N - 2)
    rw [show N - 2 + 1 = N - 1 by omega, hone, hneg (N - 2) (by omega), zero_comp, zero_add,
      Category.id_comp] at h
    exact h.symm
  have hγ₀ : γ₀ = 0 := by
    have h := hβ (N - 1)
    rw [hone, hγ₁, Category.comp_id, Category.id_comp] at h
    have h2 : γ₀ + β (N - 1 + 1) = 0 + β (N - 1 + 1) := by rw [zero_add]; exact h.symm
    exact add_right_cancel h2
  rw [hdec', hγ₀, hγ₁, rightBub_zero, rightBub_id, zero_add, Category.id_comp]

/-! ## Lemma 4.1 for `n ≤ -2` -/

/-- A bubble `γ : 𝟙 ⟶ 𝟙` placed on the left (source side) of `E 1_n`. -/
def leftBub {r : ℤ} (γ : 𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r))) : S.grE r ⟶ S.grE r :=
  (λ_ (S.grE r)).inv ≫ γ ▷ S.grE r ≫ (λ_ (S.grE r)).hom

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem leftBub_zero {r : ℤ} : S.leftBub (r := r) 0 = 0 := by
  simp only [leftBub, GradedHomBicat.zero_whiskerRight, zero_comp, comp_zero]

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem leftBub_id {r : ℤ} : S.leftBub (r := r) (𝟙 _) = 𝟙 _ := by
  simp only [leftBub, Bicategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem leftBub_comm' {r : ℤ} (γ : 𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r)))
    (w : S.grE r ⟶ S.grE r) : S.leftBub γ ≫ w = w ≫ S.leftBub γ :=
  leftBub_comm γ w

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem leftBub_smul {r : ℤ} (c : k) (γ : 𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r))) :
    S.leftBub (c • γ) = c • S.leftBub γ := by
  simp only [leftBub, GradedHomBicat.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `cisBubR` in the graded-Hom bicategory. -/
theorem of₂_cisBubRSh {a b : B} (X : a ⟶ b) {d : ℤ} (g : 𝟙 a ⟶ (𝟙 a)⟦d⟧) :
    of₂ d (cisBubRSh X g) =
      (λ_ (of₁ X)).inv ≫ (of₂ d g : 𝟙 (of a) ⟶ 𝟙 (of a)) ▷ of₁ X ≫ (λ_ (of₁ X)).hom := by
  rw [leftUnitor_inv_eq, leftUnitor_hom_eq, of₂_whiskerRight, incl₂_eq_of₂,
    incl₂_eq_of₂, of₂_comp_of₂ _ _ (zero_add d), of₂_comp_of₂ _ _ (add_zero d),
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  congr 1
  simp only [cisBubRSh, cisBubR, idShiftCompIso, shWhiskerRight, ShiftedHom.map]
  rw [Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.assoc]
  rfl

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `dotsBubN` (bubble on the left times dots, `LemMainNeg.lean`) in the graded-Hom
bicategory. -/
theorem of₂_dotsBubN (q : ℤ) (m : ℤ) (i : ℕ)
    (g : 𝟙 (S.obj (q + 1)) ⟶ (𝟙 (S.obj (q + 1)))⟦m - 2 * (i : ℤ)⟧) :
    of₂ m (S.dotsBubN q m i g) =
      S.leftBub (of₂ (m - 2 * (i : ℤ)) g) ≫ powComp (S.grDot (q + 1)) i := by
  rw [dotsBubN, ← of₂_comp_of₂ _ _ (by ring), of₂_cisBubRSh, GradedHomBicat.of₂_shPow]
  rfl

/-- **CL Lemma 3.14 in degree 2 for `n ≤ -2`, in the graded-Hom bicategory**: a
homogeneous degree-2 endomorphism of `E 1_n` is a bubble of degree 2 plus a bubble of degree 0
times the dot, the bubbles placed on the left (eq. `eq:main2`). -/
theorem exists_decomp_deg_two_neg [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    {q : ℤ} (hn : S.wt (q + 1) ≤ -2) {y : S.grE (q + 1) ⟶ S.grE (q + 1)}
    (hy : IsHomogeneous y 2) :
    ∃ γ₀ γ₁ : 𝟙 (of (S.obj (q + 1))) ⟶ 𝟙 (of (S.obj (q + 1))),
      IsHomogeneous γ₀ 2 ∧ IsHomogeneous γ₁ 0 ∧
        y = S.leftBub γ₀ + S.leftBub γ₁ ≫ S.grDot (q + 1) := by
  obtain ⟨y₀, rfl⟩ := hy
  change ∃ γ₀ γ₁ : 𝟙 (of (S.obj (q + 1))) ⟶ 𝟙 (of (S.obj (q + 1))),
    IsHomogeneous γ₀ 2 ∧ IsHomogeneous γ₁ 0 ∧
      of₂ (2 : ℤ) (y₀ : ShiftedHom (S.E (q + 1)) (S.E (q + 1)) (2 : ℤ)) =
        S.leftBub γ₀ + S.leftBub γ₁ ≫ S.grDot (q + 1)
  obtain ⟨e⟩ := S.exists_FEDecomp (r := q) (by omega)
  obtain ⟨f, hf⟩ := S.lemMainNeg_surjective_of_dotNondeg e (by omega)
    (fun r' _ => S.adjHyp r') (S.dotNondegNeg e) (m := 2) (by omega) y₀
  have hN : 2 ≤ (-S.wt (q + 1)).toNat := by omega
  rw [← hf, ΨN_apply, Finset.sum_eq_add (⟨0, by omega⟩ : Fin _) ⟨1, by omega⟩
      (by simp [Fin.ext_iff]) ?_ (fun h => absurd (Finset.mem_univ _) h)
      (fun h => absurd (Finset.mem_univ _) h),
    of₂_add, of₂_dotsBubN, of₂_dotsBubN]
  · refine ⟨of₂ _ (f ⟨0, by omega⟩), of₂ _ (f ⟨1, by omega⟩),
      (isHomogeneous_of₂ _ _).of_eq (by simp), (isHomogeneous_of₂ _ _).of_eq (by simp), ?_⟩
    simp only [powComp_zero, Category.comp_id, powComp_succ, Category.id_comp]
  · intro i _ hi
    have hi2 : 2 ≤ (i : ℕ) := by
      have h0 : (i : ℕ) ≠ 0 := fun h => hi.1 (Fin.ext h)
      have h1 : (i : ℕ) ≠ 1 := fun h => hi.2 (Fin.ext h)
      omega
    have h0 : finrank k (𝟙 (S.obj (q + 1)) ⟶
        (𝟙 (S.obj (q + 1)))⟦2 - 2 * ((i : ℕ) : ℤ)⟧) = 0 := S.hom_neg _ _ (by omega)
    have : Subsingleton (𝟙 (S.obj (q + 1)) ⟶
        (𝟙 (S.obj (q + 1)))⟦2 - 2 * ((i : ℕ) : ℤ)⟧) := Module.finrank_zero_iff.1 h0
    rw [Subsingleton.elim (f i) 0]
    exact (S.dotsBubNLin q 2 i).map_zero

/-- **CL Lemma 4.1 for `n ≤ -2`** (cyclicity of the dot, eq. (4.4)): at a weight
`n = wt (q + 1) ≤ -2`, for a left adjunction `R_n ⊣ E 1_n` normalized as in (4.1) (the
counter-clockwise degree-zero bubble at `n` is the identity), the right mate of the
(normalized) dot under `E 1_n ⊣ R_n` equals its left mate under `R_n ⊣ E 1_n`. -/
theorem cyclic_dotN_neg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {q : ℤ}
    (hn : S.wt (q + 1) ≤ -2) (adjL : S.grR (q + 1) ⊣ S.grE (q + 1))
    (hu : IsHomogeneous adjL.unit (-(2 * S.wt (q + 1) + 2)))
    (hc : IsHomogeneous adjL.counit (2 * S.wt (q + 1) + 2))
    (hnorm : S.ccwBubble adjL.counit = 𝟙 _) :
    conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) (S.grDotN (q + 1)) =
      (conjugateEquiv adjL adjL).symm (S.grDotN (q + 1)) := by
  rw [Equiv.eq_symm_apply]
  set x := S.grDotN (q + 1) with hx
  by_cases h2 : IsZero (𝟙 (S.obj (q + 1)))
  · have hE : IsZero (S.grE (q + 1)) :=
      (incl _).map_isZero (IsZero.of_iso (isZero_comp_left h2 _) (λ_ (S.E (q + 1))).symm)
    exact hE.eq_of_src _ _
  set N := (-S.wt (q + 1)).toNat with hNdef
  have hN : 2 ≤ N := by omega
  have hdN : IsHomogeneous x 2 := (isHomogeneous_of₂ _ _).smul _
  have hyH : IsHomogeneous (conjugateEquiv adjL adjL
      (conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) x)) 2 :=
    isHomogeneous_conjugateEquiv adjL adjL hu (hc.of_eq (by ring))
      (isHomogeneous_conjugateEquiv _ _ (d := 0) (isHomogeneous_incl₂ _)
        ((isHomogeneous_incl₂ _).of_eq (by simp)) hdN)
  obtain ⟨γ₀, γ₁, h0, h1, hdec⟩ := exists_decomp_deg_two_neg S hn hyH
  set γ₁' := ((S.rQ : kˣ) : k) • γ₁ with hγ₁'
  have hdec' : conjugateEquiv adjL adjL (conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) x) =
      S.leftBub γ₀ + S.leftBub γ₁' ≫ x := by
    rw [hdec, hγ₁', leftBub_smul, Linear.smul_comp, ← Linear.comp_smul, hx, grDotN, smul_smul,
      Units.mul_inv, one_smul]
  let β : ℕ → (𝟙 (of (S.obj (q + 1))) ⟶ 𝟙 (of (S.obj (q + 1)))) := fun j =>
    S.grUnit (q + 1) ≫ powComp x j ▷ S.grR (q + 1) ≫ adjL.counit
  have hβ : ∀ m, β (m + 1) = β m ≫ γ₀ + β (m + 1) ≫ γ₁' := by
    intro m
    have e1 : β (m + 1) = S.grUnit (q + 1) ≫ (powComp x m ≫
        conjugateEquiv adjL adjL (conjugateEquiv (S.grAdj (q + 1)) (S.grAdj (q + 1)) x)) ▷
          S.grR (q + 1) ≫ adjL.counit := by
      refine Eq.trans ?_
        (unit_conj_conj_whiskerRight_counit adjL (S.grAdj (q + 1)) x (powComp x m)).symm
      simp only [β, comp_powComp, grAdj_unit]
    refine e1.trans ?_
    rw [hdec', Preadditive.comp_add, GradedHomBicat.add_whiskerRight, Preadditive.add_comp,
      Preadditive.comp_add, ← S.leftBub_comm' γ₀, ← Category.assoc (powComp x m),
      ← S.leftBub_comm' γ₁', Category.assoc (S.leftBub γ₁'), ← powComp_succ]
    exact congrArg₂ (· + ·) (unit_leftBub_whiskerRight_counit _ _ γ₀ (powComp x m))
      (unit_leftBub_whiskerRight_counit _ _ γ₁' (powComp x (m + 1)))
  have hneg : ∀ j, j + 1 < N → β j = 0 := by
    intro j hj
    have hβH : IsHomogeneous (β j) ((2 * S.wt (q + 1) + 2) + (j : ℤ) * 2) :=
      ((isHomogeneous_incl₂ _).comp ((isHomogeneous_whiskerRight
        (GradedHomBicat.isHomogeneous_powComp hdN j) _).comp hc rfl) rfl).of_eq (by ring)
    exact GradedHomBicat.eq_zero_of_isHomogeneous (k := k) hβH (S.hom_neg _ _ (by omega))
  have hone : β (N - 1) = 𝟙 _ := hnorm
  have hγ₁ : γ₁' = 𝟙 _ := by
    have h := hβ (N - 2)
    rw [show N - 2 + 1 = N - 1 by omega, hone, hneg (N - 2) (by omega), zero_comp, zero_add,
      Category.id_comp] at h
    exact h.symm
  have hγ₀ : γ₀ = 0 := by
    have h := hβ (N - 1)
    rw [hone, hγ₁, Category.comp_id, Category.id_comp] at h
    have h2 : γ₀ + β (N - 1 + 1) = 0 + β (N - 1 + 1) := by rw [zero_add]; exact h.symm
    exact add_right_cancel h2
  rw [hdec', hγ₀, hγ₁, leftBub_zero, leftBub_id, zero_add, Category.id_comp]

/-! ## Lemma 4.1 for the dot, away from the weight `-1` -/

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem conjugateEquiv_smul {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) (c : k) (α : l ⟶ l) :
    conjugateEquiv adj₁ adj₂ (c • α) = c • conjugateEquiv adj₁ adj₂ α := by
  rw [conjugateEquiv_apply', conjugateEquiv_apply']
  simp only [GradedHomBicat.whiskerLeft_smul, GradedHomBicat.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem conjugateEquiv_symm_smul {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) (c : k) (β : r ⟶ r) :
    (conjugateEquiv adj₁ adj₂).symm (c • β) = c • (conjugateEquiv adj₁ adj₂).symm β := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_smul, Equiv.apply_symm_apply]

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cyclic_dot_of_cyclic_dotN {r : ℤ} (adjL : S.grR r ⊣ S.grE r)
    (h : conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDotN r) =
      (conjugateEquiv adjL adjL).symm (S.grDotN r)) :
    conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDot r) =
      (conjugateEquiv adjL adjL).symm (S.grDot r) := by
  have e : S.grDot r = ((S.rQ : kˣ) : k) • S.grDotN r := by
    rw [grDotN, smul_smul, Units.mul_inv, one_smul]
  rw [e, conjugateEquiv_smul, conjugateEquiv_symm_smul, h]

/-- **CL Lemma 4.1, at every weight `n ≠ -1`**: there is a left adjunction
`R_n ⊣ E 1_n` (homogeneous unit and counit of degrees `-2n-2`, `2n+2`), normalized as in CL
(4.1) (the clockwise degree-zero bubble at `n + 2` is the identity if `n ≥ 0`, the
counter-clockwise one at `n` if `n ≤ -2`), for which the downward dot is cyclic: the right mate
of the dot under `E 1_n ⊣ R_n` equals its left mate under `R_n ⊣ E 1_n`. -/
theorem exists_cyclic_leftAdj [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    {r : ℤ} (hn : S.wt r ≠ -1) :
    ∃ adj : S.grR r ⊣ S.grE r,
      IsHomogeneous adj.unit (-(2 * S.wt r + 2)) ∧
      IsHomogeneous adj.counit (2 * S.wt r + 2) ∧
      (0 ≤ S.wt r → S.cwBubble adj.unit = 𝟙 _) ∧
      (S.wt r ≤ -2 → S.ccwBubble adj.counit = 𝟙 _) ∧
      conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDot r) =
        (conjugateEquiv adj adj).symm (S.grDot r) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by ring⟩
  rcases le_or_gt 0 (S.wt (q + 1)) with h0 | h0
  · obtain ⟨adj, hu, hc, hb⟩ := exists_normalized_leftAdjN S (q := q)
      (by rw [S.wt_add_one]; omega)
    exact ⟨adj, hu, hc, fun _ => hb, fun h => absurd h (by omega),
      S.cyclic_dot_of_cyclic_dotN adj (cyclic_dotN S h0 adj hu hc hb)⟩
  · obtain ⟨adj, hu, hc, hb⟩ := exists_normalized_leftAdj_neg S (r := q + 1) (by omega)
    exact ⟨adj, hu, hc, fun h => absurd h (by omega), fun _ => hb,
      S.cyclic_dot_of_cyclic_dotN adj (cyclic_dotN_neg S (by omega) adj hu hc hb)⟩

end StrongSl2

end Categorification.TwoRep
