/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclicDot

/-!
# Cyclicity of the dot at the weight `-1` (CL Lemma 4.1, the curl argument)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §4.2, proof of Lemma 4.1 for `n = -1` (eqs. (4.8), (4.9)), and Lemma 3.14
in the case `m = 2`, `n = -1` (eq. `eq:new`).

For `n = -1` the bubble argument of `CyclicDot.lean` does not determine the mates (CL: "we can
not set `m = n` in (4.7)"). CL use curls instead; we make the argument a dimension count. With
`u` the unit of the normalized left adjunction `R ⊣ E 1_{-1}` and `ε` the counit of
`E 1_{-1} ⊣ R`:

* the *curl* `curlG u ε τ` of the crossing `τ` on `E 1_{-1} E 1_1` (closing `E 1_{-1}` on the
  left of `E 1_1`) has degree `-2`, hence vanishes by Lemma 3.1 at the weight `1` (CL (4.8));
* by the two dot-slide relations and the normalization `u ≫ ε = 1`, the curls with the right
  mate or with the left mate of the dot on the downward strand are both `-1` (CL (4.9));
* bubbles on the outer side of the downward strand slide out of the curl (so their curl is `0`)
  and out of the clockwise bubble;
* hence `φ ↦ (clockwise bubble of φ, curl of φ)` maps the homogeneous degree-`2` endomorphisms of
  `R` onto `Hom²(1_1, 1_1) × End(E 1_1)`, a space of the same dimension (CL eq. `eq:new`,
  `lemMain_finrank_two`), so it is injective; it takes the same value on both mates.

## Main declarations

* generic: `curlG`, `curlR`, `cwR` and their sliding lemmas;
* `StrongSl2.grDotN_slide_right` (the second dot-slide relation in the graded-Hom bicategory);
* `StrongSl2.BBw.cyclic_dotN_neg_one`: **CL Lemma 4.1 at the weight `-1`** under (BB_w);
* `StrongSl2.BBw.cyclic_dot`: **CL Lemma 4.1 under (BB_w) at every weight**, with the
  normalization (4.1).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c}

/-- The curl of `w : E ≫ E' ⟶ E ≫ E'`, closing `E` with the cup `u` and the cap `ε`. -/
def curlG (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (w : E ≫ E' ⟶ E ≫ E') : E' ⟶ E' :=
  (λ_ E').inv ≫ u ▷ E' ≫ (α_ R E E').hom ≫ R ◁ w ≫ (α_ R E E').inv ≫ eps ▷ E' ≫ (λ_ E').hom

/-- The curl of `τ` with `φ` on the downward strand. -/
def curlR (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (τ : E ≫ E' ⟶ E ≫ E') (φ : R ⟶ R) :
    E' ⟶ E' :=
  (λ_ E').inv ≫ u ▷ E' ≫ (φ ▷ E) ▷ E' ≫ (α_ R E E').hom ≫ R ◁ τ ≫ (α_ R E E').inv ≫
    eps ▷ E' ≫ (λ_ E').hom

theorem curlG_whiskerLeft_comp (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b)
    (w : E ≫ E' ⟶ E ≫ E') (z : E' ⟶ E') : curlG u eps (E ◁ z ≫ w) = z ≫ curlG u eps w := by
  unfold curlG
  calc _ = 𝟙 _ ⊗≫ (u ▷ E' ≫ (R ≫ E) ◁ z) ⊗≫ R ◁ w ⊗≫ eps ▷ E' ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 b ◁ z ≫ u ▷ E') ⊗≫ R ◁ w ⊗≫ eps ▷ E' ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = _ := by
        bicategory

theorem curlG_comp_whiskerLeft (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b)
    (w : E ≫ E' ⟶ E ≫ E') (z : E' ⟶ E') : curlG u eps (w ≫ E ◁ z) = curlG u eps w ≫ z := by
  unfold curlG
  calc _ = 𝟙 _ ⊗≫ u ▷ E' ⊗≫ R ◁ w ⊗≫ ((R ≫ E) ◁ z ≫ eps ▷ E') ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ u ▷ E' ⊗≫ R ◁ w ⊗≫ (eps ▷ E' ≫ 𝟙 b ◁ z) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        bicategory

theorem curlG_id (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) :
    curlG u eps (𝟙 (E ≫ E')) = (λ_ E').inv ≫ (u ≫ eps) ▷ E' ≫ (λ_ E').hom := by
  unfold curlG
  bicategory

/-- A right mate on the downward strand of a curl moves to the top of the upward strand. -/
theorem curlR_conjugateEquiv (u : 𝟙 b ⟶ R ≫ E) (B : E ⊣ R) (τ : E ≫ E' ⟶ E ≫ E')
    (x : E ⟶ E) : curlR u B.counit τ (conjugateEquiv B B x) = curlG u B.counit (τ ≫ x ▷ E') := by
  unfold curlR curlG
  calc _ = 𝟙 _ ⊗≫ u ▷ E' ⊗≫ (conjugateEquiv B B x ▷ (E ≫ E') ≫ R ◁ τ) ⊗≫
        B.counit ▷ E' ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ u ▷ E' ⊗≫ (R ◁ τ ≫ conjugateEquiv B B x ▷ (E ≫ E')) ⊗≫
        B.counit ▷ E' ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ u ▷ E' ⊗≫ R ◁ τ ⊗≫
        (conjugateEquiv B B x ▷ E ≫ B.counit) ▷ E' ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ u ▷ E' ⊗≫ R ◁ τ ⊗≫ (R ◁ x ≫ B.counit) ▷ E' ⊗≫ 𝟙 _ := by
        rw [conjugateEquiv_whiskerRight_counit]
    _ = _ := by
        bicategory

/-- A left mate on the downward strand of a curl moves to the bottom of the upward strand. -/
theorem curlR_conjugateEquiv_symm (A : R ⊣ E) (eps : R ≫ E ⟶ 𝟙 b) (τ : E ≫ E' ⟶ E ≫ E')
    (x : E ⟶ E) :
    curlR A.unit eps τ ((conjugateEquiv A A).symm x) = curlG A.unit eps (x ▷ E' ≫ τ) := by
  have h : A.unit ≫ (conjugateEquiv A A).symm x ▷ E = A.unit ≫ R ◁ x := by
    rw [← unit_whiskerLeft_conjugateEquiv, Equiv.apply_symm_apply]
  unfold curlR curlG
  calc _ = 𝟙 _ ⊗≫ (A.unit ≫ (conjugateEquiv A A).symm x ▷ E) ▷ E' ⊗≫ R ◁ τ ⊗≫
        eps ▷ E' ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (A.unit ≫ R ◁ x) ▷ E' ⊗≫ R ◁ τ ⊗≫ eps ▷ E' ⊗≫ 𝟙 _ := by
        rw [h]
    _ = _ := by
        bicategory

/-- A bubble on the outer side of the downward strand slides out of the curl. -/
theorem curlR_srcBub (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (τ : E ≫ E' ⟶ E ≫ E')
    (γ : 𝟙 b ⟶ 𝟙 b) :
    curlR u eps τ ((λ_ R).inv ≫ γ ▷ R ≫ (λ_ R).hom) =
      ((λ_ E').inv ≫ γ ▷ E' ≫ (λ_ E').hom) ≫ curlG u eps τ := by
  unfold curlR curlG
  calc _ = 𝟙 _ ⊗≫ (𝟙 b ◁ u ≫ γ ▷ (R ≫ E)) ▷ E' ⊗≫ R ◁ τ ⊗≫ eps ▷ E' ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (γ ▷ 𝟙 b ≫ 𝟙 b ◁ u) ▷ E' ⊗≫ R ◁ τ ⊗≫ eps ▷ E' ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        bicategory

/-- The clockwise bubble of `φ` on the downward strand. -/
def cwR (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (φ : R ⟶ R) : 𝟙 b ⟶ 𝟙 b :=
  u ≫ φ ▷ E ≫ eps

theorem cwR_srcBub (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (γ : 𝟙 b ⟶ 𝟙 b) :
    cwR u eps ((λ_ R).inv ≫ γ ▷ R ≫ (λ_ R).hom) = γ ≫ u ≫ eps := by
  unfold cwR
  calc _ = 𝟙 _ ⊗≫ (𝟙 b ◁ u ≫ γ ▷ (R ≫ E)) ⊗≫ eps := by
        bicategory
    _ = 𝟙 _ ⊗≫ (γ ▷ 𝟙 b ≫ 𝟙 b ◁ u) ⊗≫ eps := by
        rw [whisker_exchange]
    _ = _ := by
        bicategory

theorem cwR_conjugateEquiv (u : 𝟙 b ⟶ R ≫ E) (B : E ⊣ R) (x : E ⟶ E) :
    cwR u B.counit (conjugateEquiv B B x) = u ≫ R ◁ x ≫ B.counit := by
  unfold cwR
  rw [conjugateEquiv_whiskerRight_counit]

theorem cwR_conjugateEquiv_symm (A : R ⊣ E) (eps : R ≫ E ⟶ 𝟙 b) (x : E ⟶ E) :
    cwR A.unit eps ((conjugateEquiv A A).symm x) = A.unit ≫ R ◁ x ≫ eps := by
  unfold cwR
  rw [← Category.assoc, ← unit_whiskerLeft_conjugateEquiv, Equiv.apply_symm_apply,
    Category.assoc]

end Generic

/-! ## Linear algebra in the graded-Hom bicategory -/

section GradedHom

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  [GradedBicategory.IsLinear B k]

namespace GradedHomBicat

open GradedHomCat

theorem component_smul {a b : B} {f g : a ⟶ b} (e : ℤ) (c : k) (φ : of₁ f ⟶ of₁ g) :
    component e (c • φ) = c • component e φ := by
  induction φ using hom_induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add φ ψ hφ hψ => rw [smul_add, map_add, map_add, hφ, hψ, smul_add]
  | homOf d x =>
    rw [← homOf_smul]
    by_cases h : e = d
    · subst h
      rw [component_homOf_self, component_homOf_self]
    · rw [component_homOf_of_ne h, component_homOf_of_ne h, smul_zero]

theorem conjugateEquiv_add {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) (α β : l ⟶ l) :
    conjugateEquiv adj₁ adj₂ (α + β) = conjugateEquiv adj₁ adj₂ α + conjugateEquiv adj₁ adj₂ β := by
  rw [conjugateEquiv_apply', conjugateEquiv_apply', conjugateEquiv_apply']
  simp only [GradedHomBicat.whiskerLeft_add, GradedHomBicat.add_whiskerRight,
    Preadditive.add_comp, Preadditive.comp_add]

theorem conjugateEquiv_symm_add {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) (α β : r ⟶ r) :
    (conjugateEquiv adj₁ adj₂).symm (α + β) =
      (conjugateEquiv adj₁ adj₂).symm α + (conjugateEquiv adj₁ adj₂).symm β := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The inverse conjugation preserves homogeneity.** -/
theorem isHomogeneous_conjugateEquiv_symm {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) {d : ℤ} (hu : IsHomogeneous adj₁.unit d)
    (hc : IsHomogeneous adj₂.counit (-d)) {α : r ⟶ r} {e : ℤ} (hα : IsHomogeneous α e) :
    IsHomogeneous ((conjugateEquiv adj₁ adj₂).symm α) e := by
  rw [conjugateEquiv_symm_apply']
  have h1 : IsHomogeneous (λ_ l).inv 0 := isHomogeneous_incl₂ (λ_ l.as).inv
  have h2 : IsHomogeneous (α_ l r l).hom 0 := isHomogeneous_incl₂ (α_ l.as r.as l.as).hom
  have h3 : IsHomogeneous (ρ_ l).hom 0 := isHomogeneous_incl₂ (ρ_ l.as).hom
  exact (h1.comp ((isHomogeneous_whiskerRight hu l).comp (h2.comp ((isHomogeneous_whiskerLeft l
    (isHomogeneous_whiskerRight hα l)).comp ((isHomogeneous_whiskerLeft l hc).comp h3
      rfl) rfl) rfl) rfl) rfl).of_eq (by ring)

end GradedHomBicat

end GradedHom

/-! ## Lemma 4.1 at the weight `-1` -/

section WeightNegOne

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]

namespace StrongSl2

open GradedHomBicat GradedHomCat Module
open KrullSchmidtCat (HomFinite)

variable (S : StrongSl2 k B)

/-- The second dot-slide relation (CL `eq_nil_dotslide`) for the normalized dot:
`τ ; (E x) - (x E) ; τ = 1` (diagrammatic order). -/
theorem grDotN_slide_right (r : ℤ) :
    S.grCross r ≫ S.grE r ◁ S.grDotN (r + 1) - S.grDotN r ▷ S.grE (r + 1) ≫ S.grCross r =
      𝟙 _ := by
  have h := congrArg (of₂ (0 : ℤ)) (S.dot_slide_right r)
  rw [of₂_sub, ← of₂_comp_of₂, ← of₂_comp_of₂, ← whiskerLeft_of₂, ← of₂_whiskerRight,
    ShiftedHom.mk₀_smul, of₂_smul] at h
  rw [GradedHomBicat.whiskerLeft_smul, GradedHomBicat.smul_whiskerRight, Linear.smul_comp,
    Linear.comp_smul, ← smul_sub, ← h, smul_smul, Units.inv_mul, one_smul]
  rfl

section Lin

variable {a b c : GradedHomBicat B} {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c}

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem curlG_add (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (w₁ w₂ : E ≫ E' ⟶ E ≫ E') :
    curlG u eps (w₁ + w₂) = curlG u eps w₁ + curlG u eps w₂ := by
  simp only [curlG, GradedHomBicat.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem curlR_add (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (τ : E ≫ E' ⟶ E ≫ E')
    (φ₁ φ₂ : R ⟶ R) : curlR u eps τ (φ₁ + φ₂) = curlR u eps τ φ₁ + curlR u eps τ φ₂ := by
  simp only [curlR, GradedHomBicat.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem curlR_smul (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (τ : E ≫ E' ⟶ E ≫ E') (t : k)
    (φ : R ⟶ R) : curlR u eps τ (t • φ) = t • curlR u eps τ φ := by
  simp only [curlR, GradedHomBicat.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem cwR_add (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (φ₁ φ₂ : R ⟶ R) :
    cwR u eps (φ₁ + φ₂) = cwR u eps φ₁ + cwR u eps φ₂ := by
  simp only [cwR, GradedHomBicat.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem cwR_smul (u : 𝟙 b ⟶ R ≫ E) (eps : R ≫ E ⟶ 𝟙 b) (t : k) (φ : R ⟶ R) :
    cwR u eps (t • φ) = t • cwR u eps φ := by
  simp only [cwR, GradedHomBicat.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

end Lin

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **CL Lemma 4.1 at the weight `-1`** (the curl argument, CL (4.8), (4.9)) under (BB_w): at a
weight `n = wt r = -1`, for a left adjunction `R_n ⊣ E 1_n` normalized as in (4.1) (the
clockwise degree-zero bubble at `n + 2 = 1` is the identity), the right mate of the
(normalized) dot under `E 1_n ⊣ R_n` equals its left mate under `R_n ⊣ E 1_n`.

Proof: the curl of the crossing on `E 1_{-1} E 1_1` (closed by the left cup and the right cap)
has degree `-2`, hence vanishes (Lemma 3.1 at the weight `1`); by the two dot-slide relations
and the normalization, the curls with the right or the left mate of the dot on the downward
strand are both `-1`. Together with the clockwise bubble, the curl detects homogeneous
degree-`2` endomorphisms of `R_n`: the map `f ↦ (cw bubble, curl)` is onto a space of the same
dimension as `Hom²(E 1_{-1}, E 1_{-1})` (CL eq. `eq:new`, `lemMain_finrank_two`), hence injective;
both functionals agree on the two mates. -/
theorem BBw.cyclic_dotN_neg_one [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) {r : ℤ}
    (hr : S.wt r = -1) (adjL : S.grR r ⊣ S.grE r)
    (hu : IsHomogeneous adjL.unit (-(2 * S.wt r + 2)))
    (hc : IsHomogeneous adjL.counit (2 * S.wt r + 2))
    (hnorm : S.cwBubble adjL.unit = 𝟙 _) :
    conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDotN r) =
      (conjugateEquiv adjL adjL).symm (S.grDotN r) := by
  have hw1 : S.wt (r + 1) = 1 := by rw [S.wt_add_one, hr]; norm_num
  -- the trivial case
  by_cases h1 : IsZero (𝟙 (S.obj (r + 1)))
  · have hR : IsZero (S.grR r) :=
      (incl _).map_isZero (IsZero.of_iso (isZero_comp_left h1 _)
        (λ_ ((S.F r)⟦S.n₀ + 2 * r + 1⟧)).symm)
    exact hR.eq_of_src _ _
  set x := S.grDotN r with hx
  set u := adjL.unit with hudef
  set eps := S.grCounit r with hepsdef
  set τ := S.grCross r with hτ
  have hu0 : u ≫ eps = 𝟙 _ := by
    have h0 : (S.wt (r + 1)).toNat - 1 = 0 := by rw [hw1]; rfl
    simp only [cwBubble, h0, powComp_zero, Bicategory.whiskerLeft_id, Category.id_comp] at hnorm
    exact hnorm
  have hu' : IsHomogeneous u 0 := hu.of_eq (by rw [hr]; norm_num)
  have hyp : ∀ r', S.AdjHyp r' := hS.adjHyp
  -- the curl of the crossing vanishes
  have hcurl0 : curlG u eps τ = 0 := by
    have hH : IsHomogeneous (curlG u eps τ) (-2) := by
      unfold curlG
      exact ((isHomogeneous_incl₂ _).comp ((isHomogeneous_whiskerRight hu' _).comp
        ((isHomogeneous_incl₂ _).comp ((isHomogeneous_whiskerLeft _
          (isHomogeneous_of₂ _ _)).comp ((isHomogeneous_incl₂ _).comp
            ((isHomogeneous_whiskerRight (isHomogeneous_incl₂ _) _).comp
              (isHomogeneous_incl₂ _) rfl) rfl) rfl) rfl) rfl) rfl).of_eq (by norm_num)
    exact GradedHomBicat.eq_zero_of_isHomogeneous (k := k) hH
      (S.lem1_neg (r₀ := r + 1) (by omega) (fun r' _ => hyp r') (r + 1) le_rfl _ (by norm_num))
  have hcurl1 : curlG u eps (𝟙 (S.grE r ≫ S.grE (r + 1))) = 𝟙 _ := by
    rw [curlG_id, hu0, Bicategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  -- the curls of the two mates of the dot
  have hR : curlR u eps τ (conjugateEquiv (S.grAdj r) (S.grAdj r) x) = -𝟙 _ := by
    have h := curlR_conjugateEquiv u (S.grAdj r) τ x
    simp only [grAdj_counit] at h
    rw [h]
    have hs := S.grDotN_slide r
    have e : S.grE r ◁ S.grDotN (r + 1) ≫ τ = 𝟙 _ + τ ≫ x ▷ S.grE (r + 1) := by
      rw [← hs, sub_add_cancel]
    have := congrArg (curlG u eps) e
    rw [curlG_whiskerLeft_comp, hcurl0, comp_zero, curlG_add, hcurl1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hL : curlR u eps τ ((conjugateEquiv adjL adjL).symm x) = -𝟙 _ := by
    rw [curlR_conjugateEquiv_symm adjL eps τ x]
    have hs := S.grDotN_slide_right r
    have e : τ ≫ S.grE r ◁ S.grDotN (r + 1) = 𝟙 _ + x ▷ S.grE (r + 1) ≫ τ := by
      rw [← hs, sub_add_cancel]
    have := congrArg (curlG u eps) e
    rw [curlG_comp_whiskerLeft, hcurl0, zero_comp, curlG_add, hcurl1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  -- the clockwise bubbles of the two mates agree
  have hcwR : cwR u eps (conjugateEquiv (S.grAdj r) (S.grAdj r) x) = u ≫ S.grR r ◁ x ≫ eps := by
    have h := cwR_conjugateEquiv u (S.grAdj r) x
    simpa only [grAdj_counit] using h
  have hcwL : cwR u eps ((conjugateEquiv adjL adjL).symm x) = u ≫ S.grR r ◁ x ≫ eps :=
    cwR_conjugateEquiv_symm adjL eps x
  -- bubbles on the outer side of the downward strand
  let srcBub : (𝟙 (of (S.obj (r + 1))) ⟶ 𝟙 (of (S.obj (r + 1)))) → (S.grR r ⟶ S.grR r) :=
    fun γ => (λ_ (S.grR r)).inv ≫ γ ▷ S.grR r ≫ (λ_ (S.grR r)).hom
  have hcw_src : ∀ γ, cwR u eps (srcBub γ) = γ := fun γ => by
    simp only [srcBub]
    rw [cwR_srcBub, hu0, Category.comp_id]
  have hcurl_src : ∀ γ, curlR u eps τ (srcBub γ) = 0 := fun γ => by
    simp only [srcBub]
    rw [curlR_srcBub, hcurl0, comp_zero]
  have hsrcH : ∀ {γ : 𝟙 (of (S.obj (r + 1))) ⟶ 𝟙 (of (S.obj (r + 1)))} {e : ℤ},
      IsHomogeneous γ e → IsHomogeneous (srcBub γ) e := fun hγ =>
    ((isHomogeneous_incl₂ _).comp ((isHomogeneous_whiskerRight hγ _).comp
      (isHomogeneous_incl₂ _) rfl) rfl).of_eq (by ring)
  -- degrees
  have hxH : IsHomogeneous x 2 := (isHomogeneous_of₂ _ _).smul _
  have hB0 : IsHomogeneous (S.grAdj r).unit 0 := isHomogeneous_incl₂ _
  have hB0' : IsHomogeneous (S.grAdj r).counit (-0) := (isHomogeneous_incl₂ _).of_eq (by simp)
  have hxR : IsHomogeneous (conjugateEquiv (S.grAdj r) (S.grAdj r) x) 2 :=
    isHomogeneous_conjugateEquiv _ _ hB0 hB0' hxH
  have hxL : IsHomogeneous ((conjugateEquiv adjL adjL).symm x) 2 :=
    isHomogeneous_conjugateEquiv_symm _ _ hu (hc.of_eq (by ring)) hxH
  have hβ1 : IsHomogeneous (u ≫ S.grR r ◁ x ≫ eps) 2 :=
    (hu'.comp ((isHomogeneous_whiskerLeft _ hxH).comp (isHomogeneous_incl₂ _) rfl) rfl).of_eq
      (by norm_num)
  have conj_zero : conjugateEquiv (S.grAdj r) (S.grAdj r) 0 = 0 := by
    have h := conjugateEquiv_add (S.grAdj r) (S.grAdj r) 0 0
    rw [add_zero] at h
    simpa using h
  -- the linear map `f ↦ (cw bubble, curl)` on `Hom²(E 1_{-1}, E 1_{-1})`
  let T : (S.grR r ⟶ S.grR r) → ((𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦(2 : ℤ)⟧) ×
      (S.E (r + 1) ⟶ (S.E (r + 1))⟦(0 : ℤ)⟧)) :=
    fun φ => (component 2 (cwR u eps φ), component 0 (curlR u eps τ φ))
  let Φ : ShiftedHom (S.E r) (S.E r) (2 : ℤ) →ₗ[k] ((𝟙 (S.obj (r + 1)) ⟶
      (𝟙 (S.obj (r + 1)))⟦(2 : ℤ)⟧) × (S.E (r + 1) ⟶ (S.E (r + 1))⟦(0 : ℤ)⟧)) :=
    { toFun := fun f => T (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f))
      map_add' := fun f g => by
        refine Prod.ext ?_ ?_
        · show component 2 (cwR u eps (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 (f + g)))) =
            component 2 (cwR u eps (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f))) +
              component 2 (cwR u eps (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 g)))
          rw [of₂_add, conjugateEquiv_add, cwR_add, map_add]
        · show component 0 (curlR u eps τ
              (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 (f + g)))) =
            component 0 (curlR u eps τ (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f))) +
              component 0 (curlR u eps τ (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 g)))
          rw [of₂_add, conjugateEquiv_add, curlR_add, map_add]
      map_smul' := fun c f => by
        refine Prod.ext ?_ ?_
        · show component 2 (cwR u eps (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 (c • f)))) =
            c • component 2 (cwR u eps (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f)))
          rw [of₂_smul, conjugateEquiv_smul, cwR_smul]
          exact component_smul _ _ _
        · show component 0 (curlR u eps τ
              (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 (c • f)))) =
            c • component 0 (curlR u eps τ (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f)))
          rw [of₂_smul, conjugateEquiv_smul, curlR_smul]
          exact component_smul _ _ _ }
  have hΦ : ∀ f φ, conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f) = φ → Φ f = T φ := by
    intro f φ h
    change T (conjugateEquiv (S.grAdj r) (S.grAdj r) (of₂ 2 f)) = T φ
    rw [h]
  -- `Φ` is onto
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, t⟩
    obtain ⟨s, hs⟩ : ∃ s : k, t = s • ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (S.E (r + 1))) := by
      by_cases hE' : IsZero (S.E (r + 1))
      · exact ⟨0, by rw [zero_smul]; exact hE'.eq_of_src _ _⟩
      · have h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1))) := fun hz =>
          hE' (IsZero.of_iso (isZero_comp_right _ hz) (ρ_ _).symm)
        have hf1 : finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦(0 : ℤ)⟧) = 1 := by
          rw [finrank_hom_shift_zero k _ _ rfl]
          exact S.lem1_zero (r₀ := r + 1) (by omega) (fun r' _ => hyp r') le_rfl h2
        have hne : ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (S.E (r + 1))) ≠ 0 := by
          intro h0
          apply hE'
          rw [IsZero.iff_id_eq_zero]
          have h' := congrArg (· ≫ (shiftFunctorZero' _ (0 : ℤ) rfl).hom.app (S.E (r + 1))) h0
          simpa [ShiftedHom.mk₀] using h'
        obtain ⟨c, hc'⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hf1 t
        exact ⟨c, hc'.symm⟩
    let φ := srcBub (of₂ 2 g + s • (u ≫ S.grR r ◁ x ≫ eps)) +
      (-s) • conjugateEquiv (S.grAdj r) (S.grAdj r) x
    have hφ : IsHomogeneous φ 2 :=
      (hsrcH ((isHomogeneous_of₂ _ _).add (hβ1.smul _))).add (hxR.smul _)
    obtain ⟨f, hf⟩ := isHomogeneous_conjugateEquiv_symm (S.grAdj r) (S.grAdj r) hB0 hB0' hφ
    refine ⟨f, ?_⟩
    have hf' : of₂ 2 f = (conjugateEquiv (S.grAdj r) (S.grAdj r)).symm φ := hf.symm
    rw [hΦ f φ (by rw [hf', Equiv.apply_symm_apply])]
    refine Prod.ext ?_ ?_
    · change component 2 (cwR u eps φ) = g
      rw [cwR_add, cwR_smul, hcw_src, hcwR, add_assoc, ← add_smul, add_neg_cancel, zero_smul,
        add_zero]
      exact component_homOf_self 2 g
    · change component 0 (curlR u eps τ φ) = t
      rw [curlR_add, curlR_smul, hcurl_src, hR, zero_add, smul_neg, ← neg_smul, neg_neg,
        component_smul, hs, ← incl₂_id, incl₂_eq_of₂]
      exact congrArg (s • ·) (component_homOf_self 0 _)
  -- dimensions agree (CL eq. `eq:new`), hence `Φ` is injective
  have hfin : finrank k (ShiftedHom (S.E r) (S.E r) (2 : ℤ)) =
      finrank k ((𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦(2 : ℤ)⟧) ×
        (S.E (r + 1) ⟶ (S.E (r + 1))⟦(0 : ℤ)⟧)) := by
    rw [Module.finrank_prod, finrank_hom_shift_zero k _ _ rfl]
    exact S.lemMain_finrank_two hr (fun r' _ => hyp r')
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  -- the difference of the two mates vanishes
  set d := conjugateEquiv (S.grAdj r) (S.grAdj r) x - (conjugateEquiv adjL adjL).symm x with hd
  have hdH : IsHomogeneous d 2 := by
    rw [hd, sub_eq_add_neg]
    exact hxR.add hxL.neg
  obtain ⟨f₀, hf₀⟩ := isHomogeneous_conjugateEquiv_symm (S.grAdj r) (S.grAdj r) hB0 hB0' hdH
  have hΦ0 : Φ f₀ = 0 := by
    have hf₀' : of₂ 2 f₀ = (conjugateEquiv (S.grAdj r) (S.grAdj r)).symm d := hf₀.symm
    rw [hΦ f₀ d (by rw [hf₀', Equiv.apply_symm_apply])]
    refine Prod.ext ?_ ?_
    · change component 2 (cwR u eps d) = 0
      have e : cwR u eps d = 0 := by
        have h := cwR_add u eps d ((conjugateEquiv adjL adjL).symm x)
        rw [hd, sub_add_cancel, hcwR, hcwL] at h
        simpa using h
      rw [e, map_zero]
    · change component 0 (curlR u eps τ d) = 0
      have e : curlR u eps τ d = 0 := by
        have h := curlR_add u eps τ d ((conjugateEquiv adjL adjL).symm x)
        rw [hd, sub_add_cancel, hR, hL] at h
        simpa using h
      rw [e, map_zero]
  have hf00 : f₀ = 0 := hinj (hΦ0.trans (map_zero Φ).symm)
  have hd0 : d = 0 := by
    have h : (conjugateEquiv (S.grAdj r) (S.grAdj r)).symm d = 0 := by
      rw [hf₀, hf00]
      exact homOf_zero 2
    rw [← Equiv.apply_symm_apply (conjugateEquiv (S.grAdj r) (S.grAdj r)) d, h, conj_zero]
  exact sub_eq_zero.1 hd0

/-- **CL Lemma 4.1 under (BB_w)** (cyclicity of the dot, eq. (4.4)), at every weight: for every
`E 1_n` there is a left adjunction `R_n ⊣ E 1_n` (homogeneous unit and counit of degrees
`-2n-2`, `2n+2`), normalized as in CL (4.1) (the clockwise degree-zero bubble at `n + 2` is the
identity if `n ≥ -1`, the counter-clockwise one at `n` if `n ≤ -2`), for which the right mate of
the dot under `E 1_n ⊣ R_n` equals its left mate under `R_n ⊣ E 1_n`. -/
theorem BBw.cyclic_dot [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) (r : ℤ) :
    ∃ adj : S.grR r ⊣ S.grE r,
      IsHomogeneous adj.unit (-(2 * S.wt r + 2)) ∧
      IsHomogeneous adj.counit (2 * S.wt r + 2) ∧
      (-1 ≤ S.wt r → S.cwBubble adj.unit = 𝟙 _) ∧
      (S.wt r ≤ -2 → S.ccwBubble adj.counit = 𝟙 _) ∧
      conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDot r) =
        (conjugateEquiv adj adj).symm (S.grDot r) := by
  by_cases hr : S.wt r = -1
  · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by ring⟩
    obtain ⟨adj, hu, hc, hb⟩ := BBw.exists_normalized_leftAdj hS (q := q)
      (by rw [S.wt_add_one]; omega)
    exact ⟨adj, hu, hc, fun _ => hb, fun h => absurd h (by omega),
      S.cyclic_dot_of_cyclic_dotN adj (BBw.cyclic_dotN_neg_one S hS hr adj hu hc hb)⟩
  · obtain ⟨adj, hu, hc, hcw, hccw, hcyc⟩ := BBw.exists_cyclic_leftAdj S hS hr
    exact ⟨adj, hu, hc, fun h => hcw (by omega), hccw, hcyc⟩

end StrongSl2

end WeightNegOne

end Categorification.TwoRep
