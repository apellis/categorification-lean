/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.GradedHomAdjunction
import Categorification.TwoRep.RightwardCrossing

/-!
# The adjoint induction hypothesis at the weights `0` and `-2`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3, Proposition 3.9 (`prop:lradj`): in a strong 2-representation of `sl₂` the
left adjoint of `E 1_n` is `1_n F ⟨-n-1⟩` (the adjoint induction hypothesis (3.2), `eq:ind_hyp`,
`StrongSl2.AdjHyp`). CL's inductive argument (decreasing in `n` for `n ≥ 0`, increasing for
`n ≤ 0`) gives no information at the two weights `n ∈ {0, -2}` of a string of even weights: the
induction steps at these weights are empty (see the README, section on Cautis–Lauda). This file
proves (3.2) at these two weights from the invertibility of Rouquier's maps
`ρ_2 : E F 1_2 → F E 1_2 ⊕ 1_2 ⊕ 1_2`, `ρ_0 = σ_0 : E F 1_0 → F E 1_0` and
`ρ_{-2} : E F 1_{-2} ⊕ 1_{-2} ⊕ 1_{-2} → F E 1_{-2}`, by the argument of J. Brundan, *On the
definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Theorem 4.3, specialized to these weights
(`RightwardCrossing.lean`), together with the one-zigzag lemma and `End(E 1_n) = k`.

The relation chase takes place in the graded-Hom bicategory `GradedHomBicat B`
(`GradedHomBicategory.lean`), whose 2-morphisms are the homogeneous 2-morphisms of all degrees of
`B`; this is where the shift coherence `GradedBicategory.ShiftCoherence B` is used. There the right
adjoint of `E 1_n` is `R_n = 1_n F ⟨n+1⟩` with unit and counit of degree `0`
(`StrongSl2.adj`), the dot has degree `2` and the crossing degree `-2`. The resulting unit and
counit of `R_n ⊣ E 1_n` are homogeneous of degrees `-2n-2` and `2n+2`, i.e. of degree `0` for
`1_n F ⟨-n-1⟩ = R_n ⟨-2n-2⟩`.

## Main declarations

For `S : StrongSl2 k B` (objects indexed by `r`, of weight `S.wt r`):

* `S.grE r`, `S.grR r`, `S.grUnit r`, `S.grCounit r`, `S.grDot r`, `S.grCross r`: the data of `S`
  in the graded-Hom bicategory;
* `S.grSigma r : R r ≫ E r ⟶ E (r+1) ≫ R (r+1)`: the rightward crossing `σ_λ` at the object
  `r + 1` of weight `λ = S.wt (r + 1)`, homogeneous of degree `-2`
  (`isHomogeneous_grSigma`); `S.sigma r` is the corresponding shifted 2-morphism of `B`;
* `grCross_sq`, `grDotN_slide`, `grCross_braid`, `leftZigzag_grUnit_grCounit`: the nilHecke
  relations and the zigzag identity of `S` in the graded-Hom bicategory;
* `adjHyp_of_rightZigzag`: a unit and a counit of degrees `-2n-2`, `2n+2` for `R_n`, `E 1_n` in
  the graded-Hom bicategory satisfying the zigzag identity for `E 1_n` give (3.2) at `n`,
  provided `End(E 1_n)` is one-dimensional;
* `adjHyp_of_wt_eq_zero`: (3.2) at weight `0`, if `σ_0` and `ρ_2` are invertible and
  `End(E 1_0) = k`;
* `adjHyp_of_wt_eq_neg_two`: (3.2) at weight `-2`, if `σ_0` and `ρ_{-2}` are invertible and
  `End(E 1_{-2}) = k`.

The invertibility hypotheses are stated in the graded-Hom bicategory: `IsIso (S.grSigma r)`, and
`RightwardCrossing.IsIsoToSum₃`/`IsIsoFromSum₃` for the three components of `ρ_{±2}` (a 2-morphism
of `B` into or out of a direct sum of shifted 1-morphisms is an isomorphism exactly when its
homogeneous components satisfy these).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module

universe w v u

/-! ## Generalities -/

section Generalities

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- Whiskering in a graded bicategory is additive. -/
instance GradedBicategory.additiveWhiskering : AdditiveWhiskering B where
  whiskerLeft_add f _ _ η θ := Categorification.TwoRep.whiskerLeft_add f η θ
  add_whiskerRight η θ h := Categorification.TwoRep.add_whiskerRight η θ h

namespace GradedHomBicat

variable [GradedBicategory.ShiftCoherence B]

/-- Whiskering in the graded-Hom bicategory is additive. -/
instance additiveWhiskering : AdditiveWhiskering (GradedHomBicat B) where
  whiskerLeft_add f _ _ η θ := GradedHomBicat.whiskerLeft_add f η θ
  add_whiskerRight η θ h := GradedHomBicat.add_whiskerRight η θ h

end GradedHomBicat

end Generalities

section Finrank

variable {k : Type*} [Field k] {D : Type*} [Category D] [Preadditive D] [Linear k D] {X : D}

/-- An object with one-dimensional endomorphism algebra is not zero. -/
theorem id_ne_zero_of_finrank_eq_one (h : finrank k (X ⟶ X) = 1) : 𝟙 X ≠ 0 := by
  intro h0
  have hsub : Subsingleton (X ⟶ X) :=
    ⟨fun f g => by
      rw [← Category.comp_id f, ← Category.comp_id g, h0, Limits.comp_zero, Limits.comp_zero]⟩
  rw [Module.finrank_zero_of_subsingleton] at h
  exact zero_ne_one h

/-- If `End(X)` is one-dimensional, its only idempotents are `0` and `1`. -/
theorem eq_zero_or_eq_id_of_finrank_eq_one (h : finrank k (X ⟶ X) = 1) (e : X ⟶ X)
    (he : e ≫ e = e) : e = 0 ∨ e = 𝟙 X := by
  have h1 := id_ne_zero_of_finrank_eq_one h
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 X) h1).mp h e
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at he
  have hc : (c * c - c) • 𝟙 X = 0 := by rw [sub_smul, he, sub_self]
  rcases smul_eq_zero.mp hc with hc' | hc'
  · have hcc : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hc'
    rcases mul_eq_zero.mp hcc with h0 | h1'
    · left; rw [h0, zero_smul]
    · right; rw [sub_eq_zero.mp h1', one_smul]
  · exact absurd hc' h1

end Finrank

/-! ## A strong 2-representation of `sl₂` in the graded-Hom bicategory -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat RightwardCrossing

variable (S : StrongSl2 k B)

/-- `E 1_n` in the graded-Hom bicategory. -/
abbrev grE (r : ℤ) : of (S.obj r) ⟶ of (S.obj (r + 1)) := of₁ (S.E r)

/-- The right adjoint `R_n = 1_n F ⟨n+1⟩` of `E 1_n` (`StrongSl2.adj`) in the graded-Hom
bicategory. -/
abbrev grR (r : ℤ) : of (S.obj (r + 1)) ⟶ of (S.obj r) := of₁ ((S.F r)⟦S.n₀ + 2 * r + 1⟧)

/-- The unit of `E 1_n ⊣ R_n`, of degree `0`. -/
abbrev grUnit (r : ℤ) : 𝟙 (of (S.obj r)) ⟶ S.grE r ≫ S.grR r := incl₂ (S.adj r).unit

/-- The counit of `E 1_n ⊣ R_n`, of degree `0`. -/
abbrev grCounit (r : ℤ) : S.grR r ≫ S.grE r ⟶ 𝟙 (of (S.obj (r + 1))) := incl₂ (S.adj r).counit

/-- The crossing on `E E 1_n`, of degree `-2`. -/
abbrev grCross (r : ℤ) : S.grE r ≫ S.grE (r + 1) ⟶ S.grE r ≫ S.grE (r + 1) :=
  of₂ (-2) (S.cross r)

/-- The dot on `E 1_n`, of degree `2`. -/
abbrev grDot (r : ℤ) : S.grE r ⟶ S.grE r := of₂ 2 (S.dot r)

/-- The normalized dot `r_i⁻¹ x` on `E 1_n`, for which the nilHecke relation reads
`τ ∘ (x E) - (E x) ∘ τ = 1`. -/
abbrev grDotN [GradedBicategory.IsLinear B k] (r : ℤ) : S.grE r ⟶ S.grE r := ((S.rQ⁻¹ : kˣ) : k) • S.grDot r

/-- **The rightward crossing** `σ_λ : E F 1_λ → F E 1_λ` (up to grading shifts; Rouquier's and
Brundan's `σ`, Brundan (1.6)), at the object `r + 1` of weight `λ = S.wt (r + 1)`: a 2-morphism
`R r ≫ E r ⟶ E (r+1) ≫ R (r+1)` of the graded-Hom bicategory, homogeneous of degree `-2`. -/
abbrev grSigma (r : ℤ) : S.grR r ≫ S.grE r ⟶ S.grE (r + 1) ≫ S.grR (r + 1) :=
  sigma (S.grUnit (r + 1)) (S.grCross r) (S.grCounit r)

/-- The zigzag identity for `E 1_n` (from `E 1_n ⊣ R_n`). -/
theorem leftZigzag_grUnit_grCounit (r : ℤ) :
    leftZigzag (S.grUnit r) (S.grCounit r) = (λ_ (S.grE r)).hom ≫ (ρ_ (S.grE r)).inv := by
  rw [leftUnitor_hom_eq, rightUnitor_inv_eq, ← incl₂_comp, leftZigzag_incl₂,
    (S.adj r).left_triangle]

/-- `τ² = 0` (CL `eq_nil_rels`). -/
theorem grCross_sq (r : ℤ) : S.grCross r ≫ S.grCross r = 0 := by
  rw [of₂_comp_of₂ _ _ (by norm_num : (-2 : ℤ) + -2 = -4), S.cross_sq r, of₂_zero]

section Linear

variable [GradedBicategory.IsLinear B k]

/-- The dot-slide relation (CL `eq_nil_dotslide`, first equality) for the normalized dot:
`τ ∘ (x E) - (E x) ∘ τ = 1`. -/
theorem grDotN_slide (r : ℤ) :
    S.grE r ◁ S.grDotN (r + 1) ≫ S.grCross r - S.grCross r ≫ S.grDotN r ▷ S.grE (r + 1) =
      𝟙 _ := by
  have h := congrArg (of₂ (0 : ℤ)) (S.dot_slide_left r)
  rw [of₂_sub, ← of₂_comp_of₂, ← of₂_comp_of₂, ← whiskerLeft_of₂, ← of₂_whiskerRight,
    ShiftedHom.mk₀_smul, of₂_smul] at h
  rw [GradedHomBicat.whiskerLeft_smul, GradedHomBicat.smul_whiskerRight, Linear.smul_comp,
    Linear.comp_smul, ← smul_sub, ← h, smul_smul, Units.inv_mul, one_smul]
  rfl

end Linear

/-- The braid relation for the crossings on `E E E 1_n` (CL `eq_nil_rels`). -/
theorem grCross_braid (r : ℤ) :
    S.grE r ◁ S.grCross (r + 1) ≫
        ((α_ (S.grE r) (S.grE (r + 1)) (S.grE (r + 1 + 1))).inv ≫
          S.grCross r ▷ S.grE (r + 1 + 1) ≫
          (α_ (S.grE r) (S.grE (r + 1)) (S.grE (r + 1 + 1))).hom) ≫
        S.grE r ◁ S.grCross (r + 1) =
      ((α_ (S.grE r) (S.grE (r + 1)) (S.grE (r + 1 + 1))).inv ≫
          S.grCross r ▷ S.grE (r + 1 + 1) ≫
          (α_ (S.grE r) (S.grE (r + 1)) (S.grE (r + 1 + 1))).hom) ≫
        S.grE r ◁ S.grCross (r + 1) ≫
        ((α_ (S.grE r) (S.grE (r + 1)) (S.grE (r + 1 + 1))).inv ≫
          S.grCross r ▷ S.grE (r + 1 + 1) ≫
          (α_ (S.grE r) (S.grE (r + 1)) (S.grE (r + 1 + 1))).hom) := by
  have h := congrArg (of₂ (-6 : ℤ)) (S.braid r)
  simp only [← of₂_comp_of₂, Category.assoc] at h
  simp only [whiskerLeft_of₂, of₂_whiskerRight, associator_hom_eq, associator_inv_eq,
    incl₂_eq_of₂, Category.assoc]
  exact h

/-- The rightward crossing is homogeneous of degree `-2`. -/
theorem isHomogeneous_grSigma (r : ℤ) : IsHomogeneous (S.grSigma r) (-2) := by
  rw [grSigma, sigma_eq]
  refine (isHomogeneous_rightUnitor_inv _).comp ?_ (by norm_num : (-2 : ℤ) + 0 = -2)
  refine (isHomogeneous_whiskerLeft _ (isHomogeneous_incl₂ _)).comp ?_
    (by norm_num : (-2 : ℤ) + 0 = -2)
  refine (isHomogeneous_associator_hom _ _ _).comp ?_ (by norm_num : (-2 : ℤ) + 0 = -2)
  refine (isHomogeneous_whiskerLeft _ (isHomogeneous_associator_inv _ _ _)).comp ?_
    (by norm_num : (-2 : ℤ) + 0 = -2)
  refine (isHomogeneous_whiskerLeft _
    (isHomogeneous_whiskerRight (isHomogeneous_of₂ _ _) _)).comp ?_
    (by norm_num : (0 : ℤ) + -2 = -2)
  refine (isHomogeneous_whiskerLeft _ (isHomogeneous_associator_hom _ _ _)).comp ?_
    (by norm_num : (0 : ℤ) + 0 = 0)
  refine (isHomogeneous_associator_inv _ _ _).comp ?_ (by norm_num : (0 : ℤ) + 0 = 0)
  exact (isHomogeneous_whiskerRight (isHomogeneous_incl₂ _) _).comp
    (isHomogeneous_leftUnitor_hom _) (by norm_num : (0 : ℤ) + 0 = 0)

/-- **The rightward crossing as a shifted 2-morphism of `B`**:
`σ_λ : R r ≫ E r ⟶ (E (r+1) ≫ R (r+1))⟨-2⟩`, where `R r = (F r)⟨n+1⟩` is the right adjoint of
`E r = E 1_n` and `λ = n + 2`. -/
def sigma (r : ℤ) :
    ShiftedHom ((S.F r)⟦S.n₀ + 2 * r + 1⟧ ≫ S.E r)
      (S.E (r + 1) ≫ (S.F (r + 1))⟦S.n₀ + 2 * (r + 1) + 1⟧) (-2 : ℤ) :=
  component (-2) (S.grSigma r)

theorem grSigma_eq (r : ℤ) : S.grSigma r = of₂ (-2) (S.sigma r) :=
  (S.isHomogeneous_grSigma r).eq_homOf_component

/-- If `σ_λ` is an isomorphism of `B` (onto the shifted 1-morphism), it is an isomorphism of the
graded-Hom bicategory. -/
theorem isIso_grSigma (r : ℤ) [IsIso (S.sigma r)] : IsIso (S.grSigma r) := by
  rw [grSigma_eq]
  exact isIso_of₂ _ _

/-! ## From a homogeneous zigzag to the adjoint induction hypothesis -/

section Linear

variable [GradedBicategory.IsLinear B k]

omit [GradedBicategory.ShiftCoherence B] in
/-- `End(1_n F ⟨m⟩) ≅ End(E 1_n)` (mates under `E 1_n ⊣ 1_n F ⟨n+1⟩`), on dimensions. -/
theorem finrank_end_F_shift (r m : ℤ) :
    finrank k ((S.F r)⟦m⟧ ⟶ (S.F r)⟦m⟧) = finrank k (S.E r ⟶ S.E r) := by
  calc finrank k ((S.F r)⟦m⟧ ⟶ (S.F r)⟦m⟧)
      = finrank k (S.F r ⟶ S.F r) := finrank_hom_shift k _ _ m
    _ = finrank k ((S.F r)⟦S.wt r + 1⟧ ⟶ (S.F r)⟦S.wt r + 1⟧) :=
        (finrank_hom_shift k _ _ _).symm
    _ = finrank k ((S.F r)⟦S.wt r + 1⟧ ≫ 𝟙 _ ⟶ (S.F r)⟦S.wt r + 1⟧) :=
        finrank_hom_congr_left k (ρ_ _).symm _
    _ = finrank k (𝟙 _ ⟶ S.E r ≫ (S.F r)⟦S.wt r + 1⟧) :=
        ((S.dimAdj r).right (𝟙 _) _).symm
    _ = finrank k (𝟙 _ ≫ S.E r ⟶ S.E r) := ((S.dimAdj r).left (𝟙 _) (S.E r)).symm
    _ = finrank k (S.E r ⟶ S.E r) := finrank_hom_congr_left k (λ_ _) _

/-- **From a homogeneous zigzag to (3.2).** Let `u : 𝟙 ⟶ E_n R_n` and `c : R_n E_n ⟶ 𝟙` be
2-morphisms of the graded-Hom bicategory, homogeneous of degrees `-2n-2` and `2n+2`, satisfying
the zigzag identity for `E_n = E 1_n`. If `End(E 1_n)` is one-dimensional, then
`1_n F ⟨-n-1⟩ = R_n ⟨-2n-2⟩` is left adjoint to `E 1_n`: the adjoint induction hypothesis (3.2)
at `n`. (One-zigzag lemma; the other zigzag is an idempotent of `End(1_n F ⟨-n-1⟩) ≅ End(E 1_n)`,
which is nonzero since `E 1_n` is.) -/
theorem adjHyp_of_rightZigzag (r : ℤ)
    (u : 𝟙 (of (S.obj (r + 1))) ⟶ S.grR r ≫ S.grE r)
    (c : S.grE r ≫ S.grR r ⟶ 𝟙 (of (S.obj r)))
    (hu : IsHomogeneous u (-(2 * S.wt r + 2))) (hc : IsHomogeneous c (2 * S.wt r + 2))
    (hz : rightZigzag u c = (ρ_ (S.grE r)).hom ≫ (λ_ (S.grE r)).inv)
    (hend : finrank k (S.E r ⟶ S.E r) = 1) : S.AdjHyp r := by
  let θ : of₁ ((S.F r)⟦-(S.wt r + 1)⟧) ≅ S.grR r :=
    shiftIso₁ (S.F r) (-(S.wt r + 1)) ≪≫ (shiftIso₁ (S.F r) (S.n₀ + 2 * r + 1)).symm
  have hθ : IsHomogeneous θ.hom (-(2 * S.wt r + 2)) :=
    (shiftIso₁_hom_isHomogeneous (S.F r) (-(S.wt r + 1))).comp
      (shiftIso₁_inv_isHomogeneous (S.F r) (S.n₀ + 2 * r + 1)) (by simp only [wt]; ring)
  have hθ' : IsHomogeneous θ.inv (2 * S.wt r + 2) :=
    (shiftIso₁_hom_isHomogeneous (S.F r) (S.n₀ + 2 * r + 1)).comp
      (shiftIso₁_inv_isHomogeneous (S.F r) (-(S.wt r + 1))) (by simp only [wt]; ring)
  have hη : IsHomogeneous (u ≫ θ.inv ▷ S.grE r) 0 :=
    hu.comp (isHomogeneous_whiskerRight hθ' _) (by ring)
  have hε : IsHomogeneous (S.grE r ◁ θ.hom ≫ c) 0 :=
    (isHomogeneous_whiskerLeft _ hθ).comp hc (by ring)
  obtain ⟨(η₀ : 𝟙 (S.obj (r + 1)) ⟶ (S.F r)⟦-(S.wt r + 1)⟧ ≫ S.E r), hη₀⟩ :=
    hη.exists_incl_map
  obtain ⟨(ε₀ : S.E r ≫ (S.F r)⟦-(S.wt r + 1)⟧ ⟶ 𝟙 (S.obj r)), hε₀⟩ := hε.exists_incl_map
  have hz' := rightZigzag_comp_iso u c θ
  rw [hη₀, hε₀, hz] at hz'
  have h₀ : rightZigzag η₀ ε₀ = (ρ_ (S.E r)).hom ≫ (λ_ (S.E r)).inv := by
    apply incl₂_injective
    rw [← rightZigzag_incl₂, incl₂_comp]
    exact hz'
  exact ⟨adjunctionOfRightTriangle η₀ ε₀ h₀
    (eq_zero_or_eq_id_of_finrank_eq_one ((S.finrank_end_F_shift r _).trans hend))
    (id_ne_zero_of_finrank_eq_one hend)⟩

/-! ## The weights `0` and `-2` -/

/-- **(3.2) at weight `0`** (CL Proposition 3.9 at `n = 0`, by Brundan's Theorem 4.3). Let
`s + 1` be the object of weight `0`, so that `E_{-2} = E s`, `E_0 = E (s+1)`, `E_2 = E (s+2)`.
Assume that

* `σ_0 : E_{-2} R_{-2} → R_0 E_0` is invertible;
* `ρ_2 = (σ_2, ε_0, ε_0 ∘ (x R_0)) : E_0 R_0 → R_2 E_2 ⊕ 1_2 ⊕ 1_2` is invertible (both in the
  graded-Hom bicategory, i.e. up to the grading shifts that make these maps homogeneous of
  degree `0`);
* `End(E 1_0)` is one-dimensional (CL Lemma 3.1).

Then `(E 1_0)_L ≅ 1_0 F ⟨-1⟩`. The unit is the last component of `ρ_2⁻¹` (times `r_i`) and the
counit is `ε_{-2} ∘ σ_0⁻¹`. -/
theorem adjHyp_of_wt_eq_zero {s : ℤ} (h0 : S.wt (s + 1) = 0) (hσ : IsIso (S.grSigma s))
    (hρ : IsIsoToSum₃ (S.grSigma (s + 1)) (S.grCounit (s + 1))
      (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1)))
    (hend : finrank k (S.E (s + 1) ⟶ S.E (s + 1)) = 1) : S.AdjHyp (s + 1) := by
  obtain ⟨g₁, g₂, g₃, hsum, -, -, hu₁, hu₂, hu₃⟩ := hρ
  have hc : ((S.rQ⁻¹ : kˣ) : k) * (S.rQ : k) = 1 := Units.inv_mul _
  have hc' : (S.rQ : k) * ((S.rQ⁻¹ : kˣ) : k) = 1 := Units.mul_inv _
  have hf₃ : S.grR (s + 1) ◁ S.grDotN (s + 1) ≫ S.grCounit (s + 1) =
      ((S.rQ⁻¹ : kˣ) : k) • (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1)) := by
    rw [GradedHomBicat.whiskerLeft_smul, Linear.smul_comp]
  have hz := rightZigzag_zero (S.grUnit (s + 1)) (S.grCounit (s + 1)) (S.grCross s)
    (S.grCounit s) (S.grUnit (s + 1 + 1)) (S.grCross (s + 1))
    (S.leftZigzag_grUnit_grCounit (s + 1)) (S.grCross_sq s) (S.grCross_sq (s + 1))
    (S.grDotN s) (S.grDotN (s + 1)) (S.grDotN_slide s) (S.grCross_braid s)
    (σi := inv (S.grSigma s)) (IsIso.hom_inv_id _) (IsIso.inv_hom_id _)
    (s := g₁) (u₀ := g₂) (u₁ := (S.rQ : k) • g₃)
    (by rw [hf₃, Linear.smul_comp, Linear.comp_smul, smul_smul, hc, one_smul]; exact hsum)
    (by rw [Linear.smul_comp, hu₁, smul_zero])
    (by rw [Linear.smul_comp, hu₂, smul_zero])
    (by rw [hf₃, Linear.smul_comp, Linear.comp_smul, smul_smul, hc', one_smul]; exact hu₃)
  have hg₃ : IsHomogeneous g₃ (-2) :=
    isHomogeneous_of_comp_eq (S.isHomogeneous_grSigma (s + 1)) (isHomogeneous_incl₂ _)
      ((isHomogeneous_whiskerLeft _ (isHomogeneous_of₂ _ _)).comp (isHomogeneous_incl₂ _)
        (by norm_num : (0 : ℤ) + 2 = 2)) hsum hu₁ hu₂ hu₃
  have hσi : IsHomogeneous (inv (S.grSigma s)) 2 :=
    (S.isHomogeneous_grSigma s).inv.of_eq (by norm_num)
  refine S.adjHyp_of_rightZigzag (s + 1) _ _ ((hg₃.smul (S.rQ : k)).of_eq ?_)
    ((hσi.comp (isHomogeneous_incl₂ _) (by norm_num : (0 : ℤ) + 2 = 2)).of_eq ?_) hz hend
  · rw [h0]; norm_num
  · rw [h0]; norm_num

/-- **(3.2) at weight `-2`** (CL Proposition 3.9 at `n = -2`, by Brundan's Theorem 4.3). Let
`s + 1` be the object of weight `-2`, so that `E_{-4} = E s`, `E_{-2} = E (s+1)`,
`E_0 = E (s+2)`. Assume that

* `σ_0 : E_{-2} R_{-2} → R_0 E_0` is invertible;
* `ρ_{-2} = (σ_{-2}, η_{-2}, (R_{-2} x) ∘ η_{-2}) : E_{-4} R_{-4} ⊕ 1_{-2} ⊕ 1_{-2} → R_{-2} E_{-2}`
  is invertible (both in the graded-Hom bicategory);
* `End(E 1_{-2})` is one-dimensional (CL Lemma 3.1 for `n ≤ 0`).

Then `(E 1_{-2})_L ≅ 1_{-2} F ⟨1⟩`. The unit is `-σ_0⁻¹ ∘ η_0` and the counit is the last
component of `ρ_{-2}⁻¹` (times `r_i`). -/
theorem adjHyp_of_wt_eq_neg_two {s : ℤ} (h2 : S.wt (s + 1) = -2)
    (hσ : IsIso (S.grSigma (s + 1)))
    (hρ : IsIsoFromSum₃ (S.grSigma s) (S.grUnit (s + 1))
      (S.grUnit (s + 1) ≫ S.grDot (s + 1) ▷ S.grR (s + 1)))
    (hend : finrank k (S.E (s + 1) ⟶ S.E (s + 1)) = 1) : S.AdjHyp (s + 1) := by
  obtain ⟨t, w₀, w₁, hsum, ⟨-, -, hw₁⟩, ⟨-, -, hw₂⟩, -, -, hw₃⟩ := hρ
  have hc : ((S.rQ⁻¹ : kˣ) : k) * (S.rQ : k) = 1 := Units.inv_mul _
  have hc' : (S.rQ : k) * ((S.rQ⁻¹ : kˣ) : k) = 1 := Units.mul_inv _
  have hf₃ : S.grUnit (s + 1) ≫ S.grDotN (s + 1) ▷ S.grR (s + 1) =
      ((S.rQ⁻¹ : kˣ) : k) • (S.grUnit (s + 1) ≫ S.grDot (s + 1) ▷ S.grR (s + 1)) := by
    rw [GradedHomBicat.smul_whiskerRight, Linear.comp_smul]
  have hz := rightZigzag_neg_two (S.grUnit (s + 1)) (S.grCounit (s + 1)) (S.grCross s)
    (S.grCounit s) (S.grUnit (s + 1 + 1)) (S.grCross (s + 1))
    (S.leftZigzag_grUnit_grCounit (s + 1)) (S.grCross_sq s) (S.grCross_sq (s + 1))
    (S.grDotN (s + 1)) (S.grDotN (s + 1 + 1)) (S.grDotN_slide (s + 1)) (S.grCross_braid s)
    (σi := inv (S.grSigma (s + 1))) (IsIso.hom_inv_id _) (IsIso.inv_hom_id _)
    (t := t) (w₀ := w₀) (w₁ := (S.rQ : k) • w₁)
    (by rw [hf₃, Linear.smul_comp, Linear.comp_smul, smul_smul, hc', one_smul]; exact hsum)
    (by rw [Linear.comp_smul, hw₁, smul_zero])
    (by rw [Linear.comp_smul, hw₂, smul_zero])
    (by rw [hf₃, Linear.smul_comp, Linear.comp_smul, smul_smul, hc, one_smul]; exact hw₃)
  have hw : IsHomogeneous w₁ (-2) :=
    isHomogeneous_of_eq_comp (S.isHomogeneous_grSigma s) (isHomogeneous_incl₂ _)
      ((isHomogeneous_incl₂ _).comp (isHomogeneous_whiskerRight (isHomogeneous_of₂ _ _) _)
        (by norm_num : (2 : ℤ) + 0 = 2)) hsum hw₁ hw₂ hw₃
  have hσi : IsHomogeneous (inv (S.grSigma (s + 1))) 2 :=
    (S.isHomogeneous_grSigma (s + 1)).inv.of_eq (by norm_num)
  refine S.adjHyp_of_rightZigzag (s + 1) _ _
    (((isHomogeneous_incl₂ _).comp hσi (by norm_num : (2 : ℤ) + 0 = 2)).neg.of_eq ?_)
    ((hw.smul (S.rQ : k)).of_eq ?_) hz hend
  · rw [h2]; norm_num
  · rw [h2]; norm_num

end Linear

end StrongSl2

end Categorification.TwoRep
