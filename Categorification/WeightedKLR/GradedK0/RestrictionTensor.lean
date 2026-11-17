/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.CoproductK0
import Categorification.WeightedKLR.Induction.Coassociativity

/-!
# Graded restriction along tensor products

For Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Proposition 2.18 and Theorem 2.19, restriction along a juxtaposition on one tensor
factor leaves the other factor in place. This supplies the graded restriction maps
for both parenthesizations of the coproduct.
-/

noncomputable section

namespace Categorification

open InductionAlong DirectSum
open scoped TensorProduct

namespace Graded

section Restriction

universe u v

variable {k : Type v} [CommRing k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}
  (φ : A →ₙ+* B) (hφ : ∀ (c : k) (a : A), φ (c • a) = c • φ a)

attribute [local instance] Res.moduleK Res.isScalarTowerK

/-- The inclusion of the fixed submodule underlying restriction. -/
def GProj.resVal (P : GProj ℬ) : Res φ P.carrier →ₗ[k] P.carrier where
  toFun := Res.val
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k A c) • x.val = c • x.val
    rw [Algebra.algebraMap_eq_smul_one, hφ, smul_assoc, x.prop]

/-- The degree-zero projection onto the fixed submodule. -/
def GProj.resProj (P : GProj ℬ) : P.carrier →ₗ[k] Res φ P.carrier where
  toFun x := Res.mk (φ 1 • x) (by rw [smul_smul, ← map_mul, one_mul])
  map_add' x y := Res.ext (smul_add _ x y)
  map_smul' c x := Res.ext (by
    change φ 1 • c • x = (P.resVal φ hφ) (c • Res.mk (φ 1 • x) _)
    rw [map_smul]
    exact smul_comm _ _ _)

theorem GProj.resProj_resVal (P : GProj ℬ) (x : Res φ P.carrier) :
    P.resProj φ hφ (P.resVal φ hφ x) = x :=
  Res.ext x.prop

private theorem resGrade_isInternal (P : GProj ℬ) (h1 : φ 1 ∈ ℬ 0) :
    IsInternal (Graded.comap P.grading (P.resVal φ hφ)) := by
  refine isInternal_comap _ _ (fun _ _ h => Res.ext h) fun x d => ?_
  refine ⟨Res.mk _ ?_, rfl⟩
  change φ 1 • (decompose P.grading x.val d : P.carrier) = decompose P.grading x.val d
  rw [← decompose_smul_of_mem_zero P.grading h1, x.prop]

variable [GradedAlgebra 𝒜]
  (hg : ∀ ⦃d : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 d → φ a ∈ ℬ d)
  [Module.Finite A (Res φ B)] [Module.Projective A (Res φ B)]

/-- Restriction along a graded nonunital map, with the grading induced from the ambient module. -/
def GProj.resAlong (P : GProj ℬ) : GProj 𝒜 where
  carrier := Res φ P.carrier
  grading := Graded.comap P.grading (P.resVal φ hφ)
  decomposition := (resGrade_isInternal φ hφ P (hg SetLike.GradedOne.one_mem)).chooseDecomposition
  gradedSMul := ⟨fun _ _ _ _ ha hx => P.gradedSMul.smul_mem (hg ha) hx⟩
  finite := Res.finite_of_regular φ P.carrier
  projective := Res.projective_of_regular φ P.carrier

private def resAlongAdd : K0 ℬ →+ K0 𝒜 :=
  K0.lift (fun P => K0.of (P.resAlong φ hφ hg))
    (fun P Q e => K0.of_eq_of_iso
      (GradedEquiv.ofPreserves (Res.congr φ e.toLinearEquiv) (fun _ _ hx => e.map_mem hx)))
    (fun P Q => by
      rw [K0.of_eq_of_iso (show (GProj.resAlong φ hφ hg (P.prod Q)).Iso
        ((P.resAlong φ hφ hg).prod (Q.resAlong φ hφ hg)) from
        GradedEquiv.ofPreserves (Res.prodEquiv φ P.carrier Q.carrier) (fun _ _ hx => hx)),
        K0.of_prod])

/-- Restriction of graded projective classes along a graded nonunital map. -/
def K0.resAlong : K0 ℬ →ₗ[LaurentPolynomial ℤ] K0 𝒜 :=
  { resAlongAdd φ hφ hg with
    map_smul' := K0.map_smul_of_shift _ (fun d x => by
      induction x using K0.induction_on with
      | of P =>
        rw [K0.shiftHom_of]
        change resAlongAdd φ hφ hg (K0.of (P.shift d)) =
          K0.shiftHom d (resAlongAdd φ hφ hg (K0.of P))
        simp only [resAlongAdd, K0.lift_of, K0.shiftHom_of]
        exact K0.of_eq_of_iso (GradedEquiv.ofPreserves (LinearEquiv.refl _ _) (fun _ _ hx => hx))
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | neg x hx => simp only [map_neg, hx]) }

@[simp] theorem K0.resAlong_of (P : GProj ℬ) :
    K0.resAlong φ hφ hg (K0.of P) = K0.of (P.resAlong φ hφ hg) :=
  by
    change resAlongAdd φ hφ hg (K0.of P) = _
    simp only [resAlongAdd, K0.lift_of]

end Restriction

section TensorRestriction

open WeightedKLR.Juxtapose

universe u v

variable {k : Type v} [Field k] {A B C : Type u}
  [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C] [Algebra k C]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} {𝒞 : ℤ → Submodule k C}
  (φ : A →ₙ+* B) (hφ : ∀ (c : k) (a : A), φ (c • a) = c • φ a)
  (hg : ∀ ⦃d : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 d → φ a ∈ ℬ d)

attribute [local instance] Res.moduleK Res.isScalarTowerK

include hg in
theorem tensorLeft_mem_grading {d : ℤ} {x : A ⊗[k] C}
    (hx : x ∈ tensorGrading 𝒜 𝒞 d) :
    tensorLeft k C φ hφ x ∈ tensorGrading ℬ 𝒞 d :=
  tensorGrading_map_mem _ _ _ (TensorProduct.map (linearOf k φ hφ) LinearMap.id)
    (fun _ _ _ _ ha hc => tmul_mem_tensorGrading (hg ha) hc) hx

include hg in
theorem tensorRight_mem_grading {d : ℤ} {x : C ⊗[k] A}
    (hx : x ∈ tensorGrading 𝒞 𝒜 d) :
    tensorRight k C φ hφ x ∈ tensorGrading 𝒞 ℬ d :=
  tensorGrading_map_mem _ _ _ (TensorProduct.map LinearMap.id (linearOf k φ hφ))
    (fun _ _ _ _ hc ha => tmul_mem_tensorGrading hc (hg ha)) hx

variable [GradedAlgebra 𝒜] [GradedAlgebra 𝒞]
  [Module.Finite A (Res φ B)] [Module.Projective A (Res φ B)]

private noncomputable instance resTensorLeft_finite :
    Module.Finite (A ⊗[k] C) (Res (tensorLeft k C φ hφ) (B ⊗[k] C)) :=
  Res.tensorLeft_finite k C φ hφ _

private noncomputable instance resTensorLeft_projective :
    Module.Projective (A ⊗[k] C) (Res (tensorLeft k C φ hφ) (B ⊗[k] C)) :=
  Res.tensorLeft_projective k C φ hφ _

private noncomputable instance resTensorRight_finite :
    Module.Finite (C ⊗[k] A) (Res (tensorRight k C φ hφ) (C ⊗[k] B)) :=
  Res.tensorRight_finite k C φ hφ _

private noncomputable instance resTensorRight_projective :
    Module.Projective (C ⊗[k] A) (Res (tensorRight k C φ hφ) (C ⊗[k] B)) :=
  Res.tensorRight_projective k C φ hφ _

/-- Restriction on the left tensor factor on graded projectives. -/
def GProj.resTensorLeft (P : GProj (tensorGrading ℬ 𝒞)) : GProj (tensorGrading 𝒜 𝒞) :=
  P.resAlong (tensorLeft k C φ hφ) (tensorLeft_smul k C φ hφ) (fun _ _ hx => tensorLeft_mem_grading φ hφ hg hx)

/-- Restriction on the right tensor factor on graded projectives. -/
def GProj.resTensorRight (P : GProj (tensorGrading 𝒞 ℬ)) : GProj (tensorGrading 𝒞 𝒜) :=
  P.resAlong (tensorRight k C φ hφ) (tensorRight_smul k C φ hφ) (fun _ _ hx => tensorRight_mem_grading φ hφ hg hx)

/-- Restriction on the left tensor factor on graded projective classes. -/
def K0.resTensorLeft : K0 (tensorGrading ℬ 𝒞) →ₗ[LaurentPolynomial ℤ] K0 (tensorGrading 𝒜 𝒞) :=
  K0.resAlong (tensorLeft k C φ hφ) (tensorLeft_smul k C φ hφ) (fun _ _ hx => tensorLeft_mem_grading φ hφ hg hx)

/-- Restriction on the right tensor factor on graded projective classes. -/
def K0.resTensorRight : K0 (tensorGrading 𝒞 ℬ) →ₗ[LaurentPolynomial ℤ] K0 (tensorGrading 𝒞 𝒜) :=
  K0.resAlong (tensorRight k C φ hφ) (tensorRight_smul k C φ hφ) (fun _ _ hx => tensorRight_mem_grading φ hφ hg hx)

@[simp] theorem K0.resTensorLeft_of (P : GProj (tensorGrading ℬ 𝒞)) :
    K0.resTensorLeft φ hφ hg (K0.of P) = K0.of (P.resTensorLeft φ hφ hg) :=
  K0.resAlong_of _ _ _ P

@[simp] theorem K0.resTensorRight_of (P : GProj (tensorGrading 𝒞 ℬ)) :
    K0.resTensorRight φ hφ hg (K0.of P) = K0.of (P.resTensorRight φ hφ hg) :=
  K0.resAlong_of _ _ _ P

variable (P : GProj ℬ) (Q : GProj 𝒞)

private def Res.equivOfSplitting {A' B' : Type u} [Ring A'] [Ring B']
    (ψ : A' →ₙ+* B') {X Y : Type*}
    [AddCommGroup X] [Module k X] [Module A' X]
    [AddCommGroup Y] [Module k Y] [Module B' Y]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = ψ 1 • y)
    (hf : ∀ a x, f (a • x) = ψ a • f x) :
    X ≃ₗ[A'] Res ψ Y where
  toFun x := Res.mk (f x) (by rw [← hfg, hgf])
  invFun y := g y.val
  left_inv := hgf
  right_inv y := Res.ext ((hfg y.val).trans y.prop)
  map_add' x y := Res.ext (map_add f x y)
  map_smul' a x := Res.ext (hf a x)

private def resTensorLeftVal :
    ExtTensor k (Res φ P.carrier) Q.carrier →ₗ[k] ExtTensor k P.carrier Q.carrier :=
  TensorProduct.map (P.resVal φ hφ) LinearMap.id

private def resTensorLeftProj :
    ExtTensor k P.carrier Q.carrier →ₗ[k] ExtTensor k (Res φ P.carrier) Q.carrier :=
  TensorProduct.map (P.resProj φ hφ) LinearMap.id

private def resTensorRightVal :
    ExtTensor k Q.carrier (Res φ P.carrier) →ₗ[k] ExtTensor k Q.carrier P.carrier :=
  TensorProduct.map LinearMap.id (P.resVal φ hφ)

private def resTensorRightProj :
    ExtTensor k Q.carrier P.carrier →ₗ[k] ExtTensor k Q.carrier (Res φ P.carrier) :=
  TensorProduct.map LinearMap.id (P.resProj φ hφ)

/-- Restriction on the left tensor factor commutes with graded external tensor products. -/
def GProj.extTensor_resTensorLeft :
    ((P.resAlong φ hφ hg).extTensor Q).Iso ((P.extTensor Q).resTensorLeft (𝒜 := 𝒜) φ hφ hg) := by
  let f := resTensorLeftVal φ hφ P Q
  let g := resTensorLeftProj φ hφ P Q
  have hgf : ∀ x, g (f x) = x := by
    intro x
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul p q =>
      change ExtTensor.tmul (P.resProj φ hφ (P.resVal φ hφ p)) q = ExtTensor.tmul p q
      rw [P.resProj_resVal]
  have hfg : ∀ y, f (g y) = tensorLeft k C φ hφ 1 • y := by
    intro y
    induction y using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | tmul p q =>
      change ExtTensor.tmul (φ 1 • p) q = tensorLeft k C φ hφ 1 • ExtTensor.tmul p q
      rw [tensorLeft_one, ExtTensor.smul_tmul, one_smul]
  have hf : ∀ a x, f (a • x) = tensorLeft k C φ hφ a • f x := by
    refine extTensor_smul_eq_along (tensorLeft k C φ hφ).toAddMonoidHom
      (map_add f) (map_zero f) fun a c p q => ?_
    rw [ExtTensor.smul_tmul]
    change ExtTensor.tmul (φ a • p.val) (c • q) =
      tensorLeft k C φ hφ (a ⊗ₜ c) • ExtTensor.tmul p.val q
    rw [tensorLeft_tmul, ExtTensor.smul_tmul]
  refine GradedEquiv.ofPreserves (Res.equivOfSplitting (tensorLeft k C φ hφ) f g hgf hfg hf)
    (fun d x hx => ?_)
  change f x ∈ ExtTensor.grading P.grading Q.grading d
  refine ExtTensor.grading_map_mem (P.resAlong φ hφ hg).grading Q.grading
    (ExtTensor.grading P.grading Q.grading) f (fun _ _ p q hp hq => ?_) hx
  exact ExtTensor.tmul_mem_grading (p := P.resVal φ hφ p) (q := q) hp hq

/-- Restriction on the right tensor factor commutes with graded external tensor products. -/
def GProj.extTensor_resTensorRight :
    (Q.extTensor (P.resAlong φ hφ hg)).Iso ((Q.extTensor P).resTensorRight (𝒜 := 𝒜) φ hφ hg) := by
  let f := resTensorRightVal φ hφ P Q
  let g := resTensorRightProj φ hφ P Q
  have hgf : ∀ x, g (f x) = x := by
    intro x
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul q p =>
      change ExtTensor.tmul q (P.resProj φ hφ (P.resVal φ hφ p)) = ExtTensor.tmul q p
      rw [P.resProj_resVal]
  have hfg : ∀ y, f (g y) = tensorRight k C φ hφ 1 • y := by
    intro y
    induction y using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | tmul q p =>
      change ExtTensor.tmul q (φ 1 • p) = tensorRight k C φ hφ 1 • ExtTensor.tmul q p
      rw [tensorRight_one, ExtTensor.smul_tmul, one_smul]
  have hf : ∀ a x, f (a • x) = tensorRight k C φ hφ a • f x := by
    refine extTensor_smul_eq_along (tensorRight k C φ hφ).toAddMonoidHom
      (map_add f) (map_zero f) fun c a q p => ?_
    rw [ExtTensor.smul_tmul]
    change ExtTensor.tmul (c • q) (φ a • p.val) =
      tensorRight k C φ hφ (c ⊗ₜ a) • ExtTensor.tmul q p.val
    rw [tensorRight_tmul, ExtTensor.smul_tmul]
  refine GradedEquiv.ofPreserves (Res.equivOfSplitting (tensorRight k C φ hφ) f g hgf hfg hf)
    (fun d x hx => ?_)
  change f x ∈ ExtTensor.grading Q.grading P.grading d
  refine ExtTensor.grading_map_mem Q.grading (P.resAlong φ hφ hg).grading
    (ExtTensor.grading Q.grading P.grading) f (fun _ _ q p hq hp => ?_) hx
  exact ExtTensor.tmul_mem_grading (p := q) (q := P.resVal φ hφ p) hq hp

/-- The left tensor restriction identity on graded Grothendieck groups. -/
theorem K0.resTensorLeft_extTensor (x : K0 ℬ) (y : K0 𝒞) :
    K0.resTensorLeft (𝒜 := 𝒜) φ hφ hg (K0.extTensor ℬ 𝒞 x y) =
      K0.extTensor 𝒜 𝒞 (K0.resAlong φ hφ hg x) y := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]
  | of P =>
    induction y using K0.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
    | of Q =>
      simp only [K0.extTensor_of, K0.resTensorLeft_of, K0.resAlong_of]
      exact (K0.of_eq_of_iso (P.extTensor_resTensorLeft φ hφ hg Q)).symm

/-- The right tensor restriction identity on graded Grothendieck groups. -/
theorem K0.resTensorRight_extTensor (x : K0 𝒞) (y : K0 ℬ) :
    K0.resTensorRight (𝒜 := 𝒜) φ hφ hg (K0.extTensor 𝒞 ℬ x y) =
      K0.extTensor 𝒞 𝒜 x (K0.resAlong φ hφ hg y) := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]
  | of Q =>
    induction y using K0.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
    | of P =>
      simp only [K0.extTensor_of, K0.resTensorRight_of, K0.resAlong_of]
      exact (K0.of_eq_of_iso (P.extTensor_resTensorRight φ hφ hg Q)).symm

end TensorRestriction

end Graded

end Categorification
