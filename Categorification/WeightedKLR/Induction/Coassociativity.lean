/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Restriction
import Categorification.WeightedKLR.Induction.ModuleMonoidal

/-!
# Coassociativity of the coproduct of `⊕_ν K₀(W_ν)`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4: by
Proposition 2.18 restriction is comonoidal, and Theorem 2.19 uses this for the coassociativity
of the coproduct `Δ[L] = Σ [Res_{ν';ν''} L]` of `K = ⊕_ν K₀(W_ν)`. This file proves the
coassociativity on `K₀`, over every commutative ring `k`, under the hypotheses of
`Juxtapose.res_projective`.

The iterated coproducts land in `K₀((W_{ν₁} ⊗ W_{ν₂}) ⊗ W_{ν₃})` and
`K₀(W_{ν₁} ⊗ (W_{ν₂} ⊗ W_{ν₃}))`, through restriction along `ι_{ν₁;ν₂} ⊗ id` and
`id ⊗ ι_{ν₂;ν₃}`. That these restrictions preserve finitely generated projective modules is the
one new input. It holds for any nonunital `k`-linear ring map `φ : A → B` with `Res φ B`
finitely generated projective: `Res (φ ⊗ id) (B ⊗ C) ≅ Res φ B ⊠ C`.

## Main definitions and results

* `InductionAlong.Res.tensorLeftEquiv`: `Res φ B ⊠ C ≅ Res (φ ⊗ id) (B ⊗ C)`;
  `InductionAlong.Res.tensorRightEquiv`: `C ⊠ Res φ B ≅ Res (id ⊗ φ) (C ⊗ B)`.
* `InductionAlong.Res.tensorLeft_projective`, `tensorLeft_finite`, `tensorRight_projective`,
  `tensorRight_finite`: if `Res φ B` is finitely generated projective, restriction along
  `φ ⊗ id` and `id ⊗ φ` preserves finitely generated projective modules.
* `Juxtapose.resLeftK0`, `Juxtapose.resRightK0`: `Δ_{ν₁;ν₂} ⊗ id` and `id ⊗ Δ_{ν₂;ν₃}` on
  `K₀`, as restriction along `ι ⊗ id` and `id ⊗ ι`.
* `Juxtapose.resK0_coassoc`: `(Δ_{ν₁;ν₂} ⊗ id) ∘ Δ_{ν₁+ν₂;ν₃} = (id ⊗ Δ_{ν₂;ν₃}) ∘ Δ_{ν₁;ν₂+ν₃}`,
  up to the associator of `W_{ν₁} ⊗ W_{ν₂} ⊗ W_{ν₃}` and `castW`.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

/-! ### Restriction along `φ ⊗ id` and `id ⊗ φ` -/

section TensorRes

variable (k : Type*) [CommRing k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] (C : Type u) [Ring C] [Algebra k C] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)

/-- The `k`-module structure of `Res φ M` through `algebraMap k A`. -/
abbrev Res.moduleK (M : Type w) [AddCommGroup M] [Module B M] : Module k (Res φ M) :=
  Module.compHom _ (algebraMap k A)

attribute [local instance] Res.moduleK

omit [Algebra k B] in
theorem Res.isScalarTowerK (M : Type w) [AddCommGroup M] [Module B M] :
    IsScalarTower k A (Res φ M) :=
  IsScalarTower.of_compHom _ _ _

attribute [local instance] Res.isScalarTowerK

variable {φ}

include hφ in
theorem Res.val_smulK (c : k) (r : Res φ B) : (c • r).val = c • r.val := by
  change φ (algebraMap k A c) * r.val = c • r.val
  rw [Algebra.algebraMap_eq_smul_one, hφ, smul_mul_assoc]
  exact congrArg (c • ·) r.prop

variable (φ)

/-- `Res φ B → B`, `k`-linear. -/
def Res.valK : Res φ B →ₗ[k] B where
  toFun r := r.val
  map_add' _ _ := rfl
  map_smul' c r := Res.val_smulK k hφ c r

/-- `B → Res φ B`, `b ↦ φ(1) b`, `k`-linear. -/
def Res.projK : B →ₗ[k] Res φ B where
  toFun b := Res.mk (φ 1 * b) (by
    change φ 1 * (φ 1 * b) = φ 1 * b
    rw [← mul_assoc, ← map_mul, one_mul])
  map_add' b b' := Res.ext (mul_add _ _ _)
  map_smul' c b := Res.ext (by
    rw [Res.val_smulK k hφ]
    exact mul_smul_comm c (φ 1) b)

theorem Res.projK_valK (r : Res φ B) : Res.projK k φ hφ (Res.valK k φ hφ r) = r :=
  Res.ext r.prop

theorem Res.valK_projK (b : B) : Res.valK k φ hφ (Res.projK k φ hφ b) = φ 1 * b := rfl

/-- `Res φ B ⊠ C → B ⊗ C`. -/
def Res.tensorLeftVal : ExtTensor k (Res φ B) C →ₗ[k] B ⊗[k] C :=
  (TensorProduct.map (Res.valK k φ hφ) LinearMap.id).comp ExtTensor.equivTensor.toLinearMap

/-- `B ⊗ C → Res φ B ⊠ C`. -/
def Res.tensorLeftProj : B ⊗[k] C →ₗ[k] ExtTensor k (Res φ B) C :=
  ExtTensor.equivTensor.symm.toLinearMap.comp (TensorProduct.map (Res.projK k φ hφ) LinearMap.id)

theorem Res.tensorLeftProj_val (x : ExtTensor k (Res φ B) C) :
    Res.tensorLeftProj k C φ hφ (Res.tensorLeftVal k C φ hφ x) = x := by
  induction x using ExtTensor.induction_on with
  | zero => simp
  | tmul r c =>
    change ExtTensor.tmul (Res.projK k φ hφ (Res.valK k φ hφ r)) c = ExtTensor.tmul r c
    rw [Res.projK_valK]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem Res.tensorLeftVal_proj (y : B ⊗[k] C) :
    Res.tensorLeftVal k C φ hφ (Res.tensorLeftProj k C φ hφ y) = (φ 1 ⊗ₜ[k] (1 : C)) * y := by
  induction y using TensorProduct.inductionOn with
  | tmul b c =>
    change (φ 1 * b) ⊗ₜ[k] c = (φ 1 ⊗ₜ[k] (1 : C)) * (b ⊗ₜ[k] c)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

/-- **Restriction along `φ ⊗ id`**: `Res φ B ⊠ C ≅ Res (φ ⊗ id) (B ⊗ C)` as
`A ⊗ C`-modules. -/
def Res.tensorLeftEquiv :
    ExtTensor k (Res φ B) C ≃ₗ[A ⊗[k] C] Res (tensorLeft k C φ hφ) (B ⊗[k] C) where
  toFun x := Res.mk (Res.tensorLeftVal k C φ hφ x) (by
    change tensorLeft k C φ hφ 1 * _ = _
    rw [tensorLeft_one, ← Res.tensorLeftVal_proj, Res.tensorLeftProj_val])
  invFun m := Res.tensorLeftProj k C φ hφ m.val
  map_add' x y := Res.ext (map_add _ x y)
  map_smul' t x := ExtTensor.smul_eq_induction (Z := Res (tensorLeft k C φ hφ) (B ⊗[k] C))
    (F := fun x => Res.mk (Res.tensorLeftVal k C φ hφ x) (by
      change tensorLeft k C φ hφ 1 * _ = _
      rw [tensorLeft_one, ← Res.tensorLeftVal_proj, Res.tensorLeftProj_val]))
    (fun x y => Res.ext (map_add _ x y)) (Res.ext (map_zero _))
    (fun a c r c' => Res.ext (by
      rw [ExtTensor.smul_tmul, Res.val_smul]
      change (φ a * r.val) ⊗ₜ[k] (c * c') = tensorLeft k C φ hφ (a ⊗ₜ[k] c) * (r.val ⊗ₜ[k] c')
      rw [tensorLeft_tmul, Algebra.TensorProduct.tmul_mul_tmul])) t x
  left_inv x := Res.tensorLeftProj_val k C φ hφ x
  right_inv m := Res.ext (by
    change Res.tensorLeftVal k C φ hφ (Res.tensorLeftProj k C φ hφ m.val) = m.val
    rw [Res.tensorLeftVal_proj]
    exact m.prop)

/-- `C ⊠ Res φ B → C ⊗ B`. -/
def Res.tensorRightVal : ExtTensor k C (Res φ B) →ₗ[k] C ⊗[k] B :=
  (TensorProduct.map LinearMap.id (Res.valK k φ hφ)).comp ExtTensor.equivTensor.toLinearMap

/-- `C ⊗ B → C ⊠ Res φ B`. -/
def Res.tensorRightProj : C ⊗[k] B →ₗ[k] ExtTensor k C (Res φ B) :=
  ExtTensor.equivTensor.symm.toLinearMap.comp (TensorProduct.map LinearMap.id (Res.projK k φ hφ))

theorem Res.tensorRightProj_val (x : ExtTensor k C (Res φ B)) :
    Res.tensorRightProj k C φ hφ (Res.tensorRightVal k C φ hφ x) = x := by
  induction x using ExtTensor.induction_on with
  | zero => simp
  | tmul c r =>
    change ExtTensor.tmul c (Res.projK k φ hφ (Res.valK k φ hφ r)) = ExtTensor.tmul c r
    rw [Res.projK_valK]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem Res.tensorRightVal_proj (y : C ⊗[k] B) :
    Res.tensorRightVal k C φ hφ (Res.tensorRightProj k C φ hφ y) = ((1 : C) ⊗ₜ[k] φ 1) * y := by
  induction y using TensorProduct.inductionOn with
  | tmul c b =>
    change c ⊗ₜ[k] (φ 1 * b) = ((1 : C) ⊗ₜ[k] φ 1) * (c ⊗ₜ[k] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

/-- **Restriction along `id ⊗ φ`**: `C ⊠ Res φ B ≅ Res (id ⊗ φ) (C ⊗ B)` as
`C ⊗ A`-modules. -/
def Res.tensorRightEquiv :
    ExtTensor k C (Res φ B) ≃ₗ[C ⊗[k] A] Res (tensorRight k C φ hφ) (C ⊗[k] B) where
  toFun x := Res.mk (Res.tensorRightVal k C φ hφ x) (by
    change tensorRight k C φ hφ 1 * _ = _
    rw [tensorRight_one, ← Res.tensorRightVal_proj, Res.tensorRightProj_val])
  invFun m := Res.tensorRightProj k C φ hφ m.val
  map_add' x y := Res.ext (map_add _ x y)
  map_smul' t x := ExtTensor.smul_eq_induction (Z := Res (tensorRight k C φ hφ) (C ⊗[k] B))
    (F := fun x => Res.mk (Res.tensorRightVal k C φ hφ x) (by
      change tensorRight k C φ hφ 1 * _ = _
      rw [tensorRight_one, ← Res.tensorRightVal_proj, Res.tensorRightProj_val]))
    (fun x y => Res.ext (map_add _ x y)) (Res.ext (map_zero _))
    (fun c a c' r => Res.ext (by
      rw [ExtTensor.smul_tmul, Res.val_smul]
      change (c * c') ⊗ₜ[k] (φ a * r.val) = tensorRight k C φ hφ (c ⊗ₜ[k] a) * (c' ⊗ₜ[k] r.val)
      rw [tensorRight_tmul, Algebra.TensorProduct.tmul_mul_tmul])) t x
  left_inv x := Res.tensorRightProj_val k C φ hφ x
  right_inv m := Res.ext (by
    change Res.tensorRightVal k C φ hφ (Res.tensorRightProj k C φ hφ m.val) = m.val
    rw [Res.tensorRightVal_proj]
    exact m.prop)

variable (M : Type w) [AddCommGroup M] [Module (B ⊗[k] C) M] [Module.Finite (B ⊗[k] C) M]
  [Module.Projective (B ⊗[k] C) M]

/-- **Restriction along `φ ⊗ id` preserves projectivity**: if `Res φ B` is finitely generated
projective over `A`, then `Res (φ ⊗ id) M` is projective over `A ⊗ C` for every finitely
generated projective `B ⊗ C`-module `M`. -/
theorem Res.tensorLeft_projective [Module.Finite A (Res φ B)] [Module.Projective A (Res φ B)] :
    Module.Projective (A ⊗[k] C) (Res (tensorLeft k C φ hφ) M) := by
  have : Module.Projective (A ⊗[k] C) (ExtTensor k (Res φ B) C) := ExtTensor.projective
  have : Module.Projective (A ⊗[k] C) (Res (tensorLeft k C φ hφ) (B ⊗[k] C)) :=
    Module.Projective.of_equiv (Res.tensorLeftEquiv k C φ hφ)
  exact Res.projective_of_regular _ M

/-- **Restriction along `φ ⊗ id` preserves finite generation**. -/
theorem Res.tensorLeft_finite [Module.Finite A (Res φ B)] :
    Module.Finite (A ⊗[k] C) (Res (tensorLeft k C φ hφ) M) := by
  have : Module.Finite (A ⊗[k] C) (ExtTensor k (Res φ B) C) := ExtTensor.finite
  have : Module.Finite (A ⊗[k] C) (Res (tensorLeft k C φ hφ) (B ⊗[k] C)) :=
    Module.Finite.equiv (Res.tensorLeftEquiv k C φ hφ)
  exact Res.finite_of_regular _ M

variable (M' : Type w) [AddCommGroup M'] [Module (C ⊗[k] B) M'] [Module.Finite (C ⊗[k] B) M']
  [Module.Projective (C ⊗[k] B) M']

/-- **Restriction along `id ⊗ φ` preserves projectivity**. -/
theorem Res.tensorRight_projective [Module.Finite A (Res φ B)] [Module.Projective A (Res φ B)] :
    Module.Projective (C ⊗[k] A) (Res (tensorRight k C φ hφ) M') := by
  have : Module.Projective (C ⊗[k] A) (ExtTensor k C (Res φ B)) := ExtTensor.projective
  have : Module.Projective (C ⊗[k] A) (Res (tensorRight k C φ hφ) (C ⊗[k] B)) :=
    Module.Projective.of_equiv (Res.tensorRightEquiv k C φ hφ)
  exact Res.projective_of_regular _ M'

/-- **Restriction along `id ⊗ φ` preserves finite generation**. -/
theorem Res.tensorRight_finite [Module.Finite A (Res φ B)] :
    Module.Finite (C ⊗[k] A) (Res (tensorRight k C φ hφ) M') := by
  have : Module.Finite (C ⊗[k] A) (ExtTensor k C (Res φ B)) := ExtTensor.finite
  have : Module.Finite (C ⊗[k] A) (Res (tensorRight k C φ hφ) (C ⊗[k] B)) :=
    Module.Finite.equiv (Res.tensorRightEquiv k C φ hφ)
  exact Res.finite_of_regular _ M'

end TensorRes

end InductionAlong

namespace WeightedKLR

namespace Juxtapose

open InductionAlong GalleryAlgebra

universe w

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

/-! ### The iterated coproducts on `K₀` -/

section Coassoc

variable (ν₁ ν₂ ν₃ : I →₀ ℕ) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

/-- `ι_{ν₁;ν₂} ⊗ id : (W_{ν₁} ⊗ W_{ν₂}) ⊗ W_{ν₃} → W_{ν₁+ν₂} ⊗ W_{ν₃}`. -/
abbrev resLeftHom :
    (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃ →ₙ+*
      WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃ :=
  tensorLeft (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) k
    (WeightedKLRAlgebra k Γ ν₃) (inductionRingHom k Γ ν₁ ν₂) (inductionRingHom_smul k Γ ν₁ ν₂)

/-- `id ⊗ ι_{ν₂;ν₃} : W_{ν₁} ⊗ (W_{ν₂} ⊗ W_{ν₃}) → W_{ν₁} ⊗ W_{ν₂+ν₃}`. -/
abbrev resRightHom :
    WeightedKLRAlgebra k Γ ν₁ ⊗[k] (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃) →ₙ+*
      WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃) :=
  tensorRight (A := WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃) k
    (WeightedKLRAlgebra k Γ ν₁) (inductionRingHom k Γ ν₂ ν₃) (inductionRingHom_smul k Γ ν₂ ν₃)

/-- The associator `(W_{ν₁} ⊗ W_{ν₂}) ⊗ W_{ν₃} ≅ W_{ν₁} ⊗ (W_{ν₂} ⊗ W_{ν₃})`. -/
abbrev assocW :
    (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃ ≃ₐ[k]
      WeightedKLRAlgebra k Γ ν₁ ⊗[k] (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃) :=
  Algebra.TensorProduct.assoc k k k _ _ _

/-- `(Res_{ν₁;ν₂} ⊗ id) L` as a finitely generated projective `(W_{ν₁} ⊗ W_{ν₂}) ⊗ W_{ν₃}`-module,
for `L` finitely generated projective over `W_{ν₁+ν₂} ⊗ W_{ν₃}`, under the standing
hypothesis. -/
noncomputable def resLeftProj
    (L : FGProj k (WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)) :
    FGProj k ((WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃) :=
  letI := Res.moduleK k (A := (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃)
    (B := WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)
    (resLeftHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier
  haveI := Res.isScalarTowerK k (A := (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃)
    (B := WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)
    (resLeftHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier
  haveI : Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (Res (inductionRingHom k Γ ν₁ ν₂) (WeightedKLRAlgebra k Γ (ν₁ + ν₂))) :=
    res_projective Γ ν₁ ν₂ hD hZ hS _
  haveI : Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (Res (inductionRingHom k Γ ν₁ ν₂) (WeightedKLRAlgebra k Γ (ν₁ + ν₂))) :=
    res_finite Γ ν₁ ν₂ hD hZ hS _
  haveI := Res.tensorLeft_projective k (WeightedKLRAlgebra k Γ ν₃) (inductionRingHom k Γ ν₁ ν₂)
    (inductionRingHom_smul k Γ ν₁ ν₂) L.carrier
  haveI := Res.tensorLeft_finite k (WeightedKLRAlgebra k Γ ν₃) (inductionRingHom k Γ ν₁ ν₂)
    (inductionRingHom_smul k Γ ν₁ ν₂) L.carrier
  FGProj.of (Res (A := (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃)
    (B := WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)
    (resLeftHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier)

/-- `(id ⊗ Res_{ν₂;ν₃}) L` as a finitely generated projective `W_{ν₁} ⊗ (W_{ν₂} ⊗ W_{ν₃})`-module,
for `L` finitely generated projective over `W_{ν₁} ⊗ W_{ν₂+ν₃}`, under the standing
hypothesis. -/
noncomputable def resRightProj
    (L : FGProj k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))) :
    FGProj k (WeightedKLRAlgebra k Γ ν₁ ⊗[k]
      (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃)) :=
  letI := Res.moduleK k (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k]
      (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃))
    (B := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))
    (resRightHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier
  haveI := Res.isScalarTowerK k (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k]
      (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃))
    (B := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))
    (resRightHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier
  haveI : Module.Projective (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃)
      (Res (inductionRingHom k Γ ν₂ ν₃) (WeightedKLRAlgebra k Γ (ν₂ + ν₃))) :=
    res_projective Γ ν₂ ν₃ hD hZ hS _
  haveI : Module.Finite (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃)
      (Res (inductionRingHom k Γ ν₂ ν₃) (WeightedKLRAlgebra k Γ (ν₂ + ν₃))) :=
    res_finite Γ ν₂ ν₃ hD hZ hS _
  haveI := Res.tensorRight_projective k (WeightedKLRAlgebra k Γ ν₁) (inductionRingHom k Γ ν₂ ν₃)
    (inductionRingHom_smul k Γ ν₂ ν₃) L.carrier
  haveI := Res.tensorRight_finite k (WeightedKLRAlgebra k Γ ν₁) (inductionRingHom k Γ ν₂ ν₃)
    (inductionRingHom_smul k Γ ν₂ ν₃) L.carrier
  FGProj.of (Res (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k]
      (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃))
    (B := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))
    (resRightHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier)

/-- `Res L ≅ Res L'` for `L ≅ L'`. -/
noncomputable def resLeftProjCongr {L L' : FGProj k (WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)}
    (e : L.Iso L') :
    (resLeftProj ν₁ ν₂ ν₃ hD hZ hS L).Iso (resLeftProj ν₁ ν₂ ν₃ hD hZ hS L') :=
  (Res.congr (A := (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃)
    (B := WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)
    (resLeftHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) e :)

/-- `Res (L × L') ≅ Res L × Res L'`. -/
noncomputable def resLeftProjProd (L L' : FGProj k (WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)) :
    (resLeftProj ν₁ ν₂ ν₃ hD hZ hS (L.prod L')).Iso
      ((resLeftProj ν₁ ν₂ ν₃ hD hZ hS L).prod (resLeftProj ν₁ ν₂ ν₃ hD hZ hS L')) :=
  (Res.prodEquiv (A := (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
      WeightedKLRAlgebra k Γ ν₃)
    (B := WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)
    (resLeftHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier L'.carrier :)

/-- `Δ_{ν₁;ν₂} ⊗ id : K₀(W_{ν₁+ν₂} ⊗ W_{ν₃}) → K₀((W_{ν₁} ⊗ W_{ν₂}) ⊗ W_{ν₃})`, restriction along
`ι_{ν₁;ν₂} ⊗ id`, under the standing hypothesis. -/
noncomputable def resLeftK0 :
    ProjK0 k (WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃) →+
      ProjK0 k ((WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        WeightedKLRAlgebra k Γ ν₃) :=
  ProjK0.lift (fun L => ProjK0.of (resLeftProj ν₁ ν₂ ν₃ hD hZ hS L))
    (fun _ _ e => ProjK0.of_eq_of_iso (resLeftProjCongr ν₁ ν₂ ν₃ hD hZ hS e))
    (fun L L' => by
      rw [ProjK0.of_eq_of_iso (resLeftProjProd ν₁ ν₂ ν₃ hD hZ hS L L'), ProjK0.of_prod])

@[simp] theorem resLeftK0_of
    (L : FGProj k (WeightedKLRAlgebra k Γ (ν₁ + ν₂) ⊗[k] WeightedKLRAlgebra k Γ ν₃)) :
    resLeftK0 ν₁ ν₂ ν₃ hD hZ hS (ProjK0.of L) = ProjK0.of (resLeftProj ν₁ ν₂ ν₃ hD hZ hS L) :=
  ProjK0.lift_of _ _ _ L

/-- `Res L ≅ Res L'` for `L ≅ L'`. -/
noncomputable def resRightProjCongr {L L' : FGProj k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))}
    (e : L.Iso L') :
    (resRightProj ν₁ ν₂ ν₃ hD hZ hS L).Iso (resRightProj ν₁ ν₂ ν₃ hD hZ hS L') :=
  (Res.congr (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k]
      (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃))
    (B := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))
    (resRightHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) e :)

/-- `Res (L × L') ≅ Res L × Res L'`. -/
noncomputable def resRightProjProd (L L' : FGProj k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))) :
    (resRightProj ν₁ ν₂ ν₃ hD hZ hS (L.prod L')).Iso
      ((resRightProj ν₁ ν₂ ν₃ hD hZ hS L).prod (resRightProj ν₁ ν₂ ν₃ hD hZ hS L')) :=
  (Res.prodEquiv (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k]
      (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃))
    (B := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))
    (resRightHom (k := k) (Γ := Γ) ν₁ ν₂ ν₃) L.carrier L'.carrier :)

/-- `id ⊗ Δ_{ν₂;ν₃} : K₀(W_{ν₁} ⊗ W_{ν₂+ν₃}) → K₀(W_{ν₁} ⊗ (W_{ν₂} ⊗ W_{ν₃}))`, restriction along
`id ⊗ ι_{ν₂;ν₃}`, under the standing hypothesis. -/
noncomputable def resRightK0 :
    ProjK0 k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃)) →+
      ProjK0 k (WeightedKLRAlgebra k Γ ν₁ ⊗[k]
        (WeightedKLRAlgebra k Γ ν₂ ⊗[k] WeightedKLRAlgebra k Γ ν₃)) :=
  ProjK0.lift (fun L => ProjK0.of (resRightProj ν₁ ν₂ ν₃ hD hZ hS L))
    (fun _ _ e => ProjK0.of_eq_of_iso (resRightProjCongr ν₁ ν₂ ν₃ hD hZ hS e))
    (fun L L' => by
      rw [ProjK0.of_eq_of_iso (resRightProjProd ν₁ ν₂ ν₃ hD hZ hS L L'), ProjK0.of_prod])

@[simp] theorem resRightK0_of
    (L : FGProj k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ (ν₂ + ν₃))) :
    resRightK0 ν₁ ν₂ ν₃ hD hZ hS (ProjK0.of L) = ProjK0.of (resRightProj ν₁ ν₂ ν₃ hD hZ hS L) :=
  ProjK0.lift_of _ _ _ L

/-- **Coassociativity of the coproduct on `K₀`** (Webster, arXiv:1209.2463v4, §2.4,
Proposition 2.18 and Theorem 2.19): for
`x ∈ K₀(W_{ν₁+ν₂+ν₃})`,
`α ((Δ_{ν₁;ν₂} ⊗ id) (Δ_{ν₁+ν₂;ν₃} x)) = (id ⊗ Δ_{ν₂;ν₃}) (Δ_{ν₁;ν₂+ν₃} x)`, where `α` is the
associator of `W_{ν₁} ⊗ W_{ν₂} ⊗ W_{ν₃}` and `x` is moved to `K₀(W_{ν₁+(ν₂+ν₃)})` by `castW`.
Over every commutative ring `k`, under Webster's standing hypothesis (`Γ.Standing`), the
condition (†) (`Γ.Dagger`) and `Γ.NoZeroLoops`, the hypotheses of `res_projective`. -/
theorem resK0_coassoc (x : ProjK0 k (WeightedKLRAlgebra k Γ (ν₁ + ν₂ + ν₃))) :
    ProjK0.map (assocW (k := k) (Γ := Γ) ν₁ ν₂ ν₃)
        (resLeftK0 ν₁ ν₂ ν₃ hD hZ hS (resK0 (ν₁ + ν₂) ν₃ hD hZ hS x)) =
      resRightK0 ν₁ ν₂ ν₃ hD hZ hS
        (resK0 ν₁ (ν₂ + ν₃) hD hZ hS (ProjK0.map (castW k Γ (add_assoc ν₁ ν₂ ν₃)) x)) := by
  induction x using ProjK0.induction_on with
  | of L =>
    rw [resK0_of, resLeftK0_of, ProjK0.map_of (castW k Γ (add_assoc ν₁ ν₂ ν₃)), resK0_of,
      resRightK0_of]
    exact ProjK0.map_of_semilinear _ _ _
      (resCoassocEquiv k Γ ν₁ ν₂ ν₃ L.carrier
        (FGProj.restrict (castW k Γ (add_assoc ν₁ ν₂ ν₃)) L).carrier (AddEquiv.refl _)
        (fun d l => by
          change d • l = (castW k Γ (add_assoc ν₁ ν₂ ν₃)).symm
            (castW k Γ (add_assoc ν₁ ν₂ ν₃) d) • l
          rw [AlgEquiv.symm_apply_apply]))
      (resCoassocEquiv_smul ν₁ ν₂ ν₃ _ _ _ _)
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]

end Coassoc

end Juxtapose

end WeightedKLR

end

end Categorification
