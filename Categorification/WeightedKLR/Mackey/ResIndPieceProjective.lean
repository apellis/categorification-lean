/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndChain
import Categorification.WeightedKLR.Induction.Coassociativity

/-!
# The pieces of the Mackey filtration are finitely generated projective

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). For a four-block layout
`ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`, the piece
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})` of the Mackey filtration
(`ResIndPiece`) tensored with a finitely generated projective `W_{ν'} ⊗ W_{ν''}`-module `N` is a
finitely generated projective `W_{ν₁} ⊗ W_{ν₂}`-module, under Webster's standing hypothesis.

The input is that `e (W_{a+b} ⊗ W_{c+d})` is `Res_{a,b} W_{a+b} ⊠ Res_{c,d} W_{c+d}` as a left
module over `W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)` (`Juxtapose.middleBotEquiv`), which is finitely
generated projective because restriction preserves finitely generated projective modules
(`Juxtapose.res_projective`, `Juxtapose.res_finite`); and that `(W_{a+c} ⊗ W_{b+d}) e'` is a
direct summand of the regular module.

## Main results

* `Juxtapose.middleBotEquiv`: `Res_{a,b} W_{a+b} ⊠ Res_{c,d} W_{c+d} ≅ e (W_{a+b} ⊗ W_{c+d})`.
* `Juxtapose.middleTensor_projective`, `Juxtapose.middleTensor_finite`: the middle balanced
  tensor product is finitely generated projective over `W_{a+c} ⊗ W_{b+d}`.
* `ResIndPiece.projective`, `ResIndPiece.finite`: the piece is finitely generated projective
  over `W_{ν₁} ⊗ W_{ν₂}`.
* `ResIndPiece.balancedTensor_projective`, `ResIndPiece.balancedTensor_finite`: so is
  `ResIndPiece L ⊗ N` for every finitely generated projective `W_{ν'} ⊗ W_{ν''}`-module `N`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra InductionAlong MulOpposite
open scoped TensorProduct

noncomputable section

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable {a b c d : I →₀ ℕ}

/-! ### `(W_{a+c} ⊗ W_{b+d}) e'` is a direct summand of the regular module -/

variable (k Γ a b c d) in
/-- The projection `x ↦ x e'` of `W_{a+c} ⊗ W_{b+d}` onto `(W_{a+c} ⊗ W_{b+d}) e'`. -/
def middleTopProj :
    WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d) →ₗ[
      WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)]
      MiddleTop k Γ a b c d where
  toFun x := ⟨x * middleTop k Γ a b c d 1, mul_middleTop_mem x 1⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _)

theorem middleTopProj_comp_subtype :
    (middleTopProj k Γ a b c d).comp (middleTopSub k Γ a b c d).subtype = LinearMap.id :=
  LinearMap.ext fun t => Subtype.ext t.2

instance middleTop_projective :
    Module.Projective (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleTop k Γ a b c d) :=
  Module.Projective.of_split (middleTopSub k Γ a b c d).subtype (middleTopProj k Γ a b c d)
    middleTopProj_comp_subtype

instance middleTop_finite :
    Module.Finite (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleTop k Γ a b c d) :=
  Module.Finite.of_surjective (middleTopProj k Γ a b c d) fun t => ⟨t.1, Subtype.ext t.2⟩

instance : IsScalarTower k (MiddleAlg k Γ a b c d) (MiddleBot k Γ a b c d) where
  smul_assoc r s y := Subtype.ext (by
    show middleBot k Γ a b c d (r • s) * (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k]
        WeightedKLRAlgebra k Γ (c + d)) = r • (middleBot k Γ a b c d s * y)
    rw [map_smul, smul_mul_assoc])

/-! ### `e (W_{a+b} ⊗ W_{c+d})` is `Res W_{a+b} ⊠ Res W_{c+d}` -/

section MiddleBot

attribute [local instance] Res.moduleK Res.isScalarTowerK

variable (k Γ a b c d) in
/-- `Res_{a,b} W_{a+b} ⊠ Res_{c,d} W_{c+d}`, a left `(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`-module. -/
abbrev MiddleRes : Type _ :=
  ExtTensor k (Res (inductionRingHom k Γ a b) (WeightedKLRAlgebra k Γ (a + b)))
    (Res (inductionRingHom k Γ c d) (WeightedKLRAlgebra k Γ (c + d)))

variable (k Γ a b c d) in
/-- `Res W_{a+b} ⊠ Res W_{c+d} → W_{a+b} ⊗ W_{c+d}`. -/
def middleResVal :
    MiddleRes k Γ a b c d →ₗ[k] WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d) :=
  (TensorProduct.map (Res.valK k _ (inductionRingHom_smul k Γ a b))
    (Res.valK k _ (inductionRingHom_smul k Γ c d))).comp ExtTensor.equivTensor.toLinearMap

variable (k Γ a b c d) in
/-- `W_{a+b} ⊗ W_{c+d} → Res W_{a+b} ⊠ Res W_{c+d}`, `y ↦ e y`. -/
def middleResProj :
    WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d) →ₗ[k] MiddleRes k Γ a b c d :=
  ExtTensor.equivTensor.symm.toLinearMap.comp
    (TensorProduct.map (Res.projK k _ (inductionRingHom_smul k Γ a b))
      (Res.projK k _ (inductionRingHom_smul k Γ c d)))

theorem middleResProj_val (x : MiddleRes k Γ a b c d) :
    middleResProj k Γ a b c d (middleResVal k Γ a b c d x) = x := by
  induction x using ExtTensor.induction_on with
  | zero => simp
  | tmul p q =>
    change ExtTensor.tmul (Res.projK k _ (inductionRingHom_smul k Γ a b)
        (Res.valK k _ (inductionRingHom_smul k Γ a b) p))
      (Res.projK k _ (inductionRingHom_smul k Γ c d)
        (Res.valK k _ (inductionRingHom_smul k Γ c d) q)) = ExtTensor.tmul p q
    rw [Res.projK_valK, Res.projK_valK]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem middleResVal_proj
    (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleResVal k Γ a b c d (middleResProj k Γ a b c d y) = middleBot k Γ a b c d 1 * y := by
  rw [middleBot_one]
  induction y using TensorProduct.inductionOn with
  | tmul x z =>
    change (inductionRingHom k Γ a b 1 * x) ⊗ₜ[k] (inductionRingHom k Γ c d 1 * z) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem middleResVal_mem (x : MiddleRes k Γ a b c d) :
    middleResVal k Γ a b c d x ∈ middleBotSub k Γ a b c d := by
  rw [mem_middleBotSub, ← middleResVal_proj, middleResProj_val]

variable (k Γ a b c d) in
/-- **`e (W_{a+b} ⊗ W_{c+d})` is `Res_{a,b} W_{a+b} ⊠ Res_{c,d} W_{c+d}`** as a left
`W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`-module, `e = ι_{a,b}(1) ⊗ ι_{c,d}(1)`. -/
def middleBotEquiv : MiddleRes k Γ a b c d ≃ₗ[MiddleAlg k Γ a b c d] MiddleBot k Γ a b c d where
  toFun x := ⟨middleResVal k Γ a b c d x, middleResVal_mem x⟩
  invFun y := middleResProj k Γ a b c d y.1
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' t x := ExtTensor.smul_eq_induction (Z := MiddleBot k Γ a b c d)
    (F := fun x => (⟨middleResVal k Γ a b c d x, middleResVal_mem x⟩ : MiddleBot k Γ a b c d))
    (fun x y => Subtype.ext (map_add _ x y)) (Subtype.ext (map_zero _))
    (fun xab xcd p q => Subtype.ext (by
      rw [ExtTensor.smul_tmul, coe_smul_middleBot]
      change (inductionRingHom k Γ a b xab * p.val) ⊗ₜ[k] (inductionRingHom k Γ c d xcd * q.val) =
        (inductionRingHom k Γ a b xab ⊗ₜ[k] inductionRingHom k Γ c d xcd) * (p.val ⊗ₜ[k] q.val)
      rw [Algebra.TensorProduct.tmul_mul_tmul])) t x
  left_inv x := middleResProj_val x
  right_inv y := Subtype.ext (by
    change middleResVal k Γ a b c d (middleResProj k Γ a b c d y.1) = y.1
    rw [middleResVal_proj]
    exact y.2)

/-- Under the standing hypothesis, `e (W_{a+b} ⊗ W_{c+d})` is a projective left
`(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`-module. -/
theorem middleBot_projective (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Projective (MiddleAlg k Γ a b c d) (MiddleBot k Γ a b c d) := by
  have : Module.Projective (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ b)
      (Res (inductionRingHom k Γ a b) (WeightedKLRAlgebra k Γ (a + b))) :=
    res_projective Γ a b hD hZ hS _
  have : Module.Projective (WeightedKLRAlgebra k Γ c ⊗[k] WeightedKLRAlgebra k Γ d)
      (Res (inductionRingHom k Γ c d) (WeightedKLRAlgebra k Γ (c + d))) :=
    res_projective Γ c d hD hZ hS _
  have : Module.Projective (MiddleAlg k Γ a b c d) (MiddleRes k Γ a b c d) :=
    ExtTensor.projective
  exact Module.Projective.of_equiv (middleBotEquiv k Γ a b c d)

/-- Under the standing hypothesis, `e (W_{a+b} ⊗ W_{c+d})` is a finitely generated left
`(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`-module. -/
theorem middleBot_finite (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Finite (MiddleAlg k Γ a b c d) (MiddleBot k Γ a b c d) := by
  have : Module.Finite (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ b)
      (Res (inductionRingHom k Γ a b) (WeightedKLRAlgebra k Γ (a + b))) :=
    res_finite Γ a b hD hZ hS _
  have : Module.Finite (WeightedKLRAlgebra k Γ c ⊗[k] WeightedKLRAlgebra k Γ d)
      (Res (inductionRingHom k Γ c d) (WeightedKLRAlgebra k Γ (c + d))) :=
    res_finite Γ c d hD hZ hS _
  have : Module.Finite (MiddleAlg k Γ a b c d) (MiddleRes k Γ a b c d) := ExtTensor.finite
  exact Module.Finite.equiv (middleBotEquiv k Γ a b c d)

end MiddleBot

/-- Under the standing hypothesis, `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})` is a
projective left `W_{a+c} ⊗ W_{b+d}`-module. -/
theorem middleTensor_projective (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Projective (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleTensor k Γ a b c d) :=
  have := middleBot_projective (a := a) (b := b) (c := c) (d := d) hD hZ hS
  BalancedTensor.projective

/-- Under the standing hypothesis, `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})` is a
finitely generated left `W_{a+c} ⊗ W_{b+d}`-module. -/
theorem middleTensor_finite (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Finite (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleTensor k Γ a b c d) :=
  have := middleBot_finite (a := a) (b := b) (c := c) (d := d) hD hZ hS
  BalancedTensor.finite

/-- The corner map `x ↦ z x 1` is the action of `z`. -/
theorem middleCornerMap_one_apply
    (z : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (x : MiddleTensor k Γ a b c d) :
    middleCornerMap z (1 : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))
      x = z • x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul t y =>
    rw [middleCornerMap_tmul, BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext (mul_one _)
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

end Juxtapose

namespace ResIndPiece

open Juxtapose

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂)

/-- `MiddleTensor ≅ ResIndPiece`, semilinear along `W_{a+c} ⊗ W_{b+d} ≅ W_{ν₁} ⊗ W_{ν₂}`. -/
def leftSemilinearEquiv :
    haveI := RingHomInvPair.of_ringEquiv (L.leftEquiv k Γ).toRingEquiv
    haveI := RingHomInvPair.of_ringEquiv_symm (L.leftEquiv k Γ).toRingEquiv
    MiddleTensor k Γ L.a L.b L.c L.d ≃ₛₗ[((L.leftEquiv k Γ).toRingEquiv :
      WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d) →+*
        WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)] ResIndPiece k Γ L :=
  haveI := RingHomInvPair.of_ringEquiv (L.leftEquiv k Γ).toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv_symm (L.leftEquiv k Γ).toRingEquiv
  { AddEquiv.refl (MiddleTensor k Γ L.a L.b L.c L.d) with
    map_smul' := fun z x => by
      show z • x = middleCornerMap ((L.leftEquiv k Γ).symm (L.leftEquiv k Γ z)) 1 x
      rw [AlgEquiv.symm_apply_apply, middleCornerMap_one_apply] }

/-- **The piece is projective**: under the standing hypothesis, `ResIndPiece L` is a projective
left `W_{ν₁} ⊗ W_{ν₂}`-module. -/
theorem projective (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (ResIndPiece k Γ L) :=
  have := middleTensor_projective (a := L.a) (b := L.b) (c := L.c) (d := L.d) hD hZ hS
  haveI := RingHomInvPair.of_ringEquiv (L.leftEquiv k Γ).toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv_symm (L.leftEquiv k Γ).toRingEquiv
  Module.Projective.of_equiv (leftSemilinearEquiv L)

/-- **The piece is finitely generated**: under the standing hypothesis, `ResIndPiece L` is a
finitely generated left `W_{ν₁} ⊗ W_{ν₂}`-module. -/
theorem finite (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (ResIndPiece k Γ L) :=
  have := middleTensor_finite (a := L.a) (b := L.b) (c := L.c) (d := L.d) hD hZ hS
  haveI := RingHomInvPair.of_ringEquiv (L.leftEquiv k Γ).toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv_symm (L.leftEquiv k Γ).toRingEquiv
  Module.Finite.of_surjective (leftSemilinearEquiv L).toLinearMap
    (leftSemilinearEquiv L).surjective

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N]

/-- **`ResIndPiece L ⊗ N` is projective** for every projective left `W_{ν'} ⊗ W_{ν''}`-module
`N`, under the standing hypothesis (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19). -/
theorem balancedTensor_projective (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    [Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N] :
    Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ L) N) :=
  have := projective L hD hZ hS
  BalancedTensor.projective

/-- **`ResIndPiece L ⊗ N` is finitely generated** for every finitely generated left
`W_{ν'} ⊗ W_{ν''}`-module `N`, under the standing hypothesis. -/
theorem balancedTensor_finite (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    [Module.Finite (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N] :
    Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ L) N) :=
  have := finite L hD hZ hS
  BalancedTensor.finite

end ResIndPiece

end

end Categorification.WeightedKLR
