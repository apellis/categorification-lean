/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.Graded.K0Map
import Categorification.KLR.ExtTensorK0
import Categorification.WeightedKLR.Mackey.ResIndK0
import Categorification.WeightedKLR.GradedK0.ResIndChainGrading
import Categorification.WeightedKLR.GradedK0.Restriction

/-!
# Graded `Res ∘ Ind` as a balanced tensor product with `Res Ind`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19. For `ν₁ + ν₂ = ν' + ν''` and finitely generated graded projective modules `P` over
`W_{ν'}` and `P'` over `W_{ν''}`, restricting the graded induced module `Ind (P ⊠ P')` along
`ι_{ν₁;ν₂}` (with `W_{ν₁+ν₂}` acting through `castW`) is the balanced tensor product of the graded
bimodule `Res_{ν₁;ν₂} Ind_{ν';ν''}` (graded by the gallery algebra) with `P ⊠ P'`, as graded
`W_{ν₁} ⊗ W_{ν₂}`-modules. This is the graded form of `GalleryAlgebra.resIndTensorEquiv`.

## Main definitions and results

* `GalleryAlgebra.ResIndBimodule.toIndBimod`: an element of `Res Ind` as an element of the
  graded bimodule `W_{ν'+ν''} e_{ν';ν''}`.
* `GalleryAlgebra.resIndTensorGradedIso`: the graded isomorphism
  `ResIndBimodule ⊗ (P ⊠ P') ≅ Res_{ν₁;ν₂} Ind (P ⊠ P')`.
* `GalleryAlgebra.resK0_map_indK0_eq`: the corresponding identity in graded `K₀`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose InductionAlong MulOpposite Categorification.Graded
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

namespace GalleryAlgebra

section CommRing

variable {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

variable {P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
    (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (ν' + ν''), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand (ν' + ν'')), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hν₁ : ν₁ + ν₂ = ν' + ν'')

namespace ResIndBimodule

/-- An element of `Res Ind` as an element of the graded bimodule `W_{ν'+ν''} e_{ν';ν''}`. -/
def toIndBimod (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) : GradedIndBimod k Γ ν' ν'' :=
  ⟨toW hP hD hZ hΓ hW hL hν₁ z, Graded.mem_leftIdeal.2 (Subtype.ext z.val_mul_one)⟩

@[simp] theorem toIndBimod_val (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    (toIndBimod hP hD hZ hΓ hW hL hν₁ z : WeightedKLRAlgebra k Γ (ν' + ν'')).1 = z.val := rfl

/-- The element `ι_{ν₁;ν₂}(1) m` of `Res Ind`, for `m ∈ W_{ν'+ν''} e_{ν';ν''}`. -/
def ofIndBimod (m : GradedIndBimod k Γ ν' ν'') : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁ :=
  ofCorner hP hD hZ hΓ hW hL hν₁ ⟨(m : WeightedKLRAlgebra k Γ (ν' + ν'')), m.2⟩

@[simp] theorem ofIndBimod_val (m : GradedIndBimod k Γ ν' ν'') :
    (ofIndBimod hP hD hZ hΓ hW hL hν₁ m).val =
      inductionVal k hν₁ 1 * (m : WeightedKLRAlgebra k Γ (ν' + ν'')).1 := rfl

theorem toIndBimod_add (z z' : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    toIndBimod hP hD hZ hΓ hW hL hν₁ (z + z') =
      toIndBimod hP hD hZ hΓ hW hL hν₁ z + toIndBimod hP hD hZ hΓ hW hL hν₁ z' :=
  Subtype.ext (Subtype.ext rfl)

theorem toIndBimod_smul (c : k) (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    toIndBimod hP hD hZ hΓ hW hL hν₁ (c • z) = c • toIndBimod hP hD hZ hΓ hW hL hν₁ z :=
  Subtype.ext (Subtype.ext rfl)

theorem toIndBimod_op_smul (a : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    toIndBimod hP hD hZ hΓ hW hL hν₁ (op a • z) = op a • toIndBimod hP hD hZ hΓ hW hL hν₁ z :=
  Subtype.ext (Subtype.ext (by
    change inductionVal k hν₁ 1 * z.val * (inductionMap k Γ ν' ν'' a).1 =
      z.val * (inductionMap k Γ ν' ν'' a).1
    rw [z.one_mul_val]))

theorem ofIndBimod_add (m m' : GradedIndBimod k Γ ν' ν'') :
    ofIndBimod hP hD hZ hΓ hW hL hν₁ (m + m') =
      ofIndBimod hP hD hZ hΓ hW hL hν₁ m + ofIndBimod hP hD hZ hΓ hW hL hν₁ m' :=
  val_injective hP hD hZ hΓ hW hL rfl hν₁ (mul_add _ _ _)

theorem ofIndBimod_smul (c : k) (m : GradedIndBimod k Γ ν' ν'') :
    ofIndBimod hP hD hZ hΓ hW hL hν₁ (c • m) = c • ofIndBimod hP hD hZ hΓ hW hL hν₁ m :=
  val_injective hP hD hZ hΓ hW hL rfl hν₁ (by
    change inductionVal k hν₁ 1 * (c • (m : WeightedKLRAlgebra k Γ (ν' + ν'')).1) = c • (inductionVal k hν₁ 1 * _)
    rw [mul_smul_comm])

theorem ofIndBimod_op_smul (a : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (m : GradedIndBimod k Γ ν' ν'') :
    ofIndBimod hP hD hZ hΓ hW hL hν₁ (op a • m) = op a • ofIndBimod hP hD hZ hΓ hW hL hν₁ m :=
  val_injective hP hD hZ hΓ hW hL rfl hν₁ (by
    change inductionVal k hν₁ 1 * ((m : WeightedKLRAlgebra k Γ (ν' + ν'')).1 * (inductionMap k Γ ν' ν'' a).1) =
      inductionVal k hν₁ 1 * (inductionVal k hν₁ 1 * _) * (inductionMap k Γ ν' ν'' a).1
    simp only [← mul_assoc, inductionVal_mul_inductionVal_one])

theorem ofIndBimod_toIndBimod (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    ofIndBimod hP hD hZ hΓ hW hL hν₁ (toIndBimod hP hD hZ hΓ hW hL hν₁ z) = z :=
  val_injective hP hD hZ hΓ hW hL rfl hν₁ z.one_mul_val

end ResIndBimodule

section Maps

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N]

/-- The map `ResIndBimodule ⊗ N → Ind N`, `z ⊗ x ↦ z ⊗ x`, into graded induction. -/
def resIndToGradedInd :
    BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) N →ₗ[k] GradedInd k Γ ν' ν'' N :=
  BalancedTensor.lift
    (LinearMap.mk₂ k
      (fun z x => BalancedTensor.tmul (ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ z) x)
      (fun z z' x => by
        rw [ResIndBimodule.toIndBimod_add]
        exact BalancedTensor.add_tmul _ _ x)
      (fun c z x => by
        rw [ResIndBimodule.toIndBimod_smul]
        exact BalancedTensor.smul_tmul c _ x)
      (fun z x x' => BalancedTensor.tmul_add _ x x')
      (fun c z x => BalancedTensor.tmul_smul c _ x))
    (fun z a x => by
      change BalancedTensor.tmul (ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ (op a • z)) x =
        BalancedTensor.tmul (ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ z) (a • x)
      rw [ResIndBimodule.toIndBimod_op_smul]
      exact BalancedTensor.op_smul_tmul _ a x)

theorem resIndToGradedInd_tmul (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) (x : N) :
    resIndToGradedInd hP hD hZ hΓ hW hL hν₁ N (BalancedTensor.tmul z x) =
      BalancedTensor.tmul (ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ z) x :=
  BalancedTensor.lift_tmul _ _ z x

/-- The map `Ind N → ResIndBimodule ⊗ N`, `m ⊗ x ↦ ι_{ν₁;ν₂}(1) m ⊗ x`. -/
def gradedIndToResInd :
    GradedInd k Γ ν' ν'' N →ₗ[k]
      BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
        (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) N :=
  BalancedTensor.lift
    (LinearMap.mk₂ k
      (fun m x => BalancedTensor.tmul (ResIndBimodule.ofIndBimod hP hD hZ hΓ hW hL hν₁ m) x)
      (fun m m' x => by
        rw [ResIndBimodule.ofIndBimod_add]
        exact BalancedTensor.add_tmul _ _ x)
      (fun c m x => by
        rw [ResIndBimodule.ofIndBimod_smul]
        exact BalancedTensor.smul_tmul c _ x)
      (fun m x x' => BalancedTensor.tmul_add _ x x')
      (fun c m x => BalancedTensor.tmul_smul c _ x))
    (fun m a x => by
      change BalancedTensor.tmul (ResIndBimodule.ofIndBimod hP hD hZ hΓ hW hL hν₁ (op a • m)) x =
        BalancedTensor.tmul (ResIndBimodule.ofIndBimod hP hD hZ hΓ hW hL hν₁ m) (a • x)
      rw [ResIndBimodule.ofIndBimod_op_smul]
      exact BalancedTensor.op_smul_tmul _ a x)

theorem gradedIndToResInd_tmul (m : GradedIndBimod k Γ ν' ν'') (x : N) :
    gradedIndToResInd hP hD hZ hΓ hW hL hν₁ N (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (ResIndBimodule.ofIndBimod hP hD hZ hΓ hW hL hν₁ m) x :=
  BalancedTensor.lift_tmul _ _ m x

theorem resIndToGradedInd_smul (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (t : BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) N) :
    resIndToGradedInd hP hD hZ hΓ hW hL hν₁ N (u • t) =
      (castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ u) •
        resIndToGradedInd hP hD hZ hΓ hW hL hν₁ N t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  | tmul z x =>
    have hz : ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ (u • z) =
        (castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ u) •
          ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ z :=
      Subtype.ext (Subtype.ext (by
        change inductionVal k hν₁ u * z.val * (inductionMap k Γ ν' ν'' 1).1 =
          ((castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ u)).1 * z.val
        rw [castW_symm_val, mul_assoc]
        exact congrArg (inductionVal k hν₁ u * ·) z.val_mul_one))
    rw [BalancedTensor.smul_tmul', resIndToGradedInd_tmul, resIndToGradedInd_tmul, hz,
      BalancedTensor.smul_tmul']

theorem gradedIndToResInd_resIndToGradedInd
    (t : BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) N) :
    gradedIndToResInd hP hD hZ hΓ hW hL hν₁ N (resIndToGradedInd hP hD hZ hΓ hW hL hν₁ N t) =
      t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul z x =>
    rw [resIndToGradedInd_tmul, gradedIndToResInd_tmul, ResIndBimodule.ofIndBimod_toIndBimod]

theorem resIndToGradedInd_gradedIndToResInd (y : GradedInd k Γ ν' ν'' N) :
    resIndToGradedInd hP hD hZ hΓ hW hL hν₁ N (gradedIndToResInd hP hD hZ hΓ hW hL hν₁ N y) =
      (castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ 1) • y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]
  | tmul m x =>
    have hm : ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁
        (ResIndBimodule.ofIndBimod hP hD hZ hΓ hW hL hν₁ m) =
          (castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ 1) • m :=
      Subtype.ext (Subtype.ext (by
        change inductionVal k hν₁ 1 * _ =
          ((castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ 1)).1 * _
        rw [castW_symm_val]; rfl))
    rw [gradedIndToResInd_tmul, resIndToGradedInd_tmul, hm, BalancedTensor.smul_tmul']

end Maps

end CommRing

section Field

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

variable {P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
    (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (ν' + ν''), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand (ν' + ν'')), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hν₁ : ν₁ + ν₂ = ν' + ν'') (G : GradingDatum Γ) (hS : Γ.Standing)
  (Q : GProj (G.klrGrade ν')) (Q' : GProj (G.klrGrade ν''))
  [Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) (Q.extTensor Q').carrier)]
  [Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) (Q.extTensor Q').carrier)]

/-- **`Res_{ν₁;ν₂} Ind_{ν';ν''} (P ⊠ P') ≅ ResIndBimodule ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ P')`** as
graded `W_{ν₁} ⊗ W_{ν₂}`-modules (Webster, arXiv:1209.2463v4, proof of Theorem 2.19), with
`W_{ν₁+ν₂}` acting on `Ind (P ⊠ P')` through `castW`. -/
def resIndTensorGradedIso :
    (balancedTensorGProj (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
      (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) (Q.extTensor Q').grading
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁)
      (resIndBimoduleGrading hP hD hZ hΓ hW hL rfl hν₁ G)
      (fun _ _ _ _ hz hw => op_smul_mem_resIndBimoduleGrading G hz hw)).Iso
    (G.resGProj ν₁ ν₂ hD hZ hS (GProj.restrict (castW k Γ hν₁.symm)
      (fun _ _ h => G.castW_symm_mem_klrGrade hν₁.symm h) (G.indProj Q Q'))) where
  toLinearEquiv :=
    { toFun := fun t => ⟨resIndToGradedInd hP hD hZ hΓ hW hL hν₁ _ t, by
        show (castW k Γ hν₁.symm).symm (inductionMap k Γ ν₁ ν₂ 1) •
          resIndToGradedInd hP hD hZ hΓ hW hL hν₁ _ t = _
        rw [← resIndToGradedInd_smul, one_smul]
        rfl⟩
      invFun := fun l => gradedIndToResInd hP hD hZ hΓ hW hL hν₁ _ l.1
      map_add' := fun s t => Subtype.ext (map_add _ s t)
      map_smul' := fun u t => Subtype.ext (resIndToGradedInd_smul hP hD hZ hΓ hW hL hν₁ _ u t)
      left_inv := fun t => gradedIndToResInd_resIndToGradedInd hP hD hZ hΓ hW hL hν₁ _ t
      right_inv := fun l => Subtype.ext
        ((resIndToGradedInd_gradedIndToResInd hP hD hZ hΓ hW hL hν₁ _ l.1).trans l.2) }
  map_mem' _ _ ht :=
    balancedGrading_map_mem (G.gradedIndGrading ν' ν'' (Q.extTensor Q').grading)
      (resIndToGradedInd hP hD hZ hΓ hW hL hν₁ _) (fun _ _ z _ hz hx => by
        rw [resIndToGradedInd_tmul]
        exact tmul_mem_balancedGrading (B := WeightedKLRAlgebra k Γ (ν' + ν''))
          (ℳ := G.indBimodGrading ν' ν'')
          (m := ResIndBimodule.toIndBimod hP hD hZ hΓ hW hL hν₁ z) hz hx) ht
  symm_map_mem' _ _ hl :=
    balancedGrading_map_mem _ (gradedIndToResInd hP hD hZ hΓ hW hL hν₁ _)
      (fun i _ m _ hm hx => by
        rw [gradedIndToResInd_tmul]
        refine tmul_mem_balancedGrading (n := _) ?_ hx
        rw [mem_resIndBimoduleGrading, ResIndBimodule.ofIndBimod_val, ← zero_add i]
        exact SetLike.GradedMul.mul_mem (inductionVal_one_mem_grade G hν₁) hm) hl

/-- **`Res_{ν₁;ν₂} [Ind (P ⊠ P')] = [ResIndBimodule ⊗ (P ⊠ P')]`** in the graded `K₀` of
`W_{ν₁} ⊗ W_{ν₂}` (Webster, arXiv:1209.2463v4, proof of Theorem 2.19), with
`K₀(W_{ν'+ν''})` identified with `K₀(W_{ν₁+ν₂})` along `castW`. The hypotheses `hP`, `hΓ`, `hW`,
`hL` are those of Webster's Theorem 2.8 used to build the bimodule `Res Ind`. -/
theorem resK0_map_indK0_eq :
    G.resK0 ν₁ ν₂ hD hZ hS (K0.map (castW k Γ hν₁.symm)
      (fun _ _ h => G.castW_symm_mem_klrGrade hν₁.symm h)
      (G.indK0 ν' ν'' (K0.of Q) (K0.of Q'))) =
      K0.of (balancedTensorGProj (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
        (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) (Q.extTensor Q').grading
        (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁)
        (resIndBimoduleGrading hP hD hZ hΓ hW hL rfl hν₁ G)
        (fun _ _ _ _ hz hw => op_smul_mem_resIndBimoduleGrading G hz hw)) := by
  rw [GradingDatum.indK0_of, K0.map_of, GradingDatum.resK0_of]
  exact (K0.of_eq_of_iso (resIndTensorGradedIso hP hD hZ hΓ hW hL hν₁ G hS Q Q')).symm

end Field

end GalleryAlgebra

end Categorification.WeightedKLR

end
