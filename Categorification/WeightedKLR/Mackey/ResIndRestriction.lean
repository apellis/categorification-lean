/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndChain

/-!
# `Res ∘ Ind` as a balanced tensor product with the bimodule `Res Ind`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). For
`ν₁ + ν₂ = ν' + ν''` and a left `W_{ν'} ⊗ W_{ν''}`-module `X`, restricting the induced module
`Ind X = W_{ν'+ν''} ι_{ν';ν''}(1) ⊗ X` along `ι_{ν₁;ν₂}` gives the balanced tensor product of the
bimodule `Res_{ν₁;ν₂} Ind_{ν';ν''}` (`ResIndBimodule`) with `X`:
`Res_{ν₁;ν₂} Ind X ≅ ResIndBimodule ⊗_{W_{ν'} ⊗ W_{ν''}} X` as left `W_{ν₁} ⊗ W_{ν₂}`-modules
(`resIndTensorEquiv`). The algebra `W_{ν₁+ν₂}` acts on `Ind X` through an isomorphism
`σ : W_{ν₁+ν₂} ≅ W_{ν'+ν''}` compatible with `castGallery`, for instance `castW`.

## Main definitions and results

* `ResIndBimodule.toCorner`: an element of `Res Ind` as an element of the corner
  `W_{ν'+ν''} ι_{ν';ν''}(1)`.
* `resIndTensorEquiv`: `ResIndBimodule ⊗ X ≅ Res_{ν₁;ν₂} Ind X`, `W_{ν₁} ⊗ W_{ν₂}`-linear.
-/

noncomputable section

namespace Categorification.InductionAlong

/-- Induction on `IndK k N φ` with the zero, sum and `IndK.tmul` of `IndK`. -/
@[elab_as_elim]
theorem IndK.induction_on.{a, n} {k : Type*} [CommRing k] {A : Type a} [Ring A] {B : Type a}
    [Ring B] [Algebra k B] {N : Type n} [AddCommGroup N] [Module A N] {φ : A →ₙ+* B}
    {motive : IndK k N φ → Prop} (t : IndK k N φ) (zero : motive 0)
    (tmul : ∀ z n, motive (IndK.tmul z n)) (add : ∀ s t, motive s → motive t → motive (s + t)) :
    motive t :=
  Ind.induction_on (motive := motive) t zero tmul add

end Categorification.InductionAlong

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose InductionAlong MulOpposite
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

variable {P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
    (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (ν' + ν''), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand (ν' + ν'')), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hν₁ : ν₁ + ν₂ = ν' + ν'')

/-- `ι_{ν₁;ν₂}(u)` lies in the corner `W_{ν₁+ν₂+…}` after casting. -/
theorem inductionVal_mem_corner (hν : ν₁ + ν₂ = ν' + ν'')
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) :
    inductionVal k hν u ∈ Subsemigroup.corner (rankIdem k Γ (ν' + ν'')) := by
  rw [inductionVal_apply, ← castW_val]
  exact (castW k Γ hν (inductionMap k Γ ν₁ ν₂ u)).2

namespace ResIndBimodule

theorem val_mem_corner (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    z.val ∈ Subsemigroup.corner (rankIdem k Γ (ν' + ν'')) := by
  have hi := isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := ν' + ν'')
  have h₁ := (Subsemigroup.mem_corner_iff hi).1 (inductionVal_mem_corner hν₁ 1)
  have h₂ := (Subsemigroup.mem_corner_iff hi).1
    (inductionMap k Γ ν' ν'' (1 : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')).2
  rw [Subsemigroup.mem_corner_iff hi]
  refine ⟨?_, ?_⟩
  · rw [← z.one_mul_val, ← mul_assoc, h₁.1]
  · rw [← z.val_mul_one, mul_assoc]
    exact congrArg (z.val * ·) h₂.2

/-- An element of `Res Ind` as an element of `W_{ν'+ν''}`. -/
def toW (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) : WeightedKLRAlgebra k Γ (ν' + ν'') :=
  ⟨z.val, val_mem_corner hP hD hZ hΓ hW hL hν₁ z⟩

/-- An element of `Res Ind` as an element of the corner `W_{ν'+ν''} ι_{ν';ν''}(1)`. -/
def toCorner (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    Corner (inductionRingHom k Γ ν' ν'') :=
  ⟨toW hP hD hZ hΓ hW hL hν₁ z, Subtype.ext z.val_mul_one⟩

@[simp] theorem toCorner_val (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    (toCorner hP hD hZ hΓ hW hL hν₁ z).1.1 = z.val := rfl

/-- The element `ι_{ν₁;ν₂}(1) y` of `Res Ind`, for `y` in the corner `W_{ν'+ν''} ι_{ν';ν''}(1)`. -/
def ofCorner (y : Corner (inductionRingHom k Γ ν' ν'')) :
    ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁ :=
  ⟨inductionVal k hν₁ 1 * y.1.1, by
    have hy : y.1.1 * (inductionMap k Γ ν' ν'' 1).1 = y.1.1 := congrArg Subtype.val y.2
    refine ⟨?_, ?_, fun D C _ _ => ?_⟩
    · rw [← mul_assoc, inductionVal_mul_inductionVal_one]
    · change inductionVal k hν₁ 1 * y.1.1 * (inductionMap k Γ ν' ν'' 1).1 = _
      rw [mul_assoc, hy]
    · have he : ∀ E : FullChamber Γ (ν' + ν''), (e E * e E : GalleryAlgebra k Γ (ν' + ν'')) = e E :=
        fun E => by simp [e_mul_e]
      rw [mackeyFilt_univ, mem_cornerSpace_iff]
      simp only [← mul_assoc, he]
      rw [mul_assoc _ (e C) (e C), he]⟩

@[simp] theorem ofCorner_val (y : Corner (inductionRingHom k Γ ν' ν'')) :
    (ofCorner hP hD hZ hΓ hW hL hν₁ y).val = inductionVal k hν₁ 1 * y.1.1 := rfl


theorem toCorner_add (z z' : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    toCorner hP hD hZ hΓ hW hL hν₁ (z + z') =
      toCorner hP hD hZ hΓ hW hL hν₁ z + toCorner hP hD hZ hΓ hW hL hν₁ z' :=
  Subtype.ext (Subtype.ext rfl)

theorem toCorner_smul (c : k) (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    toCorner hP hD hZ hΓ hW hL hν₁ (c • z) =
      algebraMap k (WeightedKLRAlgebra k Γ (ν' + ν'')) c • toCorner hP hD hZ hΓ hW hL hν₁ z := by
  have hi := isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := ν' + ν'')
  refine Subtype.ext (Subtype.ext ?_)
  change c • z.val = (c • rankIdem k Γ (ν' + ν'')) * z.val
  rw [smul_mul_assoc,
    ((Subsemigroup.mem_corner_iff hi).1 (val_mem_corner hP hD hZ hΓ hW hL hν₁ z)).1]

theorem toCorner_op_smul (a : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    toCorner hP hD hZ hΓ hW hL hν₁ (op a • z) = op a • toCorner hP hD hZ hΓ hW hL hν₁ z :=
  Subtype.ext (Subtype.ext (by
    change inductionVal k hν₁ 1 * z.val * (inductionMap k Γ ν' ν'' a).1 =
      z.val * (inductionMap k Γ ν' ν'' a).1
    rw [z.one_mul_val]))

theorem ofCorner_toCorner (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) :
    ofCorner hP hD hZ hΓ hW hL hν₁ (toCorner hP hD hZ hΓ hW hL hν₁ z) = z :=
  val_injective hP hD hZ hΓ hW hL rfl hν₁ z.one_mul_val

end ResIndBimodule

/-! ### The isomorphism `ResIndBimodule ⊗ X ≅ Res Ind X` -/

section Equiv

variable (X : Type (max u w)) [AddCommGroup X] [Module k X]
  [Module (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') X]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') X]
  (σ : WeightedKLRAlgebra k Γ (ν₁ + ν₂) ≃ₐ[k] WeightedKLRAlgebra k Γ (ν' + ν''))
  (hσ : ∀ a, (σ a).1 = castGallery k Γ hν₁ a.1)

/-- The bilinear map `(z, x) ↦ z ⊗ x` from `Res Ind × X` to `Ind X`. -/
def resIndTensorBil :
    ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁ →ₗ[k] X →ₗ[k]
      IndK k X (inductionRingHom k Γ ν' ν'') :=
  LinearMap.mk₂ k (fun z x => IndK.tmul (ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁ z) x)
    (fun z z' x => by
      rw [ResIndBimodule.toCorner_add]
      exact Ind.add_tmul _ _ x)
    (fun c z x => by
      rw [ResIndBimodule.toCorner_smul, ← IndK.algebraMap_smul]
      exact (Ind.smul_tmul _ _ x).symm)
    (fun z x x' => Ind.tmul_add _ x x')
    (fun c z x => Ind.tmul_algebraMap_smul k (fun c t => map_smul (inductionMap k Γ ν' ν'') c t)
      _ c x)

theorem resIndTensorBil_tmul (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) (x : X) :
    resIndTensorBil hP hD hZ hΓ hW hL hν₁ X z x =
      IndK.tmul (ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁ z) x := rfl

theorem resIndTensorBil_balanced (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁)
    (a : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (x : X) :
    resIndTensorBil hP hD hZ hΓ hW hL hν₁ X (op a • z) x =
      resIndTensorBil hP hD hZ hΓ hW hL hν₁ X z (a • x) := by
  rw [resIndTensorBil_tmul, resIndTensorBil_tmul, ResIndBimodule.toCorner_op_smul]
  exact Ind.op_smul_tmul _ a x

/-- The map `ResIndBimodule ⊗ X → Ind X`, `z ⊗ x ↦ z ⊗ x`. -/
def resIndTensorToInd :
    BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) X →ₗ[k]
        IndK k X (inductionRingHom k Γ ν' ν'') :=
  BalancedTensor.lift (resIndTensorBil hP hD hZ hΓ hW hL hν₁ X)
    (resIndTensorBil_balanced hP hD hZ hΓ hW hL hν₁ X)

theorem resIndTensorToInd_tmul (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) (x : X) :
    resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X (BalancedTensor.tmul z x) =
      IndK.tmul (ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁ z) x :=
  BalancedTensor.lift_tmul _ _ z x

include hσ in
theorem resIndTensorToInd_smul (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (t : BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) X) :
    resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X (u • t) =
      σ (inductionMap k Γ ν₁ ν₂ u) • resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  | tmul z x =>
    have hz : ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁ (u • z) =
        σ (inductionMap k Γ ν₁ ν₂ u) • ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁ z :=
      Subtype.ext (Subtype.ext (by
        change inductionVal k hν₁ u * z.val * (inductionMap k Γ ν' ν'' 1).1 =
          (σ (inductionMap k Γ ν₁ ν₂ u)).1 * z.val
        rw [hσ, mul_assoc]
        exact congrArg (inductionVal k hν₁ u * ·) z.val_mul_one))
    rw [BalancedTensor.smul_tmul', resIndTensorToInd_tmul, resIndTensorToInd_tmul, hz]
    exact (Ind.smul_tmul _ _ x).symm

/-- The map `Ind X → ResIndBimodule ⊗ X`, `y ⊗ x ↦ ι_{ν₁;ν₂}(1) y ⊗ x`. -/
def indToResIndTensor :
    IndK k X (inductionRingHom k Γ ν' ν'') →+
      BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
        (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) X :=
  Ind.liftAdd (fun y x => BalancedTensor.tmul (ResIndBimodule.ofCorner hP hD hZ hΓ hW hL hν₁ y) x)
    (fun y y' x => by
      rw [← BalancedTensor.add_tmul]
      congr 1
      exact ResIndBimodule.val_injective hP hD hZ hΓ hW hL rfl hν₁ (mul_add _ _ _))
    (fun y x x' => BalancedTensor.tmul_add _ x x')
    (fun y a x => by
      rw [← BalancedTensor.op_smul_tmul]
      congr 1
      refine ResIndBimodule.val_injective hP hD hZ hΓ hW hL rfl hν₁ ?_
      change inductionVal k hν₁ 1 * (y.1.1 * (inductionMap k Γ ν' ν'' a).1) =
        inductionVal k hν₁ 1 * (inductionVal k hν₁ 1 * y.1.1) * (inductionMap k Γ ν' ν'' a).1
      simp only [← mul_assoc, inductionVal_mul_inductionVal_one])

omit [IsScalarTower k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') X] in
theorem indToResIndTensor_tmul (y : Corner (inductionRingHom k Γ ν' ν'')) (x : X) :
    indToResIndTensor hP hD hZ hΓ hW hL hν₁ X (IndK.tmul y x) =
      BalancedTensor.tmul (ResIndBimodule.ofCorner hP hD hZ hΓ hW hL hν₁ y) x := rfl

include hσ in
theorem resIndTensorToInd_indToResIndTensor (n : IndK k X (inductionRingHom k Γ ν' ν'')) :
    resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X (indToResIndTensor hP hD hZ hΓ hW hL hν₁ X n) =
      σ (inductionMap k Γ ν₁ ν₂ 1) • n := by
  induction n using IndK.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]
  | tmul y x =>
    have hy : ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁
        (ResIndBimodule.ofCorner hP hD hZ hΓ hW hL hν₁ y) = σ (inductionMap k Γ ν₁ ν₂ 1) • y :=
      Subtype.ext (Subtype.ext (by
        change inductionVal k hν₁ 1 * y.1.1 = (σ (inductionMap k Γ ν₁ ν₂ 1)).1 * y.1.1
        rw [hσ]; rfl))
    rw [indToResIndTensor_tmul, resIndTensorToInd_tmul, hy]
    exact (Ind.smul_tmul _ _ x).symm

theorem indToResIndTensor_resIndTensorToInd
    (t : BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) X) :
    indToResIndTensor hP hD hZ hΓ hW hL hν₁ X (resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X t) =
      t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul z x =>
    rw [resIndTensorToInd_tmul, indToResIndTensor_tmul, ResIndBimodule.ofCorner_toCorner]

/-- `Ind X` as a module over `W_{ν₁+ν₂}` through `σ : W_{ν₁+ν₂} ≅ W_{ν'+ν''}`. -/
abbrev indModuleAlong :
    Module (WeightedKLRAlgebra k Γ (ν₁ + ν₂)) (IndK k X (inductionRingHom k Γ ν' ν'')) :=
  Module.compHom _ (σ : WeightedKLRAlgebra k Γ (ν₁ + ν₂) →+* WeightedKLRAlgebra k Γ (ν' + ν''))

/-- **`Res_{ν₁;ν₂} Ind_{ν';ν''} X ≅ ResIndBimodule ⊗_{W_{ν'} ⊗ W_{ν''}} X`** as left
`W_{ν₁} ⊗ W_{ν₂}`-modules (Webster, arXiv:1209.2463v4, proof of Theorem 2.19), with `W_{ν₁+ν₂}`
acting on `Ind X` through `σ`. -/
def resIndTensorEquiv :
    letI := indModuleAlong X σ
    BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) X ≃ₗ[WeightedKLRAlgebra k Γ ν₁ ⊗[k]
        WeightedKLRAlgebra k Γ ν₂]
      Res (inductionRingHom k Γ ν₁ ν₂) (IndK k X (inductionRingHom k Γ ν' ν'')) :=
  letI := indModuleAlong X σ
  { toFun := fun t => Res.mk (resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X t) (by
      show σ (inductionMap k Γ ν₁ ν₂ 1) • resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X t =
        resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X t
      rw [← resIndTensorToInd_smul hP hD hZ hΓ hW hL hν₁ X σ hσ, one_smul])
    invFun := fun m => indToResIndTensor hP hD hZ hΓ hW hL hν₁ X m.val
    map_add' := fun s t => Res.ext (map_add _ s t)
    map_smul' := fun u t => Res.ext (resIndTensorToInd_smul hP hD hZ hΓ hW hL hν₁ X σ hσ u t)
    left_inv := fun t => indToResIndTensor_resIndTensorToInd hP hD hZ hΓ hW hL hν₁ X t
    right_inv := fun m => Res.ext
      ((resIndTensorToInd_indToResIndTensor hP hD hZ hΓ hW hL hν₁ X σ hσ m.val).trans m.prop) }

theorem resIndTensorEquiv_tmul (z : ResIndBimodule k hP hD hZ hΓ hW hL rfl hν₁) (x : X) :
    letI := indModuleAlong X σ
    (resIndTensorEquiv hP hD hZ hΓ hW hL hν₁ X σ hσ (BalancedTensor.tmul z x)).val =
      IndK.tmul (ResIndBimodule.toCorner hP hD hZ hΓ hW hL hν₁ z) x :=
  resIndTensorToInd_tmul hP hD hZ hΓ hW hL hν₁ X z x

end Equiv

end GalleryAlgebra

end Categorification.WeightedKLR

end
