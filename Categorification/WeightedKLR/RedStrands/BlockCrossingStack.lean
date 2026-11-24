/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingProduct
import Categorification.Algebra.BalancedTensor

/-!
# Stacking the local crossing with partial standardization

Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and §6.1, proof of Lemma 6.8.
In the right-module convention the local crossing is the left tensor factor. The middle
algebra is the external product in the uncrossed order, not the full global bottom corner.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
variable {k : Type v} [CommRing k]

namespace BlockCut
variable {R U D : Type v} [Ring R] [Algebra k R] [Ring U] [Algebra k U] [Ring D] [Algebra k D]
    {l : U →ₙₐ[k] R} {r : D →ₙₐ[k] R} (C : BlockCut (k := k) R (l 1) (r 1))

theorem incl_injective : Function.Injective C.incl := Function.LeftInverse.injective C.cut_incl

private theorem sandwich (x : C.space) : l 1 * C.incl x * r 1 = C.incl x :=
  (C.incl_cut _).symm.trans (congrArg C.incl (C.cut_incl x))

theorem left_fixed (x : C.space) : l 1 * C.incl x = C.incl x := by
  rw [← C.sandwich x, ← mul_assoc, ← mul_assoc, ← map_mul, one_mul]

theorem right_fixed (x : C.space) : C.incl x * r 1 = C.incl x := by
  rw [← C.sandwich x, mul_assoc _ (r 1), ← map_mul, one_mul]

private theorem incl_left (a : U) (x : C.space) : C.incl (C.cut (l a * C.incl x)) = l a * C.incl x := by
  rw [C.incl_cut, ← mul_assoc, ← map_mul, one_mul, mul_assoc, C.right_fixed]

private theorem incl_right (b : D) (x : C.space) : C.incl (C.cut (C.incl x * r b)) = C.incl x * r b := by
  rw [C.incl_cut, ← mul_assoc, C.left_fixed, mul_assoc, ← map_mul, mul_one]

/-- Top multiplication on the exterior product, computed in the product of the local algebras. -/
abbrev leftModule : Module U C.space where
  smul a x := C.cut (l a * C.incl x)
  one_smul x := congrArg C.cut (C.left_fixed x) |>.trans (C.cut_incl x)
  mul_smul a b x := C.incl_injective (by
    change C.incl (C.cut (l (a*b) * C.incl x)) = C.incl (C.cut (l a * C.incl (C.cut (l b * C.incl x))))
    rw [C.incl_left, C.incl_left, C.incl_left, map_mul, mul_assoc])
  smul_zero a := by change C.cut (l a * C.incl 0) = 0; rw [map_zero, mul_zero, map_zero]
  smul_add a x y := by change C.cut (l a * C.incl (x+y)) = _; rw [map_add, mul_add, map_add]; rfl
  zero_smul x := by change C.cut (l 0 * C.incl x) = 0; rw [map_zero, zero_mul, map_zero]
  add_smul a b x := by change C.cut (l (a+b) * C.incl x) = _; rw [map_add, add_mul, map_add]; rfl

/-- The balancing algebra acts on the bottom ends of the local diagrams. -/
abbrev rightModule : Module Dᵐᵒᵖ C.space where
  smul b x := C.cut (C.incl x * r b.unop)
  one_smul x := congrArg C.cut (C.right_fixed x) |>.trans (C.cut_incl x)
  mul_smul a b x := C.incl_injective (by
    change C.incl (C.cut (C.incl x * r (b.unop * a.unop))) =
      C.incl (C.cut (C.incl (C.cut (C.incl x * r b.unop)) * r a.unop))
    rw [C.incl_right, C.incl_right, C.incl_right, map_mul, mul_assoc])
  smul_zero b := by change C.cut (C.incl 0 * r b.unop) = 0; rw [map_zero, zero_mul, map_zero]
  smul_add b x y := by change C.cut (C.incl (x+y) * r b.unop) = _; rw [map_add, add_mul, map_add]; rfl
  zero_smul x := by change C.cut (C.incl x * r 0) = 0; rw [map_zero, mul_zero, map_zero]
  add_smul a b x := by change C.cut (C.incl x * r (a.unop+b.unop)) = _; rw [map_add, mul_add, map_add]; rfl

private def pairing {E : Type*} [AddCommGroup E] [Module k E] (g : R →ₐ[k] Module.End k E)
    (S : Submodule k E) : C.space →ₗ[k] S →ₗ[k] LinearMap.range (g (l 1)) := by
  let m (x : C.space) := (g (C.incl x)) ∘ₗ S.subtype
  let m' (x : C.space) := (m x).codRestrict (LinearMap.range (g (l 1))) fun z => by
    refine ⟨m x z, ?_⟩
    change (g (l 1) * g (C.incl x)) z.1 = g (C.incl x) z.1
    rw [← map_mul, C.left_fixed]
  exact {
    toFun := m'
    map_add' := fun x y => LinearMap.ext fun z => Subtype.ext (by
      change (g (C.incl (x+y))) z.1 = _; rw [map_add, map_add]; rfl)
    map_smul' := fun c x => LinearMap.ext fun z => Subtype.ext (by
      change (g (C.incl (c • x))) z.1 = _; rw [map_smul, map_smul]; rfl) }

end BlockCut

variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
local notation "Bs" => adjacentRow L M f β
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "D₀" => orderedProduct Q Λ botOrd Bs
local notation "D₁" => orderedProduct Q Λ topOrd Bs
local notation "ι₀" => orderedInclusion Q Λ hQ botOrd Bs
local notation "ι₁" => orderedInclusion Q Λ hQ topOrd Bs
local notation "C" => crossingProduct Q Λ hQ M f β L

instance crossingLeftModule : Module D₁ (C).space := (C).leftModule
instance crossingRightModule : Module D₀ᵐᵒᵖ (C).space := (C).rightModule

theorem crossing_incl_left (a : D₁) (x : (C).space) :
    (C).incl (a • x) = ι₁ a * (C).incl x := (C).incl_left a x

theorem crossing_incl_right (b : D₀ᵐᵒᵖ) (x : (C).space) :
    (C).incl (b • x) = (C).incl x * ι₀ b.unop := (C).incl_right b.unop x

instance crossingScalarTower : IsScalarTower k D₁ (C).space where
  smul_assoc c a x := (C).incl_injective (by rw [crossing_incl_left, map_smul, map_smul,
    crossing_incl_left, smul_mul_assoc])

instance crossingComm : SMulCommClass D₁ D₀ᵐᵒᵖ (C).space where
  smul_comm a b x := (C).incl_injective (by
    rw [crossing_incl_left, crossing_incl_right, crossing_incl_right, crossing_incl_left, mul_assoc])

variable (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "S₀" => orderedColumn Q Λ hQ botOrd L M f β h
local notation "S₁" => orderedColumn Q Λ hQ topOrd L M f β h
local notation "act" => blockProductAction Q Λ L M f β h
local notation "Z" => BalancedTensor k D₁ D₀ (BlockCut.space C) S₀

instance orderedColumnScalarTower (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) :
    IsScalarTower k (orderedProduct Q Λ σ Bs) (orderedColumn Q Λ hQ σ L M f β h) where
  smul_assoc c a z := LinearMap.congr_fun ((orderedBlockAction Q Λ hQ σ L M f β h).toLinearMap.map_smul c a) z

private def stackingPairing : (C).space →ₗ[k] S₀ →ₗ[k] S₁ := (C).pairing act S₀

/-- **Ordinary balanced stacking** (Webster, arXiv:1309.3796v2, proof of Lemma 6.8).
Stack the external tensor of spectator regulars and the local crossing on the
partial-standardization column. Balancing is multiplication at the uncrossed seam. -/
def crossingStack : Z →ₗ[D₁] S₁ := by
  letI : AddCommGroup S₀ := Submodule.addCommGroup _
  letI : AddCommGroup S₁ := Submodule.addCommGroup _
  apply BalancedTensor.liftB (k := k) (B := D₁) (A := D₀) (M := (C).space) (N := S₀) (P := S₁)
    (stackingPairing Q Λ hQ L M f β h)
  · intro x b z; apply Subtype.ext
    change act ((C).incl (op b • x)) z.1 = act ((C).incl x) (act (ι₀ b) z.1)
    rw [crossing_incl_right, map_mul]; rfl
  · intro a x z; apply Subtype.ext
    change act ((C).incl (a • x)) z.1 = act (ι₁ a) (act ((C).incl x) z.1)
    rw [crossing_incl_left, map_mul]; rfl

/-- On elementary tensors this is the action of the juxtaposed crossing diagrams. -/
theorem crossingStack_tmul (x : (C).space) (z : S₀) :
    (crossingStack Q Λ hQ L M f β h (BalancedTensor.tmul x z)).1 = act ((C).incl x) z.1 := rfl

end Categorification.Stendhal.RedBlock
