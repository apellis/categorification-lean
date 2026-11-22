/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastKernel

/-!
# Maps out of a standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5
(standardization, Definition 5.4, as used in the proof of Proposition 5.20). Standardization
`S(N)` is the ordered quotient of parabolic induction. A `k`-linear map `φ : N → Z` into a
module `Z` over the tensor product algebra `T^λ_{θ+β}`, which intertwines the action of the
juxtaposed diagrams `a ⊗ b` on `N` (through the factor algebras) with their action on `Z`,
extends to a `T^λ`-linear map `S(N) → Z`.

## Main results

* `parabolicDesc`: the extension `S(N) → Z`.
* `parabolicDesc_smul`: it intertwines the two actions of `T^λ_{θ+β}`.
* `parabolicDesc_unit`: it restricts to `φ` on the unit vectors `1 ⊗ n`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "F" => parabolicOrderedLoadings (ℓ := ℓ) θ β

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)
  {Z : Type*} [AddCommGroup Z] [Module k Z]
  (σ : TensorProductAlgebra k Q Λ (θ + β) →ₐ[k] Module.End k Z)

/-- The diagrams on the parabolic weight acting on `Z` through `T^λ_{θ+β}`. -/
def parabolicDescAction : KLRAlgebra k (stendhalQ Q Λ)
    (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ) +
      Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β))
    →ₐ[k] Module.End k Z :=
  σ.comp ((TensorProductAlgebra.mk Q Λ (θ + β)).comp
    ((orderProjection Q Λ (θ + β)).comp
      ((StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)).comp
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β)).toAlgHom)))

local notation "κ" => parabolicDescAction Q Λ θ β σ

theorem parabolicDescAction_apply (a : KLRAlgebra k S (α + δ)) :
    κ a = σ (parabolicAffine Q Λ θ β a) := rfl

theorem parabolicDescAction_eSum : κ (eSum S F) = 1 := by
  rw [parabolicDescAction_apply, parabolicOrderedLoadings_eq_redOrderedSet, parabolicAffine,
    castKLR_eSum_redOrderedSet, orderProjection_ofKLR_eSum_redOrderedSet, map_one, map_one]

variable {N} (φ : ParabolicInput Q Λ θ β N →ₗ[k] Z)
  (hφ : ∀ (b : TensorKLR (stendhalQ Q Λ)
      (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
      (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)))
    (n : ParabolicInput Q Λ θ β N), φ (b • n) =
      σ (parabolicAffine Q Λ θ β (concat (stendhalQ Q Λ) _ _ b)) (φ n))

/-- The bilinear map `(r, n) ↦ r · φ(n)` on the input module of induction. -/
def parabolicDescBil : IndBimod S α δ →ₗ[k] ParabolicInput Q Λ θ β N →ₗ[k] Z :=
  LinearMap.mk₂ k (fun r y => κ r.1 (φ y))
    (fun r r' y => by rw [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c r y => by
      change κ (c • r.1) (φ y) = _
      rw [map_smul, LinearMap.smul_apply])
    (fun r y y' => by
      rw [map_add, map_add])
    (fun c r y => by
      change κ r.1 (φ (c • y)) = c • κ r.1 (φ y)
      rw [map_smul, map_smul])

include hφ in
/-- The map from the shuffle module, `r ⊗ n ↦ r · φ(n)`. -/
def parabolicDescShuffle : ParabolicShuffle Q Λ θ β N →ₗ[k] Z :=
  BalancedTensor.lift (parabolicDescBil Q Λ θ β σ φ) (fun r a y => by
    change κ (r.1 * concat S α δ a) (φ y) = κ r.1 (φ (a • y))
    rw [map_mul, Module.End.mul_apply, hφ]
    rfl)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem parabolicDescShuffle_tmul (r : IndBimod S α δ) (y : ParabolicInput Q Λ θ β N) :
    parabolicDescShuffle Q Λ θ β σ φ hφ (BalancedTensor.tmul r y) = κ r.1 (φ y) := rfl

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem parabolicDescShuffle_smul (b : KLRAlgebra k S (α + δ))
    (x : ParabolicShuffle Q Λ θ β N) :
    parabolicDescShuffle Q Λ θ β σ φ hφ (b • x) =
      κ b (parabolicDescShuffle Q Λ θ β σ φ hφ x) := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul r y =>
    rw [BalancedTensor.smul_tmul', parabolicDescShuffle_tmul, parabolicDescShuffle_tmul]
    change κ (b * r.1) _ = _
    rw [map_mul, Module.End.mul_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]

/-- **The extension `S(N) → Z`** of a map `φ : N → Z` compatible with the factor actions. -/
def parabolicDesc : ParabolicStandard Q Λ θ β N →ₗ[k] Z :=
  (excludedSpace (parabolicShuffleAction Q Λ θ β N) F).liftQ
    (parabolicDescShuffle Q Λ θ β σ φ hφ) (fun x hx => by
      rw [LinearMap.mem_ker]
      have hx' : eSum S F • x = 0 := hx
      rw [← Module.End.one_apply (R := k) (parabolicDescShuffle Q Λ θ β σ φ hφ x),
        ← parabolicDescAction_eSum Q Λ θ β σ, ← parabolicDescShuffle_smul, hx', map_zero])

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem parabolicDesc_mk (x : ParabolicShuffle Q Λ θ β N) :
    parabolicDesc Q Λ θ β σ φ hφ
        ((excludedSpace (parabolicShuffleAction Q Λ θ β N) F).mkQ x) =
      parabolicDescShuffle Q Λ θ β σ φ hφ x := rfl

/-- `S(N) → Z` intertwines the actions of `T^λ_{θ+β}`. -/
theorem parabolicDesc_smul (t : T) (m : ParabolicStandard Q Λ θ β N) :
    parabolicDesc Q Λ θ β σ φ hφ (parabolicStandardAction Q Λ θ β N hQ t m) =
      σ t (parabolicDesc Q Λ θ β σ φ hφ m) := by
  obtain ⟨a, rfl⟩ := parabolicAffine_surjective Q Λ θ β t
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (excludedSpace (parabolicShuffleAction Q Λ θ β N) F) m
  rw [parabolicStandardAction_affine]
  change parabolicDesc Q Λ θ β σ φ hφ
      ((excludedSpace (parabolicShuffleAction Q Λ θ β N) F).mkQ (a • x)) = _
  rw [parabolicDesc_mk, parabolicDesc_mk, parabolicDescShuffle_smul]
  rfl

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- On the unit vectors `1 ⊗ n` the extension is `φ`. -/
theorem parabolicDesc_unit (n : ParabolicInput Q Λ θ β N) :
    parabolicDesc Q Λ θ β σ φ hφ ((excludedSpace (parabolicShuffleAction Q Λ θ β N) F).mkQ
      (indShuffleUnit (Q := S) (ν := α) (ν' := δ) (ParabolicInput Q Λ θ β N) n)) = φ n := by
  change κ (oneConcat S α δ) (φ n) = φ n
  have h := hφ 1 n
  rw [one_smul, concat_one] at h
  exact h.symm

end Categorification.Stendhal
