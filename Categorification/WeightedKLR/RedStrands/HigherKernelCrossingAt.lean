/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer

/-!
# A higher loading crossing into the retained kernel

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
Cutting the actual crossing into the source projective gives a right-module map.
An affine factorization for all surviving cuts proves surjectivity onto the kernel.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
variable {source higher : Seq (stendhalWeight (I := I) ℓ ν)} (a b : Fin ℓ) (sameOrder : redWord higher = redWord source)
variable (hlt : adjacentBlockRoot (I := I) (ν := ν) a b source < adjacentBlockRoot (I := I) (ν := ν) a b higher)
variable (j : ℕ) (hswap : TypeA.sadj (Multiset.card (stendhalWeight ℓ ν)) j • higher = source)

include source higher sameOrder hlt j

local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun w => π (KLRAlgebra.e w)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord source))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))
local notation "d" => orderedLoadingIdemAt Q Λ (redWord source) higher sameOrder
local notation "P" => rIdeal (orderedLoadingIdem Q Λ source)
local notation "K" => blockLoadingKernel Q Λ source a b
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b source) (redWord source)

/-- The red-black crossing from the higher loading into the source projective
is an element of the higher retained kernel. -/
def crossingIntoKernel : K := by
  let c := blockLoadingRep Q Λ source (π (ψ j * KLRAlgebra.e higher))
  refine ⟨c, ?_⟩
  have hd : p higher ∈ J := TwoSidedIdeal.subset_span ⟨higher, sameOrder, hlt, rfl⟩
  change c.1.1 ∈ J
  rw [blockLoadingRep_val, map_mul]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hd))

include hswap in
theorem crossingIntoKernel_val : (crossingIntoKernel Q Λ a b sameOrder hlt j).1.1.1 = π (ψ j * KLRAlgebra.e higher) := by
  change (blockLoadingRep Q Λ source (π (ψ j * KLRAlgebra.e higher))).1.1 = _
  have hx : (KLRAlgebra.e source * (ψ j * KLRAlgebra.e higher) : R) = ψ j * KLRAlgebra.e higher := by
    rw [ψ_mul_e, hswap, ← mul_assoc, e_mul_self]
  have hE : p higher * E = p higher := by
    change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left sameOrder]
    rfl
  rw [blockLoadingRep_val]
  change π (KLRAlgebra.e source) * π (ψ j * KLRAlgebra.e higher) * E = _
  rw [← map_mul, hx, map_mul, mul_assoc, hE]

/-- Left multiplication by the red-black crossing maps the higher loading projective to the kernel. -/
def crossingIntoKernelMap : rIdeal d →ₗ[Tᵐᵒᵖ] K where
  toFun y := op y.1 • crossingIntoKernel Q Λ a b sameOrder hlt j
  map_add' y z := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 + z.1.1) = _ * y.1.1 + _ * z.1.1
    rw [mul_add]
  map_smul' a y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 * a.unop.1) = (_ * y.1.1) * a.unop.1
    rw [mul_assoc]

include hswap in
theorem crossingIntoKernelMap_val (y : rIdeal d) :
    (crossingIntoKernelMap Q Λ a b sameOrder hlt j y).1.1.1 = π (ψ j * KLRAlgebra.e higher) * y.1.1 := by
  change (crossingIntoKernel Q Λ a b sameOrder hlt j).1.1.1 * y.1.1 = _
  rw [crossingIntoKernel_val Q Λ a b sameOrder hlt j hswap]

include hswap in
/-- Affine factorization of the surviving higher cuts implies surjectivity
onto the retained loading kernel. -/
theorem crossingIntoKernelMap_surjective_of_factors
    (hfactor : ∀ w : Seq μ, redWord w = redWord source →
      adjacentBlockRoot a b source < adjacentBlockRoot a b w → ¬ IsViolated w →
      ∀ z : R, ∃ y : R, (ψ j * KLRAlgebra.e higher) * y =
        KLRAlgebra.e source * z * KLRAlgebra.e w) :
    Function.Surjective (crossingIntoKernelMap Q Λ a b sameOrder hlt j) := by
  let F : rIdeal d →ₗ[Tᵐᵒᵖ] P := (K).subtype.comp (crossingIntoKernelMap Q Λ a b sameOrder hlt j)
  suffices h : K ≤ LinearMap.range F by
    intro x
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨y, Subtype.ext hy⟩
  rw [blockLoadingKernel_eq_span]
  apply Submodule.span_le.2
  rintro _ ⟨w, ho, hwlt, z, rfl⟩
  by_cases hv : IsViolated w
  · have hp : p w = 0 := violMk_e hv
    change blockLoadingRep Q Λ source (z * p w) ∈ LinearMap.range F
    rw [hp, mul_zero]
    convert (LinearMap.range F).zero_mem using 1
    apply Subtype.ext; apply Subtype.ext
    rw [blockLoadingRep_val, mul_zero, zero_mul]
    rfl
  · obtain ⟨z', rfl⟩ := (violMk_surjective.comp ofKLR_surjective : Function.Surjective π) z
    obtain ⟨y, hy⟩ := hfactor w ho hwlt hv z'
    let y' : T := ⟨E * π y * E, π y, rfl⟩
    have hidem : IsIdempotentElem d := by
      apply Subtype.ext
      change π (KLRAlgebra.e higher) * π (KLRAlgebra.e higher) = π (KLRAlgebra.e higher)
      rw [← map_mul, e_mul_self]
    refine ⟨rIdealProj hidem y', ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change (crossingIntoKernelMap Q Λ a b sameOrder hlt j (rIdealProj hidem y')).1.1.1 =
      (blockLoadingRep Q Λ source (π z' * p w)).1.1
    have hE : p higher * E = p higher := by
      change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) * E = _
      rw [← map_mul, e_mul_redProj, ite_eq_left sameOrder]
      rfl
    have hp : p higher * p higher = p higher := congrArg Subtype.val hidem.eq
    rw [crossingIntoKernelMap_val Q Λ a b sameOrder hlt j hswap, blockLoadingRep_val]
    change π (ψ j * KLRAlgebra.e higher) * (p higher * (E * π y * E)) =
      p source * (π z' * p w) * E
    have hfix : π (ψ j * KLRAlgebra.e higher) * p higher = π (ψ j * KLRAlgebra.e higher) := by
      rw [map_mul, mul_assoc, hp]
    have hfix' : π (ψ j * KLRAlgebra.e higher) * E = π (ψ j * KLRAlgebra.e higher) := by
      rw [map_mul, mul_assoc, hE]
    calc
      _ = (π (ψ j * KLRAlgebra.e higher) * p higher * E) * π y * E := by
        simp only [mul_assoc]
      _ = π ((ψ j * KLRAlgebra.e higher) * y) * E := by
        rw [hfix, hfix']
        simp only [map_mul]
      _ = _ := by rw [hy, map_mul, map_mul, mul_assoc (p source)]


end Categorification.Stendhal.BraidedStendhalAlgebra
