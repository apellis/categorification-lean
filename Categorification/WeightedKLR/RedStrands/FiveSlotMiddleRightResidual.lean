/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineHigherKernelMap
import Categorification.WeightedKLR.RedStrands.FiveSlotMiddleRightHigher
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The residual higher quotient at the middle-right loading

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
After quotienting out the central-crossing image, the nearby partial standard
maps surjectively onto the remaining higher quotient.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Module

variable {A P P' M : Type} [Ring A]
  [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A P']
  [AddCommGroup M] [Module A M]

private theorem quotient_surjects_of_two_images
    (first : P →ₗ[A] M) (second : P' →ₗ[A] M) (N : Submodule A P')
    (vanish : ∀ x ∈ N, ∃ y : P, first y = second x)
    (gen : ∀ x : M, ∃ y : P, ∃ z : P', first y + second z = x) :
    ∃ f : (P' ⧸ N) →ₗ[A] (M ⧸ first.range), Function.Surjective f := by
  let G := first.range.mkQ.comp second
  have hker : N ≤ LinearMap.ker G := by
    intro x hx
    obtain ⟨y, hy⟩ := vanish x hx
    exact (Submodule.Quotient.mk_eq_zero first.range).2 ⟨y, hy⟩
  refine ⟨N.liftQ G hker, ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := first.range.mkQ_surjective q
  obtain ⟨y, z, hz⟩ := gen x
  use N.mkQ z
  change N.liftQ G hker (Submodule.Quotient.mk z) = first.range.mkQ x
  rw [Submodule.liftQ_apply]
  change first.range.mkQ (second z) = first.range.mkQ x
  have hz₀ : first.range.mkQ (first y) = 0 := (Submodule.Quotient.mk_eq_zero first.range).2 ⟨y, rfl⟩
  rw [← hz, map_add, hz₀, zero_add]

end Module

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "rightMiddle" => sadj N 2 • fixedTopFourExitCut 2
local notation "central" => fixedTopFourExitCut 1
local notation "nearby" => sadj N 2 • fixedTopFourExitCut 0
local notation "κ" => redWord rightMiddle
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ)
local notation "K" => blockLoadingKernel Q Λ rightMiddle 1 2
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ κ)
local notation "p" => fun s : Seq μ₀ => F (e s)
local notation "c₁" => (ψ 1 * e central : R)
local notation "c₂" => (ψw [3, 2, 1] * e nearby : R)

private theorem central_order : redWord central = κ := by decide
private theorem nearby_order : redWord nearby = κ := by decide

private theorem central_higher : adjacentBlockRoot 1 2 rightMiddle < adjacentBlockRoot 1 2 central := by
  apply lt_of_le_not_ge
  · intro r i
    fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 central 1 () ≤ adjacentBlockRoot 1 2 rightMiddle 1 ())
      (h 1 ())

private theorem nearby_higher : adjacentBlockRoot 1 2 rightMiddle < adjacentBlockRoot 1 2 nearby := by
  apply lt_of_le_not_ge
  · intro r i
    fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 nearby 1 () ≤ adjacentBlockRoot 1 2 rightMiddle 1 ())
      (h 1 ())

private theorem central_left : AffineLeftFixed Q Λ rightMiddle c₁ := by
  have step : sadj N 1 • central = rightMiddle := by decide +kernel
  change (e rightMiddle : R) * (ψ 1 * e central) = ψ 1 * e central
  simp only [ψ_mul_e, step, ← mul_assoc, e_mul_self]

private theorem central_right : AffineRightFixed Q Λ central c₁ := by
  change (ψ 1 * e central : R) * e central = ψ 1 * e central
  rw [mul_assoc, e_mul_self]

private theorem nearby_left : AffineLeftFixed Q Λ rightMiddle c₂ := by
  have step : wordProd N [3, 2, 1] • nearby = rightMiddle := by decide +kernel
  change (e rightMiddle : R) * (ψw [3, 2, 1] * e nearby) = ψw [3, 2, 1] * e nearby
  rw [← step, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

private theorem nearby_right : AffineRightFixed Q Λ nearby c₂ := by
  change (ψw [3, 2, 1] * e nearby : R) * e nearby = ψw [3, 2, 1] * e nearby
  rw [mul_assoc, e_mul_self]

local notation "d₁" => orderedLoadingIdemAt Q Λ κ central central_order
local notation "d₂" => orderedLoadingIdemAt Q Λ κ nearby nearby_order
local notation "P₁" => rIdeal d₁
local notation "P₂" => rIdeal d₂
local notation "K₂" => blockLoadingKernelAt Q Λ nearby 1 2 κ nearby_order

/-- Multiplication by the central crossing, with the higher loading
projective as its source. -/
def fiveSlotMiddleRight_centralMap : P₁ →ₗ[Tᵐᵒᵖ] K :=
  affineIntoKernelMap Q Λ 1 2 central_order central_higher c₁ (central_right Q Λ)

/-- The second word from the nearby loading gives a second projective map. -/
def fiveSlotMiddleRight_nearbyMap : P₂ →ₗ[Tᵐᵒᵖ] K :=
  affineIntoKernelMap Q Λ 1 2 nearby_order nearby_higher c₂ (nearby_right Q Λ)

theorem fiveSlotMiddleRight_centralMap_eq_crossing :
    fiveSlotMiddleRight_centralMap Q Λ =
      crossingIntoKernelMap Q Λ 1 2 central_order central_higher 1 := rfl

local notation "f₁" => fiveSlotMiddleRight_centralMap Q Λ
local notation "f₂" => fiveSlotMiddleRight_nearbyMap Q Λ
local notation "J₁" => LinearMap.range f₁

private theorem centralMap_val (u : P₁) : (f₁ u).1.1.1 = F c₁ * u.1.1 :=
  affineIntoKernelMap_val Q Λ 1 2 central_order central_higher c₁ (central_left Q Λ) (central_right Q Λ) u

private theorem nearbyMap_val (u : P₂) : (f₂ u).1.1.1 = F c₂ * u.1.1 :=
  affineIntoKernelMap_val Q Λ 1 2 nearby_order nearby_higher c₂ (nearby_left Q Λ) (nearby_right Q Λ) u

private theorem mem_nearby_kernel {ω : List (Fin 3)} (hω : redWord nearby = ω)
    (u : rIdeal (orderedLoadingIdemAt Q Λ ω nearby hω)) :
    u ∈ blockLoadingKernelAt Q Λ nearby 1 2 ω hω ↔
      u.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 nearby) ω := by
  subst ω
  rfl

private theorem nearby_kernel_maps_into_central (hQ : KLRSymm Q) (x : P₂) (hx : x ∈ K₂) :
    ∃ a : P₁, f₁ a = f₂ x := by
  have hxJ : x.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2
      (adjacentBlockRoot 1 2 nearby) (redWord nearby) := by
    rw [nearby_order]
    exact (mem_nearby_kernel Q Λ nearby_order x).1 hx
  have xl : p nearby * x.1.1 = x.1.1 := congrArg (fun u : T => u.1) x.2
  obtain ⟨z, hz⟩ := fiveSlotMiddleRight_second_factors_higher_nearby Q Λ hQ x.1.1 hxJ xl
  let a₀ : T := ⟨E * z * E, z, rfl⟩
  have idem : IsIdempotentElem d₁ := by
    apply Subtype.ext
    change p central * p central = p central
    rw [← map_mul, e_mul_self]
  let a : P₁ := rIdealProj idem a₀
  have h₁ : F c₁ * p central = F c₁ := by
    rw [← map_mul]
    exact congrArg F (central_right Q Λ)
  have hpE : p central * E = p central := by
    change violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (e central)) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left central_order]
    rfl
  have h₁E : F c₁ * E = F c₁ := by
    rw [← h₁, mul_assoc, hpE]
  have xr : x.1.1 * E = x.1.1 :=
    CornerEndomorphism.corner_mul_right
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ) x.1
  have hrep : f₁ a = f₂ x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [centralMap_val, nearbyMap_val]
    change F c₁ * (p central * (E * z * E)) = F c₂ * x.1.1
    calc
      _ = (F c₁ * p central * E) * z * E := by simp only [mul_assoc]
      _ = (F c₂ * x.1.1) * E := by rw [h₁, h₁E, ← hz]
      _ = _ := by rw [mul_assoc, xr]
  exact ⟨a, hrep⟩

private theorem middleRight_generated_by_maps (hQ : KLRSymm Q) (x : K) :
    ∃ u : P₁, ∃ v : P₂, f₁ u + f₂ v = x := by
  obtain ⟨a, b, ha, hb, hx⟩ := fiveSlotMiddleRight_blockLoadingKernel_two_factors Q Λ hQ x
  let u : P₁ := ⟨a, Subtype.ext ha⟩
  let v : P₂ := ⟨b, Subtype.ext hb⟩
  have sum : f₁ u + f₂ v = x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (f₁ u).1.1.1 + (f₂ v).1.1.1 = x.1.1.1
    exact (congrArg₂ (fun a b : V => a + b)
      (centralMap_val Q Λ u) (nearbyMap_val Q Λ v)).trans hx.symm
  exact ⟨u, v, sum⟩

/-- The actual nearby higher partial standard surjects onto the remainder
of the middle-right higher kernel after the central crossing. -/
theorem fiveSlotMiddleRight_residual_quotient_of_nearby (hQ : KLRSymm Q) :
    ∃ f : (blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) →ₗ[Tᵐᵒᵖ] (K ⧸ J₁),
      Function.Surjective f := by
  let : AddCommGroup P₁ := Submodule.addCommGroup _
  let : Module Tᵐᵒᵖ P₁ := Submodule.module _
  let : AddCommGroup P₂ := Submodule.addCommGroup _
  let : Module Tᵐᵒᵖ P₂ := Submodule.module _
  change ∃ f : (P₂ ⧸ K₂) →ₗ[Tᵐᵒᵖ] (K ⧸ J₁), Function.Surjective f
  exact quotient_surjects_of_two_images (A := Tᵐᵒᵖ) (P := P₁) (P' := P₂) (M := K)
    f₁ f₂ K₂ (nearby_kernel_maps_into_central Q Λ hQ) (middleRight_generated_by_maps Q Λ hQ)

end Categorification.Stendhal.BraidedStendhalAlgebra
