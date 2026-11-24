/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt

/-!
# Affine coefficients for higher kernel maps

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
A coefficient fixed by its source and target loading cuts maps the target
projective into the higher kernel. Factorization of the surviving cuts
implies surjectivity.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
/-- An affine coefficient is fixed by multiplication with the source cut. -/
def AffineLeftFixed (s : Seq μ) (c : R) : Prop :=
  (KLRAlgebra.e s : R) * c = c

/-- An affine coefficient is fixed by multiplication with the target cut. -/
def AffineRightFixed (s : Seq μ) (c : R) : Prop :=
  c * (KLRAlgebra.e s : R) = c

variable {source higher : Seq (stendhalWeight (I := I) ℓ ν)} (a b : Fin ℓ) (sameOrder : redWord higher = redWord source)
variable (hlt : adjacentBlockRoot (I := I) (ν := ν) a b source < adjacentBlockRoot (I := I) (ν := ν) a b higher)
variable (coefficient : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
variable (hleft : AffineLeftFixed Q Λ source coefficient)
variable (hright : AffineRightFixed Q Λ higher coefficient)


include source higher sameOrder hlt coefficient hright

local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun w => π (KLRAlgebra.e w)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord source))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))
local notation "d" => orderedLoadingIdemAt Q Λ (redWord source) higher sameOrder
local notation "P" => rIdeal (orderedLoadingIdem Q Λ source)
local notation "K" => blockLoadingKernel Q Λ source a b
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b source) (redWord source)

/-- A coefficient ending at a higher loading gives an element of the source kernel. -/
def affineIntoKernel : K := by
  let c := blockLoadingRep Q Λ source (π (coefficient))
  refine ⟨c, ?_⟩
  have hd : p higher ∈ J := TwoSidedIdeal.subset_span ⟨higher, sameOrder, hlt, rfl⟩
  change c.1.1 ∈ J
  have hright' : coefficient * (KLRAlgebra.e higher : R) = coefficient := hright
  rw [blockLoadingRep_val, ← hright', map_mul]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hd))

include hleft in
theorem affineIntoKernel_val : (affineIntoKernel Q Λ a b sameOrder hlt coefficient hright).1.1.1 = π (coefficient) := by
  change (blockLoadingRep Q Λ source (π (coefficient))).1.1 = _
  have hE : p higher * E = p higher := by
    change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left sameOrder]
    rfl
  rw [blockLoadingRep_val]
  change π (KLRAlgebra.e source) * π (coefficient) * E = _
  have hleft' : (KLRAlgebra.e source : R) * coefficient = coefficient := hleft
  have hright' : coefficient * (KLRAlgebra.e higher : R) = coefficient := hright
  rw [← map_mul, hleft']
  calc
    _ = π (coefficient * KLRAlgebra.e higher) * E := by rw [hright']
    _ = _ := by rw [map_mul, mul_assoc, hE, ← map_mul, hright']

/-- Multiplication by a coefficient ending at the higher loading maps its
projective into the higher retained kernel. -/
def affineIntoKernelMap : rIdeal d →ₗ[Tᵐᵒᵖ] K where
  toFun y := op y.1 • affineIntoKernel Q Λ a b sameOrder hlt coefficient hright
  map_add' y z := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 + z.1.1) = _ * y.1.1 + _ * z.1.1
    rw [mul_add]
  map_smul' a y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 * a.unop.1) = (_ * y.1.1) * a.unop.1
    rw [mul_assoc]

include hleft in
theorem affineIntoKernelMap_val (y : rIdeal d) :
    (affineIntoKernelMap Q Λ a b sameOrder hlt coefficient hright y).1.1.1 = π (coefficient) * y.1.1 := by
  change (affineIntoKernel Q Λ a b sameOrder hlt coefficient hright).1.1.1 * y.1.1 = _
  rw [affineIntoKernel_val Q Λ a b sameOrder hlt coefficient hleft hright]

include hleft in
/-- Affine factorization of the surviving higher cuts implies surjectivity
onto the retained loading kernel. -/
theorem affineIntoKernelMap_surjective_of_factors
    (hfactor : ∀ w : Seq μ, redWord w = redWord source →
      adjacentBlockRoot a b source < adjacentBlockRoot a b w → ¬ IsViolated w →
      ∀ z : R, ∃ y : R, (coefficient) * y =
        KLRAlgebra.e source * z * KLRAlgebra.e w) :
    Function.Surjective (affineIntoKernelMap Q Λ a b sameOrder hlt coefficient hright) := by
  let F : rIdeal d →ₗ[Tᵐᵒᵖ] P := (K).subtype.comp (affineIntoKernelMap Q Λ a b sameOrder hlt coefficient hright)
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
    change (affineIntoKernelMap Q Λ a b sameOrder hlt coefficient hright (rIdealProj hidem y')).1.1.1 =
      (blockLoadingRep Q Λ source (π z' * p w)).1.1
    have hE : p higher * E = p higher := by
      change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) * E = _
      rw [← map_mul, e_mul_redProj, ite_eq_left sameOrder]
      rfl
    rw [affineIntoKernelMap_val Q Λ a b sameOrder hlt coefficient hleft hright, blockLoadingRep_val]
    change π (coefficient) * (p higher * (E * π y * E)) =
      p source * (π z' * p w) * E
    have hright' : coefficient * (KLRAlgebra.e higher : R) = coefficient := hright
    have hfix : π (coefficient) * p higher = π (coefficient) := by
      rw [← map_mul, hright']
    have hfix' : π (coefficient) * E = π (coefficient) := by
      calc
        _ = π (coefficient * KLRAlgebra.e higher) * E := by rw [hright']
        _ = _ := by rw [map_mul, mul_assoc, hE, ← map_mul, hright']
    calc
      _ = (π (coefficient) * p higher * E) * π y * E := by
        simp only [mul_assoc]
      _ = π ((coefficient) * y) * E := by
        rw [hfix, hfix']
        simp only [map_mul]
      _ = _ := by rw [hy, map_mul, map_mul, mul_assoc (p source)]


end Categorification.Stendhal.BraidedStendhalAlgebra
