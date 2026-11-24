/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FundamentalPrefixCorners
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient

/-!
# The fundamental middle character across a red crossing

For Webster, arXiv:1309.3796v2, Proposition 7.11, consider the two
fundamental reds and the single black strand of type A₁. In the crossed
middle-to-middle corner the only possible permutation reverses all three
strands. A reduced representative passes through the violated loading.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA Equiv MvPolynomial
open BraidedStendhalAlgebra

local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "V" => ViolQuotient ℚ Q wt ν
local notation "R" => KLRAlgebra ℚ (stendhalQ Q wt) μ

/-- The projection from the affine KLR diagrams to the braided violating quotient. -/
abbrev braidProject : R →ₐ[ℚ] V := (violMk ℚ Q wt ν).comp (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν)

/-- The middle cut after interchanging the fundamental red strands. -/
def crossedMiddle : Seq μ := KLRAlgebra.Seq.ofList [.inr 1,.inl (),.inr 0] (by decide)

/-- The terminal cut after interchanging the two red strands. -/
def crossedTerminal : Seq μ := KLRAlgebra.Seq.ofList [.inr 1,.inr 0,.inl ()] (by decide)

private theorem unique_perm (s : Seq μ) {u v : Perm (Fin (Multiset.card μ))} (h : u • s = v • s) : u = v :=
  NonInteracting.smul_left_injective (by simp [stendhalWeight]) s h

/-- Each pair of loadings has a single affine permutation. Every crossed
diagram in the corresponding corner is spanned by its chosen reduced word
with dots at the bottom. -/
theorem fundamentalBraidCorner_mem_span (s t : Seq μ) (γ : List ℕ)
    (hγ : IsReduced (Multiset.card μ) γ) (ht : wordProd (Multiset.card μ) γ • s = t) (x : V) :
    braidProject (e t) * x * braidProject (e s) ∈ Submodule.span ℚ
      (Set.range fun u : Fin (Multiset.card μ) →₀ ℕ => braidProject (ψw γ * pol (monomial u 1) * e s)) := by
  classical
  let w := wordProd (Multiset.card μ) γ
  let ρ := fun v => if v = w then γ else canWord (Multiset.card μ) v
  have hρ (v) : IsReduced (Multiset.card μ) (ρ v) ∧ wordProd (Multiset.card μ) (ρ v) = v := by
    by_cases hv : v = w
    · subst v
      simpa only [ρ, ite_eq_left rfl] using (show IsReduced (Multiset.card μ) γ ∧ wordProd (Multiset.card μ) γ = w from ⟨hγ,rfl⟩)
    · simpa only [ρ,ite_eq_right hv] using ⟨isReduced_canWord (Multiset.card μ) v, wordProd_canWord (Multiset.card μ) v⟩
  obtain ⟨y,rfl⟩ := violMk_surjective x
  obtain ⟨z,rfl⟩ := BraidedStendhalAlgebra.ofKLR_surjective y
  let a : R := e t * z * e s
  change braidProject (e t) * braidProject z * braidProject (e s) ∈ _
  rw [← map_mul, ← map_mul]
  have ha : e t * a * e s = a := by
    dsimp only [a]
    simp only [← mul_assoc,e_mul_self]
    rw [mul_assoc _ (e s),e_mul_self]
  have hs := mem_span_corner' ρ hρ s t ha
  change a ∈ (Submodule.span ℚ _).comap braidProject.toLinearMap
  refine Submodule.span_le.mpr ?_ hs
  rintro _ ⟨v,u,hv,rfl⟩
  obtain rfl : v = w := unique_perm s (hv.trans ht.symm)
  apply Submodule.subset_span
  exact ⟨u, by simp [ρ]⟩

private theorem firstCrossing_violated (s : Seq μ) (hs : IsViolated (sadj (Multiset.card μ) 0 • s)) :
    braidProject (ψ 0 * e s) = 0 := by
  rw [ψ_mul_e,map_mul]
  have hv : braidProject (e (sadj (Multiset.card μ) 0 • s)) = 0 := violMk_e hs
  rw [hv,zero_mul]

private theorem reversed_corner_zero (s t : Seq μ) (hs : IsViolated (sadj (Multiset.card μ) 0 • s))
    (ht : wordProd (Multiset.card μ) [0,1,0] • s = t) (x : V) :
    braidProject (e t) * x * braidProject (e s) = 0 := by
  have hr : IsReduced (Multiset.card μ) [0,1,0] := by
    constructor
    · intro k hk
      simp at hk
      rcases hk with rfl | rfl | rfl <;> decide
    · rw [length_eq_invCount]
      decide +kernel
  have hspan := fundamentalBraidCorner_mem_span s t [0,1,0] hr ht x
  have hz (u : Fin (Multiset.card μ) →₀ ℕ) : braidProject (ψw [0,1,0] * pol (monomial u 1) * e s) = 0 := by
    rw [mul_assoc, ← (e_commute_pol s _).eq, ← mul_assoc]
    change braidProject ((ψ 0 * (ψ 1 * (ψ 0 * 1)) * e s) * pol (monomial u 1)) = 0
    simp only [mul_one,mul_assoc, map_mul]
    have h : braidProject (ψ 0) * braidProject (e s) = 0 := (map_mul braidProject _ _).symm.trans (firstCrossing_violated s hs)
    rw [← mul_assoc (braidProject (ψ 0)) (braidProject (e s)),h,zero_mul,mul_zero,mul_zero]
  refine (show Submodule.span ℚ _ ≤ (⊥ : Submodule ℚ V) from Submodule.span_le.mpr ?_) hspan
  rintro _ ⟨u,rfl⟩
  exact hz u

/-- There is no middle-to-middle diagram in either direction across the red crossing. -/
theorem fundamentalBraid_middle_middle_zero (x : V) :
    braidProject (e crossedMiddle) * x * braidProject (e middle) = 0 ∧
      braidProject (e middle) * x * braidProject (e crossedMiddle) = 0 :=
  ⟨reversed_corner_zero middle crossedMiddle (by unfold IsViolated; decide +kernel) (by decide +kernel) x,
   reversed_corner_zero crossedMiddle middle (by unfold IsViolated; decide +kernel) (by decide +kernel) x⟩

end Categorification.Stendhal.FundamentalCorner
