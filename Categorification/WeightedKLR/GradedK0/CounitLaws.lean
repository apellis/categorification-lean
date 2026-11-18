/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Counit
import Categorification.WeightedKLR.GradedK0.CoproductUnits
import Categorification.WeightedKLR.GradedK0.TotalCoproduct

/-!
# Counit identities for weighted restriction

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, proof of Theorem 2.19, p. 12. The counit identities follow from the
restrictions with one factor of weight zero.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ)

local notation "R" => LaurentPolynomial ℤ
local notation "π" => DirectSum.component R (I →₀ ℕ) G.K0fam

private theorem component_K0cast {ν μ : I →₀ ℕ} (h : ν = μ) (x : G.K0W) :
    π μ x = G.K0cast h (π ν x) := by
  subst μ
  rfl

variable (hD : Γ.Dagger) (hS : Γ.Standing)
  (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
  [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)]

/-- The component at `(0, ν)` is tensoring by the left unit class. -/
theorem splitCoproduct_zero_left (ν : I →₀ ℕ) (x : G.K0fam ν) :
    G.splitCoproduct hD hS hZ hl 0 ν (zero_add ν) x = G.K0one ⊗ₜ x := by
  rw [splitCoproduct_apply]
  exact G.coproductK0_zero_left hD hZ hS _ x

/-- The component at `(ν, 0)` is tensoring by the right unit class. -/
theorem splitCoproduct_zero_right (ν : I →₀ ℕ) (x : G.K0fam ν) :
    G.splitCoproduct hD hS hZ hl ν 0 (add_zero ν) x = x ⊗ₜ G.K0one := by
  rw [splitCoproduct_apply]
  exact G.coproductK0_zero_right hD hZ hS _ x

/-- The zero-weight projection satisfies the left counit identity for the
restriction coproduct (Webster, arXiv:1209.2463v4, §2.4, proof of Theorem 2.19). -/
theorem counitK0_totalCoproduct_left (x : G.K0W) :
    TensorProduct.lid R G.K0W
      (TensorProduct.map G.counitK0 LinearMap.id (G.totalCoproduct hD hS hZ hl x)) = x := by
  apply DirectSum.ext_component R
  intro ν
  have he (z : G.K0W ⊗[R] G.K0W) :
      π ν (TensorProduct.lid R G.K0W (TensorProduct.map G.counitK0 LinearMap.id z)) =
        TensorProduct.lid R (G.K0fam ν)
          (TensorProduct.map G.K0zeroEquiv.toLinearMap LinearMap.id
            (TensorProduct.map (π 0) (π ν) z)) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul a b => simp [counitK0]
  have hs := LinearMap.congr_fun (G.component_totalCoproduct hD hS hZ hl 0 ν) x
  simp only [LinearMap.comp_apply] at hs
  have hzero := G.splitCoproduct_zero_left hD hS hZ hl ν (π ν x)
  rw [splitCoproduct_apply] at hzero
  rw [he, hs, splitCoproduct_apply, K0cast_rfl,
    component_K0cast G (zero_add ν).symm x, hzero]
  simp

/-- The zero-weight projection satisfies the right counit identity for the
restriction coproduct (Webster, arXiv:1209.2463v4, §2.4, proof of Theorem 2.19). -/
theorem counitK0_totalCoproduct_right (x : G.K0W) :
    TensorProduct.rid R G.K0W
      (TensorProduct.map LinearMap.id G.counitK0 (G.totalCoproduct hD hS hZ hl x)) = x := by
  apply DirectSum.ext_component R
  intro ν
  have he (z : G.K0W ⊗[R] G.K0W) :
      π ν (TensorProduct.rid R G.K0W (TensorProduct.map LinearMap.id G.counitK0 z)) =
        TensorProduct.rid R (G.K0fam ν)
          (TensorProduct.map LinearMap.id G.K0zeroEquiv.toLinearMap
            (TensorProduct.map (π ν) (π 0) z)) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul a b => simp [counitK0]
  have hs := LinearMap.congr_fun (G.component_totalCoproduct hD hS hZ hl ν 0) x
  simp only [LinearMap.comp_apply] at hs
  have hzero := G.splitCoproduct_zero_right hD hS hZ hl ν (π ν x)
  rw [splitCoproduct_apply] at hzero
  rw [he, hs, splitCoproduct_apply, K0cast_rfl,
    component_K0cast G (add_zero ν).symm x, hzero]
  simp

/-- The restriction coproduct takes the vacuum class to the tensor of two
vacuum classes (Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19). -/
theorem totalCoproduct_one :
    G.totalCoproduct hD hS hZ hl 1 = (1 : G.K0W) ⊗ₜ[R] (1 : G.K0W) := by
  classical
  rw [G.K0W_one, ← DirectSum.lof_eq_of R, totalCoproduct_lof]
  let p : ↥(Finset.HasAntidiagonal.antidiagonal (0 : I →₀ ℕ)) :=
    ⟨(0, 0), Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add 0)⟩
  rw [Finset.sum_eq_single p]
  · dsimp only [p]
    rw [splitCoproduct_zero_left, TensorProduct.map_tmul]
    rfl
  · intro s _ hs
    have hz := Finsupp.add_eq_zero_iff s.1.1 s.1.2 |>.mp
      (Finset.HasAntidiagonal.mem_antidiagonal.mp s.2)
    exact (hs (Subtype.ext (Prod.ext hz.1 hz.2))).elim
  · exact fun h => (h (Finset.mem_attach _ _)).elim

end Categorification.WeightedKLR.GradingDatum
