/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorGenerators

/-!
# The divided tensor generators by black content

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38: a block of black content
`ν` corresponds to the weight `∑ λⱼ − ν`. Projecting the divided-word
spanning theorem onto each tensor weight gives its integral version.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ}

/-- Black content counts multiplicities in divided blocks and ignores red insertions. -/
def TensorWord.content : {n : ℕ} → TensorWord I n → I →₀ ℕ
  | _, .empty => 0
  | _, .red w => w.content
  | _, .black w i n => w.content + Finsupp.single i n

private abbrev totalWeight (wt : Fin ℓ → Dom R) (ν : I →₀ ℕ) : Y →+ ℤ :=
  (∑ j, (wt j).1) - R.rootSum ν

/-- Each divided tensor word has the weight specified by its black content. -/
theorem tensorWordVector_torus : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin n → Dom R) (μ : Y),
    tensorRepresentation wt (K R 𝕍 μ) (tensorWordVector w wt) =
      𝕍 ^ (totalWeight wt w.content μ) • tensorWordVector w wt
  | _, .empty, wt, μ => by
    change (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wt))) (counit R 𝕍 (K R 𝕍 μ)) _ = _
    simp [totalWeight, TensorWord.content]
  | n+1, .red w, wt, μ => by
    let x := tensorWordVector w (fun j => wt (Fin.castSucc j))
    let y := IrreducibleModule.hwv R 𝕍 (wt (Fin.last n)).1
    change tensorRepresentation wt (K R 𝕍 μ) (appendTensor wt x y) = _
    rw [tensorRepresentation_K_append, tensorWordVector_torus w,
      (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := 𝕍) (Λ := (wt (Fin.last n)).1)) μ]
    change appendTensor wt _ _ = 𝕍 ^ _ • appendTensor wt x y
    simp only [appendTensor, TensorProduct.smul_tmul_smul, map_smul,
      ← zpow_add₀ (show (RatFunc.X : 𝕂) ≠ 0 from RatFunc.X_ne_zero)]
    congr 2
    rw [totalWeight, totalWeight, Fin.sum_univ_castSucc (n := n)]
    simp [TensorWord.content, AddMonoidHom.sub_apply, AddMonoidHom.add_apply]
    abel
  | n, .black w i a, wt, μ => by
    let ρ := tensorRepresentation wt
    let : Module (LieLean.QuantumGroup R 𝕍) (TensorSpace wt) := Module.compHom _ ρ.toRingHom
    let : IsScalarTower 𝕂 (LieLean.QuantumGroup R 𝕍) (TensorSpace wt) := ⟨fun c u x => by
      change ρ (c • u) x = c • ρ u x
      rw [map_smul, LinearMap.smul_apply]⟩
    have hx : tensorWordVector w wt ∈ weightSpace R 𝕍 (TensorSpace wt) (totalWeight wt w.content) :=
      fun y => tensorWordVector_torus w wt y
    have he : totalWeight wt (w.black i a).content = totalWeight wt w.content - a • R.root i := by
      simp [totalWeight, TensorWord.content, R.rootSum_add, R.rootSum_single, sub_add_eq_sub_sub]
    rw [he]
    exact (qDivPow_F_smul_mem_weightSpace hx i a) μ

variable [Finite I] (wt : Fin ℓ → Dom R) (hR : R.IsXRegular) (ν : I →₀ ℕ)

/-- The part of the integral ordered tensor lattice in total weight `∑ λⱼ − ν`. -/
def integralTensorWeight : Submodule LP (TensorSpace wt) where
  carrier := {x | x ∈ integralTensor wt ∧ tensorWeightProj wt hR (totalWeight wt ν) x = x}
  zero_mem' := ⟨zero_mem _, map_zero _⟩
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, by rw [map_add, hx.2, hy.2]⟩
  smul_mem' c x hx := ⟨(integralTensor wt).smul_mem _ hx.1, by
    rw [tensor_laurent_smul, map_smul, hx.2]⟩

omit [Finite I] in
private theorem proj_content (w : TensorWord I ℓ) :
    tensorWeightProj wt hR (totalWeight wt w.content) (tensorWordVector w wt) = tensorWordVector w wt :=
  (tensorWeightProj_eq_self_iff wt hR _ _).mpr fun y => by
    rw [← tensorRepresentation_K]; exact tensorWordVector_torus w wt y

/-- Each integral weight space is spanned by exactly the divided tensor
generators of its black content (Webster, §4.7, Theorem 4.38). -/
theorem span_tensorWordVector_content :
    Submodule.span LP {x | ∃ w : TensorWord I ℓ, w.content = ν ∧ x = tensorWordVector w wt} =
      integralTensorWeight wt hR ν := by
  classical
  set S := Submodule.span LP {x | ∃ w : TensorWord I ℓ, w.content = ν ∧ x = tensorWordVector w wt}
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, rfl, rfl⟩
    exact ⟨span_tensorWordVector wt ▸ (Submodule.subset_span (Set.mem_range_self w)), proj_content wt hR w⟩
  · rintro x ⟨hx, he⟩
    rw [← he]
    clear he
    rw [← span_tensorWordVector] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w,rfl⟩ := hz
      change tensorWeightProj wt hR (totalWeight wt ν) (tensorWordVector w wt) ∈ S
      by_cases h : w.content = ν
      · rw [← h, proj_content]
        exact Submodule.subset_span ⟨w,h,rfl⟩
      · have hn : totalWeight wt ν ≠ totalWeight wt w.content := fun e =>
          h ((R.rootSum_injective hR (sub_right_injective e)).symm)
        rw [← proj_content wt hR w, tensorWeightProj_orthogonal wt hR hn]
        exact S.zero_mem
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul c x _ hx =>
      rw [tensor_laurent_smul, map_smul, ← tensor_laurent_smul]
      exact S.smul_mem c hx

end Categorification.Stendhal.FirstWeight
