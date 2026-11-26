/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightRowStandardClass
import Categorification.WeightedKLR.RedStrands.TensorWordWeights

set_option backward.isDefEq.respectTransparency false

/-!
# The class of a right row standard is a word tensor

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Corollary 6.10. The word tensor `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}` has weight
`∑ λ_j - α(|u|)` (`wordTensor_torus`), so it is orthogonal to the images of projective classes of
other black contents (`orderedForm_wordTensor_block`). If the right standard module at the row
loading of `u` has a finite projective resolution `P_•`, then by Proposition 5.6 and
nondegeneracy of the form, `η Σ (-1)^j [P_j]` is that word tensor (`eta_altSum_rightRowStandard`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "𝕍" => (RatFunc.X : 𝕂)

section Weight

variable {I : Type} [DecidableEq I] (C : QuantumGroup.CartanDatum I)
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}

/-- The word tensor of `u` has weight `∑ λ_j - α(|u|)`. -/
theorem wordTensor_torus : ∀ {n : ℕ} (wt : Fin n → Dom R) (u : Fin n → List I) (μ : Y),
    tensorRepresentation wt (K R 𝕍 μ) (wordTensor C wt u) =
      𝕍 ^ (((∑ j, (wt j).1) - R.rootSum (blockContent u).toFinsupp) μ) • wordTensor C wt u
  | 0, wt, u, μ => by
    change (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wt))) (counit R 𝕍 (K R 𝕍 μ)) _ = _
    simp [blockContent]
  | n+1, wt, u, μ => by
    let x := wordTensor C (fun j => wt (Fin.castSucc j)) (fun j => u (Fin.castSucc j))
    let y := ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 _ (F R 𝕍 i)) (u (Fin.last n))
      (IrreducibleModule.hwv R 𝕍 (wt (Fin.last n)).1)
    have hy := ordinarySuffixOp_mem_weightSpace C (wt (Fin.last n)) (u (Fin.last n))
      (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := 𝕍) (Λ := (wt (Fin.last n)).1)) μ
    rw [wordTensor_succ, tensorRepresentation_K_append, wordTensor_torus _ _ μ]
    change appendTensor wt _ (K R 𝕍 μ • y) = _
    rw [hy]
    simp only [appendTensor, TensorProduct.smul_tmul_smul, map_smul,
      ← zpow_add₀ (show (RatFunc.X : 𝕂) ≠ 0 from RatFunc.X_ne_zero)]
    congr 2
    rw [← blockContent_succ u, Multiset.toFinsupp_add, R.rootSum_add, Fin.sum_univ_castSucc]
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply]
    abel

end Weight

section Generator

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "ι" => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ)
local notation "B" => TensorPairing.orderedForm hR wt

/-- The word tensor of `u` is orthogonal to the projective classes of every other black
content. -/
theorem orderedForm_wordTensor_block (u : Fin ℓ → List I) {γ : Multiset I}
    (h : blockContent u ≠ γ) (y : tensorProjectiveGroup C hQ Λ γ) :
    B (wordTensor C wt u) (η (ι γ y)).val = 0 := by
  let μ (s : Multiset I) : Y →+ ℤ := (∑ r, (wt r).1) - R.rootSum s.toFinsupp
  have hμ : μ (blockContent u) ≠ μ γ := by
    intro he
    have hc := R.rootSum_injective hR (sub_right_injective he)
    exact h (by simpa using congrArg Finsupp.toMultiset hc)
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hμ
  have ht := TensorPairing.orderedForm_adjoint hR wt (LieLean.QuantumGroup.K R 𝕍 a)
    (wordTensor C wt u) (η (ι γ y)).val
  simp only [rho_K, barHom_K] at ht
  rw [wordTensor_torus, tensorModuleEquiv_torus_block,
    map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at ht
  change barRingHom (𝕍 ^ μ (blockContent u) a) * _ = 𝕍 ^ (μ γ (-a)) * _ at ht
  rw [map_neg, map_zpow₀, show barRingHom 𝕍 = 𝕍⁻¹ from RatFunc.bar_X, inv_zpow'] at ht
  by_contra hn
  exact ha (neg_injective (zpow_injective_of_not_root RatFunc.X_ne_zero hvn_ratFunc
    (mul_right_cancel₀ hn ht)))

/-- The image under `η'` of a right projective class is the image under `η` of the
reflected left class. -/
theorem rightTensorModuleEquiv_lof_rightTwist (γ : Multiset I)
    (y : tensorProjectiveGroup C hQ Λ γ) :
    (η' (DirectSum.lof LP _ Kr γ (K0.rightTwistEquiv (tensorReflectionG C hQ Λ γ) y)) :
      TensorSpace wt) = η (ι γ y) := by
  have hr : (tensorReflectionK0 C hQ Λ).symm
      (DirectSum.lof LP _ Kr γ (K0.rightTwistEquiv (tensorReflectionG C hQ Λ γ) y)) = ι γ y := by
    rw [LinearEquiv.symm_apply_eq, tensorReflectionK0_lof]
  change (η ((tensorReflectionK0 C hQ Λ).symm _) : TensorSpace wt) = _
  rw [hr]

variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- **Generator classes** (Webster, arXiv:1309.3796v2, proof of Corollary 6.10). If the right
standard module at the row loading of `u` has a finite graded projective resolution `P_•`, then
`η Σ (-1)^j [P_j] = F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}`. -/
theorem eta_altSum_rightRowStandard (u : Fin ℓ → List I)
    {Ps : List (GProj (oppositeGrade (tensorProductGrade G (blockContent u))))}
    (r : GFin.Resolution (rightRowStandard C hQ Λ u) (Ps.map GProj.toGFin)) :
    (η' (altSum (Ps.map fun P => DirectSum.lof LP _ Kr (blockContent u) (K0.of P))) :
      TensorSpace wt) = wordTensor C wt u := by
  set a : TensorSpace wt :=
    (η' (altSum (Ps.map fun P => DirectSum.lof LP _ Kr (blockContent u) (K0.of P))) :
      TensorSpace wt)
  have hform := classFunctional_eq_form_of_resolution C hQ hR Λ wt hwt (blockContent u) r
  have hB : B a = B (wordTensor C wt u) := by
    rw [← hform]
    have key : ∀ x : DirectSum (Multiset I) Kr,
        classFunctional C hQ hR Λ wt hwt (blockContent u) (rightRowStandard C hQ Λ u) (η' x) =
          B (wordTensor C wt u) (η' x) := by
      intro x
      induction x using DirectSum.induction_on with
      | zero => simp only [map_zero, ZeroMemClass.coe_zero]
      | add x y hx hy => rw [map_add, Submodule.coe_add, map_add, map_add, hx, hy]
      | of γ y =>
        rw [← DirectSum.lof_eq_of LP]
        by_cases hγ : blockContent u = γ
        · subst hγ
          exact classFunctional_rightRowStandard C hQ hR Λ wt hwt u y
        · obtain ⟨y', rfl⟩ := (K0.rightTwistEquiv (tensorReflectionG C hQ Λ γ)).surjective y
          rw [classFunctional_eta, rightTensorModuleEquiv_lof_rightTwist,
            orderedForm_wordTensor_block C hQ hR Λ wt hwt u hγ y',
            DirectSum.lof_eq_of, DirectSum.of_eq_of_ne γ (blockContent u) _ hγ,
            map_zero, map_zero]
    refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz => ?_
    obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
    have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
    rw [hzx]
    exact key x
  have h0 := (TensorPairing.orderedForm_nondegenerate hR wt).1 (a - wordTensor C wt u)
    fun z => by rw [map_sub, LinearMap.sub_apply, hB, sub_self]
  exact sub_eq_zero.1 h0

end Generator

end Categorification.Stendhal.FirstWeight
