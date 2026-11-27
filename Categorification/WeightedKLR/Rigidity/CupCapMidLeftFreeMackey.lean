/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeStagedLoopRight
import Categorification.Algebra.InductionAlongExact

/-!
# The model of a cap after `λ_j` as a sum over top loadings

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19 (step (I2) of the route, in `T̃^{λ⁺}`). The diagrams at the maximum at `midPos` are
the sum over the loadings `s` of `λ` of the diagrams on the window at `midPos j s` of `s`, and
these are orthogonal (`midStendhal_eq_sum_posStendhal`, `posStendhal_mul_posStendhal_of_ne`).
Induction along an orthogonal sum of maps is the product of the inductions
(`InductionAlong.Ind.piEquivOfOrthogonal`), so the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` of `K̃` is
the product over `s` of the staged modules `L ⊗_{T̃^{(μ,μ*)}} e_{s, midPos j s} T̃^{λ⁺}`
(`midModelPiEquiv`).

## Main definitions

* `InductionAlong.Ind.piEquivOfOrthogonal`: induction along an orthogonal sum.
* `CupCap.midModelPiEquiv`: the model of `K̃` as a product of staged modules.
-/

noncomputable section

namespace Categorification

open MulOpposite

namespace InductionAlong

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {N : Type w} [AddCommGroup N] [Module A N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {φ : A →ₙ+* B} {ψ : ι → A →ₙ+* B}

omit [DecidableEq ι] in
theorem intertwines_of_orthogonal_incl (hsum : ∀ a, φ a = ∑ s, ψ s a)
    (horth : ∀ s s' a a', s ≠ s' → ψ s a * ψ s' a' = 0) (s : ι) :
    Intertwines (ψ s) φ (ψ s 1) := fun a => by
  rw [hsum, Finset.mul_sum, Finset.sum_eq_single s (fun s' _ h => horth s s' 1 a (Ne.symm h))
    (by simp), ← map_mul, ← map_mul, mul_one, one_mul]

omit [DecidableEq ι] in
theorem intertwines_of_orthogonal_proj (hsum : ∀ a, φ a = ∑ s, ψ s a)
    (horth : ∀ s s' a a', s ≠ s' → ψ s a * ψ s' a' = 0) (s : ι) :
    Intertwines φ (ψ s) (ψ s 1) := fun a => by
  rw [hsum, Finset.sum_mul, Finset.sum_eq_single s (fun s' _ h => horth s' s a 1 h)
    (by simp), ← map_mul, ← map_mul, mul_one, one_mul]

variable (N) in
/-- **Induction along an orthogonal sum is the product of the inductions**: if
`φ = ∑_s ψ_s` with `ψ_s a ψ_{s'} a' = 0` for `s ≠ s'`, then `Ind N φ ≅ ∏_s Ind N ψ_s`,
`y ↦ (y ψ_s(1))_s`. -/
def Ind.piEquivOfOrthogonal (hsum : ∀ a, φ a = ∑ s, ψ s a)
    (horth : ∀ s s' a a', s ≠ s' → ψ s a * ψ s' a' = 0) :
    Ind N φ ≃ₗ[B] ((s : ι) → Ind N (ψ s)) where
  toFun y s := natMap (intertwines_of_orthogonal_proj hsum horth s) y
  map_add' y y' := funext fun s => map_add _ y y'
  map_smul' b y := funext fun s => map_smul _ b y
  invFun f := ∑ s, natMap (intertwines_of_orthogonal_incl hsum horth s) (f s)
  left_inv y := by
    induction y using Ind.induction_on with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, Finset.sum_add_distrib] at hy hy' ⊢
      rw [hy, hy']
    | tmul z n =>
      simp only [natMap_tmul]
      rw [← Ind.sum_tmul]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change ∑ s ∈ Finset.univ, z.1 * ψ s 1 * ψ s 1 = z.1
      refine Eq.trans (b := z.1 * ∑ s, ψ s 1) ?_ (by rw [← hsum]; exact z.2)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, ← map_mul, mul_one]
  right_inv f := by
    funext s
    simp only [map_sum]
    rw [Finset.sum_eq_single s]
    · rw [← LinearMap.comp_apply, natMap_comp, natMap_eq_of_unit_mul _ (Intertwines.unit (ψ s))
        (by rw [← map_mul, ← map_mul, mul_one, mul_one]), natMap_unit, LinearMap.id_apply]
    · intro s' _ h
      rw [← LinearMap.comp_apply, natMap_comp, natMap_eq_of_unit_mul _ Intertwines.zero
        (by rw [mul_zero, ← mul_assoc, ← map_mul, mul_one, horth s' s 1 1 h]), natMap_zero,
        LinearMap.zero_apply]
    · simp

omit [DecidableEq ι] in
theorem Ind.piEquivOfOrthogonal_tmul (hsum : ∀ a, φ a = ∑ s, ψ s a)
    (horth : ∀ s s' a a', s ≠ s' → ψ s a * ψ s' a' = 0) (z : Corner φ) (n : N) (s : ι) :
    Ind.piEquivOfOrthogonal N hsum horth (Ind.tmul z n) s =
      Ind.tmul (cornerMul (intertwines_of_orthogonal_proj hsum horth s) z) n := rfl

end InductionAlong

end Categorification

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

/-- The diagrams at the maximum at `midPos` and on each window come from one KLR diagram. -/
theorem exists_midStendhal_posStendhal (z : StendhalAlgebra k Q Λc ν₀) :
    ∃ x, midStendhal j hj Q Λ Λc ν ν₀ z = midBot j hj Q Λ Λc ν ν₀ x ∧
      ∀ (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ Multiset.card (stendhalWeight ℓ ν)),
        posStendhal j hj Q Λ Λc ν₀ s n hn z = posBot j hj Q Λ Λc ν₀ s n hn x := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨x, ?_, fun s n hn => ?_⟩
  · rw [midStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]
  · rw [posStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]

/-- **The diagrams at the maximum at `midPos` are the sum of the diagrams on the windows**. -/
theorem midStendhal_eq_sum_posStendhal (z : StendhalAlgebra k Q Λc ν₀) :
    midStendhal j hj Q Λ Λc ν ν₀ z =
      ∑ s, posStendhal j hj Q Λ Λc ν₀ s (midPos j s) (midPos_le j s) z := by
  obtain ⟨x, h1, h2⟩ := exists_midStendhal_posStendhal (j := j) (hj := hj) (Λ := Λ) (ν := ν) z
  simp only [h1, h2, midBot_apply, midMapKLR, map_sum, posBot_apply]

/-- **The diagrams on the windows at `midPos` of distinct loadings are orthogonal.** -/
theorem posStendhal_mul_posStendhal_of_ne {s s' : Seq (stendhalWeight ℓ ν)} (h : s ≠ s')
    (z z' : StendhalAlgebra k Q Λc ν₀) :
    posStendhal j hj Q Λ Λc ν₀ s (midPos j s) (midPos_le j s) z *
      posStendhal j hj Q Λ Λc ν₀ s' (midPos j s') (midPos_le j s') z' = 0 := by
  obtain ⟨x, -, hx⟩ := exists_midStendhal_posStendhal (j := j) (hj := hj) (Λ := Λ) (ν := ν) z
  obtain ⟨x', -, hx'⟩ := exists_midStendhal_posStendhal (j := j) (hj := hj) (Λ := Λ) (ν := ν) z'
  rw [hx, hx', posBot_apply, posBot_apply, ← map_mul, insertMap_midPos_mul_of_ne h, map_zero]

theorem midOp_eq_sum_posOp (a : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    midOp j hj Q Λ Λc ν ν₀ a = ∑ s, posOp j hj Q Λ Λc ν₀ s (midPos j s) (midPos_le j s) a := by
  rw [midOp_apply, midStendhal_eq_sum_posStendhal]
  exact map_sum (opAddEquiv : Tp ≃+ Tpᵐᵒᵖ) _ _

theorem posOp_mul_posOp_of_ne {s s' : Seq (stendhalWeight ℓ ν)} (h : s ≠ s')
    (a a' : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    posOp j hj Q Λ Λc ν₀ s (midPos j s) (midPos_le j s) a *
      posOp j hj Q Λ Λc ν₀ s' (midPos j s') (midPos_le j s') a' = 0 := by
  rw [posOp_apply, posOp_apply, ← op_mul, posStendhal_mul_posStendhal_of_ne (Ne.symm h), op_zero]

variable (j hj Q Λ Λc ν ν₀) in
variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- **The model of `K̃` is the product of the staged modules at `midPos`**:
`L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺} ≅ ∏_s L ⊗_{T̃^{(μ,μ*)}} e_{s, midPos j s} T̃^{λ⁺}` as right
`T̃^{λ⁺}`-modules. -/
def midModelPiEquiv :
    MidModel j hj Q Λ Λc ν ν₀ L ≃ₗ[Tpᵐᵒᵖ]
      ((s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ s (midPos j s) (midPos_le j s) L) :=
  Ind.piEquivOfOrthogonal L midOp_eq_sum_posOp fun _ _ a a' h => posOp_mul_posOp_of_ne h a a'

end Categorification.Stendhal.CupCap
