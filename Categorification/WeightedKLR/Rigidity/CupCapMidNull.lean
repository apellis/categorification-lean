/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidDescent
import Categorification.WeightedKLR.Rigidity.CupCapEndNull
import Categorification.WeightedKLR.Rigidity.CupCapLeftDescent

/-!
# Diagrams in which a strand leaves the cap vanish in the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Let `L` be a right `T̃^{(μ,μ*)}`-module
on which the idempotents of the loadings not of the form `μ ⋯ μ*` act by zero. In the model
`L ⊗ e T̃^{λ⁺}` of `K̃^{λ⁺}_λ` with the maximum just before the red strand `λ_{j+1}`
(`CupCap.MidModel`), a diagram in which a strand at the maximum leaves the window at the top
factors through such an idempotent, so it gives zero (`CupCap.exitSpan_midPos_mem_nullIdeal`).

## Main results

* `CupCap.commute_midStendhal_one_midBot`: the unit of the maximum commutes with its diagrams.
* `CupCap.midStendhal_one_eq_midBot`: the unit is the red-ordered idempotent at the maximum.
* `CupCap.midGen`: the elements `e · Z` of the corner of the maximum.
* `CupCap.midBot_mul_botMap_eSum`: a diagram at the maximum below the cap generators at `s`.
* `CupCap.exitSpan_midPos_mem_nullIdeal`: the exit diagrams lie in the null ideal of the model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀

theorem midBot_eq_allOrdersLift (x : Rc) :
    midBot j hj Q Λ Λc ν ν₀ x =
      allOrdersLift redRelations_midBot (StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x) :=
  (allOrdersLift_ofKLR _ x).symm

/-- **The unit of the maximum commutes with its diagrams**: red strands do not cross, so every
diagram preserves the order of the red strands. -/
theorem commute_midStendhal_one_midBot (x : Rc) : Commute (σ 1) (midBot j hj Q Λ Λc ν ν₀ x) := by
  have h1 : σ 1 = allOrdersLift (redRelations_midBot (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) (ν₀ := ν₀)) (StendhalAlgebraAllOrders.redOrderedIdem k Q Λc ν₀) := rfl
  rw [Commute, SemiconjBy, h1, midBot_eq_allOrdersLift, ← map_mul, ← map_mul,
    (redOrderedIdem_commute Q Λc ν₀ _).eq]

theorem midStendhal_cupMap' (x : Rc) :
    σ (cupMap k Q Λc ν₀ x) = σ 1 * midBot j hj Q Λ Λc ν ν₀ x := by
  rw [midStendhal_cupMap, (commute_midStendhal_one_midBot x).eq]

/-- The unit of the maximum is the red-ordered idempotent of `T̃^{(μ,μ*)}` placed at the
maximum. -/
theorem midStendhal_one_eq_midBot :
    σ 1 = midBot j hj Q Λ Λc ν ν₀ (redOrderedKLR k Q Λc ν₀) := by
  have h1 : σ 1 = allOrdersLift (redRelations_midBot (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) (ν₀ := ν₀)) (StendhalAlgebraAllOrders.redOrderedIdem k Q Λc ν₀) := rfl
  rw [h1, midBot_eq_allOrdersLift, ofKLR_redOrderedKLR]

theorem midMapKLR_mul_insertMap (s : Seq (stendhalWeight ℓ ν)) (x y : Rc) :
    midMapKLR j hj Q Λ Λc ν ν₀ x * ι s (midPos j s) (midPos_le j s) y =
      ι s (midPos j s) (midPos_le j s) (x * y) := by
  rw [midMapKLR, Finset.sum_mul, Finset.sum_eq_single s
    (fun s' _ h => insertMap_midPos_mul_of_ne h x y) (by simp), insertMap_mul]

theorem insertMap_mul_midMapKLR (s : Seq (stendhalWeight ℓ ν)) (x y : Rc) :
    ι s (midPos j s) (midPos_le j s) x * midMapKLR j hj Q Λ Λc ν ν₀ y =
      ι s (midPos j s) (midPos_le j s) (x * y) := by
  rw [midMapKLR, Finset.mul_sum, Finset.sum_eq_single s
    (fun s' _ h => insertMap_midPos_mul_of_ne (Ne.symm h) x y) (by simp), insertMap_mul]

/-- A diagram at the maximum below the cap generators at `s` is the diagram at the maximum cut by
`E_s`. -/
theorem midBot_mul_botMap_eSum (s : Seq (stendhalWeight ℓ ν)) (x : Rc) :
    midBot j hj Q Λ Λc ν ν₀ x * bot (E s) = bot (ι s (midPos j s) (midPos_le j s) x) := by
  rw [midBot_apply, ← map_mul, ← insertMap_one Q Λ Λc s (midPos_le j s), midMapKLR_mul_insertMap,
    mul_one]

/-- The sum of the window idempotents is the diagram `1` at the maximum. -/
theorem midMapKLR_one :
    midMapKLR j hj Q Λ Λc ν ν₀ 1 = ∑ s : Seq (stendhalWeight ℓ ν), E s := by
  rw [midMapKLR]
  exact Finset.sum_congr rfl fun s _ => insertMap_one Q Λ Λc s (midPos_le j s)

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

variable (j hj Q Λ Λc ν ν₀) in
/-- An element `e · Z` of the corner of the maximum at `midPos`. -/
def midGen (Z : Tp) : Corner (midOp j hj Q Λ Λc ν ν₀) :=
  ⟨op (σ 1 * Z), by
    change op (σ 1 * Z) * midOp j hj Q Λ Λc ν ν₀ 1 = _
    rw [midOp_apply, ← op_mul, unop_one, ← mul_assoc, ← map_mul, one_mul]⟩

theorem midGen_val (Z : Tp) : (midGen j hj Q Λ Λc ν ν₀ Z).1 = op (σ 1 * Z) := rfl

theorem op_smul_midGen (b Z : Tp) :
    (op b : Tpᵐᵒᵖ) • midGen j hj Q Λ Λc ν ν₀ Z = midGen j hj Q Λ Λc ν ν₀ (Z * b) :=
  Subtype.ext (by
    change op b * op _ = op _
    rw [← op_mul, mul_assoc])

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **Diagrams in which a strand leaves the window at `midPos s` at the top vanish in the
model.** -/
theorem exitSpan_midPos_mem_nullIdeal
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (s : Seq (stendhalWeight ℓ ν)) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s)) :
    op (σ 1 * bot y) ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    have h : σ 1 * bot (ι s (midPos j s) (midPos_le j s) z * r) =
        σ (cupMap k Q Λc ν₀ z) * bot (E s * r) := by
      rw [midStendhal_cupMap', map_mul, map_mul, ← midBot_mul_botMap_eSum]
      simp only [mul_assoc]
    rw [h, op_mul]
    exact mul_map_mem_nullIdeal _ (b := op (cupMap k Q Λc ν₀ z))
      (smul_eq_zero_of_mem_capNull hL hz)
  | zero => rw [map_zero, mul_zero, op_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [map_add, mul_add, op_add]; exact add_mem h h'
  | smul c y _ h =>
    rw [map_smul, mul_smul_comm, op_smul]
    exact Submodule.smul_of_tower_mem _ c h

end Categorification.Stendhal.CupCap
