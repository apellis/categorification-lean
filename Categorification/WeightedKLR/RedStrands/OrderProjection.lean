/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedOrder
import Categorification.KLR.Prop213
import Categorification.KLR.CyclotomicSplit
import Categorification.KLR.DividedPowerIdempotents

/-!
# Projection onto a red order

In Webster's Stendhal diagram presentation, a crossing of two red strands
vanishes. Every nonzero diagram therefore preserves the ordering of its red
boundary labels. Cutting by the idempotent of the prescribed order is a
surjective algebra homomorphism.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR StendhalAlgebraAllOrders
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "E" => redOrderedIdem k Q Λ ν
local notation "π" => ofKLR k Q Λ ν

private theorem commute_cross (j : ℕ) : Commute E (ψ j) := by
  classical
  by_cases hj : j+1 < m
  · have he : (∑ s : Seq μ, e s : A) = 1 := by simp only [e, ← map_sum, KLRAlgebra.sum_e, map_one]
    change E * ψ j = ψ j * E
    rw [← mul_one (E * ψ j), ← mul_one (ψ j * E), ← he, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    let t := TypeA.sadj m j • s
    have hc : (ψ j * e s : A) = e t * ψ j := by
      exact (map_mul π _ _).symm.trans ((congrArg π (KLRAlgebra.ψ_mul_e j s)).trans (map_mul π _ _))
    rw [mul_assoc, mul_assoc, hc, ← mul_assoc E, redOrderedIdem_mul_e, redOrderedIdem_mul_e]
    by_cases hb : (s.lbl ⟨j, by omega⟩).isLeft ∨ (s.lbl ⟨j+1, hj⟩).isLeft
    · have ht : IsRedOrdered t ↔ IsRedOrdered s := by
        refine ⟨fun ht => ?_, fun hs => isRedOrdered_sadj hs hj hb⟩
        have hbt : (t.lbl ⟨j, by omega⟩).isLeft ∨ (t.lbl ⟨j+1, hj⟩).isLeft := by
          simpa only [t, KLRAlgebra.lbl_sadj_left hj, KLRAlgebra.lbl_sadj_right hj, or_comm] using hb
        simpa only [t, KLRAlgebra.sadj_smul_smul] using isRedOrdered_sadj ht hj hbt
      rw [if_congr ht rfl rfl]
      split_ifs <;> simp [hc]
    · push Not at hb
      have hz : (ψ j * e s : A) = 0 := ψ_mul_e_of_red j hj s
        (by cases ha : s.lbl ⟨j, by omega⟩ <;> simp_all)
        (by cases ha : s.lbl ⟨j+1, hj⟩ <;> simp_all)
      split_ifs <;> simp [← hc, hz]
  · change Commute E (π (KLRAlgebra.ψ j))
    rw [KLRAlgebra.ψ_eq_zero j (by omega), map_zero]
    exact Commute.zero_right _

/-- The idempotent selecting the prescribed red order is central. -/
theorem redOrderedIdem_commute (z : A) : Commute E z := by
  classical
  obtain ⟨a, rfl⟩ := ofKLR_surjective z
  induction a using KLRAlgebra.klr_induction with
  | hr c => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right _ _
  | he s => exact (redOrderedIdem_mul_e s).trans (e_mul_redOrderedIdem s).symm
  | hx a =>
    rw [redOrderedIdem]
    apply Commute.sum_left
    intro s _
    exact (Commute.map (show Commute (KLRAlgebra.x a) (KLRAlgebra.e s) from
      KLRAlgebra.x_mul_e a s) π).symm
  | hψ j => exact commute_cross Q Λ ν j
  | hadd a b ha hb => simpa only [map_add] using ha.add_right hb
  | hmul a b ha hb => simpa only [map_mul] using ha.mul_right hb

/-- Projection from all orders of red strands onto Webster's ordered algebra. -/
def orderProjection : A →ₐ[k] StendhalAlgebra k Q Λ ν where
  toFun x := ⟨x * E, x, by
    change E * x * E = x * E
    rw [(redOrderedIdem_commute Q Λ ν x).eq, mul_assoc,
                              isIdempotentElem_redOrderedIdem.eq]⟩
  map_one' := Subtype.ext (one_mul _)
  map_mul' x y := Subtype.ext (by change x * y * E = x * E * (y * E)
                                  rw [mul_assoc x E, ← mul_assoc E, (redOrderedIdem_commute Q Λ ν y).eq,
                                    mul_assoc y, isIdempotentElem_redOrderedIdem.eq, mul_assoc])
  map_zero' := Subtype.ext (zero_mul _)
  map_add' x y := Subtype.ext (add_mul x y E)
  commutes' c := Subtype.ext (by change algebraMap k A c * E = c • E
                                 rw [Algebra.smul_def])

theorem orderProjection_surjective : Function.Surjective (orderProjection Q Λ ν) := by
  intro x
  exact ⟨x.val, Subtype.ext ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).mp x.2).2⟩

end Categorification.Stendhal
