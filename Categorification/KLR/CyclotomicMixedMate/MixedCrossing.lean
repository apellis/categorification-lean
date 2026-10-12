/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicInductionCalculus
import Categorification.KLR.CyclotomicMixedInversionDescent

/-!
# The signed two-colour crossing

The actual crossing has sign `tau = -psi`, intertwines both lower inclusions, and
satisfies both support cuts. It supplies the crossing in the ordinary mixed mate.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedCrossing
open TypeA MulOpposite
variable {I : Type*} {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (γ : Multiset I) (i j : I)

theorem square : ({j} : Multiset I) + ({i} + γ) = {i} + ({j} + γ) := add_left_comm _ _ _

def doubleSeq (s : Seq γ) : Seq (({i} : Multiset I) + ({j} + γ)) :=
  Seq.cast (add_comm ({j} + γ) {i})
    ((Seq.cast (add_comm γ {j}) (s.append default)).append default)

theorem doubleSeq_apply_lt (s : Seq γ)
    (b : Fin (Multiset.card (({i} : Multiset I) + ({j} + γ)))) (hb : b.val < Multiset.card γ) :
    (doubleSeq γ i j s).1 b = s.1 ⟨b.val, hb⟩ := by
  simp only [doubleSeq, Seq.cast_apply]
  rw [Seq.append_apply_lt _ _ _ (by
    change b.val < Multiset.card ({j} + γ)
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega), Seq.cast_apply,
    Seq.append_apply_lt _ _ _ (by exact hb)]
  rfl

theorem doubleSeq_apply_mid (s : Seq γ)
    (b : Fin (Multiset.card (({i} : Multiset I) + ({j} + γ)))) (hb : b.val = Multiset.card γ) :
    (doubleSeq γ i j s).1 b = j := by
  simp only [doubleSeq, Seq.cast_apply]
  rw [Seq.append_apply_lt _ _ _ (by
    change b.val < Multiset.card ({j} + γ)
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega), Seq.cast_apply,
    Seq.append_apply_ge _ _ _ (by change Multiset.card γ ≤ b.val; omega)]
  exact Multiset.mem_singleton.1 (Seq.mem _ _)

theorem doubleSeq_apply_last (s : Seq γ)
    (b : Fin (Multiset.card (({i} : Multiset I) + ({j} + γ)))) (hb : b.val = Multiset.card γ + 1) :
    (doubleSeq γ i j s).1 b = i := by
  simp only [doubleSeq, Seq.cast_apply]
  rw [Seq.append_apply_ge _ _ _ (by
    change Multiset.card ({j} + γ) ≤ b.val
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega)]
  exact Multiset.mem_singleton.1 (Seq.mem _ _)

theorem doubleSeq_swap (s : Seq γ) :
    sadj (Multiset.card (({i} : Multiset I) + ({j} + γ))) (Multiset.card γ) • doubleSeq γ i j s =
      Seq.cast (square γ i j) (doubleSeq γ j i s) := by
  apply Subtype.ext
  funext b
  rw [sadj_smul_apply, Seq.cast_apply]
  have hv := sadj_apply_val (n := Multiset.card (({i} : Multiset I) + ({j} + γ)))
    (j := Multiset.card γ) (by simp) b
  by_cases hb : b.val < Multiset.card γ
  · have hs : (sadj _ (Multiset.card γ) b).val = b.val := by
      simpa only [ite_eq_right (show b.val ≠ Multiset.card γ by omega),
        ite_eq_right (show b.val ≠ Multiset.card γ + 1 by omega)] using hv
    rw [doubleSeq_apply_lt _ _ _ _ _ (by omega), doubleSeq_apply_lt γ j i s _ hb]
    exact congrArg s.1 (Fin.ext hs)
  · have hb' := b.isLt
    simp only [Multiset.card_add, Multiset.card_singleton] at hb'
    have hc : b.val = Multiset.card γ ∨ b.val = Multiset.card γ + 1 := by omega
    rcases hc with hc | hc
    · rw [doubleSeq_apply_last _ _ _ _ _ (by
          simpa only [hc, ite_true] using hv),
        doubleSeq_apply_mid γ j i s _ hc]
    · rw [doubleSeq_apply_mid _ _ _ _ _ (by
          simpa only [hc, ite_eq_right (Nat.succ_ne_self _), ite_true] using hv),
        doubleSeq_apply_last γ j i s _ hc]

variable [DecidableEq I]

theorem doubleLast_e_intertwine (s : Seq γ) :
    cL Q i ({j} + γ) (cL Q j γ (e s)) * ψ (Multiset.card γ) =
      (ψ (Multiset.card γ) : KLRAlgebra k Q ({i} + ({j} + γ))) *
        castKLR Q (square γ i j) (cL Q j ({i} + γ) (cL Q i γ (e s))) := by
  rw [cL_e, cL_e, cL_e, cL_e, castKLR_e, e_mul_ψ]
  exact congrArg (fun s => (ψ (Multiset.card γ) : KLRAlgebra k Q ({i} + ({j} + γ))) * e s)
    (doubleSeq_swap γ i j s)

def doubleLast : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q ({i} + ({j} + γ)) where
  toFun r := cL Q i ({j} + γ) (cL Q j γ r)
  map_zero' := by rw [cL_zero, cL_zero]
  map_add' r s := by rw [cL_add, cL_add]
  map_mul' r s := by rw [cL_mul, cL_mul]
  map_smul' c r := by rw [cL_smul, cL_smul]; rfl

theorem doubleLast_x (b : Fin (Multiset.card γ)) :
    doubleLast Q γ i j (x b) =
      x ⟨b.val, by simp; omega⟩ * doubleLast Q γ i j 1 := by
  change cL Q i ({j} + γ) (cL Q j γ (x b)) = _
  rw [cL_x, cL_mul, cL_x, mul_assoc, ← cL_mul, one_mul]
  rfl

theorem doubleLast_psi (b : ℕ) (hb : b + 1 < Multiset.card γ) :
    doubleLast Q γ i j (ψ b) = ψ b * doubleLast Q γ i j 1 := by
  change cL Q i ({j} + γ) (cL Q j γ (ψ b)) = _
  rw [cL_ψ j γ hb, cL_mul, cL_ψ i ({j} + γ) (by simp; omega),
    mul_assoc, ← cL_mul, one_mul]
  rfl

theorem doubleLast_one_intertwine :
    doubleLast Q γ i j 1 * ψ (Multiset.card γ) =
      ψ (Multiset.card γ) * castKLR Q (square γ i j) (doubleLast Q γ j i 1) := by
  rw [← sum_e (k := k) (Q := Q) (ν := γ)]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ => doubleLast_e_intertwine Q γ i j s)

/-- The two-colour lower actions are intertwined, not commuted. -/
theorem doubleLast_intertwine (r : KLRAlgebra k Q γ) :
    doubleLast Q γ i j r * ψ (Multiset.card γ) =
      ψ (Multiset.card γ) * castKLR Q (square γ i j) (doubleLast Q γ j i r) := by
  induction r using klr_induction with
  | hadd r s hr hs => simp only [map_add, add_mul, mul_add, hr, hs]
  | hmul r s hr hs =>
    simp only [map_mul]
    rw [mul_assoc, hs, ← mul_assoc, hr, mul_assoc]
  | hr c =>
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [map_smul, smul_mul_assoc, mul_smul_comm, doubleLast_one_intertwine]
  | he s => exact doubleLast_e_intertwine Q γ i j s
  | hx b =>
    rw [doubleLast_x, doubleLast_x, map_mul, castKLR_x]
    have hc : Commute (x (k := k) (Q := Q) (ν := {i} + ({j} + γ))
      ⟨b.val, by simp; omega⟩) (ψ (Multiset.card γ)) :=
      x_mul_ψ _ _ (by change b.val ≠ Multiset.card γ; omega)
        (by change b.val ≠ Multiset.card γ + 1; omega)
    rw [mul_assoc, doubleLast_one_intertwine, ← mul_assoc, hc.eq, mul_assoc]
    rfl
  | hψ b =>
    by_cases hb : b + 1 < Multiset.card γ
    · rw [doubleLast_psi Q γ i j b hb, doubleLast_psi Q γ j i b hb,
        map_mul, castKLR_ψ]
      rw [mul_assoc, doubleLast_one_intertwine, ← mul_assoc,
        (ψ_mul_ψ (Q := Q) b (Multiset.card γ) (by omega)), mul_assoc]
    · rw [ψ_eq_zero b (by omega), map_zero, map_zero, map_zero, zero_mul, mul_zero]

/-- The original signed two-colour crossing coefficient with its target cut. -/
def crossingElement : KLRAlgebra k Q ({i} + ({j} + γ)) :=
  -ψ (Multiset.card γ) * castKLR Q (square γ i j) (doubleLast Q γ j i 1)

theorem crossingElement_right :
    crossingElement Q γ i j * castKLR Q (square γ i j) (doubleLast Q γ j i 1) =
      crossingElement Q γ i j := by
  rw [crossingElement, mul_assoc, ← map_mul, ← map_mul, one_mul]

theorem crossingElement_intertwine (r : KLRAlgebra k Q γ) :
    doubleLast Q γ i j r * crossingElement Q γ i j =
      crossingElement Q γ i j * castKLR Q (square γ i j) (doubleLast Q γ j i r) := by
  rw [crossingElement]
  simp only [mul_neg, neg_mul]
  congr 1
  calc
    _ = (doubleLast Q γ i j r * ψ (Multiset.card γ)) *
        castKLR Q (square γ i j) (doubleLast Q γ j i 1) := (mul_assoc _ _ _).symm
    _ = _ := by
      rw [doubleLast_intertwine, mul_assoc, ← map_mul, ← map_mul, mul_one,
        mul_assoc, ← map_mul, ← map_mul, one_mul]

theorem crossingElement_left :
    doubleLast Q γ i j 1 * crossingElement Q γ i j = crossingElement Q γ i j := by
  rw [crossingElement_intertwine, crossingElement_right]

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedCrossing
