/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicBLeading

/-!
# The coefficient of the intertwiner product

The actual value of the `ψ`-normalized map `B` on the product of intertwiners,
as used before Kang–Kashiwara, arXiv:1102.4677v4, (5.15).
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}
  (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Ri" => KLRAlgebra k Q Si
local notation "Rb" => KLRAlgebra k Q β
local notation "T" => Ri ⊗[k] Rb
local notation "R" => KLRAlgebra k Q (Si + β)

/-- The tensor coefficient of the longest first-strand word, before the quotient. -/
noncomputable def gLeadTensor : (n : ℕ) → n ≤ Multiset.card β → Seq β → T
  | 0, _, s => 1 ⊗ₜ e s
  | n + 1, hn, s =>
    (if s.1 ⟨n, by omega⟩ = i then
      (x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1 - 1 ⊗ₜ x ⟨n, by omega⟩) ^ 2 else 1) *
      gLeadTensor n (by omega) s

theorem concat_diff_mul (b : Fin (Multiset.card β)) (t : T) :
    concat Q Si β ((x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1 - 1 ⊗ₜ x b) * t) =
      (x ⟨0, zero_lt_card_single_add i β⟩ - x (Seq.posR Si b)) * concat Q Si β t := by
  rw [concat_mul, map_sub, concat_x_tmul_one, concat_one_tmul_x, ← sub_mul,
    mul_assoc, oneConcat_mul_concat]
  rfl

theorem concat_diff_sq_mul (b : Fin (Multiset.card β)) (t : T) :
    concat Q Si β ((x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1 - 1 ⊗ₜ x b) ^ 2 * t) =
      (x ⟨0, zero_lt_card_single_add i β⟩ - x (Seq.posR Si b)) ^ 2 * concat Q Si β t := by
  rw [pow_two, mul_assoc, concat_diff_mul, concat_diff_mul, ← mul_assoc, ← pow_two]

/-- The tensor coefficient is the polynomial leading coefficient of the intertwiner. -/
theorem concat_gLeadTensor (n : ℕ) (hn : n ≤ Multiset.card β) (s : Seq β) :
    concat Q Si β (gLeadTensor i β n hn s) =
      pol (gLead n (by have := card_single_add i β; omega) (cons1 i β s)) * e (cons1 i β s) := by
  induction n with
  | zero =>
    rw [gLeadTensor, gLead, map_one, one_mul]
    exact cR_e i β s
  | succ n ih =>
    rw [gLeadTensor, gLead, cons1_succ, cons1_zero]
    split_ifs with hs
    · rw [concat_diff_sq_mul, ih (by omega), map_mul, map_pow, map_sub, pol_X, pol_X]
      have hp : Seq.posR Si (⟨n, by omega⟩ : Fin (Multiset.card β)) =
          (⟨n + 1, by have := card_single_add i β; omega⟩ : Fin (Multiset.card (Si + β))) := by
        apply Fin.ext
        simp only [Seq.posR_val, card_single', Nat.add_comm]
      rw [hp, mul_assoc]
    · rw [one_mul, one_mul, ih (by omega)]

variable (a : I → Polynomial k)
local notation "Rl" => CycKLR k Q a β

/-- The coefficient as a cyclotomic polynomial: one squared dot difference for each
occurrence of the selected colour. -/
noncomputable def gLeadPoly : (n : ℕ) → n ≤ Multiset.card β → Seq β → Polynomial Rl
  | 0, _, s => Polynomial.C (CycKLR.mk k Q a β (e s))
  | n + 1, hn, s =>
    (if s.1 ⟨n, by omega⟩ = i then
      (Polynomial.X - Polynomial.C (CycKLR.mk k Q a β (x ⟨n, by omega⟩))) ^ 2 else 1) *
      gLeadPoly n (by omega) s

theorem thetaL_gLeadTensor (n : ℕ) (hn : n ≤ Multiset.card β) (s : Seq β) :
    thetaL Q i β a (gLeadTensor i β n hn s) = gLeadPoly i β a n hn s := by
  induction n with
  | zero => rw [gLeadTensor, gLeadPoly, thetaL_one_tmul]
  | succ n ih =>
    rw [gLeadTensor, gLeadPoly, map_mul, ih (by omega)]
    split_ifs with hs
    · rw [map_pow, map_sub, thetaL_x_tmul_one, thetaL_one_tmul]
    · rw [map_one]

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hβ : 0 < Multiset.card β)

include hβ in
theorem bCoord_gProd_cons1 (s : Seq β) :
    bCoord i β hPQ hP (gProd (Multiset.card β) * e (cons1 i β s)) =
      gLeadTensor i β (Multiset.card β) le_rfl s := by
  rw [bCoord_gProd i β hPQ hP hβ, mul_assoc, ← concat_gLeadTensor i β, bCoord_top]

/-- The actual map `B` evaluates the intertwiner product to the squared-difference polynomial. -/
theorem bMap_gProd_cons1 (s : Seq β) :
    bMap i β hPQ hP a h1 hβ (Submodule.Quotient.mk
      (gProd (Multiset.card β) * e (cons1 i β s))) =
      gLeadPoly i β a (Multiset.card β) le_rfl s := by
  rw [bMap_mk]
  change thetaL Q i β a (bCoord i β hPQ hP _) = _
  rw [bCoord_gProd_cons1 i β hPQ hP hβ, thetaL_gLeadTensor]

/-- The first dot acts as the polynomial variable under the final-coordinate map. -/
theorem bCoord_mul_first_dot (r : R) :
    bCoord i β hPQ hP (r * x ⟨0, zero_lt_card_single_add i β⟩) =
      bCoord i β hPQ hP r * (x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1) := by
  calc
    _ = bCoord i β hPQ hP ((r * x ⟨0, zero_lt_card_single_add i β⟩) * oneConcat Q Si β) :=
      (bCoord_mul_oneConcat i β hPQ hP _).symm
    _ = bCoord i β hPQ hP (r * concat Q Si β
        (x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1)) := by
      rw [concat_x_tmul_one, posL_single_zero, mul_assoc]
    _ = _ := bCoord_mul_concat i β hPQ hP _ _

theorem bCoord_mul_first_dot_pow (r : R) (m : ℕ) :
    bCoord i β hPQ hP (r * x ⟨0, zero_lt_card_single_add i β⟩ ^ m) =
      bCoord i β hPQ hP r * (x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, mul_one]
  | succ m ih => rw [pow_succ, ← mul_assoc, bCoord_mul_first_dot, ih, mul_assoc, ← pow_succ]

/-- The dotted intertwiner has coefficient `S_s X^m`. Since `X` is central, this
is also `X^m S_s`, the summand used before (5.15). -/
theorem bMap_gProd_cons1_mul_first_dot_pow (s : Seq β) (m : ℕ) :
    bMap i β hPQ hP a h1 hβ (Submodule.Quotient.mk
      (gProd (Multiset.card β) * e (cons1 i β s) *
        x ⟨0, zero_lt_card_single_add i β⟩ ^ m)) =
      gLeadPoly i β a (Multiset.card β) le_rfl s * Polynomial.X ^ m := by
  rw [bMap_mk]
  change thetaL Q i β a (bCoord i β hPQ hP _) = _
  rw [bCoord_mul_first_dot_pow, bCoord_gProd_cons1 i β hPQ hP hβ, map_mul,
    map_pow, thetaL_x_tmul_one, thetaL_gLeadTensor]

end Categorification.KLR.KLRAlgebra
