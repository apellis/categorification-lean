/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient
import Categorification.KLR.Filtration
import Categorification.KLR.CyclotomicFinite

/-!
# A braid correction between equal-black crossings

Webster, arXiv:1309.3796v2, relations (4.1a) and (6.20), and proof of Lemma
6.11. The degree-one dot polynomial of a black-red-black braid can survive
between two equal-black crossings. The nilHecke relation contracts the dot
on the crossing pair to one crossing, while the distant dot gives zero.
-/

namespace Categorification.KLR.KLRAlgebra

open KLR

variable {I k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- The equal-colour crossing sandwiches a dot on its left strand to one
crossing. -/
theorem crossing_dot_left_crossing (j : ℕ) (h : j + 1 < m) (s : Seq ν)
    (he : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩) :
    (ψ j * (x ⟨j, by omega⟩ * (ψ j * e s)) : A) = ψ j * e s := by
  have hsq : (ψ j * ψ j * e s : A) = 0 := by rw [ψ_sq j h s, ite_eq_left he]
  have hd := dot_cross_left (Q := Q) j h s
  rw [ite_eq_left he, sub_mul] at hd
  have hz : (ψ j * (ψ j * (x ⟨j + 1, h⟩ * e s)) : A) = 0 := by
    rw [x_mul_e, ← mul_assoc (ψ j), ← mul_assoc, hsq, zero_mul]
  have hh := congrArg (fun a : A => ψ j * a) hd
  simpa only [mul_sub, mul_assoc, hz, sub_zero] using hh

/-- The two dots in the adjacent braid coefficient have different behaviour
when the second dot lies on the left strand of an equal-colour crossing and
the first dot lies away from that crossing. -/
theorem crossing_add_dots_crossing (j : ℕ) (h : j + 1 < m) (a : Fin m) (s : Seq ν)
    (ha : a.val ≠ j) (hb : a.val ≠ j + 1)
    (he : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩) :
    (ψ j * ((x a + x ⟨j, by omega⟩) * (ψ j * e s)) : A) = ψ j * e s := by
  have hsq : (ψ j * ψ j * e s : A) = 0 := by rw [ψ_sq j h s, ite_eq_left he]
  have hd : (ψ j * (x a * (ψ j * e s)) : A) = 0 := by
    rw [← mul_assoc (ψ j) (x a), ← x_mul_ψ a j ha hb, mul_assoc (x a),
      ← mul_assoc (ψ j) (ψ j), hsq, mul_zero]
  rw [add_mul, mul_add, hd, zero_add, crossing_dot_left_crossing j h s he]

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra MvPolynomial TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ

/-- When the red exponent is two, the black–red–black braid coefficient
is the sum of the two outer dots in the affine algebra. -/
theorem affine_braid_black_red_black_two (j : ℕ) (h : j + 2 < m) (s : Seq μ)
    (i : I) (r : Fin ℓ) (hΛ : Λ r i = 2)
    (hi : s.lbl ⟨j, by omega⟩ = .inl i)
    (hr : s.lbl ⟨j + 1, by omega⟩ = .inr r)
    (hi' : s.lbl ⟨j + 2, h⟩ = .inl i) :
    ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e s : A) =
      (x ⟨j, by omega⟩ + x ⟨j + 2, h⟩) * e s := by
  have key := KLRAlgebra.braid (Q := stendhalQ Q Λ) j h s
  have hx : (![x ⟨j, by omega⟩, x ⟨j + 1, by omega⟩, x ⟨j + 2, h⟩] : Fin 3 → A) =
      fun a => x (![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩] a) := by
    funext a
    fin_cases a <;> rfl
  rw [hi, hr, hi'] at key
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self, ↓reduceIte] at key
  rw [stendhalQ_inl_inr, hΛ, StendhalAlgebraAllOrders.qbar_X_zero_pow, hx,
    KLRAlgebra.ncEval_eq_pol] at key
  simpa [Finset.sum_range_succ, add_comm, KLRAlgebra.pol_X] using key

/-- The braid correction at positions two through four contracts the two
equal-black crossings at positions four and five to one crossing. This is the
local calculation in the three-block reversal example. -/
theorem affine_braid_two_between_black_crossings (h : 5 < m) (s : Seq μ)
    (i : I) (r : Fin ℓ) (hΛ : Λ r i = 2)
    (h₂ : s.lbl ⟨2, by omega⟩ = .inl i) (h₃ : s.lbl ⟨3, by omega⟩ = .inr r)
    (h₄ : s.lbl ⟨4, by omega⟩ = .inl i) (h₅ : s.lbl ⟨5, h⟩ = .inl i) :
    (ψ 4 * ((ψ 2 * ψ 3 * ψ 2 - ψ 3 * ψ 2 * ψ 3) * (ψ 4 * e s)) : A) = ψ 4 * e s := by
  let B : A := ψ 2 * ψ 3 * ψ 2 - ψ 3 * ψ 2 * ψ 3
  let P : A := x ⟨2, by omega⟩ + x ⟨4, by omega⟩
  have he : (ψ 4 * e s : A) = e s * ψ 4 := ψ_mul_e_comm 4 h (h₄.trans h₅.symm)
  have hb : B * e s = P * e s :=
    affine_braid_black_red_black_two Q Λ 2 (by omega) s i r hΛ h₂ h₃ h₄
  change ψ 4 * (B * (ψ 4 * e s)) = _
  calc
    _ = ψ 4 * ((B * e s) * ψ 4) := by rw [he, mul_assoc B]
    _ = ψ 4 * (P * (ψ 4 * e s)) := by rw [hb, he, mul_assoc P]
    _ = _ := crossing_add_dots_crossing 4 h ⟨2, by omega⟩ s (by simp) (by simp)
      (h₄.trans h₅.symm)

/-- The exact word difference for the active braid in the three-block
reversal, at red exponent two. The loading immediately below the two equal
black crossings is obtained from the suffix `[1,2,3]`. -/
theorem threeBlockReversal_correction (h : 5 < m) (s : Seq μ)
    (i : I) (r : Fin ℓ) (hΛ : Λ r i = 2)
    (h₂ : (wordProd m [1, 2, 3] • s).lbl ⟨2, by omega⟩ = .inl i)
    (h₃ : (wordProd m [1, 2, 3] • s).lbl ⟨3, by omega⟩ = .inr r)
    (h₄ : (wordProd m [1, 2, 3] • s).lbl ⟨4, by omega⟩ = .inl i)
    (h₅ : (wordProd m [1, 2, 3] • s).lbl ⟨5, h⟩ = .inl i) :
    (ψw [3, 2, 1, 0, 4, 2, 3, 2, 4, 1, 2, 3] * e s : A) -
      ψw [3, 2, 1, 0, 4, 3, 2, 3, 4, 1, 2, 3] * e s =
      ψw [3, 2, 1, 0, 4, 1, 2, 3] * e s := by
  let t := wordProd m [1, 2, 3] • s
  let a : A := ψw [3, 2, 1, 0]
  let b : A := ψw [1, 2, 3] * e s
  have hsupport : e t * b = b := by
    dsimp only [b, t]
    rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  have hlocal := affine_braid_two_between_black_crossings Q Λ h t i r hΛ h₂ h₃ h₄ h₅
  have hframe := congrArg (fun x : A => a * (x * b)) hlocal
  simp only [mul_assoc, hsupport] at hframe
  simpa [a, b, ψw_cons, ψw_nil, mul_sub, sub_mul, mul_assoc] using hframe

namespace BraidedStendhalAlgebra

local notation "raw" => ofKLR k Q Λ ν
local notation "q" => violMk k Q Λ ν

private theorem cut_vanishes (α β : List ℕ) (s : Seq μ)
    (hv : IsViolated (wordProd m β • s)) :
    q (raw (ψw (α ++ β) * e s)) = 0 := by
  have hz : q (raw (e (wordProd m β • s))) = 0 :=
    (violMk_eq_zero_iff _).2 (TwoSidedIdeal.subset_span ⟨_, hv, rfl⟩)
  rw [ψw_append, mul_assoc, ψw_mul_e, map_mul raw, map_mul raw, map_mul q, map_mul q,
    hz, zero_mul, mul_zero]

/-- The residual correction of the exponent-two reversal factors through a
violated loading after one commutation and an exact braid. -/
theorem threeBlockResidual_eq_zero (s : Seq μ) (h : 5 < m)
    (hne : (wordProd m [4, 2, 3] • s).lbl ⟨0, by omega⟩ ≠
      (wordProd m [4, 2, 3] • s).lbl ⟨2, by omega⟩)
    (hv : IsViolated (wordProd m [1, 0, 4, 2, 3] • s)) :
    q (raw (ψw [3, 2, 1, 0, 4, 1, 2, 3] * e s)) = 0 := by
  have far : Commute (ψ 1 : A) (ψ 4) := ψ_mul_ψ 1 4 (by decide)
  have hcomm : (ψw [3, 2, 1, 0, 4, 1, 2, 3] * e s : A) =
      ψw [3, 2, 1, 0, 1, 4, 2, 3] * e s := by
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
    rw [far.symm.left_comm]
  let t := wordProd m [4, 2, 3] • s
  let b : A := ψw [4, 2, 3] * e s
  have hs : e t * b = b := by
    dsimp only [b, t]
    rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  have hb := KLRAlgebra.braid (Q := stendhalQ Q Λ) 0 (by omega) t
  rw [ite_eq_right (fun h => hne h.1), sub_mul, sub_eq_zero] at hb
  have hh := congrArg (fun x : A => ψ 3 * (ψ 2 * (x * b))) hb.symm
  simp only [mul_assoc, hs] at hh
  have he : (ψw [3, 2, 1, 0, 1, 4, 2, 3] * e s : A) =
      ψw [3, 2, 0, 1, 0, 4, 2, 3] * e s := by
    simpa [b, ψw_cons, ψw_nil, mul_assoc] using hh
  rw [hcomm, he]
  exact cut_vanishes Q Λ [3, 2, 0] [1, 0, 4, 2, 3] s hv

end BraidedStendhalAlgebra

end Categorification.Stendhal
