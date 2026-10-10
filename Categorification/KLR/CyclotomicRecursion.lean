/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicA
import Categorification.KLR.CyclotomicPhi

/-!
# The constant-error dot recursion

The constant-error consequence of Kang–Kashiwara, arXiv:1102.4677v4,
Lemma 5.4: applying the cokernel coordinate `C` to a last dot differs from
multiplication by the polynomial variable by a constant coefficient. This gives
(5.18) and (5.19) for the concrete map `A`, as used in the proof of Lemma 5.5.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "Ri" => KLRAlgebra k Q Si
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "T0" => Rb ⊗[k] Ri

/-- The inclusion of the first `n` strands, regarded as a linear map. -/
noncomputable def cLLinear : Rb →ₗ[k] R where
  toFun := cL Q i β
  map_add' := cL_add i β
  map_smul' := cL_smul i β

/-- Left multipliers preserving the constant coefficient summand after right projection. -/
noncomputable def cLCore : Subalgebra k R where
  carrier := {w | ∃ y : Rb, w * cL Q i β 1 = cL Q i β y}
  mul_mem' := by
    rintro u v ⟨y, hy⟩ ⟨z, hz⟩
    refine ⟨y * z, ?_⟩
    rw [mul_assoc, hz, cL_mul]
    have he : cL Q i β 1 * cL Q i β z = cL Q i β z := by rw [← cL_mul, one_mul]
    rw [← he, ← mul_assoc, hy, he]
  one_mem' := ⟨1, one_mul _⟩
  add_mem' := by
    rintro u v ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by rw [add_mul, hy, hz, cL_add]⟩
  zero_mem' := ⟨0, by rw [zero_mul, cL_zero]⟩
  algebraMap_mem' := by
    intro r
    exact ⟨r • 1, by rw [cL_smul, Algebra.smul_def]⟩

theorem cLCore_mul_cL {w : R} (hw : w ∈ cLCore i β) (y : Rb) :
    ∃ z : Rb, w * cL Q i β y = cL Q i β z := by
  obtain ⟨z, hz⟩ := hw
  refine ⟨z * y, ?_⟩
  have he : cL Q i β 1 * cL Q i β y = cL Q i β y := by rw [← cL_mul, one_mul]
  rw [← he, ← mul_assoc, hz, cL_mul]

theorem e_mem_cLCore (t : Seq (Si + β)) : (e t : R) ∈ cLCore i β := by
  suffices h : e t * cL Q i β 1 ∈ LinearMap.range (cLLinear i β) from
    let ⟨y, hy⟩ := h; ⟨y, hy.symm⟩
  rw [cL_one, Finset.mul_sum]
  apply Submodule.sum_mem
  intro s _
  by_cases ht : t = Seq.cast (add_comm β Si) (s.append default)
  · subst t
    rw [e_mul_self, ← cL_e]
    exact ⟨e s, rfl⟩
  · rw [e_mul_e, ite_eq_right ht]
    exact Submodule.zero_mem _

theorem x_mem_cLCore (b : Fin (Multiset.card β)) :
    (x ⟨b.val, by have := b.2; rw [card_single_add]; omega⟩ : R) ∈ cLCore i β :=
  ⟨x b, (cL_x i β b).symm⟩

theorem ψ_mem_cLCore (j : ℕ) (hj : j + 1 < Multiset.card β) :
    (ψ j : R) ∈ cLCore i β := ⟨ψ j, (cL_ψ i β hj).symm⟩

theorem ψw_mem_cLCore (w : List ℕ) (hw : ∀ j ∈ w, j + 1 < Multiset.card β) :
    (ψw w : R) ∈ cLCore i β := by
  induction w with
  | nil => rw [ψw_nil]; exact Subalgebra.one_mem _
  | cons j w ih =>
    rw [ψw_cons]
    exact Subalgebra.mul_mem _ (ψ_mem_cLCore i β j (hw j (by simp)))
      (ih (fun j hj => hw j (by simp [hj])))

theorem eqIdem_mem_cLCore (j : ℕ) (hj : j + 1 < Multiset.card (Si + β)) :
    (eqIdem j hj : R) ∈ cLCore i β := by
  rw [eqIdem]
  exact Subalgebra.sum_mem _ fun s _ => by
    split_ifs
    · exact e_mem_cLCore i β s
    · exact Subalgebra.zero_mem _

theorem aeval_mem_cLCore (b : Fin (Multiset.card β)) (f : Polynomial k) :
    Polynomial.aeval (x ⟨b.val, by have := b.2; rw [card_single_add]; omega⟩ : R) f ∈
      cLCore i β := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Subalgebra.sum_mem _ fun d _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (x_mem_cLCore i β b) _) _

/-- Multiplying an `F` coordinate by the last dot differs from another `F`
coordinate by an element of `R(β)`, with no last-strand polynomial variable. -/
theorem fT_mul_last_dot (b : Fin (Multiset.card β)) (t : T0) :
    ∃ y : Rb,
      fT Q i β b.val t * x ⟨Multiset.card β, lastPos_lt i β⟩ =
        fT Q i β b.val (t * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩)) + cL Q i β y := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht =>
    obtain ⟨y, hs⟩ := hs
    obtain ⟨z, ht⟩ := ht
    refine ⟨y + z, ?_⟩
    simp only [map_add, add_mul, hs, ht, cL_add]
    abel
  | tmul y c =>
    have hn : 0 < Multiset.card β := by have := b.2; omega
    let xp : R := x ⟨Multiset.card β - 1, penPos_lt i β⟩
    let xl : R := x ⟨Multiset.card β, lastPos_lt i β⟩
    let f := singlePoly Q i c
    let w : R := ψw (upW b.val (Multiset.card β - 1))
    let δ : R := eqIdem (Multiset.card β - 1) (by rw [card_single_add]; omega)
    have hd : xp * ψ (Multiset.card β - 1) = ψ (Multiset.card β - 1) * xl + δ := by
      simpa only [xp, xl, δ, Nat.sub_add_cancel hn] using
        x_mul_ψ_self (Q := Q) (ν := Si + β) (Multiset.card β - 1)
          (by rw [card_single_add]; omega)
    have hc : w * Polynomial.aeval xp f * δ ∈ cLCore i β := by
      apply Subalgebra.mul_mem
      · apply Subalgebra.mul_mem
        · exact ψw_mem_cLCore i β _ (fun j hj => by rw [upW, List.mem_range'_1] at hj; omega)
        · exact aeval_mem_cLCore i β ⟨Multiset.card β - 1, by omega⟩ f
      · exact eqIdem_mem_cLCore i β _ _
    obtain ⟨z, hz⟩ := cLCore_mul_cL i β hc y
    refine ⟨-z, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hneg : cL Q i β (-z) = -cL Q i β z := by
      exact map_neg (cLLinear i β) z
    rw [fT_tmul, fT_tmul, map_mul, singlePoly_x, map_mul, Polynomial.aeval_X, hneg, ← sub_eq_add_neg]
    change (w * Polynomial.aeval xp f * ψ (Multiset.card β - 1) * cL Q i β y) * xl =
      w * (Polynomial.aeval xp f * xp) * ψ (Multiset.card β - 1) * cL Q i β y - cL Q i β z
    rw [← hz]
    have hy := (commute_x_last_cL i β y).eq
    change xl * cL Q i β y = cL Q i β y * xl at hy
    calc
      _ = w * Polynomial.aeval xp f * (ψ (Multiset.card β - 1) * xl) * cL Q i β y := by
        rw [mul_assoc _ _ xl, ← hy]; simp only [mul_assoc]
      _ = _ := by rw [eq_sub_iff_add_eq.mpr hd.symm]; noncomm_ring

theorem kkF_single_zero (b : Fin (Multiset.card β)) (t : T0) :
    kkF i β (Pi.single b t) 0 = fT Q i β b.val t := by
  rw [kkF, map_zero, add_zero, Finset.sum_eq_single b]
  · rw [Pi.single_eq_same]
  · intro c _ hc; rw [Pi.single_eq_of_ne hc, map_zero]
  · simp

theorem cLL_mul_last_dot (t : T0) :
    cLL Q i β (t * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩)) =
      cLL Q i β t * x ⟨Multiset.card β, lastPos_lt i β⟩ := by
  rw [cLL_mul, cLL_one_tmul_x, (commute_x_last_cL i β 1).eq,
    ← mul_assoc, cLL_mul_cL_one]

/-- In the direct-sum coordinates, a last dot advances every `F` coordinate by
one polynomial degree and adds a constant to the complementary coordinate. -/
theorem kkF_mul_last_dot (p : Fin (Multiset.card β) → T0) (q : T0) :
    ∃ y : Rb, kkF i β p q * x ⟨Multiset.card β, lastPos_lt i β⟩ =
      kkF i β (fun b => p b * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩))
        (q * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩) + y ⊗ₜ 1) := by
  choose y hy using fun b => fT_mul_last_dot i β b (p b)
  refine ⟨∑ b, y b, ?_⟩
  simp only [kkF, add_mul, Finset.sum_mul, hy, Finset.sum_add_distrib,
    map_add, cLL_mul_last_dot, cLL_tmul_one]
  have hs : cL Q i β (∑ b, y b) = ∑ b, cL Q i β (y b) := map_sum (cLLinear i β) _ _
  rw [hs]
  abel

variable (a : I → Polynomial k)

theorem thetaL0_one_tmul_x :
    thetaL0 Q i β a (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩) = Polynomial.X := by
  rw [thetaL0_apply, Algebra.TensorProduct.comm_tmul, thetaL, AlgHom.comp_apply,
    theta_tmul, singlePoly_x, Polynomial.aeval_X, map_one, mul_one,
    Polynomial.coe_mapAlgHom, Polynomial.map_X]

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

theorem cPoly_fT (b : Fin (Multiset.card β)) (t : T0) :
    cPoly i β hPQ hP a (fT Q i β b.val t) = 0 := by
  rw [← kkF_single_zero i β b, cPoly_kkF, map_zero]

theorem cPoly_cLL (t : T0) : cPoly i β hPQ hP a (cLL Q i β t) = thetaL0 Q i β a t := by
  rw [← kkF_zero_left i β, cPoly_kkF]

theorem cPoly_cL (y : Rb) :
    cPoly i β hPQ hP a (cL Q i β y) = Polynomial.C (CycKLR.mk k Q a β y) := by
  rw [← cLL_tmul_one, cPoly_cLL, thetaL0_tmul_one]

theorem cPoly_mul_cL_one (r : R) : cPoly i β hPQ hP a (r * cL Q i β 1) = cPoly i β hPQ hP a r := by
  change thetaL0 Q i β a (cCoord i β hPQ hP (r * cL Q i β 1)) = _
  rw [cCoord_mul_cL, ← Algebra.TensorProduct.one_def, mul_one]
  rfl

theorem cPoly_cLL_mul_last_dot (t : T0) :
    cPoly i β hPQ hP a (cLL Q i β t * x ⟨Multiset.card β, lastPos_lt i β⟩) =
      thetaL0 Q i β a t * Polynomial.X := by
  rw [← cLL_mul_last_dot, cPoly_cLL, map_mul, thetaL0_one_tmul_x]

/-- The constant-error recursion for the `C` coordinate. -/
theorem cPoly_mul_last_dot_sub (r : R) :
    ∃ y : Rb, cPoly i β hPQ hP a (r * x ⟨Multiset.card β, lastPos_lt i β⟩) -
      cPoly i β hPQ hP a r * Polynomial.X = Polynomial.C (CycKLR.mk k Q a β y) := by
  obtain ⟨p, q, hpq⟩ := kkF_surj i β hPQ hP r
  choose y hy using fun b => fT_mul_last_dot i β b (p b)
  have hc : cPoly i β hPQ hP a r = thetaL0 Q i β a q := by
    rw [← cPoly_mul_cL_one i β a hPQ hP r, hpq, cPoly_kkF]
  have hd : cPoly i β hPQ hP a (r * x ⟨Multiset.card β, lastPos_lt i β⟩) =
      cPoly i β hPQ hP a (kkF i β p q * x ⟨Multiset.card β, lastPos_lt i β⟩) := by
    rw [← hpq, mul_assoc, ← (commute_x_last_cL i β 1).eq, ← mul_assoc,
      cPoly_mul_cL_one]
  refine ⟨∑ b, y b, ?_⟩
  rw [hc, hd, kkF, add_mul, Finset.sum_mul, map_add, map_sum,
    cPoly_cLL_mul_last_dot, add_sub_cancel_right, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [hy b, map_add, cPoly_fT, zero_add, cPoly_cL]

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hβ : 0 < Multiset.card β)

omit [IsDomain k] in
theorem thetaL_x_tmul_one :
    thetaL Q i β a (x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1) = Polynomial.X := by
  rw [thetaL, AlgHom.comp_apply, theta_tmul, singlePoly_x, Polynomial.aeval_X,
    map_one, mul_one, Polynomial.coe_mapAlgHom, Polynomial.map_X]

omit [IsDomain k] in
theorem concat_mul_first_dot (t : Ri ⊗[k] Rb) :
    concat Q Si β (t * (x ⟨0, by rw [card_single']; omega⟩ ⊗ₜ 1)) =
      concat Q Si β t * x ⟨0, zero_lt_card_single_add i β⟩ := by
  rw [concat_mul, concat_x_tmul_one, posL_single_zero]
  have he : (x ⟨0, zero_lt_card_single_add i β⟩ : R) * oneConcat Q Si β =
      oneConcat Q Si β * x ⟨0, zero_lt_card_single_add i β⟩ := x_mul_eSum _ _
  rw [he, ← mul_assoc, concat_mul_oneConcat]

/-- The last-dot recursion descends through `P` to the polynomial map `A`.
This is KK (5.18), a consequence of the recursion (5.14). -/
theorem aMap_mul_X_sub (s : Polynomial (CycKLR k Q a β)) :
    ∃ y : CycKLR k Q a β,
      aMap i β a h1 hβ hPQ hP (s * Polynomial.X) -
        aMap i β a h1 hβ hPQ hP s * Polynomial.X = Polynomial.C y := by
  obtain ⟨t, rfl⟩ := thetaL_surjective i β a s
  let r : R := ψw (descRun 0 (Multiset.card β)) * concat Q Si β t
  have he : cPoly i β hPQ hP a
      ((r * x ⟨0, zero_lt_card_single_add i β⟩) * tauW a (zero_lt_card_single_add i β) (Multiset.card β)) =
      cPoly i β hPQ hP a
        ((r * tauW a (zero_lt_card_single_add i β) (Multiset.card β)) *
          x ⟨Multiset.card β, lastPos_lt i β⟩) := by
    apply sub_eq_zero.1
    rw [← map_sub]
    apply cPoly_eq_zero i β hPQ hP a hβ
    have hz := Submodule.smul_mem (cycL0 (Q := Q) a (zero_lt_card_single_add i β)) r
      (x_zero_mul_tauW a (zero_lt_card_single_add i β) (Multiset.card β)
        (card_single_add i β).symm)
    simpa only [smul_eq_mul, mul_sub, ← mul_assoc] using hz
  obtain ⟨y, hy⟩ := cPoly_mul_last_dot_sub i β a hPQ hP
    (r * tauW a (zero_lt_card_single_add i β) (Multiset.card β))
  refine ⟨CycKLR.mk k Q a β y, ?_⟩
  rw [← thetaL_x_tmul_one i β a, ← map_mul, aMap_thetaL,
    aMap_thetaL, concat_mul_first_dot, ← mul_assoc]
  rw [thetaL_x_tmul_one]
  exact he ▸ hy

/-- The concrete `A` satisfies the constant-error hypothesis of `CyclotomicPhi`. -/
theorem aMap_mul_X_degree (s : Polynomial (CycKLR k Q a β)) :
    (aMap i β a h1 hβ hPQ hP (s * Polynomial.X) -
      aMap i β a h1 hβ hPQ hP s * Polynomial.X).degree ≤ 0 := by
  obtain ⟨y, hy⟩ := aMap_mul_X_sub i β a hPQ hP h1 hβ s
  rw [hy]
  exact Polynomial.degree_C_le

/-- KK (5.19) for the concrete cyclotomic polynomial map. -/
theorem aMap_mul_sub_degree_lt (m : ℕ) (f : Polynomial (CycKLR k Q a β))
    (hf : f.natDegree ≤ m) (s : Polynomial (CycKLR k Q a β)) :
    (aMap i β a h1 hβ hPQ hP (s * f) - aMap i β a h1 hβ hPQ hP s * f).degree <
      (m : WithBot ℕ) :=
  PhiAlg.degree_sub_mul_lt (aMap i β a h1 hβ hPQ hP).toAddMonoidHom
    (aMap_mul_C i β a h1 hβ hPQ hP) (aMap_mul_X_degree i β a hPQ hP h1 hβ) m f hf s

end Categorification.KLR.KLRAlgebra
