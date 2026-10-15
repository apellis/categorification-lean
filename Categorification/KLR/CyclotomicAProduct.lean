/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicPQ
import Categorification.KLR.CyclotomicAB
import Categorification.KLR.CyclotomicSCentral

/-!
# Product identities for the actual cyclotomic map A

The polynomial identities of Kang–Kashiwara, arXiv:1102.4677v4,
(5.15)–(5.16), obtained from `AB = CP` and the reversed product on `K₀`.
-/

namespace Categorification.KLR.KLRAlgebra
open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rb" => KLRAlgebra k Q β
local notation "Ri" => KLRAlgebra k Q Si
local notation "T" => Ri ⊗[k] Rb
local notation "T0" => Rb ⊗[k] Ri

/-- Rotating polynomial tensor coefficients from the first to the last strand. -/
theorem cLL_comm_cOf (F : MvPolynomial (Fin (Multiset.card (Si + β))) k) :
    cLL Q i β (Algebra.TensorProduct.comm k Ri Rb (cOf Q i β F)) =
      pol (rename (cP (Multiset.card (Si + β)) (Multiset.card β)) F) * cL Q i β 1 := by
  have h0 := zero_lt_card_single_add i β
  have hn := (card_single_add i β).symm
  induction F using MvPolynomial.induction_on with
  | C c =>
    have hC : cOf Q i β (MvPolynomial.C c) = (1 : Ri) ⊗ₜ (algebraMap k Rb c) := by
      unfold cOf
      rw [MvPolynomial.algHom_C, Polynomial.algebraMap_apply, Polynomial.map_C,
        ← Polynomial.monomial_zero_left, thetaInv_monomial, pow_zero, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C]
    rw [hC, Algebra.TensorProduct.comm_tmul, cLL_tmul_one, Algebra.algebraMap_eq_smul_one,
      cL_smul, rename_C, algHom_C, Algebra.smul_def]
  | add F G hF hG =>
    unfold cOf at hF hG ⊢
    rw [map_add, Polynomial.map_add, map_add, map_add, map_add, hF, hG,
      map_add, map_add, add_mul]
  | mul_X F b hF =>
    rw [cOf_mul, map_mul, cLL_mul, hF, map_mul, map_mul, rename_X, pol_X]
    rw [mul_assoc, cL_one_mul_cLL]
    obtain ⟨b, hb⟩ := b
    rcases b with _ | b
    · unfold cOf
      rw [fSplit_X_zero i β h0, Polynomial.map_X, ← Polynomial.monomial_one_one_eq_X,
        thetaInv_monomial, pow_one, Algebra.TensorProduct.comm_tmul, cLL_one_tmul_x,
        cP_apply_zero _ hn h0, mul_assoc]
    · unfold cOf
      rw [fSplit_X_succ i β b hb, Polynomial.map_C, ← Polynomial.monomial_zero_left,
        thetaInv_monomial, pow_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pol_X,
        Algebra.TensorProduct.comm_tmul, cLL_tmul_one, cL_x,
        cP_apply_pos _ hn (b + 1) (by omega) (by rw [card_single_add] at hb; omega), mul_assoc]
      rfl

variable (a : I → Polynomial k)

/-- The reversed-product multiplier is the existing tensor polynomial `aPrime`, rotated. -/
theorem bElt_mul_cL_one :
    (bElt a (zero_lt_card_single_add i β) (Multiset.card β) * cL Q i β 1 : R) =
      cLL Q i β (Algebra.TensorProduct.comm k Ri Rb (aPrime Q i β a)) := by
  rw [cL_one, Finset.mul_sum, aPrime, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_mul, cLL_mul, cLL_comm_cOf, Algebra.TensorProduct.comm_tmul, cLL_tmul_one,
    mul_assoc, ← cL_mul, one_mul, cL_e]
  rw [bElt, Finset.sum_mul, Finset.sum_eq_single (cons1 i β s)]
  · rw [cP_smul_cons1, mul_assoc, e_mul_self]
    rfl
  · intro t _ ht
    rw [mul_assoc, e_mul_e, ite_eq_right, mul_zero]
    intro he
    apply ht
    have he' : cP (Multiset.card (Si + β)) (Multiset.card β) • t =
        cP (Multiset.card (Si + β)) (Multiset.card β) • cons1 i β s := by
      rw [cP_smul_cons1]; exact he
    exact (MulAction.injective _ he')
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cLL_mul_last_dot_pow (t : T0) (d : ℕ) :
    cLL Q i β t * (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) ^ d =
      cLL Q i β (t * (1 ⊗ₜ ((x ⟨0, by rw [card_single']; omega⟩ : Ri) ^ d))) := by
  induction d with
  | zero => rw [pow_zero, pow_zero, mul_one, ← Algebra.TensorProduct.one_def, mul_one]
  | succ d ih =>
    rw [pow_succ, ← mul_assoc, ih, ← cLL_mul_last_dot]
    congr 1
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_succ]

variable (hsym : KLRSymm Q)
  (hβ : 0 < Multiset.card β)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)

include hβ hQ ha in
/-- The dotted intertwiner yields the actual product polynomial after applying `CP`. -/
theorem cPoly_gProd_first_dot_tauW (d : ℕ) :
    cPoly i β hsym a ((gProd (Multiset.card β) * oneConcat Q Si β *
      (x ⟨0, zero_lt_card_single_add i β⟩ : R) ^ d) *
        tauW a (zero_lt_card_single_add i β) (Multiset.card β)) =
      thetaL Q i β a (aPrime Q i β a) * Polynomial.X ^ d := by
  let h0 := zero_lt_card_single_add i β
  have hn := (card_single_add i β).symm
  have hx := pol_mul_tauW (Q := Q) a h0 (Multiset.card β) hn (X ⟨0, h0⟩ ^ d)
  rw [map_pow, pol_X, map_pow, rename_X, cP_apply_zero _ hn h0, map_pow, pol_X] at hx
  have hz := cPoly_eq_zero i β hsym a hβ
    (Submodule.smul_mem _ (gProd (Multiset.card β) * oneConcat Q Si β : R) hx)
  change cPoly i β hsym a
    ((gProd (Multiset.card β) * oneConcat Q Si β) *
      (x ⟨0, h0⟩ ^ d * tauW a h0 (Multiset.card β) -
        tauW a h0 (Multiset.card β) * x ⟨Multiset.card β, lastPos_lt i β⟩ ^ d)) = 0 at hz
  rw [mul_sub, map_sub, sub_eq_zero] at hz
  have hd := mul_mem_cycL0 a (reverse_defect_cut_mem a hsym i β hβ hQ ha)
    (Subalgebra.pow_mem _ (x_mem_subR0 ⟨Multiset.card β, lastPos_lt i β⟩) d)
  have hz' := cPoly_eq_zero i β hsym a hβ hd
  rw [sub_mul, sub_mul, map_sub, sub_eq_zero] at hz'
  rw [mul_assoc, hz, ← mul_assoc, mul_assoc (gProd (Multiset.card β)), oneConcat_mul_tauW,
    ← mul_assoc, hz', bElt_mul_cL_one, cLL_mul_last_dot_pow,
    cPoly_cLL, map_mul, thetaL0_apply, ← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
  congr 1
  rw [thetaL0_apply, Algebra.TensorProduct.comm_tmul, thetaL, AlgHom.comp_apply,
    theta_tmul, map_pow, singlePoly_x, map_pow, Polynomial.aeval_X,
    map_one, mul_one, Polynomial.coe_mapAlgHom, Polynomial.map_pow, Polynomial.map_X]

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

include hQ ha in
/-- The summed form of KK (5.15) for the actual map `A`. -/
theorem aMap_sPoly_mul_X_pow (d : ℕ) :
    aMap i β a h1 hβ hsym (sPoly (Q := Q) i β a * Polynomial.X ^ d) =
      thetaL Q i β a (aPrime Q i β a) * Polynomial.X ^ d := by
  rw [← bMap_gProd_mul_first_dot_pow i β a hsym h1 hβ,
    aMap_bMap, pMap_mk, cMap_mk]
  exact cPoly_gProd_first_dot_tauW i β a hsym hβ hQ ha d

include hQ ha in
/-- KK (5.16), using the existing monic polynomial `aMonicL` rather than a new normalization. -/
theorem aMap_sPoly_mul_X_pow_monic (d : ℕ) :
    aMap i β a h1 hβ hsym (sPoly (Q := Q) i β a * Polynomial.X ^ d) =
      lamA Q i β • (aMonicL Q i β a * Polynomial.X ^ d) := by
  rw [aMap_sPoly_mul_X_pow i β a hsym hβ hQ ha h1, thetaL_aPrime i β a hQ,
    smul_mul_assoc]

theorem sPoly_mul_C_e (s : Seq β) :
    sPoly (Q := Q) i β a * Polynomial.C (CycKLR.mk k Q a β (e s)) =
      gLeadPoly (Q := Q) i β a (Multiset.card β) le_rfl s := by
  rw [sPoly, Finset.sum_mul]
  rw [Finset.sum_eq_single s]
  · rw [gLeadPoly_eq_factors, mul_assoc, ← Polynomial.C_mul, ← map_mul, e_mul_self]
  · intro t _ ht
    rw [gLeadPoly_eq_factors, mul_assoc, ← Polynomial.C_mul, ← map_mul,
      e_mul_e, ite_eq_right ht, map_zero, Polynomial.C_0, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem aPrime_mul_one_tmul_e (s : Seq β) :
    aPrime Q i β a * (1 ⊗ₜ e s) = cOf Q i β (gPol Q i β a s) * (1 ⊗ₜ e s) := by
  rw [aPrime, Finset.sum_mul]
  rw [Finset.sum_eq_single s]
  · rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, e_mul_self]
  · intro t _ ht
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      e_mul_e, ite_eq_right ht, TensorProduct.tmul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

include hQ ha in
/-- KK (5.15), sequence by sequence, with its signed product encoded by `gPol`. -/
theorem aMap_gLeadPoly_mul_X_pow (s : Seq β) (d : ℕ) :
    aMap i β a h1 hβ hsym
      (gLeadPoly (Q := Q) i β a (Multiset.card β) le_rfl s * Polynomial.X ^ d) =
      thetaL Q i β a (cOf Q i β (gPol Q i β a s) * (1 ⊗ₜ e s)) * Polynomial.X ^ d := by
  rw [← sPoly_mul_C_e, mul_assoc,
    ← (Polynomial.commute_X_pow (Polynomial.C (CycKLR.mk k Q a β (e s))) d).eq,
    ← mul_assoc, aMap_mul_C, aMap_sPoly_mul_X_pow i β a hsym hβ hQ ha h1,
    mul_assoc, (Polynomial.commute_X_pow (Polynomial.C (CycKLR.mk k Q a β (e s))) d).eq,
    ← mul_assoc, ← thetaL_one_tmul, ← map_mul, aPrime_mul_one_tmul_e]

end Categorification.KLR.KLRAlgebra
