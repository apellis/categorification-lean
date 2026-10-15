/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicMonic
import Categorification.KLR.SymmetricFactorization
import Categorification.KLR.CyclotomicBalanced

/-!
# The reversed cyclotomic product

Kang–Kashiwara, arXiv:1102.4677v4, Lemma 4.19: the product `PQ` on `K₀`
is the cyclically transported polynomial multiplier of `QP` on `K₁`.
The crossing normalization is the one used by `aElt` and `qMap_pMap`.
-/

namespace Categorification.KLR.KLRAlgebra
open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
  (a : I → Polynomial k)
local notation "R" => KLRAlgebra k Q ν
local notation "m" => Multiset.card ν

/-- The cyclic transport of the `QP` multiplier to the last strand. -/
noncomputable def bElt (h0 : 0 < m) (n : ℕ) : R :=
  ∑ s : Seq ν, pol (rename (cP m n) (cycA a h0 s * cycF Q s n)) * e (cP m n • s)

theorem bElt_mem_subR0 (h0 : 0 < m) (n : ℕ) :
    bElt (Q := Q) a h0 n ∈ subR0 ν := by
  exact Subalgebra.sum_mem _ fun s _ =>
    Subalgebra.mul_mem _ (pol_mem_subR0 _) (e_mem_subR0 _)

theorem pol_commute_bElt (h0 : 0 < m) (n : ℕ) (f : MvPolynomial (Fin m) k) :
    Commute (pol f : R) (bElt a h0 n) := by
  apply Commute.sum_right
  intro s _
  exact (pol_commute _ _).mul_right (commute_e_pol _ _).symm

/-- Transporting the polynomial multiplier through `P`. -/
theorem aElt_tauW_sub_mem (h0 : 0 < m) (n : ℕ) (hn : n + 1 = m) :
    (aElt a h0 n * tauW a h0 n - tauW a h0 n * bElt a h0 n : R) ∈ cycL0 a h0 := by
  rw [aElt, bElt, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro s _
  rw [mul_assoc, e_mul_tauW, ← mul_assoc, ← mul_assoc, ← sub_mul]
  exact mul_mem_cycL0 a (pol_mul_tauW a h0 n hn _) (e_mem_subR0 _)

variable (hsym : KLRSymm Q)

include hsym

/-- The defect of the reversed product is zero on the image of `P`. -/
theorem tauW_reverse_defect_mem (h0 : 0 < m) (h1 : 1 < m) (n : ℕ) (hn : n + 1 = m) :
    (tauW a h0 n * (gProd n * tauW a h0 n - bElt a h0 n) : R) ∈ cycL0 a h0 := by
  have h := qMap_pMap (Q := Q) a hsym h0 h1 n hn (1 : R)
  rw [pMap_mk, qMap_mk, one_mul, one_mul, Submodule.Quotient.eq] at h
  have hp := mul_tauW_mem a h0 h1 n hn h
  have ht := aElt_tauW_sub_mem (Q := Q) a h0 n hn
  convert Submodule.add_mem _ hp ht using 1
  noncomm_ring

/-- The reversed-product defect descends through the cyclotomic quotient. -/
theorem cycL0_mul_reverse_defect_mem (h0 : 0 < m) (h1 : 1 < m) (n : ℕ) (hn : n + 1 = m)
    {z : R} (hz : z ∈ cycL0 a h0) :
    z * (gProd n * tauW a h0 n - bElt a h0 n) ∈ cycL0 a h0 := by
  rw [mul_sub, ← mul_assoc]
  exact Submodule.sub_mem _ (mul_tauW_mem a h0 h1 n hn (mul_gProd_mem a hsym h0 h1 n hn hz))
    (mul_mem_cycL0 a hz (bElt_mem_subR0 a h0 n))

/-- The defect annihilates the full cyclotomic ideal, not just `cycL0`. -/
theorem cycIdeal_mul_reverse_defect_mem (h0 : 0 < m) (h1 : 1 < m) (n : ℕ) (hn : n + 1 = m)
    {z : R} (hz : z ∈ cycIdeal Q a ν) :
    z * (gProd n * tauW a h0 n - bElt a h0 n) ∈ cycL0 a h0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (cycIdeal_le a h0 n hn hz)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [add_mul, smul_eq_mul, mul_assoc]
  exact Submodule.add_mem _ (cycL0_mul_reverse_defect_mem a hsym h0 h1 n hn hu)
    (Submodule.smul_mem _ c (tauW_reverse_defect_mem a hsym h0 h1 n hn))

/-- Polynomial multiplication commutes with the reversed-product defect modulo `cycL0`. -/
theorem pol_reverse_defect_sub_mem (h0 : 0 < m) (n : ℕ) (hn : n + 1 = m)
    (f : MvPolynomial (Fin m) k) :
    (pol f * (gProd n * tauW a h0 n - bElt a h0 n) -
      (gProd n * tauW a h0 n - bElt a h0 n) * pol f : R) ∈ cycL0 a h0 := by
  have hp := pol_mul_tauW (Q := Q) a h0 n hn (rename (cP m n).symm f)
  have he : rename (cP m n) (rename (cP m n).symm f) = f := by
    rw [rename_rename, show (cP m n) ∘ (cP m n).symm = id from funext (cP m n).apply_symm_apply,
      rename_id_apply]
  rw [he] at hp
  have h := Submodule.smul_mem _ (gProd n : R) hp
  rw [smul_eq_mul, mul_sub] at h
  have hg := pol_mul_gProd (Q := Q) hsym n (by omega) f
  have hb := (pol_commute_bElt (Q := Q) a h0 n f).eq
  convert h using 1
  rw [mul_sub, sub_mul, ← mul_assoc (pol f), hg, hb]
  noncomm_ring

omit hsym

variable (i : I) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "R0" => KLRAlgebra k Q (Si + β)

/-- The first and last colour cuts are intertwined by `P` exactly. -/
theorem oneConcat_mul_tauW :
    (oneConcat Q Si β * tauW a (zero_lt_card_single_add i β) (Multiset.card β) : R0) =
      tauW a (zero_lt_card_single_add i β) (Multiset.card β) * cL Q i β 1 := by
  rw [oneConcat_single_eq, cL_one, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [e_mul_tauW, cP_smul_cons1]

variable (hβ : 0 < Multiset.card β)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)

include hsym hβ hQ ha in
/-- KK Lemma 4.19: the reversed-product defect vanishes on the last-colour corner. -/
theorem reverse_defect_cut_mem :
    ((gProd (Multiset.card β) * tauW a (zero_lt_card_single_add i β) (Multiset.card β) -
      bElt a (zero_lt_card_single_add i β) (Multiset.card β)) * cL Q i β 1 : R0) ∈
        cycL0 a (zero_lt_card_single_add i β) := by
  let h0 := zero_lt_card_single_add i β
  have h1 : 1 < Multiset.card (Si + β) := by rw [card_single_add]; omega
  have hn := (card_single_add i β).symm
  let d : R0 := gProd (Multiset.card β) * tauW a h0 (Multiset.card β) - bElt a h0 (Multiset.card β)
  obtain ⟨g, hg, hgz⟩ := CycKLR.exists_monic_dots (ν := Si + β)
    (fun i j h => isUnit_of_leadConst (hQ i j h)) ha
  have hz := hgz ⟨Multiset.card β, lastPos_lt i β⟩
  rw [CycKLR.mk_eq_zero_iff] at hz
  have hj := cycIdeal_mul_reverse_defect_mem a hsym h0 h1 (Multiset.card β) hn hz
  have hc := pol_reverse_defect_sub_mem a hsym h0 (Multiset.card β) hn
    (Polynomial.aeval (X ⟨Multiset.card β, lastPos_lt i β⟩) g)
  have hd := Submodule.sub_mem _ hj hc
  rw [sub_sub_cancel, pol_aeval_X] at hd
  have hd' := mul_mem_cycL0 a hd (cL_one_mem_subR0 i β)
  have he := (commute_aeval_of_commute (commute_x_last_cL (Q := Q) i β 1) g).eq
  have hcut : (d * cL Q i β 1) * cL Q i β 1 = d * cL Q i β 1 := by
    rw [mul_assoc, ← cL_mul, mul_one]
  apply (mul_monic_mem_cycL0_iff_of_cut i β a hsym hβ _ hcut g hg).1
  change (d * cL Q i β 1) * Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R0) g ∈ _
  rw [mul_assoc, ← he, ← mul_assoc]
  exact hd'

include hsym hβ hQ ha in
/-- The reversed product after explicit last-colour projection. -/
theorem pMap_qMap_cut (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β)) (r : R0) :
    (act0 Q i β a 1)
      (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
        (qMap a hsym (zero_lt_card_single_add i β) h1 (Multiset.card β)
          (card_single_add i β).symm (Submodule.Quotient.mk r))) =
      Submodule.Quotient.mk (r * bElt a (zero_lt_card_single_add i β) (Multiset.card β) * cL Q i β 1) := by
  rw [qMap_mk, pMap_mk, act0_mk, Submodule.Quotient.eq]
  have h := Submodule.smul_mem _ r (reverse_defect_cut_mem a hsym i β hβ hQ ha)
  convert h using 1
  simp only [smul_eq_mul, mul_sub, sub_mul, mul_assoc]

include hsym hβ hQ ha in
/-- **KK Lemma 4.19**, on the right `e(β,i)` corner: `PQ` is right multiplication
by the cyclically transported polynomial, with the library's crossing normalization. -/
theorem pMap_qMap (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
    (r : R0) (hr : r * cL Q i β 1 = r) :
    pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
      (qMap a hsym (zero_lt_card_single_add i β) h1 (Multiset.card β)
        (card_single_add i β).symm (Submodule.Quotient.mk r)) =
      Submodule.Quotient.mk (r * bElt a (zero_lt_card_single_add i β) (Multiset.card β)) := by
  have h := pMap_qMap_cut a hsym i β hβ hQ ha h1 r
  have he : act0 Q i β a 1 (Submodule.Quotient.mk r) = Submodule.Quotient.mk r := by
    rw [act0_mk, hr]
  rw [← pMap_act, ← qMap_act, he] at h
  rw [mul_assoc, commute_cL_one_subR0 i β (bElt_mem_subR0 a _ _), ← mul_assoc, hr] at h
  exact h

end Categorification.KLR.KLRAlgebra
