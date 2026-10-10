/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicBalanced

/-!
# Compatibility of the cyclotomic diagram: AB = CP

The lower first-strand coordinates map under `P` to the balanced crossing
image killed by `C`. Thus the concrete map `A`, not merely its value on the
chosen section of `B`, makes the diagram of Kang–Kashiwara,
arXiv:1102.4677v4, §5.2 commute.
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

/-- The first singleton factor uses only the first dot and colour idempotents. -/
theorem concat_first_mem (S : Subalgebra k R)
    (he : ∀ t, (e t : R) ∈ S)
    (hx : ∀ b : Fin (Multiset.card Si), (x (Seq.posL β b) : R) ∈ S) (c : Ri) :
    concat Q Si β (c ⊗ₜ 1) ∈ S := by
  have hunit : (oneConcat Q Si β : R) ∈ S := by
    rw [oneConcat_single_eq]; exact Subalgebra.sum_mem _ fun t _ => he _
  induction c using klr_induction with
  | hadd c d hc hd => rw [TensorProduct.add_tmul, map_add]; exact Subalgebra.add_mem _ hc hd
  | hmul c d hc hd =>
    have hh : ((c * d) ⊗ₜ[k] (1 : Rb)) = (c ⊗ₜ 1) * (d ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hh, concat_mul]; exact Subalgebra.mul_mem _ hc hd
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', map_smul,
      concat_one_tmul_one]
    exact Subalgebra.smul_mem _ hunit r
  | he t =>
    have ht : (e t : Ri) = 1 := e_single i t
    rw [ht, concat_one_tmul_one]; exact hunit
  | hx b => rw [concat_x_tmul_one]; exact Subalgebra.mul_mem _ (hx b) hunit
  | hψ j =>
    rw [ψ_eq_zero j (by rw [card_single']; omega), TensorProduct.zero_tmul, map_zero]
    exact Subalgebra.zero_mem _

theorem cycAt_mem_of_generators {ν : Multiset I} (a : I → Polynomial k)
    (S : Subalgebra k (KLRAlgebra k Q ν)) (he : ∀ t, (e t : KLRAlgebra k Q ν) ∈ S)
    (b : Fin (Multiset.card ν)) (hx : (x b : KLRAlgebra k Q ν) ∈ S) : cycAt a b ∈ S := by
  rw [cycAt]
  apply Subalgebra.sum_mem
  intro t _
  rw [pol_aeval_X, Polynomial.aeval_eq_sum_range]
  exact Subalgebra.mul_mem _ (Subalgebra.sum_mem _ fun d _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hx _) _) (he t)

variable (a : I → Polynomial k) (hβ : 0 < Multiset.card β)
  [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hβ in
/-- `CP` vanishes on every lower first-strand coordinate. -/
theorem cPoly_lower_tauW (b : ℕ) (hb : b < Multiset.card β) (t : T) :
    cPoly i β hPQ hP a ((ψw (descRun 0 b) * concat Q Si β t) *
      tauW a (zero_lt_card_single_add i β) (Multiset.card β)) = 0 := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, mul_add, add_mul, hs, ht, add_zero]
  | tmul c y =>
    let u : R := ψw (descRun 0 b) * concat Q Si β (c ⊗ₜ 1)
    have hc : concat Q Si β (c ⊗ₜ 1) ∈ cLCore i β :=
      concat_first_mem i β _ (e_mem_cLCore i β)
        (fun j => x_mem_cLCore i β ⟨j.val, by have := j.2; simp only [card_single'] at this; omega⟩) c
    have hc' : concat Q Si β (c ⊗ₜ 1) ∈ subR0 (k := k) (Q := Q) (Si + β) :=
      concat_first_mem i β _ e_mem_subR0 (fun j => x_mem_subR0 _) c
    have hd : ∀ j ∈ descRun 0 b, j + 1 < Multiset.card β := by
      intro j hj
      rw [descRun, List.mem_reverse, List.mem_range'_1] at hj
      omega
    have hu : u ∈ cLCore i β := Subalgebra.mul_mem _ (ψw_mem_cLCore i β _ hd) hc
    have hu' : u ∈ subR0 (k := k) (Q := Q) (Si + β) := Subalgebra.mul_mem _
      (ψw_mem_subR0 _ (fun j hj => by have := hd j hj; rw [card_single_add]; omega)) hc'
    let w : R := u * cycAt a ⟨0, zero_lt_card_single_add i β⟩ * tauProd (Multiset.card β - 1)
    have hw : w ∈ cLCore i β := Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ hu (cycAt_mem_of_generators a _ (e_mem_cLCore i β) _
        (x_mem_cLCore i β ⟨0, hβ⟩)))
      (ψw_mem_cLCore i β _ (fun j hj => by rw [List.mem_range] at hj; omega))
    have hw' : w ∈ subR0 (k := k) (Q := Q) (Si + β) := Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ hu' (cycAt_mem_of_generators a _ e_mem_subR0 _ (x_mem_subR0 _)))
      (tauProd_mem_subR0 _ (by rw [card_single_add]; omega))
    have hz := cPoly_eq_zero i β hPQ hP a hβ
      (Submodule.smul_mem _ u (cR_mul_tauW_sub_mem i β a y))
    change cPoly i β hPQ hP a (u * (cR Q i β y * tauW a _ _ - tauW a _ _ * cL Q i β y)) = 0 at hz
    rw [mul_sub, map_sub, sub_eq_zero] at hz
    have ht : concat Q Si β (c ⊗ₜ y) = concat Q Si β (c ⊗ₜ 1) * cR Q i β y := by
      rw [cR, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, ← mul_assoc, mul_assoc, hz]
    have hn : Multiset.card β = (Multiset.card β - 1) + 1 := by omega
    have he : u * (tauW a (zero_lt_card_single_add i β) (Multiset.card β) * cL Q i β y) =
        w * ψ (Multiset.card β - 1) * cL Q i β y := by
      unfold tauW
      rw [show tauProd (Multiset.card β) = (tauProd (Multiset.card β - 1) * ψ (Multiset.card β - 1) : R) by
        conv_lhs => rw [hn]; rw [tauProd_succ]]
      simp only [w, mul_assoc]
    rw [he]
    exact cPoly_core_crossing i β hβ hPQ hP a hw hw' y

include hβ in
/-- Only the final first-strand coordinate contributes to `CP`. -/
theorem cPoly_firstFree_tauW (t : Fin (Multiset.card β + 1) → T) :
    cPoly i β hPQ hP a (firstFree i β t *
      tauW a (zero_lt_card_single_add i β) (Multiset.card β)) =
    cPoly i β hPQ hP a ((ψw (descRun 0 (Multiset.card β)) *
      concat Q Si β (t (Fin.last (Multiset.card β)))) *
        tauW a (zero_lt_card_single_add i β) (Multiset.card β)) := by
  rw [firstFree, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_single (Fin.last (Multiset.card β))
  · intro b _ hb
    exact cPoly_lower_tauW i β a hβ hPQ hP b.val
      (by have := b.2; have : b.val ≠ Multiset.card β := fun h => hb (Fin.ext h); omega) (t b)
  · intro h; exact absurd (Finset.mem_univ _) h

include hβ in
/-- Right projection to `e(i,β)` does not change `CP`. -/
theorem cPoly_oneConcat_tauW (r : R) :
    cPoly i β hPQ hP a ((r * oneConcat Q Si β) *
      tauW a (zero_lt_card_single_add i β) (Multiset.card β)) =
    cPoly i β hPQ hP a (r * tauW a (zero_lt_card_single_add i β) (Multiset.card β)) := by
  have hz := cPoly_eq_zero i β hPQ hP a hβ
    (Submodule.smul_mem _ r (cR_mul_tauW_sub_mem i β a 1))
  change cPoly i β hPQ hP a (r * (cR Q i β 1 * tauW a _ _ - tauW a _ _ * cL Q i β 1)) = 0 at hz
  rw [mul_sub, map_sub, sub_eq_zero] at hz
  have he : cR Q i β 1 = oneConcat Q Si β := concat_one_tmul_one
  rw [he, ← mul_assoc, ← mul_assoc, cPoly_mul_cL_one] at hz
  exact hz

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

/-- The actual diagram identity `AB = CP` on all of `K_1`. -/
theorem aMap_bMap (w : KOne Q (Si + β) a h1) :
    aMap i β a h1 hβ hPQ hP (bMap i β hPQ hP a h1 hβ w) =
      cMap i β hPQ hP a hβ
        (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
          (card_single_add i β).symm w) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [bMap_mk, pMap_mk, cMap_mk]
  change aMap i β a h1 hβ hPQ hP
    (thetaL Q i β a (firstCoord i β hPQ hP r (Fin.last (Multiset.card β)))) = _
  rw [aMap_thetaL, ← cPoly_firstFree_tauW i β a hβ hPQ hP,
    firstFree_firstCoord, cPoly_oneConcat_tauW i β a hβ hPQ hP]

/-- Equality of the two composites in the cyclotomic diagram. -/
theorem aMap_comp_bMap :
    (aMap i β a h1 hβ hPQ hP).comp (bMap i β hPQ hP a h1 hβ) =
      (cMap i β hPQ hP a hβ).comp
        ((pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
          (card_single_add i β).symm).restrictScalars k) := by
  apply LinearMap.ext
  intro w
  exact aMap_bMap i β a hβ hPQ hP h1 w

end Categorification.KLR.KLRAlgebra
