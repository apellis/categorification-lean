/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAProduct

/-!
# Polynomial division and triangularity for the actual map A

Apply the polynomial argument of Kang–Kashiwara, arXiv:1102.4677v4,
Lemma 5.5 and Proposition 5.3, to the concrete cyclotomic maps.
The degree gap is expressed in polynomial degrees; identification with the
Cartan pairing and the final bimodule maps are separate steps.
-/

namespace Categorification.KLR.KLRAlgebra
open MvPolynomial TypeA Polynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [IsDomain k]
  {Q P : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)
  (a : I → Polynomial k)
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (hβ : 0 < Multiset.card β)
  (hQ : ∀ i j : I, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff)
  (ha : ∀ i, (a i).Monic)
  (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

local notation "Rl" => CycKLR k Q a β
local notation "A" => aMap i β a h1 hβ hPQ hP
local notation "S" => sPoly (Q := Q) i β a
local notation "F" => aMonicL Q i β a

include hQ ha in
/-- **KK Lemma 5.5** for the actual map `A`: its values are polynomial quotients. -/
theorem aMap_X_pow_eq_div (d : ℕ) :
    A (Polynomial.X ^ d) = lamA Q i β • ((Polynomial.X ^ d * F) /ₘ S) := by
  obtain ⟨c, hc⟩ := isUnit_lamA (Q := Q) i β hQ
  have hAS (j : ℕ) : A (Polynomial.X ^ j * S) = (c : k) • (Polynomial.X ^ j * F) := by
    rw [(Polynomial.commute_X_pow S j).eq,
      aMap_sPoly_mul_X_pow_monic i β a hPQ hP hβ hQ ha h1,
      (Polynomial.commute_X_pow F j).eq, hc]
  simpa only [hc, LinearMap.toAddMonoidHom_coe] using PhiAlg.apply_X_pow_eq (A).toAddMonoidHom c
    (aMap_mul_C i β a h1 hβ hPQ hP) (aMap_mul_X_degree i β a hPQ hP h1 hβ)
    (sPoly_monic i β a) (sPoly_comm i β a hPQ hP) hAS d

include hQ ha in
theorem aMap_X_pow_normalized (d : ℕ) :
    Ring.inverse (lamA Q i β) • A (Polynomial.X ^ d) = (Polynomial.X ^ d * F) /ₘ S := by
  rw [aMap_X_pow_eq_div i β a hPQ hP hβ hQ ha h1, smul_smul,
    Ring.inverse_mul_cancel _ (isUnit_lamA i β hQ), one_smul]

include hQ ha in
/-- **KK Proposition 5.3**, with the concrete degree gap in place of its Cartan-pairing expression. -/
theorem aMap_phi_spec [Nontrivial Rl] :
    (∀ j < (S).natDegree - (F).natDegree, A (Polynomial.X ^ j) = 0) ∧
      (∀ j, (S).natDegree - (F).natDegree ≤ j →
        (Ring.inverse (lamA Q i β) • A (Polynomial.X ^ j)).Monic ∧
        (Ring.inverse (lamA Q i β) • A (Polynomial.X ^ j)).natDegree =
          j - ((S).natDegree - (F).natDegree) + ((F).natDegree - (S).natDegree)) := by
  have hS := sPoly_monic (Q := Q) i β a
  have hF := monic_aMonicL (Q := Q) i β a (sym_of_factor hPQ) hQ (ha i)
  have hm (j : ℕ) : (Polynomial.X ^ j * F).Monic := (Polynomial.monic_X_pow j).mul hF
  have hmd (j : ℕ) : (Polynomial.X ^ j * F).natDegree = j + (F).natDegree := by
    rw [(Polynomial.monic_X_pow j).natDegree_mul hF, Polynomial.natDegree_X_pow]
  constructor
  · intro j hj
    rw [aMap_X_pow_eq_div i β a hPQ hP hβ hQ ha h1,
      (divByMonic_eq_zero_iff hS).2, smul_zero]
    rw [Polynomial.degree_eq_natDegree (hm j).ne_zero, Polynomial.degree_eq_natDegree hS.ne_zero, hmd]
    exact_mod_cast (show j + (F).natDegree < (S).natDegree by omega)
  · intro j hj
    rw [aMap_X_pow_normalized i β a hPQ hP hβ hQ ha h1]
    refine ⟨PhiAlg.monic_divByMonic (hm j) hS (by rw [hmd]; omega), ?_⟩
    rw [natDegree_divByMonic _ hS, hmd]
    omega

include hQ ha in
/-- The actual polynomial kernel consists exactly of degrees below the negative degree gap. -/
theorem aMap_eq_zero_iff [Nontrivial Rl] (p : Polynomial Rl) :
    A p = 0 ↔ p.degree < ((S).natDegree - (F).natDegree : ℕ) := by
  obtain ⟨c, hc⟩ := isUnit_lamA (Q := Q) i β hQ
  obtain ⟨hlow, hhigh⟩ := aMap_phi_spec i β a hPQ hP hβ hQ ha h1
  rw [← hc, Ring.inverse_unit] at hhigh
  simpa only [LinearMap.toAddMonoidHom_coe] using
    PhiAlg.apply_eq_zero_iff (A).toAddMonoidHom c
      ((S).natDegree - (F).natDegree) ((F).natDegree - (S).natDegree)
      (aMap_mul_C i β a h1 hβ hPQ hP) hlow hhigh p

include hQ ha in
/-- The actual polynomial cokernel has representatives below the positive degree gap. -/
theorem aMap_exists_remainder [Nontrivial Rl] (q : Polynomial Rl) :
    ∃ p, (q - A p).degree < ((F).natDegree - (S).natDegree : ℕ) := by
  obtain ⟨c, hc⟩ := isUnit_lamA (Q := Q) i β hQ
  obtain ⟨hlow, hhigh⟩ := aMap_phi_spec i β a hPQ hP hβ hQ ha h1
  rw [← hc, Ring.inverse_unit] at hhigh
  simpa only [LinearMap.toAddMonoidHom_coe] using
    PhiAlg.exists_sub_apply_degree_lt (A).toAddMonoidHom c
      ((S).natDegree - (F).natDegree) ((F).natDegree - (S).natDegree)
      (aMap_mul_C i β a h1 hβ hPQ hP) hlow hhigh q

include hQ ha in
/-- The nonnegative degree-gap case of the concrete polynomial map. -/
theorem aMap_injective_of_degree_le [Nontrivial Rl]
    (hd : (S).natDegree ≤ (F).natDegree) : Function.Injective A := by
  intro p q hpq
  have hz : A (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  have h := (aMap_eq_zero_iff i β a hPQ hP hβ hQ ha h1 (p - q)).1 hz
  rw [Nat.sub_eq_zero_of_le hd, Nat.cast_zero] at h
  have hz' : p - q = 0 := by
    simpa only [Polynomial.zero_le_degree_iff, not_not] using (not_le.mpr h)
  exact sub_eq_zero.1 hz'

include hQ ha in
/-- The nonpositive degree-gap case of the concrete polynomial map. -/
theorem aMap_surjective_of_degree_le [Nontrivial Rl]
    (hd : (F).natDegree ≤ (S).natDegree) : Function.Surjective A := by
  intro q
  obtain ⟨p, hp⟩ := aMap_exists_remainder i β a hPQ hP hβ hQ ha h1 q
  rw [Nat.sub_eq_zero_of_le hd, Nat.cast_zero] at hp
  have hz : q - A p = 0 := by
    simpa only [Polynomial.zero_le_degree_iff, not_not] using (not_le.mpr hp)
  exact ⟨p, (sub_eq_zero.1 hz).symm⟩

end Categorification.KLR.KLRAlgebra
