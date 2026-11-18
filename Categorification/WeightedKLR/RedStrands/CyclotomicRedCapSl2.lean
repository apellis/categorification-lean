/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedCapTrace
import Categorification.QuantumGroup.UDotKL3

/-!
# A nonzero cap across opposite coroot signs

For the red crossings in Webster, arXiv:1309.3796v2, Theorem 4.25,
the trace on a normalized crossing difference at highest weights 3 and 5
projects to the same nonzero two-strand nilHecke commutator.
-/

noncomputable section
namespace Categorification.Stendhal.TypeA1Cap
open KLR KLRAlgebra Polynomial QuantumGroup.UDot

local notation "ι" => Unit.unit

local notation "β₁" => (Singleton.singleton Unit.unit : Multiset Unit)

local notation "𝒬" => (fun _ _ : Unit => (0 : MvPolynomial (Fin 2) ℚ))

local notation "𝒜" => (fun n : ℕ => fun _ : Unit => (X ^ n : Polynomial ℚ))

local notation "β" => (β₁ + (0 : Multiset Unit))

local notation "ℛ" => (fun n : ℕ => CycKLR ℚ 𝒬 (𝒜 n) β)

local notation "RD" => sl2RootDatum

private theorem hsym : KLRSymm 𝒬 := fun j l h => (h (Subsingleton.elim j l)).elim

private theorem hQ : ∀ j l : Unit, j ≠ l →
    ∃ c : ℚ, IsUnit c ∧ (polyInY (𝒬 j l)).leadingCoeff = C c :=
  fun j l h => (h (Subsingleton.elim j l)).elim

private theorem hdeg : ∀ j : Unit, j ≠ ι →
    ((polyInY (𝒬 j ι)).natDegree : ℤ) = -(RD).pair ((RD).iY ι) ((RD).iX j) :=
  fun j h => (h (Subsingleton.elim j ι)).elim

private theorem hΛ (n : ℕ) : (((𝒜 n) ι).natDegree : ℤ) = (RD).pair ((RD).iY ι) n := by
  simp [sl2RootDatum]

private theorem wt (n : ℕ) :
    (RD).pair ((RD).iY ι) ((n : ℤ) - Multiset.sum ((β₁ + 0).map (RD).iX)) = (n : ℤ) - 2 := by
  simp [sl2RootDatum]

private instance seqUnique (ν : Multiset Unit) : Unique (Seq ν) where
  default := Classical.choice (inferInstance : Nonempty (Seq ν))
  uniq _s := Subtype.ext (funext fun _ => Subsingleton.elim _ _)

private theorem e_one {ν : Multiset Unit} (s : Seq ν) : (e s : KLRAlgebra ℚ 𝒬 ν) = 1 := by
  rw [Subsingleton.elim s default]
  simpa using (sum_e (Q := 𝒬) (ν := ν))

private theorem cl_one (ν : Multiset Unit) : cL 𝒬 ι ν 1 = 1 := by
  rw [cL_one, Fintype.sum_unique, e_one]

private def firstDot (n : ℕ) : ℛ n :=
  CycKLR.mk ℚ 𝒬 (𝒜 n) β (x ⟨0, by simp⟩)

private theorem label_eq (j : Unit) : j = ι := Subsingleton.elim _ _

private def cap (n : ℕ) :=
  CornerTrace.trace 𝒬 ι (0 : Multiset Unit) (𝒜 n) hsym hQ (fun _ => monic_X_pow n)
    RD (n : ℤ) (hΛ n) hdeg

private theorem upper_pos :
    0 < (RD).pair ((RD).iY ι) (((3 : ℕ) : ℤ) - Multiset.sum ((β₁ + 0).map (RD).iX)) := by
  norm_num [sl2RootDatum]

private theorem powerDvd (n d : ℕ) : ∀ j, (𝒜 n) j ∣ (𝒜 (n+d)) j :=
  redPower_dvd (fun _ => n) (fun _ => d)

private def lowerLeft (n : ℕ) (r : ℛ n) :
    CornerTensor.Left (lowerLastCyc 𝒬 ι 0 (𝒜 n)) :=
  ⟨r, by
    change r * CycKLR.mk ℚ 𝒬 (𝒜 n) β (cL 𝒬 ι 0 1) = r
    rw [cl_one, map_one, mul_one]⟩

private def lowerRight (n : ℕ) (r : ℛ n) : LowerCoefficient 𝒬 ι 0 (𝒜 n) :=
  ⟨r, by
    change CycKLR.mk ℚ 𝒬 (𝒜 n) β (cL 𝒬 ι 0 1) * r = r
    rw [cl_one, map_one, one_mul]⟩

private def cross (n : ℕ) (r : ℛ n) : MiddleCyclotomic 𝒬 ι 0 (𝒜 n) :=
  cyclotomicSigma 𝒬 ι 0 (𝒜 n) (BalancedTensor.tmul (lowerLeft n r) (lowerRight n 1))

local notation "β₂" => (β₁ + β)

local notation "𝒯" => (fun n : ℕ => CycKLR ℚ 𝒬 (𝒜 n) β₂)

private abbrev mkTwo (n : ℕ) := CycKLR.mk ℚ 𝒬 (𝒜 n) β₂

local notation "dot₁" => (x (Q := 𝒬) (ν := β₂) ⟨0, by simp⟩)

local notation "dot₂" => (x (Q := 𝒬) (ν := β₂) ⟨1, by simp⟩)

local notation "τ" => (-ψ (Q := 𝒬) (ν := β₂) 0)

private def corner (n : ℕ) (z : 𝒯 n) : MiddleCyclotomic 𝒬 ι 0 (𝒜 n) :=
  ⟨z, by
    change mkTwo n (cL 𝒬 ι β 1) * z = z ∧ z * mkTwo n (cL 𝒬 ι β 1) = z
    rw [cl_one, map_one, one_mul, mul_one]
    exact ⟨rfl,rfl⟩⟩

private theorem eqIdem_one : (eqIdem (Q := 𝒬) (ν := β₂) 0 (by simp)) = 1 := by
  simp only [eqIdem, label_eq, Fintype.sum_unique, ite_true, e_one]

private theorem cyclotomicLast_one (n : ℕ) : cyclotomicLast 𝒬 ι 0 (𝒜 n) 1 = 1 := by
  rw [← map_one (CycKLR.mk ℚ 𝒬 (𝒜 n) β), cyclotomicLast_mk, cl_one, map_one]

private theorem cross_one_coe (n : ℕ) : (cross n 1 : 𝒯 n) = mkTwo n τ := by
  rw [cross, cyclotomicSigma_tmul_canonical]
  change cyclotomicLast 𝒬 ι 0 (𝒜 n) 1 * _ * cyclotomicLast 𝒬 ι 0 (𝒜 n) 1 = _
  rw [cyclotomicLast_one, one_mul, mul_one]
  rfl

private theorem cross_dot_coe (n : ℕ) :
    (cross n (firstDot n) : 𝒯 n) = mkTwo n dot₁ * mkTwo n τ := by
  rw [cross, cyclotomicSigma_tmul_canonical]
  change cyclotomicLast 𝒬 ι 0 (𝒜 n) (firstDot n) * _ *
    cyclotomicLast 𝒬 ι 0 (𝒜 n) 1 = _
  rw [cyclotomicLast_one, mul_one, firstDot, cyclotomicLast_mk, cL_x, cl_one, mul_one]
  rfl

private theorem unit_poly_coe (n : ℕ) :
    (cyclotomicDotUnit 𝒬 ι 0 (𝒜 n) (monomial 0 1) : 𝒯 n) = 1 := by
  have := cyclotomicDotUnit_monomial 𝒬 ι (0 : Multiset Unit) (𝒜 n) 1 0
  simpa only [map_one, cl_one, pow_zero, mul_one] using this

private theorem tau_dot : τ * dot₂ = dot₁ * τ + 1 := by
  have hr := x_mul_ψ_self (Q := 𝒬) (ν := β₂) 0 (by simp)
  rw [eqIdem_one] at hr
  calc
    _ = -(dot₁ * ψ 0 - 1) := by rw [neg_mul, hr, add_sub_cancel_right]
    _ = _ := by rw [neg_sub, mul_neg, sub_eq_add_neg]; exact add_comm _ _

private theorem crossed_dot_decompose :
    corner 3 ((cross 3 1 : 𝒯 3) * mkTwo 3 dot₂) =
      cross 3 (firstDot 3) + cyclotomicDotUnit 𝒬 ι 0 (𝒜 3) (monomial 0 1) := by
  apply Subtype.ext
  change (cross 3 1 : 𝒯 3) * mkTwo 3 dot₂ =
    (cross 3 (firstDot 3) : 𝒯 3) +
      (cyclotomicDotUnit 𝒬 ι 0 (𝒜 3) (monomial 0 1) : 𝒯 3)
  rw [cross_one_coe, cross_dot_coe, unit_poly_coe, ← map_mul, tau_dot,
    map_add, map_mul, map_one]

theorem cap_cross_dot :
    cap 3 (corner 3 ((cross 3 1 : 𝒯 3) * mkTwo 3 dot₂)) = 1 := by
  rw [crossed_dot_decompose, cap, CornerTrace.trace, dite_eq_left upper_pos, map_add, cross,
    CornerTrace.positive_crossing, zero_add]
  let j : Fin ((RD).pair ((RD).iY ι)
    (((3 : ℕ) : ℤ) - Multiset.sum ((β).map (RD).iX))).toNat := ⟨0, by rw [wt]; decide⟩
  have hj : 0 = ((RD).pair ((RD).iY ι)
    (((3 : ℕ) : ℤ) - Multiset.sum ((β).map (RD).iX))).toNat - 1 := by
    rw [wt]
    rfl
  have h := CornerTrace.positive_dotUnit 𝒬 ι 0 (𝒜 3) hsym hQ (fun _ => monic_X_pow 3)
    RD (3 : ℤ) (hΛ 3) hdeg upper_pos j 1
  change _ = (if 0 = ((RD).pair ((RD).iY ι)
    (((3 : ℕ) : ℤ) - Multiset.sum ((β).map (RD).iX))).toNat - 1 then 1 else 0) at h
  rwa [ite_eq_left hj] at h

private theorem tau_sq : (τ : KLRAlgebra ℚ 𝒬 β₂) * τ = 0 := by
  have h := ψ_sq (Q := 𝒬) (ν := β₂) 0 (by simp) default
  rw [e_one, mul_one] at h
  rw [neg_mul_neg]
  exact h

private theorem nontrivialBase3 : Nontrivial (ℛ 3) := by
  change Nontrivial (CycKLR ℚ 𝒬 (𝒜 3) β₁)
  have h : Nontrivial (AdjoinRoot ((𝒜 3) ι)) := AdjoinRoot.nontrivial _ (by
    change degree ((X : Polynomial ℚ) ^ 3) ≠ 0
    rw [degree_X_pow]
    decide)
  exact (cyclotomicSingleEquiv 𝒬 ι (𝒜 3)).symm.injective.nontrivial

private theorem nontrivialTwo3 : Nontrivial (𝒯 3) := by
  rcases subsingleton_or_nontrivial (𝒯 3) with h | h
  · have hn := nontrivialBase3
    have he : corner 3 ((cross 3 1 : 𝒯 3) * mkTwo 3 dot₂) = 0 :=
      Subtype.ext (Subsingleton.elim _ _)
    have htt := cap_cross_dot
    rw [he, map_zero] at htt
    exact (zero_ne_one htt).elim
  · exact h

private theorem commutator_ne_zero :
    mkTwo 3 τ * mkTwo 3 dot₂ - mkTwo 3 dot₂ * mkTwo 3 τ ≠ 0 := by
  have := nontrivialTwo3
  intro hz
  have h := congrArg (mkTwo 3) tau_dot
  simp only [map_mul, map_add, map_one] at h
  have hsq := congrArg (mkTwo 3) tau_sq
  simp only [map_mul, map_zero] at hsq
  rw [sub_eq_zero] at hz
  rw [hz] at h
  have he := congrArg (fun z => z * mkTwo 3 τ) h
  simp only [mul_assoc, hsq, mul_zero, add_mul, one_mul, zero_add] at he
  rw [← he, mul_zero, mul_zero, zero_add] at h
  exact zero_ne_one h

private def leftTwo (n : ℕ) (r : 𝒯 n) :
    CornerTensor.Left (lowerLastCyc 𝒬 ι β (𝒜 n)) :=
  ⟨r, by change r * mkTwo n (cL 𝒬 ι β 1) = r; rw [cl_one, map_one, mul_one]⟩

private def rightTwo (n : ℕ) (r : 𝒯 n) : LowerCoefficient 𝒬 ι β (𝒜 n) :=
  ⟨r, by change mkTwo n (cL 𝒬 ι β 1) * r = r; rw [cl_one, map_one, one_mul]⟩

private def differenceTensor (n : ℕ) : LowerCyclotomic 𝒬 ι β (𝒜 n) :=
  BalancedTensor.tmul (leftTwo n (mkTwo n τ)) (rightTwo n 1) -
    BalancedTensor.tmul (leftTwo n 1) (rightTwo n (mkTwo n τ))

private def differenceCross (n : ℕ) : MiddleCyclotomic 𝒬 ι β (𝒜 n) :=
  cyclotomicSigma 𝒬 ι β (𝒜 n) (differenceTensor n)

private def capTwo (n : ℕ) :=
  CornerTrace.trace 𝒬 ι β (𝒜 n) hsym hQ (fun _ => monic_X_pow n)
    RD (n : ℤ) (hΛ n) hdeg

private theorem wtTwo (n : ℕ) :
    (RD).pair ((RD).iY ι) ((n : ℤ) - Multiset.sum ((β₂).map (RD).iX)) = (n : ℤ) - 4 := by
  simp [sl2RootDatum]

private theorem differenceCounitZero : cyclotomicDotCounit 𝒬 ι β (𝒜 3) 0 (differenceTensor 3) = 0 := by
  rw [differenceTensor, map_sub, cyclotomicDotCounit_tmul, cyclotomicDotCounit_tmul, pow_zero]
  change mkTwo 3 τ * mkTwo 3 1 * 1 - 1 * mkTwo 3 1 * mkTwo 3 τ = 0
  simp only [map_one, mul_one, one_mul, sub_self]

theorem strict_lower_cap :
    capTwo 3 (differenceCross 3) = mkTwo 3 τ * mkTwo 3 dot₂ - mkTwo 3 dot₂ * mkTwo 3 τ := by
  have hneg : ¬ 0 < (RD).pair ((RD).iY ι)
      (((3 : ℕ) : ℤ) - Multiset.sum ((β₂).map (RD).iX)) := by rw [wtTwo]; decide
  rw [capTwo, CornerTrace.trace, dite_eq_right hneg, differenceCross,
    CornerTrace.nonpositive_crossing_normalized]
  · have hh : (-(RD).pair ((RD).iY ι)
        (((3 : ℕ) : ℤ) - Multiset.sum ((β₂).map (RD).iX))).toNat = 1 := by rw [wtTwo]; decide
    rw [hh, differenceTensor, map_sub, cyclotomicDotCounit_tmul, cyclotomicDotCounit_tmul, pow_one]
    change mkTwo 3 τ * mkTwo 3 dot₂ * 1 - 1 * mkTwo 3 dot₂ * mkTwo 3 τ = _
    simp only [one_mul, mul_one]
  · intro j
    have hh : (-(RD).pair ((RD).iY ι)
        (((3 : ℕ) : ℤ) - Multiset.sum ((β₂).map (RD).iX))).toNat = 1 := by rw [wtTwo]; decide
    have hj : (j : ℕ) = 0 := by have := j.isLt; omega
    rw [hj, differenceCounitZero]

theorem strict_lower_cap_ne_zero : capTwo 3 (differenceCross 3) ≠ 0 := by
  rw [strict_lower_cap]
  exact commutator_ne_zero

private theorem twoLast_one (n : ℕ) : cyclotomicLast 𝒬 ι β (𝒜 n) 1 = 1 := by
  rw [← map_one (mkTwo n), cyclotomicLast_mk, cl_one, map_one]

private theorem differenceCross_coe (n : ℕ) :
    (differenceCross n : CycKLR ℚ 𝒬 (𝒜 n) (β₁ + β₂)) =
      CycKLR.mk ℚ 𝒬 (𝒜 n) (β₁ + β₂)
        (cL 𝒬 ι β₂ τ * (-ψ ((β).card)) - (-ψ ((β).card)) * cL 𝒬 ι β₂ τ) := by
  dsimp only [differenceCross, differenceTensor]
  rw [map_sub]
  change ((cyclotomicSigma 𝒬 ι β (𝒜 n) (BalancedTensor.tmul (leftTwo n (mkTwo n τ)) (rightTwo n 1))) :
      CycKLR ℚ 𝒬 (𝒜 n) (β₁ + β₂)) -
    ((cyclotomicSigma 𝒬 ι β (𝒜 n) (BalancedTensor.tmul (leftTwo n 1) (rightTwo n (mkTwo n τ)))) :
      CycKLR ℚ 𝒬 (𝒜 n) (β₁ + β₂)) = _
  rw [cyclotomicSigma_tmul_canonical, cyclotomicSigma_tmul_canonical]
  change cyclotomicLast 𝒬 ι β (𝒜 n) (mkTwo n τ) * _ * cyclotomicLast 𝒬 ι β (𝒜 n) 1 -
    cyclotomicLast 𝒬 ι β (𝒜 n) 1 * _ * cyclotomicLast 𝒬 ι β (𝒜 n) (mkTwo n τ) = _
  simp only [twoLast_one, one_mul, mul_one, cyclotomicLast_mk, map_mul, map_sub]

private theorem strict_projection :
    middleRedProjection 𝒬 ι β (powerDvd 3 2) (differenceCross 5) = differenceCross 3 := by
  apply Subtype.ext
  change cyclotomicRedProjection 𝒬 (powerDvd 3 2) (β₁ + β₂)
    (differenceCross 5 : CycKLR ℚ 𝒬 (𝒜 5) (β₁ + β₂)) = _
  rw [differenceCross_coe, cyclotomicRedProjection_mk, differenceCross_coe]

theorem strict_upper_projected_cap :
    cyclotomicRedProjection 𝒬 (powerDvd 3 2) β₂
        (capTwo 5 (middleDotPow 𝒬 ι β (𝒜 5) 2 (differenceCross 5))) =
      mkTwo 3 τ * mkTwo 3 dot₂ - mkTwo 3 dot₂ * mkTwo 3 τ := by
  have he := redProjection_oppositeCap 𝒬 ι β (powerDvd 3 2) hsym hQ
    (fun _ => monic_X_pow 3) (fun _ => monic_X_pow 5)
    RD (3 : ℤ) (5 : ℤ) (hΛ 3) (hΛ 5) hdeg 2 (by change X ^ 5 = X ^ 2 * (X ^ 3 : ℚ[X]); rw [← pow_add])
    (differenceCross 5)
  rw [strict_projection] at he
  exact he.trans strict_lower_cap

end Categorification.Stendhal.TypeA1Cap
