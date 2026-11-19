/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotWords
import Categorification.KLR.Rouquier.Polynomial
import Categorification.WeightedKLR.RedStrands.Stendhal

/-!
# Cyclotomic cover parameters for the red-strand presentation

Webster, arXiv:1309.3796v2, §2.2 and Definition 4.5. For the restriction
calculation of Lemma 4.35, enlarge the Cartan datum by one vertex of square
length two for each red label. Both leading coefficients of a mixed parameter
are units, and setting red dots to zero gives the polynomials of Definition 4.5.
-/
noncomputable section
namespace Categorification.Stendhal

open QuantumGroup KLR MvPolynomial
open scoped Matrix

variable {I k : Type*} {ℓ : ℕ} (C : CartanDatum I) (Λ : Fin ℓ → I →₀ ℕ)

private def halfLength (i : I) : ℕ := (C.dot i i / 2).toNat

private theorem twice_halfLength (i : I) : 2 * (halfLength C i : ℤ) = C.dot i i := by
  obtain ⟨a, ha⟩ := C.dot_self_even i
  have := C.dot_self_pos i
  unfold halfLength
  omega

private theorem halfLength_pos (i : I) : 0 < halfLength C i := by
  have := twice_halfLength C i
  have := C.dot_self_pos i
  omega

private def coverDot : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℤ
  | .inl i, .inl j => C.dot i j
  | .inl i, .inr r | .inr r, .inl i => -((halfLength C i * Λ r i : ℕ) : ℤ)
  | .inr r, .inr s => if r = s then 2 else -1

/-- The Cartan datum on black colours and individual red labels used to lift
Webster's parameters in Definition 4.5 to cyclotomic parameters. -/
def extendedCartanDatum : CartanDatum (I ⊕ Fin ℓ) where
  dot := coverDot C Λ
  symm a b := by cases a <;> cases b <;> simp [coverDot, C.symm, eq_comm]
  dot_self_pos a := by cases a <;> simp [coverDot, C.dot_self_pos]
  dot_self_even a := by cases a <;> simp [coverDot, C.dot_self_even]
  dot_nonpos a b h := by
    cases a <;> cases b <;> simp_all [coverDot, C.dot_nonpos] <;> positivity
  dvd_two_mul a b := by
    cases a with
    | inl i =>
      cases b with
      | inl j => exact C.dvd_two_mul i j
      | inr r =>
        refine ⟨-(Λ r i : ℤ), ?_⟩
        simp only [coverDot, Nat.cast_mul]
        rw [← twice_halfLength C i]
        ring
    | inr r =>
      cases b with
      | inl i => simp [coverDot]
      | inr s => by_cases h : r = s <;> simp [coverDot, h]

variable [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

private def purePowers (a b : ℕ) : MvPolynomial (Fin 2) k :=
  if a = 0 then 1 else X 0 ^ a + X 1 ^ b

/-- The mixed polynomial has a second pure power in the red variable, except
when the black and red vertices are orthogonal. -/
def cyclotomicCoverQ : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k
  | .inl i, .inl j => Q i j
  | .inl i, .inr r => purePowers (Λ r i) (halfLength C i * Λ r i)
  | .inr r, .inl i => purePowers (halfLength C i * Λ r i) (Λ r i)
  | .inr _, .inr _ => X 0 + X 1

private theorem purePowers_swap (a b : ℕ) (h : a = 0 ↔ b = 0) :
    rename (![1, 0] : Fin 2 → Fin 2) (purePowers (k := k) a b) = purePowers b a := by
  by_cases ha : a = 0 <;> simp_all [purePowers, add_comm]

private theorem purePowers_homogeneous (a b : ℕ) (u v d : ℤ)
    (hu : a * u = d) (hv : b * v = d) :
    (purePowers (k := k) a b).IsWeightedHomogeneous ![u, v] d := by
  by_cases ha : a = 0
  · subst a
    simpa [purePowers, ← hu] using (isWeightedHomogeneous_one (R := k) ![u,v])
  · rw [purePowers, ite_eq_right ha]
    apply IsWeightedHomogeneous.add
    · simpa [nsmul_eq_mul, hu] using (isWeightedHomogeneous_X (R := k) ![u,v] 0).pow a
    · simpa [nsmul_eq_mul, hv] using (isWeightedHomogeneous_X (R := k) ![u,v] 1).pow b

private theorem purePowers_unit (a b : ℕ) :
    IsUnit ((purePowers (k := k) a b).coeff (Finsupp.single 0 a)) := by
  by_cases ha : a = 0 <;> simp [purePowers, ha, coeff_single_X_pow]

private theorem cover_dij {a b : I ⊕ Fin ℓ} (h : a ≠ b) (n : ℕ)
    (hn : n * (extendedCartanDatum C Λ).dot a a = -2 * (extendedCartanDatum C Λ).dot a b) :
    (extendedCartanDatum C Λ).dij a b = n := by
  have hpos := (extendedCartanDatum C Λ).dot_self_pos a
  have H := (extendedCartanDatum C Λ).dij_mul h
  exact_mod_cast (mul_right_cancel₀ (ne_of_gt hpos) (H.trans hn.symm))

private theorem mixed_degree (i : I) (r : Fin ℓ) :
    (Λ r i : ℤ) * C.dot i i = -2 * -((halfLength C i * Λ r i : ℕ) : ℤ) := by
  rw [← twice_halfLength C i, Nat.cast_mul]
  ring

/-- The enlarged parameters satisfy the homogeneous Rouquier conditions of
Webster §2.2 over the same coefficient ring as the black parameters. -/
theorem isRouquierQ_cyclotomicCoverQ (hQ : IsRouquierQ C Q) :
    IsRouquierQ (extendedCartanDatum C Λ) (cyclotomicCoverQ C Λ Q) where
  symm a b h := by
    cases a with
    | inl i =>
      cases b with
      | inl j => exact hQ.symm i j (by simpa using h)
      | inr r => exact purePowers_swap _ _ (by simp [(halfLength_pos C i).ne'])
    | inr r =>
      cases b with
      | inl i => exact purePowers_swap _ _ (by simp [(halfLength_pos C i).ne'])
      | inr s => simp [cyclotomicCoverQ, add_comm]
  homogeneous a b h := by
    cases a with
    | inl i =>
      cases b with
      | inl j => exact hQ.homogeneous i j (by simpa using h)
      | inr r =>
        apply purePowers_homogeneous
        · exact mixed_degree C Λ i r
        · simp [extendedCartanDatum, coverDot]; ring
    | inr r =>
      cases b with
      | inl i =>
        apply purePowers_homogeneous
        · simp [extendedCartanDatum, coverDot]; ring
        · exact mixed_degree C Λ i r
      | inr s =>
        have hrs : r ≠ s := by simpa using h
        simp [cyclotomicCoverQ, extendedCartanDatum, coverDot, hrs]
        apply IsWeightedHomogeneous.add
        · exact isWeightedHomogeneous_X (R := k) ![(2 : ℤ), 2] 0
        · exact isWeightedHomogeneous_X (R := k) ![(2 : ℤ), 2] 1
  unit_coeff a b h := by
    cases a with
    | inl i =>
      cases b with
      | inl j => exact hQ.unit_coeff i j (by simpa using h)
      | inr r =>
        rw [cover_dij C Λ h (Λ r i) (mixed_degree C Λ i r)]
        exact purePowers_unit _ _
    | inr r =>
      cases b with
      | inl i =>
        rw [cover_dij C Λ h (halfLength C i * Λ r i) (by simp [extendedCartanDatum, coverDot]; ring)]
        exact purePowers_unit _ _
      | inr s =>
        have hrs : r ≠ s := by simpa using h
        rw [cover_dij C Λ h 1 (by simp [extendedCartanDatum, coverDot, hrs])]
        simp [cyclotomicCoverQ]

/-- The extremal coefficient of a black/red parameter is one: the coefficient of
`u^{d_ij}` in `u^{Λ_r(i)} + v^{…}` (or in `1` when `Λ_r(i) = 0`). -/
theorem coeff_dij_cyclotomicCoverQ_inl_inr (i : I) (r : Fin ℓ) :
    (cyclotomicCoverQ C Λ Q (.inl i) (.inr r)).coeff
      (Finsupp.single 0 ((extendedCartanDatum C Λ).dij (.inl i) (.inr r))) = 1 := by
  rw [cover_dij C Λ (show (Sum.inl i : I ⊕ Fin ℓ) ≠ .inr r from Sum.inl_ne_inr) (Λ r i)
    (mixed_degree C Λ i r)]
  by_cases h : Λ r i = 0
  · simp [cyclotomicCoverQ, purePowers, h]
  · have hb : halfLength C i * Λ r i ≠ 0 := Nat.mul_ne_zero (halfLength_pos C i).ne' h
    have hne : (Finsupp.single 1 (halfLength C i * Λ r i) : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 (Λ r i) := by
      intro he
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) he
      simp [hb] at this
    simp only [cyclotomicCoverQ, purePowers, h, ite_false]
    generalize halfLength C i * Λ r i = b at hne ⊢
    simp [coeff_X_pow, hne]

/-- Set the dot of each red label to zero in a two-strand parameter. -/
def specializeRedDots (a b : I ⊕ Fin ℓ) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![if a.isRight then 0 else X 0, if b.isRight then 0 else X 1]

/-- After the red-dot relations the enlarged parameters give exactly the
Stendhal crossing-square polynomials of Webster, Definition 4.5. -/
theorem specializeRedDots_cyclotomicCoverQ [DecidableEq I] (a b : I ⊕ Fin ℓ) :
    specializeRedDots a b (cyclotomicCoverQ C Λ Q a b) = stendhalQ Q Λ a b := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have he : specializeRedDots (k := k) (ℓ := ℓ) (.inl i) (.inl j) = AlgHom.id _ _ := by
        apply MvPolynomial.algHom_ext
        intro t
        fin_cases t <;> simp [specializeRedDots]
      rw [he]
      rfl
    | inr r =>
      by_cases h : Λ r i = 0 <;>
        simp [specializeRedDots, cyclotomicCoverQ, stendhalQ, purePowers, h, (halfLength_pos C i).ne']
  | inr r =>
    cases b with
    | inl i =>
      by_cases h : Λ r i = 0 <;>
        simp [specializeRedDots, cyclotomicCoverQ, stendhalQ, purePowers, h, (halfLength_pos C i).ne']
    | inr s => simp [specializeRedDots, cyclotomicCoverQ, stendhalQ]

/-- For a black outer label the divided difference in the braid relation of
Definition 4.5 is already equal before the red dots are specialized. -/
theorem qbar_cyclotomicCoverQ_black [DecidableEq I] (i : I) (b : I ⊕ Fin ℓ) :
    qbar (cyclotomicCoverQ C Λ Q (.inl i) b) = qbar (stendhalQ Q Λ (.inl i) b) := by
  cases b with
  | inl j => rfl
  | inr r =>
    by_cases h : Λ r i = 0
    · simp [cyclotomicCoverQ, stendhalQ, purePowers, h]
    · simp only [cyclotomicCoverQ, stendhalQ, purePowers, ite_eq_right h,
        qbar_X_pow_add_X_pow, StendhalAlgebraAllOrders.qbar_X_zero_pow]

/-- A black/red parameter is Webster's crossing-square polynomial plus a multiple of a positive
power of the red dot variable. -/
theorem cyclotomicCoverQ_inl_inr_eq [DecidableEq I] (i : I) (r : Fin ℓ) :
    ∃ (c : k) (n : ℕ), cyclotomicCoverQ C Λ Q (.inl i) (.inr r) =
      stendhalQ Q Λ (.inl i) (.inr r) + MvPolynomial.C c * X 1 ^ (n + 1) := by
  by_cases h : Λ r i = 0
  · exact ⟨0, 0, by simp [cyclotomicCoverQ, stendhalQ, purePowers, h]⟩
  · have hb : halfLength C i * Λ r i ≠ 0 := Nat.mul_ne_zero (halfLength_pos C i).ne' h
    refine ⟨1, halfLength C i * Λ r i - 1, ?_⟩
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hb)]
    simp [cyclotomicCoverQ, stendhalQ, purePowers, h]

/-- A red/black parameter is Webster's crossing-square polynomial plus a multiple of a positive
power of the red dot variable. -/
theorem cyclotomicCoverQ_inr_inl_eq [DecidableEq I] (r : Fin ℓ) (i : I) :
    ∃ (c : k) (n : ℕ), cyclotomicCoverQ C Λ Q (.inr r) (.inl i) =
      stendhalQ Q Λ (.inr r) (.inl i) + MvPolynomial.C c * X 0 ^ (n + 1) := by
  by_cases h : Λ r i = 0
  · exact ⟨0, 0, by simp [cyclotomicCoverQ, stendhalQ, purePowers, h]⟩
  · have hb : halfLength C i * Λ r i ≠ 0 := Nat.mul_ne_zero (halfLength_pos C i).ne' h
    refine ⟨1, halfLength C i * Λ r i - 1, ?_⟩
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hb)]
    simp [cyclotomicCoverQ, stendhalQ, purePowers, h, add_comm, (halfLength_pos C i).ne']

/-- In the enlarged Cartan datum a red letter contributes the corresponding
dominant-weight multiplicity to the black coroot pairing of a prefix. -/
theorem cover_black_red {C : CartanDatum I} (Λ : Fin ℓ → I →₀ ℕ) (i : I) (r : Fin ℓ) :
    UDot.A (extendedCartanDatum C Λ) (.inl i) (.inr r) = -(Λ r i : ℤ) := by
  change 2 * -(((C.dot i i / 2).toNat * Λ r i : ℕ) : ℤ) / C.dot i i = _
  have hd := C.dot_self_pos i
  have htwo := UDot.two_mul_di C i
  unfold UDot.di at htwo
  have hn : 0 ≤ C.dot i i / 2 := by omega
  rw [Nat.cast_mul, Int.toNat_of_nonneg hn]
  have he : 2 * -(C.dot i i / 2 * (Λ r i : ℤ)) = (-(Λ r i : ℤ)) * C.dot i i := by
    calc
      _ = (-(Λ r i : ℤ)) * (2 * (C.dot i i / 2)) := by ring
      _ = _ := by rw [htwo]
  rw [he, Int.mul_ediv_cancel _ hd.ne']

end Categorification.Stendhal
