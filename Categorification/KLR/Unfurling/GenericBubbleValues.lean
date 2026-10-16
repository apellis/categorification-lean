/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.BubbleFibres
import Categorification.KLR.Unfurling.GenericWeights
import Categorification.KLR.Unfurling.VacuumMixed

/-!
# Generic scalar bubble values

The scalar products in Webster, *Unfurling KLR algebras*, arXiv:1603.06311v3, proof of the
theorem labelled `nondegenerate`, “Triviality of a relation”, using the fields and labels
constructed in `GenericFields`.

The sign of the base weight chooses the orientation used by `bubGen`: for nonnegative weight,
the local counterclockwise series has positive negative-alphabet multiplicities and negative
positive-alphabet multiplicities; at negative weight the signs are reversed. This is the same
orientation convention recorded by `RouqFamily.bubbleMap_X`.

`bubbleEval_X_of_nonneg` and `bubbleEval_X_of_neg` express these scalars in the `lwSeq` form
of `ccw_app_vacuum` and `cw_app_vacuum`. `bubbleEval_indep` proves the independence required
by `UnfurledEval.bub_indep`, without assuming any independence of the constructed spectral
values and without requiring a finite colour set. It needs only enough negative-alphabet
slots of level one; the remaining multiplicities are arbitrary natural numbers.
`vacuumBubbleEval_indep` specializes this to the constructed `negLevel`/`posLevel`,
leaving only the numerical requirement that the number of bubble slots is at least `N`.

Identification with the categorical vacuum action still requires the structural hypotheses
of the vacuum bubble theorems and reindexing their edge products by these slots. This file
does not assume or assert that identification.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open PowerSeries
variable {L : Type*} [Field L]
/-- The dot count at positive degree index `n + 1` selects coefficient `n + 1`. -/
theorem lwSeq_degree_index (D n : ℕ) (F : PowerSeries L) :
    lwSeq D F (D + n) = coeff (n + 1) F := by
  simp [lwSeq, Nat.add_assoc]
end Categorification.KLR.Unfurling
namespace Categorification.KLR.Unfurling.GenericFields
open PowerSeries
variable (k : Type*) [Field k] (I Q : Type*)

/-- The two generic alphabets arranged in finite fibres over colours. -/
def slotValues : I × (Q ⊕ Q) → L k (I × Q) (I × Q) :=
  Sum.elim (zNeg k (I × Q) (I × Q)) (zPos k (I × Q) (I × Q)) ∘
    Equiv.prodSumDistrib I Q Q

/-- Independence of the constructed spectral values, with the fibre indexing. -/
theorem independent_slots : AlgebraicIndependent k (slotValues k I Q) :=
  (independent k (I × Q) (I × Q)).comp _ (Equiv.prodSumDistrib I Q Q).injective

variable {I Q}

open Classical in
/-- Signed multiplicities for the orientation chosen by the base weight. -/
def bubbleMultiplicity (h : I → ℤ) (nm np : I → Q → ℕ) (i : I) : Q ⊕ Q → ℤ :=
  if 0 ≤ h i then Sum.elim (fun q => (nm i q : ℤ)) (fun q => -(np i q : ℤ))
  else Sum.elim (fun q => -(nm i q : ℤ)) (fun q => (np i q : ℤ))

variable [Fintype Q]

/-- The polynomial map given by the oriented generic scalar products. -/
def bubbleEval (h : I → ℤ) (nm np : I → Q → ℕ) :
    KL3.Diagram.PiLam I k →ₐ[k] L k (I × Q) (I × Q) :=
  fibreBubEval (bubbleMultiplicity h nm np) (slotValues k I Q)

/-- The constructed scalar map satisfies `UnfurledEval.bub_indep` when there are
enough level-one slots in the negative alphabet. -/
theorem bubbleEval_indep (h : I → ℤ) (nm np : I → Q → ℕ)
    (G : Finset Q) (hG : ∀ i q, q ∈ G → nm i q = 1) {N : ℕ} (hN : N ≤ G.card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} =>
      bubbleEval k h nm np (MvPolynomial.X p.1) := by
  classical
  apply fibreBubEval_indep _ (independent_slots k I Q)
    (G.map ⟨Sum.inl, Sum.inl_injective⟩) (fun i => decide (0 ≤ h i))
  · intro i j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hj
    dsimp [bubbleMultiplicity]
    by_cases hi : 0 ≤ h i <;> simp [hi, hG i q hq]
  · simpa using hN

/-- Product formula for the local counterclockwise orientation. -/
theorem bubbleSeries_of_nonneg (h : I → ℤ) (nm np : I → Q → ℕ) (i : I) (hi : 0 ≤ h i) :
    fibreMultSeries (bubbleMultiplicity h nm np) (slotValues k I Q) i =
      (∏ q, (1 - C (zNeg k (I × Q) (I × Q) (i, q)) * X) ^ nm i q) *
      ((∏ q, oneSubUnit (zPos k (I × Q) (I × Q) (i, q)) ^ (-(np i q : ℤ)) :
        (PowerSeries (L k (I × Q) (I × Q)))ˣ) : PowerSeries _) := by
  simp only [fibreMultSeries, Fintype.prod_sum_type, bubbleMultiplicity, ite_eq_left hi,
    Sum.elim_inl, Sum.elim_inr, slotValues, Function.comp_apply,
    Equiv.prodSumDistrib_apply_left, Equiv.prodSumDistrib_apply_right]
  simp only [Units.val_mul, Units.coe_prod, zpow_natCast,
    Units.val_pow_eq_pow_val, coe_oneSubUnit]

/-- Product formula for the local clockwise orientation. -/
theorem bubbleSeries_of_neg (h : I → ℤ) (nm np : I → Q → ℕ) (i : I) (hi : h i < 0) :
    fibreMultSeries (bubbleMultiplicity h nm np) (slotValues k I Q) i =
      (∏ q, (1 - C (zPos k (I × Q) (I × Q) (i, q)) * X) ^ np i q) *
      ((∏ q, oneSubUnit (zNeg k (I × Q) (I × Q) (i, q)) ^ (-(nm i q : ℤ)) :
        (PowerSeries (L k (I × Q) (I × Q)))ˣ) : PowerSeries _) := by
  simp only [fibreMultSeries, Fintype.prod_sum_type, bubbleMultiplicity, ite_eq_right (not_le.mpr hi),
    Sum.elim_inl, Sum.elim_inr, slotValues, Function.comp_apply,
    Equiv.prodSumDistrib_apply_left, Equiv.prodSumDistrib_apply_right]
  simp only [Units.val_mul, Units.coe_prod, zpow_natCast,
    Units.val_pow_eq_pow_val, coe_oneSubUnit]
  exact mul_comm _ _

/-- The generator value with the dot shift used by `ccw_app_vacuum`. -/
theorem bubbleEval_X_of_nonneg (h : I → ℤ) (nm np : I → Q → ℕ)
    (i : I) (hi : 0 ≤ h i) (n : ℕ) :
    bubbleEval k h nm np (MvPolynomial.X (i, n)) =
      lwSeq (h i).toNat
        ((∏ q, (1 - C (zNeg k (I × Q) (I × Q) (i, q)) * X) ^ nm i q) *
          ((∏ q, oneSubUnit (zPos k (I × Q) (I × Q) (i, q)) ^ (-(np i q : ℤ)) :
            (PowerSeries (L k (I × Q) (I × Q)))ˣ) : PowerSeries _))
        (h i + n).toNat := by
  have hm : (h i + n).toNat = (h i).toNat + n := by omega
  rw [hm, lwSeq_degree_index]
  simp only [bubbleEval, fibreBubEval, MvPolynomial.aeval_X, fibreMultVal]
  rw [bubbleSeries_of_nonneg k h nm np i hi]

/-- The generator value with the dot shift used by `cw_app_vacuum`. -/
theorem bubbleEval_X_of_neg (h : I → ℤ) (nm np : I → Q → ℕ)
    (i : I) (hi : h i < 0) (n : ℕ) :
    bubbleEval k h nm np (MvPolynomial.X (i, n)) =
      lwSeq (-h i).toNat
        ((∏ q, (1 - C (zPos k (I × Q) (I × Q) (i, q)) * X) ^ np i q) *
          ((∏ q, oneSubUnit (zNeg k (I × Q) (I × Q) (i, q)) ^ (-(nm i q : ℤ)) :
            (PowerSeries (L k (I × Q) (I × Q)))ˣ) : PowerSeries _))
        (-h i + n).toNat := by
  have hm : (-h i + n).toNat = (-h i).toNat + n := by omega
  rw [hm, lwSeq_degree_index]
  simp only [bubbleEval, fibreBubEval, MvPolynomial.aeval_X, fibreMultVal]
  rw [bubbleSeries_of_neg k h nm np i hi]

omit [Fintype Q] in
/-- The scalar bubble map for the concrete strand, bubble and balancing levels. -/
def vacuumBubbleEval (s b M : ℕ) (h : I → ℤ) :
    KL3.Diagram.PiLam I k →ₐ[k] L k (I × Slots s b) (I × Slots s b) :=
  bubbleEval k h (negLevel s b M h) (posLevel s b M h)

omit [Fintype Q] in
/-- The explicit generic weights supply the independence required by `UnfurledEval.bub_indep`.
There is no characteristic restriction on the strand level `M` and no finiteness hypothesis
on the colour set. -/
theorem vacuumBubbleEval_indep (s b M : ℕ) (h : I → ℤ) {N : ℕ} (hN : N ≤ b) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} =>
      vacuumBubbleEval k s b M h (MvPolynomial.X p.1) := by
  classical
  let e : Fin b ↪ Slots s b := ⟨fun q => Sum.inr (Sum.inl q),
    fun _ _ h => Sum.inl_injective (Sum.inr_injective h)⟩
  refine bubbleEval_indep k h (negLevel s b M h) (posLevel s b M h)
    (Finset.univ.map e) ?_ ?_
  · intro i q hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hq
    rfl
  · simpa using hN

end Categorification.KLR.Unfurling.GenericFields
