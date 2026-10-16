/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Datum

/-!
# KL crossing polynomials under scalar extension and symmetrization

Supporting Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action`: the existing KL II crossing polynomials `klP2 C o` supply the
factorization required by `UnfurlingDatum`. Their off-diagonal nonvanishing and
factorization are `klP2_ne_zero` and `klQ2_eq_klP2`; take `o = KL1.stdOrient` and
`KL2.stdOrient_spec` to choose an orientation without adding an order hypothesis.

Here coefficient extension commutes with both `klQ2` and `klP2`, and `klP2` is
weighted homogeneous for every natural-number symmetrizer satisfying the displayed
compatibility. This supplies the polynomial inputs of `UnfurlingDatum.ofClosure`.
The library convention is `Q i j = P j i * rename ![1, 0] (P i j)`, reversing the
indices of the factors in Webster's convention. No characteristic restriction is
needed for these polynomial identities; the subsequent power-series construction
separately requires the symmetrizer entries to be invertible.
-/

noncomputable section
namespace Categorification.KLR
open MvPolynomial
variable {k L : Type*} [CommRing k] [CommRing L] {I : Type*}
  (C : QuantumGroup.CartanDatum I)

/-- Extending coefficients preserves the KL polynomials. -/
theorem map_klQ2 (φ : k →+* L) (i j : I) :
    MvPolynomial.map φ (klQ2 k C i j) = klQ2 L C i j := by
  unfold klQ2
  split_ifs <;> simp

/-- The chosen crossing factorization is preserved by every coefficient map. -/
theorem map_klP2 (φ : k →+* L) (o : I → I → Prop) [DecidableRel o] (i j : I) :
    MvPolynomial.map φ (klP2 C o i j) = klP2 C o i j := by
  unfold klP2
  split_ifs <;> simp

/-- The Cartan symmetrizer also symmetrizes the off-diagonal exponents. -/
theorem symmetrizer_dij (d : I → ℕ)
    (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)
    {i j : I} (hij : i ≠ j) : d i * C.dij i j = d j * C.dij j i := by
  by_cases hd : C.dot i j = 0
  · have hd' : C.dot j i = 0 := by rw [C.symm]; exact hd
    rw [(C.dij_eq_zero_iff hij).2 hd, (C.dij_eq_zero_iff hij.symm).2 hd']
    simp
  · have h₁ := C.dij_mul hij
    have h₂ := C.dij_mul hij.symm
    rw [C.symm j i] at h₂
    have hs := hsym i j hd
    have he : ((d i : ℤ) * C.dij i j) * C.dot i i =
        ((d j : ℤ) * C.dij j i) * C.dot i i := by
      calc
        _ = (d i : ℤ) * (-2 * C.dot i j) := by rw [mul_assoc, h₁]
        _ = (d i : ℤ) * ((C.dij j i : ℤ) * C.dot j j) := by rw [h₂]
        _ = ((d j : ℤ) * C.dij j i) * C.dot i i := by nlinarith [congrArg (fun z : ℤ => (C.dij j i : ℤ) * z) hs]
    have := mul_right_cancel₀ (ne_of_gt (C.dot_self_pos i)) he
    exact_mod_cast this

/-- Weighted homogeneity of the crossing factors, with the reversed variable weights
required by the library factorization convention. -/
theorem klP2_isWeightedHomogeneous (o : I → I → Prop) [DecidableRel o]
    (d : I → ℕ)
    (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)
    (i j : I) (hij : i ≠ j) :
    ∃ D, (klP2 (k := k) C o i j).IsWeightedHomogeneous ![d j, d i] D := by
  unfold klP2
  split_ifs
  · refine ⟨d j * C.dij j i, IsWeightedHomogeneous.add ?_ ?_⟩
    · convert (isWeightedHomogeneous_X k ![d j, d i] 0).pow (C.dij j i) using 1
      simp [mul_comm]
    · convert (isWeightedHomogeneous_X k ![d j, d i] 1).pow (C.dij i j) using 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, nsmul_eq_mul]
      exact (symmetrizer_dij C d hsym hij).symm.trans (Nat.mul_comm _ _)
  · exact ⟨0, isWeightedHomogeneous_one k _⟩
end Categorification.KLR
