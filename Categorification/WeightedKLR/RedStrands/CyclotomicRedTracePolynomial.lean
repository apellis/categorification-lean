/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicSCentral
import Categorification.WeightedKLR.RedStrands.CyclotomicRedPullback

/-!
# The trace polynomials under cyclotomic projection

For the red weight change in Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25,
changing the new colour's cyclotomic polynomial by a power of `X` multiplies the
normalized polynomial `A` of Kang–Kashiwara, arXiv:1102.4677v4, Remark 4.20 and §5.2,
by that same power. Their squared-difference polynomial `S` projects coefficientwise.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → Polynomial k}
  (hab : ∀ i, a i ∣ b i) (i : I) (β : Multiset I)

private theorem red_aMonic (d : ℕ) (hi : b i = Polynomial.X ^ d * a i) :
    aMonic Q i β b = Polynomial.X ^ d * aMonic Q i β a := by
  have hsplit (s : Seq β) : fSplit i β (gPol Q i β b s) =
      Polynomial.X ^ d * fSplit i β (gPol Q i β a s) := by
    simp only [gPol, KLRAlgebra.cycA, cons1_zero, hi, map_mul, map_pow, Polynomial.aeval_X,
      fSplit_X_zero, mul_assoc]
  simp only [aMonic, theta_aPrime, hsplit, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, mul_assoc, Finset.mul_sum, mul_smul_comm]

private theorem red_map_affine_polynomial (p : Polynomial (KLRAlgebra k Q β)) :
    (p.map (CycKLR.mk k Q b β).toRingHom).map (cyclotomicRedProjection Q hab β).toRingHom =
      p.map (CycKLR.mk k Q a β).toRingHom := by
  ext n
  simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    cyclotomicRedProjection_mk]

/-- The cyclotomic projection sends the larger block's normalized `A` to `Xᵈ A` for
`bᵢ = Xᵈ aᵢ`. The normalization scalar in KK Remark 4.20 depends only on `Q,i,β`. -/
theorem cyclotomicRedProjection_aMonicL (d : ℕ) (hi : b i = Polynomial.X ^ d * a i) :
    (aMonicL Q i β b).map (cyclotomicRedProjection Q hab β).toRingHom =
      Polynomial.X ^ d * aMonicL Q i β a := by
  trans (aMonic Q i β b).map (CycKLR.mk k Q a β).toRingHom
  · exact red_map_affine_polynomial Q hab β _
  change _ = Polynomial.X ^ d * (aMonic Q i β a).map (CycKLR.mk k Q a β).toRingHom
  rw [red_aMonic Q i β d hi,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

/-- The squared-difference polynomial of KK §5.2 projects to the smaller block's `S`. -/
theorem cyclotomicRedProjection_sPoly :
    (sPoly (Q := Q) i β b).map (cyclotomicRedProjection Q hab β).toRingHom =
      sPoly (Q := Q) i β a := by
  rw [← thetaL_sTensor, ← thetaL_sTensor]
  exact red_map_affine_polynomial Q hab β _

end Categorification.Stendhal
