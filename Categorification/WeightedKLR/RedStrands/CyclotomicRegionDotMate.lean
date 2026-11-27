/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFamilyPiCap
import Categorification.WeightedKLR.RedStrands.CyclotomicRedDotCap
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDownMate

/-!
# The dot crossing is the mate of the red/up crossing

Webster, arXiv:1309.3796v3, §4.6, proof of Theorem 4.25. In the double model of the region
family, the red/down crossing `b′` is defined as the mate of the inverse red/up crossing for the
left adjunctions `F_i ⊣ E_i` (Rouquier's, built from the leftward caps). When the red
polynomial is a monomial, `p r i = X ^ d`, it is the dot crossing `regionRedDownDot`
(`regionRedDownDot_mate`, `regionRedDownDot_eq`), so the down bigons (4.2) of the double model
are the cyclotomic bigons (`regionDownBigon`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ℓ : ℕ} {p : Fin ℓ → I → k[X]}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {lam : Fin ℓ → X}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (hp : ∀ r i, (p r i).Monic)
  (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
  (h₂ : μ + lam r = μ₂) (h₃ : μ₁ + lam r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)
  (d : ℕ) (hpr : p r i = Polynomial.X ^ d)

/-- **The dot crossing on regions is the mate of the inverse red/up crossing** (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25): `b′` is the mate of `a⁻¹` for the left
adjunctions `F_i ⊣ E_i` of the region family, when `p r i = X ^ d`. -/
theorem regionRedDownDot_mate :
    Bicategory.mateEquiv ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adjL i h₄)
      ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adjL i h₁)
      (regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄).inv =
      regionRedDownDot Q p RD lam r i h₁ h₂ h₃ h₄ d hpr := by
  apply ObjectProperty.hom_ext
  erw [LinearCat.mate_hom]
  refine mateNat_blockResCrossRev_eq_of_counit (fun ν => r ::ₘ ν) (redFactor Q p RD lam r h₂)
    (redFactor Q p RD lam r h₃) (downFactor Q p RD lam i h₄) (downFactor Q p RD lam i h₁)
    (upFactor Q p RD lam i h₄) (upFactor Q p RD lam i h₁)
    (fun ν => ((cyclotomicFamily.{u, v, w} hQ hlead (regionPoly_monic hp ν) RD
      (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg).adjL i h₄).counit.hom)
    (fun ν => ((cyclotomicFamily.{u, v, w} hQ hlead (regionPoly_monic hp ν) RD
      (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg).adjL i h₁).counit.hom)
    (redFactorDownDot Q p RD lam r i h₁ h₂ h₃ h₄ d hpr) _
    (LinearCat.toAdjunction ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adjL i h₄))
    (LinearCat.toAdjunction ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adjL i h₁))
    (fun Y ν => RouqFamily.pi_adjL_counit_app (fun ν => cyclotomicFamily.{u, v, w} hQ hlead
      (regionPoly_monic hp ν) RD (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg)
      i h₄ Y ν)
    (fun Y ν => RouqFamily.pi_adjL_counit_app (fun ν => cyclotomicFamily.{u, v, w} hQ hlead
      (regionPoly_monic hp ν) RD (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg)
      i h₁ Y ν) ?_
  intro ν ν' hν N
  subst hν
  dsimp only [redFactorUpIso, Iso.symm_inv, redFactor, upFactor, downFactor, redFactorDownDot]
  have key := redPullbackAtDotCrossing_capL Q (regionPoly_dvd_cons p r ν) i d
    (regionPoly_cons_eq p r i d hpr ν) RD (regionHighest lam ν) (lam r) h₄ h₁ h₂ h₃ hQ hlead
    (regionPoly_monic hp ν) (regionPoly_monic hp (r ::ₘ ν)) (regionPoly_natDegree RD hp hpdeg ν)
    hdeg (regionHighest_cons lam r ν) (regionPoly_natDegree RD hp hpdeg (r ::ₘ ν)) N
  exact key

/-- **The red/down crossing `b′` of the region model is the dot crossing** (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25), when `p r i = X ^ d`. -/
theorem regionRedDownDot_eq :
    DoubleDiagram.redDownDot (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
        (fun r _ _ h => regionRed Q p RD lam r h)
        (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄)
        r i h₁ h₂ h₃ h₄ =
      regionRedDownDot Q p RD lam r i h₁ h₂ h₃ h₄ d hpr :=
  regionRedDownDot_mate RD hQ hlead hp hpdeg hdeg r i h₁ h₂ h₃ h₄ d hpr

end Categorification.Stendhal
