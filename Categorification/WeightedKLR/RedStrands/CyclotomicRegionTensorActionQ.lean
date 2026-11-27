/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionTensorAction
import Categorification.WeightedKLR.RedStrands.DoubleRouquierWebsterQ

/-!
# The representation of `𝒯` on the region categories for general black parameters

Webster, arXiv:1309.3796v3, Theorem 4.25, for every Rouquier polynomial family `Q`
(`IsRouquierQ C Q`: symmetric, weighted homogeneous of degree `-2 (α_i, α_j)`, with unit leading
coefficients) rather than only the Khovanov–Lauda parameters of `regionTensorPseudofunctor`.
The region categories carry the action of `U_Sc(g)` with the Kang–Kashiwara scalars
`Sc = cyclotomicScalars` of `Q`, so the black part of `𝒯` is the reflection of `U_Sc(g)`, that
is, the presentation `tensorTwoCatPresentationQ` at the scalars `Sc^θ = CLQ.thetaScalars RD Sc`
(`regionTensorPseudofunctorQ`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Bicategory KLR CyclotomicAction TwoRep QuantumGroup
  Polynomial KL3.Diagram

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k]
  {Q : I → I → MvPolynomial (Fin 2) k}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {ℓ : ℕ} (lam : Fin ℓ → X)
  (hR : IsRouquierQ C Q)
  (exponents : Fin ℓ → I →₀ ℕ)
  (hexp : ∀ r i, (exponents r i : ℤ) = RD.pair (RD.iY i) (lam r))

/-- **The representation of `𝒯` on the region categories for general black parameters**
(Webster, arXiv:1309.3796v3, Theorem 4.25), for every Rouquier polynomial family `Q` over a
nontrivial commutative ring and the cyclotomic polynomials `X ^ ⟨α_i^∨, λ_r⟩` of dominant weights
`λ_r`: the pseudofunctor out of the presented 2-category `𝒯` with the reflected Kang–Kashiwara
scalars of `Q` on black strands, read with 1-morphisms from the right region to the left
region, sending a region of weight `μ` to the region category, a red line `r` to the pullback
along the cyclotomic quotients, and the black strands to cyclotomic induction and restriction on
every factor. -/
def regionTensorPseudofunctorQ :
    Pseudofunctor (RevBicat (DoubleDiagram.tensorTwoCatPresentationQ RD lam Q exponents
      (CLQ.thetaScalars RD (cyclotomicScalars hR.klrSymm hR.polyInY_leading RD
        (hR.polyInY_degree_pair RD)))
      (DoubleDiagram.emptyPresentation RD lam k)).Bicat)
      (LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) :=
  have hQ := hR.klrSymm
  have hlead := hR.polyInY_leading
  have hdeg := hR.polyInY_degree_pair RD
  have hp : ∀ r i, ((redMonomials (k := k) exponents) r i).Monic := fun _ _ =>
    Polynomial.monic_X_pow _
  have hpdeg := redMonomials_natDegree RD lam exponents hexp
  have hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ, -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
      (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0 := fun i j h p q hlt =>
    coeff_eq_zero_of_lt_of_hom C (hR.homogeneous i j h) p q hlt
  DoubleDiagram.tensorTwoCatPseudofunctorQ (S := regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
    (red := fun r _ _ h => regionRed Q (redMonomials exponents) RD lam r h)
    (upIso := fun r i _ _ _ _ h₁ h₂ h₃ h₄ =>
      regionRedUpIso Q (redMonomials exponents) RD lam r i h₁ h₂ h₃ h₄)
    Q exponents DoubleDiagram.AdmRelsZero.emptyPresentation
    (regionFamily_brundanUpKLR RD hQ hlead hp hpdeg hdeg hsupp)
    (regionFamily_mixedInversion RD hQ hlead hp hpdeg hdeg) (fun _ => rfl)
    (fun i j p q hp' hq' h => kkScalars_s_eq_zero C hQ _ hR.homogeneous i j p q hp' hq' h)
    (RouqUpKLR.pi fun ν => cyclotomicFamily_upKLR hQ hlead (regionPoly_monic hp ν) RD
      (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg)
    (regionDownBigon hQ hlead hdeg hp hpdeg (fun r i => exponents r i) fun _ _ => rfl)
    (regionUpIsoDotNatural hQ hlead hp hpdeg hdeg)
    (regionUpIsoCrossNatural RD hQ hlead hp hpdeg hdeg hsupp)
    (regionDownMidSame RD hQ hlead hp hpdeg hdeg (fun r i => exponents r i) fun _ _ => rfl)

end Categorification.Stendhal
