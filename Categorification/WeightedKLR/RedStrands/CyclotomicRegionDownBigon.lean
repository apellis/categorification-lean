/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossingBigon
import Categorification.KLR.CyclotomicAction.GlobalNilpotent
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDotMate
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBigon

/-!
# The down bigons of the region model

Webster, arXiv:1309.3796v3, (4.2), in the proof of Theorem 4.25. When every red polynomial is
a monomial, `p r i = X ^ n r i`, the red/down crossings `a′` and `b′` of the double model of the
region family compose, in either order, to the `n r i`-th power of the dot on the downward black
strand (`regionDownBigon`). This is the hypothesis `DownBigon` of the assembled representation
of `𝒯`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y)

/-- **Bigon on the higher-weight side for a red pullback** (Webster, arXiv:1309.3796v3, (4.2)):
the quotient crossing followed by the dot crossing is the red pullback followed by the `d`-th
power of the dot on `E_i`. -/
theorem redPullbackAtDownQuotient_dotCrossing {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)
    (Λ δ : X) {Λ' : X} (hΛ : Λ + δ = Λ') (i : I) {x x₂ y y₂ : X}
    (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂) (h : y + δ = x) (h₂ : y₂ + δ = x₂)
    (d : ℕ) (hi : b i = Polynomial.X ^ d * a i) :
    redPullbackAtDownQuotient.{u, v, w} Q RD hab Λ δ hΛ i hx hy h h₂ ≫
        redPullbackAtDotCrossing Q RD hab Λ δ hΛ i hx hy h h₂ d hi =
      Functor.whiskerLeft (redPullbackAt Q RD hab Λ δ hΛ h)
        (blockSumMap (blockSucc RD Λ' i hy) fun _ _ hβ =>
          (End.of (dot.{u, v, w} Q b i (blockSucc_eq RD Λ' i hβ)) ^ d :
            End (ind Q b i (blockSucc_eq RD Λ' i hβ)))) := by
  subst hΛ
  refine NatTrans.ext (funext fun N => funext fun δ' => ?_)
  exact globalRedDownQuotient_dotCrossing_app Q hab RD Λ δ i hx hy h h₂ d hi N δ'

variable (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- The powers of the dot of a cyclotomic family are the block sums of the powers of the dot. -/
theorem cyclotomicFamily_dotPow_hom {a : I → k[X]} (ha : ∀ i, (a i).Monic) (Λ : X)
    (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ) (i : I) {x y : X}
    (h : x + RD.iX i = y) (n : ℕ) :
    ((show End ((cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).E i h) from
        (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).dot i h) ^ n).hom =
      blockSumMap (blockSucc RD Λ i h) fun _ _ hβ =>
        (End.of (dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ)) ^ n :
          End (ind Q a i (blockSucc_eq RD Λ i hβ))) := by
  rw [← powComp_eq_endPow, LinearCat.powComp_hom]
  refine (powComp_blockSumMap (blockSucc RD Λ i h)
    (fun _ _ hβ => dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ)) n).trans ?_
  congr 1
  funext _ _ hβ
  exact powComp_eq_endPow (End.of (dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))) n

section Region

variable {Q RD} {ℓ : ℕ} {p : Fin ℓ → I → k[X]} {lam : Fin ℓ → X}
  (hp : ∀ r i, (p r i).Monic)
  (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))

/-- The powers of the dot of the region family, factor by factor. -/
theorem regionFamily_dotPow_app (i : I) {μ μ' : X} (h : μ + RD.iX i = μ') (n : ℕ)
    (N : region.{u, v, w} Q p RD lam μ) (ν : Multiset (Fin ℓ)) :
    ((show End ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).E i h) from
        (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).dot i h) ^ n).hom.app N ν =
      (blockSumMap (blockSucc RD (regionHighest lam ν) i h) fun _ _ hβ =>
        (End.of (dot.{u, v, w} Q (regionPoly p ν) i
            (blockSucc_eq RD (regionHighest lam ν) i hβ)) ^ n :
          End (ind Q (regionPoly p ν) i (blockSucc_eq RD (regionHighest lam ν) i hβ)))).app
        (N ν) := by
  rw [← cyclotomicFamily_dotPow_hom Q RD hQ hlead hdeg (regionPoly_monic hp ν)
    (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) i h n]
  rw [← powComp_eq_endPow, ← powComp_eq_endPow]
  erw [LinearCat.powComp_piCell]
  rfl

/-- **The down bigons (4.2) of the region model** (Webster, arXiv:1309.3796v3, (4.2), proof of
Theorem 4.25): when every red polynomial is the monomial `p r i = X ^ n r i`, the red/down
crossings `a′` and `b′` of the double model of the region family compose, in either order, to
the `n r i`-th power of the dot on the downward black strand. -/
theorem regionDownBigon (n : Fin ℓ → I → ℕ) (hpr : ∀ r i, p r i = Polynomial.X ^ n r i) :
    DoubleDiagram.DownBigon (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
      (fun r _ _ h => regionRed Q p RD lam r h)
      (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄) n := by
  intro r i μ μ₁ μ₂ μ₃ h₁ h₂ h₃ h₄
  rw [regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r i h₁ h₂ h₃ h₄,
    regionRedDownDot_eq RD hQ hlead hp hpdeg hdeg r i h₁ h₂ h₃ h₄ (n r i) (hpr r i)]
  constructor
  · apply ObjectProperty.hom_ext
    refine NatTrans.ext (funext fun N => funext fun ν' => ?_)
    refine (blockResCrossRev_blockResCross_app_of_whiskerLeft (fun ν => r ::ₘ ν)
      (fun ν => r ::ₘ ν) id id (fun _ => rfl) (redFactor Q p RD lam r h₂)
      (redFactor Q p RD lam r h₃) (downFactor Q p RD lam i h₄) (downFactor Q p RD lam i h₁)
      (redFactorDownDot Q p RD lam r i h₁ h₂ h₃ h₄ (n r i) (hpr r i))
      (redFactorDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄)
      (fun _ => ⟨fun _ _ _ => Subsingleton.elim _ _, fun q => ⟨q, Subtype.ext rfl⟩⟩)
      (fun ν' => blockSumMap (blockSucc RD (regionHighest lam ν') i h₁) fun _ _ hβ =>
        (End.of (dot.{u, v, w} Q (regionPoly p ν') i
            (blockSucc_eq RD (regionHighest lam ν') i hβ)) ^ n r i :
          End (ind Q (regionPoly p ν') i (blockSucc_eq RD (regionHighest lam ν') i hβ))))
      ?_ N ν').trans ?_
    · intro ν ν' hν
      subst hν
      exact redPullbackAtDownQuotient_dotCrossing Q RD (regionPoly_dvd_cons p r ν) _ (lam r)
        (regionHighest_cons lam r ν) i h₄ h₁ h₂ h₃ (n r i)
        (regionPoly_cons_eq p r i (n r i) (hpr r i) ν)
    · exact (regionFamily_dotPow_app hQ hlead hdeg hp hpdeg i h₁ (n r i) _ ν').symm
  · apply ObjectProperty.hom_ext
    refine NatTrans.ext (funext fun N => funext fun ν' => ?_)
    refine (regionRedDownDot_quotient_app Q p RD lam r i h₁ h₂ h₃ h₄ (n r i) (hpr r i)
      N ν').trans ?_
    change _ = Limits.biproduct.map fun q : {ν // r ::ₘ ν = ν'} =>
      (redFactor Q p RD lam r h₃ q.1 ν' q.2).map
        (((show End ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).E i h₄) from
          (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).dot i h₄) ^ n r i).hom.app N q.1)
    congr 1
    funext q
    obtain ⟨ν, hν⟩ := q
    subst hν
    rw [regionFamily_dotPow_app hQ hlead hdeg hp hpdeg i h₄ (n r i) N ν]
    rfl

end Region

end Categorification.Stendhal
