/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDownMidSame
import Categorification.WeightedKLR.RedStrands.DoubleRouquierWebster
import Categorification.KLR.KKScalarsStandardPres
import Categorification.KLR.Rouquier.KLStandard

/-!
# The representation of `𝒯` on the region categories

Webster, arXiv:1309.3796v3, Theorem 4.25. The 2-category `𝒯` of Definitions 4.22 and 4.24, with
the black parameters of Khovanov–Lauda (`Q i j = qCL kl i j` for `i ≠ j`) and the cyclotomic
polynomials `X ^ ⟨α_i^∨, λ_r⟩` of dominant weights `λ_r`, acts on the region categories: a region of weight `μ` goes to the
product over multisets `ν` of red labels of the weight spaces of weight `μ` of the cyclotomic
KLR algebras with highest weight `∑_{r ∈ ν} λ_r`, a red line `r` acts by the pullback `I^λ`
along the cyclotomic quotients, and the black strands by cyclotomic induction and restriction
(`regionTensorPseudofunctor`).

The presentation is `tensorTwoCatPresentation` over the empty presentation of the double
signature.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Bicategory KLR CyclotomicAction TwoRep QuantumGroup
  Polynomial KL3.Diagram

universe u v w u₁

namespace DoubleDiagram

variable {I : Type u} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) (k : Type v) [CommRing k]

/-- The presentation of the double signature with no relations. -/
def emptyPresentation : StringDiagrams.Presentation.{v, max u u₁} (signature RD Λ) k where
  Rel := PEmpty
  dom := PEmpty.elim
  cod := PEmpty.elim
  rel i := i.elim

variable {RD Λ k}

theorem AdmRelsZero.emptyPresentation {B : Type*} [Bicategory B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    {M : Diagrams.BicatInterp.Model (signature RD Λ) B} {G : Diagrams.BicatInterp.GenImg M} :
    AdmRelsZero G (DoubleDiagram.emptyPresentation RD Λ k) :=
  fun i => i.elim

end DoubleDiagram

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k]
  {Q : I → I → MvPolynomial (Fin 2) k}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {ℓ : ℕ} (lam : Fin ℓ → X)
  (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  (exponents : Fin ℓ → I →₀ ℕ)
  (hexp : ∀ r i, (exponents r i : ℤ) = RD.pair (RD.iY i) (lam r))

/-- The cyclotomic polynomials `X ^ ⟨α_i^∨, λ_r⟩` of the red labels. -/
abbrev redMonomials : Fin ℓ → I → k[X] := fun r i => Polynomial.X ^ exponents r i

omit [DecidableEq I] [Nontrivial k] in
include hstd in
/-- The Khovanov–Lauda parameters are symmetric. -/
theorem kl_klrSymm : KLRSymm Q := (isRouquierQ_of_kl hstd).klrSymm

omit [DecidableEq I] in
include hstd in
/-- The leading coefficients of the Khovanov–Lauda parameters are units. -/
theorem kl_polyInY_leading : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c :=
  (isRouquierQ_of_kl hstd).polyInY_leading

omit [DecidableEq I] in
include hstd in
/-- The degrees of the Khovanov–Lauda parameters are given by the Cartan datum. -/
theorem kl_polyInY_degree : ∀ i j, j ≠ i →
    ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j) :=
  (isRouquierQ_of_kl hstd).polyInY_degree_pair RD

omit [DecidableEq I] in
include hexp in
/-- The cyclotomic polynomial of the red label `r` has degree `⟨α_i^∨, λ_r⟩`. -/
theorem redMonomials_natDegree (r : Fin ℓ) (i : I) :
    (((redMonomials (k := k) exponents) r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r) := by
  rw [Polynomial.natDegree_X_pow]
  exact hexp r i

/-- **The representation of `𝒯` on the region categories** (Webster, arXiv:1309.3796v3,
Theorem 4.25), for the Khovanov–Lauda black parameters (`Q i j = qCL kl i j` for `i ≠ j`) over a
nontrivial commutative ring and the cyclotomic polynomials `X ^ ⟨α_i^∨, λ_r⟩` of dominant weights
`λ_r`: the pseudofunctor out of the presented 2-category `𝒯`, read with 1-morphisms from the
right region to the left region, sending a region of weight `μ` to the region category (the
product over multisets `ν` of red labels of the weight spaces of weight `μ` of the cyclotomic
KLR algebras with highest weight `∑_{r ∈ ν} λ_r`), a red line `r` to the pullback along the
cyclotomic quotients, and the black strands to cyclotomic induction and restriction on every
factor. -/
def regionTensorPseudofunctor :
    Pseudofunctor (RevBicat (DoubleDiagram.tensorTwoCatPresentation RD lam Q exponents
      (cyclotomicScalars (kl_klrSymm hstd) (kl_polyInY_leading hstd) RD
        (kl_polyInY_degree RD hstd))
      (DoubleDiagram.emptyPresentation RD lam k)).Bicat)
      (LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) :=
  have hQ := kl_klrSymm hstd
  have hlead := kl_polyInY_leading hstd
  have hdeg := kl_polyInY_degree RD hstd
  have hp : ∀ r i, ((redMonomials (k := k) exponents) r i).Monic := fun _ _ =>
    Polynomial.monic_X_pow _
  have hpdeg := redMonomials_natDegree RD lam exponents hexp
  have hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ, -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
      (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0 := fun i j h p q hlt =>
    coeff_eq_zero_of_lt_of_hom C ((isRouquierQ_of_kl hstd).homogeneous i j h) p q hlt
  DoubleDiagram.tensorTwoCatPseudofunctor (S := regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
    (red := fun r _ _ h => regionRed Q (redMonomials exponents) RD lam r h)
    (upIso := fun r i _ _ _ _ h₁ h₂ h₃ h₄ =>
      regionRedUpIso Q (redMonomials exponents) RD lam r i h₁ h₂ h₃ h₄)
    Q exponents DoubleDiagram.AdmRelsZero.emptyPresentation
    (regionFamily_brundanUpKLR RD hQ hlead hp hpdeg hdeg hsupp)
    (regionFamily_mixedInversion RD hQ hlead hp hpdeg hdeg) (fun _ => rfl)
    (fun _ _ _ _ hp' hq' _ => kkScalars_s_eq_zero_of_kl hQ _ (hstd _ _) hp' hq')
    (presCL_kkScalars_of_kl RD hQ _ hstd)
    (RouqUpKLR.pi fun ν => cyclotomicFamily_upKLR hQ hlead (regionPoly_monic hp ν) RD
      (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg)
    (regionDownBigon hQ hlead hdeg hp hpdeg (fun r i => exponents r i) fun _ _ => rfl)
    (regionUpIsoDotNatural hQ hlead hp hpdeg hdeg)
    (regionUpIsoCrossNatural RD hQ hlead hp hpdeg hdeg hsupp)
    (regionDownMidSame RD hQ hlead hp hpdeg hdeg (fun r i => exponents r i) fun _ _ => rfl)

end Categorification.Stendhal
