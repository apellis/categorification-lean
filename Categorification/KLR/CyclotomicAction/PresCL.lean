/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalMixed
import Categorification.KLR.KKScalars

/-!
# The Cautis–Lauda presentation acts on cyclotomic KLR modules

Kang–Kashiwara (arXiv:1102.4677v4, (3.1)) take KLR polynomials with `KLRSymm Q`, unit extremal
coefficients, and coefficients `t_{i,j;p,q}` vanishing above the line
`(i · i) p + (j · j) q = -2 (i · j)`. The coefficients may lie in positive degrees of a graded
base ring, so the terms below the line need not vanish. Let `a_i` be monic cyclotomic polynomials
of degree `⟨h_i, Λ⟩`.

* For every such `Q`, `Q_ij = brundanQ (kkScalars Q) i j` for `i ≠ j` (`KLR.eq_brundanQ`), and
  the weight-indexed cyclotomic Rouquier family satisfies Brundan's mixed upward relations with
  these scalars (`cyclotomicFamily_brundanUpKLR`) and his mixed inversion
  (`cyclotomicFamily_mixedInversion`).
* When moreover each `Q_ij` is weighted homogeneous of degree `-2 (i · j)` (all
  `t_{i,j;p,q}` of degree `0`), the normalized Cautis–Lauda presentation `presCL` with the scalars
  `kkScalars Q` acts on the weight spaces of the cyclotomic KLR algebras by a pseudofunctor into
  `LinearCat k`, with `E_i`, `F_i` acting by cyclotomic induction and restriction
  (`cyclotomicPresCL`; Brundan, arXiv:1501.00350v1, Main Theorem; Khovanov–Lauda III,
  arXiv:0807.3250v1, Theorem 1.2, as a 2-representation on cyclotomic quotients).

The homogeneity hypothesis of `cyclotomicPresCL` comes from the presentation, not from the
cyclotomic family: `presCL` is written with Cautis–Lauda's homogeneous polynomials `qCL`, which
keep only the coefficients on the line. It is the setting of Khovanov–Lauda III, whose
2-category is graded over a field with `Q_ij` homogeneous of degree `-2 (i · j)`, so the statement
is not weaker than KL III's. Dropping it is a generalization to Kang–Kashiwara's graded base
rings; it requires a version of `presCL` with Brundan's unfiltered polynomials `brundanQ`
(issue #187).

The unit extremal coefficients enter in the form of the hypotheses `hlead`, `hdeg` of
`cyclotomicFamily` (`KLR.isUnit_extremalCoeff`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup KLRAlgebra.AbsentColour

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ, -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0)
  (hhom : ∀ i j, i ≠ j →
    (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j))

/-- The Cautis–Lauda scalars of `Q`. -/
abbrev cyclotomicScalars : KL3.Diagram.CL.CLScalars C k :=
  kkScalars C hQ fun _ _ h => isUnit_extremalCoeff C hQ hlead RD hdeg h

include hsupp in
/-- **Brundan's mixed upward relations for the cyclotomic family**, with the scalars of `Q`, for
every Kang–Kashiwara family `Q`. -/
theorem cyclotomicFamily_brundanUpKLR :
    BrundanUpKLR (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg)
      (cyclotomicScalars hQ hlead RD hdeg) :=
  (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg).of_eq fun _ _ h =>
    eq_brundanQ C hQ _ hsupp h

/-- **The Cautis–Lauda presentation acts on the weight spaces of the cyclotomic KLR algebras**
(Brundan, arXiv:1501.00350v1, Main Theorem; Khovanov–Lauda III, arXiv:0807.3250v1, Theorem 1.2
on cyclotomic quotients), for Kang–Kashiwara families `Q` with weighted homogeneous `Q_ij`.

The homogeneity hypothesis `hhom` is required by `presCL` (built on the homogeneous `qCL`), not by
the cyclotomic family (`cyclotomicFamily_brundanUpKLR` holds without it). It matches the setting of
Khovanov–Lauda III (graded, `Q_ij` homogeneous of degree `-2 (i · j)`). Removing it, for
Kang–Kashiwara's graded base rings, needs a version of `presCL` for Brundan's unfiltered `brundanQ`
(issue #187). -/
def cyclotomicPresCL :
    Pseudofunctor (RevBicat
      (KL3.Diagram.CL.presCL RD k (cyclotomicScalars hQ hlead RD hdeg)).Bicat)
      (LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) :=
  (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).presCLPseudofunctor
    (cyclotomicScalars hQ hlead RD hdeg)
    (cyclotomicFamily_brundanUpKLR hQ hlead ha RD Λ hΛ hdeg fun i j h =>
      coeff_eq_zero_of_lt_of_hom C (hhom i j h))
    (cyclotomicFamily_mixedInversion RD Λ hQ hlead ha hΛ hdeg) (fun _ => rfl)
    (kkScalars_s_eq_zero C hQ _ hhom)

end

end Categorification.KLR.CyclotomicAction
