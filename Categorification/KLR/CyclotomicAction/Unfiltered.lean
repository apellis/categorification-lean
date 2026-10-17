/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.PresCL
import Categorification.TwoRep.RouqUnfilteredDescent

/-!
# The unfiltered presentation acts on cyclotomic KLR modules

Kang–Kashiwara, arXiv:1102.4677v4, (3.1), §4.2 and Theorem 5.2;
Brundan, arXiv:1501.00350v1, Definition 1.1 and cyclicity (1.26).
The existing cyclotomic family gives a pseudofunctor from `presUnfiltered`
without weighted homogeneity of the polynomials. Its coefficient hypothesis
is vanishing strictly above the weighted line, not vanishing off that line.

The target is the existing ungraded category of modules on each cyclotomic
weight space. Induction, restriction and all generator images are unchanged.
The unit-leading-coefficient and degree hypotheses are exactly those of
`cyclotomicFamily`; mixed inversion is proved, not supplied as an assumption.
This is before additive completion, and does not assert redundancy of the
separately added downward presentation or an equivalence of presentations.

The old homogeneous `cyclotomicPresCL` API is retained. Under homogeneity,
`cyclotomic_presUnfiltered_eq_presCL` identifies the source presentations;
the representative formulas for the two actions use the same `genImg`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup KLRAlgebra.AbsentColour
open KL3.Diagram StringDiagrams Diagrams.BicatInterp

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ, -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0)

/-- The normalized unfiltered presentation acts on cyclotomic weight spaces for
KK (3.1) polynomials, without weighted homogeneity. -/
def cyclotomicPresUnfiltered :
    Pseudofunctor (RevBicat
      (CL.presUnfiltered RD k (cyclotomicScalars hQ hlead RD hdeg)).Bicat)
      (LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) :=
  (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).presUnfilteredPseudofunctor
    (cyclotomicScalars hQ hlead RD hdeg)
    (cyclotomicFamily_brundanUpKLR hQ hlead ha RD Λ hΛ hdeg hsupp)
    (cyclotomicFamily_mixedInversion RD Λ hQ hlead ha hΛ hdeg) (fun _ => rfl)

/-- Every linear representative is interpreted by the existing cyclotomic
induction/restriction generator model. -/
@[simp] theorem cyclotomicPresUnfiltered_map₂_lin
    {s t : RevBicat (CL.presUnfiltered RD k (cyclotomicScalars hQ hlead RD hdeg)).Bicat}
    {x y : s ⟶ t} (f : LinDiagram k x.obj y.obj) :
    (cyclotomicPresUnfiltered.{u, v, w} hQ hlead ha RD Λ hΛ hdeg hsupp).map₂
      ((CL.presUnfiltered RD k (cyclotomicScalars hQ hlead RD hdeg)).lin f : x ⟶ y) =
    admissibleMap
      ((cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).genImg
        (cyclotomicScalars hQ hlead RD hdeg))
      (PresPseudo.condW x) (PresPseudo.condW y) f := rfl

variable (hhom : ∀ i j, i ≠ j →
  (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j))

include hhom in
/-- For homogeneous polynomials the new source is the old CL presentation. -/
theorem cyclotomic_presUnfiltered_eq_presCL :
    CL.presUnfiltered RD k (cyclotomicScalars hQ hlead RD hdeg) =
      CL.presCL RD k (cyclotomicScalars hQ hlead RD hdeg) :=
  CL.presUnfiltered_eq_presCL RD k _ (kkScalars_s_eq_zero C hQ _ hhom)

/-- The retained homogeneous action uses the same map on linear representatives
as the unfiltered action; its extra premise belongs to the source presentation. -/
@[simp] theorem cyclotomicPresCL_map₂_lin
    {s t : RevBicat (CL.presCL RD k (cyclotomicScalars hQ hlead RD hdeg)).Bicat}
    {x y : s ⟶ t} (f : LinDiagram k x.obj y.obj) :
    (cyclotomicPresCL.{u, v, w} hQ hlead ha RD Λ hΛ hdeg hhom).map₂
      ((CL.presCL RD k (cyclotomicScalars hQ hlead RD hdeg)).lin f : x ⟶ y) =
    admissibleMap
      ((cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).genImg
        (cyclotomicScalars hQ hlead RD hdeg))
      (PresPseudo.condW x) (PresPseudo.condW y) f := rfl

end

end Categorification.KLR.CyclotomicAction
