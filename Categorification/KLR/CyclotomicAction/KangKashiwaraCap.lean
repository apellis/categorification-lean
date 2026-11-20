/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.KangKashiwara
import Categorification.TwoRep.RouqLocTransportCap

/-!
# Leftward cups and caps of the cyclotomic block data

The leftward cap and cup of `blockLoc` (Brundan, arXiv:1501.00350v1, (1.14)–(1.18)) are those
of `ConcreteAdjunction.loc`, conjugated by the comparison isomorphisms `indIsoA`, `resIsoA` of
`CyclotomicAction.Comparison`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep KLRAlgebra.AbsentColour

universe u v w

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- The leftward cap of `blockLoc` at the middle block `{i} + γ` is the leftward cap of
`ConcreteAdjunction.loc` precomposed with the comparison isomorphisms. -/
theorem blockLoc_capL (i : I) (γ : Multiset I) :
    (blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i (γ := γ) rfl rfl).capL =
      ((indIsoA Q a i ({i} + γ)).hom ▷ _ ≫ _ ◁ (resIsoA Q a i ({i} + γ)).hom) ≫
        (ConcreteAdjunction.loc.{u, v, w} Q i a γ hQ hlead ha RD Λ (hΛ i) (hdeg i)).capL :=
  AdditiveCat.transport_capL _ _ _ _ _ (unit_compat Q a i ({i} + γ))
    (counit_compat Q a i γ) (dot_compat Q a i γ) (dot_compat Q a i ({i} + γ))
    (cross_compat Q a i γ)

/-- The leftward cup of `blockLoc` at the middle block `{i} + γ`, followed by the comparison
isomorphisms, is the leftward cup of `ConcreteAdjunction.loc`. -/
theorem blockLoc_cupL (i : I) (γ : Multiset I) :
    (blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i (γ := γ) rfl rfl).cupL ≫
        ((resIsoA Q a i γ).hom ▷ _ ≫ _ ◁ (indIsoA Q a i γ).hom) =
      (ConcreteAdjunction.loc.{u, v, w} Q i a γ hQ hlead ha RD Λ (hΛ i) (hdeg i)).cupL :=
  AdditiveCat.transport_cupL _ _ _ _ _ (unit_compat Q a i ({i} + γ))
    (counit_compat Q a i γ) (dot_compat Q a i γ) (dot_compat Q a i ({i} + γ))
    (cross_compat Q a i γ)

end

end Categorification.KLR.CyclotomicAction
