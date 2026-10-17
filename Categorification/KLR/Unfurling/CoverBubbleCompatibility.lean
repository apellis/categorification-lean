/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverRouqFamily
import Categorification.KLR.Unfurling.CoverFurlingFibres
import Categorification.TwoRep.FurlingBubbleCompatibility

/-!
# Local generator compatibility for the cyclotomic cover

The signed-fibre construction of the Rouquier family and the combined-fibre
furling used by the vacuum have equal local generator data. This supplies the
compatibility required for the bubble evaluation in Webster,
arXiv:1603.06311v3, proof of `nondegenerate`.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open QuantumGroup QuantumGroup.UDot TwoRep CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
universe u v w u₄
variable {I : Type*} [DecidableEq I] {L : Type v} [Field L]
  {P : I → I → MvPolynomial (Fin 2) L}
  {Jm Jp : Type u} [DecidableEq Jm] [DecidableEq Jp]
  (D : UnfurlingDatum L P (Jm ⊕ Jp)) (Λm : Jm → ℕ) (Λp : Jp → ℕ)
  {C : CartanDatum I} {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X)
  (hΛm : ∀ i, ({a | D.π (.inl a) = i ∧ Λm a ≠ 0} : Set Jm).Finite) (hΛp : ∀ i, ({a | D.π (.inr a) = i ∧ Λp a ≠ 0} : Set Jp).Finite)
  (hD : NoCrossArrows D)
  (hμ : ∀ i, RD.pair (RD.iY i) μ = ∑ᶠ a : {a // D.π a = i}, coverBaseVal Λm Λp a.1)
  (hcover : ∀ (c : Jm ⊕ Jp) (i : I), i ≠ D.π c →
      ∑ᶠ a : {a // D.π a = i}, (((D.arrows a.1 c + D.arrows c a.1 : ℕ)) : ℤ) =
        -RD.pair (RD.iY i) (RD.iX (D.π c)))


variable {Q : I → I → MvPolynomial (Fin 2) L}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hΛ : ∀ i, {a | D.π a = i ∧ coverBaseVal Λm Λp a ≠ 0}.Finite)


attribute [local irreducible] coverProduct

/-- Signed-fibre and combined-fibre presentations have the same local generators. -/
theorem coverRouqFamily_localData_eq (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    (coverRouqFamily.{u, v, w} D Λm Λp RD μ hΛm hΛp hD hμ hcover hPQ).localData i h₁ h₂ =
      (coverFurlingOfFibreFinite D Λm Λp RD μ hΛ).localData
        (coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp) D i h₁ h₂ := by
  exact Furling.rouqFamilyOfPairing_localData
    (S := coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp)
    (Φ := coverFurling D Λm Λp RD μ hΛm hΛp) (D := D)
    (hπ := fun _ => rfl) (H := coverProduct_upKLR_unfQ D Λm Λp hD)
    (hnil := coverProduct_dot_isNilpotent D Λm Λp) (hPQ := hPQ)
    (hzero := fun β a _ h hr => (coverFurling_isZero D Λm Λp RD μ hΛm hΛp β a h hr).1)
    (hmix := Furling.sameColour_mixedInversion _ D (coverProduct_upKLR_unfQ D Λm Λp hD)
      (coverProduct_mixedInversion (arrowsNeg D) Λm (arrowsPos D) Λp)
      (coverProduct_dot_isNilpotent D Λm Λp) D.π (fun _ => rfl))
    (hpairOrZero := fun i β => by
      classical
      by_cases hβ : CoverAdm β
      · exact Or.inl (coverFurling_pair_lab D Λm Λp RD μ hΛm hΛp hD hμ hcover i β hβ)
      · exact Or.inr (coverFurling_isZero_obj D Λm Λp RD μ hΛm hΛp β hβ)) i h₁ h₂

end Categorification.KLR.Unfurling
