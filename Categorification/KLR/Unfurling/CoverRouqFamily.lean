/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingZero
import Categorification.TwoRep.FurlingKM3
import Categorification.KLR.Unfurling.CoverFurling
import Categorification.KLR.Unfurling.FurlingVacuum
import Categorification.TwoRep.FurlingMixedInversion

/-!
# The Rouquier family of the furled cyclotomic cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
§2.3, Theorem `th:coproduct` and Lemma `lem:g-action`;
J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Definition 1.1, (1.8)–(1.9).

`coverRouqFamily` constructs the family on the categories and generator maps of
`coverFurling` applied to `coverProduct`. Neither the shift-zero block inverses nor
same-base-colour mixed inversion are inputs. The latter uses distinct cover labels
with the *same* image under `π`, via `Furling.sameColour_mixedInversion`.

The correction count is `coverFurling_pair_lab` on admissible blocks; on other
blocks all objects are zero. Thus no pairing identity is required on a zero block.
Nilpotence and omitted-edge vanishing come from the cyclotomic cover construction.

The structural inputs remain explicit: finite support of `Λm`, `Λp`, no arrows
between the two signed components, the base-weight and off-fibre Cartan pairing
identities, and `Q = Pᵒᵖ P`. Specializing these inputs to the generic KL spectral
cover and constructing `UnfurledEval` are separate from this family construction.
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
  (hΛm : (Function.support Λm).Finite) (hΛp : (Function.support Λp).Finite)
  (hD : NoCrossArrows D)
  (hμ : ∀ i, RD.pair (RD.iY i) μ = ∑ᶠ a : {a // D.π a = i}, coverBaseVal Λm Λp a.1)
  (hcover : ∀ (c : Jm ⊕ Jp) (i : I), i ≠ D.π c →
      ∑ᶠ a : {a // D.π a = i}, (((D.arrows a.1 c + D.arrows c a.1 : ℕ)) : ℤ) =
        -RD.pair (RD.iY i) (RD.iX (D.π c)))


omit [DecidableEq I] in
include hD hμ hcover in
/-- The cover pairing identity on precisely the finite label indexing of the shift-zero block. -/
theorem coverFurling_pair_lab (i : I) (β : Jm ⊕ Jp →₀ ℤ) (hβ : CoverAdm β) :
    RD.pair (RD.iY i) ((coverFurling D Λm Λp RD μ hΛm hΛp).wtG β) =
      ∑ t : Fin (Furling.nLbl (coverFurling D Λm Λp RD μ hΛm hΛp) i β),
        (coverProdWeight D).pair ((coverProdWeight D).iY
          (Furling.lab (coverFurling D Λm Λp RD μ hΛm hΛp) i β t))
          ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β) := by
  classical
  let A := Finset.univ.image (Furling.lab (coverFurling D Λm Λp RD μ hΛm hΛp) i β)
  have hA : ∀ a ∈ A, D.π a = i := by
    intro a ha
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
    exact Furling.lab_π β t
  have hA' : ∀ a, D.π a = i → coverRel D Λm Λp β a ∨
      coverRel D Λm Λp (β - Finsupp.single a 1) a → a ∈ A := by
    intro a ha hr
    exact Finset.mem_image.mpr ⟨Furling.labIdx β a ha hr.symm, Finset.mem_univ _,
      Furling.lab_labIdx β a ha hr.symm⟩
  have H := coverFurling_pair D Λm Λp RD μ hΛm hΛp hD hμ hcover β hβ i A hA hA'
  rw [Finset.sum_image (fun a _ b _ h => Furling.lab_injective β h)] at H
  exact H

omit [DecidableEq I] in
/-- Nilpotence of the actual cover-product dots, in endomorphism-ring form. -/
theorem coverProduct_dot_isNilpotent :
    ∀ (a : Jm ⊕ Jp) {x y} (h : x + (coverProdWeight D).iX a = y),
      IsNilpotent (End.of ((coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp).dot a h)) := by
  intro a x y h
  obtain ⟨n, hn⟩ := coverProduct_dot_nilpotent.{u, v, w} (L := L) (arrowsNeg D) Λm (arrowsPos D) Λp a h
  exact ⟨n, by simpa only [powComp_eq_pow'] using hn⟩

/-- The Rouquier family of the furled cyclotomic cover product (Webster,
arXiv:1603.06311v3, §2.3, `lem:g-action`). The shift-zero inverses, mixed inverses,
nilpotence and omitted-edge vanishing are all constructed, not assumed.
The finite support, base-weight and branched-cover pairing inputs are explicit. -/
def coverRouqFamily {Q : I → I → MvPolynomial (Fin 2) L}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b)) :=
  Furling.rouqFamilyOfPairing
    (S := coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp)
    (Φ := coverFurling D Λm Λp RD μ hΛm hΛp) (D := D)
    (fun β a _ h hr => (coverFurling_isZero D Λm Λp RD μ hΛm hΛp β a h hr).1)
    (Furling.sameColour_mixedInversion _ D (coverProduct_upKLR_unfQ D Λm Λp hD)
      (coverProduct_mixedInversion (arrowsNeg D) Λm (arrowsPos D) Λp)
      (coverProduct_dot_isNilpotent D Λm Λp) D.π (fun _ => rfl))
    (fun _ => rfl) (coverProduct_upKLR_unfQ D Λm Λp hD)
    (coverProduct_dot_isNilpotent D Λm Λp) hPQ
    (fun i β => by
      classical
      by_cases hβ : CoverAdm β
      · exact Or.inl (coverFurling_pair_lab D Λm Λp RD μ hΛm hΛp hD hμ hcover i β hβ)
      · exact Or.inr (coverFurling_isZero_obj D Λm Λp RD μ hΛm hΛp β hβ))

/-- The constructed family has exactly the furled dot and crossing data. -/
theorem coverRouqFamily_toRouqData {Q : I → I → MvPolynomial (Fin 2) L}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b)) :
    (coverRouqFamily.{u, v, w} D Λm Λp RD μ hΛm hΛp hD hμ hcover hPQ).toRouqData =
      Furling.rouqData (coverFurling D Λm Λp RD μ hΛm hΛp)
        (coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp) D := rfl

end Categorification.KLR.Unfurling
