/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixedInversion
import Categorification.TwoRep.FurlingMixed

/-!
# Discarded mixed paths and the same-colour mixed matrix

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action`; Brundan, arXiv:1501.00350v1, (1.7).

Cover mixed inversion identifies the two mixed words even if an edge of the
opposite path is irrelevant. Vanishing of that edge therefore forces the
whole mixed summand to vanish. The lemmas apply to arbitrary distinct cover
labels, not only to labels over one base colour.

`isIso_mixed_of_cover` also discharges the cover-level hypothesis of the
same-colour mixed submatrix, including its discarded-path summands. It does
not assert distinct-base-colour mixed inversion for the whole furled action.
-/

noncomputable section
namespace Categorification.TwoRep.Furling
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
universe wk v₁ u₁ u₂ u₃ u₄
variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc]
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)

omit [DecidableEq I] [DecidableEq J] in
/-- If either edge of the opposite mixed word is zero, the source word is zero.
This is the discarded-path implication; the source edges need not vanish. -/
theorem mixed_source_zero_of_dropped (hmix : BrundanMixedInversion S)
    {a b : J} (hab : a ≠ b) {x y y' z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z)
    (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z)
    (hz : IsZero (S.E b h₂) ∨ IsZero (S.E a h₄)) (M : (S.obj y' : Type u₂)) :
    IsZero ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) := by
  have := hmix b a hab.symm h₁ h₂ h₃ h₄
  have ht : IsZero ((S.F b h₂).obj.obj ((S.E a h₄).obj.obj M)) := by
    rcases hz with hb | ha
    · exact isZero_F_of_isZero_E h₂ hb _
    · exact Functor.map_isZero (S.F b h₂).obj
        (Functor.map_isZero (LinearCat.evalAt M) ha)
  let e := asIso ((S.mixedSigma b a h₁ h₂ h₃ h₄).hom.app M)
  exact ht.of_iso e

omit [DecidableEq I] [DecidableEq J] in
/-- Conversely a mixed target whose opposite path has a zero edge is zero. -/
theorem mixed_target_zero_of_dropped (hmix : BrundanMixedInversion S)
    {a b : J} (hab : a ≠ b) {x y y' z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z)
    (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z)
    (hz : IsZero (S.E a h₁) ∨ IsZero (S.E b h₃)) (M : (S.obj y' : Type u₂)) :
    IsZero ((S.F b h₂).obj.obj ((S.E a h₄).obj.obj M)) := by
  have := hmix b a hab.symm h₁ h₂ h₃ h₄
  have hs : IsZero ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) := by
    rcases hz with ha | hb
    · exact Functor.map_isZero (LinearCat.evalAt _) ha
    · exact Functor.map_isZero (S.E a h₁).obj (isZero_F_of_isZero_E h₃ hb M)
  exact hs.of_iso (asIso ((S.mixedSigma b a h₁ h₂ h₃ h₄).hom.app M)).symm

variable (Φ : Furling RDc RD)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k}
  (D : KLR.Unfurling.UnfurlingDatum k P J)
  (H : RouqUpKLR S (KLR.Unfurling.unfQ (k := k) D.arrows))
  (hmix : BrundanMixedInversion S)
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hπ : ∀ a, Φ.π a = D.π a)
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))

include H hmix hnil hπ hzero in
/-- The same-colour mixed submatrix is invertible using only cover relations.
This discharges its cover-level mixed-crossing hypothesis and includes all
summands outside the relevant-path graph. It is not distinct-base-colour U3. -/
theorem isIso_mixed_of_cover {i : I} {l l' l'' : X}
    (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
    (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l') :
    IsIso (matrixW fun x y =>
      sM h₁ N δ x ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rM' h₂ N δ y) :=
  isIso_mixed D h₁ h₂ N δ hzero
    (sameColour_mixedInversion S D H hmix hnil Φ.π hπ)

end Categorification.TwoRep.Furling
