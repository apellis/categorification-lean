/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingKLR

/-!
# Furling: the Rouquier family of `g`

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`: the 1-morphisms, adjunctions, dots and crossings of `g` built from a
Rouquier family `S̃` of the cover `g̃` (`Furling.rouqData`, `Furling.adj`) satisfy the KLR
relations (`Furling.respectsKLR`). With the inverses of Rouquier's maps for `g` (J. Brundan,
*On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, (1.8) and (1.9)), they form a
Rouquier family of `g` (`Furling.rouqFamilyOf`), by `RouqData.RespectsKLR.toRouqFamily`.

`Furling.rouqFamilyOf` takes these inverses as hypotheses (`invPos`, `invNeg`). This is an
intermediate statement: in Webster's proof they come from the coproduct theorem
(`th:coproduct`, `RouqCoproduct.isIso_rouqMap_of_nonneg`, `isIso_rouqMap_of_nonpos`) on each
block, after reparametrizing the dots of each label (`RouqLoc.reparam`).

## Main definitions

* `Furling.rouqFamilyOf`: the Rouquier family of `g`, given the inverses of Rouquier's maps;
  its Rouquier data are `Furling.rouqData` (`Furling.rouqFamilyOf_toRouqData`), its right
  adjoints `Furling.F` and its adjunctions `Furling.adj`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits KLR KLR.Diagram

universe u₁ u₂ v₁ wk u₃ u₄

namespace Furling

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} {D : KLR.Unfurling.UnfurlingDatum k P J}
  (hπ : ∀ a, Φ.π a = D.π a)
  (H : RouqUpKLR S (Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  {Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))

variable
  (invPos : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
    0 ≤ RD.pair (RD.iY i) b →
    SumInvTo (RightwardCrossing.sigma (adj Φ S i h₂).unit
        ((rouqData Φ S D).cross i i h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit)
      (fun n => F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫ (adj Φ S i h₁).counit)
      (RD.pair (RD.iY i) b).toNat)
  (invNeg : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
    RD.pair (RD.iY i) b ≤ 0 →
    SumInvFrom (RightwardCrossing.sigma (adj Φ S i h₂).unit
        ((rouqData Φ S D).cross i i h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit)
      (fun n => (adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) n ▷ F Φ S i h₂)
      (-RD.pair (RD.iY i) b).toNat)

/-- **The Rouquier family of `g`** (Webster, arXiv:1603.06311v3, §2.3, `lem:g-action`), given
the inverses of Rouquier's maps for `g` (Brundan, arXiv:1501.00350v1, (1.8), (1.9)) as the
hypotheses `invPos`, `invNeg`: the Rouquier data `Furling.rouqData` with the right adjoints
`Furling.F` and the adjunctions `Furling.adj`. The KLR relations are `Furling.respectsKLR`,
under the hypotheses of the cover (`hπ`, `H`, `hnil`, `hzero`, `hPQ`). -/
def rouqFamilyOf : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD :=
  (respectsKLR hπ H hnil hzero hPQ).toRouqFamily (fun i _ _ h => F Φ S i h)
    (fun i _ _ h => adj Φ S i h) invPos invNeg

theorem rouqFamilyOf_toRouqData :
    (rouqFamilyOf hπ H hnil hzero hPQ invPos invNeg).toRouqData = rouqData Φ S D :=
  rfl

theorem rouqFamilyOf_F (i : I) {l l' : X} (h : l + RD.iX i = l') :
    (rouqFamilyOf hπ H hnil hzero hPQ invPos invNeg).F i h = F Φ S i h :=
  rfl

theorem rouqFamilyOf_adj (i : I) {l l' : X} (h : l + RD.iX i = l') :
    (rouqFamilyOf hπ H hnil hzero hPQ invPos invNeg).adj i h = adj Φ S i h :=
  rfl

end Furling

end Categorification.TwoRep
