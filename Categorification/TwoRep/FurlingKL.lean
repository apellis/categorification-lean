/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingFamily
import Categorification.TwoRep.RouqUpScalars
import Categorification.KLR.KL2.ScalarExtension

/-!
# KL scalar parameters for the furled family

Supporting Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action`: choose the existing crossing factors `klP2 C KL1.stdOrient`.
Their factorization, nonvanishing and weighted homogeneity are established by
`klQ2_eq_klP2`, `klP2_ne_zero` and `klP2_isWeightedHomogeneous`.

`Furling.brundanUpKLR_kl` proves Brundan's upward KL relations over `k` for a furled
action in `LinearCat L`, not just over `L`. The family can be `Furling.rouqFamilyOf`:
its defining data equality is `rouqFamilyOf_toRouqData`. The existing cover hypotheses
(nilpotent dots and vanishing of irrelevant edges) are unchanged. Construction of
KM3 and mixed inversion is separate; neither is asserted by the upward relation theorem.
`Furling.upEvalAtSemilinear` then evaluates the original k-presentation at an object.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits KLR KLR.Diagram
open KL3.Diagram

universe wk wL u₁ u₂ v₁ u₃ u₄

namespace Furling
variable {k : Type wk} [CommRing k] {L : Type wL} [Field L] [Algebra k L]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc]
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wL, v₁, u₂} L) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {D : Unfurling.UnfurlingDatum L (klP2 C KL1.stdOrient) J}
  (hπ : ∀ a, Φ.π a = D.π a)
  (H : RouqUpKLR S (Unfurling.unfQ (k := L) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  (T : RouqFamily (B := LinearCat.{wL, max u₁ v₁, max u₁ u₂} L) RD)
  (hT : T.toRouqData = rouqData Φ S D)

include hπ H hnil hzero hT in
/-- The standard KL crossing factorization gives KL upward relations for the furled family. -/
theorem rouqUpKLR_kl : RouqUpKLR T (klQ2 L C) :=
  rouqUpKLR hπ H hnil hzero (klQ2_eq_klP2 KL2.stdOrient_spec) T hT

attribute [local instance] ScalarRestriction.linearCatHom

include hπ H hnil hzero hT in
/-- Brundan's upward relations over the original ground ring, with scalar compatibility proved. -/
theorem brundanUpKLR_kl : BrundanUpKLR T (CL.CLScalars.kl : CL.CLScalars C k) :=
  (rouqUpKLR_kl hπ H hnil hzero T hT).brundan_kl_restrictScalars

/-- Semilinear evaluation at an object of the furled family. The only additional action
input is mixed inversion, as required by `RouqFamily.upEval`. -/
def upEvalAtSemilinear (M : BrundanMixedInversion T) (μ : X) (V : T.obj μ)
    {ν : Multiset I} {t t' : Seq ν} :
    ((pres RD k).obj (ob RD μ (ups (word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (word t')))) →ₛₗ[algebraMap k L]
      ((T.wordCell μ t).obj.obj V ⟶ (T.wordCell μ t').obj.obj V) :=
  T.upEvalAtSemilinear (rouqUpKLR_kl hπ H hnil hzero T hT) M μ V

end Furling
end Categorification.TwoRep
