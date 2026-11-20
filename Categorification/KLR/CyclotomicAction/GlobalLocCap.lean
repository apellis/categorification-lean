/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalLoc
import Categorification.KLR.CyclotomicAction.KangKashiwaraCap
import Categorification.TwoRep.SumInvUnique

/-!
# The leftward cap of the weight-space Rouquier data

On a block `{i} + γ` of a weight space, the leftward cap of `globalLoc` (Brundan,
arXiv:1501.00350v1, (1.15), (1.17)) is the leftward cap of `blockLoc`, through the generator
`cupIso` of `E_i F_i` at that block (`globalLoc_capL_app`). The inverses of Rouquier's maps are
unique (`TwoRep.SumInvFrom.g'_eq`, `TwoRep.SumInvTo.f'_eq`), so the comparison does not depend
on how `globalLoc` assembles them from the blocks.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory TwoRep QuantumGroup
  KLRAlgebra.AbsentColour

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)

/-- Evaluation of an endomorphism of a weight space at an object and a block. -/
def blockEval {y : X}
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) :
    (weightSpace.{u, v, w} Q a RD Λ y ⟶ weightSpace Q a RD Λ y) ⥤
      ModuleCat.{max (max u v) w} (CycKLR k Q a β.1) :=
  LinearCat.homForget _ _ ⋙ (evaluation _ _).obj M ⋙ Pi.eval _ β

instance {y : X}
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) : (blockEval.{u, v, w} RD Λ M β).Additive :=
  ⟨rfl⟩

@[simp] theorem blockEval_map {y : X}
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) {F G : weightSpace.{u, v, w} Q a RD Λ y ⟶ weightSpace Q a RD Λ y}
    (η : F ⟶ G) : (blockEval RD Λ M β).map η = η.hom.app M β := rfl

variable (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- The inverse (1.9) of `blockLoc` at the block `{i} + γ`, evaluated and moved to the weight
space through the generators `capIso`, `cupIso` (as in `locNegInterior`). -/
def blockNegInv (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x)
    (hB : -(RD.pair (RD.iY i) (Λ - ((blockSucc RD Λ i h₁ γ).1.map RD.iX).sum)) ≤ 0) :
    SumInvFrom ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M
        (blockSucc RD Λ i h₁ γ))
      (fun n => ((globalAdj.{u, v, w} Q a RD Λ i h₂).unit ≫
        powComp (globalDot Q a RD Λ i h₂) n ▷ globalF Q a RD Λ i h₂).hom.app M
          (blockSucc RD Λ i h₁ γ))
      (-(-(RD.pair (RD.iY i) (Λ - ((blockSucc RD Λ i h₁ γ).1.map RD.iX).sum)))).toNat :=
  haveI : (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
        (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
        (M (blockSucc RD Λ i h₁ γ))).Additive := ⟨rfl⟩
  (((blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i (blockSucc_step RD Λ i h₁ γ)
      (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).iN hB).map
    (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
      (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
      (M (blockSucc RD Λ i h₁ γ)))).conj (cupIso Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ))
    (capIso Q a RD Λ i h₁ M γ).symm (Iso.refl _)
    ((Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (sigma_app Q a RD Λ i h₁ h₂ M γ)))))
    (fun m => (cupD_app Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ) m).trans
      (Category.id_comp _).symm)

/-- The `♣`-caps of `globalLoc` at the block `{i} + γ` are those of `blockLoc`. -/
theorem globalLoc_iN_g'_app (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) {m : ℕ} (hm : m < (-RD.pair (RD.iY i) y).toNat)
    (hB : -(RD.pair (RD.iY i) (Λ - ((blockSucc RD Λ i h₁ γ).1.map RD.iX).sum)) ≤ 0) :
    (((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).iN hneg).g' m).hom.app M
        (blockSucc RD Λ i h₁ γ) =
      (cupIso Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ)).inv ≫
        (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
          (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1) (M (blockSucc RD Λ i h₁ γ))).map
          (((blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i (blockSucc_step RD Λ i h₁ γ)
            (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).iN hB).g' m) ≫ 𝟙 _ := by
  have hw := blockLoc_weight RD Λ i (blockSucc RD Λ i h₁ γ)
  exact SumInvFrom.g'_eq
    (((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).iN hneg).map
      (blockEval.{u, v, w} RD Λ M (blockSucc RD Λ i h₁ γ)))
    ((blockNegInv RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M γ hB).congr rfl rfl (by rw [hw])) hm

end

end Categorification.KLR.CyclotomicAction
