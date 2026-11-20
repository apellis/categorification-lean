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
    (β : WeightBlocks RD Λ y)
    {F G : weightSpace.{u, v, w} Q a RD Λ y ⟶ weightSpace Q a RD Λ y}
    (η : F ⟶ G) : (blockEval RD Λ M β).map η = η.hom.app M β := rfl

variable (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/- Abbreviations for the block `{i} + γ`, its weight, the evaluation functors there and the
block-level and global Rouquier data, in terms of the variables of each statement below. -/
set_option hygiene false in
local notation "BS" => blockSucc RD Λ i h₁ γ
set_option hygiene false in
local notation "WB" => (-(RD.pair (RD.iY i) (Λ - ((BS).1.map RD.iX).sum)))
set_option hygiene false in
local notation "HE" => AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (BS).1)
  (D := blockCat.{u, v, w} Q a (BS).1) (M (BS))
set_option hygiene false in
local notation "BL" => blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i
  (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ (BS))
set_option hygiene false in
local notation "GLOC" => globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂
set_option hygiene false in
local notation "EV" => blockEval.{u, v, w} RD Λ M (BS)
set_option hygiene false in
local notation "SIG" => (RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
  (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M
    (BS)

/-- The inverse (1.9) of `blockLoc` at the block `{i} + γ`, evaluated and moved to the weight
space through the generators `capIso`, `cupIso` (as in `locNegInterior`). -/
def blockNegInv (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) (hB : WB ≤ 0) :
    SumInvFrom SIG
      (fun n => ((globalAdj.{u, v, w} Q a RD Λ i h₂).unit ≫
        powComp (globalDot Q a RD Λ i h₂) n ▷ globalF Q a RD Λ i h₂).hom.app M (BS))
      (-WB).toNat :=
  haveI : (HE).Additive := ⟨rfl⟩
  (((BL).iN hB).map (HE)).conj (cupIso Q a RD Λ i h₂ M (BS))
    (capIso Q a RD Λ i h₁ M γ).symm (Iso.refl _)
    ((Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) (sigma_app Q a RD Λ i h₁ h₂ M γ)))))
    (fun m => (cupD_app Q a RD Λ i h₂ M (BS) m).trans (Category.id_comp _).symm)

/-- The `♣`-caps of `globalLoc` at the block `{i} + γ` are those of `blockLoc`. -/
theorem globalLoc_iN_g'_app (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) {m : ℕ} (hm : m < (-RD.pair (RD.iY i) y).toNat) (hB : WB ≤ 0) :
    (((GLOC).iN hneg).g' m).hom.app M (BS) =
      (cupIso Q a RD Λ i h₂ M (BS)).inv ≫ (HE).map (((BL).iN hB).g' m) ≫ 𝟙 _ := by
  have hw := blockLoc_weight RD Λ i (BS)
  exact SumInvFrom.g'_eq (((GLOC).iN hneg).map (EV))
    ((blockNegInv RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M γ hB).congr rfl rfl (by rw [hw])) hm

/-- The inverse (1.8) of `blockLoc` at the block `{i} + γ`, evaluated and moved to the weight
space through the generators `capIso`, `cupIso` (as in `locPosInterior`). -/
def blockPosInv (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) (hB : 0 ≤ WB) :
    SumInvTo SIG
      (fun n => (globalF.{u, v, w} Q a RD Λ i h₁ ◁ powComp (globalDot Q a RD Λ i h₁) n ≫
        (globalAdj Q a RD Λ i h₁).counit).hom.app M (BS))
      (WB).toNat :=
  haveI : (HE).Additive := ⟨rfl⟩
  (((BL).ip hB).map (HE)).conj
    (capIso Q a RD Λ i h₁ M γ).symm (cupIso Q a RD Λ i h₂ M (BS)) (Iso.refl _)
    ((Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) (sigma_app Q a RD Λ i h₁ h₂ M γ)))))
    (fun m => (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((capD_app Q a RD Λ i h₁ M γ m).trans (Category.comp_id _).symm)))))

/-- The leftward crossing component of (1.8) for `globalLoc` at the block `{i} + γ` is that of
`blockLoc`. -/
theorem globalLoc_ip_f'_app (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) (hpos : 0 ≤ RD.pair (RD.iY i) y) (hB : 0 ≤ WB) :
    (EV).map ((GLOC).ip hpos).f' =
      (cupIso Q a RD Λ i h₂ M (BS)).inv ≫ (HE).map ((BL).ip hB).f' ≫
        (capIso Q a RD Λ i h₁ M γ).symm.inv := by
  have hw := blockLoc_weight RD Λ i (BS)
  exact SumInvTo.f'_eq (((GLOC).ip hpos).map (EV))
    ((blockPosInv RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M γ hB).congr rfl rfl (by rw [hw]))

/-- The dotted caps of `globalLoc` at the block `{i} + γ`. -/
theorem globalLoc_capD_app (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) (n : ℕ) :
    (EV).map ((GLOC).capD n) = (capIso Q a RD Λ i h₁ M γ).inv ≫ (HE).map ((BL).capD n) :=
  (Iso.eq_inv_comp _).mpr (capD_app Q a RD Λ i h₁ M γ n)

/-- **The leftward cap of the weight-space Rouquier data is the block one** (Brundan (1.15),
(1.17)) at an interior block `{i} + γ`, through the generator `cupIso` of `E_i F_i`. -/
theorem globalLoc_capL_app (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :
    (EV).map (GLOC).capL =
      (cupIso Q a RD Λ i h₂ M (BS)).inv ≫ (HE).map (BL).capL ≫ 𝟙 _ := by
  have hw := blockLoc_weight RD Λ i (BS)
  have : (HE).Additive := ⟨rfl⟩
  rcases lt_or_ge (RD.pair (RD.iY i) y) 0 with hh | hh
  · have hB : WB < 0 := by rw [hw]; exact hh
    rw [RouqLoc.capL_of_neg hh, RouqLoc.capL_of_neg hB, RouqLoc.capN, RouqLoc.capN,
      dite_eq_left hh.le, dite_eq_left hB.le]
    have hn : (-WB - 1).toNat = (-RD.pair (RD.iY i) y - 1).toNat := by rw [hw]
    rw [hn]
    exact globalLoc_iN_g'_app RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ hh.le M γ (by omega) hB.le
  · have hB : 0 ≤ WB := by rw [hw]; exact hh
    rw [RouqLoc.capL_of_nonneg hh, RouqLoc.capL_of_nonneg hB, RouqLoc.sigL_of_nonneg hh,
      RouqLoc.sigL_of_nonneg hB]
    have hn : (WB).toNat = (RD.pair (RD.iY i) y).toNat := by rw [hw]
    simp only [Preadditive.neg_comp, neg_neg]
    rw [Functor.map_comp, Functor.map_comp,
      globalLoc_ip_f'_app RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M γ hh hB,
      globalLoc_capD_app RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M γ, ← hn, Iso.symm_inv]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _))))).trans
      (congrArg (_ ≫ ·) (Category.comp_id _).symm)

end

end Categorification.KLR.CyclotomicAction
