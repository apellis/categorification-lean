/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqDerivedBlockQ
import Categorification.WeightedKLR.RedStrands.BlackRouqSlides
import Categorification.WeightedKLR.RedStrands.BlackRouqWeight
import Categorification.KLR.CyclotomicAction.GlobalLoc

/-!
# Rouquier's local data for Webster's functors on derived categories of `T^λ`-modules

Rouquier's local data (`TwoRep.RouqLoc`; Brundan, arXiv:1501.00350v1, (1.2), (1.8), (1.9)) for
the weight-indexed generators `blackRouqData` of Webster's derived action (arXiv:1309.3796v3,
§4.6, §5.1, Theorem 4.31), at a weight `y` with Brundan weight `⟨h_i, y⟩`: `blackRouqLoc`.

As in the cyclotomic case (`KLR.CyclotomicAction.globalLoc`), the rightward crossing, the dotted
caps and the dotted cups on a weight space are block diagonal (`blackRouq_sigma_app`,
`blackRouq_capD_app`, `blackRouq_cupD_app`). On a block `{i} + γ` the inverses are the derived
ones of `derivedBlackSumInvToQ`/`FromQ`; on a block without a strand of colour `i`, `Fᵢ Eᵢ`
vanishes and the inverses come from the dotted units (`blackModuleSumInvFromOfNotMemQ`,
`blackDerivedCoeff`).

The weight `Λ₀` of `blackRouqData` is tied to the red labels `Λ` by the hypothesis
`hΛ₀ : ∀ i, ⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` (`pair_blockWeight_eq_neg_ip`); for the coordinate weight datum
it holds with `Λ₀ = coordinateHighest Λ C` (`pair_coordinateHighest`). The presentation `P` is
subject to the hypotheses of Webster's Theorem 4.30 in the library: negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory QuantumGroup
  QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram
  NatTrans

open scoped Classical

universe u w w₂ u₁

variable {I : Type u} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : IsRouquierQ C Q)
  [∀ β : Multiset I,
    HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ₀ : X)

set_option hygiene false in
local notation "D" β => DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

/-- Composition in a product of categories, componentwise. -/
theorem pi_comp_apply_blocks {J : Type*} {Cs : J → Type*}
    [∀ j, Category (Cs j)] {A B E : ∀ j, Cs j} (f : A ⟶ B) (g : B ⟶ E) (j : J) :
    (f ≫ g) j = f j ≫ g j := rfl

theorem blackRouqAdj_unit_app (i : I) {y z : X} (h : y + RD.iX i = z)
    (N : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :
    (blackRouqAdj Λ hQ RD Λ₀ i h).unit.hom.app N β =
      (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h β)).unit.app (N β) ≫
        (derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map
          (blockι (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h) N ⟨β, rfl⟩) := rfl

/-- **The dotted cups on weight spaces, blockwise.** -/
theorem blackRouq_cupD_app (i : I) {y z : X} (h : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) (m : ℕ) :
    ((blackRouqAdj Λ hQ RD Λ₀ i h).unit ≫
        powComp (blackRouqDot Λ hQ RD Λ₀ i h) m ▷ blackRouqF Q Λ RD Λ₀ i h).hom.app M β =
      ((derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h β)).unit ≫
          Functor.whiskerRight (powComp (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h β)) m)
            (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))).app (M β) ≫
        (derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map
          (blockι (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h) M ⟨β, rfl⟩) := by
  have t1 : (blackRouqAdj Λ hQ RD Λ₀ i h).unit.hom.app M β =
      (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h β)).unit.app (M β) ≫
      (derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map
        (blockι (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h) M ⟨β, rfl⟩) := rfl
  have t2 : (powComp (blackRouqDot Λ hQ RD Λ₀ i h) m ▷ blackRouqF Q Λ RD Λ₀ i h).hom.app M β =
      (derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map
        ((powComp (blackRouqDot Λ hQ RD Λ₀ i h) m).hom.app M (blockSucc RD Λ₀ i h β)) := rfl
  have t3 : ((blackRouqAdj Λ hQ RD Λ₀ i h).unit ≫
        powComp (blackRouqDot Λ hQ RD Λ₀ i h) m ▷ blackRouqF Q Λ RD Λ₀ i h).hom.app M β =
      (blackRouqAdj Λ hQ RD Λ₀ i h).unit.hom.app M β ≫
        (powComp (blackRouqDot Λ hQ RD Λ₀ i h) m ▷ blackRouqF Q Λ RD Λ₀ i h).hom.app M β := rfl
  rw [t3, t1, t2, NatTrans.comp_app, Functor.whiskerRight_app, LinearCat.powComp_hom]
  simp only [Category.assoc]
  have key := blockι_powComp_blockSumMap (blockSucc RD Λ₀ i h)
    (fun _ _ hβ => derivedIndDotOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ)) M ⟨β, rfl⟩ m
  exact congrArg (_ ≫ ·) (((derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map_comp _ _).symm.trans
    ((congrArg (derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map key).trans
      ((derivedEBlock Q Λ RD Λ₀ i h β _ rfl).map_comp _ _)))

/-- **The dotted caps on weight spaces, blockwise**, on the generator of `Fᵢ Eᵢ` at the block
`{i} + γ`. -/
theorem blackRouq_capD_app (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) (m : ℕ) :
    blockι (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h)
        ((blackRouqF Q Λ RD Λ₀ i h).obj.obj M) ⟨γ, rfl⟩ ≫
      (blackRouqF Q Λ RD Λ₀ i h ◁ powComp (blackRouqDot Λ hQ RD Λ₀ i h) m ≫
        (blackRouqAdj Λ hQ RD Λ₀ i h).counit).hom.app M (blockSucc RD Λ₀ i h γ) =
      (Functor.whiskerLeft (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h γ))
          (powComp (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h γ)) m) ≫
        (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h γ)).counit).app
          (M (blockSucc RD Λ₀ i h γ)) := by
  change _ ≫ (powComp (blackRouqDot Λ hQ RD Λ₀ i h) m).hom.app
      ((blackRouqF Q Λ RD Λ₀ i h).obj.obj M) (blockSucc RD Λ₀ i h γ) ≫ biproduct.desc _ =
    (powComp (derivedIndDotOfEq Λ hQ i (blockSucc_step RD Λ₀ i h γ)) m).app _ ≫
      (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h γ)).counit.app (M (blockSucc RD Λ₀ i h γ))
  rw [LinearCat.powComp_hom]
  have key := blockι_powComp_blockSumMap (blockSucc RD Λ₀ i h)
    (fun _ _ hβ => derivedIndDotOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ))
    ((blackRouqF Q Λ RD Λ₀ i h).obj.obj M) ⟨γ, rfl⟩ m
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (biproduct.ι_desc _ _))))

/-- The generator of `Fᵢ Fᵢ` on `Fᵢ Eᵢ` followed by the counit. -/
theorem blackRouq_gen₂_counit (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    Eq (gen₂ (b := blockSucc RD Λ₀ i h₁ γ) (d := blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))
        (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₁)
        (derivedFBlock Λ hQ RD Λ₀ i h₂)
        ((blockRes (blockSucc RD Λ₀ i h₁) (derivedEBlock Q Λ RD Λ₀ i h₁)).obj M) γ rfl rfl ≫
      (TwoRep.blockSum (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₂)).map
        ((blockCounitNat (blockSucc RD Λ₀ i h₁)
          (fun _ _ hβ => derivedAdjOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ))).app M)
        (blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)))
      ((derivedFBlock Λ hQ RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)
          (blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)) rfl).map
          ((derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ)).counit.app
            (M (blockSucc RD Λ₀ i h₁ γ))) ≫
        blockι (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₂) M
          ⟨blockSucc RD Λ₀ i h₁ γ, rfl⟩) := by
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact biproduct.ι_desc _ _

/-- **The rightward crossing on weight spaces, blockwise**: on the generator of `Fᵢ Eᵢ` at the
block `{i} + γ`, it is the rightward crossing of the derived block functors at `{i} + γ`,
followed by the generator of `Eᵢ Fᵢ`. -/
theorem blackRouq_sigma_app (hsym : KLRSymm Q) (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z) (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    Eq (blockι (blockSucc RD Λ₀ i h₁) (derivedFBlock Λ hQ RD Λ₀ i h₁)
        ((blockRes (blockSucc RD Λ₀ i h₁) (derivedEBlock Q Λ RD Λ₀ i h₁)).obj M) ⟨γ, rfl⟩ ≫
      (RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      ((functorSigma
          (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))).unit
          (derivedIndCrossOfEq Λ hQ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
            (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)) (blockSucc_step RD Λ₀ i h₁ γ)
            (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)))
          (derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₁ γ)).counit).app
            (M (blockSucc RD Λ₀ i h₁ γ)) ≫
        (derivedEBlock Q Λ RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ) _ rfl).map
          (blockι (blockSucc RD Λ₀ i h₂) (derivedFBlock Λ hQ RD Λ₀ i h₂) M
            ⟨blockSucc RD Λ₀ i h₁ γ, rfl⟩)) := by
  rw [LinearCat.sigma_hom]
  have hU := (derivedAdjOfEq Λ hQ i
      (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))).unit_naturality
    (blockι (blockSucc RD Λ₀ i h₁) (derivedFBlock Λ hQ RD Λ₀ i h₁)
        ((blockRes (blockSucc RD Λ₀ i h₁) (derivedEBlock Q Λ RD Λ₀ i h₁)).obj M) ⟨γ, rfl⟩)
  have hT := gen₂_blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂
    ((blockRes (blockSucc RD Λ₀ i h₁) (derivedEBlock Q Λ RD Λ₀ i h₁)).obj M) γ rfl rfl rfl rfl
  have hC := blackRouq_gen₂_counit Λ hQ RD Λ₀ i h₁ h₂ M γ
  have key := (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    pi_comp_apply_blocks, blackRouqAdj_unit_app]
  simp only [Category.assoc]
  erw [← reassoc_of% hU]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  have key' := congrArg
    (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))).map key
  erw [key']
  simp only [Functor.map_comp, functorSigma_app, Category.assoc]

/-- The generator of `Fᵢ Eᵢ` at the block `{i} + γ`, as an isomorphism. -/
def blackRouqCapIso (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :=
  blockιIso (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h)
    ((blockRes (blockSucc RD Λ₀ i h) (derivedEBlock Q Λ RD Λ₀ i h)).obj M) ⟨γ, rfl⟩
    fun _ => Subsingleton.elim _ _

/-- The generator of `Eᵢ Fᵢ` at the block `β`, as an isomorphism. -/
def blackRouqCupIso (i : I) {y z : X} (h : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :=
  (derivedEBlock Q Λ RD Λ₀ i h β _ rfl).mapIso
    (blockιIso (blockSucc RD Λ₀ i h) (derivedFBlock Λ hQ RD Λ₀ i h) M ⟨β, rfl⟩
      fun _ => Subsingleton.elim _ _)

local notation "RDc" => coordinateDatum Λ C

section Loc

variable {Λ hQ RD Λ₀} {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom) (hsym : KLRSymm Q)
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))

include hΛ₀ in
/-- The Brundan weight of a weight space is minus the coordinate pairing of each of its
blocks. -/
theorem blackRouq_pair_eq (i : I) {y : X} (β : WeightBlocks RD Λ₀ y) :
    RD.pair (RD.iY i) y =
      -ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1) := by
  obtain ⟨β, rfl⟩ := β
  exact pair_blockWeight_eq_neg_ip Λ C RD Λ₀ hΛ₀ i β

include hP hwf hΛ₀ in
/-- Brundan (1.8) on the weight space at `y`, at a block `{i} + γ`. -/
def blackRouqLocPosInterior (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z) (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    SumInvTo ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      (fun n => (blackRouqF Q Λ RD Λ₀ i h₁ ◁ powComp (blackRouqDot Λ hQ RD Λ₀ i h₁) n ≫
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      (RD.pair (RD.iY i) y).toNat := by
  have hw := blackRouq_pair_eq hΛ₀ i (blockSucc RD Λ₀ i h₁ γ)
  have hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + γ.1)) ≤ 0 := by
    have hp := hpos
    rw [hw] at hp
    exact neg_nonneg.mp hp
  let S₀ := (derivedBlackSumInvToQ hP hwf i γ.1 hsym hn).map
    ((evaluation _ _).obj (M (blockSucc RD Λ₀ i h₁ γ)))
  refine (S₀.conj (blackRouqCapIso Λ hQ RD Λ₀ i h₁ M γ).symm
      (blackRouqCupIso Λ hQ RD Λ₀ i h₂ M (blockSucc RD Λ₀ i h₁ γ)) (Iso.refl _) ?_ ?_).congr
      rfl rfl (by rw [hw]; rfl)
  · exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (blackRouqCapIso Λ hQ RD Λ₀ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (blackRouq_sigma_app Λ hQ RD Λ₀ hsym i h₁ h₂ M γ))))
  · intro m
    exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (blackRouqCapIso Λ hQ RD Λ₀ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((blackRouq_capD_app Λ hQ RD Λ₀ i h₁ M γ m).trans (Category.comp_id _).symm))))

include hP hwf hΛ₀ in
/-- Brundan (1.9) on the weight space at `y`, at a block `{i} + γ`. -/
def blackRouqLocNegInterior (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z) (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    SumInvFrom ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      (fun n => ((blackRouqAdj Λ hQ RD Λ₀ i h₂).unit ≫
        powComp (blackRouqDot Λ hQ RD Λ₀ i h₂) n ▷ blackRouqF Q Λ RD Λ₀ i h₂).hom.app M
          (blockSucc RD Λ₀ i h₁ γ))
      (-RD.pair (RD.iY i) y).toNat := by
  have hw := blackRouq_pair_eq hΛ₀ i (blockSucc RD Λ₀ i h₁ γ)
  have hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + γ.1)) := by
    have hp := hneg
    rw [hw] at hp
    exact neg_nonpos.mp hp
  let S₀ := (derivedBlackSumInvFromQ hP hwf i γ.1 hsym hn).map
    ((evaluation _ _).obj (M (blockSucc RD Λ₀ i h₁ γ)))
  refine (S₀.conj (blackRouqCupIso Λ hQ RD Λ₀ i h₂ M (blockSucc RD Λ₀ i h₁ γ))
      (blackRouqCapIso Λ hQ RD Λ₀ i h₁ M γ).symm (Iso.refl _) ?_ ?_).congr rfl rfl
      (by rw [hw, neg_neg]; rfl)
  · exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (blackRouqCapIso Λ hQ RD Λ₀ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (blackRouq_sigma_app Λ hQ RD Λ₀ hsym i h₁ h₂ M γ))))
  · intro m
    exact (blackRouq_cupD_app Λ hQ RD Λ₀ i h₂ M (blockSucc RD Λ₀ i h₁ γ) m).trans
      (Category.id_comp _).symm

variable (Λ hQ) in
/-- A transformation `Eᵢ Fᵢ ⟶ 𝟭` of module functors, on derived categories (`derivedCoeff`). -/
def blackDerivedCoeff (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (c : blackFOfEq Q Λ i h ⋙ blackEOfEq Q Λ i h ⟶ 𝟭 _) :
    derivedFOfEq Λ hQ i h ⋙ derivedEOfEq Q Λ i h ⟶ 𝟭 _ :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h
  derivedCoeff c

include hP hwf in
/-- The derived dotted units identify `Eᵢ Fᵢ` with copies of the identity on a block without a
strand of colour `i` (`derivedCoeff_total`, `derivedCoeff_entry`). -/
theorem blackRouq_boundary_total (i : I) {y z : X} (h : y + RD.iX i = z)
    (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) :
    ∑ m ∈ Finset.range
        (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat,
      blackDerivedCoeff Λ hQ i (blockSucc_step RD Λ₀ i h β)
          ((blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).g' m) ≫
        ((derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h β)).unit ≫
          Functor.whiskerRight (powComp (derivedIndDotOfEq Λ hQ i
            (blockSucc_step RD Λ₀ i h β)) m) (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))) =
      𝟙 _ := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i (blockSucc_step RD Λ₀ i h β)
  have := blackFOfEq_preservesFiniteColimits Λ hQ i (blockSucc_step RD Λ₀ i h β)
  unfold blackDerivedCoeff
  refine derivedCoeff_total (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))
    (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)) _ ?_
  have t := (blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).total
  rw [Limits.comp_zero, zero_add] at t
  exact t

include hP hwf in
theorem blackRouq_boundary_entry (i : I) {y z : X} (h : y + RD.iX i = z)
    (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) (m m' : ℕ)
    (hm : m < (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat)
    (hm' : m' < (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat) :
    ((derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h β)).unit ≫
        Functor.whiskerRight (powComp (derivedIndDotOfEq Λ hQ i
          (blockSucc_step RD Λ₀ i h β)) m) (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))) ≫
      blackDerivedCoeff Λ hQ i (blockSucc_step RD Λ₀ i h β)
          ((blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).g' m') =
        if m = m' then 𝟙 _ else 0 := by
  have := blackFOfEq_preservesFiniteLimits Λ hQ i (blockSucc_step RD Λ₀ i h β)
  have := blackFOfEq_preservesFiniteColimits Λ hQ i (blockSucc_step RD Λ₀ i h β)
  unfold blackDerivedCoeff
  refine (derivedCoeff_entry (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))
    (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)) _ m _
    ((blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).gg m m' hm hm')).trans ?_
  split_ifs
  · rw [mapDerivedCategory_id, Category.id_comp, Iso.inv_hom_id]
  · rw [mapDerivedCategory_zero, Limits.zero_comp, Limits.comp_zero]

include hP hwf hΛ₀ in
/-- Brundan (1.9) on the weight space at `y`, at a block without a strand of colour `i`: the
derived dotted units. -/
def blackRouqLocNegBoundary (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) :
    SumInvFrom ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => ((blackRouqAdj Λ hQ RD Λ₀ i h₂).unit ≫
        powComp (blackRouqDot Λ hQ RD Λ₀ i h₂) n ▷ blackRouqF Q Λ RD Λ₀ i h₂).hom.app M β)
      (-RD.pair (RD.iY i) y).toNat := by
  have hw := blackRouq_pair_eq hΛ₀ i β
  let Φ := (evaluation (D β.1) (D β.1)).obj (M β)
  refine ((SumInvFrom.ofIsZero ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β ≫
          (blackRouqCupIso Λ hQ RD Λ₀ i h₂ M β).inv)
      (fun m => Φ.map ((derivedAdjOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ β)).unit ≫
        Functor.whiskerRight (powComp (derivedIndDotOfEq Λ hQ i
          (blockSucc_step RD Λ₀ i h₂ β)) m) (derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ β))))
      (blockSum_obj_isZero _ _ _ (isEmpty_of_not_mem RD Λ₀ i h₁ β hi))
      (fun m => Φ.map (blackDerivedCoeff Λ hQ i (blockSucc_step RD Λ₀ i h₂ β)
        ((blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).g' m))) ?_ ?_).conj
      (blackRouqCupIso Λ hQ RD Λ₀ i h₂ M β) (Iso.refl _) (Iso.refl _) ?_ ?_).congr rfl rfl
      (by rw [hw, neg_neg])
  · refine (Finset.sum_congr rfl fun m _ => (Φ.map_comp _ _).symm).trans ?_
    exact (Φ.map_sum _ _).symm.trans ((congrArg Φ.map
      (blackRouq_boundary_total hP hwf i h₂ β hi)).trans (Φ.map_id _))
  · intro m m' hm hm'
    refine (Φ.map_comp _ _).symm.trans ((congrArg Φ.map
      (blackRouq_boundary_entry hP hwf i h₂ β hi m m' hm hm')).trans ?_)
    split_ifs
    · exact Φ.map_id _
    · exact Φ.map_zero _ _
  · exact (Category.comp_id _).symm.trans
      ((congrArg (_ ≫ ·) (blackRouqCupIso Λ hQ RD Λ₀ i h₂ M β).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm))
  · intro m
    exact (blackRouq_cupD_app Λ hQ RD Λ₀ i h₂ M β m).trans (Category.id_comp _).symm

include hP hwf hΛ₀ in
/-- Brundan (1.8) on the weight space at `y`, at a block without a strand of colour `i`: there
`⟨h_i, y⟩ = 0` and both sides vanish. -/
def blackRouqLocPosBoundary (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) :
    SumInvTo ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => (blackRouqF Q Λ RD Λ₀ i h₁ ◁ powComp (blackRouqDot Λ hQ RD Λ₀ i h₁) n ≫
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β)
      (RD.pair (RD.iY i) y).toNat := by
  have hw := blackRouq_pair_eq hΛ₀ i β
  have hnn := ip_nonneg_of_notMem (RD := RDc) (Λ := coordinateRedWeights Λ C) i β.1 hi
  have h0 : RD.pair (RD.iY i) y = 0 := by linarith
  have hip : (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat = 0 := by
    rw [show ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1) = 0 by linarith]
    rfl
  have ht := blackRouq_boundary_total hP hwf i h₂ β hi
  have hr : Finset.range
      (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat = ∅ := by
    rw [hip, Finset.range_zero]
  rw [hr, Finset.sum_empty] at ht
  have hZ : IsZero ((derivedFOfEq Λ hQ i (blockSucc_step RD Λ₀ i h₂ β) ⋙
      derivedEOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ β)).obj (M β)) :=
    (IsZero.iff_id_eq_zero _).2 (congrArg (fun η => NatTrans.app η (M β)) ht).symm
  refine SumInvTo.congr (n := 0) (SumInvTo.ofIsZero _ _ ?_ ?_) rfl rfl (by rw [h0]; rfl)
  · exact blockSum_obj_isZero _ _ _ (isEmpty_of_not_mem RD Λ₀ i h₁ β hi)
  · exact hZ.of_iso (blackRouqCupIso Λ hQ RD Λ₀ i h₂ M β).symm

include hP hwf hΛ₀ in
/-- Brundan (1.8) on the weight space at `y`, blockwise. -/
def blackRouqLocPos (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :
    SumInvTo ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => (blackRouqF Q Λ RD Λ₀ i h₁ ◁ powComp (blackRouqDot Λ hQ RD Λ₀ i h₁) n ≫
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β)
      (RD.pair (RD.iY i) y).toNat :=
  if hi : i ∈ β.1 then
    (fun γ (hγ : blockSucc RD Λ₀ i h₁ γ = β) => by
      subst hγ; exact blackRouqLocPosInterior hP hwf hsym hΛ₀ i h₁ h₂ hpos M γ) _
      (exists_blockSucc_of_mem RD Λ₀ i h₁ β hi).choose_spec
  else blackRouqLocPosBoundary hP hwf hsym hΛ₀ i h₁ h₂ hpos M β hi

include hP hwf hΛ₀ in
/-- Brundan (1.9) on the weight space at `y`, blockwise. -/
def blackRouqLocNeg (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :
    SumInvFrom ((RightwardCrossing.sigma (blackRouqAdj Λ hQ RD Λ₀ i h₂).unit
        (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackRouqAdj Λ hQ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => ((blackRouqAdj Λ hQ RD Λ₀ i h₂).unit ≫
        powComp (blackRouqDot Λ hQ RD Λ₀ i h₂) n ▷ blackRouqF Q Λ RD Λ₀ i h₂).hom.app M β)
      (-RD.pair (RD.iY i) y).toNat :=
  if hi : i ∈ β.1 then
    (fun γ (hγ : blockSucc RD Λ₀ i h₁ γ = β) => by
      subst hγ; exact blackRouqLocNegInterior hP hwf hsym hΛ₀ i h₁ h₂ hneg M γ) _
      (exists_blockSucc_of_mem RD Λ₀ i h₁ β hi).choose_spec
  else blackRouqLocNegBoundary hP hwf hsym hΛ₀ i h₁ h₂ M β hi

include hP hwf hΛ₀ in
/-- **Rouquier's local data for Webster's derived action** (Webster, arXiv:1309.3796v3, §4.6,
§5.1, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30; Brundan, arXiv:1501.00350v1,
(1.2), (1.8), (1.9)): at the weight `y`, with Brundan weight `⟨h_i, y⟩`, the derived induction
`Fᵢ`, its adjunction, dot and same-colour crossing (acting as `-ψ`, the convention of
Khovanov–Lauda III) on the weight spaces of `D(T^λ)`. The hypotheses are those of
`clBlackModuleEFEquivQ`: a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`), together with the compatibility
`hΛ₀ : ⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` of the weight `Λ₀` with the red labels. -/
def blackRouqLoc (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z) :
    RouqLoc (blackRouqAdj Λ hQ RD Λ₀ i h₁) (blackRouqAdj Λ hQ RD Λ₀ i h₂)
      (blackRouqDot Λ hQ RD Λ₀ i h₁) (blackRouqDot Λ hQ RD Λ₀ i h₂)
      (blackRouqCross Λ hQ RD Λ₀ hsym i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) y) where
  slide_left := blackRouqCross_slide_left_self Λ hQ RD Λ₀ hsym i h₁ h₂
  slide_right := blackRouqCross_slide_right_self Λ hQ RD Λ₀ hsym i h₁ h₂
  invPos hpos := SumInvTo.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvTo.ofApp fun M => SumInvTo.pi fun β =>
      blackRouqLocPos hP hwf hsym hΛ₀ i h₁ h₂ hpos M β)
  invNeg hneg := SumInvFrom.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvFrom.ofApp fun M => SumInvFrom.pi fun β =>
      blackRouqLocNeg hP hwf hsym hΛ₀ i h₁ h₂ hneg M β)

include hP hwf hΛ₀ in
/-- **Webster's derived action as a Rouquier family** (Webster, arXiv:1309.3796v3, §4.6, §5.1,
Theorem 4.31; Brundan, arXiv:1501.00350v1, Definition 1.1, single-colour part): the weight
spaces of the derived categories of right `T^λ`-modules, derived induction and restriction
with their adjunction, dots, crossings (the same-colour crossing acts as `-ψ`, the convention
of Khovanov–Lauda III), the nil-Hecke relations and Rouquier's local data `blackRouqLoc`. Its
generators are `blackRouqData` (`blackRouqFamily_toRouqData`). The hypotheses are a
presentation `P` with negligible cover relations (`CoverRelsNegligible`) and well-founded
domains (`WFDom`), and the compatibility `hΛ₀ : ⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` of `Λ₀` with the red
labels (satisfied by `coordinateHighest Λ C` in the coordinate weight datum). -/
def blackRouqFamily : RouqFamily (B := LinearCat k) RD where
  toRouqData := blackRouqData Λ hQ RD Λ₀ hsym
  F i _ _ h := blackRouqF Q Λ RD Λ₀ i h
  adj i _ _ h := blackRouqAdj Λ hQ RD Λ₀ i h
  square i _ _ _ h₁ h₂ := blackRouqCross_sq Λ hQ RD Λ₀ hsym i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := blackRouqCross_sameBraid Λ hQ RD Λ₀ hsym i h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := blackRouqLoc hP hwf hsym hΛ₀ i h₁ h₂

omit [∀ β : Multiset I,
  HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)] in
theorem blackRouqFamily_toRouqData
    [∀ β : Multiset I,
      HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)] :
    (blackRouqFamily hP hwf hsym hΛ₀).toRouqData = blackRouqData Λ hQ RD Λ₀ hsym := rfl

end Loc

end Categorification.Stendhal
