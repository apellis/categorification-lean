/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleRouqData
import Categorification.WeightedKLR.RedStrands.BlackRouqLocQ

/-!
# Webster's action on categories of `T^λ`-modules as a Rouquier family

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and
Theorem 4.31; Brundan, arXiv:1501.00350v1, Definition 1.1 (single-colour part), (1.2), (1.8),
(1.9).

This is the abelian counterpart of `blackRouqFamily`: Rouquier's local data (`TwoRep.RouqLoc`)
for the generators `blackModuleRouqData` on the weight spaces of all right `T^λ`-modules
(`blackModLoc`), and the resulting `TwoRep.RouqFamily` (`blackModuleRouqFamily`), with
induction `blackFOfEq`, restriction `blackEOfEq` and their adjunction `blackAdjOfEq`.

As for derived categories, the rightward crossing, the dotted caps and the dotted cups on a
weight space are block diagonal (`blackMod_sigma_app`, `blackMod_capD_app`,
`blackMod_cupD_app`). On a block `{i} + γ` the inverses are the module inverses
`clBlackModuleSumInvToQ`/`FromQ` themselves (the derived family uses their derived images); on a
block without a strand of colour `i`, `Fᵢ Eᵢ` vanishes and the inverses come from the dotted units
(`blackModuleSumInvFromOfNotMemQ`).

The hypotheses are those of `blackRouqFamily`, without derived categories: a presentation `P`
with negligible cover relations (`CoverRelsNegligible`) and well-founded domains (`WFDom`)
(Webster's Theorem 4.30 in the library), a Rouquier polynomial family `Q` over a field
(`IsRouquierQ`), `KLRSymm Q`, and the compatibility `hΛ₀ : ⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` of the
weight `Λ₀` with the red labels (the route hypothesis of `blackRouqFamily`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory QuantumGroup
  QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram
  NatTrans

open scoped Classical

universe u w u₁

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ₀ : X)

set_option hygiene false in
local notation "D" β => ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ

theorem blackModAdj_unit_app (i : I) {y z : X} (h : y + RD.iX i = z)
    (N : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :
    (blackModAdj Q Λ RD Λ₀ i h).unit.hom.app N β =
      (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)).unit.app (N β) ≫
        (moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map
          (blockι (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h) N ⟨β, rfl⟩) := rfl

/-- **The dotted cups on weight spaces, blockwise.** -/
theorem blackMod_cupD_app (i : I) {y z : X} (h : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) (m : ℕ) :
    ((blackModAdj Q Λ RD Λ₀ i h).unit ≫
        powComp (blackModDot Q Λ RD Λ₀ i h) m ▷ blackModF Q Λ RD Λ₀ i h).hom.app M β =
      ((blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)).unit ≫
          Functor.whiskerRight (powComp (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)) m)
            (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))).app (M β) ≫
        (moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map
          (blockι (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h) M ⟨β, rfl⟩) := by
  have t1 : (blackModAdj Q Λ RD Λ₀ i h).unit.hom.app M β =
      (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)).unit.app (M β) ≫
      (moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map
        (blockι (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h) M ⟨β, rfl⟩) := rfl
  have t2 : (powComp (blackModDot Q Λ RD Λ₀ i h) m ▷ blackModF Q Λ RD Λ₀ i h).hom.app M β =
      (moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map
        ((powComp (blackModDot Q Λ RD Λ₀ i h) m).hom.app M (blockSucc RD Λ₀ i h β)) := rfl
  have t3 : ((blackModAdj Q Λ RD Λ₀ i h).unit ≫
        powComp (blackModDot Q Λ RD Λ₀ i h) m ▷ blackModF Q Λ RD Λ₀ i h).hom.app M β =
      (blackModAdj Q Λ RD Λ₀ i h).unit.hom.app M β ≫
        (powComp (blackModDot Q Λ RD Λ₀ i h) m ▷ blackModF Q Λ RD Λ₀ i h).hom.app M β := rfl
  rw [t3, t1, t2, NatTrans.comp_app, Functor.whiskerRight_app, LinearCat.powComp_hom]
  simp only [Category.assoc]
  have key := blockι_powComp_blockSumMap (blockSucc RD Λ₀ i h)
    (fun _ _ hβ => indDotOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ)) M ⟨β, rfl⟩ m
  exact congrArg (_ ≫ ·) (((moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map_comp _ _).symm.trans
    ((congrArg (moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map key).trans
      ((moduleEBlock Q Λ RD Λ₀ i h β _ rfl).map_comp _ _)))

/-- **The dotted caps on weight spaces, blockwise**, on the generator of `Fᵢ Eᵢ` at the block
`{i} + γ`. -/
theorem blackMod_capD_app (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) (m : ℕ) :
    blockι (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h)
        ((blackModF Q Λ RD Λ₀ i h).obj.obj M) ⟨γ, rfl⟩ ≫
      (blackModF Q Λ RD Λ₀ i h ◁ powComp (blackModDot Q Λ RD Λ₀ i h) m ≫
        (blackModAdj Q Λ RD Λ₀ i h).counit).hom.app M (blockSucc RD Λ₀ i h γ) =
      (Functor.whiskerLeft (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h γ))
          (powComp (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h γ)) m) ≫
        (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h γ)).counit).app
          (M (blockSucc RD Λ₀ i h γ)) := by
  change _ ≫ (powComp (blackModDot Q Λ RD Λ₀ i h) m).hom.app
      ((blackModF Q Λ RD Λ₀ i h).obj.obj M) (blockSucc RD Λ₀ i h γ) ≫ biproduct.desc _ =
    (powComp (indDotOfEq Q Λ i (blockSucc_step RD Λ₀ i h γ)) m).app _ ≫
      (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h γ)).counit.app (M (blockSucc RD Λ₀ i h γ))
  rw [LinearCat.powComp_hom]
  have key := blockι_powComp_blockSumMap (blockSucc RD Λ₀ i h)
    (fun _ _ hβ => indDotOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ))
    ((blackModF Q Λ RD Λ₀ i h).obj.obj M) ⟨γ, rfl⟩ m
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (biproduct.ι_desc _ _))))

/-- The generator of `Fᵢ Fᵢ` on `Fᵢ Eᵢ` followed by the counit. -/
theorem blackMod_gen₂_counit (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    Eq (gen₂ (b := blockSucc RD Λ₀ i h₁ γ) (d := blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))
        (blockSucc RD Λ₀ i h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₁)
        (moduleFBlock Q Λ RD Λ₀ i h₂)
        ((blockRes (blockSucc RD Λ₀ i h₁) (moduleEBlock Q Λ RD Λ₀ i h₁)).obj M) γ rfl rfl ≫
      (TwoRep.blockSum (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₂)).map
        ((blockCounitNat (blockSucc RD Λ₀ i h₁)
          (fun _ _ hβ => blackAdjOfEq Q Λ i (blockSucc_eq RD Λ₀ i hβ))).app M)
        (blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)))
      ((moduleFBlock Q Λ RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)
          (blockSucc RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)) rfl).map
          ((blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ)).counit.app
            (M (blockSucc RD Λ₀ i h₁ γ))) ≫
        blockι (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₂) M
          ⟨blockSucc RD Λ₀ i h₁ γ, rfl⟩) := by
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact biproduct.ι_desc _ _

/-- **The rightward crossing on weight spaces, blockwise**: on the generator of `Fᵢ Eᵢ` at the
block `{i} + γ`, it is the rightward crossing of the block functors at `{i} + γ`,
followed by the generator of `Eᵢ Fᵢ`. -/
theorem blackMod_sigma_app (hsym : KLRSymm Q) (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z) (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    Eq (blockι (blockSucc RD Λ₀ i h₁) (moduleFBlock Q Λ RD Λ₀ i h₁)
        ((blockRes (blockSucc RD Λ₀ i h₁) (moduleEBlock Q Λ RD Λ₀ i h₁)).obj M) ⟨γ, rfl⟩ ≫
      (RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      ((functorSigma
          (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))).unit
          (indCrossOfEq Λ hsym i i (blockSucc_step RD Λ₀ i h₁ γ)
            (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)) (blockSucc_step RD Λ₀ i h₁ γ)
            (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ)))
          (blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h₁ γ)).counit).app
            (M (blockSucc RD Λ₀ i h₁ γ)) ≫
        (moduleEBlock Q Λ RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ) _ rfl).map
          (blockι (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ i h₂) M
            ⟨blockSucc RD Λ₀ i h₁ γ, rfl⟩)) := by
  rw [LinearCat.sigma_hom]
  have hU := (blackAdjOfEq Q Λ i
      (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))).unit_naturality
    (blockι (blockSucc RD Λ₀ i h₁) (moduleFBlock Q Λ RD Λ₀ i h₁)
        ((blockRes (blockSucc RD Λ₀ i h₁) (moduleEBlock Q Λ RD Λ₀ i h₁)).obj M) ⟨γ, rfl⟩)
  have hT := gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂
    ((blockRes (blockSucc RD Λ₀ i h₁) (moduleEBlock Q Λ RD Λ₀ i h₁)).obj M) γ rfl rfl rfl rfl
  have hC := blackMod_gen₂_counit Q Λ RD Λ₀ i h₁ h₂ M γ
  have key := (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    pi_comp_apply_blocks, blackModAdj_unit_app]
  simp only [Category.assoc]
  erw [← reassoc_of% hU]
  have key' := congrArg
    (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ (blockSucc RD Λ₀ i h₁ γ))).map key
  simp only [Functor.map_comp] at key'
  simp only [functorSigma_app, Category.assoc]
  exact congrArg (_ ≫ ·) key'

/-- The generator of `Fᵢ Eᵢ` at the block `{i} + γ`, as an isomorphism. -/
def blackModCapIso (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :=
  blockιIso (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h)
    ((blockRes (blockSucc RD Λ₀ i h) (moduleEBlock Q Λ RD Λ₀ i h)).obj M) ⟨γ, rfl⟩
    fun _ => Subsingleton.elim _ _

/-- The generator of `Eᵢ Fᵢ` at the block `β`, as an isomorphism. -/
def blackModCupIso (i : I) {y z : X} (h : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :=
  (moduleEBlock Q Λ RD Λ₀ i h β _ rfl).mapIso
    (blockιIso (blockSucc RD Λ₀ i h) (moduleFBlock Q Λ RD Λ₀ i h) M ⟨β, rfl⟩
      fun _ => Subsingleton.elim _ _)

local notation "RDc" => coordinateDatum Λ C

section Loc

variable {Q Λ RD Λ₀} {hQ : IsRouquierQ C Q} {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom) (hsym : KLRSymm Q)
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))

include hΛ₀ in
/-- The Brundan weight of a weight space is minus the coordinate pairing of each of its
blocks. -/
theorem blackMod_pair_eq (i : I) {y : X} (β : WeightBlocks RD Λ₀ y) :
    RD.pair (RD.iY i) y =
      -ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1) := by
  obtain ⟨β, rfl⟩ := β
  exact pair_blockWeight_eq_neg_ip Λ C RD Λ₀ hΛ₀ i β

include hP hwf hΛ₀ in
/-- Brundan (1.8) on the weight space at `y`, at a block `{i} + γ`. -/
def blackModLocPosInterior (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z) (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    SumInvTo ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      (fun n => (blackModF Q Λ RD Λ₀ i h₁ ◁ powComp (blackModDot Q Λ RD Λ₀ i h₁) n ≫
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      (RD.pair (RD.iY i) y).toNat := by
  have hw := blackMod_pair_eq hΛ₀ i (blockSucc RD Λ₀ i h₁ γ)
  have hn : ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + γ.1)) ≤ 0 := by
    have hp := hpos
    rw [hw] at hp
    exact neg_nonneg.mp hp
  let S₀ := (clBlackModuleSumInvToQ hP hwf i γ.1 hsym hn).map
    ((evaluation _ _).obj (M (blockSucc RD Λ₀ i h₁ γ)))
  refine (S₀.conj (blackModCapIso Q Λ RD Λ₀ i h₁ M γ).symm
      (blackModCupIso Q Λ RD Λ₀ i h₂ M (blockSucc RD Λ₀ i h₁ γ)) (Iso.refl _) ?_ ?_).congr
      rfl rfl (by rw [hw]; rfl)
  · exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (blackModCapIso Q Λ RD Λ₀ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (blackMod_sigma_app Q Λ RD Λ₀ hsym i h₁ h₂ M γ))))
  · intro m
    exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (blackModCapIso Q Λ RD Λ₀ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((blackMod_capD_app Q Λ RD Λ₀ i h₁ M γ m).trans (Category.comp_id _).symm))))

include hP hwf hΛ₀ in
/-- Brundan (1.9) on the weight space at `y`, at a block `{i} + γ`. -/
def blackModLocNegInterior (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z) (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (γ : WeightBlocks RD Λ₀ x) :
    SumInvFrom ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M (blockSucc RD Λ₀ i h₁ γ))
      (fun n => ((blackModAdj Q Λ RD Λ₀ i h₂).unit ≫
        powComp (blackModDot Q Λ RD Λ₀ i h₂) n ▷ blackModF Q Λ RD Λ₀ i h₂).hom.app M
          (blockSucc RD Λ₀ i h₁ γ))
      (-RD.pair (RD.iY i) y).toNat := by
  have hw := blackMod_pair_eq hΛ₀ i (blockSucc RD Λ₀ i h₁ γ)
  have hn : 0 ≤ ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) ({i} + γ.1)) := by
    have hp := hneg
    rw [hw] at hp
    exact neg_nonpos.mp hp
  let S₀ := (clBlackModuleSumInvFromQ hP hwf i γ.1 hsym hn).map
    ((evaluation _ _).obj (M (blockSucc RD Λ₀ i h₁ γ)))
  refine (S₀.conj (blackModCupIso Q Λ RD Λ₀ i h₂ M (blockSucc RD Λ₀ i h₁ γ))
      (blackModCapIso Q Λ RD Λ₀ i h₁ M γ).symm (Iso.refl _) ?_ ?_).congr rfl rfl
      (by rw [hw, neg_neg]; rfl)
  · exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (blackModCapIso Q Λ RD Λ₀ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (blackMod_sigma_app Q Λ RD Λ₀ hsym i h₁ h₂ M γ))))
  · intro m
    exact (blackMod_cupD_app Q Λ RD Λ₀ i h₂ M (blockSucc RD Λ₀ i h₁ γ) m).trans
      (Category.id_comp _).symm

include hP hwf in
/-- The dotted units identify `Eᵢ Fᵢ` with copies of the identity on a block without a strand
of colour `i` (`blackModuleSumInvFromOfNotMemQ`): the total relation. -/
theorem blackMod_boundary_total (i : I) {y z : X} (h : y + RD.iX i = z)
    (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) :
    ∑ m ∈ Finset.range
        (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat,
      (blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).g' m ≫
        ((blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)).unit ≫
          Functor.whiskerRight (powComp (indDotOfEq Q Λ i
            (blockSucc_step RD Λ₀ i h β)) m) (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))) =
      𝟙 _ := by
  have t := (blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).total
  rw [Limits.comp_zero, zero_add] at t
  exact t

include hP hwf in
/-- The dotted units identify `Eᵢ Fᵢ` with copies of the identity on a block without a strand
of colour `i`: the entries. -/
theorem blackMod_boundary_entry (i : I) {y z : X} (h : y + RD.iX i = z)
    (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) (m m' : ℕ)
    (hm : m < (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat)
    (hm' : m' < (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat) :
    ((blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h β)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i
          (blockSucc_step RD Λ₀ i h β)) m) (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h β))) ≫
      (blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).g' m' =
        if m = m' then 𝟙 _ else 0 :=
  (blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).gg m m' hm hm'

include hP hwf hΛ₀ in
/-- Brundan (1.9) on the weight space at `y`, at a block without a strand of colour `i`: the
dotted units. -/
def blackModLocNegBoundary (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) :
    SumInvFrom ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => ((blackModAdj Q Λ RD Λ₀ i h₂).unit ≫
        powComp (blackModDot Q Λ RD Λ₀ i h₂) n ▷ blackModF Q Λ RD Λ₀ i h₂).hom.app M β)
      (-RD.pair (RD.iY i) y).toNat := by
  have hw := blackMod_pair_eq hΛ₀ i β
  let Φ := (evaluation (D β.1) (D β.1)).obj (M β)
  refine ((SumInvFrom.ofIsZero ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β ≫
          (blackModCupIso Q Λ RD Λ₀ i h₂ M β).inv)
      (fun m => Φ.map ((blackAdjOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ β)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i
          (blockSucc_step RD Λ₀ i h₂ β)) m) (blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ β))))
      (blockSum_obj_isZero _ _ _ (isEmpty_of_not_mem RD Λ₀ i h₁ β hi))
      (fun m => Φ.map ((blackModuleSumInvFromOfNotMemQ hP hwf i β.1 hi).g' m)) ?_ ?_).conj
      (blackModCupIso Q Λ RD Λ₀ i h₂ M β) (Iso.refl _) (Iso.refl _) ?_ ?_).congr rfl rfl
      (by rw [hw, neg_neg])
  · refine (Finset.sum_congr rfl fun m _ => (Φ.map_comp _ _).symm).trans ?_
    exact (Φ.map_sum _ _).symm.trans ((congrArg Φ.map
      (blackMod_boundary_total hP hwf i h₂ β hi)).trans (Φ.map_id _))
  · intro m m' hm hm'
    refine (Φ.map_comp _ _).symm.trans ((congrArg Φ.map
      (blackMod_boundary_entry hP hwf i h₂ β hi m m' hm hm')).trans ?_)
    split_ifs
    · exact Φ.map_id _
    · exact Φ.map_zero _ _
  · exact (Category.comp_id _).symm.trans
      ((congrArg (_ ≫ ·) (blackModCupIso Q Λ RD Λ₀ i h₂ M β).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm))
  · intro m
    exact (blackMod_cupD_app Q Λ RD Λ₀ i h₂ M β m).trans (Category.id_comp _).symm

include hP hwf hΛ₀ in
/-- Brundan (1.8) on the weight space at `y`, at a block without a strand of colour `i`: there
`⟨h_i, y⟩ = 0` and both sides vanish. -/
def blackModLocPosBoundary (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) (hi : i ∉ β.1) :
    SumInvTo ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => (blackModF Q Λ RD Λ₀ i h₁ ◁ powComp (blackModDot Q Λ RD Λ₀ i h₁) n ≫
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β)
      (RD.pair (RD.iY i) y).toNat := by
  have hw := blackMod_pair_eq hΛ₀ i β
  have hnn := ip_nonneg_of_notMem (RD := RDc) (Λ := coordinateRedWeights Λ C) i β.1 hi
  have h0 : RD.pair (RD.iY i) y = 0 := by linarith
  have hip : (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat = 0 := by
    rw [show ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1) = 0 by linarith]
    rfl
  have ht := blackMod_boundary_total hP hwf i h₂ β hi
  have hr : Finset.range
      (ip (RDc) i (downRightWeight (RDc) (coordinateRedWeights Λ C) β.1)).toNat = ∅ := by
    rw [hip, Finset.range_zero]
  rw [hr, Finset.sum_empty] at ht
  have hZ : IsZero ((blackFOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ β) ⋙
      blackEOfEq Q Λ i (blockSucc_step RD Λ₀ i h₂ β)).obj (M β)) :=
    (IsZero.iff_id_eq_zero _).2 (congrArg (fun η => NatTrans.app η (M β)) ht).symm
  refine SumInvTo.congr (n := 0) (SumInvTo.ofIsZero _ _ ?_ ?_) rfl rfl (by rw [h0]; rfl)
  · exact blockSum_obj_isZero _ _ _ (isEmpty_of_not_mem RD Λ₀ i h₁ β hi)
  · exact hZ.of_iso (blackModCupIso Q Λ RD Λ₀ i h₂ M β).symm

include hP hwf hΛ₀ in
/-- Brundan (1.8) on the weight space at `y`, blockwise. -/
def blackModLocPos (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :
    SumInvTo ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => (blackModF Q Λ RD Λ₀ i h₁ ◁ powComp (blackModDot Q Λ RD Λ₀ i h₁) n ≫
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β)
      (RD.pair (RD.iY i) y).toNat :=
  if hi : i ∈ β.1 then
    (fun γ (hγ : blockSucc RD Λ₀ i h₁ γ = β) => by
      subst hγ; exact blackModLocPosInterior hP hwf hsym hΛ₀ i h₁ h₂ hpos M γ) _
      (exists_blockSucc_of_mem RD Λ₀ i h₁ β hi).choose_spec
  else blackModLocPosBoundary hP hwf hsym hΛ₀ i h₁ h₂ hpos M β hi

include hP hwf hΛ₀ in
/-- Brundan (1.9) on the weight space at `y`, blockwise. -/
def blackModLocNeg (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ₀ y, D β.1) (β : WeightBlocks RD Λ₀ y) :
    SumInvFrom ((RightwardCrossing.sigma (blackModAdj Q Λ RD Λ₀ i h₂).unit
        (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂)
        (blackModAdj Q Λ RD Λ₀ i h₁).counit).hom.app M β)
      (fun n => ((blackModAdj Q Λ RD Λ₀ i h₂).unit ≫
        powComp (blackModDot Q Λ RD Λ₀ i h₂) n ▷ blackModF Q Λ RD Λ₀ i h₂).hom.app M β)
      (-RD.pair (RD.iY i) y).toNat :=
  if hi : i ∈ β.1 then
    (fun γ (hγ : blockSucc RD Λ₀ i h₁ γ = β) => by
      subst hγ; exact blackModLocNegInterior hP hwf hsym hΛ₀ i h₁ h₂ hneg M γ) _
      (exists_blockSucc_of_mem RD Λ₀ i h₁ β hi).choose_spec
  else blackModLocNegBoundary hP hwf hsym hΛ₀ i h₁ h₂ M β hi

include hP hwf hΛ₀ in
/-- **Rouquier's local data for Webster's action on `T^λ`-modules** (Webster,
arXiv:1309.3796v3, §4.6, §5.1, Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30;
Brundan, arXiv:1501.00350v1, (1.2), (1.8), (1.9)): at the weight `y`, with Brundan weight
`⟨h_i, y⟩`, induction `Fᵢ`, its adjunction, dot and same-colour crossing (acting as `-ψ`, the
convention of Khovanov–Lauda III) on the weight spaces of right `T^λ`-modules. The hypotheses are
those of `clBlackModuleEFEquivQ`: a presentation `P` with negligible cover relations
(`CoverRelsNegligible`) and well-founded domains (`WFDom`), together with the compatibility
`hΛ₀ : ⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` of the weight `Λ₀` with the red labels. -/
def blackModLoc (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z) :
    RouqLoc (blackModAdj Q Λ RD Λ₀ i h₁) (blackModAdj Q Λ RD Λ₀ i h₂)
      (blackModDot Q Λ RD Λ₀ i h₁) (blackModDot Q Λ RD Λ₀ i h₂)
      (blackModCross Q Λ RD Λ₀ hsym i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) y) where
  slide_left := blackModCross_slide_left_self Q Λ RD Λ₀ hsym i h₁ h₂
  slide_right := blackModCross_slide_right_self Q Λ RD Λ₀ hsym i h₁ h₂
  invPos hpos := SumInvTo.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvTo.ofApp fun M => SumInvTo.pi fun β =>
      blackModLocPos hP hwf hsym hΛ₀ i h₁ h₂ hpos M β)
  invNeg hneg := SumInvFrom.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvFrom.ofApp fun M => SumInvFrom.pi fun β =>
      blackModLocNeg hP hwf hsym hΛ₀ i h₁ h₂ hneg M β)

include hP hwf hΛ₀ in
/-- **Webster's action on `T^λ`-modules as a Rouquier family** (Webster, arXiv:1309.3796v3,
§4.6, §5.1, Theorem 4.31; Brundan, arXiv:1501.00350v1, Definition 1.1, single-colour part): the
weight spaces of the categories of all right `T^λ`-modules, induction `blackFOfEq` and
restriction `blackEOfEq` with their adjunction, dots, crossings (the same-colour crossing acts as
`-ψ`, the convention of Khovanov–Lauda III), the nil-Hecke relations and Rouquier's local data
`blackModLoc`. Its generators are `blackModuleRouqData` (`blackModuleRouqFamily_toRouqData`).
The hypotheses are those of `blackRouqFamily` without derived categories: a presentation `P`
with negligible cover relations (`CoverRelsNegligible`) and well-founded domains (`WFDom`), and
the compatibility `hΛ₀ : ⟨h_i, Λ₀⟩ = Σ_r Λ_r(i)` of `Λ₀` with the red labels (satisfied by
`coordinateHighest Λ C` in the coordinate weight datum). -/
def blackModuleRouqFamily : RouqFamily (B := LinearCat k) RD where
  toRouqData := blackModuleRouqData Q Λ RD Λ₀ hsym
  F i _ _ h := blackModF Q Λ RD Λ₀ i h
  adj i _ _ h := blackModAdj Q Λ RD Λ₀ i h
  square i _ _ _ h₁ h₂ := blackModCross_sq Q Λ RD Λ₀ hsym i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := blackModCross_sameBraid Q Λ RD Λ₀ hsym i h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := blackModLoc hP hwf hsym hΛ₀ i h₁ h₂

theorem blackModuleRouqFamily_toRouqData :
    (blackModuleRouqFamily hP hwf hsym hΛ₀).toRouqData = blackModuleRouqData Q Λ RD Λ₀ hsym :=
  rfl

end Loc

end Categorification.Stendhal
