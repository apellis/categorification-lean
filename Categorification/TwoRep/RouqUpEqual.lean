/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpInterp

/-!
# Equal-colour upward relation consumers

The nilHecke relations of Cautis–Lauda, arXiv:1111.1431v3, §2.2, are evaluated
on the unchanged `RouqFamily.genImg`. The two slides require the explicit local
normalization `Sc.r i = 1`; the square and braid do not. These are statements
in the original target Hom categories, with no zero-object assumption.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}
namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh

/-- The actual equal-colour crossing has the prescribed upward image. -/
theorem readUp_X2_self (i : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.X2 i i) =
      S.cross i i (cross_up_reg i μ) (cross_up_reg i _) (cross_up_reg i μ)
        (cross_up_reg i _) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain1_key S.model ?t1 ?t1' _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 | t1' => exact (λ_ _) ≪≫ (ρ_ _)
    erw [layerAt_whole]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    exact Category.comp_id _
  all_goals rfl

/-- The original CL square relation at an arbitrary weight and colour. -/
theorem klr_sqEq_rel (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [i, i] μ) (condUp [i, i] μ)
      (CL.relationCL RD k Sc (.klr μ (.sqEq i))) = 0 := by
  change S.upEndAlg Sc [i, i] μ (LinDiagram.of
    (KLR.Diagram.X2 i i ≫ KLR.Diagram.X2 i i)) = 0
  rw [upEndAlg_of, readUp_X2X2]
  exact S.square i _ _

private theorem upEndAlg_comp (l : List I) (μ : X)
    (f g : KLR.Diagram.ob l ⟶ KLR.Diagram.ob l) :
    S.upEndAlg Sc l μ (LinDiagram.of (f ≫ g)) =
      S.readUp Sc μ f ≫ S.readUp Sc μ g := by
  change admissibleMap (S.genImg Sc) _ _ (upLin RD k μ (LinDiagram.of (f ≫ g))) = _
  erw [upLin_of, admissibleMap_of]
  have hc : upDiag RD μ (f ≫ g) = upDiag RD μ f ≫ upDiag RD μ g := by
    apply Diagram.ext
    simp only [layers_upDiag, Diagram.layers_comp, List.map_append]
  rw [hc]
  exact (S.interp Sc _ μ).map_comp
    (ObjectProperty.homMk (X := ⟨_, condUp l μ⟩) (Y := ⟨_, condUp l μ⟩) (upDiag RD μ f))
    (ObjectProperty.homMk (X := ⟨_, condUp l μ⟩) (Y := ⟨_, condUp l μ⟩) (upDiag RD μ g))

/-- The first actual CL nilHecke slide, with its identity coefficient retained. -/
theorem klr_slideLEq_rel (i : I) (μ : X) (hr : Sc.r i = 1) :
    admissibleMap (S.genImg Sc) (condUp [i, i] μ) (condUp [i, i] μ)
      (CL.relationCL RD k Sc (.klr μ (.slideLEq i))) = 0 := by
  change S.upEndAlg Sc [i, i] μ (CL.relationR k (CL.qCL Sc)
    (fun c => (Sc.r c : k)) (.slideLEq i)) = 0
  dsimp only [CL.relationR]
  erw [hr, Units.val_one, one_smul, map_sub, map_sub,
    upEndAlg_comp, upEndAlg_comp, readUp_X2_self, readUp_D0, readUp_D1]
  erw [show S.upEndAlg Sc [i, i] μ (LinDiagram.of (𝟙 _)) = 𝟙 _ from
    (S.upEndAlg Sc [i, i] μ).map_one]
  exact sub_eq_zero.mpr (S.loc i (cross_up_reg i μ) (cross_up_reg i _)).slide_right

/-- The second actual CL nilHecke slide, with its identity coefficient retained. -/
theorem klr_slideREq_rel (i : I) (μ : X) (hr : Sc.r i = 1) :
    admissibleMap (S.genImg Sc) (condUp [i, i] μ) (condUp [i, i] μ)
      (CL.relationCL RD k Sc (.klr μ (.slideREq i))) = 0 := by
  change S.upEndAlg Sc [i, i] μ (CL.relationR k (CL.qCL Sc)
    (fun c => (Sc.r c : k)) (.slideREq i)) = 0
  dsimp only [CL.relationR]
  erw [hr, Units.val_one, one_smul, map_sub, map_sub,
    upEndAlg_comp, upEndAlg_comp, readUp_X2_self, readUp_D0, readUp_D1]
  erw [show S.upEndAlg Sc [i, i] μ (LinDiagram.of (𝟙 _)) = 𝟙 _ from
    (S.upEndAlg Sc [i, i] μ).map_one]
  exact sub_eq_zero.mpr (S.loc i (cross_up_reg i μ) (cross_up_reg i _)).slide_left

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [AdditiveWhiskering B] in
private theorem braid_reassoc {a b c d : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    (x : f ≫ g ⟶ f ≫ g) (y : g ≫ h ⟶ g ≫ h)
    (hb : f ◁ y ≫ ((α_ f g h).inv ≫ x ▷ h ≫ (α_ f g h).hom) ≫ f ◁ y =
      ((α_ f g h).inv ≫ x ▷ h ≫ (α_ f g h).hom) ≫ f ◁ y ≫
        ((α_ f g h).inv ≫ x ▷ h ≫ (α_ f g h).hom)) :
    ((α_ f g h).hom ≫ f ◁ y ≫ (α_ f g h).inv) ≫ x ▷ h ≫
      ((α_ f g h).hom ≫ f ◁ y ≫ (α_ f g h).inv) =
    x ▷ h ≫ ((α_ f g h).hom ≫ f ◁ y ≫ (α_ f g h).inv) ≫ x ▷ h := by
  apply (cancel_epi (α_ f g h).inv).1
  apply (cancel_mono (α_ f g h).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hb

set_option maxHeartbeats 2000000 in
/-- The all-equal braid is the original single-colour source braid. -/
theorem readUp_braid_self (i : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.braidL i i i) =
      S.readUp Sc μ (KLR.Diagram.braidR i i i) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  change (eqToHom _ ≫ coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, i) + (sh RD (true, i) + (sh RD (true, i) + μ))), [],
        PivotalGen.gen (Gen0.cross true i i (sh RD (true, i) + μ)), [⟨(true, i), μ⟩]⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, i) + (sh RD (true, i) + (sh RD (true, i) + μ))), [⟨(true, i), sh RD (true, i) + (sh RD (true, i) + μ)⟩],
        PivotalGen.gen (Gen0.cross true i i μ), []⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, i) + (sh RD (true, i) + (sh RD (true, i) + μ))), [],
        PivotalGen.gen (Gen0.cross true i i (sh RD (true, i) + μ)), [⟨(true, i), μ⟩]⟩) _ _ ≫ eqToHom _) =
    (eqToHom _ ≫ coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, i) + (sh RD (true, i) + (sh RD (true, i) + μ))), [⟨(true, i), sh RD (true, i) + (sh RD (true, i) + μ)⟩],
        PivotalGen.gen (Gen0.cross true i i μ), []⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, i) + (sh RD (true, i) + (sh RD (true, i) + μ))), [],
        PivotalGen.gen (Gen0.cross true i i (sh RD (true, i) + μ)), [⟨(true, i), μ⟩]⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, i) + (sh RD (true, i) + (sh RD (true, i) + μ))), [⟨(true, i), sh RD (true, i) + (sh RD (true, i) + μ)⟩],
        PivotalGen.gen (Gen0.cross true i i μ), []⟩) _ _ ≫ eqToHom _)
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain3_key S.model ?t1 ?t1' _ ?t2 ?t2' _ ?t3 ?t3' _
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _),
      chain3_key S.model ?t4 ?t4' _ ?t5 ?t5' _ ?t6 ?t6' _
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 | t1' | t3 | t3' | t5 | t5' =>
      exact whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm
    case t2 | t2' | t4 | t4' | t6 | t6' => exact λ_ _
    repeat erw [layerAt_right_assoc]
    repeat erw [layerAt_left]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id, Category.comp_id]
    exact braid_reassoc _ _ (S.braid i (cross_up_reg i μ)
      (cross_up_reg i _) (cross_up_reg i _))
  all_goals rfl

/-- The actual CL all-equal braid relation, with arbitrary scalar parameters. -/
theorem klr_braid_self_rel (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [i, i, i] μ) (condUp [i, i, i] μ)
      (CL.relationCL RD k Sc (.klr μ (.braid i i i (by simp)))) = 0 := by
  change S.upEndAlg Sc [i, i, i] μ
    (KLR.Diagram.relation k (CL.qCL Sc) (.braid i i i (by simp))) = 0
  unfold KLR.Diagram.relation
  erw [map_sub, upEndAlg_of, upEndAlg_of]
  exact sub_eq_zero.mpr (S.readUp_braid_self Sc i μ)

end RouqFamily
end Categorification.TwoRep
