/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCyc

/-!
# Actual dotted-bubble relations for ungraded Rouquier families

The four original CL dotted-bubble relations vanish under the admissible
interpretation of `RouqFamily.genImg`. The comparison uses the original constructed
left adjunction and downward dot. In the local naming convention, diagrammatic
`cwReal` is `RouqLoc.ccw`, and `ccwReal` is `RouqLoc.cw`, at the same region weight.

CL, arXiv:1111.1431v3, §2.5, and Brundan, arXiv:1501.00350v1, Lemma 3.1.
The proof uses the existing local inverse-component identities, not grading or
bounds on endomorphism spaces. The four relations and their generator images are
independent of `Sc.r`, so the scalar data are arbitrary. Curls, decompositions,
and soundness of the aggregate non-mixed presentation are separate assertions.
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

/-- The empty word in its unchanged outer region. -/
abbrev bubbleNil (μ : X) : Admissible (S := psig RD) μ μ :=
  ⟨ob RD μ [], ⟨trivial, rfl, rfl⟩⟩
private abbrev bubbleDU (i : I) (μ : X) : Admissible (S := psig RD) μ μ :=
  ⟨ob RD μ [dn i, up i],
    ⟨⟨sh_dn_add_sh_up i μ, rfl, trivial⟩, rfl, sh_dn_add_sh_up i μ⟩⟩

private theorem bubble_cupDn (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleDU i μ)
        (mkD RD μ [([], .cup (dn i), [])] ⟨rfl, rfl⟩)) =
      (S.adj i (cross_up_reg i μ)).unit := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleNil, bubbleDU, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _))
      _ _ _ _ _ (𝟙 _) (eqToHom ?e)).trans ?main
    case main =>
      erw [layerAt_whole, PrelaxFunctor.map₂_id, Category.id_comp, lift_map₂_eqToHom,
        eqToHom_refl, Category.comp_id]
      rfl
    case e =>
      apply fw_eq
      · change ([⟨dn i, sh RD (up i) + μ⟩,
          ⟨up i, sh RD (dn i) + (sh RD (up i) + μ)⟩] : List (Col I X)) = _
        rw [sh_dn_add_sh_up]
        rfl
  case w0 => rfl
  case w1 =>
    change ([⟨dn i, sh RD (up i) + μ⟩,
      ⟨up i, sh RD (dn i) + (sh RD (up i) + μ)⟩] : List (Col I X)) = _
    rw [sh_dn_add_sh_up]
    rfl

private theorem bubble_capUp (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleNil μ)
        (mkD RD μ [([], .cap (up i), [])] ⟨rfl, rfl⟩)) =
      (S.adjL i (cross_up_reg i μ)).counit := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleNil, bubbleDU, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _))
      _ _ _ _ _ (eqToHom ?e) (𝟙 _)).trans ?main
    case main =>
      erw [layerAt_whole, lift_map₂_eqToHom, eqToHom_refl, Category.id_comp,
        PrelaxFunctor.map₂_id, Category.comp_id]
      rfl
    case e => rfl
  case w0 => rfl
  case w1 => rfl

private theorem bubble_dotUp (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleDU i μ)
        (mkD RD μ [([dn i], .dot (up i), [])] ⟨rfl, rfl⟩)) =
      S.dot i (cross_up_reg i μ) ▷ S.F i (cross_up_reg i μ) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleDU, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil,
    List.nil_append, List.cons_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _]
  · unfold coreC core
    refine (chain1_key S.model (λ_ _) (λ_ _)
      _ _ _ _ _ (eqToHom ?e) (eqToHom ?e')).trans ?main
    case main =>
      erw [layerAt_left, lift_map₂_eqToHom,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    case e => rfl
    case e' => rfl
  case w0 => rfl

private abbrev bubbleUD (i : I) (μ : X) : Admissible (S := psig RD) μ μ :=
  ⟨ob RD μ [up i, dn i],
    ⟨⟨sh_up_add_sh_dn i μ, rfl, trivial⟩, rfl, sh_up_add_sh_dn i μ⟩⟩

private theorem bubble_cupUp (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleUD i μ)
        (mkD RD μ [([], .cup (up i), [])] ⟨rfl, rfl⟩)) =
      (S.adjL i (cross_dn_reg i μ)).unit := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleNil, bubbleUD, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _))
      _ _ _ _ _ (𝟙 _) (eqToHom ?e)).trans ?main
    case main =>
      erw [layerAt_whole, PrelaxFunctor.map₂_id, Category.id_comp, lift_map₂_eqToHom,
        eqToHom_refl, Category.comp_id]
      rfl
    case e =>
      apply fw_eq
      · change ([⟨up i, sh RD (dn i) + μ⟩,
          ⟨dn i, sh RD (up i) + (sh RD (dn i) + μ)⟩] : List (Col I X)) = _
        rw [sh_up_add_sh_dn]
        rfl
  case w0 => rfl
  case w1 =>
    change ([⟨up i, sh RD (dn i) + μ⟩,
      ⟨dn i, sh RD (up i) + (sh RD (dn i) + μ)⟩] : List (Col I X)) = _
    rw [sh_up_add_sh_dn]
    rfl

private theorem bubble_capDn (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleNil μ)
        (mkD RD μ [([], .cap (dn i), [])] ⟨rfl, rfl⟩)) =
      (S.adj i (cross_dn_reg i μ)).counit := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleNil, bubbleUD, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_nil, wt_nil, List.nil_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _))
      _ _ _ _ _ (eqToHom ?e) (𝟙 _)).trans ?main
    case main =>
      erw [layerAt_whole, lift_map₂_eqToHom, eqToHom_refl, Category.id_comp,
        PrelaxFunctor.map₂_id, Category.comp_id]
      rfl
    case e => rfl
  case w0 => rfl
  case w1 => rfl

private theorem bubble_dotDn (i : I) (μ : X) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleUD i μ)
        (mkD RD μ [([up i], .dot (dn i), [])] ⟨rfl, rfl⟩)) =
      S.dotDn i (cross_dn_reg i μ) ▷ S.E i (cross_dn_reg i μ) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, bubbleUD, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil,
    List.nil_append, List.cons_append, Shape.dom]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?w0 _]
  · unfold coreC core
    refine (chain1_key S.model (λ_ _) (λ_ _)
      _ _ _ _ _ (eqToHom ?e) (eqToHom ?e')).trans ?main
    case main =>
      erw [layerAt_left, lift_map₂_eqToHom,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    case e => rfl
    case e' => rfl
  case w0 => rfl

private theorem bubble_dots (μ : X) (u : List (Letter I)) (l : Letter I)
    (v : List (Letter I)) (h : Cond (S := psig RD) μ μ (ob RD μ (u ++ [l] ++ v)))
    (m : ℕ) :
    (S.interp Sc μ μ).map (ObjectProperty.homMk (X := ⟨_, h⟩) (Y := ⟨_, h⟩)
      (dots RD μ u l v m)) =
    powComp ((S.interp Sc μ μ).map (ObjectProperty.homMk (X := ⟨_, h⟩) (Y := ⟨_, h⟩)
      (mkD RD μ [(u, .dot l, v)] ⟨rfl, rfl⟩))) m := by
  induction m with
  | zero => exact (S.interp Sc μ μ).map_id _
  | succ m ih =>
    have hd : dots RD μ u l v (m + 1) =
        dots RD μ u l v m ≫ mkD RD μ [(u, .dot l, v)] ⟨rfl, rfl⟩ := by
      unfold dots
      erw [mkD_comp]
      congr 1
      exact List.replicate_succ'
    rw [hd]
    change (S.interp Sc μ μ).map
      ((ObjectProperty.homMk (X := ⟨_, h⟩) (Y := ⟨_, h⟩) (dots RD μ u l v m)) ≫
        ObjectProperty.homMk (X := ⟨_, h⟩) (Y := ⟨_, h⟩)
          (mkD RD μ [(u, .dot l, v)] ⟨rfl, rfl⟩)) = _
    rw [Functor.map_comp, ih, powComp_succ]

/-- The actual counterclockwise diagram is the local `cw` bubble. -/
theorem bubble_ccwReal (i : I) (μ : X) (m : ℕ) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleNil μ)
        (ccwReal RD μ i m)) =
      (S.loc i (sub_add_cancel μ (RD.iX i)) (cross_up_reg i μ)).cw (m : ℤ) := by
  have hd : ccwReal RD μ i m =
      mkD RD μ [([], .cup (dn i), [])] ⟨rfl, rfl⟩ ≫
        dots RD μ [dn i] (up i) [] m ≫
          mkD RD μ [([], .cap (up i), [])] ⟨rfl, rfl⟩ := by
    unfold ccwReal dots
    erw [mkD_comp, mkD_comp]
    rfl
  rw [hd]
  change (S.interp Sc μ μ).map
    ((ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleDU i μ)
      (mkD RD μ [([], .cup (dn i), [])] ⟨rfl, rfl⟩)) ≫
      (ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleDU i μ)
        (dots RD μ [dn i] (up i) [] m)) ≫
      (ObjectProperty.homMk (X := bubbleDU i μ) (Y := bubbleNil μ)
        (mkD RD μ [([], .cap (up i), [])] ⟨rfl, rfl⟩))) = _
  erw [Functor.map_comp, Functor.map_comp, bubble_cupDn, bubble_capUp, bubble_dots,
    bubble_dotUp, ← powComp_whiskerRight]
  rw [RouqLoc.cw_of_nonneg (by omega), Int.toNat_natCast]
  change _ = ((S.adj i (cross_up_reg i μ)).unit ≫
    powComp (S.dot i (cross_up_reg i μ)) m ▷ S.F i (cross_up_reg i μ)) ≫ _
  erw [Category.assoc]
  rfl

/-- The actual clockwise diagram is the local `ccw` bubble. -/
theorem bubble_cwReal (i : I) (μ : X) (m : ℕ) :
    (S.interp Sc μ μ).map
      (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleNil μ)
        (cwReal RD μ i m)) =
      (S.loc i (cross_dn_reg i μ) rfl).ccw (m : ℤ) := by
  have hd : cwReal RD μ i m =
      mkD RD μ [([], .cup (up i), [])] ⟨rfl, rfl⟩ ≫
        dots RD μ [up i] (dn i) [] m ≫
          mkD RD μ [([], .cap (dn i), [])] ⟨rfl, rfl⟩ := by
    unfold cwReal dots
    erw [mkD_comp, mkD_comp]
    rfl
  rw [hd]
  change (S.interp Sc μ μ).map
    ((ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleUD i μ)
      (mkD RD μ [([], .cup (up i), [])] ⟨rfl, rfl⟩)) ≫
      (ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleUD i μ)
        (dots RD μ [up i] (dn i) [] m)) ≫
      (ObjectProperty.homMk (X := bubbleUD i μ) (Y := bubbleNil μ)
        (mkD RD μ [([], .cap (dn i), [])] ⟨rfl, rfl⟩))) = _
  erw [Functor.map_comp, Functor.map_comp, bubble_cupUp, bubble_capDn, bubble_dots,
    bubble_dotDn, ← powComp_whiskerRight]
  rw [RouqLoc.ccw_of_nonneg (by omega), Int.toNat_natCast]
  erw [S.dotDn_eq_rightMate]
  change (S.adjL i (cross_dn_reg i μ)).unit ≫
    powComp (S.loc i (cross_dn_reg i μ) rfl).dotD₁ m ▷ S.E i (cross_dn_reg i μ) ≫
      (S.adj i (cross_dn_reg i μ)).counit = _
  rw [RouqLoc.mirror_capD]
  rw [S.adjL_eq i (sub_add_cancel (sh RD (dn i) + μ) (RD.iX i))
    (cross_dn_reg i μ) rfl]
  rfl

/-- The original negative-degree cw bubble relation vanishes. -/
theorem cwNeg_rel (i : I) (μ : X) (m : ℕ)
    (hm : (m : ℤ) < ip RD i μ - 1) :
    admissibleMap (S.genImg Sc) (bubbleNil μ).property (bubbleNil μ).property
      (CL.relationCL RD k Sc (.cwNeg i μ m hm)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _ (LinDiagram.of (cwReal RD μ i m)) = 0
  erw [admissibleMap_of, bubble_cwReal]
  exact (S.loc i (cross_dn_reg i μ) rfl).ccw_of_lt (by change (m : ℤ) < RD.pair (RD.iY i) μ - 1 at hm; omega) hm

/-- The original degree-zero cw bubble relation vanishes. -/
theorem cwOne_rel (i : I) (μ : X) (hm : 1 ≤ ip RD i μ) :
    admissibleMap (S.genImg Sc) (bubbleNil μ).property (bubbleNil μ).property
      (CL.relationCL RD k Sc (.cwOne i μ hm)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (cwReal RD μ i (ip RD i μ - 1).toNat) - LinDiagram.of (𝟙 _)) = 0
  erw [map_sub]
  apply sub_eq_zero.mpr
  erw [admissibleMap_of, admissibleMap_of]
  change (S.interp Sc μ μ).map
    (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleNil μ)
      (cwReal RD μ i (ip RD i μ - 1).toNat)) = 𝟙 (𝟙 (S.obj μ))
  erw [bubble_cwReal]
  rw [Int.toNat_of_nonneg (by omega)]
  exact ((S.loc i (cross_dn_reg i μ) rfl).ccw_self (by change 1 ≤ RD.pair (RD.iY i) μ at hm; omega))

/-- The original negative-degree ccw bubble relation vanishes. -/
theorem ccwNeg_rel (i : I) (μ : X) (m : ℕ)
    (hm : (m : ℤ) < -ip RD i μ - 1) :
    admissibleMap (S.genImg Sc) (bubbleNil μ).property (bubbleNil μ).property
      (CL.relationCL RD k Sc (.ccwNeg i μ m hm)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _ (LinDiagram.of (ccwReal RD μ i m)) = 0
  erw [admissibleMap_of, bubble_ccwReal]
  exact (S.loc i (sub_add_cancel μ (RD.iX i)) (cross_up_reg i μ)).cw_of_lt (by change (m : ℤ) < -RD.pair (RD.iY i) μ - 1 at hm; omega) hm

/-- The original degree-zero ccw bubble relation vanishes. -/
theorem ccwOne_rel (i : I) (μ : X) (hm : ip RD i μ ≤ -1) :
    admissibleMap (S.genImg Sc) (bubbleNil μ).property (bubbleNil μ).property
      (CL.relationCL RD k Sc (.ccwOne i μ hm)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (ccwReal RD μ i (-ip RD i μ - 1).toNat) - LinDiagram.of (𝟙 _)) = 0
  erw [map_sub]
  apply sub_eq_zero.mpr
  erw [admissibleMap_of, admissibleMap_of]
  change (S.interp Sc μ μ).map
    (ObjectProperty.homMk (X := bubbleNil μ) (Y := bubbleNil μ)
      (ccwReal RD μ i (-ip RD i μ - 1).toNat)) = 𝟙 (𝟙 (S.obj μ))
  erw [bubble_ccwReal]
  rw [Int.toNat_of_nonneg (by omega)]
  exact ((S.loc i (sub_add_cancel μ (RD.iX i)) (cross_up_reg i μ)).cw_self (by change RD.pair (RD.iY i) μ ≤ -1 at hm; omega))

end RouqFamily
end Categorification.TwoRep
