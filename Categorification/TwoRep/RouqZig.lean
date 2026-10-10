/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqInterp

/-!
# Ungraded zigzag relations on admissible words

The two zigzags for each oriented strand evaluate to identities in `RouqFamily.interp`.
The corresponding linear relations vanish under `admissibleMap`. The left adjunction is
constructed from Rouquier's local inverses, by Brundan arXiv:1501.00350v1, Theorem 4.3;
no grading, finiteness or zero-object assumption is used.

These are the biadjunction relations needed for the non-mixed presentation, not a claim
that all non-mixed relations have already been checked.
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

/-- The admissible one-letter word. -/
def colourAdmissible (c : Col I X) : Admissible (S := psig RD) (sh RD c.l + c.r) c.r :=
  ⟨Pivotal.colourObj (inv RD).toColourDuality c, ⟨⟨rfl, trivial⟩, rfl, rfl⟩⟩

theorem sh_dn_add_sh_up (i : I) (r : X) :
    sh RD ((false, i) : Letter I) + (sh RD ((true, i) : Letter I) + r) = r := by
  rw [sh_up, sh_dn]; abel

/-- The left zigzag on an upward strand. -/
theorem zigL_up (i : I) (r : X) :
    (S.interp Sc (sh RD ((true, i) : Letter I) + r) r).map
      (ObjectProperty.homMk (X := colourAdmissible ⟨(true, i), r⟩)
        (Y := colourAdmissible ⟨(true, i), r⟩)
        (Pivotal.zigL (inv RD).toColourDuality ⟨(true, i), r⟩)) = 𝟙 _ := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, colourAdmissible, Pivotal.zigL]
  refine (admissibleChain_congr _ (Diagram.layers_leftZigzag _ _ _ _ _) _ _ _).trans ?_
  dsimp only [Pivotal.cupD, Pivotal.capD, Diagram.layer, Diagram.cast, Diagram.layers,
    List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, admissibleChain, Layer.wr, Layer.wl]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  change _ = 𝟙 (S.model.lift.map _)
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zig_key' S.model
      (a := fo (S := psig RD) r)
      (b := fo (S := psig RD) (sh RD ((true, i) : Letter I) + r))
      (e := FreeBicategory.Hom.of (⟨⟨(true, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((true, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(true, i), r⟩, rfl, sh_dn_add_sh_up i r⟩ :
        rq (S := psig RD) (sh RD ((true, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.adjL i (x := r) (y := sh RD ((true, i) : Letter I) + r) (up_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
  all_goals rfl
theorem sh_up_add_sh_dn (i : I) (r : X) :
    sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + r) = r := by
  rw [sh_up, sh_dn]; abel

/-- The admissible dual one-letter word with the regions exchanged. -/
def dualAdmissible (c : Col I X) : Admissible (S := psig RD) c.r (sh RD c.l + c.r) :=
  ⟨Pivotal.dualObj (inv RD).toColourDuality c, by
    obtain ⟨⟨b, i⟩, r⟩ := c
    cases b
    · exact ⟨⟨sh_up_add_sh_dn i r, trivial⟩, rfl, rfl⟩
    · exact ⟨⟨sh_dn_add_sh_up i r, trivial⟩, rfl, rfl⟩⟩

/-- The left zigzag on a downward strand. -/
theorem zigL_down (i : I) (r : X) :
    (S.interp Sc (sh RD ((false, i) : Letter I) + r) r).map
      (ObjectProperty.homMk (X := colourAdmissible ⟨(false, i), r⟩)
        (Y := colourAdmissible ⟨(false, i), r⟩)
        (Pivotal.zigL (inv RD).toColourDuality ⟨(false, i), r⟩)) = 𝟙 _ := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, colourAdmissible, Pivotal.zigL]
  refine (admissibleChain_congr _ (Diagram.layers_leftZigzag _ _ _ _ _) _ _ _).trans ?_
  dsimp only [Pivotal.cupD, Pivotal.capD, Diagram.layer, Diagram.cast, Diagram.layers,
    List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, admissibleChain, Layer.wr, Layer.wl]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  change _ = 𝟙 (S.model.lift.map _)
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zig_key' S.model
      (a := fo (S := psig RD) r)
      (b := fo (S := psig RD) (sh RD ((false, i) : Letter I) + r))
      (e := FreeBicategory.Hom.of (⟨⟨(false, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((false, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(false, i), r⟩, rfl, sh_up_add_sh_dn i r⟩ :
        rq (S := psig RD) (sh RD ((false, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.adj i (x := sh RD ((false, i) : Letter I) + r) (y := r) (dn_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
  all_goals rfl

/-- The right zigzag on the dual of an upward strand. -/
theorem zigR_up (i : I) (r : X) :
    (S.interp Sc r (sh RD ((true, i) : Letter I) + r)).map
      (ObjectProperty.homMk (X := dualAdmissible ⟨(true, i), r⟩)
        (Y := dualAdmissible ⟨(true, i), r⟩)
        (Pivotal.zigR (inv RD).toColourDuality ⟨(true, i), r⟩)) = 𝟙 _ := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, dualAdmissible, Pivotal.zigR]
  refine (admissibleChain_congr _ (Diagram.layers_rightZigzag _ _ _ _ _) _ _ _).trans ?_
  dsimp only [Pivotal.cupD, Pivotal.capD, Diagram.layer, Diagram.cast, Diagram.layers,
    List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, admissibleChain, Layer.wr, Layer.wl]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  change _ = 𝟙 (S.model.lift.map _)
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zag_key' S.model
      (a := fo (S := psig RD) r)
      (b := fo (S := psig RD) (sh RD ((true, i) : Letter I) + r))
      (e := FreeBicategory.Hom.of (⟨⟨(true, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((true, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(true, i), r⟩, rfl, sh_dn_add_sh_up i r⟩ :
        rq (S := psig RD) (sh RD ((true, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.adjL i (x := r) (y := sh RD ((true, i) : Letter I) + r) (up_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
  all_goals rfl

/-- The right zigzag on the dual of a downward strand. -/
theorem zigR_down (i : I) (r : X) :
    (S.interp Sc r (sh RD ((false, i) : Letter I) + r)).map
      (ObjectProperty.homMk (X := dualAdmissible ⟨(false, i), r⟩)
        (Y := dualAdmissible ⟨(false, i), r⟩)
        (Pivotal.zigR (inv RD).toColourDuality ⟨(false, i), r⟩)) = 𝟙 _ := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, dualAdmissible, Pivotal.zigR]
  refine (admissibleChain_congr _ (Diagram.layers_rightZigzag _ _ _ _ _) _ _ _).trans ?_
  dsimp only [Pivotal.cupD, Pivotal.capD, Diagram.layer, Diagram.cast, Diagram.layers,
    List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, admissibleChain, Layer.wr, Layer.wl]
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  change _ = 𝟙 (S.model.lift.map _)
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zag_key' S.model
      (a := fo (S := psig RD) r)
      (b := fo (S := psig RD) (sh RD ((false, i) : Letter I) + r))
      (e := FreeBicategory.Hom.of (⟨⟨(false, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((false, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(false, i), r⟩, rfl, sh_up_add_sh_dn i r⟩ :
        rq (S := psig RD) (sh RD ((false, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.adj i (x := sh RD ((false, i) : Letter I) + r) (y := r) (dn_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
  all_goals rfl

/-- The left zigzag relation for every oriented strand in the ungraded interpretation. -/
theorem zigL_eq (c : Col I X) :
    (S.interp Sc (sh RD c.l + c.r) c.r).map
      (ObjectProperty.homMk (X := colourAdmissible c) (Y := colourAdmissible c)
        (Pivotal.zigL (inv RD).toColourDuality c)) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases b
  · exact S.zigL_down Sc i r
  · exact S.zigL_up Sc i r

/-- The right zigzag relation for every oriented strand in the ungraded interpretation. -/
theorem zigR_eq (c : Col I X) :
    (S.interp Sc c.r (sh RD c.l + c.r)).map
      (ObjectProperty.homMk (X := dualAdmissible c) (Y := dualAdmissible c)
        (Pivotal.zigR (inv RD).toColourDuality c)) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases b
  · exact S.zigR_down Sc i r
  · exact S.zigR_up Sc i r

/-- The linear left-zigzag relation vanishes without using a zero object. -/
theorem zigL_rel (c : Col I X) :
    admissibleMap (k := k) (S.genImg Sc) (colourAdmissible c).property
      (colourAdmissible c).property
      (LinDiagram.of (Pivotal.zigL (inv RD).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0 := by
  erw [map_sub, admissibleMap_of, admissibleMap_of]
  change (S.interp Sc (sh RD c.l + c.r) c.r).map _ -
    (S.interp Sc (sh RD c.l + c.r) c.r).map (𝟙 (colourAdmissible c)) = 0
  erw [S.zigL_eq, CategoryTheory.Functor.map_id]
  exact sub_self _

/-- The linear right-zigzag relation vanishes without using a zero object. -/
theorem zigR_rel (c : Col I X) :
    admissibleMap (k := k) (S.genImg Sc) (dualAdmissible c).property
      (dualAdmissible c).property
      (LinDiagram.of (Pivotal.zigR (inv RD).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0 := by
  erw [map_sub, admissibleMap_of, admissibleMap_of]
  change (S.interp Sc c.r (sh RD c.l + c.r)).map _ -
    (S.interp Sc c.r (sh RD c.l + c.r)).map (𝟙 (dualAdmissible c)) = 0
  erw [S.zigR_eq, CategoryTheory.Functor.map_id]
  exact sub_self _

end RouqFamily
end Categorification.TwoRep
