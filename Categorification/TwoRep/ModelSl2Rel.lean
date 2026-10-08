/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2

/-!
# The defining relations of `U` in the `sl₂` model

Verification, for the `sl₂` model of `Categorification.TwoRep.ModelSl2`, of the defining relations
of KL III's `U` (with CL's scalars `r_i = 1`): for each relation, read with its own outer regions,
the image of the relation under the interpretation `BicatInterp.interp (genImg hS) s t` vanishes.

* Biadjointness (KL III (3.1), (3.2); CL Definition 1.1 (1)): the four zigzag relations of the
  pivotal extension, from the triangle identities of `E ⊣ R` and of the normalized left
  adjunctions `R ⊣ E` (`zigL_up`, `zigL_down`, `zigR_up`, `zigR_down`; `zigL_eq`, `zigR_eq`).

The computation of an image goes through `BicatInterp`'s normal forms: the image of the diagram is
unfolded into images of layers (`layerI_pos`), the transports between words become images of free
2-morphisms (`eqToHom_word`), and an abstract normal-form lemma (`zig_key'`, `zag_key'`) reduces the
relation to the corresponding identity of the generator images in the graded-Hom bicategory.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]

namespace StrongSl2

variable {S : StrongSl2 k B} (hS : S.BBw)

attribute [local irreducible] KL3.Diagram.sh

/-! ## Biadjointness -/

/-- **The left zigzag on an upward strand** (KL III (3.1)): the triangle identity of the
normalized left adjunction `R ⊣ E`. -/
theorem zigL_up (r : ℤ) :
    (interp (genImg hS) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) r).functor.map
      (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) r
      (Pivotal.colourObj (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) :=
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg hS) _ _).functor.map
        (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg hS) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨rfl, sh_false_sh_true () r, rfl, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    refine zig_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(true, ()), r⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) r ⟶ rq (sh sl2RootDatum ((true, ()) : Letter Unit) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv sl2RootDatum).dual ⟨(true, ()), r⟩, rfl,
          sh_false_sh_true () r⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) ⟶ rq r))
      (λ_ _) (Iso.refl _) (Iso.refl _) (whiskerRightIso (λ_ _) _) (Iso.refl _) (λ_ _)
      (whiskerRightIso (λ_ _) _) (Iso.refl _)
      (gAdjL hS (S.qi r) (S.qi (sh sl2RootDatum ((true, ()) : Letter Unit) + r)) (S.qi_sh_true () r))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, whiskerRightIso_hom,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_hom]
      simp only [genImg]
      erw [Category.id_comp, Category.assoc]
      erw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    · simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, whiskerRightIso_inv,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_inv]
      simp only [genImg]
      erw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, Category.id_comp]
  all_goals rfl

/-- **The left zigzag on a downward strand** (KL III (3.1)): the triangle identity of
`E ⊣ R`. -/
theorem zigL_down (r : ℤ) :
    (interp (genImg hS) (sh sl2RootDatum ((false, ()) : Letter Unit) + r) r).functor.map
      (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum ((false, ()) : Letter Unit) + r) r
      (Pivotal.colourObj (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) :=
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg hS) _ _).functor.map
        (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg hS) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨rfl, sh_true_sh_false () r, rfl, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    refine zig_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(false, ()), r⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) r ⟶ rq (sh sl2RootDatum ((false, ()) : Letter Unit) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv sl2RootDatum).dual ⟨(false, ()), r⟩, rfl,
          sh_true_sh_false () r⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum ((false, ()) : Letter Unit) + r) ⟶ rq r))
      (λ_ _) (Iso.refl _) (Iso.refl _) (whiskerRightIso (λ_ _) _) (Iso.refl _) (λ_ _)
      (whiskerRightIso (λ_ _) _) (Iso.refl _)
      (S.gAdjE (S.qi (sh sl2RootDatum ((false, ()) : Letter Unit) + r)) (S.qi r) (S.qi_sh_false () r))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, whiskerRightIso_hom,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_hom]
      simp only [genImg]
      erw [Category.id_comp, Category.assoc]
      erw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    · simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, whiskerRightIso_inv,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_inv]
      simp only [genImg]
      erw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, Category.id_comp]
  all_goals rfl

/-- **The right zigzag on the dual of an upward strand** (KL III (3.2)): the other triangle
identity of the normalized left adjunction `R ⊣ E`. -/
theorem zigR_up (r : ℤ) :
    (interp (genImg hS) r (sh sl2RootDatum ((true, ()) : Letter Unit) + r)).functor.map
      (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) r (sh sl2RootDatum ((true, ()) : Letter Unit) + r)
      (Pivotal.dualObj (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) :=
    ⟨⟨sh_false_sh_true () r, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg hS) _ _).functor.map
        (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg hS) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨sh_false_sh_true () r, rfl, sh_false_sh_true () r, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨sh_false_sh_true () r, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    refine zag_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(true, ()), r⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) r ⟶ rq (sh sl2RootDatum ((true, ()) : Letter Unit) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv sl2RootDatum).dual ⟨(true, ()), r⟩, rfl,
          sh_false_sh_true () r⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) ⟶ rq r))
      (Iso.refl _) (λ_ _) (Iso.refl _) (whiskerRightIso (λ_ _) _) (λ_ _) (Iso.refl _)
      (whiskerRightIso (λ_ _) _) (Iso.refl _)
      (gAdjL hS (S.qi r) (S.qi (sh sl2RootDatum ((true, ()) : Letter Unit) + r)) (S.qi_sh_true () r))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, whiskerRightIso_hom,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_hom]
      simp only [genImg]
      erw [Category.id_comp, Category.assoc]
      erw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    · simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, whiskerRightIso_inv,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_inv]
      simp only [genImg]
      erw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, Category.id_comp]
  all_goals rfl



/-- **The right zigzag on the dual of a downward strand** (KL III (3.2)): the other triangle
identity of `E ⊣ R`. -/
theorem zigR_down (r : ℤ) :
    (interp (genImg hS) r (sh sl2RootDatum ((false, ()) : Letter Unit) + r)).functor.map
      (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) r (sh sl2RootDatum ((false, ()) : Letter Unit) + r)
      (Pivotal.dualObj (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) :=
    ⟨⟨sh_true_sh_false () r, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg hS) _ _).functor.map
        (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg hS) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨sh_true_sh_false () r, rfl, sh_true_sh_false () r, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨sh_true_sh_false () r, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    refine zag_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(false, ()), r⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) r ⟶ rq (sh sl2RootDatum ((false, ()) : Letter Unit) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv sl2RootDatum).dual ⟨(false, ()), r⟩, rfl,
          sh_true_sh_false () r⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum ((false, ()) : Letter Unit) + r) ⟶ rq r))
      (Iso.refl _) (λ_ _) (Iso.refl _) (whiskerRightIso (λ_ _) _) (λ_ _) (Iso.refl _)
      (whiskerRightIso (λ_ _) _) (Iso.refl _)
      (S.gAdjE (S.qi (sh sl2RootDatum ((false, ()) : Letter Unit) + r)) (S.qi r) (S.qi_sh_false () r))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, whiskerRightIso_hom,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_hom]
      simp only [genImg]
      erw [Category.id_comp, Category.assoc]
      erw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    · simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, whiskerRightIso_inv,
        lift_map₂_whiskerRight, lift_map₂_leftUnitor_inv]
      simp only [genImg]
      erw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, Category.id_comp]
  all_goals rfl


/-- **Biadjointness in the `sl₂` model**: the left zigzag relation of every strand. -/
theorem zigL_eq (c : Col Unit ℤ) :
    (interp (genImg hS) (sh sl2RootDatum c.l + c.r) c.r).functor.map
      (Pivotal.zigL (inv sl2RootDatum).toColourDuality c) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases i
  cases b
  · exact zigL_down hS r
  · exact zigL_up hS r

/-- **Biadjointness in the `sl₂` model**: the right zigzag relation of every strand. -/
theorem zigR_eq (c : Col Unit ℤ) :
    (interp (genImg hS) c.r (sh sl2RootDatum c.l + c.r)).functor.map
      (Pivotal.zigR (inv sl2RootDatum).toColourDuality c) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases i
  cases b
  · exact zigR_down hS r
  · exact zigR_up hS r

end StrongSl2

end Model

end Categorification.TwoRep
