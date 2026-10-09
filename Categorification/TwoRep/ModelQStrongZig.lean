/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongSl2

/-!
# Biadjointness in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.1 (1) (`eq_biadjoint1`, `eq_biadjoint2`; KL III (3.1), (3.2)):
in the model of `Categorification.TwoRep.ModelQStrong`, the four zigzag relations of the pivotal
extension hold for every strand: on an upward strand they are the triangle identities of the left
adjunction `R ⊣ E` (`QStrong.adjL`, the normalized left adjunction of the restriction to the
`α_i`-string), on a downward strand those of `E ⊣ R` (`QStrong.adjR`).

## Main results

* `QStrong.zigL_up`, `zigL_down`, `zigR_up`, `zigR_down`;
* `QStrong.zigL_eq`, `QStrong.zigR_eq`: the left and right zigzag relations of every strand.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

section Model

open GradedHomBicat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable {S : QStrong B C RD k Q} (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh

theorem sh_dn_add_sh_up (i : I) (r : X) :
    sh RD ((false, i) : Letter I) + (sh RD ((true, i) : Letter I) + r) = r := by
  rw [sh_up, sh_dn]; abel

theorem sh_up_add_sh_dn (i : I) (r : X) :
    sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + r) = r := by
  rw [sh_up, sh_dn]; abel

/-- **The left zigzag on an upward strand** (KL III (3.1)): the triangle identity of the left
adjunction `R ⊣ E`. -/
theorem zigL_up (i : I) (r : X) :
    (interp (genImg (S := S) Sc) (sh RD ((true, i) : Letter I) + r) r).functor.map
      (Pivotal.zigL (inv RD).toColourDuality ⟨(true, i), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig RD) (sh RD ((true, i) : Letter I) + r) r
      (Pivotal.colourObj (inv RD).toColourDuality ⟨(true, i), r⟩) :=
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg (S := S) Sc) _ _).functor.map
        (Pivotal.zigL (inv RD).toColourDuality ⟨(true, i), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc)
      ((interp (genImg (S := S) Sc) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨rfl, sh_dn_add_sh_up i r, rfl, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zig_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(true, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((true, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(true, i), r⟩, rfl, sh_dn_add_sh_up i r⟩ :
        rq (S := psig RD) (sh RD ((true, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (adjL (S := S) i (x := r) (y := sh RD ((true, i) : Letter I) + r) (up_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
  all_goals rfl

/-- **The left zigzag on a downward strand** (KL III (3.1)): the triangle identity of
`E ⊣ R`. -/
theorem zigL_down (i : I) (r : X) :
    (interp (genImg (S := S) Sc) (sh RD ((false, i) : Letter I) + r) r).functor.map
      (Pivotal.zigL (inv RD).toColourDuality ⟨(false, i), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig RD) (sh RD ((false, i) : Letter I) + r) r
      (Pivotal.colourObj (inv RD).toColourDuality ⟨(false, i), r⟩) :=
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg (S := S) Sc) _ _).functor.map
        (Pivotal.zigL (inv RD).toColourDuality ⟨(false, i), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc)
      ((interp (genImg (S := S) Sc) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨rfl, sh_up_add_sh_dn i r, rfl, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zig_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(false, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((false, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(false, i), r⟩, rfl, sh_up_add_sh_dn i r⟩ :
        rq (S := psig RD) (sh RD ((false, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.adjR i (x := sh RD ((false, i) : Letter I) + r) (y := r) (dn_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
  all_goals rfl

/-- **The right zigzag on the dual of an upward strand** (KL III (3.2)): the other triangle
identity of the left adjunction `R ⊣ E`. -/
theorem zigR_up (i : I) (r : X) :
    (interp (genImg (S := S) Sc) r (sh RD ((true, i) : Letter I) + r)).functor.map
      (Pivotal.zigR (inv RD).toColourDuality ⟨(true, i), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig RD) r (sh RD ((true, i) : Letter I) + r)
      (Pivotal.dualObj (inv RD).toColourDuality ⟨(true, i), r⟩) :=
    ⟨⟨sh_dn_add_sh_up i r, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg (S := S) Sc) _ _).functor.map
        (Pivotal.zigR (inv RD).toColourDuality ⟨(true, i), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc)
      ((interp (genImg (S := S) Sc) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨sh_dn_add_sh_up i r, rfl, sh_dn_add_sh_up i r, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨sh_dn_add_sh_up i r, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zag_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(true, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((true, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(true, i), r⟩, rfl, sh_dn_add_sh_up i r⟩ :
        rq (S := psig RD) (sh RD ((true, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (adjL (S := S) i (x := r) (y := sh RD ((true, i) : Letter I) + r) (up_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
  all_goals rfl

/-- **The right zigzag on the dual of a downward strand** (KL III (3.2)): the other triangle
identity of `E ⊣ R`. -/
theorem zigR_down (i : I) (r : X) :
    (interp (genImg (S := S) Sc) r (sh RD ((false, i) : Letter I) + r)).functor.map
      (Pivotal.zigR (inv RD).toColourDuality ⟨(false, i), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig RD) r (sh RD ((false, i) : Letter I) + r)
      (Pivotal.dualObj (inv RD).toColourDuality ⟨(false, i), r⟩) :=
    ⟨⟨sh_up_add_sh_dn i r, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg (S := S) Sc) _ _).functor.map
        (Pivotal.zigR (inv RD).toColourDuality ⟨(false, i), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc)
      ((interp (genImg (S := S) Sc) _ _).functor.map _), key]
    simp
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD,
    Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Interpretation.mapChain, Layer.wr, Layer.wl]
  set_option backward.isDefEq.respectTransparency false in
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2]
  rotate_left
  · exact ⟨⟨sh_up_add_sh_dn i r, rfl, sh_up_add_sh_dn i r, trivial⟩, rfl, rfl⟩
  · exact ⟨⟨sh_up_add_sh_dn i r, trivial⟩, rfl, rfl⟩
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, ← PrelaxFunctor.map₂_id]
  · unfold coreC core
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zag_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(false, i), r⟩, rfl, rfl⟩ :
        rq (S := psig RD) r ⟶ rq (sh RD ((false, i) : Letter I) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv RD).dual ⟨(false, i), r⟩, rfl, sh_up_add_sh_dn i r⟩ :
        rq (S := psig RD) (sh RD ((false, i) : Letter I) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.adjR i (x := sh RD ((false, i) : Letter I) + r) (y := r) (dn_reg i rfl rfl))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
  all_goals rfl

/-- **Biadjointness in the model**: the left zigzag relation of every strand. -/
theorem zigL_eq (c : Col I X) :
    (interp (genImg (S := S) Sc) (sh RD c.l + c.r) c.r).functor.map
      (Pivotal.zigL (inv RD).toColourDuality c) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases b
  · exact zigL_down (S := S) Sc i r
  · exact zigL_up (S := S) Sc i r

/-- **Biadjointness in the model**: the right zigzag relation of every strand. -/
theorem zigR_eq (c : Col I X) :
    (interp (genImg (S := S) Sc) c.r (sh RD c.l + c.r)).functor.map
      (Pivotal.zigR (inv RD).toColourDuality c) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases b
  · exact zigR_down (S := S) Sc i r
  · exact zigR_up (S := S) Sc i r

end QStrong

end Model

end Categorification.TwoRep
