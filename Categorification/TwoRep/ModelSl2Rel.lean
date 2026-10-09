/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2

/-!
# The defining relations of `U` in the `sl₂` model

Verification, for the `sl₂` model of `Categorification.TwoRep.ModelSl2`, of the defining relations
of KL III's `U` (with CL's scalars `r_i = 1`): for each relation, read with its own outer regions,
the image of the relation under the interpretation `BicatInterp.interp (genImg S) s t` vanishes.

* Biadjointness (KL III (3.1), (3.2); CL Definition 1.1 (1)): the four zigzag relations of the
  pivotal extension, from the triangle identities of `E ⊣ R` and of the normalized left
  adjunctions `R ⊣ E` (`zigL_up`, `zigL_down`, `zigR_up`, `zigR_down`; `zigL_eq`, `zigR_eq`).
* Cyclicity of dots (KL III (3.3); CL Definition 1.1 (2)): the upward dot rotated by a cup on the
  right and a cap on the left (`cycDotR`), or on the other side (`cycDotL`), is the downward dot.
  The first is the definition of the downward dot as a mate; the second is CL Lemma 4.1 for the
  normalized left adjunctions (`gDot_cyclic`), which holds.
* Cyclicity of crossings (KL III `eq_cyclic_cross-gen` for `i = j`): the upward crossing rotated
  by nested cups and caps on the right (`cycCrossR`) or on the left (`cycCrossL`) is the downward
  crossing; the second is CL Lemma 4.2 for the normalized left adjunctions (`gCross_cyclic`).
* The nilHecke relations on upward strands (KL III Def. 3.1 relations of `R(ν)`, for `sl₂`):
  `klr_sqEq`, `klr_slideLEq`, `klr_slideREq`, `klr_braid`, from `grCross_sq`, the dot slides and
  `grCross_braid`. Layers occupying the same word are compared through `chain2_key'`,
  `chain3_key'` and the evaluations `layerAt_*`.

The computation of an image goes through `BicatInterp`'s normal forms: the image of the diagram is
unfolded into images of layers (`layerI_pos`), the transports between words become images of free
2-morphisms (`eqToHom_word`), and an abstract normal-form lemma (`zig_key'`, `zag_key'`,
`rot_key`, `rotL_key`, `rot2_key`, `rot2L_key`) reduces the relation to the corresponding identity of the generator images
in the graded-Hom bicategory. Regions of a diagram that are equal but not definitionally so (such
as `λ` and `λ + i_X - i_X`) are first identified by generalizing them, before the images of the
layers are unfolded.
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

variable (S : StrongSl2 k B)

attribute [local irreducible] KL3.Diagram.sh

/-! ## Biadjointness -/

/-- **The left zigzag on an upward strand** (KL III (3.1)): the triangle identity of the
normalized left adjunction `R ⊣ E`. -/
theorem zigL_up (r : ℤ) :
    (interp (genImg S) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) r).functor.map
      (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) r
      (Pivotal.colourObj (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) :=
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg S) _ _).functor.map
        (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg S) _ _).functor.map _), key]
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
    dsimp only [Signature.endR_cons, Signature.endR_nil, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_dom_cup, Signature.pivotal_cod_cup,
      Signature.pivotal_left_cap, Signature.pivotal_right_cap, Signature.pivotal_dom_cap,
      Signature.pivotal_cod_cap, psig_colourSrc, psig_colourTgt, inv_dual]
    refine zig_key' S.model
      (e := FreeBicategory.Hom.of (⟨⟨(true, ()), r⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) r ⟶ rq (sh sl2RootDatum ((true, ()) : Letter Unit) + r)))
      (ρ := FreeBicategory.Hom.of (⟨(inv sl2RootDatum).dual ⟨(true, ()), r⟩, rfl,
          sh_false_sh_true () r⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum ((true, ()) : Letter Unit) + r) ⟶ rq r))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (gAdjL S (S.qi r) (S.qi (sh sl2RootDatum ((true, ()) : Letter Unit) + r)) (S.qi_sh_true () r))
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
theorem zigL_down (r : ℤ) :
    (interp (genImg S) (sh sl2RootDatum ((false, ()) : Letter Unit) + r) r).functor.map
      (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum ((false, ()) : Letter Unit) + r) r
      (Pivotal.colourObj (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) :=
    ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg S) _ _).functor.map
        (Pivotal.zigL (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg S) _ _).functor.map _), key]
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
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.gAdjE (S.qi (sh sl2RootDatum ((false, ()) : Letter Unit) + r)) (S.qi r) (S.qi_sh_false () r))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
  all_goals rfl

/-- **The right zigzag on the dual of an upward strand** (KL III (3.2)): the other triangle
identity of the normalized left adjunction `R ⊣ E`. -/
theorem zigR_up (r : ℤ) :
    (interp (genImg S) r (sh sl2RootDatum ((true, ()) : Letter Unit) + r)).functor.map
      (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) r (sh sl2RootDatum ((true, ()) : Letter Unit) + r)
      (Pivotal.dualObj (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) :=
    ⟨⟨sh_false_sh_true () r, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg S) _ _).functor.map
        (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(true, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg S) _ _).functor.map _), key]
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
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (gAdjL S (S.qi r) (S.qi (sh sl2RootDatum ((true, ()) : Letter Unit) + r)) (S.qi_sh_true () r))
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
theorem zigR_down (r : ℤ) :
    (interp (genImg S) r (sh sl2RootDatum ((false, ()) : Letter Unit) + r)).functor.map
      (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) = 𝟙 _ := by
  have hc : Cond (S := psig sl2RootDatum) r (sh sl2RootDatum ((false, ()) : Letter Unit) + r)
      (Pivotal.dualObj (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) :=
    ⟨⟨sh_true_sh_false () r, trivial⟩, rfl, rfl⟩
  suffices key : eqToHom (objI_pos _ _ hc).symm ≫
      (interp (genImg S) _ _).functor.map
        (Pivotal.zigR (inv sl2RootDatum).toColourDuality ⟨(false, ()), r⟩) ≫
      eqToHom (objI_pos _ _ hc) = 𝟙 _ by
    set_option backward.isDefEq.respectTransparency false in
    rw [eq_conj (objI_pos _ _ hc) (objI_pos _ _ hc) ((interp (genImg S) _ _).functor.map _), key]
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
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (S.gAdjE (S.qi (sh sl2RootDatum ((false, ()) : Letter Unit) + r)) (S.qi r) (S.qi_sh_false () r))
      _ _ ?_ ?_ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
  all_goals rfl


/-- **Biadjointness in the `sl₂` model**: the left zigzag relation of every strand. -/
theorem zigL_eq (c : Col Unit ℤ) :
    (interp (genImg S) (sh sl2RootDatum c.l + c.r) c.r).functor.map
      (Pivotal.zigL (inv sl2RootDatum).toColourDuality c) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases i
  cases b
  · exact zigL_down S r
  · exact zigL_up S r

/-- **Biadjointness in the `sl₂` model**: the right zigzag relation of every strand. -/
theorem zigR_eq (c : Col Unit ℤ) :
    (interp (genImg S) c.r (sh sl2RootDatum c.l + c.r)).functor.map
      (Pivotal.zigR (inv sl2RootDatum).toColourDuality c) = 𝟙 _ := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  cases i
  cases b
  · exact zigR_down S r
  · exact zigR_up S r

/-! ## Cyclicity of dots -/

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem sig0_colourSrc' (c : Col Unit ℤ) :
    (sig0 sl2RootDatum).colourSrc c = sh sl2RootDatum c.l + c.r := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem sig0_colourTgt' (c : Col Unit ℤ) : (sig0 sl2RootDatum).colourTgt c = c.r := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem sig0_dom_dot' (c : Col Unit ℤ) : (sig0 sl2RootDatum).dom (.dot c) = [c] := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem sig0_cod_dot' (c : Col Unit ℤ) : (sig0 sl2RootDatum).cod (.dot c) = [c] := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem sig0_dom_cross' (e : Bool) (i j : Unit) (ν : ℤ) :
    (sig0 sl2RootDatum).dom (.cross e i j ν) = wd sl2RootDatum ν [(e, i), (e, j)] := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem sig0_cod_cross' (e : Bool) (i j : Unit) (ν : ℤ) :
    (sig0 sl2RootDatum).cod (.cross e i j ν) = wd sl2RootDatum ν [(e, j), (e, i)] := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem dual_up' (i : Unit) : Letter.dual (up i) = dn i := rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem dual_dn' (i : Unit) : Letter.dual (dn i) = up i := rfl

/-- Transporting the counit of `R ⊣ E` along an equality of indices. -/
theorem gAdjL_counit_congr (a b b' : ℤ) (h : b = b') (p : a + 1 = b) (p' : a + 1 = b')
    (e : S.gEc a b' p' ≫ S.gRc a b' p' = S.gEc a b p ≫ S.gRc a b p) :
    eqToHom e ≫ (gAdjL S a b p).counit = (gAdjL S a b' p').counit := by
  subst h; simp

set_option maxHeartbeats 2000000 in
/-- **Cyclicity of the dot, right rotation** (KL III (3.3), left-hand picture): the upward dot
rotated by a cup on the right and a cap on the left is the downward dot. -/
theorem cycDotR (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn ()] : ℤ) μ).functor.map
      (rotDotR sl2RootDatum () μ) =
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn ()] : ℤ) μ).functor.map
      (downDot sl2RootDatum () μ) := by
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [dn ()] : ℤ) μ
      (ob sl2RootDatum μ [dn ()]) := ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, rotDotR, downDot, mkD, Diagram.layers_mk, layList_cons,
    layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_up']
  generalize_proofs
  generalize hx : sh sl2RootDatum (up ()) + (sh sl2RootDatum (dn ()) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_true_sh_false () μ
  subst hxμ
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3,
    layerI_pos _ _ _ _ ?c4]
  case c1 | c2 | c3 | c4 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sig0_colourSrc', sig0_colourTgt', sig0_dom_dot']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  erw [eqToHom_word ?w2 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_dot', inv_dual, dual_up',
      sig0_colourTgt', sig0_colourSrc']
    refine rot_key S.model
      (r := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl,
          sh_true_sh_false () x⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (gAdjL S (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (S.gDot (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc1)) _)
      _ ?hg1
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg2
      (Iso.refl _) (Iso.refl _) (eqToIso (by refine comp_of_congr hx rfl ?_; exact congrArg (Col.mk (dn ())) hx)) (Iso.refl _) _ ?hg3
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg4
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hc1 => exact congrArg (Col.mk (dn ())) hx
    case hg1 =>
      simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp, whiskerRightIso_hom,
        eqToIso.hom, lift_map₂_whiskerRight, lift_map₂_eqToHom]
      erw [eqToHom_refl, id_whiskerRight, Category.comp_id]
      rfl
    case hg2 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    case hg3 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id, eqToIso.inv,
        lift_map₂_eqToHom]
      exact gAdjL_counit_congr S _ _ _ (congrArg S.qi hx) _ _ _
    case hg4 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      simp only [genImg, gDotR]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, hx, sig0_dom_dot', sig0_cod_dot']

set_option maxHeartbeats 2000000 in
/-- **Cyclicity of the dot, left rotation** (KL III (3.3), right-hand picture): the upward dot
rotated by a cup on the left and a cap on the right is the downward dot. This is CL Lemma 4.1
for the normalized left adjunctions, which holds (`cyclic_dot_leftAdjN`). -/
theorem cycDotL (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn ()] : ℤ) μ).functor.map
      (rotDotL sl2RootDatum () μ) =
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn ()] : ℤ) μ).functor.map
      (downDot sl2RootDatum () μ) := by
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [dn ()] : ℤ) μ
      (ob sl2RootDatum μ [dn ()]) := ⟨⟨rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, rotDotL, downDot, mkD, Diagram.layers_mk, layList_cons,
    layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_dn']
  generalize_proofs
  generalize hx : sh sl2RootDatum (up ()) + (sh sl2RootDatum (dn ()) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_true_sh_false () μ
  subst hxμ
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3,
    layerI_pos _ _ _ _ ?c4]
  case c1 | c2 | c3 | c4 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sig0_colourSrc', sig0_colourTgt', sig0_dom_dot']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_dot', inv_dual, dual_up',
      sig0_colourTgt', sig0_colourSrc']
    refine rotL_key S.model
      (r := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl,
          sh_true_sh_false () x⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (S.gDot (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg1
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg2
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg3
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg4
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hg1 | hg2 | hg3 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    case hg4 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      simp only [genImg]
      rw [← gDot_cyclic S]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, sig0_dom_dot']

omit [GradedBicategory.IsLinear B k] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- Transporting the crossing along an equality of the middle index. -/
theorem gCross_congr (a b b' c : ℤ) (h : b = b') (p₁ : a + 1 = b) (p₂ : b + 1 = c)
    (p₁' : a + 1 = b') (p₂' : b' + 1 = c)
    (e₁ : S.gEc a b' p₁' ≫ S.gEc b' c p₂' = S.gEc a b p₁ ≫ S.gEc b c p₂)
    (e₂ : S.gEc a b p₁ ≫ S.gEc b c p₂ = S.gEc a b' p₁' ≫ S.gEc b' c p₂') :
    eqToHom e₁ ≫ S.gCross a b c p₁ p₂ ≫ eqToHom e₂ = S.gCross a b' c p₁' p₂' := by
  subst h; simp

set_option maxHeartbeats 2000000 in
/-- **Cyclicity of the crossing, right rotation** (KL III `eq_cyclic_cross-gen`, left-hand
picture): the upward crossing rotated by nested cups on the right and nested caps on the left is
the downward crossing. -/
theorem cycCrossR (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn (), dn ()] : ℤ) μ).functor.map
      (rotCrossR sl2RootDatum () () μ) =
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn (), dn ()] : ℤ) μ).functor.map
      (downCross sl2RootDatum () () μ) := by
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [dn (), dn ()] : ℤ) μ
      (ob sl2RootDatum μ [dn (), dn ()]) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, rotCrossR, downCross, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_up']
  generalize_proofs
  generalize hy : sh sl2RootDatum (up ()) +
    (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + μ)) = y at *
  have hyμ : y = sh sl2RootDatum (dn ()) + μ := by rw [← hy]; exact sh_true_sh_false () _
  subst hyμ
  generalize hx : sh sl2RootDatum (up ()) + (sh sl2RootDatum (dn ()) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_true_sh_false () μ
  subst hxμ
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3,
    layerI_pos _ _ _ _ ?c4, layerI_pos _ _ _ _ ?c5, layerI_pos _ _ _ _ ?c6]
  case c1 | c2 | c3 | c4 | c5 | c6 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sig0_colourSrc', sig0_colourTgt', sig0_dom_cross']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w3 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w4 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w5 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross', sig0_cod_cross',
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up', sig0_colourTgt', sig0_colourSrc']
    refine rot2_key S.model
      (r₁ := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e₁ := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl,
          sh_true_sh_false () x⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (r₂ := FreeBicategory.Hom.of (⟨⟨dn (), sh sl2RootDatum (dn ()) + x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶
          rq (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x))))
      (e₂ := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) +
          (sh sl2RootDatum (dn ()) + x)⟩, rfl, sh_true_sh_false () _⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x)) ⟶
          rq (sh sl2RootDatum (dn ()) + x)))
      (gAdjL S (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (gAdjL S (S.qi (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x)))
        (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi_sh_false () _))
      (S.gCross (S.qi (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x)))
        (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () _) (S.qi_sh_false () x))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc1)) _)
      _ ?hg1
      (Iso.refl _) (α_ _ _ _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc2)) _)
      _ ?hg2
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up ())) hy))
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up ())) hy)) _ ?hg3
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hx rfl ?_; exact congrArg (Col.mk (dn ())) hx))
      (Iso.refl _) _ ?hg4
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (dn ())) hy))
      (Iso.refl _) _ ?hg5
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hc1 => exact congrArg (Col.mk (dn ())) hx
    case hc2 => exact congrArg (Col.mk (dn ())) hy
    case hg1 | hg2 =>
      simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp, whiskerRightIso_hom,
        eqToIso.hom, lift_map₂_whiskerRight, lift_map₂_eqToHom]
      erw [eqToHom_refl, id_whiskerRight, Category.comp_id]
      rfl
    case hg3 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      exact S.gCross_congr _ _ _ _ (congrArg S.qi hy) _ _ _ _ _ _
    case hg4 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id, eqToIso.inv,
        lift_map₂_eqToHom]
      exact gAdjL_counit_congr S _ _ _ (congrArg S.qi hx) _ _ _
    case hg5 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id, eqToIso.inv,
        lift_map₂_eqToHom]
      exact gAdjL_counit_congr S _ _ _ (congrArg S.qi hy) _ _ _
    case hg6 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      simp only [genImg, gCrossR]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, hx, hy, sig0_dom_cross', sig0_cod_cross']

set_option maxHeartbeats 2000000 in
/-- **Cyclicity of the crossing, left rotation** (KL III `eq_cyclic_cross-gen`, right-hand
picture): the upward crossing rotated by nested cups on the left and nested caps on the right is
the downward crossing. This is CL Lemma 4.2 for the normalized left adjunctions, which holds
(`cyclic_cross`). -/
theorem cycCrossL (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn (), dn ()] : ℤ) μ).functor.map
      (rotCrossL sl2RootDatum () () μ) =
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [dn (), dn ()] : ℤ) μ).functor.map
      (downCross sl2RootDatum () () μ) := by
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [dn (), dn ()] : ℤ) μ
      (ob sl2RootDatum μ [dn (), dn ()]) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, rotCrossL, downCross, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_dn']
  generalize_proofs
  generalize hy : sh sl2RootDatum (up ()) +
    (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + μ)) = y at *
  have hyμ : y = sh sl2RootDatum (dn ()) + μ := by rw [← hy]; exact sh_true_sh_false () _
  subst hyμ
  generalize hx : sh sl2RootDatum (up ()) + (sh sl2RootDatum (dn ()) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_true_sh_false () μ
  subst hxμ
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3,
    layerI_pos _ _ _ _ ?c4, layerI_pos _ _ _ _ ?c5, layerI_pos _ _ _ _ ?c6]
  case c1 | c2 | c3 | c4 | c5 | c6 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sig0_colourSrc', sig0_colourTgt', sig0_dom_cross']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w3 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w4 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w5 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross', sig0_cod_cross',
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up', sig0_colourTgt', sig0_colourSrc']
    refine rot2L_key S.model
      (r₁ := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e₁ := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl,
          sh_true_sh_false () x⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (r₂ := FreeBicategory.Hom.of (⟨⟨dn (), sh sl2RootDatum (dn ()) + x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶
          rq (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x))))
      (e₂ := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) +
          (sh sl2RootDatum (dn ()) + x)⟩, rfl, sh_true_sh_false () _⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x)) ⟶
          rq (sh sl2RootDatum (dn ()) + x)))
      (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x)))
        (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi_sh_false () _))
      (S.gCross (S.qi (sh sl2RootDatum (dn ()) + (sh sl2RootDatum (dn ()) + x)))
        (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () _) (S.qi_sh_false () x))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg1
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg2
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up ())) hy))
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up ())) hy)) _ ?hg3
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg4
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg5
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hg1 | hg2 | hg4 | hg5 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      rfl
    case hg3 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      exact S.gCross_congr _ _ _ _ (congrArg S.qi hy) _ _ _ _ _ _
    case hg6 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      simp only [genImg]
      rw [← gCross_cyclic S]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, hy, sig0_dom_cross', sig0_cod_cross']


/-! ## The nilHecke relations on upward strands -/

omit [GradedBicategory.IsLinear B k] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem gCross_sq (a b c : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) :
    S.gCross a b c h₁ h₂ ≫ S.gCross a b c h₁ h₂ = 0 := by
  subst h₁ h₂; exact S.grCross_sq a

set_option maxHeartbeats 2000000 in
/-- `τ² = 0` on two upward strands. -/
theorem klr_sqEq (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
      (upDiag sl2RootDatum μ (KLR.Diagram.X2 () () ≫ KLR.Diagram.X2 () ())) = 0 := by
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ
      (ob sl2RootDatum μ (ups [(), ()])) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, layers_upDiag, Diagram.layers_comp,
    KLR.Diagram.layers_dl, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Interpretation.mapChain]
  simp only [Limits.comp_zero, Limits.zero_comp]
  set_option backward.isDefEq.respectTransparency false in
  simp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups, wt_cons, wt_nil,
    List.nil_append, List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc', sig0_colourTgt',
        sig0_dom_cross']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
      Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
      sig0_dom_cross', sig0_cod_cross', wd_cons, wd_nil, wt_cons, wt_nil, sig0_colourTgt',
      sig0_colourSrc', List.map_nil, List.map_cons, List.nil_append, List.append_nil,
      List.cons_append]
    refine (chain2_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _
      ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?_
    rw [layerAt_whole, layerAt_whole]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
    exact S.gCross_sq _ _ _ _ _
  all_goals simp [sig0_dom_cross', Layer.dom, ob]


omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem gDot_slide_right (a b c : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) :
    S.gCross a b c h₁ h₂ ≫ S.gEc a b h₁ ◁ S.gDot b c h₂ -
        S.gDot a b h₁ ▷ S.gEc b c h₂ ≫ S.gCross a b c h₁ h₂ = 𝟙 _ := by
  subst h₁ h₂; exact S.grDotN_slide_right a

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_X2_D0 (μ : ℤ) :
    upDiag sl2RootDatum μ (KLR.Diagram.X2 () () ≫ KLR.Diagram.D0 () ()) =
      mkD sl2RootDatum μ [([], .cross true () (), []), ([], .dot (up ()), [up ()])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_D1_X2 (μ : ℤ) :
    upDiag sl2RootDatum μ (KLR.Diagram.D1 () () ≫ KLR.Diagram.X2 () ()) =
      mkD sl2RootDatum μ [([up ()], .dot (up ()), []), ([], .cross true () (), [])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_id2 (μ : ℤ) :
    upDiag sl2RootDatum μ (𝟙 (KLR.Diagram.ob [(), ()])) =
      mkD sl2RootDatum μ (t := [up (), up ()]) [] rfl := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The dot slide `τ (x on the left strand) - (x on the right strand) τ = 1`. -/
theorem klr_slideLEq (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (KLR.Diagram.X2 () () ≫ KLR.Diagram.D0 () ())) -
      (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (KLR.Diagram.D1 () () ≫ KLR.Diagram.X2 () ())) -
      (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (𝟙 _)) = 0 := by
  rw [upDiag_X2_D0, upDiag_D1_X2, upDiag_id2]
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ
      (ob sl2RootDatum μ [up (), up ()]) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Limits.comp_zero, Limits.zero_comp, Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  try rw [layerI_pos _ _ _ _ ?c3]
  case c1 | c2 | c3 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc', sig0_colourTgt',
        sig0_dom_cross', sig0_dom_dot']
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross', sig0_cod_cross', sig0_dom_dot', sig0_cod_dot', wd_cons, wd_nil, wt_cons,
    wt_nil, sig0_colourTgt', sig0_colourSrc']
  rw [chain2_key' S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ (𝟙 _) (𝟙 _),
    chain2_key' S.model ?t3 ?t3' _ ?t4 ?t4' _ _ _ _ _ (𝟙 _) (𝟙 _)]
  case t1 => exact (λ_ _) ≪≫ (ρ_ _)
  case t1' => exact (λ_ _) ≪≫ (ρ_ _)
  case t2 => exact whiskerLeftIso _ (ρ_ _)
  case t2' => exact whiskerLeftIso _ (ρ_ _)
  case t3 => exact λ_ _
  case t3' => exact λ_ _
  case t4 => exact (λ_ _) ≪≫ (ρ_ _)
  case t4' => exact (λ_ _) ≪≫ (ρ_ _)
  erw [layerAt_whole, layerAt_right, layerAt_left]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  refine sub_eq_zero.2 ((S.gDot_slide_right _ _ _ _ _).trans ?_)
  erw [Category.id_comp, eqToHom_trans]
  exact (eqToHom_refl _ _).symm

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem gDot_slide (a b c : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) :
    S.gEc a b h₁ ◁ S.gDot b c h₂ ≫ S.gCross a b c h₁ h₂ -
        S.gCross a b c h₁ h₂ ≫ S.gDot a b h₁ ▷ S.gEc b c h₂ = 𝟙 _ := by
  subst h₁ h₂; exact S.grDotN_slide a

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_D0_X2 (μ : ℤ) :
    upDiag sl2RootDatum μ (KLR.Diagram.D0 () () ≫ KLR.Diagram.X2 () ()) =
      mkD sl2RootDatum μ [([], .dot (up ()), [up ()]), ([], .cross true () (), [])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_X2_D1 (μ : ℤ) :
    upDiag sl2RootDatum μ (KLR.Diagram.X2 () () ≫ KLR.Diagram.D1 () ()) =
      mkD sl2RootDatum μ [([], .cross true () (), []), ([up ()], .dot (up ()), [])]
        ⟨rfl, rfl, rfl⟩ := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The dot slide `(x on the left strand) τ - τ (x on the right strand) = 1`. -/
theorem klr_slideREq (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (KLR.Diagram.D0 () () ≫ KLR.Diagram.X2 () ())) -
      (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (KLR.Diagram.X2 () () ≫ KLR.Diagram.D1 () ())) -
      (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (𝟙 _)) = 0 := by
  rw [upDiag_D0_X2, upDiag_X2_D1, upDiag_id2]
  have hc : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ [up (), up ()] : ℤ) μ
      (ob sl2RootDatum μ [up (), up ()]) := ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Limits.comp_zero, Limits.zero_comp, Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  try rw [layerI_pos _ _ _ _ ?c3]
  case c1 | c2 | c3 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc', sig0_colourTgt',
        sig0_dom_cross', sig0_dom_dot']
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross', sig0_cod_cross', sig0_dom_dot', sig0_cod_dot', wd_cons, wd_nil, wt_cons,
    wt_nil, sig0_colourTgt', sig0_colourSrc']
  rw [chain2_key' S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ (𝟙 _) (𝟙 _),
    chain2_key' S.model ?t3 ?t3' _ ?t4 ?t4' _ _ _ _ _ (𝟙 _) (𝟙 _)]
  case t1 => exact whiskerLeftIso _ (ρ_ _)
  case t1' => exact whiskerLeftIso _ (ρ_ _)
  case t2 => exact (λ_ _) ≪≫ (ρ_ _)
  case t2' => exact (λ_ _) ≪≫ (ρ_ _)
  case t3 => exact (λ_ _) ≪≫ (ρ_ _)
  case t3' => exact (λ_ _) ≪≫ (ρ_ _)
  case t4 => exact λ_ _
  case t4' => exact λ_ _
  erw [layerAt_whole, layerAt_right, layerAt_left]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  refine sub_eq_zero.2 ((S.gDot_slide _ _ _ _ _).trans ?_)
  erw [Category.id_comp, eqToHom_trans]
  exact (eqToHom_refl _ _).symm

omit [GradedBicategory.IsLinear B k] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem gCross_braid (a b c d : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) (h₃ : c + 1 = d) :
    S.gEc a b h₁ ◁ S.gCross b c d h₂ h₃ ≫
        ((α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).inv ≫
          S.gCross a b c h₁ h₂ ▷ S.gEc c d h₃ ≫
          (α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).hom) ≫
        S.gEc a b h₁ ◁ S.gCross b c d h₂ h₃ =
      ((α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).inv ≫
          S.gCross a b c h₁ h₂ ▷ S.gEc c d h₃ ≫
          (α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).hom) ≫
        S.gEc a b h₁ ◁ S.gCross b c d h₂ h₃ ≫
        ((α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).inv ≫
          S.gCross a b c h₁ h₂ ▷ S.gEc c d h₃ ≫
          (α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).hom) := by
  subst h₁ h₂ h₃; exact S.grCross_braid a

omit [GradedBicategory.IsLinear B k] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The braid relation with the bracketing `(E E) E`. -/
theorem gCross_braid' (a b c d : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) (h₃ : c + 1 = d) :
    ((α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).hom ≫
        S.gEc a b h₁ ◁ S.gCross b c d h₂ h₃ ≫
          (α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).inv) ≫
        S.gCross a b c h₁ h₂ ▷ S.gEc c d h₃ ≫
        ((α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).hom ≫
          S.gEc a b h₁ ◁ S.gCross b c d h₂ h₃ ≫
            (α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).inv) =
      S.gCross a b c h₁ h₂ ▷ S.gEc c d h₃ ≫
        ((α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).hom ≫
          S.gEc a b h₁ ◁ S.gCross b c d h₂ h₃ ≫
            (α_ (S.gEc a b h₁) (S.gEc b c h₂) (S.gEc c d h₃)).inv) ≫
        S.gCross a b c h₁ h₂ ▷ S.gEc c d h₃ := by
  have h := S.gCross_braid a b c d h₁ h₂ h₃
  simp only [Category.assoc] at h ⊢
  rw [reassoc_of% h]
  simp

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_braidL (μ : ℤ) :
    upDiag sl2RootDatum μ (KLR.Diagram.braidL () () ()) =
      mkD sl2RootDatum μ [([], .cross true () (), [up ()]), ([up ()], .cross true () (), []),
        ([], .cross true () (), [up ()])] ⟨rfl, rfl, rfl, rfl⟩ := by
  rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem upDiag_braidR (μ : ℤ) :
    upDiag sl2RootDatum μ (KLR.Diagram.braidR () () ()) =
      mkD sl2RootDatum μ [([up ()], .cross true () (), []), ([], .cross true () (), [up ()]),
        ([up ()], .cross true () (), [])] ⟨rfl, rfl, rfl, rfl⟩ := by
  rfl

set_option maxHeartbeats 10000000 in
/-- The braid relation on three upward strands. -/
theorem klr_braid (μ : ℤ) :
    (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (KLR.Diagram.braidL () () ())) -
      (interp (genImg S) (KL3.Diagram.wt sl2RootDatum μ [up (), up (), up ()] : ℤ) μ).functor.map
        (upDiag sl2RootDatum μ (KLR.Diagram.braidR () () ())) = 0 := by
  rw [upDiag_braidL, upDiag_braidR]
  have hc : Cond (S := psig sl2RootDatum)
      (KL3.Diagram.wt sl2RootDatum μ [up (), up (), up ()] : ℤ) μ
      (ob sl2RootDatum μ [up (), up (), up ()]) := ⟨⟨rfl, rfl, rfl, trivial⟩, rfl, rfl⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Limits.comp_zero, Limits.zero_comp, Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  case c1 | c2 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc', sig0_colourTgt',
        sig0_dom_cross']
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross', sig0_cod_cross', wd_cons, wd_nil, wt_cons, wt_nil, sig0_colourTgt',
    sig0_colourSrc']
  rw [chain3_key' S.model ?t1 ?t1' _ ?t2 ?t2' _ ?t3 ?t3' _ _ _ _ _ _ _ (𝟙 _) (𝟙 _),
    chain3_key' S.model ?t4 ?t4' _ ?t5 ?t5' _ ?t6 ?t6' _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)]
  case t1 | t1' | t3 | t3' | t5 | t5' =>
    exact whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm
  case t2 | t2' | t4 | t4' | t6 | t6' => exact λ_ _
  erw [layerAt_right_assoc, layerAt_left]
  simp only [genImg_cross_true, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  refine sub_eq_zero.2 ?_
  exact S.gCross_braid' _ _ _ _ _ _ _

end StrongSl2

end Model

end Categorification.TwoRep
