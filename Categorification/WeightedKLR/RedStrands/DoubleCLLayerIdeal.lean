/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackRelations

/-!
# Functors out of a free 2-category agreeing on layers modulo an ideal

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A downward KLR diagram placed in a
signed context and sent through the cover functor agrees with its signed reflection only up
to red-negligible terms: the two functors differ on red dots. This file proves the generic
statement: two functors out of a free 2-category whose values on every layer differ by a
morphism of a class `N` closed under sums and composition on both sides differ by a
morphism of `N` on every diagram (`functor_map_sub_mem_of_layer`) and on every linear
combination of diagrams (`freeLift_map_sub_mem_of_layer`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams

universe u₀ u₁ u₂ w₁ w₂ w

variable {S : Signature.{u₀, u₁, u₂}} {E : Type w₁} [Category.{w₂} E] [Preadditive E]

/-- Two functors out of the free 2-category whose values on every layer differ (up to the
identifications of the images of well-formed objects) by a morphism of a class `N` closed
under zero, sums and composition on both sides differ by a morphism of `N` on every diagram
with a well-formed source. -/
theorem functor_map_sub_mem_of_layer (F G : Obj S ⥤ E)
    (hobj : ∀ a : Obj S, a.WF → F.obj a = G.obj a)
    (N : ∀ {x y : E}, (x ⟶ y) → Prop) (h0 : ∀ {x y : E}, N (0 : x ⟶ y))
    (hadd : ∀ {x y : E} {f g : x ⟶ y}, N f → N g → N (f + g))
    (hpre : ∀ {x y z : E} (h : x ⟶ y) {f : y ⟶ z}, N f → N (h ≫ f))
    (hpost : ∀ {x y z : E} {f : x ⟶ y} (h : y ⟶ z), N f → N (f ≫ h))
    (hlay : ∀ (L : Layer S) (hv : L.Valid), N (F.map (Diagram.ofLayer L hv) -
      eqToHom (hobj _ hv.wf_dom) ≫ G.map (Diagram.ofLayer L hv) ≫
        eqToHom (hobj _ hv.wf_cod).symm)) :
    ∀ {a b : Obj S} (d : a ⟶ b) (ha : a.WF),
      N (F.map d - eqToHom (hobj a ha) ≫ G.map d ≫
        eqToHom (hobj b ((Diagram.chain d).wf ha)).symm) := by
  intro a b d ha
  obtain ⟨ls, h⟩ := d
  induction ls generalizing a with
  | nil =>
    obtain rfl : a = b := by assumption
    have e : (⟨[], rfl⟩ : a ⟶ a) = 𝟙 a := rfl
    rw [e]; simpa using h0
  | cons L ls ih =>
    rename_i h
    obtain ⟨hv, rfl, hc⟩ := h
    have : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ b) =
        Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b) := rfl
    rw [this]
    set e₁ := hobj _ hv.wf_dom
    set e₂ := hobj _ hv.wf_cod
    set e₃ := hobj b ((Diagram.chain (Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b))).wf
      hv.wf_dom)
    have key : F.map (Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b)) -
        eqToHom e₁ ≫ G.map (Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b)) ≫ eqToHom e₃.symm =
        (F.map (Diagram.ofLayer L hv) - eqToHom e₁ ≫ G.map (Diagram.ofLayer L hv) ≫
          eqToHom e₂.symm) ≫ F.map (⟨ls, hc⟩ : L.cod ⟶ b) +
        (eqToHom e₁ ≫ G.map (Diagram.ofLayer L hv) ≫ eqToHom e₂.symm) ≫
          (F.map (⟨ls, hc⟩ : L.cod ⟶ b) - eqToHom e₂ ≫ G.map (⟨ls, hc⟩ : L.cod ⟶ b) ≫
            eqToHom e₃.symm) := by
      simp only [F.map_comp, G.map_comp, Preadditive.sub_comp, Preadditive.comp_sub,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      abel
    rw [key]
    exact hadd (hpost _ (hlay L hv)) (hpre _ (ih hv.wf_cod hc))

variable {R : Type w} [CommRing R] [Linear R E]

theorem freeLift_obj_eq (F G : Obj S ⥤ E) (hobj : ∀ a : Obj S, a.WF → F.obj a = G.obj a)
    (a : Obj S) (ha : a.WF) :
    (freeLift R F).obj (Free.of R a) = (freeLift R G).obj (Free.of R a) := hobj a ha

/-- The linear form of `functor_map_sub_mem_of_layer`: if moreover `N` is closed under
scalar multiples, the linear extensions of the two functors differ by a morphism of `N` on
every linear combination of diagrams with well-formed source and target. -/
theorem freeLift_map_sub_mem_of_layer (F G : Obj S ⥤ E)
    (hobj : ∀ a : Obj S, a.WF → F.obj a = G.obj a)
    (N : ∀ {x y : E}, (x ⟶ y) → Prop) (h0 : ∀ {x y : E}, N (0 : x ⟶ y))
    (hadd : ∀ {x y : E} {f g : x ⟶ y}, N f → N g → N (f + g))
    (hsmul : ∀ {x y : E} (r : R) {f : x ⟶ y}, N f → N (r • f))
    (hpre : ∀ {x y z : E} (h : x ⟶ y) {f : y ⟶ z}, N f → N (h ≫ f))
    (hpost : ∀ {x y z : E} {f : x ⟶ y} (h : y ⟶ z), N f → N (f ≫ h))
    (hlay : ∀ (L : Layer S) (hv : L.Valid), N (F.map (Diagram.ofLayer L hv) -
      eqToHom (hobj _ hv.wf_dom) ≫ G.map (Diagram.ofLayer L hv) ≫
        eqToHom (hobj _ hv.wf_cod).symm))
    {a b : Obj S} (f : LinDiagram R a b) (ha : a.WF) (hb : b.WF) :
    N ((freeLift R F).map f - eqToHom (freeLift_obj_eq (R := R) F G hobj a ha) ≫ (freeLift R G).map f ≫
      eqToHom (freeLift_obj_eq (R := R) F G hobj b hb).symm) := by
  induction f using Finsupp.induction_linear with
  | zero => simpa using h0
  | add f g hf hg =>
    have e : (freeLift R F).map (f + g) - eqToHom (freeLift_obj_eq (R := R) F G hobj a ha) ≫ (freeLift R G).map (f + g) ≫
        eqToHom (freeLift_obj_eq (R := R) F G hobj b hb).symm =
        ((freeLift R F).map f - eqToHom (freeLift_obj_eq (R := R) F G hobj a ha) ≫ (freeLift R G).map f ≫
          eqToHom (freeLift_obj_eq (R := R) F G hobj b hb).symm) +
        ((freeLift R F).map g - eqToHom (freeLift_obj_eq (R := R) F G hobj a ha) ≫ (freeLift R G).map g ≫
          eqToHom (freeLift_obj_eq (R := R) F G hobj b hb).symm) := by
      rw [Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
      abel
    rw [e]; exact hadd hf hg
  | single d r =>
    have hd := functor_map_sub_mem_of_layer F G hobj N h0 hadd hpre hpost hlay d ha
    rw [freeLift_map_single, freeLift_map_single]
    convert hsmul r hd using 1
    all_goals try rfl
    rw [smul_sub, Linear.smul_comp, Linear.comp_smul]

end Categorification.Stendhal.DoubleDiagram
