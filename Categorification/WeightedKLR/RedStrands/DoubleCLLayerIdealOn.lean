/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLLayerIdeal

/-!
# Functors agreeing on layers modulo an ideal, on a class of objects

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A variant of
`functor_map_sub_mem_of_layer` in which the two functors are only compared on objects
satisfying a predicate `P` that is preserved by every valid layer
(`functor_map_sub_mem_of_layer_on`, `freeLift_map_sub_mem_of_layer_on`). For the downward
KLR relations, `P` says that a boundary word has at most one red letter: on such words the
downward translation and the reflected upward KLR diagrams agree on every layer up to red dots.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams

universe u₀ u₁ u₂ w₁ w₂ w

variable {S : Signature.{u₀, u₁, u₂}} {E : Type w₁} [Category.{w₂} E] [Preadditive E]

/-- Two functors out of the free 2-category whose values on every layer with domain in a
layer-stable class `P` differ by a morphism of an ideal-like class `N` differ by a morphism of
`N` on every diagram with well-formed source in `P`. -/
theorem functor_map_sub_mem_of_layer_on (F G : Obj S ⥤ E) (P : Obj S → Prop)
    (hP : ∀ (L : Layer S), L.Valid → P L.dom → P L.cod)
    (hobj : ∀ a : Obj S, a.WF → P a → F.obj a = G.obj a)
    (N : ∀ {x y : E}, (x ⟶ y) → Prop) (h0 : ∀ {x y : E}, N (0 : x ⟶ y))
    (hadd : ∀ {x y : E} {f g : x ⟶ y}, N f → N g → N (f + g))
    (hpre : ∀ {x y z : E} (h : x ⟶ y) {f : y ⟶ z}, N f → N (h ≫ f))
    (hpost : ∀ {x y z : E} {f : x ⟶ y} (h : y ⟶ z), N f → N (f ≫ h))
    (hlay : ∀ (L : Layer S) (hv : L.Valid) (hd : P L.dom),
      N (F.map (Diagram.ofLayer L hv) -
        eqToHom (hobj _ hv.wf_dom hd) ≫ G.map (Diagram.ofLayer L hv) ≫
          eqToHom (hobj _ hv.wf_cod (hP L hv hd)).symm)) :
    ∀ {a b : Obj S} (d : a ⟶ b) (ha : a.WF) (hpa : P a) (hpb : P b),
      N (F.map d - eqToHom (hobj a ha hpa) ≫ G.map d ≫
        eqToHom (hobj b ((Diagram.chain d).wf ha) hpb).symm) := by
  intro a b d ha hpa hpb
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
    have hpc := hP L hv hpa
    set e₁ := hobj _ hv.wf_dom hpa
    set e₂ := hobj _ hv.wf_cod hpc
    set e₃ := hobj b ((Diagram.chain (Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b))).wf
      hv.wf_dom) hpb
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
    exact hadd (hpost _ (hlay L hv hpa)) (hpre _ (ih hv.wf_cod hpc hc))

variable {R : Type w} [CommRing R] [Linear R E]

theorem freeLift_obj_eq_on (F G : Obj S ⥤ E) (P : Obj S → Prop)
    (hobj : ∀ a : Obj S, a.WF → P a → F.obj a = G.obj a) (a : Obj S) (ha : a.WF) (hpa : P a) :
    (freeLift R F).obj (Free.of R a) = (freeLift R G).obj (Free.of R a) := hobj a ha hpa

/-- The linear form of `functor_map_sub_mem_of_layer_on`. -/
theorem freeLift_map_sub_mem_of_layer_on (F G : Obj S ⥤ E) (P : Obj S → Prop)
    (hP : ∀ (L : Layer S), L.Valid → P L.dom → P L.cod)
    (hobj : ∀ a : Obj S, a.WF → P a → F.obj a = G.obj a)
    (N : ∀ {x y : E}, (x ⟶ y) → Prop) (h0 : ∀ {x y : E}, N (0 : x ⟶ y))
    (hadd : ∀ {x y : E} {f g : x ⟶ y}, N f → N g → N (f + g))
    (hsmul : ∀ {x y : E} (r : R) {f : x ⟶ y}, N f → N (r • f))
    (hpre : ∀ {x y z : E} (h : x ⟶ y) {f : y ⟶ z}, N f → N (h ≫ f))
    (hpost : ∀ {x y z : E} {f : x ⟶ y} (h : y ⟶ z), N f → N (f ≫ h))
    (hlay : ∀ (L : Layer S) (hv : L.Valid) (hd : P L.dom),
      N (F.map (Diagram.ofLayer L hv) -
        eqToHom (hobj _ hv.wf_dom hd) ≫ G.map (Diagram.ofLayer L hv) ≫
          eqToHom (hobj _ hv.wf_cod (hP L hv hd)).symm))
    {a b : Obj S} (f : LinDiagram R a b) (ha : a.WF) (hb : b.WF) (hpa : P a) (hpb : P b) :
    N ((freeLift R F).map f - eqToHom (freeLift_obj_eq_on (R := R) F G P hobj a ha hpa) ≫
      (freeLift R G).map f ≫ eqToHom (freeLift_obj_eq_on (R := R) F G P hobj b hb hpb).symm) := by
  induction f using Finsupp.induction_linear with
  | zero => simpa using h0
  | add f g hf hg =>
    rw [Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
    convert hadd hf hg using 1
    abel
  | single d r =>
    have hd := functor_map_sub_mem_of_layer_on F G P hP hobj N h0 hadd hpre hpost hlay d ha
      hpa hpb
    rw [freeLift_map_single, freeLift_map_single]
    convert hsmul r hd using 1
    all_goals try rfl
    rw [smul_sub, Linear.smul_comp, Linear.comp_smul]

end Categorification.Stendhal.DoubleDiagram
