/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackDiagram
import StringDiagrams.LayerMap.Generators
import StringDiagrams.Transport

/-!
# Transferring black KL relations through reflection

Webster, arXiv:1309.3796v3, Definitions 2.4 and 4.24 and the proof of
Lemma 4.29. The black relations required by the straightening argument
are read in physical word order after a vertical reflection. Here the
reflected black presentation uses the KL III parameters. Its geometrical
transport maps a whiskered relation to the relation whiskered on the
opposite sides, so the fixed red prefix can then be attached.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
  {ℓ : ℕ} (Λ : Fin ℓ → X)

local notation "S" => psig RD
local notation "T" => signature RD Λ

private abbrev reflectColour (c : Col I X) : X × DoubleStrand I ℓ := (c.r, .inl c.l)

private theorem mirrorWord_wd (μ : X) (s : List (Letter I)) :
    ((wd RD μ s).map (reflectColour (ℓ := ℓ))).reverse =
      colours RD Λ μ (blackWord s) := by
  induction s with
  | nil => rfl
  | cons l s ih =>
    simp only [wd_cons, List.map_cons, List.reverse_cons, ih]
    have hw : blackWord (ℓ := ℓ) (l :: s) = blackWord s ++ [.inl l] := by
      simp [blackWord]
    rw [hw, colours_append, endWeight_blackWord]
    rfl

private theorem shapeOf_gen (g : (S).Gen) :
    (shapeOf RD g).gen RD ((S).right g) = g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · change PivotalGen.cup (⟨c.l, sh RD c.l.dual + (sh RD c.l + c.r)⟩ : Col I X) = _
    rw [← add_assoc, sh_dual_add_sh, zero_add]
    cases c
    rfl
  · rfl

private def reflectedGen (g : (S).Gen) : (T).Gen :=
  ((S).right g, .black (Sig.shape (shapeOf RD g)))

/-- Reflect a black KL signature into the physical left-to-right signed
signature. A strand retains its orientation and colour. -/
def blackMirror : SigMirror S T where
  region := id
  colour := reflectColour
  colourSrc _ := rfl
  colourTgt c := by
    change c.r + sh RD c.l = sh RD c.l + c.r
    exact add_comm _ _
  gen := reflectedGen RD Λ
  dom g := by
    let h := shapeOf RD g
    let μ := (S).right g
    have hd := Shape.dom_gen (RD := RD) μ h
    rw [shapeOf_gen] at hd
    change colours RD Λ μ ((Sig.shape h).dom.map Sum.inl) = _
    rw [hd, mirrorWord_wd, Sig.shape_dom]
    rfl
  cod g := by
    let h := shapeOf RD g
    let μ := (S).right g
    have hc := Shape.cod_gen (RD := RD) μ h
    rw [shapeOf_gen] at hc
    change colours RD Λ μ ((Sig.shape h).cod.map Sum.inl) = _
    rw [hc, mirrorWord_wd, Sig.shape_cod]
    rfl
  left _ := rfl
  right g := by
    let h := shapeOf RD g
    let μ := (S).right g
    have hg := Shape.left_gen (RD := RD) μ h
    rw [shapeOf_gen] at hg
    change endWeight RD Λ μ ((Sig.shape h).dom.map Sum.inl) = (S).left g
    rw [Sig.shape_dom]
    exact (endWeight_blackWord RD Λ μ h.dom).trans hg.symm

@[simp] theorem blackMirror_obj_ob (μ : X) (s : List (Letter I)) :
    (blackMirror RD Λ).obj (ob RD μ s) = obj RD Λ μ (blackWord s) := by
  apply Obj.ext
  · exact ob_endR RD _ _
  · exact mirrorWord_wd RD Λ _ _

private theorem mirror_layer_lay (μ : X) (u v : List (Letter I)) (g : Shape I) :
    (blackMirror RD Λ).layer (lay RD μ u g v) =
      layer RD Λ μ (blackWord v) (.black (Sig.shape g)) (blackWord u) := by
  have hs : shapeOf RD (g.gen RD (wt RD μ v)) = g := by cases g <;> rfl
  have hwt : endWeight RD Λ (wt RD μ v) ((Sig.shape g).dom.map Sum.inl) =
      wt RD (wt RD μ v) g.dom := by
    rw [Sig.shape_dom]
    exact endWeight_blackWord RD Λ _ _
  apply Layer.ext
  · change (S).endR ((S).right (g.gen RD (wt RD μ v))) (wd RD μ v) = μ
    rw [Shape.right_gen, endR_wd]
  · exact mirrorWord_wd RD Λ _ _
  · change ((S).right (g.gen RD (wt RD μ v)), Move.black (Sig.shape (shapeOf RD
       (g.gen RD (wt RD μ v))))) = (endWeight RD Λ μ (blackWord v), .black (Sig.shape g))
    rw [Shape.right_gen, endWeight_blackWord, hs]
  · change ((wd RD (wt RD μ (g.dom ++ v)) u).map reflectColour).reverse =
      colours RD Λ (endWeight RD Λ (endWeight RD Λ μ (blackWord v))
        ((Sig.shape g).dom.map Sum.inl)) (blackWord u)
    rw [wt_append, endWeight_blackWord, hwt, mirrorWord_wd]

variable {k : Type w} [CommRing k]

/-- Reflect a black linear combination before placing it in a signed context. -/
def blackMirrorLinear {a b : Obj S} :
    LinDiagram k a b →ₗ[k] LinDiagram k ((blackMirror RD Λ).obj a) ((blackMirror RD Λ).obj b) :=
  Finsupp.lmapDomain k k (blackMirror RD Λ).toLayerMap.map

@[simp] theorem blackMirrorLinear_of {a b : Obj S} (d : a ⟶ b) :
    blackMirrorLinear RD Λ (LinDiagram.of (R := k) d) =
      LinDiagram.of ((blackMirror RD Λ).toLayerMap.map d) :=
  Finsupp.mapDomain_single

/-- Adjoin the black KL III relations to a signed presentation. These are
local relations and hence can be whiskered by arbitrary signed words. -/
def addBlackKLRelations (P : Presentation.{w, max u v} T k) : Presentation.{w, max u v} T k :=
  P.addRels (pres RD k).Rel ((blackMirror RD Λ).obj ∘ (pres RD k).dom)
    ((blackMirror RD Λ).obj ∘ (pres RD k).cod) fun r =>
      blackMirrorLinear RD Λ ((pres RD k).rel r)

local notation "M" => blackMirror RD Λ

private theorem freeLift_mirror_map (P : Presentation.{w, max u v} T k)
    {a b : Obj S} (f : LinDiagram k a b) :
    (freeLift k ((M).toLayerMap.toPresented P (fun _ => 1))).map f =
      P.lin (blackMirrorLinear RD Λ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Functor.map_add, map_add, Presentation.lin_add, hf, hg]
  | single d a =>
    rw [show (Finsupp.single d a : LinDiagram k _ _) = a • LinDiagram.of d from
      by
        change Finsupp.single d a = a • Finsupp.single d (1 : k)
        rw [Finsupp.smul_single_one]]
    rw [Functor.map_smul, freeLift_map_of, LayerMap.toPresented_map]
    simp [Diagram.weight, blackMirrorLinear_of]

/-- Reflection from KL into any signed presentation satisfying the reflected
local KL relations. Whiskerings and interchange are supplied by the signature map. -/
def blackMirrorInto (P : Presentation.{w, max u v} T k)
    (hP : ∀ r : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0) :
    (pres RD k).Presented ⥤ P.Presented :=
  (M).lift (pres RD k) (Q := P) (χ := fun _ => 1)
    (by rintro ((c | e) | c | c) <;> rfl) (pres_dom_wf (RD := RD) (k := k)) fun r => by
      rw [freeLift_mirror_map RD Λ P]
      exact hP r

instance (P : Presentation.{w, max u v} T k) (hP) :
    (blackMirrorInto RD Λ P hP).Additive := by
  unfold blackMirrorInto
  infer_instance

instance (P : Presentation.{w, max u v} T k) (hP) :
    (blackMirrorInto RD Λ P hP).Linear k := by
  unfold blackMirrorInto
  infer_instance

@[simp] theorem blackMirrorInto_obj (P : Presentation.{w, max u v} T k) (hP)
    (a : Obj S) :
    (blackMirrorInto RD Λ P hP).obj ((pres RD k).obj a) = P.obj ((M).obj a) := rfl

@[simp] theorem blackMirrorInto_lin (P : Presentation.{w, max u v} T k) (hP)
    {a b : Obj S} (f : LinDiagram k a b) :
    (blackMirrorInto RD Λ P hP).map ((pres RD k).lin f) = P.lin (blackMirrorLinear RD Λ f) := by
  unfold blackMirrorInto
  rw [SigMirror.lift_lin, freeLift_mirror_map]

/-- Reflection from the black KL presentation into the signed category with
its black relations imposed. -/
abbrev blackPresentedMirror (base : Presentation.{w, max u v} T k) :
    (pres RD k).Presented ⥤ (addBlackKLRelations RD Λ base).Presented :=
  blackMirrorInto RD Λ (addBlackKLRelations RD Λ base)
    (fun r => (addBlackKLRelations RD Λ base).lin_rel_self (.inr r))

@[simp] theorem blackPresentedMirror_obj (base : Presentation.{w, max u v} T k) (a : Obj S) :
    (blackPresentedMirror RD Λ base).obj ((pres RD k).obj a) =
      (addBlackKLRelations RD Λ base).obj ((M).obj a) := rfl

@[simp] theorem blackPresentedMirror_lin (base : Presentation.{w, max u v} T k)
    {a b : Obj S} (f : LinDiagram k a b) :
    (blackPresentedMirror RD Λ base).map ((pres RD k).lin f) =
      (addBlackKLRelations RD Λ base).lin (blackMirrorLinear RD Λ f) :=
  blackMirrorInto_lin RD Λ _ _ f

section Context

variable (μ : X) (u : List (DoubleStrand I ℓ))

private theorem mirror_whisker_ok (s : List (Letter I)) :
    ((M).obj (ob RD (endWeight RD Λ μ u) s)).WhiskerOK (obj RD Λ μ u) [] := by
  rw [blackMirror_obj_ob]
  exact ⟨colours_ok RD Λ μ u, colours_endR RD Λ μ u, trivial⟩

private theorem mirror_whisker_obj (s : List (Letter I)) :
    ((M).obj (ob RD (endWeight RD Λ μ u) s)).whisker (obj RD Λ μ u) [] =
      obj RD Λ μ (u ++ blackWord s ++ []) := by
  rw [blackMirror_obj_ob]
  refine Obj.ext rfl ?_
  simp [Obj.whisker, obj, colours_append]

private theorem mirror_whisker_diagram {s t : List (Letter I)}
    (d : ob RD (endWeight RD Λ μ u) s ⟶ ob RD (endWeight RD Λ μ u) t) :
    Diagram.cast (Diagram.whisker ((M).toLayerMap.map d) (obj RD Λ μ u) [] (mirror_whisker_ok RD Λ μ u s))
      (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t) = blackDiagram RD Λ μ u [] d := by
  obtain ⟨ls, h, rfl⟩ := exists_mkD RD (endWeight RD Λ μ u) d
  apply Diagram.ext
  rw [Diagram.layers_cast, Diagram.layers_whisker, LayerMap.layers_map, layers_mkD,
    layers_blackDiagram_mkD]
  simp only [layList, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  change ((M).layer (lay RD (endWeight RD Λ μ u) x.1 x.2.1 x.2.2)).whisker _ _ = _
  rw [mirror_layer_lay]
  apply Layer.ext
  · rfl
  · simp [Layer.whisker, layer, obj, colours_append]
  · simp [Layer.whisker, layer, endWeight_append]
  · simp [Layer.whisker, layer, endWeight_append]

private theorem mirror_whisker_linear {s t : List (Letter I)}
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t)) :
    LinDiagram.cast (LinDiagram.whisker (blackMirrorLinear RD Λ f) (obj RD Λ μ u) []
      (mirror_whisker_ok RD Λ μ u s)) (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t) =
      blackLinear RD Λ k μ u [] f := by
  induction f using Finsupp.induction_linear with
  | zero => simp [LinDiagram.cast, LinDiagram.whisker]
  | add f g hf hg =>
    rw [map_add, map_add, LinDiagram.whisker_add, LinDiagram.cast_add, hf, hg]
  | single d a =>
    have he : (Finsupp.single d a : LinDiagram k _ _) = a • LinDiagram.of d := by
      change Finsupp.single d a = a • Finsupp.single d (1 : k)
      rw [Finsupp.smul_single_one]
    rw [he, map_smul, map_smul, blackMirrorLinear_of, blackLinear_of,
      LinDiagram.whisker_smul, LinDiagram.whisker_of]
    rw [LinDiagram.cast_smul, LinDiagram.cast_of, mirror_whisker_diagram]

variable (P : Presentation.{w, max u v} (signature RD Λ) k)
  (hP : ∀ r : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0)

/-- The black KL Hom map after reflecting to physical order and inserting a
fixed word on the left. -/
def blackPrefixHom {s t : List (Letter I)} :
    ((pres RD k).obj (ob RD (endWeight RD Λ μ u) s) ⟶
      (pres RD k).obj (ob RD (endWeight RD Λ μ u) t)) →ₗ[k]
    (P.obj (obj RD Λ μ (u ++ blackWord s ++ [])) ⟶
      P.obj (obj RD Λ μ (u ++ blackWord t ++ []))) :=
  (P.castLinearEquiv (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t)).toLinearMap.comp
    ((P.whiskLinearMap _ _ (obj RD Λ μ u) []).comp ((blackMirrorInto RD Λ P hP).mapLinearMap k))

@[simp] theorem blackPrefixHom_lin {s t : List (Letter I)}
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t)) :
    blackPrefixHom RD Λ μ u P hP ((pres RD k).lin f) =
      P.lin (blackLinear RD Λ k μ u [] f) := by
  change P.castHom (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t)
    (P.whisk ((blackMirrorInto RD Λ P hP).map ((pres RD k).lin f)) (obj RD Λ μ u) []) = _
  rw [blackMirrorInto_lin, Presentation.whisk_lin,
    LinDiagram.whisk_of_ok _ (mirror_whisker_ok RD Λ μ u s)]
  unfold Presentation.castHom
  rw [← P.lin_cast _ (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t),
    mirror_whisker_linear]

theorem blackPrefixHom_comp {s t z : List (Letter I)}
    (f : (pres RD k).obj (ob RD (endWeight RD Λ μ u) s) ⟶
      (pres RD k).obj (ob RD (endWeight RD Λ μ u) t))
    (g : (pres RD k).obj (ob RD (endWeight RD Λ μ u) t) ⟶
      (pres RD k).obj (ob RD (endWeight RD Λ μ u) z)) :
    blackPrefixHom RD Λ μ u P hP (f ≫ g) =
      blackPrefixHom RD Λ μ u P hP f ≫ blackPrefixHom RD Λ μ u P hP g := by
  let G := blackMirrorInto RD Λ P hP
  let e := mirror_whisker_obj RD Λ μ u
  change P.castHom (e s) (e z) (P.whisk (G.map (f ≫ g)) (obj RD Λ μ u) []) =
    P.castHom (e s) (e t) (P.whisk (G.map f) (obj RD Λ μ u) []) ≫
      P.castHom (e t) (e z) (P.whisk (G.map g) (obj RD Λ μ u) [])
  rw [Functor.map_comp, Presentation.whisk_comp, Presentation.castHom_comp]

theorem blackPrefixHom_id (s : List (Letter I)) :
    blackPrefixHom RD Λ μ u P hP (𝟙 ((pres RD k).obj (ob RD (endWeight RD Λ μ u) s))) = 𝟙 _ := by
  change _ = 𝟙 (P.obj (obj RD Λ μ (u ++ blackWord s ++ [])))
  rw [← (pres RD k).diag_id, ← Presentation.lin_of, blackPrefixHom_lin, blackLinear_of,
    Presentation.lin_of, blackDiagram_id, Presentation.diag_id]

/-- A relation in a black KL Hom remains valid after reflection and insertion
to the right of any fixed signed prefix. The base may contain additional red
and bubble relations. -/
theorem blackContext_lin_eq_of_KL_eq (base : Presentation.{w, max u v} T k)
    {s t : List (Letter I)}
    (f g : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t))
    (h : (pres RD k).lin f = (pres RD k).lin g) :
    (addBlackKLRelations RD Λ base).lin (blackLinear RD Λ k μ u [] f) =
      (addBlackKLRelations RD Λ base).lin (blackLinear RD Λ k μ u [] g) := by
  let B := addBlackKLRelations RD Λ base
  have hB : ∀ r : (pres RD k).Rel, B.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0 :=
    fun r => B.lin_rel_self (.inr r)
  simpa only [blackPrefixHom_lin] using congrArg (blackPrefixHom RD Λ μ u B hB) h

end Context

end Categorification.Stendhal.DoubleDiagram
