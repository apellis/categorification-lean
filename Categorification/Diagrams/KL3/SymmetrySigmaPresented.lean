/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigmaSymm

/-!
# The signed reflection on the presented KLR category

Khovanov–Lauda, arXiv:0803.4121v2 (KL I), end of §2.1: reflecting KLR diagrams across the
`y`-axis, with the sign `-1` on every crossing of two strands with the same label, is a
symmetry of the KLR relations when `Q_{ba}(u, v) = Q_{ab}(v, u)`. This file descends the
signed reflection `KSig.ksFree` to the presented KLR category (`KSig.ksP`): it respects the
whiskered KLR relations (`KSig.ksL_relation_of_symm`) and the interchange law. It is used in
the proof of Webster, arXiv:1309.3796v3, Lemma 4.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams Presentation

universe w u

variable {I : Type u} (k : Type w) [CommRing k]

namespace KSig

/-- The reflection of a whiskered layer is the reflected layer whiskered on the other side. -/
theorem klay_whisker (L : Layer (KLR.Diagram.sig I)) (u : Obj (KLR.Diagram.sig I))
    (v : List I) : klay (L.whisker u v) = (klay L).whisker ⟨(), v.reverse⟩ u.word.reverse :=
  KLR.Diagram.layer_ext (by simp [klay, Layer.whisker]) rfl (by simp [klay, Layer.whisker])

/-- The reflected object of a whiskering. -/
theorem kobj_whisker (a u : Obj (KLR.Diagram.sig I)) (v : List I) :
    (kobj a).whisker ⟨(), v.reverse⟩ u.word.reverse = kobj (a.whisker u v) :=
  KLR.Diagram.obj_ext (by simp [kobj, Obj.whisker, List.append_assoc])

theorem ksD_whisker {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) (u : Obj (KLR.Diagram.sig I))
    (v : List I) (hw : a.WhiskerOK u v) :
    ksD (Diagram.whisker d u v hw) =
      Diagram.cast (Diagram.whisker (ksD d) ⟨(), v.reverse⟩ u.word.reverse
        (Obj.whiskerOK_of_subsingleton _ _ _)) (kobj_whisker a u v) (kobj_whisker b u v) := by
  apply Diagram.ext
  simp only [ksD, Diagram.layers_mk, Diagram.layers_whisker, Diagram.layers_cast, List.map_map]
  exact List.map_congr_left fun L _ => klay_whisker L u v

variable [DecidableEq I]

theorem ksgn_whisker (ls : List (Layer (KLR.Diagram.sig I))) (u : Obj (KLR.Diagram.sig I))
    (v : List I) : ksgn (ls.map (·.whisker u v)) = ksgn ls := by
  simp [ksgn, List.map_map, Function.comp_def, Layer.whisker]

variable {k} {Q : I → I → MvPolynomial (Fin 2) k}

theorem ksL_zero {a b : Obj (KLR.Diagram.sig I)} : ksL Q (0 : LinDiagram k a b) = 0 :=
  Functor.map_zero _ _ _

theorem ksL_add {a b : Obj (KLR.Diagram.sig I)} (f g : LinDiagram k a b) :
    ksL Q (f + g) = ksL Q f + ksL Q g := Functor.map_add _

theorem ksL_smul {a b : Obj (KLR.Diagram.sig I)} (r : k) (f : LinDiagram k a b) :
    ksL Q (r • f) = r • ksL Q f := Functor.map_smul _ _ _

theorem ksL_single {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) (r : k) :
    ksL Q (Finsupp.single d r) =
      r • ((ksgn (Diagram.layers d) : ℤ) : k) • (KLR.Diagram.pres k Q).diag (ksD d) :=
  freeLift_map_single _ d r

/-- The signed reflection reverses whiskering. -/
theorem ksL_whisker {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (u : Obj (KLR.Diagram.sig I)) (v : List I) (hw : a.WhiskerOK u v) :
    ksL Q (LinDiagram.whisker f u v hw) =
      eqToHom (congrArg (KLR.Diagram.pres k Q).obj (kobj_whisker a u v).symm) ≫
        (KLR.Diagram.pres k Q).whisk (ksL Q f) ⟨(), v.reverse⟩ u.word.reverse ≫
          eqToHom (congrArg (KLR.Diagram.pres k Q).obj (kobj_whisker b u v)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      ksL_zero, ksL_zero, Presentation.whisk_zero, Limits.zero_comp,
      Limits.comp_zero]
  | add f g hf hg =>
    rw [LinDiagram.whisker_add, ksL_add, hf, hg, ksL_add,
      Presentation.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
  | single d r =>
    rw [LinDiagram.whisker_single, ksL_single, ksL_single, Diagram.layers_whisker,
      ksgn_whisker, ksD_whisker, Presentation.diag_cast, Presentation.whisk_smul,
      Presentation.whisk_smul, Presentation.whisk_diag _ _ _ _
      (Obj.whiskerOK_of_subsingleton _ _ _)]
    simp only [Linear.smul_comp, Linear.comp_smul]

theorem ksL_whisker_eq_zero {a b : Obj (KLR.Diagram.sig I)} {f : LinDiagram k a b}
    (hf : ksL Q f = 0) (u : Obj (KLR.Diagram.sig I)) (v : List I) (hw : a.WhiskerOK u v) :
    ksL Q (LinDiagram.whisker f u v hw) = 0 := by
  rw [ksL_whisker, hf, Presentation.whisk_zero, Limits.zero_comp, Limits.comp_zero]

/-- The reflection of the interchange law is the interchange law with the generators
exchanged. -/
theorem ksL_interchange (x : InterchangeData (KLR.Diagram.sig I)) (hx : x.Valid) :
    ksL Q (InterchangeData.rel k hx) = 0 := by
  obtain ⟨start, g, mid, h⟩ := x
  let x' : InterchangeData (KLR.Diagram.sig I) := ⟨(), kgen h, mid.reverse, kgen g⟩
  have hx' : x'.Valid := InterchangeData.valid_of_subsingleton _
  have hw : x'.dom.WhiskerOK (Obj.nil x'.start) [] := Obj.whiskerOK_of_subsingleton _ _ _
  have ha : x'.dom.whisker (Obj.nil x'.start) [] =
      kobj (InterchangeData.dom ⟨start, g, mid, h⟩) :=
    KLR.Diagram.obj_ext (by
      simp [x', InterchangeData.dom, Obj.whisker, Obj.nil, kobj, kgen_dom, List.append_assoc])
  have hb : x'.cod.whisker (Obj.nil x'.start) [] =
      kobj (InterchangeData.cod ⟨start, g, mid, h⟩) :=
    KLR.Diagram.obj_ext (by
      simp [x', InterchangeData.cod, Obj.whisker, Obj.nil, kobj, kgen_cod, List.append_assoc])
  have key := (KLR.Diagram.pres k Q).diag_interchange x' hx' (Obj.nil x'.start) [] hw ha hb
  have hsg : ∀ y : InterchangeData (KLR.Diagram.sig I), ((y.sign : ℤ) : k) = 1 := by
    intro y; simp [InterchangeData.sign]
  rw [hsg, one_smul] at key
  have hs : ksgn (Diagram.layers (InterchangeData.hgDiagram hx)) =
      ksgn (Diagram.layers (InterchangeData.ghDiagram hx)) := by
    simp only [ksgn, InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, InterchangeData.gh₁,
      InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂]
    ring
  have d₁ : (KLR.Diagram.pres k Q).diag (ksD (InterchangeData.ghDiagram hx)) =
      (KLR.Diagram.pres k Q).diag (Diagram.cast (Diagram.whisker (InterchangeData.hgDiagram hx')
        (Obj.nil x'.start) [] hw) ha hb) := by
    apply (KLR.Diagram.pres k Q).diag_eq_of_layers_eq
    simp only [ksD, InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk,
      Diagram.layers_cast, Diagram.layers_whisker, List.map_cons, List.map_nil]
    refine congrArg₂ _ (KLR.Diagram.layer_ext ?_ rfl ?_)
      (congrArg₂ _ (KLR.Diagram.layer_ext ?_ rfl ?_) rfl) <;>
      simp [klay, x', Layer.whisker, Obj.nil, InterchangeData.gh₁, InterchangeData.gh₂,
        InterchangeData.hg₁, InterchangeData.hg₂, kgen_dom, kgen_cod]
  have d₂ : (KLR.Diagram.pres k Q).diag (ksD (InterchangeData.hgDiagram hx)) =
      (KLR.Diagram.pres k Q).diag (Diagram.cast (Diagram.whisker (InterchangeData.ghDiagram hx')
        (Obj.nil x'.start) [] hw) ha hb) := by
    apply (KLR.Diagram.pres k Q).diag_eq_of_layers_eq
    simp only [ksD, InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk,
      Diagram.layers_cast, Diagram.layers_whisker, List.map_cons, List.map_nil]
    refine congrArg₂ _ (KLR.Diagram.layer_ext ?_ rfl ?_)
      (congrArg₂ _ (KLR.Diagram.layer_ext ?_ rfl ?_) rfl) <;>
      simp [klay, x', Layer.whisker, Obj.nil, InterchangeData.gh₁, InterchangeData.gh₂,
        InterchangeData.hg₁, InterchangeData.hg₂, kgen_dom, kgen_cod]
  rw [InterchangeData.rel, ksL_sub, ksL_smul, ksL_of, ksL_of, hsg, one_smul, hs, d₁, d₂,
    key, sub_self]

variable (Q) in
/-- The signed reflection respects the KLR relations, when `Q_{ba}(u, v) = Q_{ab}(v, u)`, and
the interchange law. -/
theorem ksFree_respects (hQ : KLR.KLRSymm Q) : (KLR.Diagram.pres k Q).Respects (ksFree Q) where
  rel r u v hw := ksL_whisker_eq_zero (ksL_relation_of_symm k hQ r) u v hw
  interchange x hx u v hw := ksL_whisker_eq_zero (ksL_interchange x hx) u v hw

variable (Q) in
/-- **The signed reflection of the presented KLR category** (KL I, end of §2.1), for KLR
polynomials with `Q_{ba}(u, v) = Q_{ab}(v, u)`. -/
def ksP (hQ : KLR.KLRSymm Q) :
    (KLR.Diagram.pres k Q).Presented ⥤ (KLR.Diagram.pres k Q).Presented :=
  (KLR.Diagram.pres k Q).lift (ksFree_respects Q hQ)

instance (hQ : KLR.KLRSymm Q) : (ksP Q hQ).Additive := by unfold ksP; infer_instance

instance (hQ : KLR.KLRSymm Q) : (ksP Q hQ).Linear k := by unfold ksP; infer_instance

@[simp] theorem ksP_obj (hQ : KLR.KLRSymm Q) (a : Obj (KLR.Diagram.sig I)) :
    (ksP Q hQ).obj ((KLR.Diagram.pres k Q).obj a) = (KLR.Diagram.pres k Q).obj (kobj a) := rfl

theorem ksP_lin (hQ : KLR.KLRSymm Q) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    (ksP Q hQ).map ((KLR.Diagram.pres k Q).lin f) = ksL Q f := rfl

theorem ksP_diag (hQ : KLR.KLRSymm Q) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (ksP Q hQ).map ((KLR.Diagram.pres k Q).diag d) =
      ((ksgn (Diagram.layers d) : ℤ) : k) • (KLR.Diagram.pres k Q).diag (ksD d) :=
  (KLR.Diagram.pres k Q).lift_diag _ d

end KSig

end Categorification.KL3.Diagram
