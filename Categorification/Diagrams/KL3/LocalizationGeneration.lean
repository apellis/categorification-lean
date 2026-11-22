/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationDots
import Categorification.Diagrams.KL3.SpanningBasic

/-!
# Generation of `U′` by the layers of `U` and the inverse dots

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. Every 2-morphism of `U′` out of `1_μ` is a linear combination of composites of
images of layers of `U` and of inverse downward dots.

## Main results

* `loc_layer_cases`: a layer of `U′` is the image of a layer of `U` or an inverse dot.
* `diag_invDot_eq_inv`: the inverse dot between strands is the inverse of the image of the dot.
* `loc_mem_of_layers`: a family of submodules of the hom spaces out of `1_μ`, containing the
  identity and closed under composition with images of layers of `U` and with inverse dots,
  contains every 2-morphism of `U′` out of `1_μ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

theorem lsig_ok (r : X) (w : List (Col I X)) : (lsig RD).ok r w ↔ (psig RD).ok r w := by
  induction w generalizing r with
  | nil => exact Iff.rfl
  | cons c w ih => exact and_congr Iff.rfl (ih _)

theorem lsig_endR (r : X) (w : List (Col I X)) : (lsig RD).endR r w = (psig RD).endR r w := by
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => exact ih _

/-- A valid layer of `U′` whose generator is a generator `g` of `U` comes from a valid layer of
`U`. -/
theorem valid_of_lsig_inl {st : X} {lf rt : List (Col I X)} {g : (psig RD).Gen}
    (hv : (⟨st, lf, .inl g, rt⟩ : Layer (lsig RD)).Valid) :
    (⟨st, lf, g, rt⟩ : Layer (psig RD)).Valid :=
  ⟨(lsig_ok RD _ _).1 hv.left_ok, (lsig_endR RD _ _).symm.trans hv.left_end,
    (lsig_ok RD _ _).1 hv.dom_ok, (lsig_endR RD _ _).symm.trans hv.dom_end,
    (lsig_ok RD _ _).1 hv.cod_ok, (lsig_endR RD _ _).symm.trans hv.cod_end,
    (lsig_ok RD _ _).1 hv.right_ok⟩

/-- A valid layer of `U′` whose generator is an inverse dot gives a valid layer of `U` with the
dot in its place. -/
theorem valid_of_lsig_inr {st : X} {lf rt : List (Col I X)} {i : I} {x : X}
    (hv : (⟨st, lf, .inr (i, x), rt⟩ : Layer (lsig RD)).Valid) :
    (⟨st, lf, .gen (.dot ⟨dn i, x⟩), rt⟩ : Layer (psig RD)).Valid :=
  ⟨(lsig_ok RD _ _).1 hv.left_ok, (lsig_endR RD _ _).symm.trans hv.left_end,
    (lsig_ok RD _ _).1 hv.dom_ok, (lsig_endR RD _ _).symm.trans hv.dom_end,
    (lsig_ok RD _ _).1 hv.cod_ok, (lsig_endR RD _ _).symm.trans hv.cod_end,
    (lsig_ok RD _ _).1 hv.right_ok⟩

/-- **The layers of `U′`**: a valid layer of `U′` with bottom boundary `E_s 1_μ` is the image of
a valid layer of `U` with the same bottom boundary, or an inverse dot. -/
theorem loc_layer_cases (μ : X) (s : List (Letter I)) (L : Layer (lsig RD)) (hv : L.Valid)
    (hd : L.dom = (incl RD).obj (ob RD μ s)) :
    (∃ M : Layer (psig RD), M.Valid ∧ M.dom = ob RD μ s ∧ L = (incl RD).layer M) ∨
      (∃ u i w, s = u ++ [dn i] ++ w ∧ L = invDotLayer RD μ u i w) := by
  obtain ⟨st, lf, g, rt⟩ := L
  have h1 : st = (ob RD μ s).start := congrArg Obj.start hd
  have h2 : lf ++ (lsig RD).dom g ++ rt = (ob RD μ s).word := congrArg Obj.word hd
  rcases g with g | ⟨i, x⟩
  · left
    refine ⟨⟨st, lf, g, rt⟩, valid_of_lsig_inl RD hv, ?_, rfl⟩
    cases h1
    exact congrArg (Obj.mk _) h2
  · right
    set M : Layer (psig RD) := ⟨st, lf, .gen (.dot ⟨dn i, x⟩), rt⟩ with hM
    have hMv : M.Valid := valid_of_lsig_inr RD hv
    have hMd : M.dom = ob RD μ s := by
      cases h1
      exact congrArg (Obj.mk _) h2
    obtain ⟨hs, hL⟩ := layer_eq_lay RD μ s M hMv hMd
    refine ⟨lf.map Col.l, i, rt.map Col.l, hs, ?_⟩
    have e := congrArg (fun N : Layer (psig RD) => ((⟨N.start, N.left, .inr (i, x), N.right⟩ :
      Layer (lsig RD)), N.gen)) hL
    simp only [hM, lay] at e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    rw [e1]
    have hx : x = wt RD μ (rt.map Col.l) := by
      have := congrArg (fun g : (psig RD).Gen => match g with
        | .gen (.dot c) => c.r | _ => x) e2
      simpa [shapeOf, Shape.gen] using this
    rw [hx]
    rfl

/-- The inverse dot between the strands `u` and `w` is the whiskering of the inverse dot on a
single strand. -/
theorem invDotLayer_eq_whisker (μ : X) (u : List (Letter I)) (i : I) (w : List (Letter I)) :
    invDotLayer RD μ u i w = (invDotLayer RD (wt RD μ w) [] i []).whisker
      ((incl RD).obj (ob RD (wt RD (wt RD μ w) [dn i]) u)) ((incl RD).word (wd RD μ w)) := by
  have h := lay_whisker RD μ u w [] (.dot (dn i)) [] [dn i] rfl
  have e := congrArg (incl RD).layer h
  rw [(incl RD).layer_whisker, List.append_nil, List.nil_append] at e
  exact Layer.ext (congrArg Layer.start e).symm (congrArg Layer.left e).symm rfl
    (congrArg Layer.right e).symm

set_option backward.isDefEq.respectTransparency false in
/-- In `U′` the dot followed by the inverse dot, both between the strands `u` and `w`, is the
identity. -/
theorem toLoc_dg_dot_comp_invDot (μ : X) (u : List (Letter I)) (i : I) (w : List (Letter I)) :
    (toLoc RD k).map (dg RD k μ (u ++ [dn i] ++ w) (u ++ [dn i] ++ w) [(u, .dot (dn i), w)]) ≫
      (presLoc RD k).diag (invDot RD μ u i w) = 𝟙 _ := by
  have hw := (incl RD).whiskerOK (whiskerOK_ob RD μ u w [dn i])
  have he : (incl RD).obj (ob RD μ (u ++ [dn i] ++ w)) =
      ((incl RD).obj (ob RD (wt RD μ w) [dn i])).whisker
        ((incl RD).obj (ob RD (wt RD (wt RD μ w) [dn i]) u)) ((incl RD).word (wd RD μ w)) :=
    (congrArg (incl RD).obj (ob_whisker RD μ u w [dn i] [dn i] rfl).symm).trans
      ((incl RD).obj_whisker _ _ _)
  rw [dg_of (show SChain (u ++ [dn i] ++ w) [(u, .dot (dn i), w)] (u ++ [dn i] ++ w) from
    ⟨rfl, rfl⟩), toLoc_diag, ← (presLoc RD k).diag_comp,
    (presLoc RD k).diag_eq_of_layers_eq' _
      (Diagram.whisker (inclD RD (downDot RD i (wt RD μ w)) ≫ invDotF RD i (wt RD μ w)) _ _ hw)
      he he ?_, ← (presLoc RD k).whisk_diag _ _ _ hw, (presLoc RD k).diag_comp,
    downDot_comp_invDot, (presLoc RD k).whisk_id _ _ _ hw]
  · simp
  · simp only [Diagram.layers_comp, Diagram.layers_whisker]
    rw [List.map_append]
    congr 1
    · show [(incl RD).layer (lay RD μ u (.dot (dn i)) w)] =
        [((incl RD).layer (lay RD (wt RD μ w) [] (.dot (dn i)) [])).whisker _ _]
      rw [← (incl RD).layer_whisker, lay_whisker RD μ u w [] _ [] [dn i] rfl, List.append_nil,
        List.nil_append]
    · show [invDotLayer RD μ u i w] = [_]
      rw [invDotLayer_eq_whisker]

/-- **The inverse dot between strands is the inverse of the dot** in `U′`. -/
theorem diag_invDot_eq_inv (μ : X) (u : List (Letter I)) (i : I) (w : List (Letter I)) :
    (presLoc RD k).diag (invDot RD μ u i w) = CategoryTheory.inv ((toLoc RD k).map
      (dg RD k μ (u ++ [dn i] ++ w) (u ++ [dn i] ++ w) [(u, .dot (dn i), w)])) :=
  IsIso.eq_inv_of_hom_inv_id (toLoc_dg_dot_comp_invDot RD k μ u i w)

/-! ## Generation -/

theorem incl_ob_injective (μ : X) {s s' : List (Letter I)}
    (h : (incl RD).obj (ob RD μ s) = (incl RD).obj (ob RD μ s')) : s = s' := by
  have : (wd RD μ s).map Col.l = (wd RD μ s').map Col.l :=
    congrArg (fun o : Obj (lsig RD) => o.word.map Col.l) h
  rwa [map_l_wd, map_l_wd] at this

/-- The images of the layers of `U` in normal form, up to retyping. -/
theorem diag_ofLayer_incl_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (hv : ((incl RD).layer (lay RD μ u g v)).Valid) :
    (presLoc RD k).diag (Diagram.ofLayer _ hv) =
      eqToHom (congrArg (presLoc RD k).obj (((incl RD).toLayerMap.dom_eq (lay_valid RD μ u g v)).trans
        (congrArg (incl RD).obj (lay_dom RD μ u g v)))) ≫
      (toLoc RD k).map (dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]) ≫
      eqToHom (congrArg (presLoc RD k).obj (((incl RD).toLayerMap.cod_eq (lay_valid RD μ u g v)).trans
        (congrArg (incl RD).obj (lay_cod RD μ u g v))).symm) := by
  rw [dg_of (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩),
    toLoc_diag]
  exact (presLoc RD k).diag_eq_of_layers_eq' _ _
    (((incl RD).toLayerMap.dom_eq (lay_valid RD μ u g v)).trans
      (congrArg (incl RD).obj (lay_dom RD μ u g v)))
    (((incl RD).toLayerMap.cod_eq (lay_valid RD μ u g v)).trans
      (congrArg (incl RD).obj (lay_cod RD μ u g v))) rfl

/-- The inverse-dot layers, up to retyping. -/
theorem diag_ofLayer_invDotLayer (μ : X) (u : List (Letter I)) (i : I) (w : List (Letter I))
    (hv : (invDotLayer RD μ u i w).Valid) :
    (presLoc RD k).diag (Diagram.ofLayer _ hv) =
      eqToHom (congrArg (presLoc RD k).obj (invDotLayer_dom RD μ u i w)) ≫
      (presLoc RD k).diag (invDot RD μ u i w) ≫
      eqToHom (congrArg (presLoc RD k).obj (invDotLayer_cod RD μ u i w).symm) :=
  (presLoc RD k).diag_eq_of_layers_eq' _ _ (invDotLayer_dom RD μ u i w)
    (invDotLayer_cod RD μ u i w) rfl

variable {RD k} in
/-- The family `T` extended to all objects of `U′`. -/
def locExt (μ : X) {a : Obj (lsig RD)}
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj a ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s)))) (b : Obj (lsig RD)) :
    Submodule k ((presLoc RD k).obj a ⟶ (presLoc RD k).obj b) where
  carrier := {f | ∀ s (e : b = (incl RD).obj (ob RD μ s)),
    f ≫ eqToHom (congrArg (presLoc RD k).obj e) ∈ T s}
  zero_mem' s e := by simp only [Limits.zero_comp]; exact (T s).zero_mem
  add_mem' hf hg s e := by rw [Preadditive.add_comp]; exact (T s).add_mem (hf s e) (hg s e)
  smul_mem' r f hf s e := by rw [Linear.smul_comp]; exact (T s).smul_mem r (hf s e)

theorem mem_locExt_ob (μ : X) {a : Obj (lsig RD)}
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj a ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s)))) (s : List (Letter I)) (f) :
    f ∈ locExt μ T ((incl RD).obj (ob RD μ s)) ↔ f ∈ T s := by
  refine ⟨fun h => by simpa using h s rfl, fun h s' e => ?_⟩
  obtain rfl := incl_ob_injective RD μ e
  simpa using h

variable {RD k} in
/-- The morphisms preserving the extended family under postcomposition. -/
def locRight (μ : X) {a : Obj (lsig RD)}
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj a ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s)))) (b c : Obj (lsig RD)) :
    Submodule k ((presLoc RD k).obj b ⟶ (presLoc RD k).obj c) where
  carrier := {g | ∀ f ∈ locExt μ T b, f ≫ g ∈ locExt μ T c}
  zero_mem' f _ := by rw [Limits.comp_zero]; exact Submodule.zero_mem _
  add_mem' hg hh f hf := by rw [Preadditive.comp_add]; exact Submodule.add_mem _ (hg f hf) (hh f hf)
  smul_mem' r g hg f hf := by rw [Linear.comp_smul]; exact Submodule.smul_mem _ r (hg f hf)

theorem locRight_eqToHom (μ : X) {a : Obj (lsig RD)}
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj a ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s)))) {b b' c c' : Obj (lsig RD)} (eb : b = b')
    (ec : c' = c) (g : (presLoc RD k).obj b' ⟶ (presLoc RD k).obj c') (hg : g ∈ locRight μ T b' c') :
    eqToHom (congrArg (presLoc RD k).obj eb) ≫ g ≫ eqToHom (congrArg (presLoc RD k).obj ec) ∈
      locRight μ T b c := by
  subst eb ec
  simpa using hg

theorem locRight_ob (μ : X) {a : Obj (lsig RD)}
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj a ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s)))) (s t : List (Letter I))
    (g : (presLoc RD k).obj ((incl RD).obj (ob RD μ s)) ⟶ (presLoc RD k).obj ((incl RD).obj (ob RD μ t)))
    (hg : ∀ f ∈ T s, f ≫ g ∈ T t) :
    g ∈ locRight μ T ((incl RD).obj (ob RD μ s)) ((incl RD).obj (ob RD μ t)) := fun f hf =>
  (mem_locExt_ob RD k μ T t _).2 (hg f ((mem_locExt_ob RD k μ T s f).1 hf))

/-- **Generation of `U′`** (Webster arXiv:1309.3796v2, proof of Lemma 3.29). A family of
submodules of the 2-morphisms of `U′` out of `1_μ`, containing the identity and closed under
postcomposition with the images of the layers of `U` and with the inverse dots, contains every
2-morphism of `U′` out of `1_μ`. -/
theorem loc_mem_of_layers (μ : X)
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s))))
    (hid : 𝟙 _ ∈ T [])
    (hlay : ∀ (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) (f), f ∈ T (u ++ g.dom ++ v) →
      f ≫ (toLoc RD k).map (dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]) ∈
        T (u ++ g.cod ++ v))
    (hinv : ∀ (u : List (Letter I)) (i : I) (w : List (Letter I)) (f), f ∈ T (u ++ [dn i] ++ w) →
      f ≫ (presLoc RD k).diag (invDot RD μ u i w) ∈ T (u ++ [dn i] ++ w))
    (s : List (Letter I)) (f : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s))) : f ∈ T s := by
  let C : Set (Obj (lsig RD)) := {b | ∃ s, b = (incl RD).obj (ob RD μ s)}
  have hC : ∀ (L : Layer (lsig RD)), L.Valid → L.dom ∈ C → L.cod ∈ C := by
    rintro L hv ⟨s, hd⟩
    rcases loc_layer_cases RD μ s L hv hd with ⟨M, hMv, hMd, rfl⟩ | ⟨u, i, w, -, rfl⟩
    · obtain ⟨-, hL⟩ := layer_eq_lay RD μ s M hMv hMd
      generalize M.left.map Col.l = u at hL
      generalize shapeOf RD M.gen = g at hL
      generalize M.right.map Col.l = v at hL
      subst hL
      exact ⟨_, ((incl RD).toLayerMap.cod_eq hMv).trans
        (congrArg (incl RD).obj (lay_cod RD μ u g v))⟩
    · exact ⟨_, invDotLayer_cod RD μ u i w⟩
  have hlayer : ∀ (L : Layer (lsig RD)) (hv : L.Valid), L.dom ∈ C →
      (presLoc RD k).diag (Diagram.ofLayer L hv) ∈ locRight μ T L.dom L.cod := by
    rintro L hv ⟨s, hd⟩
    rcases loc_layer_cases RD μ s L hv hd with ⟨M, hMv, hMd, rfl⟩ | ⟨u, i, w, -, rfl⟩
    · obtain ⟨-, hL⟩ := layer_eq_lay RD μ s M hMv hMd
      generalize M.left.map Col.l = u at hL
      generalize shapeOf RD M.gen = g at hL
      generalize M.right.map Col.l = v at hL
      subst hL
      rw [diag_ofLayer_incl_lay]
      exact locRight_eqToHom RD k μ T (((incl RD).toLayerMap.dom_eq (lay_valid RD μ u g v)).trans
        (congrArg (incl RD).obj (lay_dom RD μ u g v)))
        (((incl RD).toLayerMap.cod_eq (lay_valid RD μ u g v)).trans
          (congrArg (incl RD).obj (lay_cod RD μ u g v))).symm _
        (locRight_ob RD k μ T _ _ _ (hlay u g v))
    · rw [diag_ofLayer_invDotLayer]
      exact locRight_eqToHom RD k μ T (invDotLayer_dom RD μ u i w)
        (invDotLayer_cod RD μ u i w).symm _ (locRight_ob RD k μ T _ _ _ (hinv u i w))
  have h := (presLoc RD k).mem_of_layers C hC (locRight μ T)
    (fun _ _ f hf => by simpa using hf)
    (fun _ _ _ f g hf hg x hx => by rw [← Category.assoc]; exact hg _ (hf x hx))
    hlayer ⟨[], rfl⟩ ⟨s, rfl⟩ f (𝟙 _) ((mem_locExt_ob RD k μ T [] _).2 hid)
  rw [Category.id_comp] at h
  exact (mem_locExt_ob RD k μ T s f).1 h

end Categorification.KL3.Diagram
