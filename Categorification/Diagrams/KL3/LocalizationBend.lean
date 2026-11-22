/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationCapClosure
import Categorification.Diagrams.KL3.LocalizationPlace
import Categorification.Diagrams.KL3.SpanningOneSided

/-!
# Bending in `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. The bending map of `U` (nested caps, `bendG`) has an analogue `bendLoc` in the
localization `U′`, compatible with the localization functor. Every 2-morphism
`E_s 1_μ ⟶ E_t 1_μ` of `U′` is the bending of a 2-morphism `1_μ ⟶ E_{s* t} 1_μ` of `U′`.

## Main results

* `loc_mem_of_layers_from`: generation of `U′` by layers and inverse dots, from any source.
* `bendLoc`: bending in `U′`; `bendLoc_toLoc`: it extends the bending of `U`.
* `bendLoc_comp_layer`, `bendLoc_comp_inv`: compatibility with layers and inverse dots.
* `exists_bendLoc_eq`: every 2-morphism of `U′` is a bending.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [Field k]

/-- **Generation of `U′` from any source** (Webster arXiv:1309.3796v2, proof of Lemma 3.29): a
family of submodules of the 2-morphisms of `U′` out of `E_{s₀} 1_μ`, containing the identity and
closed under postcomposition with the images of the layers of `U` and with the inverse dots,
contains every 2-morphism of `U′` out of `E_{s₀} 1_μ`. -/
theorem loc_mem_of_layers_from (μ : X) (s₀ : List (Letter I))
    (T : ∀ s : List (Letter I), Submodule k ((presLoc RD k).obj ((incl RD).obj (ob RD μ s₀)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s))))
    (hid : 𝟙 _ ∈ T s₀)
    (hlay : ∀ (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) (f), f ∈ T (u ++ g.dom ++ v) →
      f ≫ (toLoc RD k).map (dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]) ∈
        T (u ++ g.cod ++ v))
    (hinv : ∀ (u : List (Letter I)) (i : I) (w : List (Letter I)) (f), f ∈ T (u ++ [dn i] ++ w) →
      f ≫ (presLoc RD k).diag (invDot RD μ u i w) ∈ T (u ++ [dn i] ++ w))
    (s : List (Letter I)) (f : (presLoc RD k).obj ((incl RD).obj (ob RD μ s₀)) ⟶
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
    hlayer ⟨s₀, rfl⟩ ⟨s, rfl⟩ f (𝟙 _) ((mem_locExt_ob RD k μ T s₀ _).2 hid)
  rw [Category.id_comp] at h
  exact (mem_locExt_ob RD k μ T s f).1 h

/-! ## Bending in `U′` -/

theorem plcLoc_add (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f g : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) t))) :
    plcLoc RD k μ u v hst (f + g) = plcLoc RD k μ u v hst f + plcLoc RD k μ u v hst g := by
  simp only [plcLoc, Presentation.whisk_add, Preadditive.add_comp, Preadditive.comp_add]

theorem plcLoc_smul (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) (r : k)
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) t))) :
    plcLoc RD k μ u v hst (r • f) = r • plcLoc RD k μ u v hst f := by
  simp only [plcLoc, Presentation.whisk_smul, Linear.smul_comp, Linear.comp_smul]

open Classical in
/-- **Bending in `U′`** (Webster arXiv:1309.3796v2, proof of Lemma 3.29): the analogue of `bendG`
for the localization. A 2-morphism `1_μ ⟶ E_{s* t} 1_μ` of `U′` is placed to the right of the
strands `s`, and the strands `s s*` are closed by nested caps. It is `0` if `s* t` does not
preserve the weight. -/
def bendLoc (μ : X) (s t : List (Letter I)) :
    ((presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (rd s ++ t)))) →ₗ[k]
      ((presLoc RD k).obj ((incl RD).obj (ob RD μ s)) ⟶
        (presLoc RD k).obj ((incl RD).obj (ob RD μ t))) :=
  if h : wt RD (wt RD μ []) (rd s ++ t) = wt RD (wt RD μ []) [] then
    { toFun := fun F => (toLoc RD k).map (dg RD k μ s (s ++ [] ++ []) []) ≫
        plcLoc RD k μ s [] h F ≫
        (toLoc RD k).map (dg RD k μ (s ++ (rd s ++ t) ++ []) t ((capA (rd s)).map (whL [] t)))
      map_add' := fun F G => by
        rw [plcLoc_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r F => by
        rw [plcLoc_smul, Linear.smul_comp, Linear.comp_smul]; rfl }
  else 0

theorem bendG_apply (μ : X) (s t : List (Letter I))
    (g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (rd s ++ t))) :
    bendG RD k μ s t g = dg RD k μ s (s ++ [] ++ []) [] ≫ plcL RD k μ s [] [] (rd s ++ t) g ≫
      dg RD k μ (s ++ (rd s ++ t) ++ []) t ((capA (rd s)).map (whL [] t)) :=
  rfl

theorem bendLoc_apply (μ : X) (s t : List (Letter I))
    (h : wt RD (wt RD μ []) (rd s ++ t) = wt RD (wt RD μ []) [])
    (F : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (rd s ++ t)))) :
    bendLoc RD k μ s t F = (toLoc RD k).map (dg RD k μ s (s ++ [] ++ []) []) ≫
        plcLoc RD k μ s [] h F ≫
        (toLoc RD k).map (dg RD k μ (s ++ (rd s ++ t) ++ []) t ((capA (rd s)).map (whL [] t))) := by
  rw [bendLoc, dite_eq_left h]
  rfl

theorem bendLoc_of_not (μ : X) (s t : List (Letter I))
    (h : ¬ wt RD (wt RD μ []) (rd s ++ t) = wt RD (wt RD μ []) [])
    (F : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (rd s ++ t)))) :
    bendLoc RD k μ s t F = 0 := by
  rw [bendLoc, dite_eq_right h]
  rfl

/-- **Bending in `U′` extends bending in `U`.** -/
theorem bendLoc_toLoc (μ : X) (s t : List (Letter I))
    (g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (rd s ++ t))) :
    bendLoc RD k μ s t ((toLoc RD k).map g) = (toLoc RD k).map (bendG RD k μ s t g) := by
  rw [bendG_apply]
  by_cases h : wt RD (wt RD μ []) (rd s ++ t) = wt RD (wt RD μ []) []
  · rw [bendLoc_apply RD k μ s t h, Functor.map_comp, Functor.map_comp,
      toLoc_plcL RD k μ s [] [] (rd s ++ t) h]
  · rw [bendLoc_of_not RD k μ s t h, plcL, dite_eq_right h, LinearMap.zero_apply,
      Limits.zero_comp, Limits.comp_zero, Functor.map_zero]

/-- In `U`, a layer to the right of the bending caps moves below them (interchange). -/
theorem dg_layer_comp_cap (μ : X) (s u v : List (Letter I)) (g : Shape I) :
    dg RD k μ (s ++ (rd s ++ (u ++ g.dom ++ v)) ++ []) (s ++ (rd s ++ (u ++ g.cod ++ v)) ++ [])
        ([(rd s ++ u, g, v)].map (whL s [])) ≫
      dg RD k μ (s ++ (rd s ++ (u ++ g.cod ++ v)) ++ []) (u ++ g.cod ++ v)
        ((capA (rd s)).map (whL [] (u ++ g.cod ++ v))) =
    dg RD k μ (s ++ (rd s ++ (u ++ g.dom ++ v)) ++ []) (u ++ g.dom ++ v)
        ((capA (rd s)).map (whL [] (u ++ g.dom ++ v))) ≫
      dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)] := by
  have hL : SChain (s ++ (rd s ++ (u ++ g.dom ++ v)) ++ [])
      ([(rd s ++ u, g, v)].map (whL s [])) (s ++ (rd s ++ (u ++ g.cod ++ v)) ++ []) := by
    simp [whL]
  have hC : ∀ t : List (Letter I),
      SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := fun t => by
    simpa using (sChain_capA (rd s)).whisk [] t
  have hA : SChain (s ++ rd s) (capA (rd s)) [] := by simpa using sChain_capA (rd s)
  have hB : SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) := ⟨rfl, rfl⟩
  rw [dg_comp hL (hC _), dg_comp (hC _) hB]
  have e := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s ++ (rd s ++ (u ++ g.dom ++ v)) ++ [])
    (T := u ++ g.cod ++ v) [] [] hA hB
  have e1 : [(rd s ++ u, g, v)].map (whL s []) ++ (capA (rd s)).map (whL [] (u ++ g.cod ++ v)) =
      [] ++ [(u, g, v)].map (whL (s ++ rd s) []) ++
        (capA (rd s)).map (whL [] (u ++ g.cod ++ v)) ++ [] := by
    simp [whL]
  have e2 : (capA (rd s)).map (whL [] (u ++ g.dom ++ v)) ++ [(u, g, v)] =
      [] ++ (capA (rd s)).map (whL [] (u ++ g.dom ++ v)) ++ [(u, g, v)].map (whL [] []) ++ [] := by
    simp
  rw [e1, e2, e]

/-- **Bending in `U′` commutes with layers** to the right of the bent strands. -/
theorem bendLoc_comp_layer (μ : X) (s u v : List (Letter I)) (g : Shape I)
    (F : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (rd s ++ (u ++ g.dom ++ v))))) :
    bendLoc RD k μ s (u ++ g.cod ++ v) (F ≫ (toLoc RD k).map
        (dg RD k μ (rd s ++ (u ++ g.dom ++ v)) (rd s ++ (u ++ g.cod ++ v)) [(rd s ++ u, g, v)])) =
      bendLoc RD k μ s (u ++ g.dom ++ v) F ≫
        (toLoc RD k).map (dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]) := by
  have hch : SChain (rd s ++ (u ++ g.dom ++ v)) [(rd s ++ u, g, v)] (rd s ++ (u ++ g.cod ++ v)) :=
    ⟨by simp, by simp⟩
  have hw := hch.wt_eq RD (wt RD μ [])
  by_cases h : wt RD (wt RD μ []) (rd s ++ (u ++ g.dom ++ v)) = wt RD (wt RD μ []) []
  · have h' := hw.trans h
    rw [bendLoc_apply RD k μ s _ h', bendLoc_apply RD k μ s _ h,
      ← plcLoc_comp RD k μ s [] h hw, ← toLoc_plcL RD k μ s [] _ _ hw, plcL_dg_nil]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [dg_layer_comp_cap]
  · have h' : ¬ wt RD (wt RD μ []) (rd s ++ (u ++ g.cod ++ v)) = wt RD (wt RD μ []) [] :=
      fun h' => h (hw.symm.trans h')
    rw [bendLoc_of_not RD k μ s _ h', bendLoc_of_not RD k μ s _ h, Limits.zero_comp]

theorem isIso_toLoc_dg_dot_of_eq (μ : X) {S u w : List (Letter I)} (l : Letter I)
    (h : S = u ++ [l] ++ w) : IsIso ((toLoc RD k).map (dg RD k μ S S [(u, .dot l, w)])) := by
  subst h
  infer_instance

/-- **Bending in `U′` commutes with inverse dots** to the right of the bent strands. -/
theorem bendLoc_comp_inv (μ : X) (s u w : List (Letter I)) (i : I)
    (F : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (rd s ++ (u ++ [dn i] ++ w))))) :
    ∃ F', bendLoc RD k μ s (u ++ [dn i] ++ w) F' =
      bendLoc RD k μ s (u ++ [dn i] ++ w) F ≫ CategoryTheory.inv ((toLoc RD k).map
        (dg RD k μ (u ++ [dn i] ++ w) (u ++ [dn i] ++ w) [(u, .dot (dn i), w)])) := by
  have hiso := isIso_toLoc_dg_dot_of_eq RD k μ (S := rd s ++ (u ++ [dn i] ++ w))
    (u := rd s ++ u) (w := w) (dn i) (by simp)
  refine ⟨F ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ (rd s ++ (u ++ [dn i] ++ w))
    (rd s ++ (u ++ [dn i] ++ w)) [(rd s ++ u, .dot (dn i), w)])), ?_⟩
  rw [IsIso.eq_comp_inv]
  have e := bendLoc_comp_layer RD k μ s u w (.dot (dn i)) (F ≫ CategoryTheory.inv
    ((toLoc RD k).map (dg RD k μ (rd s ++ (u ++ [dn i] ++ w))
      (rd s ++ (u ++ [dn i] ++ w)) [(rd s ++ u, .dot (dn i), w)])))
  simp only [Shape.dom, Shape.cod] at e
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at e
  exact e.symm

/-- **Every 2-morphism of `U′` is a bending** (Webster arXiv:1309.3796v2, proof of
Lemma 3.29): every `f : E_s 1_μ ⟶ E_t 1_μ` of `U′` is `bendLoc F` for some
`F : 1_μ ⟶ E_{s* t} 1_μ`. -/
theorem exists_bendLoc_eq (μ : X) (s t : List (Letter I))
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD μ s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ t))) :
    ∃ F, bendLoc RD k μ s t F = f := by
  refine loc_mem_of_layers_from RD k μ s (fun t => LinearMap.range (bendLoc RD k μ s t)) ?_ ?_ ?_
    t f
  · refine ⟨(toLoc RD k).map (bendF RD k μ s s (𝟙 _)), ?_⟩
    show bendLoc RD k μ s s _ = 𝟙 ((presLoc RD k).obj ((incl RD).obj (ob RD μ s)))
    rw [bendLoc_toLoc, (bend_facts (RD := RD) (k := k) μ s s).2.2.1]
    exact (toLoc RD k).map_id _
  · rintro u g v _ ⟨F, rfl⟩
    exact ⟨_, bendLoc_comp_layer RD k μ s u v g F⟩
  · rintro u i w _ ⟨F, rfl⟩
    obtain ⟨F', hF'⟩ := bendLoc_comp_inv RD k μ s u w i F
    exact ⟨F', by rw [hF', diag_invDot_eq_inv]⟩

end Categorification.KL3.Diagram
