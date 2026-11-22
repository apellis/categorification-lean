/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCups
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# Normal-form diagrams under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The weight shift `shiftImg RD k δ a b` sends a normal-form layer
`lay μ u g v` to the same layer in the shifted region, followed (for a cup) or preceded (for a
cap) by integer powers of the downward dot on the downward leg.

## Main results

* `ldg`: the image in `U′` of the normal-form diagram `dg μ s t ls` of `U`, with its composition
  calculus.
* `shiftFree_layer_lay`: the image of a normal-form layer (`imgLay`).
* `shiftFree_map_mkD`: the image of a normal-form diagram is the composite `imgList` of the images
  of its layers.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- The normal-form diagram with layers `ls` in `U′`. -/
abbrev ldg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    lob RD k μ s ⟶ lob RD k μ t :=
  (toLoc RD k).map (dg RD k μ s t ls)

theorem ldg_of {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    ldg RD k μ s t ls = (presLoc RD k).diag (inclD RD (mkD RD μ ls h)) := by
  rw [ldg, dg_of h, ← lin_of, toLoc_lin, inclLin_of, lin_of]

theorem ldg_comp {μ : X} {s t r : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A t)
    (hB : SChain t B r) : ldg RD k μ s t A ≫ ldg RD k μ t r B = ldg RD k μ s r (A ++ B) := by
  rw [ldg, ldg, ← Functor.map_comp, dg_comp hA hB]

theorem ldg_nil (μ : X) (s : List (Letter I)) : ldg RD k μ s s [] = 𝟙 _ := by
  rw [ldg, dg_nil]; exact (toLoc RD k).map_id _

theorem sChain_single (x : LayerData I) :
    SChain (x.1 ++ x.2.1.dom ++ x.2.2) [x] (x.1 ++ x.2.1.cod ++ x.2.2) := ⟨rfl, rfl⟩

theorem whiskerOK_lob (μ : X) (u v s s' : List (Letter I))
    (hs : wt RD (wt RD μ v) s' = wt RD (wt RD μ v) s) :
    ((incl RD).obj (ob RD (wt RD μ v) s')).WhiskerOK (lU RD μ u v s) (wd RD μ v) := by
  rw [lU, ← hs]; exact lwhiskerOK RD μ u v s'

theorem lob_whisker' (μ : X) (u v s s' : List (Letter I))
    (hs : wt RD (wt RD μ v) s' = wt RD (wt RD μ v) s) :
    ((incl RD).obj (ob RD (wt RD μ v) s')).whisker (lU RD μ u v s) (wd RD μ v) =
      (incl RD).obj (ob RD μ (u ++ s' ++ v)) :=
  congrArg (incl RD).obj (ob_whisker RD μ u v s s' hs)

/-- Placing a one-layer diagram between strands gives the placed layer. -/
theorem whisk_lgen (μ : X) (u v : List (Letter I)) (g : Shape I) :
    (presLoc RD k).whisk (lgen RD k (wt RD μ v) g) (lU RD μ u v g.dom) (wd RD μ v) =
      eqToHom (congrArg (presLoc RD k).obj (lob_whisker RD μ u v g.dom)) ≫
        ldg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)] ≫
          eqToHom (congrArg (presLoc RD k).obj (lob_whisker' RD μ u v g.dom g.cod
            (Shape.wt_dom_eq_wt_cod (RD := RD) _ g).symm)).symm := by
  rw [lgen, Presentation.whisk_diag _ _ _ _ (lwhiskerOK RD μ u v g.dom),
    (presLoc RD k).diag_eq_of_layers_eq' _ (inclD RD (mkD RD μ [(u, g, v)] (sChain_single (u, g, v))))
      (lob_whisker RD μ u v g.dom) (lob_whisker' RD μ u v g.dom g.cod
            (Shape.wt_dom_eq_wt_cod (RD := RD) _ g).symm), ldg_of RD k (sChain_single (u, g, v))]
  show [((incl RD).layer (lay RD (wt RD μ v) [] g [])).whisker _ _] =
    [(incl RD).layer (lay RD μ u g v)]
  congr 1
  have := lay_whisker RD μ u v [] g [] g.dom (by simp)
  simp only [List.append_nil, List.nil_append] at this
  rw [← this]; rfl

theorem whisk_lgen' (μ : X) (u v s : List (Letter I)) (g : Shape I) (hs : g.dom = s) :
    (presLoc RD k).whisk (lgen RD k (wt RD μ v) g) (lU RD μ u v s) (wd RD μ v) =
      eqToHom (congrArg (presLoc RD k).obj (lob_whisker' RD μ u v s g.dom (by rw [hs]))) ≫
        ldg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)] ≫
          eqToHom (congrArg (presLoc RD k).obj (lob_whisker' RD μ u v s g.cod
            (by rw [← hs, ← Shape.wt_dom_eq_wt_cod]))).symm := by
  subst hs; exact whisk_lgen RD k μ u v g

theorem lob_whisker_dot (μ : X) (u v s u₀ v₀ u' v' : List (Letter I)) (i : I)
    (hs : wt RD (wt RD μ v) (u₀ ++ [dn i] ++ v₀) = wt RD (wt RD μ v) s)
    (hu : u ++ u₀ = u') (hv : v₀ ++ v = v') :
    ((incl RD).obj (ob RD (wt RD μ v) (u₀ ++ [dn i] ++ v₀))).whisker (lU RD μ u v s) (wd RD μ v) =
      (incl RD).obj (ob RD μ (u' ++ [dn i] ++ v')) := by
  subst hu hv
  refine (lob_whisker' RD μ u v s _ hs).trans ?_
  simp only [List.append_assoc]

/-- Placing integer powers of the downward dot between strands. -/
theorem whisk_zdot_lU (μ : X) (u v s u₀ v₀ u' v' : List (Letter I)) (i : I) (n : ℤ)
    (hs : wt RD (wt RD μ v) (u₀ ++ [dn i] ++ v₀) = wt RD (wt RD μ v) s)
    (hu : u ++ u₀ = u') (hv : v₀ ++ v = v') :
    (presLoc RD k).whisk (zdot RD k (wt RD μ v) u₀ i v₀ n) (lU RD μ u v s) (wd RD μ v) =
      eqToHom (congrArg (presLoc RD k).obj (lob_whisker_dot RD μ u v s u₀ v₀ u' v' i hs hu hv)) ≫
        zdot RD k μ u' i v' n ≫
          eqToHom (congrArg (presLoc RD k).obj
            (lob_whisker_dot RD μ u v s u₀ v₀ u' v' i hs hu hv)).symm := by
  refine whisk_zdot RD k (wt RD μ v) u₀ i v₀ n _ _ (whiskerOK_lob RD μ u v s _ hs) μ u' v'
    (lob_whisker_dot RD μ u v s u₀ v₀ u' v' i hs hu hv) ?_
  subst hu hv
  have := lay_whisker RD μ u v u₀ (.dot (dn i)) v₀ s hs
  exact congrArg (incl RD).layer this


section Layers

variable (δ : X) (a b : I → ℤ)

theorem ofGen_layer_cap (s : X) (l' : List (Col I X)) (c : Col I X) (r : List (Col I X))
    (hv : (⟨s, l', .inl (.cap c), r⟩ : Layer (lsig RD)).Valid) :
    (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer _ hv =
      eqToHom (congrArg (presLoc RD k).obj
          ((congrArg (fun x => Obj.whisker x _ _) (genDom_cap RD δ c)).symm.trans
            (LocalMap.whisker_genDom (shiftMap RD δ) ⟨s, l', .inl (.cap c), r⟩))).symm ≫
        (presLoc RD k).whisk (capImg RD k a b c.l (c.r + δ))
          ((shiftMap RD δ).obj ⟨s, l'⟩) ((shiftMap RD δ).word r) ≫
        eqToHom (congrArg (presLoc RD k).obj
          ((congrArg (fun x => Obj.whisker x _ _) (genCod_cap RD δ c)).symm.trans
            (LocalMap.whisker_genCod (shiftMap RD δ) ⟨s, l', .inl (.cap c), r⟩))) := by
  rw [LocalMap.ofGen_layer]
  show _ ≫ (presLoc RD k).whisk (eqToHom _ ≫ _ ≫ eqToHom _) _ _ ≫ _ = _
  rw [whisk_conj RD k (genDom_cap RD δ c) (genCod_cap RD δ c)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem whisk_cupImg_congr (l : Letter I) {ν ν' : X} (hν : ν' = ν) {U U' : Obj (lsig RD)}
    (hU : U = U') {V V' : List (Col I X)} (hV : V = V') :
    (presLoc RD k).whisk (cupImg RD k a b l ν') U V =
      eqToHom (congrArg (presLoc RD k).obj
          (show ((incl RD).obj (ob RD ν' [])).whisker U V =
            ((incl RD).obj (ob RD ν [])).whisker U' V' by subst hν hU hV; rfl)) ≫
        (presLoc RD k).whisk (cupImg RD k a b l ν) U' V' ≫
          eqToHom (congrArg (presLoc RD k).obj
            (show ((incl RD).obj (ob RD ν' [l, l.dual])).whisker U V =
              ((incl RD).obj (ob RD ν [l, l.dual])).whisker U' V' by subst hν hU hV; rfl)).symm := by
  subst hν hU hV; simp

theorem whisk_capImg_congr (l : Letter I) {ν ν' : X} (hν : ν' = ν) {U U' : Obj (lsig RD)}
    (hU : U = U') {V V' : List (Col I X)} (hV : V = V') :
    (presLoc RD k).whisk (capImg RD k a b l ν') U V =
      eqToHom (congrArg (presLoc RD k).obj
          (show ((incl RD).obj (ob RD ν' [l.dual, l])).whisker U V =
            ((incl RD).obj (ob RD ν [l.dual, l])).whisker U' V' by subst hν hU hV; rfl)) ≫
        (presLoc RD k).whisk (capImg RD k a b l ν) U' V' ≫
          eqToHom (congrArg (presLoc RD k).obj
            (show ((incl RD).obj (ob RD ν' [])).whisker U V =
              ((incl RD).obj (ob RD ν [])).whisker U' V' by subst hν hU hV; rfl)).symm := by
  subst hν hU hV; simp

/-- The dots `y^{a_i}`, resp. `y^{b_i}`, on the downward leg of a cap `l* l` placed between the
strands `u` and `v`. -/
def capDecAt (ν : X) (u : List (Letter I)) :
    (l : Letter I) → (v : List (Letter I)) →
      (lob RD k ν (u ++ [l.dual, l] ++ v) ⟶ lob RD k ν (u ++ [l.dual, l] ++ v))
  | (true, i), v => eqToHom (congrArg (lob RD k ν) (by simp)) ≫
      zdot RD k ν u i ([up i] ++ v) (a i) ≫ eqToHom (congrArg (lob RD k ν) (by simp))
  | (false, i), v => eqToHom (congrArg (lob RD k ν) (by simp)) ≫
      zdot RD k ν (u ++ [up i]) i v (b i) ≫ eqToHom (congrArg (lob RD k ν) (by simp))

theorem shiftFree_layer_cup (μ : X) (u v : List (Letter I)) (l : Letter I)
    (hv : ((incl RD).layer (lay RD μ u (.cup l) v)).Valid) :
    (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer _ hv =
      eqToHom (congrArg (presLoc RD k).obj (shift_lay_dom RD δ μ u (.cup l) v)) ≫
        (ldg RD k (μ + δ) (u ++ [] ++ v) (u ++ [l, l.dual] ++ v) [(u, .cup l, v)] ≫
          cupDecAt RD k a b (μ + δ) u l v) ≫
        eqToHom (congrArg (presLoc RD k).obj (shift_lay_cod RD δ μ u (.cup l) v)).symm := by
  refine (ofGen_layer_cup RD k δ a b _ _ _ _ hv).trans ?_
  rw [whisk_cupImg_congr RD k a b _ (ν := wt RD (μ + δ) v) (U' := lU RD (μ + δ) u v [])
    (V' := wd RD (μ + δ) v) ?_ ?_ ?_, cupImg, Presentation.whisk_comp]
  rotate_left
  · show _ = _; simp only [sh_add_sh_dual_add, wt_add_shift]
  · exact shift_lay_left RD δ μ u (.cup l) v
  · exact shift_lay_right RD δ μ u (.cup l) v
  dsimp only
  rw [whisk_lgen' RD k (μ + δ) u v [] (.cup l) rfl]
  obtain ⟨_ | _, i⟩ := l
  · simp only [cupDec, cupDecAt]
    rw [whisk_zdot_lU RD k (μ + δ) u v [] [] [up i] u ([up i] ++ v) i (-b i) (by simp)
      (List.append_nil u) rfl]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  · simp only [cupDec, cupDecAt]
    rw [whisk_zdot_lU RD k (μ + δ) u v [] [up i] [] (u ++ [up i]) v i (-a i) (by simp)
      rfl (List.nil_append v)]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl

theorem shiftFree_layer_cap (μ : X) (u v : List (Letter I)) (l : Letter I)
    (hv : ((incl RD).layer (lay RD μ u (.cap l) v)).Valid) :
    (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer _ hv =
      eqToHom (congrArg (presLoc RD k).obj (shift_lay_dom RD δ μ u (.cap l) v)) ≫
        (capDecAt RD k a b (μ + δ) u l v ≫
          ldg RD k (μ + δ) (u ++ [l.dual, l] ++ v) (u ++ [] ++ v) [(u, .cap l, v)]) ≫
        eqToHom (congrArg (presLoc RD k).obj (shift_lay_cod RD δ μ u (.cap l) v)).symm := by
  refine (ofGen_layer_cap RD k δ a b _ _ _ _ hv).trans ?_
  rw [whisk_capImg_congr RD k a b _ (ν := wt RD (μ + δ) v) (U' := lU RD (μ + δ) u v [l.dual, l])
    (V' := wd RD (μ + δ) v) ?_ ?_ ?_, capImg, Presentation.whisk_comp]
  rotate_left
  · show _ = _; simp only [wt_add_shift]
  · exact shift_lay_left RD δ μ u (.cap l) v
  · exact shift_lay_right RD δ μ u (.cap l) v
  dsimp only
  rw [whisk_lgen' RD k (μ + δ) u v [l.dual, l] (.cap l) rfl]
  obtain ⟨_ | _, i⟩ := l
  · simp only [capDec, capDecAt]
    rw [whisk_zdot_lU RD k (μ + δ) u v [Letter.dual (false, i), (false, i)] [up i] [] (u ++ [up i]) v i (b i) (by simp)
      rfl (List.nil_append v)]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  · simp only [capDec, capDecAt]
    rw [whisk_zdot_lU RD k (μ + δ) u v [Letter.dual (true, i), (true, i)] [] [up i] u ([up i] ++ v) i (a i) (by simp)
      (List.append_nil u) rfl]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl


/-- The image of one normal-form layer under the weight shift: the same layer, followed by the
dots `y^{-a_i}`, `y^{-b_i}` on the downward leg of a cup, or preceded by the dots `y^{a_i}`,
`y^{b_i}` on the downward leg of a cap. -/
def imgLay (ν : X) : (x : LayerData I) →
    (lob RD k ν (x.1 ++ x.2.1.dom ++ x.2.2) ⟶ lob RD k ν (x.1 ++ x.2.1.cod ++ x.2.2))
  | (u, .dot l, v) => ldg RD k ν _ _ [(u, .dot l, v)]
  | (u, .cross ε i j, v) => ldg RD k ν _ _ [(u, .cross ε i j, v)]
  | (u, .cup l, v) => ldg RD k ν _ _ [(u, .cup l, v)] ≫ cupDecAt RD k a b ν u l v
  | (u, .cap l, v) => capDecAt RD k a b ν u l v ≫ ldg RD k ν _ _ [(u, .cap l, v)]

theorem shiftFree_layer_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (hv : ((incl RD).layer (lay RD μ u g v)).Valid) :
    (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer _ hv =
      eqToHom (congrArg (presLoc RD k).obj (shift_lay_dom RD δ μ u g v)) ≫
        imgLay RD k a b (μ + δ) (u, g, v) ≫
        eqToHom (congrArg (presLoc RD k).obj (shift_lay_cod RD δ μ u g v)).symm := by
  cases g with
  | cup l => exact shiftFree_layer_cup RD k δ a b μ u v l hv
  | cap l => exact shiftFree_layer_cap RD k δ a b μ u v l hv
  | dot l =>
    obtain ⟨hv', e₁, e₂, h⟩ := shiftFree_layer RD k δ a b _ hv trivial
    rw [h, (presLoc RD k).diag_eq_of_layers_eq' _
      (inclD RD (mkD RD (μ + δ) [(u, .dot l, v)] (sChain_single _)))
      (shift_lay_dom RD δ μ u _ v) (shift_lay_cod RD δ μ u _ v)
      (by show [_] = [_]; rw [shiftLayer_lay]; rfl), ← ldg_of]
    rfl
  | cross ε i j =>
    obtain ⟨hv', e₁, e₂, h⟩ := shiftFree_layer RD k δ a b _ hv trivial
    rw [h, (presLoc RD k).diag_eq_of_layers_eq' _
      (inclD RD (mkD RD (μ + δ) [(u, .cross ε i j, v)] (sChain_single _)))
      (shift_lay_dom RD δ μ u _ v) (shift_lay_cod RD δ μ u _ v)
      (by show [_] = [_]; rw [shiftLayer_lay]; rfl), ← ldg_of]
    rfl

/-- The composite of the images of the layers of a normal-form diagram. -/
def imgList (ν : X) : (ls : List (LayerData I)) → {s t : List (Letter I)} → SChain s ls t →
    (lob RD k ν s ⟶ lob RD k ν t)
  | [], _, _, h => eqToHom (congrArg (lob RD k ν) h)
  | x :: ls, _, _, h =>
    eqToHom (congrArg (lob RD k ν) h.1) ≫ imgLay RD k a b ν x ≫ imgList ν ls h.2

/-- **The image of a normal-form diagram under the weight shift** (Webster arXiv:1309.3796v2,
Proposition 3.30): the composite of the images of its layers. -/
theorem shiftFree_map_mkD (μ : X) (ls : List (LayerData I)) {s t : List (Letter I)}
    (h : SChain s ls t) :
    (shiftFree RD k δ a b).map (inclD RD (mkD RD μ ls h)) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ s) ≫ imgList RD k a b (μ + δ) ls h ≫
        eqToHom (shiftFree_obj_ob RD k δ a b μ t).symm := by
  induction ls generalizing s with
  | nil =>
    cases h
    simp only [imgList, eqToHom_refl, Category.id_comp, eqToHom_trans]
    rfl
  | cons x ls ih =>
    obtain ⟨rfl, h₂⟩ := h
    have hv : ((incl RD).layer (lay RD μ x.1 x.2.1 x.2.2)).Valid :=
      (incl RD).toLayerMap.valid (lay_valid RD μ x.1 x.2.1 x.2.2)
    have e₁ : ((incl RD).layer (lay RD μ x.1 x.2.1 x.2.2)).dom = _ := ((incl RD).toLayerMap.dom_eq (lay_valid RD μ x.1 x.2.1 x.2.2)).trans
      (congrArg (incl RD).obj (lay_dom RD μ x.1 x.2.1 x.2.2))
    have e₂ : ((incl RD).layer (lay RD μ x.1 x.2.1 x.2.2)).cod = _ := ((incl RD).toLayerMap.cod_eq (lay_valid RD μ x.1 x.2.1 x.2.2)).trans
      (congrArg (incl RD).obj (lay_cod RD μ x.1 x.2.1 x.2.2))
    have e : inclD RD (mkD RD μ (x :: ls) ⟨rfl, h₂⟩) =
        Diagram.layer _ hv e₁ e₂ ≫ inclD RD (mkD RD μ ls h₂) := Diagram.ext rfl
    have e' : (shiftFree RD k δ a b).map (Diagram.layer _ hv e₁ e₂) =
        eqToHom (congrArg (fun z => (presLoc RD k).obj
            ((LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).obj z)) e₁.symm) ≫
          (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer _ hv ≫
          eqToHom (congrArg (fun z => (presLoc RD k).obj
            ((LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).obj z)) e₂) := rfl
    rw [e, Functor.map_comp, e', shiftFree_layer_lay, ih]
    simp only [imgList, eqToHom_refl, Category.id_comp, Category.assoc, eqToHom_trans_assoc]

end Layers

end Categorification.KL3.Diagram
