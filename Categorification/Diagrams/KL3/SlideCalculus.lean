/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Upward

/-!
# A calculus of local rewriting for normal-form diagrams of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.

Diagrams of `U` in normal form (`mkD RD μ ls h`, a list of layers `(u, g, v)` with rightmost
region `μ`, see `Categorification.Diagrams.KL3.Basic`) are manipulated by local moves: a
subdiagram, possibly placed between strands `u` and `v`, is replaced by an equal linear
combination of subdiagrams. This file provides the placement map and the general rewriting
principle:

* `whL u v`: a layer datum placed between the strands `u` and `v`;
* `plc RD k μ u v hst`, `plcL`: the `k`-linear map placing a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`
  (`ν = μ + v_X`) between the strands `u` and `v`, with rightmost region `μ` (whiskering in the
  presented category); `plc_diag`, `plcL_dg`: on a normal-form diagram it acts by `whL u v` on
  the layers; `plcL_comp`: placement is functorial;
* `dg RD k μ s t ls`: the class of the normal-form diagram with layers `ls` (or `0` if they do
  not chain from `s` to `t`), with `dg_comp`, `dg_nil`;
* `ctxL`, `ctxL_dg`, `dg_step`, `dg_stepL` and the tactic `dstep pre post u v E`: one step of a
  certificate chain, rewriting a subdiagram (placed between the strands `u`, `v`, with `pre`
  below and `post` above) by a local equation `E`; `schain` proves the typing side conditions;
* the local relations in normal form: `dg_swap`, `dg_swap'` (interchange), `dg_zigL'`,
  `dg_zigR'` (zigzags), `dg_downupEF`, `dg_downupFE` (`eq_downup_ij-gen`), `dg_cycDotL`,
  `dg_cycDotR` (KL III (3.3)), `dg_slideLNe`, `dg_slideRNe`, `dg_sqNe` (`eq_dot_slide_ij-gen`,
  `eq_r2_ij-gen`), `dg_slideLEq`, `dg_slideREq`, `dg_sqEq` (`eq_nil_rels`, `eq_nil_dotslide`),
  `dg_ccwNeg`, `dg_cwNeg`, `dg_ccwOne`, `dg_cwOne` (`eq_positivity_bubbles` and the degree-zero
  bubbles), `dg_curlL`, `dg_curlR` (curl relations, item iv)), `dg_decompEF`, `dg_decompFE`
  (`eq_ident_decomp`);
* `bubLU`, `bubRU`: endomorphisms of `1` placed to the left/right of a strand, with
  `lin_bubL`, `lin_bubR` (the `bubL`, `bubR` of `Relations.lean`) and the centrality lemmas
  `bubLU_comm`, `bubRU_comm` (interchange law); `ccwU`, `cwU`: the real or fake bubbles
  `ccwL`, `cwL` in `U`; `dotsU`: dots on a strand.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Whiskering of layer data -/

/-- The layer datum `x` placed between the strands `u` (left) and `v` (right). -/
def whL (u v : List (Letter I)) (x : LayerData I) : LayerData I := (u ++ x.1, x.2.1, x.2.2 ++ v)

@[simp] theorem whL_nil_nil (x : LayerData I) : whL [] [] x = x := by
  obtain ⟨a, g, b⟩ := x; simp [whL]

@[simp] theorem map_whL_nil_nil (l : List (LayerData I)) : l.map (whL [] []) = l := by
  simp [List.map_congr_left (fun x _ => whL_nil_nil x)]

theorem SChain.whisk {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (u v : List (Letter I)) : SChain (u ++ s ++ v) (ls.map (whL u v)) (u ++ t ++ v) := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [whL], ?_⟩
    have := ih h
    simpa [whL] using this

/-- The weight of the left region is constant along a chain of layers. -/
theorem SChain.wt_eq (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    wt RD ν t = wt RD ν s := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [ih h, wt_lay_dom]

theorem SChain.wt_mem (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain s ls t) : ∀ x ∈ ls, wt RD ν (x.1 ++ x.2.1.dom ++ x.2.2) = wt RD ν s := by
  induction ls generalizing s with
  | nil => simp
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · rfl
    · rw [ih h y hy, wt_lay_dom]

theorem SChain.eq_target {s t t' : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (h' : SChain s ls t') : t = t' := by
  induction ls generalizing s with
  | nil => exact h.symm.trans h'
  | cons x ls ih => exact ih h.2 h'.2

theorem SChain.split {s t : List (Letter I)} {ls ms : List (LayerData I)} (h : SChain s (ls ++ ms) t) :
    ∃ a, SChain s ls a ∧ SChain a ms t := by
  induction ls generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    obtain ⟨a, h₁, h₂⟩ := ih h
    exact ⟨a, ⟨rfl, h₁⟩, h₂⟩

/-- A placed layer in normal form. -/
theorem lay_whisker (μ : X) (u v a : List (Letter I)) (g : Shape I) (b s : List (Letter I))
    (hs : wt RD (wt RD μ v) (a ++ g.dom ++ b) = wt RD (wt RD μ v) s) :
    (lay RD (wt RD μ v) a g b).whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) =
      lay RD μ (u ++ a) g (b ++ v) := by
  have e₁ : wt RD μ (g.dom ++ b ++ v) = wt RD (wt RD μ v) (g.dom ++ b) := by
    simp only [List.append_assoc, wt_append]
  have hs' : wt RD (wt RD (wt RD μ v) (g.dom ++ b)) a = wt RD (wt RD μ v) s := by
    rw [← wt_append, ← List.append_assoc]; exact hs
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp only [Layer.whisker, ob_start, lay, List.append_assoc, wt_append] at hs ⊢
    rw [hs]
  · simp only [wt_append] at hs'
    simp only [Layer.whisker, ob_word, lay, List.append_assoc, wd_append, wt_append]
    rw [hs']
  · simp only [Layer.whisker, lay, wt_append]
  · simp only [Layer.whisker, lay, wd_append]

theorem layList_whisker (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    {ls : List (LayerData I)} (h : SChain s ls t) :
    (layList RD (wt RD μ v) ls).map (·.whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)) =
      layList RD μ (ls.map (whL u v)) := by
  have hm := h.wt_mem RD (wt RD μ v)
  simp only [layList, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  exact lay_whisker RD μ u v x.1 x.2.1 x.2.2 s (hm x hx)

/-! ## Placement -/

theorem whiskerOK_ob (μ : X) (u v s : List (Letter I)) :
    (ob RD (wt RD μ v) s).WhiskerOK (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) :=
  ⟨ok_wd RD _ u, endR_wd RD _ u, by rw [ob_endR]; exact ok_wd RD μ v⟩

theorem ob_whisker (μ : X) (u v s s' : List (Letter I))
    (hs : wt RD (wt RD μ v) s' = wt RD (wt RD μ v) s) :
    (ob RD (wt RD μ v) s').whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) =
      ob RD μ (u ++ s' ++ v) := by
  refine Obj.ext ?_ ?_
  · simp only [Obj.whisker_start, ob_start, List.append_assoc, wt_append, hs]
  · simp only [Obj.whisker_word, ob_word, List.append_assoc, wd_append, wt_append, hs]

variable {RD} in
/-- The objects `E_{u s v} 1_μ` and the whiskering of `E_s 1_{μ + v_X}`. -/
abbrev obW (μ : X) (u v s : List (Letter I)) :=
  (ob RD (wt RD μ v) s).whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)

/-- **Placement.** The `k`-linear map placing a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`, with
`ν = μ + v_X`, between the strands `u` and `v`; the rightmost region becomes `μ`. -/
def plc (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) :
    ((pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) →ₗ[k]
      ((pres RD k).obj (ob RD μ (u ++ s ++ v)) ⟶ (pres RD k).obj (ob RD μ (u ++ t ++ v))) where
  toFun f := eqToHom (congrArg (pres RD k).obj (ob_whisker RD μ u v s s rfl).symm) ≫
    (pres RD k).whisk f (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) ≫
      eqToHom (congrArg (pres RD k).obj (ob_whisker RD μ u v s t hst))
  map_add' f g := by
    rw [Presentation.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [Presentation.whisk_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Placement acts on normal-form diagrams by placing every layer. -/
theorem plc_diag (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) (ls : List (LayerData I))
    (h : SChain s ls t) :
    plc RD k μ u v hst ((pres RD k).diag (mkD RD (wt RD μ v) ls h)) =
      (pres RD k).diag (mkD RD μ (ls.map (whL u v)) (h.whisk u v)) := by
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ u v s)]
  rw [(pres RD k).diag_eq_of_layers_eq' (mkD RD μ (ls.map (whL u v)) (h.whisk u v))
    (Diagram.whisker (mkD RD (wt RD μ v) ls h) (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)
      (whiskerOK_ob RD μ u v s)) (ob_whisker RD μ u v s s rfl).symm
      (ob_whisker RD μ u v s t hst).symm ?_]
  rw [Diagram.layers_whisker, layers_mkD, layers_mkD, layList_whisker RD μ u v h]

/-! ## Rewriting in context -/

/-- **Rewriting in context.** Place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + v_X`) between
the strands `u` and `v`, and compose with the normal-form diagrams `pre` below and `post`
above. -/
def ctx (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) :
    ((pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) →ₗ[k]
      ((pres RD k).obj (ob RD μ s₀) ⟶ (pres RD k).obj (ob RD μ t₀)) where
  toFun f := (pres RD k).diag (mkD RD μ pre hpre) ≫ plc RD k μ u v hst f ≫
    (pres RD k).diag (mkD RD μ post hpost)
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ctx_apply (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) :
    ctx RD k μ pre u v post hpre hpost hst f =
      (pres RD k).diag (mkD RD μ pre hpre) ≫ plc RD k μ u v hst f ≫
        (pres RD k).diag (mkD RD μ post hpost) := rfl

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctx_diag (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (ls : List (LayerData I)) (h : SChain s ls t) :
    ctx RD k μ pre u v post hpre hpost hst ((pres RD k).diag (mkD RD (wt RD μ v) ls h)) =
      (pres RD k).diag (mkD RD μ (pre ++ ls.map (whL u v) ++ post)
        ((hpre.append (h.whisk u v)).append hpost)) := by
  rw [ctx_apply, plc_diag, ← Presentation.diag_comp, ← Presentation.diag_comp, mkD_comp, mkD_comp]
  exact (pres RD k).diag_eq_of_layers_eq (by simp)

/-! ## Diagram classes without typing proofs -/

section Dg

variable {RD k}

theorem SChain.nil' (s : List (Letter I)) : SChain s [] s := rfl

theorem SChain.eq_source {b b' t : List (Letter I)} {ls : List (LayerData I)} (h : SChain b ls t)
    (h' : SChain b' ls t) : b = b' := by
  cases ls with
  | nil => exact h.trans h'.symm
  | cons x ls => exact h.1.trans h'.1.symm

theorem SChain.of_whisk {u v s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain (u ++ s ++ v) (ls.map (whL u v)) (u ++ t ++ v)) : SChain s ls t := by
  induction ls generalizing s with
  | nil =>
    have h' : u ++ s ++ v = u ++ t ++ v := h
    simpa using h'
  | cons x ls ih =>
    obtain ⟨h₁, h₂⟩ := h
    have e : s = x.1 ++ x.2.1.dom ++ x.2.2 := by
      have h₁' : u ++ (s ++ v) = u ++ ((x.1 ++ x.2.1.dom ++ x.2.2) ++ v) := by
        simpa [whL, List.append_assoc] using h₁
      exact List.append_cancel_right (List.append_cancel_left h₁')
    subst e
    refine ⟨rfl, ih ?_⟩
    simpa [whL] using h₂

end Dg

open Classical in
/-- The class in `U` of the normal-form diagram with layers `ls` from `E_s 1_μ` to `E_t 1_μ`
(rightmost region `μ`), or `0` if the layers do not form such a diagram. -/
def dg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t) :=
  if h : SChain s ls t then (pres RD k).diag (mkD RD μ ls h) else 0

section Dg

variable {RD k}

theorem dg_of {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    dg RD k μ s t ls = (pres RD k).diag (mkD RD μ ls h) := dif_pos h

theorem dg_of_not {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : ¬ SChain s ls t) : dg RD k μ s t ls = 0 := dif_neg h

theorem dg_nil (μ : X) (s : List (Letter I)) : dg RD k μ s s [] = 𝟙 _ := by
  rw [dg_of (show SChain s [] s from rfl)]
  exact ((pres RD k).diag_eq_of_layers_eq rfl).trans ((pres RD k).diag_id _)

theorem dg_comp {μ : X} {s t r : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A t)
    (hB : SChain t B r) : dg RD k μ s t A ≫ dg RD k μ t r B = dg RD k μ s r (A ++ B) := by
  rw [dg_of hA, dg_of hB, dg_of (hA.append hB), ← Presentation.diag_comp, mkD_comp]

end Dg

open Classical in
/-- Placement between the strands `u` and `v`, as a `k`-linear map on all morphisms
`E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + v_X`); it is `0` if `s` and `t` have different weights. -/
def plcL (μ : X) (u v s t : List (Letter I)) :
    ((pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) →ₗ[k]
      ((pres RD k).obj (ob RD μ (u ++ s ++ v)) ⟶ (pres RD k).obj (ob RD μ (u ++ t ++ v))) :=
  if h : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s then plc RD k μ u v h else 0

theorem plcL_dg (μ : X) (u v s t : List (Letter I)) (A : List (LayerData I)) :
    plcL RD k μ u v s t (dg RD k (wt RD μ v) s t A) =
      dg RD k μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) := by
  by_cases hA : SChain s A t
  · rw [plcL, dif_pos (hA.wt_eq RD _), dg_of hA, plc_diag, dg_of]
  · rw [dg_of_not hA, map_zero, dg_of_not (fun h => hA h.of_whisk)]

/-- `plcL_dg` for an empty right context. -/
theorem plcL_dg_nil (μ : X) (u s t : List (Letter I)) (A : List (LayerData I)) :
    plcL RD k μ u [] s t (dg RD k μ s t A) = dg RD k μ (u ++ s ++ []) (u ++ t ++ []) (A.map (whL u [])) :=
  plcL_dg RD k μ u [] s t A

/-- **Rewriting in context**, as a `k`-linear map: place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`
(`ν = μ + v_X`) between the strands `u` and `v` and compose with the normal-form diagrams
`pre` below and `post` above. -/
def ctxL (μ : X) (s₀ t₀ : List (Letter I)) (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (s t : List (Letter I)) :
    ((pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) →ₗ[k]
      ((pres RD k).obj (ob RD μ s₀) ⟶ (pres RD k).obj (ob RD μ t₀)) where
  toFun f := dg RD k μ s₀ (u ++ s ++ v) pre ≫ plcL RD k μ u v s t f ≫
    dg RD k μ (u ++ t ++ v) t₀ post
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctxL_dg (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (A : List (LayerData I)) :
    ctxL RD k μ s₀ t₀ pre u v post s t (dg RD k (wt RD μ v) s t A) =
      dg RD k μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) := by
  show dg RD k μ s₀ (u ++ s ++ v) pre ≫ plcL RD k μ u v s t _ ≫ dg RD k μ (u ++ t ++ v) t₀ post = _
  rw [plcL_dg]
  by_cases hA : SChain s A t
  · rw [dg_comp (hA.whisk u v) hpost, dg_comp hpre ((hA.whisk u v).append hpost),
      List.append_assoc]
  · rw [dg_of_not (fun h => hA h.of_whisk), Limits.zero_comp, Limits.comp_zero, dg_of_not]
    intro h
    obtain ⟨a, h₁, h₂⟩ := SChain.split h
    obtain ⟨b, h₃, h₄⟩ := SChain.split h₁
    obtain rfl := h₃.eq_target hpre
    obtain rfl := h₂.eq_source hpost
    exact hA h₄.of_whisk

/-- `ctxL_dg` for an empty right context (the region is then unchanged). -/
theorem ctxL_dg_nil (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ [])) (hpost : SChain (u ++ t ++ []) post t₀)
    (A : List (LayerData I)) :
    ctxL RD k μ s₀ t₀ pre u [] post s t (dg RD k μ s t A) =
      dg RD k μ s₀ t₀ (pre ++ A.map (whL u []) ++ post) :=
  ctxL_dg RD k μ hpre hpost A

/-- **The rewriting principle.** If `dg ν s t A = F` (`ν = μ + v_X`), then the diagram
`pre ++ A ++ post`, with `A` placed between the strands `u` and `v`, equals the image of `F`
under `ctxL`. -/
theorem dg_rw (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    {A : List (LayerData I)} {F : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶
      (pres RD k).obj (ob RD (wt RD μ v) t)} (E : dg RD k (wt RD μ v) s t A = F) :
    dg RD k μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) = ctxL RD k μ s₀ t₀ pre u v post s t F := by
  rw [← E, ctxL_dg RD k μ hpre hpost]

/-- **One step of a certificate chain.** If `dg ν s t A = dg ν s t B` (`ν = μ + v_X`), then
in any diagram in which `A` occurs between the strands `u` and `v` (below it the layers `pre`,
above it the layers `post`), `A` may be replaced by `B`. -/
theorem dg_step (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B L L' : List (LayerData I)}
    (E : dg RD k (wt RD μ v) s t A = dg RD k (wt RD μ v) s t B)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    dg RD k μ s₀ t₀ L = dg RD k μ s₀ t₀ L' := by
  rw [hL, hL', dg_rw RD k μ hpre hpost E, ctxL_dg RD k μ hpre hpost]

/-- One step of a certificate chain whose right-hand side is a linear combination: the image of
the right-hand side under `ctxL`. -/
theorem dg_stepL (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A L : List (LayerData I)}
    {F : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)}
    (E : dg RD k (wt RD μ v) s t A = F)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) :
    dg RD k μ s₀ t₀ L = ctxL RD k μ s₀ t₀ pre u v post s t F := by
  rw [hL, dg_rw RD k μ hpre hpost E]

section SChainLemmas

theorem sChain_append_iff {s t : List (Letter I)} (ls ms : List (LayerData I)) (a : List (Letter I))
    (h : SChain s ls a) : SChain s (ls ++ ms) t ↔ SChain a ms t := by
  constructor
  · intro h'
    obtain ⟨b, h₁, h₂⟩ := SChain.split h'
    obtain rfl := h.eq_target h₁
    exact h₂
  · exact h.append

/-- A block of dots (or other generators with equal source and target) does not change the
boundary. -/
theorem sChain_replicate_append {s t : List (Letter I)} (n : ℕ) (x : LayerData I)
    (hx : x.2.1.dom = x.2.1.cod) (ls : List (LayerData I))
    (hs : s = x.1 ++ x.2.1.dom ++ x.2.2) :
    SChain s (List.replicate n x ++ ls) t ↔ SChain s ls t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, sChain_cons]
    constructor
    · rintro ⟨-, h⟩; rw [← hx, ← hs] at h; exact ih.1 h
    · intro h; exact ⟨hs, by rw [← hx, ← hs]; exact ih.2 h⟩

theorem sChain_replicate {s t : List (Letter I)} (n : ℕ) (x : LayerData I)
    (hx : x.2.1.dom = x.2.1.cod) (hs : s = x.1 ++ x.2.1.dom ++ x.2.2) :
    SChain s (List.replicate n x) t ↔ s = t := by
  have := sChain_replicate_append (t := t) n x hx [] hs
  rwa [List.append_nil] at this

end SChainLemmas

/-! ## The interchange law in normal form -/

/-- The interchange law for two adjacent layers with empty outer context: the generator `g`
on the left, the strands `m`, the generator `h` on the right. -/
theorem swap_diag₀ (ν : X) (m : List (Letter I)) (g h : Shape I) {s t : List (Letter I)}
    (H₁ : SChain s [([], g, m ++ h.dom), (g.cod ++ m, h, [])] t)
    (H₂ : SChain s [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] t) :
    (pres RD k).diag (mkD RD ν _ H₁) = (pres RD k).diag (mkD RD ν _ H₂) := by
  obtain ⟨rfl, -, rfl⟩ := H₁
  have hm : wt RD ν (m ++ h.cod) = wt RD ν (m ++ h.dom) := by
    rw [wt_append, wt_append, Shape.wt_dom_eq_wt_cod]
  let x : InterchangeData (psig RD) :=
    ⟨(wt RD ν (g.dom ++ m ++ h.dom) : X), g.gen RD (wt RD ν (m ++ h.dom)), wd RD (wt RD ν h.dom) m,
      h.gen RD ν⟩
  have e₁ : x.gh₁ = lay RD ν [] g (m ++ h.dom) := by
    refine Layer.ext ?_ ?_ ?_ ?_ <;>
      simp [x, InterchangeData.gh₁, lay, Shape.dom_gen, wd_append, wt_append]
  have e₂ : x.gh₂ = lay RD ν (g.cod ++ m) h [] := by
    refine Layer.ext ?_ ?_ ?_ ?_ <;>
      simp [x, InterchangeData.gh₂, lay, Shape.cod_gen, wd_append, wt_append,
        Shape.wt_dom_eq_wt_cod]
  have e₃ : x.hg₁ = lay RD ν (g.dom ++ m) h [] := by
    refine Layer.ext ?_ ?_ ?_ ?_ <;>
      simp [x, InterchangeData.hg₁, lay, Shape.dom_gen, wd_append, wt_append]
  have e₄ : x.hg₂ = lay RD ν [] g (m ++ h.cod) := by
    refine Layer.ext ?_ ?_ ?_ ?_
    · simp [x, InterchangeData.hg₂, lay, wt_append, Shape.wt_dom_eq_wt_cod]
    · simp [x, InterchangeData.hg₂, lay]
    · simp only [x, InterchangeData.hg₂, lay, hm]
    · simp [x, InterchangeData.hg₂, lay, Shape.cod_gen, wd_append, wt_append,
        Shape.wt_dom_eq_wt_cod]
  have hx : x.Valid := ⟨e₁ ▸ lay_valid RD _ _ _ _, e₂ ▸ lay_valid RD _ _ _ _,
    e₃ ▸ lay_valid RD _ _ _ _, e₄ ▸ lay_valid RD _ _ _ _⟩
  have hw : x.dom.WhiskerOK (Obj.nil x.start) [] := ⟨trivial, rfl, by
    show (psig RD).ok (x.dom.endR) []
    trivial⟩
  have key := (pres RD k).diag_interchange x hx (Obj.nil x.start) [] hw rfl rfl
  have hs : ((x.sign : ℤ) : k) = 1 := by
    simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]
  rw [hs, one_smul] at key
  have ha : ob RD ν ([] ++ g.dom ++ (m ++ h.dom)) = x.dom.whisker (Obj.nil x.start) [] := by
    refine Obj.ext ?_ ?_
    · simp [x, ob]
    · simp [x, ob, InterchangeData.dom, Obj.whisker, Shape.dom_gen, wd_append, wt_append]
  have hb : ob RD ν (g.cod ++ m ++ h.cod ++ []) = x.cod.whisker (Obj.nil x.start) [] := by
    refine Obj.ext ?_ ?_
    · simp [x, ob, wt_append, Shape.wt_dom_eq_wt_cod]
    · simp [x, ob, InterchangeData.cod, Obj.whisker, Shape.cod_gen, wd_append, wt_append,
        Shape.wt_dom_eq_wt_cod]
  rw [(pres RD k).diag_eq_of_layers_eq' (mkD RD ν _ _) (Diagram.cast
      (Diagram.whisker (InterchangeData.ghDiagram hx) (Obj.nil x.start) [] hw) rfl rfl) ha hb ?_,
    (pres RD k).diag_eq_of_layers_eq' (mkD RD ν _ H₂) (Diagram.cast
      (Diagram.whisker (InterchangeData.hgDiagram hx) (Obj.nil x.start) [] hw) rfl rfl) ha hb ?_,
    key]
  · simp only [layers_mkD, layList_cons, layList_nil, Diagram.layers_cast, Diagram.layers_whisker,
      InterchangeData.hgDiagram, Diagram.layers_mk, List.map_cons, List.map_nil, ← e₃, ← e₄]
    simp [Layer.whisker]
    exact ⟨rfl, rfl⟩
  · simp only [layers_mkD, layList_cons, layList_nil, Diagram.layers_cast, Diagram.layers_whisker,
      InterchangeData.ghDiagram, Diagram.layers_mk, List.map_cons, List.map_nil, ← e₁, ← e₂]
    simp [Layer.whisker]
    exact ⟨rfl, rfl⟩

theorem dg_swap₀ (ν : X) (m : List (Letter I)) (g h : Shape I) :
    dg RD k ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [([], g, m ++ h.dom), (g.cod ++ m, h, [])] =
      dg RD k ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] := by
  have H₁ : SChain (g.dom ++ m ++ h.dom) [([], g, m ++ h.dom), (g.cod ++ m, h, [])]
      (g.cod ++ m ++ h.cod) := ⟨by simp, by simp, by simp⟩
  have H₂ : SChain (g.dom ++ m ++ h.dom) [(g.dom ++ m, h, []), ([], g, m ++ h.cod)]
      (g.cod ++ m ++ h.cod) := ⟨by simp, by simp, by simp⟩
  rw [dg_of H₁, dg_of H₂]
  exact swap_diag₀ RD k ν m g h H₁ H₂

/-- **The interchange law in normal form**: two adjacent layers whose generators `g` (left) and
`h` (right) are separated by the strands `m` can be exchanged. -/
theorem dg_swap (μ : X) (s t a m b : List (Letter I)) (g h : Shape I) :
    dg RD k μ s t [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dg RD k μ s t [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] := by
  have i₁ : SChain s [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] t ↔
      s = a ++ (g.dom ++ m ++ h.dom) ++ b ∧ t = a ++ (g.cod ++ m ++ h.cod) ++ b := by
    simp only [sChain_cons, sChain_nil, List.append_assoc, true_and]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  have i₂ : SChain s [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] t ↔
      s = a ++ (g.dom ++ m ++ h.dom) ++ b ∧ t = a ++ (g.cod ++ m ++ h.cod) ++ b := by
    simp only [sChain_cons, sChain_nil, List.append_assoc, true_and]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  by_cases hc : s = a ++ (g.dom ++ m ++ h.dom) ++ b ∧ t = a ++ (g.cod ++ m ++ h.cod) ++ b
  · obtain ⟨rfl, rfl⟩ := hc
    have E := congrArg (ctxL RD k μ (a ++ (g.dom ++ m ++ h.dom) ++ b)
      (a ++ (g.cod ++ m ++ h.cod) ++ b) [] a b [] _ _) (dg_swap₀ RD k (wt RD μ b) m g h)
    rw [ctxL_dg RD k μ (SChain.nil' _) (SChain.nil' _),
      ctxL_dg RD k μ (SChain.nil' _) (SChain.nil' _)] at E
    simpa [whL] using E
  · rw [dg_of_not (fun h' => hc (i₁.1 h')), dg_of_not (fun h' => hc (i₂.1 h'))]

/-- The interchange law in normal form, with the natural boundaries. -/
theorem dg_swap' (μ : X) (a m b : List (Letter I)) (g h : Shape I) :
    dg RD k μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dg RD k μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] :=
  dg_swap RD k μ _ _ a m b g h

/-! ## The zigzag relations in normal form -/

@[simp] theorem sh_dual_add_sh_add (l : Letter I) (ν : X) : sh RD l.dual + (sh RD l + ν) = ν := by
  rw [← add_assoc, sh_dual_add_sh, zero_add]

@[simp] theorem sh_add_sh_dual_add (l : Letter I) (ν : X) : sh RD l + (sh RD l.dual + ν) = ν := by
  rw [← add_assoc, sh_add_sh_dual, zero_add]

@[simp] theorem sh_up_dn_add (i : I) (ν : X) : sh RD (up i) + (sh RD (dn i) + ν) = ν :=
  sh_add_sh_dual_add RD (up i) ν

@[simp] theorem sh_dn_up_add (i : I) (ν : X) : sh RD (dn i) + (sh RD (up i) + ν) = ν :=
  sh_dual_add_sh_add RD (up i) ν

/-- **Zigzag relation**, first form: the cup `1 ⟶ l l*` to the left of the strand `l`, followed
by the cap `l* l ⟶ 1`, is the identity of `l`. -/
theorem dg_zigL (ν : X) (l : Letter I) :
    dg RD k ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = 𝟙 _ := by
  have H : SChain [l] [([], .cup l, [l]), ([l], .cap l, [])] [l] := ⟨rfl, rfl, rfl⟩
  let c : Col I X := ⟨l, ν⟩
  have ha : ob RD ν [l] = Pivotal.colourObj (inv RD).toColourDuality c := Obj.ext rfl rfl
  rw [dg_of H, (pres RD k).diag_eq_of_layers_eq' (mkD RD ν _ H)
    (Pivotal.zigL (inv RD).toColourDuality c) ha ha ?_, ((zigzags RD k) c).1]
  · simp
  · simp only [layers_mkD, layList_cons, layList_nil, Pivotal.zigL, Diagram.layers_leftZigzag,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
    all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, c, inv_dual])
    all_goals rfl

/-- **Zigzag relation**, second form: the cup `1 ⟶ l l*` to the right of the strand `l*`,
followed by the cap `l* l ⟶ 1`, is the identity of `l*`. -/
theorem dg_zigR (ν : X) (l : Letter I) :
    dg RD k ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] = 𝟙 _ := by
  have H : SChain [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] [l.dual] :=
    ⟨rfl, rfl, rfl⟩
  let c : Col I X := ⟨l, sh RD l.dual + ν⟩
  have ha : ob RD ν [l.dual] = Pivotal.dualObj (inv RD).toColourDuality c :=
    Obj.ext rfl (by simp [ob, c, inv_dual])
  rw [dg_of H, (pres RD k).diag_eq_of_layers_eq' (mkD RD ν _ H)
    (Pivotal.zigR (inv RD).toColourDuality c) ha ha ?_, ((zigzags RD k) c).2]
  · simp
  · simp only [layers_mkD, layList_cons, layList_nil, Pivotal.zigR, Diagram.layers_rightZigzag,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
    all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, c, inv_dual])
    all_goals rfl

theorem dg_zigL' (ν : X) (l : Letter I) :
    dg RD k ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = dg RD k ν [l] [l] [] := by
  rw [dg_zigL, dg_nil]

theorem dg_zigR' (ν : X) (l : Letter I) :
    dg RD k ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] =
      dg RD k ν [l.dual] [l.dual] [] := by
  rw [dg_zigR, dg_nil]

/-! ## Composition of placements -/

theorem whisk_congr_left {a b U U' : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b)
    (V : List (Col I X)) (h : U = U') :
    (pres RD k).whisk f U V =
      eqToHom (by rw [h]) ≫ (pres RD k).whisk f U' V ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Placement is compatible with composition. -/
theorem plcL_comp (μ : X) (u v : List (Letter I)) {s r t : List (Letter I)}
    (hsr : wt RD (wt RD μ v) r = wt RD (wt RD μ v) s) (hrt : wt RD (wt RD μ v) t = wt RD (wt RD μ v) r)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) r))
    (g : (pres RD k).obj (ob RD (wt RD μ v) r) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) :
    plcL RD k μ u v s r f ≫ plcL RD k μ u v r t g = plcL RD k μ u v s t (f ≫ g) := by
  simp only [plcL, dif_pos hsr, dif_pos hrt, dif_pos (hrt.trans hsr), plc, LinearMap.coe_mk,
    AddHom.coe_mk, Presentation.whisk_comp]
  rw [whisk_congr_left RD k g (wd RD μ v) (show ob RD (wt RD (wt RD μ v) r) u =
    ob RD (wt RD (wt RD μ v) s) u by rw [hsr])]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

/-! ## Bubbles placed next to a strand -/

theorem lin_cast {a b a' b' : Obj (psig RD)} (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    (pres RD k).lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg (pres RD k).obj ha).symm ≫ (pres RD k).lin f ≫
        eqToHom (congrArg (pres RD k).obj hb) := by
  subst ha hb; simp

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (`bubR`) is its placement. -/
theorem lin_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    (pres RD k).lin (bubR RD k lam [l] b) = plcL RD k lam [l] [] [] [] ((pres RD k).lin b) := by
  rw [bubR, lin_cast, ← LinDiagram.whisk_of_ok _ (whiskerOK_right RD lam [l]),
    ← Presentation.whisk_lin]
  simp only [plcL, dif_pos, plc, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- An endomorphism of `1_{μ + l}` placed to the left of the strand `l` (`bubL`) is its
placement. -/
theorem lin_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    (pres RD k).lin (bubL RD k μ [l] b) = plcL RD k μ [] [l] [] [] ((pres RD k).lin b) := by
  rw [bubL, lin_cast, ← LinDiagram.whisk_of_ok _ (whiskerOK_left RD μ [l]),
    ← Presentation.whisk_lin]
  simp only [plcL, plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos trivial]
  rfl

/-- An endomorphism of `1_{μ + l_X}` placed to the left of the strand `l` (rightmost region
`μ`). -/
abbrev bubLU (μ : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))) :
    End ((pres RD k).obj (ob RD μ [l])) :=
  plcL RD k μ [] [l] [] [] β

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (rightmost region `λ`). -/
abbrev bubRU (lam : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD lam []))) :
    End ((pres RD k).obj (ob RD lam [l])) :=
  plcL RD k lam [l] [] [] [] β

theorem sign_even {a b a' b' : Obj (psig RD)} (f : a ⟶ b) (g : a' ⟶ b') :
    ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) = 1 := by
  simp [Diagram.oddCount, Diagram.oddCountList, Signature.IsEven.odd_eq_false]

theorem plcL_diag_left (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) []) :
    bubLU RD k μ l ((pres RD k).diag d) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker d (ob RD (wt RD μ [l]) []) (wd RD μ [l])
        (whiskerOK_ob RD μ [] [l] [])) (ob_whisker RD μ [] [l] [] [] rfl)
        (ob_whisker RD μ [] [l] [] [] rfl)) := by
  simp only [bubLU, plcL, plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos trivial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ [] [l] []), Presentation.diag_cast]
  rfl

theorem bubLU_diag_comm (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) [])
    (e : ob RD μ [l] ⟶ ob RD μ [l]) :
    bubLU RD k μ l ((pres RD k).diag d) ≫ (pres RD k).diag e =
      (pres RD k).diag e ≫ bubLU RD k μ l ((pres RD k).diag d) := by
  rw [plcL_diag_left, ← Presentation.diag_comp, ← Presentation.diag_comp]
  have hc : (ob RD (wt RD μ [l]) []).Composable (ob RD μ [l]) :=
    ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
  have key := (pres RD k).diag_interchange_of_composable d e hc
  rw [sign_even, one_smul] at key
  have hd : Chain (ob RD (wt RD μ [l]) []) (Diagram.layers d) (ob RD (wt RD μ [l]) []) :=
    Diagram.chain d
  have he : Chain (ob RD μ [l]) (Diagram.layers e) (ob RD μ [l]) := Diagram.chain e
  have e₁ : ∀ L ∈ Diagram.layers d, L.whisker (ob RD (wt RD μ [l]) []) (wd RD μ [l]) =
      L.wr (ob RD μ [l]).word := by
    intro L hL
    have := hd.start_of_mem hL
    simp only [ob_start, wt_nil] at this
    simp only [Layer.whisker, Layer.wr, ob_start, ob_word, wd_nil, wt_nil, List.nil_append, this]
  have e₂ : ∀ L ∈ Diagram.layers e, L.wl (ob RD (wt RD μ [l]) []) = L := by
    intro L hL
    have := he.start_of_mem hL
    simp only [ob_start] at this
    simp only [Layer.wl, ob_start, ob_word, wd_nil, wt_nil, List.nil_append, ← this]
  refine ((pres RD k).diag_eq_of_layers_eq ?_).trans (key.trans
    ((pres RD k).diag_eq_of_layers_eq ?_))
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']

/-- **Bubbles to the left of a strand are central**: an endomorphism of `1_{μ + l_X}` placed to
the left of the strand `l` commutes with every endomorphism of `E_l 1_μ` (interchange law). -/
theorem bubLU_comm (μ : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD (wt RD μ [l]) [])))
    (γ : End ((pres RD k).obj (ob RD μ [l]))) :
    bubLU RD k μ l β ≫ γ = γ ≫ bubLU RD k μ l β := by
  obtain ⟨F, rfl⟩ := (pres RD k).lin_surjective β
  obtain ⟨G, rfl⟩ := (pres RD k).lin_surjective γ
  unfold bubLU
  induction F using Finsupp.induction_linear with
  | zero => simp only [Presentation.lin_zero, map_zero, Limits.zero_comp, Limits.comp_zero]
  | add F₁ F₂ h₁ h₂ =>
    rw [Presentation.lin_add, map_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
  | single d r =>
    rw [Presentation.lin_single, map_smul, Linear.smul_comp, Linear.comp_smul]
    congr 1
    induction G using Finsupp.induction_linear with
    | zero => simp only [Presentation.lin_zero, Limits.zero_comp, Limits.comp_zero]
    | add G₁ G₂ h₁ h₂ =>
      rw [Presentation.lin_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
    | single e r' =>
      rw [Presentation.lin_single, Linear.smul_comp, Linear.comp_smul]
      congr 1
      exact bubLU_diag_comm RD k μ l d e

theorem plcL_diag_right (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam []) :
    bubRU RD k lam l ((pres RD k).diag d) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker d (ob RD lam [l]) []
        (whiskerOK_ob RD lam [l] [] [])) (ob_whisker RD lam [l] [] [] [] rfl)
        (ob_whisker RD lam [l] [] [] [] rfl)) := by
  simp only [bubRU, plcL, plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos trivial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD lam [l] [] []), Presentation.diag_cast]
  rfl

theorem bubRU_diag_comm (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam [])
    (e : ob RD lam [l] ⟶ ob RD lam [l]) :
    bubRU RD k lam l ((pres RD k).diag d) ≫ (pres RD k).diag e =
      (pres RD k).diag e ≫ bubRU RD k lam l ((pres RD k).diag d) := by
  rw [plcL_diag_right, ← Presentation.diag_comp, ← Presentation.diag_comp]
  have hc : (ob RD lam [l]).Composable (ob RD lam []) := ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
  have key := (pres RD k).diag_interchange_of_composable e d hc
  rw [sign_even, one_smul] at key
  have hd : Chain (ob RD lam []) (Diagram.layers d) (ob RD lam []) := Diagram.chain d
  have he : Chain (ob RD lam [l]) (Diagram.layers e) (ob RD lam [l]) := Diagram.chain e
  have e₁ : ∀ L ∈ Diagram.layers d, L.whisker (ob RD lam [l]) [] = L.wl (ob RD lam [l]) := by
    intro L hL
    simp only [Layer.whisker, Layer.wl, List.append_nil]
  have e₂ : ∀ L ∈ Diagram.layers e, L.wr (ob RD lam []).word = L := by
    intro L hL
    simp only [Layer.wr, ob_word, wd_nil, List.append_nil]
  refine ((pres RD k).diag_eq_of_layers_eq ?_).trans (key.symm.trans
    ((pres RD k).diag_eq_of_layers_eq ?_))
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']

/-- **Bubbles to the right of a strand are central** in `END(E_l 1_λ)`. -/
theorem bubRU_comm (lam : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD lam [])))
    (γ : End ((pres RD k).obj (ob RD lam [l]))) :
    bubRU RD k lam l β ≫ γ = γ ≫ bubRU RD k lam l β := by
  obtain ⟨F, rfl⟩ := (pres RD k).lin_surjective β
  obtain ⟨G, rfl⟩ := (pres RD k).lin_surjective γ
  unfold bubRU
  induction F using Finsupp.induction_linear with
  | zero => simp only [Presentation.lin_zero, map_zero, Limits.zero_comp, Limits.comp_zero]
  | add F₁ F₂ h₁ h₂ =>
    rw [Presentation.lin_add, map_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
  | single d r =>
    rw [Presentation.lin_single, map_smul, Linear.smul_comp, Linear.comp_smul]
    congr 1
    induction G using Finsupp.induction_linear with
    | zero => simp only [Presentation.lin_zero, Limits.zero_comp, Limits.comp_zero]
    | add G₁ G₂ h₁ h₂ =>
      rw [Presentation.lin_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
    | single e r' =>
      rw [Presentation.lin_single, Linear.smul_comp, Linear.comp_smul]
      congr 1
      exact bubRU_diag_comm RD k lam l d e

theorem lin_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    (pres RD k).lin (LinDiagram.of (mkD RD μ ls h)) = dg RD k μ s t ls := (dg_of h).symm

/-! ## Proving that concrete lists of layers chain -/

/-- Closes `SChain s ls t` for explicit lists of layers, possibly containing blocks of dots
`List.replicate n x`. -/
macro "schain" : tactic => `(tactic| (
  try simp only [whL, List.map_append, List.map_cons, List.map_nil, List.map_replicate,
    List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.append_nil]
  repeat' (first
    | exact rfl
    | refine ⟨rfl, ?_⟩
    | refine (sChain_replicate_append _ _ (by rfl) _ (by rfl)).2 ?_
    | refine (sChain_replicate _ _ (by rfl) (by rfl)).2 ?_)))

theorem SChain.replicate_of {s : List (Letter I)} {x : LayerData I} (hx : SChain s [x] s)
    (n : ℕ) : SChain s (List.replicate n x) s := by
  induction n with
  | zero => rfl
  | succ n ih => exact hx.append ih

/-- Normal form of lists of layers. -/
macro "lnf" : tactic => `(tactic| simp only [whL, List.map_append, List.map_cons, List.map_nil,
  List.map_replicate, List.cons_append, List.nil_append, List.append_nil, List.singleton_append,
  List.append_assoc])

/-- `dstep pre post u v E`: one step of a certificate chain (`dg_step`), rewriting the current
diagram `dg μ s₀ t₀ L` (left-hand side of the goal) with the local equation `E` placed between
the strands `u`, `v`, with the layers `pre` below and `post` above. -/
syntax "dstep " term:max term:max term:max term:max term:max : tactic

macro_rules
  | `(tactic| dstep $pre $post $u $v $E) =>
    `(tactic| refine (dg_step _ _ _ $pre $post $u $v $E (by schain) (by schain)
      (by simp [whL, List.replicate_succ]) rfl).trans ?_)

/-- `dg` for endomorphisms, as an element of the endomorphism ring. -/
abbrev dgE (μ : X) (s : List (Letter I)) (ls : List (LayerData I)) :
    End ((pres RD k).obj (ob RD μ s)) := dg RD k μ s s ls

theorem dgE_pow_single (μ : X) (s : List (Letter I)) (x : LayerData I) (hx : SChain s [x] s)
    (n : ℕ) : (dgE RD k μ s [x]) ^ n = dgE RD k μ s (List.replicate n x) := by
  induction n with
  | zero => rw [pow_zero, List.replicate_zero, dgE, dg_nil]; rfl
  | succ n ih =>
    rw [pow_succ, ih, End.mul_def, dgE, dgE, dgE, dg_comp hx (hx.replicate_of n),
      List.replicate_succ]
    rfl

/-! ## The relations of `U` in normal form -/

/-- The layers of the sideways crossing `crossl RD i j : E_i F_j ⟶ F_j E_i`. -/
def crosslL (i j : I) : List (LayerData I) :=
  [([], .cup (dn j), [up i, dn j]), ([dn j], .cross true j i, [dn j]), ([dn j, up i], .cap (dn j), [])]

/-- The layers of the sideways crossing `crossr RD i j : F_j E_i ⟶ E_i F_j`. -/
def crossrL (i j : I) : List (LayerData I) :=
  [([dn j, up i], .cup (up j), []), ([dn j], .cross true i j, [dn j]), ([], .cap (up j), [up i, dn j])]

theorem dg_crossl (i j : I) (μ : X) :
    dg RD k μ [up i, dn j] [dn j, up i] (crosslL i j) = (pres RD k).diag (crossl RD i j μ) := by
  rw [dg_of (by schain)]; rfl

theorem dg_crossr (i j : I) (μ : X) :
    dg RD k μ [dn j, up i] [up i, dn j] (crossrL i j) = (pres RD k).diag (crossr RD i j μ) := by
  rw [dg_of (by schain)]; rfl

/-- **KL III, `eq_downup_ij-gen`, first relation** (`i ≠ j`): `crossr ∘ crossl = 1` on
`E_i F_j 1_μ`. -/
theorem dg_downupEF (i j : I) (h : i ≠ j) (μ : X) :
    dg RD k μ [up i, dn j] [up i, dn j] (crosslL i j ++ crossrL i j) =
      dg RD k μ [up i, dn j] [up i, dn j] [] := by
  rw [← dg_comp (t := [dn j, up i]) (by schain) (by schain), dg_crossl, dg_crossr, dg_nil,
    ← Presentation.diag_comp, (pres RD k).diag_eq_of_rel (.inr (.downupEF i j h μ)) rfl]
  exact (pres RD k).diag_id _

/-- **KL III, `eq_downup_ij-gen`, second relation** (`i ≠ j`): `crossl ∘ crossr = 1` on
`F_i E_j 1_μ`. -/
theorem dg_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    dg RD k μ [dn i, up j] [dn i, up j] (crossrL j i ++ crosslL j i) =
      dg RD k μ [dn i, up j] [dn i, up j] [] := by
  rw [← dg_comp (t := [up j, dn i]) (by schain) (by schain), dg_crossl, dg_crossr, dg_nil,
    ← Presentation.diag_comp, (pres RD k).diag_eq_of_rel (.inr (.downupFE i j h μ)) rfl]
  exact (pres RD k).diag_id _

/-- **KL III (3.3)**, rotation with the cup on the left: the downward dot on `F_i 1_μ` is the
upward dot rotated by the cup `1 ⟶ F E` and the cap `E F ⟶ 1`. -/
theorem dg_cycDotL (i : I) (μ : X) :
    dg RD k μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dg RD k μ [dn i] [dn i]
        [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])] := by
  rw [dg_of (by schain), dg_of (by schain)]
  exact ((pres RD k).diag_eq_of_rel (.inr (.cycDotL i μ)) rfl).symm

/-- **KL III (3.3)**, rotation with the cup on the right. -/
theorem dg_cycDotR (i : I) (μ : X) :
    dg RD k μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dg RD k μ [dn i] [dn i]
        [([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]), ([], .cap (up i), [dn i])] := by
  rw [dg_of (by schain), dg_of (by schain)]
  exact ((pres RD k).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl).symm

/-! ### The KLR relations on upward strands -/

/-- A KLR layer as a normal-form layer on upward strands. -/
def upLD (L : Layer (KLR.Diagram.sig I)) : LayerData I := (ups L.left, upShape L.gen, ups L.right)

theorem sChain_upLD {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) : SChain (ups a.word) (ls.map upLD) (ups b.word) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    refine ⟨?_, ?_⟩
    · simp [upLD, upShape_dom, ups_append]
    · have := ih hc
      simpa [upLD, upShape_cod, ups_append] using this

theorem upDiag_eq_dg (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (pres RD k).diag (upDiag RD μ d) =
      dg RD k μ (ups a.word) (ups b.word) ((Diagram.layers d).map upLD) := by
  rw [dg_of (sChain_upLD (Diagram.chain d))]
  exact (pres RD k).diag_eq_of_layers_eq (by simp [layList, upLay, upLD, List.map_map])

/-- The upward dot slide `ψ x₀ = x₁ ψ` for `c ≠ d` (KL III `eq_dot_slide_ij-gen`), in the form
"a dot on the left strand of `E_c E_d` moves up through the crossing to the right strand". -/
theorem dg_slideRNe (μ : X) (c d : I) (h : c ≠ d) :
    dg RD k μ [up c, up d] [up d, up c] [([], .dot (up c), [up d]), ([], .cross true c d, [])] =
      dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([up d], .dot (up c), [])] := by
  have key := (KLR.Diagram.pres k (KLR.klQ2 k C)).diag_eq_of_rel (.slideRNe c d h) rfl
  have key' := congrArg (upFunctor RD k μ).map key
  rw [upFunctor_diag, upFunctor_diag, upDiag_eq_dg, upDiag_eq_dg] at key'
  exact key'

/-- The upward dot slide `x₀ ψ = ψ x₁` for `c ≠ d` (KL III `eq_dot_slide_ij-gen`): a dot on the
right strand of `E_c E_d` moves up through the crossing to the left strand. -/
theorem dg_slideLNe (μ : X) (c d : I) (h : c ≠ d) :
    dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([], .dot (up d), [up c])] =
      dg RD k μ [up c, up d] [up d, up c] [([up c], .dot (up d), []), ([], .cross true c d, [])] := by
  have key := (KLR.Diagram.pres k (KLR.klQ2 k C)).diag_eq_of_rel (.slideLNe c d h) rfl
  have key' := congrArg (upFunctor RD k μ).map key
  rw [upFunctor_diag, upFunctor_diag, upDiag_eq_dg, upDiag_eq_dg] at key'
  exact key'

section EndAlg

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] [Category 𝒟] [Preadditive 𝒟]
  [Linear k 𝒟]

/-- A `k`-linear functor induces an algebra homomorphism of endomorphism algebras. -/
def functorEndAlg (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (a : 𝒞) :
    End a →ₐ[k] End (F.obj a) where
  toFun := F.map
  map_one' := F.map_id a
  map_mul' f g := F.map_comp g f
  map_zero' := F.map_zero a a
  map_add' _ _ := F.map_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [F.map_smul]
    exact congrArg (r • ·) (F.map_id a)

end EndAlg

section ncEvalAux

variable {k} {A : Type*} [Ring A] [Algebra k A]

theorem ncEval_add_aux {n : ℕ} (y : Fin n → A) (p q : MvPolynomial (Fin n) k) :
    KLR.ncEval y (p + q) = KLR.ncEval y p + KLR.ncEval y q :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem ncEval_monomial_aux {n : ℕ} (y : Fin n → A) (s : Fin n →₀ ℕ) (c : k) :
    KLR.ncEval y (MvPolynomial.monomial s c) =
      algebraMap k A c * (List.ofFn fun a => y a ^ s a).prod :=
  Finsupp.sum_single_index (by simp)

theorem ncEval_one_aux {n : ℕ} (y : Fin n → A) : KLR.ncEval y (1 : MvPolynomial (Fin n) k) = 1 := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, ncEval_monomial_aux]
  simp

theorem ncEval_X_pow_add_X_pow (y : Fin 2 → A) (p q : ℕ) :
    KLR.ncEval y (MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) k) =
      y 0 ^ p + y 1 ^ q := by
  rw [ncEval_add_aux, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    ncEval_monomial_aux, ncEval_monomial_aux]
  simp [List.ofFn_succ, Finsupp.single_apply]

end ncEvalAux

/-- **KL III `eq_r2_ij-gen`** (`c ≠ d`): the double crossing of upward strands `E_c E_d` is
`1` if `c · d = 0`, and `x_c^{d_cd} + x_d^{d_dc}` otherwise (the KL II polynomial
`Q_cd = u^{d_cd} + v^{d_dc}`). -/
theorem dg_sqNe (μ : X) (c d : I) (h : c ≠ d) :
    dg RD k μ [up c, up d] [up c, up d] [([], .cross true c d, []), ([], .cross true d c, [])] =
      if C.dot c d = 0 then dg RD k μ [up c, up d] [up c, up d] []
      else dg RD k μ [up c, up d] [up c, up d] (List.replicate (C.dij c d) ([], .dot (up c), [up d]))
        + dg RD k μ [up c, up d] [up c, up d] (List.replicate (C.dij d c) ([up c], .dot (up d), [])) := by
  have key := KLR.Diagram.sqNe_at (KLR.klQ2 k C) (u := []) (v := []) h
    (KLR.Diagram.X2 c d ≫ KLR.Diagram.X2 d c) (KLR.Diagram.D0 c d) (KLR.Diagram.D1 c d) rfl rfl rfl
  have key' := congrArg (functorEndAlg k (upFunctor RD k μ) _) key
  rw [AlgHom.map_ncEval] at key'
  simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    upFunctor_diag] at key'
  rw [upDiag_eq_dg] at key'
  refine key'.trans ?_
  have e₀ : (fun a => ((upFunctor RD k μ).map ((![(KLR.Diagram.pres k (KLR.klQ2 k C)).diag
      (KLR.Diagram.D0 c d), (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (KLR.Diagram.D1 c d)] :
        Fin 2 → _) a) : End ((pres RD k).obj (ob RD μ [up c, up d])))) =
      ![dg RD k μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])],
        dg RD k μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])]] := by
    funext a; fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, upFunctor_diag, upDiag_eq_dg]; rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
        upFunctor_diag, upDiag_eq_dg]
      rfl
  rw [e₀, KLR.klQ2]
  split_ifs
  · rw [ncEval_one_aux, dg_nil]; rfl
  · rw [ncEval_X_pow_add_X_pow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact congrArg₂ (· + ·) (dgE_pow_single RD k μ _ _ (by schain) _)
      (dgE_pow_single RD k μ _ _ (by schain) _)

/-! ### The nilHecke relations on upward strands of one colour -/

/-- **KL III `eq_nil_rels`**: `ψ² = 0` on `E_c E_c`. -/
theorem dg_sqEq (μ : X) (c : I) :
    dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .cross true c c, [])] = 0 := by
  have key := KLR.Diagram.sqEq_at (KLR.klQ2 k C) (u := []) (v := [])
    (KLR.Diagram.X2 c c ≫ KLR.Diagram.X2 c c) rfl
  have key' := congrArg (upFunctor RD k μ).map key
  rw [upFunctor_diag, Functor.map_zero, upDiag_eq_dg] at key'
  exact key'

/-- **KL III `eq_nil_dotslide`**, first form: `x₁ ψ = ψ x₂ + 1` on `E_c E_c` (bottom to top: a dot
on the left strand below the crossing equals a dot on the right strand above it, plus the
identity). -/
theorem dg_slideREq (μ : X) (c : I) :
    dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c]), ([], .cross true c c, [])] =
      dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([up c], .dot (up c), [])] +
        dg RD k μ [up c, up c] [up c, up c] [] := by
  have key := KLR.Diagram.slideREq_at (KLR.klQ2 k C) (u := []) (v := [])
    (KLR.Diagram.D0 c c ≫ KLR.Diagram.X2 c c) (KLR.Diagram.X2 c c ≫ KLR.Diagram.D1 c c) rfl rfl
  have key' := congrArg (upFunctor RD k μ).map key
  rw [Functor.map_sub, upFunctor_diag, upFunctor_diag, CategoryTheory.Functor.map_id, upDiag_eq_dg,
    upDiag_eq_dg] at key'
  rw [dg_nil]
  exact sub_eq_iff_eq_add'.mp key'

/-- **KL III `eq_nil_dotslide`**, second form: `ψ x₁ = x₂ ψ + 1` on `E_c E_c` (a dot on the
left strand above the crossing equals a dot on the right strand below it, plus the identity). -/
theorem dg_slideLEq (μ : X) (c : I) :
    dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .dot (up c), [up c])] =
      dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), []), ([], .cross true c c, [])] +
        dg RD k μ [up c, up c] [up c, up c] [] := by
  have key := KLR.Diagram.slideLEq_at (KLR.klQ2 k C) (u := []) (v := [])
    (KLR.Diagram.X2 c c ≫ KLR.Diagram.D0 c c) (KLR.Diagram.D1 c c ≫ KLR.Diagram.X2 c c) rfl rfl
  have key' := congrArg (upFunctor RD k μ).map key
  rw [Functor.map_sub, upFunctor_diag, upFunctor_diag, CategoryTheory.Functor.map_id, upDiag_eq_dg,
    upDiag_eq_dg] at key'
  rw [dg_nil]
  exact sub_eq_iff_eq_add'.mp key'

/-! ### Bubbles -/

/-- The layers of the counterclockwise bubble with `m` dots (`ccwReal`). -/
def ccwLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), []) ++ [([], .cap (up i), [])]

/-- The layers of the clockwise bubble with `m` dots (`cwReal`). -/
def cwLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]

theorem sChain_ccwLs (i : I) (m : ℕ) : SChain [] (ccwLs i m) [] := by
  unfold ccwLs; schain

theorem sChain_cwLs (i : I) (m : ℕ) : SChain [] (cwLs i m) [] := by
  unfold cwLs; schain

theorem lin_ccwReal (ν : X) (i : I) (m : ℕ) :
    (pres RD k).lin (LinDiagram.of (ccwReal RD ν i m)) = dg RD k ν [] [] (ccwLs i m) := by
  rw [ccwReal, lin_of_mkD]; rfl

theorem lin_cwReal (ν : X) (i : I) (m : ℕ) :
    (pres RD k).lin (LinDiagram.of (cwReal RD ν i m)) = dg RD k ν [] [] (cwLs i m) := by
  rw [cwReal, lin_of_mkD]; rfl

/-- **KL III (3.4)**, counterclockwise. -/
theorem dg_ccwNeg (ν : X) (i : I) (α : ℕ) (h : (α : ℤ) < -ip RD i ν - 1) :
    dg RD k ν [] [] (ccwLs i α) = 0 := by
  rw [← lin_ccwReal]; exact (pres RD k).lin_rel_self (.inr (.ccwNeg i ν α h))

/-- **KL III (3.4)**, clockwise. -/
theorem dg_cwNeg (ν : X) (i : I) (α : ℕ) (h : (α : ℤ) < ip RD i ν - 1) :
    dg RD k ν [] [] (cwLs i α) = 0 := by
  rw [← lin_cwReal]; exact (pres RD k).lin_rel_self (.inr (.cwNeg i ν α h))

/-- The degree-zero counterclockwise bubble is `1` (`⟨i,ν⟩ ≤ -1`). -/
theorem dg_ccwOne (ν : X) (i : I) (h : ip RD i ν ≤ -1) :
    dg RD k ν [] [] (ccwLs i (-ip RD i ν - 1).toNat) = dg RD k ν [] [] [] := by
  rw [← lin_ccwReal, dg_nil]
  exact ((pres RD k).diag_eq_of_rel (.inr (.ccwOne i ν h)) rfl).trans ((pres RD k).diag_id _)

/-- The degree-zero clockwise bubble is `1` (`⟨i,ν⟩ ≥ 1`). -/
theorem dg_cwOne (ν : X) (i : I) (h : 1 ≤ ip RD i ν) :
    dg RD k ν [] [] (cwLs i (ip RD i ν - 1).toNat) = dg RD k ν [] [] [] := by
  rw [← lin_cwReal, dg_nil]
  exact ((pres RD k).diag_eq_of_rel (.inr (.cwOne i ν h)) rfl).trans ((pres RD k).diag_id _)

/-! ### Dots, fake bubbles, curls and the decompositions -/

/-- `n` dots on the strand `l` with rightmost region `λ`, as a 2-morphism of `U`
(the class of `dots RD λ [] l [] n`, see `dotsU_eq`). -/
abbrev dotsU (lam : X) (l : Letter I) (n : ℕ) :
    End ((pres RD k).obj (ob RD lam [l])) :=
  dg RD k lam [l] [l] (List.replicate n ([], .dot l, []))

theorem dotsU_eq (lam : X) (l : Letter I) (n : ℕ) :
    (pres RD k).diag (dots RD lam [] l [] n) = dotsU RD k lam l n :=
  (dg_of _).symm

theorem dotsU_add (lam : X) (l : Letter I) (p q : ℕ) :
    dotsU RD k lam l p ≫ dotsU RD k lam l q = dotsU RD k lam l (p + q) := by
  rw [dotsU, dotsU, dotsU, dg_comp (by schain) (by schain), List.replicate_add]

theorem dotsU_zero (lam : X) (l : Letter I) : dotsU RD k lam l 0 = 𝟙 _ := by
  rw [dotsU, List.replicate_zero, dg_nil]

/-- The counterclockwise bubble with label `m ∈ ℤ` (real, fake or zero; `ccwL`) in `U`. -/
abbrev ccwU (ν : X) (i : I) (m : ℤ) : End ((pres RD k).obj (ob RD ν [])) :=
  (pres RD k).lin (ccwL RD k ν i m)

/-- The clockwise bubble with label `m ∈ ℤ` (real, fake or zero; `cwL`) in `U`. -/
abbrev cwU (ν : X) (i : I) (m : ℤ) : End ((pres RD k).obj (ob RD ν [])) :=
  (pres RD k).lin (cwL RD k ν i m)

theorem ccwU_of_nonneg (ν : X) (i : I) (m : ℕ) :
    ccwU RD k ν i m = dg RD k ν [] [] (ccwLs i m) := by
  rw [ccwU, ccwL, if_pos (Int.natCast_nonneg m), Int.toNat_natCast, lin_ccwReal]

theorem cwU_of_nonneg (ν : X) (i : I) (m : ℕ) :
    cwU RD k ν i m = dg RD k ν [] [] (cwLs i m) := by
  rw [cwU, cwL, if_pos (Int.natCast_nonneg m), Int.toNat_natCast, lin_cwReal]

theorem lin_finsum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    (pres RD k).lin (∑ x ∈ s, f x) = ∑ x ∈ s, (pres RD k).lin (f x) :=
  map_sum (Presentation.linFunctor (pres RD k)).mapAddHom f s

/-- **KL III, curl relation (item iv), left curl)**, in normal form: an upward strand `E_i` with
a curl on its left (outer region `λ = μ + i_X`, `n = ⟨i, λ⟩`) equals
`∑_{g=0}^{n} ccw_{-n-1+g} x^{n-g}`, the bubbles to the left of the strand. -/
theorem dg_curlL (i : I) (μ : X) :
    dg RD k μ [up i] [up i]
        [([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])] =
      ∑ g ∈ Finset.range (ip RD i (wt RD μ [up i]) + 1).toNat,
        bubLU RD k μ (up i) (ccwU RD k (wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)) ≫
          dotsU RD k μ (up i) (ip RD i (wt RD μ [up i]) - g).toNat := by
  have key : (pres RD k).lin (relation (RD := RD) k (.curlL i μ)) = 0 :=
    (pres RD k).lin_rel_self (.inr (.curlL i μ))
  simp only [relation, Presentation.lin_sub, Presentation.lin_of,
    sub_eq_zero] at key
  rw [dg_of (by schain)]
  refine key.trans ?_
  rw [curlLHS, lin_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, lin_bubL, Presentation.lin_of, dotsU_eq]

/-- **KL III, curl relation (item iv), right curl)**, in normal form: an upward strand `E_i`
with a curl on its right (outer region `λ`, `n = ⟨i, λ⟩`) equals
`-∑_{f=0}^{-n} x^{-n-f} cw_{n-1+f}`, the bubbles to the right of the strand. -/
theorem dg_curlR (i : I) (lam : X) :
    dg RD k lam [up i] [up i]
        [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] =
      -∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
        bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + f)) ≫
          dotsU RD k lam (up i) (-ip RD i lam - f).toNat := by
  have key : (pres RD k).lin (relation (RD := RD) k (.curlR i lam)) = 0 :=
    (pres RD k).lin_rel_self (.inr (.curlR i lam))
  simp only [relation, Presentation.lin_sub, Presentation.lin_of,
    sub_eq_zero] at key
  rw [dg_of (by schain)]
  refine key.trans ?_
  rw [curlRHS, Presentation.lin_neg, lin_finsum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Presentation.lin_comp, lin_bubR, Presentation.lin_of, dotsU_eq]

/-- The layers of `dotCapEF`. -/
def dotCapEFLs (i : I) (m : ℕ) : List (LayerData I) :=
  List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]

/-- The layers of `cupDotEF`. -/
def cupDotEFLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), [])

/-- The layers of `dotCapFE`. -/
def dotCapFELs (i : I) (m : ℕ) : List (LayerData I) :=
  List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]

/-- The layers of `cupDotFE`. -/
def cupDotFELs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), [])

/-- **KL III `eq_ident_decomp`, first identity**, in normal form (`n = ⟨i, λ⟩`):
`1_{E F 1_λ} = -crossr ∘ crossl + ∑_{f=0}^{n-1} ∑_{g=0}^{f}` (cap with `f-g` dots)
`ccw_{-n-1+g}` (cup with `n-1-f` dots). -/
theorem dg_decompEF (i : I) (lam : X) :
    dg RD k lam [up i, dn i] [up i, dn i] [] =
      -dg RD k lam [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) +
        ∑ f ∈ Finset.range (ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          dg RD k lam [up i, dn i] [] (dotCapEFLs i (f - g)) ≫ ccwU RD k lam i (-ip RD i lam - 1 + g) ≫
            dg RD k lam [] [up i, dn i] (cupDotEFLs i ((ip RD i lam).toNat - 1 - f)) := by
  have key : (pres RD k).lin (relation (RD := RD) k (.decompEF i lam)) = 0 :=
    (pres RD k).lin_rel_self (.inr (.decompEF i lam))
  simp only [relation, Presentation.lin_sub, Presentation.lin_add,
    Presentation.lin_of, sub_eq_zero] at key
  rw [dg_nil, ← dg_comp (t := [dn i, up i]) (by schain) (by schain), dg_crossl, dg_crossr,
    ← Presentation.diag_comp, eq_neg_add_iff_add_eq, ← Presentation.diag_id, add_comm, key,
    decompEFSum,
    lin_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [lin_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of,
    dotCapEF, cupDotEF, ← lin_of_mkD, ← lin_of_mkD]
  rfl

/-- **KL III `eq_ident_decomp`, second identity**, in normal form (`n = ⟨i, λ⟩`):
`1_{F E 1_λ} = -crossl ∘ crossr + ∑_{f=0}^{-n-1} ∑_{g=0}^{f}` (cap with `f-g` dots)
`cw_{n-1+g}` (cup with `-n-1-f` dots). -/
theorem dg_decompFE (i : I) (lam : X) :
    dg RD k lam [dn i, up i] [dn i, up i] [] =
      -dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) +
        ∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          dg RD k lam [dn i, up i] [] (dotCapFELs i (f - g)) ≫ cwU RD k lam i (ip RD i lam - 1 + g) ≫
            dg RD k lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - f)) := by
  have key : (pres RD k).lin (relation (RD := RD) k (.decompFE i lam)) = 0 :=
    (pres RD k).lin_rel_self (.inr (.decompFE i lam))
  simp only [relation, Presentation.lin_sub, Presentation.lin_add,
    Presentation.lin_of, sub_eq_zero] at key
  rw [dg_nil, ← dg_comp (t := [up i, dn i]) (by schain) (by schain), dg_crossl, dg_crossr,
    ← Presentation.diag_comp, eq_neg_add_iff_add_eq, ← Presentation.diag_id, add_comm, key,
    decompFESum,
    lin_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [lin_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of,
    dotCapFE, cupDotFE, ← lin_of_mkD, ← lin_of_mkD]
  rfl

-- `schain` also unfolds the named lists of layers of this file.
macro_rules
  | `(tactic| schain) => `(tactic| (
      simp only [dotCapEFLs, cupDotEFLs, dotCapFELs, cupDotFELs, ccwLs, cwLs]
      schain))

end Categorification.KL3.Diagram
