/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Layers

/-!
# Normal-form diagrams in any presentation on the signature of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.

The local rewriting calculus of normal-form diagrams (lists of layers `(u, g, v)`, see
`Categorification.Diagrams.KL3.Basic`) uses only the interchange law and, for the moves through
cups and caps, the zigzag relations (KL III (3.1), (3.2)). It is developed here once for an
arbitrary presentation `P` on the signature `psig RD` of `U` (with `HasZigzags P` where the
zigzag relations are used), and specialized to KL III's `U`
(`Categorification.Diagrams.KL3.SlideCalculus`, `pres RD k`) and to `U_Q(g)` with Cautis–Lauda
scalars (`Categorification.Diagrams.CLQ`, `CLQ.pres RD k sc`).

## Main definitions and results

* `plc`, `plcL`: placement of a 2-morphism between strands `u` and `v`; `ctx`, `ctxL`:
  rewriting in context; `dg P μ s t ls`: the class of a normal-form diagram (`0` if the layers
  do not chain).
* `dg_comp`, `dg_nil`, `ctxL_dg`, `dg_step`, `dg_stepL` and the tactic `dstepQ`: certificate
  chains of local moves.
* `dg_swap`, `dg_swap'`: the interchange law; `dg_zigL'`, `dg_zigR'`: the zigzag relations.
* `dg_swapLR_at`, `dg_swapRL_at`, `dg_step_at` and the tactics `dswapQ`, `datQ`: positional
  rewriting; `dg_interchange`: the interchange law for blocks of layers.
* `bubLU`, `bubRU`, `bubLU_comm`, `bubRU_comm`: endomorphisms of `1` placed next to a strand,
  and their centrality; `dotsU`, `ccwU`, `cwU`.
* `dg_swap_rep`, `dg_swap_dots`: blocks of dots commute with generators on other strands;
  `dg_pull_ccw`, `dg_pull_cw`: pulling a strand through a bubble (KL III's proof of
  Proposition 3.3).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.NF

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w r u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] (P : Presentation.{w, r} (psig RD) k)

/-- The zigzag relations (KL III (3.1), (3.2)) hold in the presentation `P`. -/
class HasZigzags : Prop where
  zigzags : P.PivotalZigzags (inv RD).toColourDuality

/-- **Placement.** The `k`-linear map placing a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`, with
`ν = μ + v_X`, between the strands `u` and `v`; the rightmost region becomes `μ`. -/
def plc (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ (u ++ s ++ v)) ⟶ P.obj (ob RD μ (u ++ t ++ v))) where
  toFun f := eqToHom (congrArg P.obj (ob_whisker RD μ u v s s rfl).symm) ≫
    P.whisk f (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) ≫
      eqToHom (congrArg P.obj (ob_whisker RD μ u v s t hst))
  map_add' f g := by
    rw [Presentation.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [Presentation.whisk_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Placement acts on normal-form diagrams by placing every layer. -/
theorem plc_diag (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) (ls : List (LayerData I))
    (h : SChain s ls t) :
    plc P μ u v hst (P.diag (mkD RD (wt RD μ v) ls h)) =
      P.diag (mkD RD μ (ls.map (whL u v)) (h.whisk u v)) := by
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ u v s)]
  rw [P.diag_eq_of_layers_eq' (mkD RD μ (ls.map (whL u v)) (h.whisk u v))
    (Diagram.whisker (mkD RD (wt RD μ v) ls h) (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)
      (whiskerOK_ob RD μ u v s)) (ob_whisker RD μ u v s s rfl).symm
      (ob_whisker RD μ u v s t hst).symm ?_]
  rw [Diagram.layers_whisker, layers_mkD, layers_mkD, layList_whisker RD μ u v h]

/-- **Rewriting in context.** Place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + v_X`) between
the strands `u` and `v`, and compose with the normal-form diagrams `pre` below and `post`
above. -/
def ctx (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ s₀) ⟶ P.obj (ob RD μ t₀)) where
  toFun f := P.diag (mkD RD μ pre hpre) ≫ plc P μ u v hst f ≫
    P.diag (mkD RD μ post hpost)
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ctx_apply (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    ctx P μ pre u v post hpre hpost hst f =
      P.diag (mkD RD μ pre hpre) ≫ plc P μ u v hst f ≫
        P.diag (mkD RD μ post hpost) := rfl

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctx_diag (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (ls : List (LayerData I)) (h : SChain s ls t) :
    ctx P μ pre u v post hpre hpost hst (P.diag (mkD RD (wt RD μ v) ls h)) =
      P.diag (mkD RD μ (pre ++ ls.map (whL u v) ++ post)
        ((hpre.append (h.whisk u v)).append hpost)) := by
  rw [ctx_apply, plc_diag, ← Presentation.diag_comp, ← Presentation.diag_comp, mkD_comp, mkD_comp]
  exact P.diag_eq_of_layers_eq (by simp)

open Classical in
/-- The class in `U` of the normal-form diagram with layers `ls` from `E_s 1_μ` to `E_t 1_μ`
(rightmost region `μ`), or `0` if the layers do not form such a diagram. -/
def dg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    P.obj (ob RD μ s) ⟶ P.obj (ob RD μ t) :=
  if h : SChain s ls t then P.diag (mkD RD μ ls h) else 0

section Dg

variable {P}

theorem dg_of {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    dg P μ s t ls = P.diag (mkD RD μ ls h) := dite_eq_left h

theorem dg_of_not {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : ¬ SChain s ls t) : dg P μ s t ls = 0 := dite_eq_right h

theorem dg_nil (μ : X) (s : List (Letter I)) : dg P μ s s [] = 𝟙 _ := by
  rw [dg_of (show SChain s [] s from rfl)]
  exact (P.diag_eq_of_layers_eq rfl).trans (P.diag_id _)

theorem dg_comp {μ : X} {s t r : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A t)
    (hB : SChain t B r) : dg P μ s t A ≫ dg P μ t r B = dg P μ s r (A ++ B) := by
  rw [dg_of hA, dg_of hB, dg_of (hA.append hB), ← Presentation.diag_comp, mkD_comp]

end Dg

open Classical in
/-- Placement between the strands `u` and `v`, as a `k`-linear map on all morphisms
`E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + v_X`); it is `0` if `s` and `t` have different weights. -/
def plcL (μ : X) (u v s t : List (Letter I)) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ (u ++ s ++ v)) ⟶ P.obj (ob RD μ (u ++ t ++ v))) :=
  if h : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s then plc P μ u v h else 0

theorem plcL_dg (μ : X) (u v s t : List (Letter I)) (A : List (LayerData I)) :
    plcL P μ u v s t (dg P (wt RD μ v) s t A) =
      dg P μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) := by
  by_cases hA : SChain s A t
  · rw [plcL, dite_eq_left (hA.wt_eq RD _), dg_of hA, plc_diag, dg_of]
  · rw [dg_of_not hA, map_zero, dg_of_not (fun h => hA h.of_whisk)]

/-- `plcL_dg` for an empty right context. -/
theorem plcL_dg_nil (μ : X) (u s t : List (Letter I)) (A : List (LayerData I)) :
    plcL P μ u [] s t (dg P μ s t A) = dg P μ (u ++ s ++ []) (u ++ t ++ []) (A.map (whL u [])) :=
  plcL_dg P μ u [] s t A

/-- **Rewriting in context**, as a `k`-linear map: place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`
(`ν = μ + v_X`) between the strands `u` and `v` and compose with the normal-form diagrams
`pre` below and `post` above. -/
def ctxL (μ : X) (s₀ t₀ : List (Letter I)) (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (s t : List (Letter I)) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ s₀) ⟶ P.obj (ob RD μ t₀)) where
  toFun f := dg P μ s₀ (u ++ s ++ v) pre ≫ plcL P μ u v s t f ≫
    dg P μ (u ++ t ++ v) t₀ post
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctxL_dg (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (A : List (LayerData I)) :
    ctxL P μ s₀ t₀ pre u v post s t (dg P (wt RD μ v) s t A) =
      dg P μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) := by
  show dg P μ s₀ (u ++ s ++ v) pre ≫ plcL P μ u v s t _ ≫ dg P μ (u ++ t ++ v) t₀ post = _
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
    ctxL P μ s₀ t₀ pre u [] post s t (dg P μ s t A) =
      dg P μ s₀ t₀ (pre ++ A.map (whL u []) ++ post) :=
  ctxL_dg P μ hpre hpost A

/-- **The rewriting principle.** If `dg ν s t A = F` (`ν = μ + v_X`), then the diagram
`pre ++ A ++ post`, with `A` placed between the strands `u` and `v`, equals the image of `F`
under `ctxL`. -/
theorem dg_rw (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    {A : List (LayerData I)} {F : P.obj (ob RD (wt RD μ v) s) ⟶
      P.obj (ob RD (wt RD μ v) t)} (E : dg P (wt RD μ v) s t A = F) :
    dg P μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) = ctxL P μ s₀ t₀ pre u v post s t F := by
  rw [← E, ctxL_dg P μ hpre hpost]

/-- **One step of a certificate chain.** If `dg ν s t A = dg ν s t B` (`ν = μ + v_X`), then
in any diagram in which `A` occurs between the strands `u` and `v` (below it the layers `pre`,
above it the layers `post`), `A` may be replaced by `B`. -/
theorem dg_step (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B L L' : List (LayerData I)}
    (E : dg P (wt RD μ v) s t A = dg P (wt RD μ v) s t B)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    dg P μ s₀ t₀ L = dg P μ s₀ t₀ L' := by
  rw [hL, hL', dg_rw P μ hpre hpost E, ctxL_dg P μ hpre hpost]

/-- One step of a certificate chain whose right-hand side is a linear combination: the image of
the right-hand side under `ctxL`. -/
theorem dg_stepL (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A L : List (LayerData I)}
    {F : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)}
    (E : dg P (wt RD μ v) s t A = F)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) :
    dg P μ s₀ t₀ L = ctxL P μ s₀ t₀ pre u v post s t F := by
  rw [hL, dg_rw P μ hpre hpost E]

/-- The interchange law for two adjacent layers with empty outer context: the generator `g`
on the left, the strands `m`, the generator `h` on the right. -/
theorem swap_diag₀ (ν : X) (m : List (Letter I)) (g h : Shape I) {s t : List (Letter I)}
    (H₁ : SChain s [([], g, m ++ h.dom), (g.cod ++ m, h, [])] t)
    (H₂ : SChain s [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] t) :
    P.diag (mkD RD ν _ H₁) = P.diag (mkD RD ν _ H₂) := by
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
  have key := P.diag_interchange x hx (Obj.nil x.start) [] hw rfl rfl
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
  rw [P.diag_eq_of_layers_eq' (mkD RD ν _ _) (Diagram.cast
      (Diagram.whisker (InterchangeData.ghDiagram hx) (Obj.nil x.start) [] hw) rfl rfl) ha hb ?_,
    P.diag_eq_of_layers_eq' (mkD RD ν _ H₂) (Diagram.cast
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
    dg P ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [([], g, m ++ h.dom), (g.cod ++ m, h, [])] =
      dg P ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] := by
  have H₁ : SChain (g.dom ++ m ++ h.dom) [([], g, m ++ h.dom), (g.cod ++ m, h, [])]
      (g.cod ++ m ++ h.cod) := ⟨by simp, by simp, by simp⟩
  have H₂ : SChain (g.dom ++ m ++ h.dom) [(g.dom ++ m, h, []), ([], g, m ++ h.cod)]
      (g.cod ++ m ++ h.cod) := ⟨by simp, by simp, by simp⟩
  rw [dg_of H₁, dg_of H₂]
  exact swap_diag₀ P ν m g h H₁ H₂

/-- **The interchange law in normal form**: two adjacent layers whose generators `g` (left) and
`h` (right) are separated by the strands `m` can be exchanged. -/
theorem dg_swap (μ : X) (s t a m b : List (Letter I)) (g h : Shape I) :
    dg P μ s t [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dg P μ s t [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] := by
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
    have E := congrArg (ctxL P μ (a ++ (g.dom ++ m ++ h.dom) ++ b)
      (a ++ (g.cod ++ m ++ h.cod) ++ b) [] a b [] _ _) (dg_swap₀ P (wt RD μ b) m g h)
    rw [ctxL_dg P μ (SChain.nil' _) (SChain.nil' _),
      ctxL_dg P μ (SChain.nil' _) (SChain.nil' _)] at E
    simpa [whL] using E
  · rw [dg_of_not (fun h' => hc (i₁.1 h')), dg_of_not (fun h' => hc (i₂.1 h'))]

/-- The interchange law in normal form, with the natural boundaries. -/
theorem dg_swap' (μ : X) (a m b : List (Letter I)) (g h : Shape I) :
    dg P μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dg P μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] :=
  dg_swap P μ _ _ a m b g h

/-! ## The zigzag relations in normal form -/

section Zigzag

variable [HasZigzags P]

/-- **Zigzag relation**, first form: the cup `1 ⟶ l l*` to the left of the strand `l`, followed
by the cap `l* l ⟶ 1`, is the identity of `l`. -/
theorem dg_zigL (ν : X) (l : Letter I) :
    dg P ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = 𝟙 _ := by
  have H : SChain [l] [([], .cup l, [l]), ([l], .cap l, [])] [l] := ⟨rfl, rfl, rfl⟩
  let c : Col I X := ⟨l, ν⟩
  have ha : ob RD ν [l] = Pivotal.colourObj (inv RD).toColourDuality c := Obj.ext rfl rfl
  rw [dg_of H, P.diag_eq_of_layers_eq' (mkD RD ν _ H)
    (Pivotal.zigL (inv RD).toColourDuality c) ha ha ?_, (HasZigzags.zigzags (P := P) c).1]
  · simp
  · simp only [layers_mkD, layList_cons, layList_nil, Pivotal.zigL, Diagram.layers_leftZigzag,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
    all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, c])
    all_goals rfl

/-- **Zigzag relation**, second form: the cup `1 ⟶ l l*` to the right of the strand `l*`,
followed by the cap `l* l ⟶ 1`, is the identity of `l*`. -/
theorem dg_zigR (ν : X) (l : Letter I) :
    dg P ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] = 𝟙 _ := by
  have H : SChain [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] [l.dual] :=
    ⟨rfl, rfl, rfl⟩
  let c : Col I X := ⟨l, sh RD l.dual + ν⟩
  have ha : ob RD ν [l.dual] = Pivotal.dualObj (inv RD).toColourDuality c :=
    Obj.ext rfl (by simp [ob, c, inv_dual])
  rw [dg_of H, P.diag_eq_of_layers_eq' (mkD RD ν _ H)
    (Pivotal.zigR (inv RD).toColourDuality c) ha ha ?_, (HasZigzags.zigzags (P := P) c).2]
  · simp
  · simp only [layers_mkD, layList_cons, layList_nil, Pivotal.zigR, Diagram.layers_rightZigzag,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
    all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, c, inv_dual])
    all_goals rfl

theorem dg_zigL' (ν : X) (l : Letter I) :
    dg P ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = dg P ν [l] [l] [] := by
  rw [dg_zigL, dg_nil]

theorem dg_zigR' (ν : X) (l : Letter I) :
    dg P ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] =
      dg P ν [l.dual] [l.dual] [] := by
  rw [dg_zigR, dg_nil]

end Zigzag

theorem whisk_congr_left {a b U U' : Obj (psig RD)} (f : P.obj a ⟶ P.obj b)
    (V : List (Col I X)) (h : U = U') :
    P.whisk f U V =
      eqToHom (by rw [h]) ≫ P.whisk f U' V ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Placement is compatible with composition. -/
theorem plcL_comp (μ : X) (u v : List (Letter I)) {s r t : List (Letter I)}
    (hsr : wt RD (wt RD μ v) r = wt RD (wt RD μ v) s) (hrt : wt RD (wt RD μ v) t = wt RD (wt RD μ v) r)
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) r))
    (g : P.obj (ob RD (wt RD μ v) r) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    plcL P μ u v s r f ≫ plcL P μ u v r t g = plcL P μ u v s t (f ≫ g) := by
  simp only [plcL, dite_eq_left hsr, dite_eq_left hrt, dite_eq_left (hrt.trans hsr), plc, LinearMap.coe_mk,
    AddHom.coe_mk, Presentation.whisk_comp]
  rw [whisk_congr_left P g (wd RD μ v) (show ob RD (wt RD (wt RD μ v) r) u =
    ob RD (wt RD (wt RD μ v) s) u by rw [hsr])]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

theorem lin_cast {a b a' b' : Obj (psig RD)} (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    P.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha).symm ≫ P.lin f ≫
        eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (`bubR`) is its placement. -/
theorem lin_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    P.lin (bubR RD k lam [l] b) = plcL P lam [l] [] [] [] (P.lin b) := by
  rw [bubR, lin_cast, ← LinDiagram.whisk_of_ok _ (whiskerOK_right RD lam [l]),
    ← Presentation.whisk_lin]
  simp only [plcL, dite_eq_left, plc, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- An endomorphism of `1_{μ + l}` placed to the left of the strand `l` (`bubL`) is its
placement. -/
theorem lin_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    P.lin (bubL RD k μ [l] b) = plcL P μ [] [l] [] [] (P.lin b) := by
  rw [bubL, lin_cast, ← LinDiagram.whisk_of_ok _ (whiskerOK_left RD μ [l]),
    ← Presentation.whisk_lin]
  simp only [plcL, plc]
  rw [dite_eq_left trivial]
  rfl

/-- An endomorphism of `1_{μ + l_X}` placed to the left of the strand `l` (rightmost region
`μ`). -/
abbrev bubLU (μ : X) (l : Letter I) (β : End (P.obj (ob RD (wt RD μ [l]) []))) :
    End (P.obj (ob RD μ [l])) :=
  plcL P μ [] [l] [] [] β

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (rightmost region `λ`). -/
abbrev bubRU (lam : X) (l : Letter I) (β : End (P.obj (ob RD lam []))) :
    End (P.obj (ob RD lam [l])) :=
  plcL P lam [l] [] [] [] β

theorem plcL_diag_left (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) []) :
    bubLU P μ l (P.diag d) =
      P.diag (Diagram.cast (Diagram.whisker d (ob RD (wt RD μ [l]) []) (wd RD μ [l])
        (whiskerOK_ob RD μ [] [l] [])) (ob_whisker RD μ [] [l] [] [] rfl)
        (ob_whisker RD μ [] [l] [] [] rfl)) := by
  simp only [bubLU, plcL, plc]
  rw [dite_eq_left trivial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ [] [l] []), Presentation.diag_cast]
  rfl

theorem bubLU_diag_comm (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) [])
    (e : ob RD μ [l] ⟶ ob RD μ [l]) :
    bubLU P μ l (P.diag d) ≫ P.diag e =
      P.diag e ≫ bubLU P μ l (P.diag d) := by
  rw [plcL_diag_left, ← Presentation.diag_comp, ← Presentation.diag_comp]
  have hc : (ob RD (wt RD μ [l]) []).Composable (ob RD μ [l]) :=
    ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
  have key := P.diag_interchange_of_composable d e hc
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
  refine (P.diag_eq_of_layers_eq ?_).trans (key.trans
    (P.diag_eq_of_layers_eq ?_))
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']

/-- **Bubbles to the left of a strand are central**: an endomorphism of `1_{μ + l_X}` placed to
the left of the strand `l` commutes with every endomorphism of `E_l 1_μ` (interchange law). -/
theorem bubLU_comm (μ : X) (l : Letter I) (β : End (P.obj (ob RD (wt RD μ [l]) [])))
    (γ : End (P.obj (ob RD μ [l]))) :
    bubLU P μ l β ≫ γ = γ ≫ bubLU P μ l β := by
  obtain ⟨F, rfl⟩ := P.lin_surjective β
  obtain ⟨G, rfl⟩ := P.lin_surjective γ
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
      exact bubLU_diag_comm P μ l d e

theorem plcL_diag_right (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam []) :
    bubRU P lam l (P.diag d) =
      P.diag (Diagram.cast (Diagram.whisker d (ob RD lam [l]) []
        (whiskerOK_ob RD lam [l] [] [])) (ob_whisker RD lam [l] [] [] [] rfl)
        (ob_whisker RD lam [l] [] [] [] rfl)) := by
  simp only [bubRU, plcL, plc]
  rw [dite_eq_left trivial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD lam [l] [] []), Presentation.diag_cast]
  rfl

theorem bubRU_diag_comm (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam [])
    (e : ob RD lam [l] ⟶ ob RD lam [l]) :
    bubRU P lam l (P.diag d) ≫ P.diag e =
      P.diag e ≫ bubRU P lam l (P.diag d) := by
  rw [plcL_diag_right, ← Presentation.diag_comp, ← Presentation.diag_comp]
  have hc : (ob RD lam [l]).Composable (ob RD lam []) := ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
  have key := P.diag_interchange_of_composable e d hc
  rw [sign_even, one_smul] at key
  have hd : Chain (ob RD lam []) (Diagram.layers d) (ob RD lam []) := Diagram.chain d
  have he : Chain (ob RD lam [l]) (Diagram.layers e) (ob RD lam [l]) := Diagram.chain e
  have e₁ : ∀ L ∈ Diagram.layers d, L.whisker (ob RD lam [l]) [] = L.wl (ob RD lam [l]) := by
    intro L hL
    simp only [Layer.whisker, Layer.wl, List.append_nil]
  have e₂ : ∀ L ∈ Diagram.layers e, L.wr (ob RD lam []).word = L := by
    intro L hL
    simp only [Layer.wr, ob_word, wd_nil, List.append_nil]
  refine (P.diag_eq_of_layers_eq ?_).trans (key.symm.trans
    (P.diag_eq_of_layers_eq ?_))
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']
  · simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_whisker,
      Diagram.layers_rwhisker, Diagram.layers_lwhisker, List.map_congr_left e₁,
      List.map_congr_left e₂, List.map_id']

/-- **Bubbles to the right of a strand are central** in `END(E_l 1_λ)`. -/
theorem bubRU_comm (lam : X) (l : Letter I) (β : End (P.obj (ob RD lam [])))
    (γ : End (P.obj (ob RD lam [l]))) :
    bubRU P lam l β ≫ γ = γ ≫ bubRU P lam l β := by
  obtain ⟨F, rfl⟩ := P.lin_surjective β
  obtain ⟨G, rfl⟩ := P.lin_surjective γ
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
      exact bubRU_diag_comm P lam l d e

theorem lin_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    P.lin (LinDiagram.of (mkD RD μ ls h)) = dg P μ s t ls := (dg_of h).symm

/-- `dstepQ pre post u v E`: one step of a certificate chain (`dg_step`), rewriting the current
diagram `dg μ s₀ t₀ L` (left-hand side of the goal) with the local equation `E` placed between
the strands `u`, `v`, with the layers `pre` below and `post` above. -/
syntax "dstepQ " term:max term:max term:max term:max term:max : tactic

macro_rules
  | `(tactic| dstepQ $pre $post $u $v $E) =>
    `(tactic| refine (dg_step _ _ $pre $post $u $v $E (by schain) (by schain)
      (by simp [whL, List.replicate_succ]) rfl).trans ?_)

/-- `dg` for endomorphisms, as an element of the endomorphism ring. -/
abbrev dgE (μ : X) (s : List (Letter I)) (ls : List (LayerData I)) :
    End (P.obj (ob RD μ s)) := dg P μ s s ls

theorem dgE_pow_single (μ : X) (s : List (Letter I)) (x : LayerData I) (hx : SChain s [x] s)
    (n : ℕ) : (dgE P μ s [x]) ^ n = dgE P μ s (List.replicate n x) := by
  induction n with
  | zero => rw [pow_zero, List.replicate_zero, dgE, dg_nil]; rfl
  | succ n ih =>
    rw [pow_succ, ih, End.mul_def, dgE, dgE, dgE, dg_comp hx (hx.replicate_of n),
      List.replicate_succ]
    rfl

theorem lin_ccwReal (ν : X) (i : I) (m : ℕ) :
    P.lin (LinDiagram.of (ccwReal RD ν i m)) = dg P ν [] [] (ccwLs i m) := by
  rw [ccwReal, lin_of_mkD]; rfl

theorem lin_cwReal (ν : X) (i : I) (m : ℕ) :
    P.lin (LinDiagram.of (cwReal RD ν i m)) = dg P ν [] [] (cwLs i m) := by
  rw [cwReal, lin_of_mkD]; rfl

/-- `n` dots on the strand `l` with rightmost region `λ`, as a 2-morphism of `U`
(the class of `dots RD λ [] l [] n`, see `dotsU_eq`). -/
abbrev dotsU (lam : X) (l : Letter I) (n : ℕ) :
    End (P.obj (ob RD lam [l])) :=
  dg P lam [l] [l] (List.replicate n ([], .dot l, []))

theorem dotsU_eq (lam : X) (l : Letter I) (n : ℕ) :
    P.diag (dots RD lam [] l [] n) = dotsU P lam l n :=
  (dg_of _).symm

theorem dotsU_add (lam : X) (l : Letter I) (p q : ℕ) :
    dotsU P lam l p ≫ dotsU P lam l q = dotsU P lam l (p + q) := by
  rw [dotsU, dotsU, dotsU, dg_comp (by schain) (by schain), List.replicate_add]

theorem dotsU_zero (lam : X) (l : Letter I) : dotsU P lam l 0 = 𝟙 _ := by
  rw [dotsU, List.replicate_zero, dg_nil]

/-- The counterclockwise bubble with label `m ∈ ℤ` (real, fake or zero; `ccwL`) in `U`. -/
abbrev ccwU (ν : X) (i : I) (m : ℤ) : End (P.obj (ob RD ν [])) :=
  P.lin (ccwL RD k ν i m)

/-- The clockwise bubble with label `m ∈ ℤ` (real, fake or zero; `cwL`) in `U`. -/
abbrev cwU (ν : X) (i : I) (m : ℤ) : End (P.obj (ob RD ν [])) :=
  P.lin (cwL RD k ν i m)

theorem ccwU_of_nonneg (ν : X) (i : I) (m : ℕ) :
    ccwU P ν i m = dg P ν [] [] (ccwLs i m) := by
  rw [ccwU, ccwL, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast, lin_ccwReal]

theorem cwU_of_nonneg (ν : X) (i : I) (m : ℕ) :
    cwU P ν i m = dg P ν [] [] (cwLs i m) := by
  rw [cwU, cwL, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast, lin_cwReal]

theorem lin_finsum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    P.lin (∑ x ∈ s, f x) = ∑ x ∈ s, P.lin (f x) :=
  map_sum (Presentation.linFunctor P).mapAddHom f s

/-! ## Positional rewriting -/

section Positional

variable {P}

/-- A subdiagram `A` may be replaced by `B` in any context if `A` and `B` chain between the same
boundaries and have the same class whenever they chain. -/
theorem dg_congr_ctx {μ : X} {A B : List (LayerData I)}
    (hc : ∀ s t, SChain s A t → SChain s B t) (hc' : ∀ s t, SChain s B t → SChain s A t)
    (hd : ∀ s t, SChain s A t → dg P μ s t A = dg P μ s t B)
    (s₀ t₀ : List (Letter I)) (pre post : List (LayerData I)) :
    dg P μ s₀ t₀ (pre ++ A ++ post) = dg P μ s₀ t₀ (pre ++ B ++ post) := by
  by_cases h : SChain s₀ (pre ++ A ++ post) t₀
  · obtain ⟨b, h₁, h₂⟩ := SChain.split h
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    rw [← dg_comp h₁ h₂, ← dg_comp h₃ h₄, hd a b h₄, dg_comp h₃ (hc a b h₄),
      dg_comp (h₃.append (hc a b h₄)) h₂]
  · rw [dg_of_not h, dg_of_not]
    intro h'
    obtain ⟨b, h₁, h₂⟩ := SChain.split h'
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    exact h ((h₃.append (hc' a b h₄)).append h₂)

/-- **The interchange law at the position `n`**: the layers `n` (generator on the left) and
`n + 1` (generator on the right) of a normal-form diagram are exchanged. -/
theorem dg_swapLR_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.2.2 = y.1.drop (x.1.length + x.2.1.cod.length) ++ y.2.1.dom ++ y.2.2)
    (hy : y.1 = x.1 ++ x.2.1.cod ++ y.1.drop (x.1.length + x.2.1.cod.length)) :
    dg P μ s t L = dg P μ s t (L.take n ++ swapLR x y ++ rest) := by
  rw [congrArg (dg P μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨a, g, r⟩ := x
  obtain ⟨p, h, b⟩ := y
  simp only [swapLR] at hx hy ⊢
  generalize p.drop (a.length + g.cod.length) = m at hx hy ⊢
  subst hx hy
  exact dg_congr_ctx (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t => (sChain_swap_iff a m b g h s t).2) (fun s t _ => dg_swap P μ s t a m b g h)
    s t _ _

/-- **The interchange law at the position `n`**: the layers `n` (generator on the right) and
`n + 1` (generator on the left) of a normal-form diagram are exchanged. -/
theorem dg_swapRL_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.1 = y.1 ++ y.2.1.dom ++ x.1.drop (y.1.length + y.2.1.dom.length))
    (hy : y.2.2 = x.1.drop (y.1.length + y.2.1.dom.length) ++ x.2.1.cod ++ x.2.2) :
    dg P μ s t L = dg P μ s t (L.take n ++ swapRL x y ++ rest) := by
  rw [congrArg (dg P μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨p, h, b⟩ := x
  obtain ⟨a, g, r⟩ := y
  simp only [swapRL] at hx hy ⊢
  generalize p.drop (a.length + g.dom.length) = m at hx hy ⊢
  subst hx hy
  exact dg_congr_ctx (fun s t => (sChain_swap_iff a m b g h s t).2)
    (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t _ => (dg_swap P μ s t a m b g h).symm) s t _ _

/-- **One step of a certificate chain at a position**: if `dg ν s t A = dg ν s t B`
(`ν = μ + v_X`) and the layers `n, …, n + |A| - 1` of `L` are `A` placed between the strands `u`
and `v`, these layers may be replaced by `B` placed between `u` and `v`. -/
theorem dg_step_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)}
    (E : dg P (wt RD μ v) s t A = dg P (wt RD μ v) s t B)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dg P μ s₀ t₀ L =
      dg P μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) :=
  dg_step P μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length) rfl

/-- One step of a certificate chain at a position, with a linear combination on the right-hand
side (`dg_stepL`). -/
theorem dg_stepL_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)}
    {F : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)}
    (E : dg P (wt RD μ v) s t A = F)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dg P μ s₀ t₀ L =
      ctxL P μ s₀ t₀ (L.take n) u v (L.drop (n + A.length)) s t F :=
  dg_stepL P μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length)

/-- One step of a certificate chain at a position, with a scalar multiple of a normal-form
diagram on the right-hand side. -/
theorem dg_step_at_smul {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} (c : k)
    (E : dg P (wt RD μ v) s t A = c • dg P (wt RD μ v) s t B)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dg P μ s₀ t₀ L =
      c • dg P μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) := by
  rw [dg_stepL_at L n u v E hpre hpost hL, map_smul, ctxL_dg P μ hpre hpost]

/-- `dswapQ n`: exchange the layers `n` and `n + 1` of the left-hand side `dg μ s t L` of the
goal by the interchange law. -/
macro "dswapQ " n:term:max : tactic => `(tactic| (
  first
    | refine Eq.trans (dg_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl) (by exact rfl)) ?_
    | refine Eq.trans (dg_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl) (by exact rfl)) ?_
  try dnorm))

/-- `datQ n u v E`: rewrite the left-hand side `dg μ s₀ t₀ L` of the goal with the local
equation `E : dg ν s t A = dg ν s t B` placed between the strands `u` and `v`, `A` starting at
the layer `n` of `L`. -/
macro "datQ " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine Eq.trans (dg_step_at _ $n $u $v $E (by (try dnorm); schain) (by (try dnorm); schain)
    (by dnorm)) ?_
  try dnorm))

/-- A layer `(a, g, b)` on the left slides past a list of layers `B` on the strands to its right
(interchange law, in any context). -/
theorem dg_interchange_one {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (a b : List (Letter I)) (g : Shape I) {t₀ t₁ : List (Letter I)} {B : List (LayerData I)}
    (hB : SChain t₀ B t₁) :
    dg P μ S T (pre ++ [(a, g, b ++ t₀)] ++ B.map (whL (a ++ g.cod ++ b) []) ++ post) =
      dg P μ S T (pre ++ B.map (whL (a ++ g.dom ++ b) []) ++ [(a, g, b ++ t₁)] ++ post) := by
  induction B generalizing pre t₀ with
  | nil =>
    cases hB
    simp
  | cons y B ih =>
    obtain ⟨c, h, d⟩ := y
    obtain ⟨rfl, hB'⟩ := hB
    have e₁ : pre ++ [(a, g, b ++ (c ++ h.dom ++ d))] ++
        List.map (whL (a ++ g.cod ++ b) []) ((c, h, d) :: B) ++ post =
        pre ++ [(a, g, (b ++ c) ++ h.dom ++ d), (a ++ g.cod ++ (b ++ c), h, d)] ++
          (List.map (whL (a ++ g.cod ++ b) []) B ++ post) := by
      simp [whL, List.append_assoc]
    have e₂ : pre ++ [(a ++ g.dom ++ (b ++ c), h, d), (a, g, (b ++ c) ++ h.cod ++ d)] ++
        (List.map (whL (a ++ g.cod ++ b) []) B ++ post) =
        (pre ++ [(a ++ g.dom ++ b ++ c, h, d)]) ++ [(a, g, b ++ (c ++ h.cod ++ d))] ++
          List.map (whL (a ++ g.cod ++ b) []) B ++ post := by
      simp [List.append_assoc]
    rw [e₁, dg_congr_ctx (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).1)
      (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).2)
      (fun s t _ => dg_swap P μ s t a (b ++ c) d g h) S T pre _, e₂, ih _ hB']
    simp [whL, List.append_assoc]

/-- **The interchange law for blocks of layers**: a diagram `A` (from `s` to `s'`) on the left
and a diagram `B` (from `t` to `t'`) on the right can be exchanged, in any context. -/
theorem dg_interchange {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    {s s' t t' : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A s')
    (hB : SChain t B t') :
    dg P μ S T (pre ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post) =
      dg P μ S T (pre ++ B.map (whL s []) ++ A.map (whL [] t') ++ post) := by
  induction A generalizing pre s with
  | nil =>
    cases hA
    simp
  | cons x A ih =>
    obtain ⟨a, g, b⟩ := x
    obtain ⟨rfl, hA'⟩ := hA
    have e₁ : pre ++ List.map (whL [] t) ((a, g, b) :: A) ++ B.map (whL s' []) ++ post =
        (pre ++ [(a, g, b ++ t)]) ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post := by
      simp [whL, List.append_assoc]
    have e₂ : (pre ++ [(a, g, b ++ t)]) ++ B.map (whL (a ++ g.cod ++ b) []) ++
        A.map (whL [] t') ++ post =
        pre ++ [(a, g, b ++ t)] ++ B.map (whL (a ++ g.cod ++ b) []) ++
          (A.map (whL [] t') ++ post) := by
      simp [List.append_assoc]
    rw [e₁, ih _ hA', e₂, dg_interchange_one _ _ a b g hB]
    simp [whL, List.append_assoc]

end Positional

/-! ## Moving blocks of dots -/

/-- A block of `n` copies of a generator `h` with equal source and target (a dot) to the right
of a generator `g` slides below `g`. -/
theorem dg_swap_rep (μ : X) (a m b : List (Letter I)) (g h : Shape I) (hh : h.dom = h.cod)
    (n : ℕ) :
    dg P μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        (List.replicate n (a ++ g.dom ++ m, h, b) ++ [(a, g, m ++ h.cod ++ b)]) =
      dg P μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        ([(a, g, m ++ h.dom ++ b)] ++ List.replicate n (a ++ g.cod ++ m, h, b)) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    refine (dg_step P μ [(a ++ g.dom ++ m, h, b)] [] [] [] ih
      (by simp [hh]) (by simp) (by simp [whL, List.replicate_succ]) rfl).trans ?_
    refine (dg_step P μ [] (List.replicate n (a ++ g.cod ++ m, h, b)) [] []
      (dg_swap' P μ a m b g h).symm (by simp) (by
        simp only [List.nil_append, List.append_nil]
        exact SChain.replicate_of (by simp [hh]) n) (by simp [whL, hh]) rfl).trans ?_
    simp [whL, List.replicate_succ, hh]

/-- A block of `n` copies of a generator `h` with equal source and target (a dot) to the left
of a generator `g` slides below `g`. -/
theorem dg_swap_rep' (μ : X) (a m b : List (Letter I)) (g h : Shape I) (hh : h.dom = h.cod)
    (n : ℕ) :
    dg P μ (a ++ h.dom ++ m ++ g.dom ++ b) (a ++ h.cod ++ m ++ g.cod ++ b)
        (List.replicate n (a, h, m ++ g.dom ++ b) ++ [(a ++ h.cod ++ m, g, b)]) =
      dg P μ (a ++ h.dom ++ m ++ g.dom ++ b) (a ++ h.cod ++ m ++ g.cod ++ b)
        ([(a ++ h.dom ++ m, g, b)] ++ List.replicate n (a, h, m ++ g.cod ++ b)) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    refine (dg_step P μ [(a, h, m ++ g.dom ++ b)] [] [] [] ih
      (by simp [hh]) (by simp) (by simp [whL, List.replicate_succ]) rfl).trans ?_
    refine (dg_step P μ [] (List.replicate n (a, h, m ++ g.cod ++ b)) [] []
      (dg_swap' P μ a m b h g) (by simp) (by
        simp only [List.nil_append, List.append_nil]
        exact SChain.replicate_of (by simp [hh]) n) (by simp [whL, hh]) rfl).trans ?_
    simp [whL, List.replicate_succ, hh]

/-- Two blocks of dots on different strands commute. -/
theorem dg_swap_dots (μ : X) (a m b : List (Letter I)) (l l' : Letter I) (p q : ℕ) :
    dg P μ (a ++ [l] ++ m ++ [l'] ++ b) (a ++ [l] ++ m ++ [l'] ++ b)
        (List.replicate p (a ++ [l] ++ m, .dot l', b) ++ List.replicate q (a, .dot l, m ++ [l'] ++ b)) =
      dg P μ (a ++ [l] ++ m ++ [l'] ++ b) (a ++ [l] ++ m ++ [l'] ++ b)
        (List.replicate q (a, .dot l, m ++ [l'] ++ b) ++ List.replicate p (a ++ [l] ++ m, .dot l', b)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.replicate_succ]
    refine (dg_step P μ [] (List.replicate q (a, .dot l, m ++ [l'] ++ b)) [] []
      (dg_swap_rep P μ a m b (.dot l) (.dot l') rfl p) (by simp) (by
        simp only [List.nil_append, List.append_nil]
        exact SChain.replicate_of (by simp) q) (by simp [whL]) rfl).trans ?_
    refine (dg_step P μ [(a, .dot l, m ++ [l'] ++ b)] [] [] [] ih (by simp) (by simp)
      (by simp [whL]) rfl).trans ?_
    simp [whL]

/-! ## Pulling a strand through a bubble -/

section Pull

variable [HasZigzags P]

/-- **Pulling a strand through a counterclockwise bubble.** After inserting `crossr ∘ crossl`
between an upward `j`-strand and a counterclockwise `i`-bubble on its right, the interchange law
and two zigzag relations turn the diagram into the left closure of `ψ_{ji} x^m ψ_{ij}` (the
strand crosses the upward arc of the bubble twice). Valid for all `i, j`. -/
theorem dg_pull_ccw (lam : X) (i j : I) (m : ℕ) :
    dg P lam [up j] [up j]
        ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
          (crosslL j i ++ crossrL j i).map (whL [] [up i]) ++ [([up j], .cap (up i), [])]) =
      dg P lam [up j] [up j]
        ([([], .cup (dn i), [up j]), ([dn i], .cross true i j, [])] ++
          List.replicate m ([dn i, up j], .dot (up i), []) ++
          [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) := by
  simp only [crosslL, crossrL]
  -- 2., 3. interchange: move the bubble's cap below the crossing of `crossr`
  dstepQ ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
      [([], .cup (dn i), [up j, dn i, up i]), ([dn i], .cross true i j, [dn i, up i]),
        ([dn i, up j], .cap (dn i), [up i]), ([dn i, up j], .cup (up i), [up i]),
        ([dn i], .cross true j i, [dn i, up i])]) [] [] []
    (dg_swap' P lam [] [up j] [] (.cap (up i)) (.cap (up i)))
  dstepQ ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
      [([], .cup (dn i), [up j, dn i, up i]), ([dn i], .cross true i j, [dn i, up i]),
        ([dn i, up j], .cap (dn i), [up i]), ([dn i, up j], .cup (up i), [up i])])
    [([], .cap (up i), [up j])] [] []
    (dg_swap' P lam [dn i] [] [] (.cross true j i) (.cap (up i)))
  -- 4. zigzag
  dstepQ ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
      [([], .cup (dn i), [up j, dn i, up i]), ([dn i], .cross true i j, [dn i, up i]),
        ([dn i, up j], .cap (dn i), [up i])])
    [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [dn i, up j] []
    (dg_zigL' P lam (up i))
  -- 5. slide the cup of `crossl` below the dots of the bubble
  dstepQ [([up j], .cup (dn i), [])]
    [([dn i], .cross true i j, [dn i, up i]), ([dn i, up j], .cap (dn i), [up i]),
      ([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [] []
    (dg_swap_rep P lam [] [up j, dn i] [] (.cup (dn i)) (.dot (up i)) rfl m)
  -- 6. and below the cup of the bubble
  dstepQ [] (List.replicate m ([dn i, up i, up j, dn i], .dot (up i), []) ++
      [([dn i], .cross true i j, [dn i, up i]), ([dn i, up j], .cap (dn i), [up i]),
        ([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) [] []
    (dg_swap' P lam [] [up j] [] (.cup (dn i)) (.cup (dn i))).symm
  -- 7. slide the crossing of `crossl` below the dots
  dstepQ [([], .cup (dn i), [up j]), ([dn i, up i, up j], .cup (dn i), [])]
    [([dn i, up j], .cap (dn i), [up i]), ([dn i], .cross true j i, []),
      ([], .cap (up i), [up j])] [] []
    (dg_swap_rep P lam [dn i] [dn i] [] (.cross true i j) (.dot (up i)) rfl m)
  -- 8. and below the cup of the bubble
  dstepQ [([], .cup (dn i), [up j])]
    (List.replicate m ([dn i, up j, up i, dn i], .dot (up i), []) ++
      [([dn i, up j], .cap (dn i), [up i]), ([dn i], .cross true j i, []),
        ([], .cap (up i), [up j])]) [] []
    (dg_swap' P lam [dn i] [] [] (.cross true i j) (.cup (dn i))).symm
  -- 9. slide the cap of `crossl` below the dots
  dstepQ [([], .cup (dn i), [up j]), ([dn i], .cross true i j, []),
      ([dn i, up j, up i], .cup (dn i), [])]
    [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] [] []
    (dg_swap_rep P lam [dn i, up j] [] [] (.cap (dn i)) (.dot (up i)) rfl m)
  -- 10. zigzag
  dstepQ [([], .cup (dn i), [up j]), ([dn i], .cross true i j, [])]
    (List.replicate m ([dn i, up j], .dot (up i), []) ++
      [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) [dn i, up j] []
    (dg_zigR' P lam (dn i))
  lnf

/-- **Pulling a strand through a clockwise bubble.** After inserting `crossl ∘ crossr` between
a clockwise `i`-bubble (dots on its upward strand) and an upward `j`-strand on its right, the
interchange law and two zigzag relations turn the diagram into the right closure of
`ψ_{ij} x^m ψ_{ji}`. Valid for all `i, j`. -/
theorem dg_pull_cw (lam : X) (i j : I) (m : ℕ) :
    dg P lam [up j] [up j]
        ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
          (crossrL j i ++ crosslL j i).map (whL [up i] []) ++ [([], .cap (dn i), [up j])]) =
      dg P lam [up j] [up j]
        ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
          List.replicate m ([], .dot (up i), [up j, dn i]) ++
          [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) := by
  simp only [crosslL, crossrL]
  -- 2., 3. interchange: move the bubble's cap below the crossing of `crossl`
  dstepQ ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
      [([up i, dn i, up j], .cup (up i), []), ([up i, dn i], .cross true j i, [dn i]),
        ([up i], .cap (up i), [up j, dn i]), ([up i], .cup (dn i), [up j, dn i]),
        ([up i, dn i], .cross true i j, [dn i])]) [] [] []
    (dg_swap' P lam [] [up j] [] (.cap (dn i)) (.cap (dn i))).symm
  dstepQ ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
      [([up i, dn i, up j], .cup (up i), []), ([up i, dn i], .cross true j i, [dn i]),
        ([up i], .cap (up i), [up j, dn i]), ([up i], .cup (dn i), [up j, dn i])])
    [([up j], .cap (dn i), [])] [] []
    (dg_swap' P lam [] [] [dn i] (.cap (dn i)) (.cross true i j)).symm
  -- 4. zigzag
  dstepQ ([([], .cup (up i), [up j])] ++ List.replicate m ([], .dot (up i), [dn i, up j]) ++
      [([up i, dn i, up j], .cup (up i), []), ([up i, dn i], .cross true j i, [dn i]),
        ([up i], .cap (up i), [up j, dn i])])
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] [up j, dn i]
    (dg_zigR' P (wt RD lam [up j, dn i]) (dn i))
  -- 5. slide the cup of `crossr` below the dots of the bubble
  dstepQ [([], .cup (up i), [up j])]
    [([up i, dn i], .cross true j i, [dn i]), ([up i], .cap (up i), [up j, dn i]),
      ([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] []
    (dg_swap_rep' P lam [] [dn i, up j] [] (.cup (up i)) (.dot (up i)) rfl m)
  -- 6. and below the cup of the bubble
  dstepQ [] (List.replicate m ([], .dot (up i), [dn i, up j, up i, dn i]) ++
      [([up i, dn i], .cross true j i, [dn i]), ([up i], .cap (up i), [up j, dn i]),
        ([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) [] []
    (dg_swap' P lam [] [up j] [] (.cup (up i)) (.cup (up i)))
  -- 7. slide the crossing of `crossr` below the dots
  dstepQ [([up j], .cup (up i), []), ([], .cup (up i), [up j, up i, dn i])]
    [([up i], .cap (up i), [up j, dn i]), ([], .cross true i j, [dn i]),
      ([up j], .cap (dn i), [])] [] []
    (dg_swap_rep' P lam [] [dn i] [dn i] (.cross true j i) (.dot (up i)) rfl m)
  -- 8. and below the cup of the bubble
  dstepQ [([up j], .cup (up i), [])]
    (List.replicate m ([], .dot (up i), [dn i, up i, up j, dn i]) ++
      [([up i], .cap (up i), [up j, dn i]), ([], .cross true i j, [dn i]),
        ([up j], .cap (dn i), [])]) [] []
    (dg_swap' P lam [] [] [dn i] (.cup (up i)) (.cross true j i))
  -- 9. slide the cap of `crossr` below the dots
  dstepQ [([up j], .cup (up i), []), ([], .cross true j i, [dn i]),
      ([], .cup (up i), [up i, up j, dn i])]
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] []
    (dg_swap_rep' P lam [] [] [up j, dn i] (.cap (up i)) (.dot (up i)) rfl m)
  -- 10. zigzag
  dstepQ [([up j], .cup (up i), []), ([], .cross true j i, [dn i])]
    (List.replicate m ([], .dot (up i), [up j, dn i]) ++
      [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) [] [up j, dn i]
    (dg_zigL' P (wt RD lam [up j, dn i]) (up i))
  lnf

end Pull

/-! ## Bubbles next to a strand in normal form -/

theorem lin_bubR_ccwReal (lam : X) (l : Letter I) (i : I) (m : ℕ) :
    P.lin (bubR RD k lam [l] (LinDiagram.of (ccwReal RD lam i m))) =
      dg P lam [l] [l] ([([l], .cup (dn i), [])] ++ List.replicate m ([l, dn i], .dot (up i), []) ++
        [([l], .cap (up i), [])]) := by
  rw [lin_bubR, ccwReal, lin_of_mkD, plcL_dg_nil]
  show dg P lam [l] [l] _ = _
  congr 1; lnf

theorem lin_bubL_ccwReal (μ : X) (l : Letter I) (i : I) (m : ℕ) :
    P.lin (bubL RD k μ [l] (LinDiagram.of (ccwReal RD (wt RD μ [l]) i m))) =
      dg P μ [l] [l] ([([], .cup (dn i), [l])] ++ List.replicate m ([dn i], .dot (up i), [l]) ++
        [([], .cap (up i), [l])]) := by
  rw [lin_bubL, ccwReal, lin_of_mkD, plcL_dg]
  show dg P μ [l] [l] _ = _
  congr 1; lnf

theorem lin_bubR_cwReal (lam : X) (l : Letter I) (i : I) (m : ℕ) :
    P.lin (bubR RD k lam [l] (LinDiagram.of (cwReal RD lam i m))) =
      dg P lam [l] [l] ([([l], .cup (up i), [])] ++ List.replicate m ([l, up i], .dot (dn i), []) ++
        [([l], .cap (dn i), [])]) := by
  rw [lin_bubR, cwReal, lin_of_mkD, plcL_dg_nil]
  show dg P lam [l] [l] _ = _
  congr 1; lnf

theorem lin_bubL_cwReal (μ : X) (l : Letter I) (i : I) (m : ℕ) :
    P.lin (bubL RD k μ [l] (LinDiagram.of (cwReal RD (wt RD μ [l]) i m))) =
      dg P μ [l] [l] ([([], .cup (up i), [l])] ++ List.replicate m ([up i], .dot (dn i), [l]) ++
        [([], .cap (dn i), [l])]) := by
  rw [lin_bubL, cwReal, lin_of_mkD, plcL_dg]
  show dg P μ [l] [l] _ = _
  congr 1; lnf

end Categorification.KL3.Diagram.NF
