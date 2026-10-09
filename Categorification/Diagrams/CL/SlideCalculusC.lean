/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Rotate
import Categorification.Diagrams.KL3.Rewriting

/-!
# Positional rewriting of normal-form diagrams in a presentation on the signature of `U`

The calculus of local rewriting of `Categorification.Diagrams.KL3.SlideCalculus` and
`Categorification.Diagrams.KL3.Rewriting`, which is stated for the presentation `pres RD k` of
Khovanov–Lauda's `U`, for an arbitrary presentation `P` on the signature `psig RD` (the class of
a normal-form diagram is `dgC P`, `Categorification.Diagrams.CL.Rotate`). Nothing here uses a
relation of `P` except, for `dgC_zigL`, `dgC_zigR`, the zigzag relations (`hz`). This is used for
presentations such as `U_Q(g)` (Cautis–Lauda) and its sub-presentations.

* `plcC`, `plcLC`, `plcC_diag`, `plcLC_dg`: placement of a 2-morphism between strands;
* `ctxC`, `ctxLC`, `ctxLC_dg`, `dgC_rw`, `dgC_step`, `dgC_stepL`: rewriting in context;
* `dgC_swap`, `dgC_swap'` (interchange), `dgC_zigL`, `dgC_zigR` (zigzags);
* `dgC_congr_ctx`, `dgC_swapLR_at`, `dgC_swapRL_at`, `dgC_step_at`, `dgC_stepL_at` and the
  tactics `dswapC n`, `datC n u v E` (positional front end; `dnorm`, `schain` as in
  `Categorification.Diagrams.KL3`);
* `dgC_interchange_one`, `dgC_interchange`: interchange of blocks of layers.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (psig RD) k)


/-- **Placement.** The `k`-linear map placing a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`, with
`ν = μ + v_X`, between the strands `u` and `v`; the rightmost region becomes `μ`. -/
def plcC (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
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
theorem plcC_diag (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) (ls : List (LayerData I))
    (h : SChain s ls t) :
    plcC P μ u v hst (P.diag (mkD RD (wt RD μ v) ls h)) =
      P.diag (mkD RD μ (ls.map (whL u v)) (h.whisk u v)) := by
  simp only [plcC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ u v s)]
  rw [P.diag_eq_of_layers_eq' (mkD RD μ (ls.map (whL u v)) (h.whisk u v))
    (Diagram.whisker (mkD RD (wt RD μ v) ls h) (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)
      (whiskerOK_ob RD μ u v s)) (ob_whisker RD μ u v s s rfl).symm
      (ob_whisker RD μ u v s t hst).symm ?_]
  rw [Diagram.layers_whisker, layers_mkD, layers_mkD, layList_whisker RD μ u v h]

/-! ## Rewriting in context -/

/-- **Rewriting in context.** Place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + v_X`) between
the strands `u` and `v`, and compose with the normal-form diagrams `pre` below and `post`
above. -/
def ctxC (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ s₀) ⟶ P.obj (ob RD μ t₀)) where
  toFun f := P.diag (mkD RD μ pre hpre) ≫ plcC P μ u v hst f ≫
    P.diag (mkD RD μ post hpost)
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ctxC_apply (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    ctxC P μ pre u v post hpre hpost hst f =
      P.diag (mkD RD μ pre hpre) ≫ plcC P μ u v hst f ≫
        P.diag (mkD RD μ post hpost) := rfl

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctxC_diag (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (ls : List (LayerData I)) (h : SChain s ls t) :
    ctxC P μ pre u v post hpre hpost hst (P.diag (mkD RD (wt RD μ v) ls h)) =
      P.diag (mkD RD μ (pre ++ ls.map (whL u v) ++ post)
        ((hpre.append (h.whisk u v)).append hpost)) := by
  rw [ctxC_apply, plcC_diag, ← Presentation.diag_comp, ← Presentation.diag_comp, mkD_comp, mkD_comp]
  exact P.diag_eq_of_layers_eq (by simp)


open Classical in
/-- Placement between the strands `u` and `v`, as a `k`-linear map on all morphisms
`E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + v_X`); it is `0` if `s` and `t` have different weights. -/
def plcLC (μ : X) (u v s t : List (Letter I)) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ (u ++ s ++ v)) ⟶ P.obj (ob RD μ (u ++ t ++ v))) :=
  if h : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s then plcC P μ u v h else 0

theorem plcLC_dg (μ : X) (u v s t : List (Letter I)) (A : List (LayerData I)) :
    plcLC P μ u v s t (dgC P (wt RD μ v) s t A) =
      dgC P μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) := by
  by_cases hA : SChain s A t
  · rw [plcLC, dite_eq_left (hA.wt_eq RD _), dgC_of hA, plcC_diag, dgC_of]
  · rw [dgC_of_not hA, map_zero, dgC_of_not (fun h => hA h.of_whisk)]

/-- `plcLC_dg` for an empty right context. -/
theorem plcLC_dg_nil (μ : X) (u s t : List (Letter I)) (A : List (LayerData I)) :
    plcLC P μ u [] s t (dgC P μ s t A) = dgC P μ (u ++ s ++ []) (u ++ t ++ []) (A.map (whL u [])) :=
  plcLC_dg P μ u [] s t A

/-- **Rewriting in context**, as a `k`-linear map: place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`
(`ν = μ + v_X`) between the strands `u` and `v` and compose with the normal-form diagrams
`pre` below and `post` above. -/
def ctxLC (μ : X) (s₀ t₀ : List (Letter I)) (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (s t : List (Letter I)) :
    (P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) →ₗ[k]
      (P.obj (ob RD μ s₀) ⟶ P.obj (ob RD μ t₀)) where
  toFun f := dgC P μ s₀ (u ++ s ++ v) pre ≫ plcLC P μ u v s t f ≫
    dgC P μ (u ++ t ++ v) t₀ post
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctxLC_dg (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (A : List (LayerData I)) :
    ctxLC P μ s₀ t₀ pre u v post s t (dgC P (wt RD μ v) s t A) =
      dgC P μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) := by
  show dgC P μ s₀ (u ++ s ++ v) pre ≫ plcLC P μ u v s t _ ≫ dgC P μ (u ++ t ++ v) t₀ post = _
  rw [plcLC_dg]
  by_cases hA : SChain s A t
  · rw [dgC_comp (hA.whisk u v) hpost, dgC_comp hpre ((hA.whisk u v).append hpost),
      List.append_assoc]
  · rw [dgC_of_not (fun h => hA h.of_whisk), Limits.zero_comp, Limits.comp_zero, dgC_of_not]
    intro h
    obtain ⟨a, h₁, h₂⟩ := SChain.split h
    obtain ⟨b, h₃, h₄⟩ := SChain.split h₁
    obtain rfl := h₃.eq_target hpre
    obtain rfl := h₂.eq_source hpost
    exact hA h₄.of_whisk

/-- `ctxLC_dg` for an empty right context (the region is then unchanged). -/
theorem ctxLC_dg_nil (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ [])) (hpost : SChain (u ++ t ++ []) post t₀)
    (A : List (LayerData I)) :
    ctxLC P μ s₀ t₀ pre u [] post s t (dgC P μ s t A) =
      dgC P μ s₀ t₀ (pre ++ A.map (whL u []) ++ post) :=
  ctxLC_dg P μ hpre hpost A

/-- **The rewriting principle.** If `dgC ν s t A = F` (`ν = μ + v_X`), then the diagram
`pre ++ A ++ post`, with `A` placed between the strands `u` and `v`, equals the image of `F`
under `ctxLC`. -/
theorem dgC_rw (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    {A : List (LayerData I)} {F : P.obj (ob RD (wt RD μ v) s) ⟶
      P.obj (ob RD (wt RD μ v) t)} (E : dgC P (wt RD μ v) s t A = F) :
    dgC P μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) = ctxLC P μ s₀ t₀ pre u v post s t F := by
  rw [← E, ctxLC_dg P μ hpre hpost]

/-- **One step of a certificate chain.** If `dgC ν s t A = dgC ν s t B` (`ν = μ + v_X`), then
in any diagram in which `A` occurs between the strands `u` and `v` (below it the layers `pre`,
above it the layers `post`), `A` may be replaced by `B`. -/
theorem dgC_step (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B L L' : List (LayerData I)}
    (E : dgC P (wt RD μ v) s t A = dgC P (wt RD μ v) s t B)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    dgC P μ s₀ t₀ L = dgC P μ s₀ t₀ L' := by
  rw [hL, hL', dgC_rw P μ hpre hpost E, ctxLC_dg P μ hpre hpost]

/-- One step of a certificate chain whose right-hand side is a linear combination: the image of
the right-hand side under `ctxLC`. -/
theorem dgC_stepL (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A L : List (LayerData I)}
    {F : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)}
    (E : dgC P (wt RD μ v) s t A = F)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) :
    dgC P μ s₀ t₀ L = ctxLC P μ s₀ t₀ pre u v post s t F := by
  rw [hL, dgC_rw P μ hpre hpost E]


/-! ## The interchange law in normal form -/

/-- The interchange law for two adjacent layers with empty outer context: the generator `g`
on the left, the strands `m`, the generator `h` on the right. -/
theorem swapC_diag₀ (ν : X) (m : List (Letter I)) (g h : Shape I) {s t : List (Letter I)}
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

theorem dgC_swap₀ (ν : X) (m : List (Letter I)) (g h : Shape I) :
    dgC P ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [([], g, m ++ h.dom), (g.cod ++ m, h, [])] =
      dgC P ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] := by
  have H₁ : SChain (g.dom ++ m ++ h.dom) [([], g, m ++ h.dom), (g.cod ++ m, h, [])]
      (g.cod ++ m ++ h.cod) := ⟨by simp, by simp, by simp⟩
  have H₂ : SChain (g.dom ++ m ++ h.dom) [(g.dom ++ m, h, []), ([], g, m ++ h.cod)]
      (g.cod ++ m ++ h.cod) := ⟨by simp, by simp, by simp⟩
  rw [dgC_of H₁, dgC_of H₂]
  exact swapC_diag₀ P ν m g h H₁ H₂

/-- **The interchange law in normal form**: two adjacent layers whose generators `g` (left) and
`h` (right) are separated by the strands `m` can be exchanged. -/
theorem dgC_swap (μ : X) (s t a m b : List (Letter I)) (g h : Shape I) :
    dgC P μ s t [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dgC P μ s t [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] := by
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
    have E := congrArg (ctxLC P μ (a ++ (g.dom ++ m ++ h.dom) ++ b)
      (a ++ (g.cod ++ m ++ h.cod) ++ b) [] a b [] _ _) (dgC_swap₀ P (wt RD μ b) m g h)
    rw [ctxLC_dg P μ (SChain.nil' _) (SChain.nil' _),
      ctxLC_dg P μ (SChain.nil' _) (SChain.nil' _)] at E
    simpa [whL] using E
  · rw [dgC_of_not (fun h' => hc (i₁.1 h')), dgC_of_not (fun h' => hc (i₂.1 h'))]

/-- The interchange law in normal form, with the natural boundaries. -/
theorem dgC_swap' (μ : X) (a m b : List (Letter I)) (g h : Shape I) :
    dgC P μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dgC P μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] :=
  dgC_swap P μ _ _ a m b g h

/-! ## The zigzag relations in normal form -/

/-- **Zigzag relation**, first form: the cup `1 ⟶ l l*` to the left of the strand `l`, followed
by the cap `l* l ⟶ 1`, is the identity of `l`. -/
theorem dgC_zigL (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (l : Letter I) :
    dgC P ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = 𝟙 _ := by
  have H : SChain [l] [([], .cup l, [l]), ([l], .cap l, [])] [l] := ⟨rfl, rfl, rfl⟩
  let c : Col I X := ⟨l, ν⟩
  have ha : ob RD ν [l] = Pivotal.colourObj (inv RD).toColourDuality c := Obj.ext rfl rfl
  rw [dgC_of H, P.diag_eq_of_layers_eq' (mkD RD ν _ H)
    (Pivotal.zigL (inv RD).toColourDuality c) ha ha ?_, ((hz) c).1]
  · simp
  · simp only [layers_mkD, layList_cons, layList_nil, Pivotal.zigL, Diagram.layers_leftZigzag,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
    all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, c])

/-- **Zigzag relation**, second form: the cup `1 ⟶ l l*` to the right of the strand `l*`,
followed by the cap `l* l ⟶ 1`, is the identity of `l*`. -/
theorem dgC_zigR (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (l : Letter I) :
    dgC P ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] = 𝟙 _ := by
  have H : SChain [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] [l.dual] :=
    ⟨rfl, rfl, rfl⟩
  let c : Col I X := ⟨l, sh RD l.dual + ν⟩
  have ha : ob RD ν [l.dual] = Pivotal.dualObj (inv RD).toColourDuality c :=
    Obj.ext rfl (by simp [ob, c, inv_dual])
  rw [dgC_of H, P.diag_eq_of_layers_eq' (mkD RD ν _ H)
    (Pivotal.zigR (inv RD).toColourDuality c) ha ha ?_, ((hz) c).2]
  · simp
  · simp only [layers_mkD, layList_cons, layList_nil, Pivotal.zigR, Diagram.layers_rightZigzag,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
    all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, c, inv_dual])

theorem dgC_zigL' (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (l : Letter I) :
    dgC P ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = dgC P ν [l] [l] [] := by
  rw [dgC_zigL P hz, dgC_nil]

theorem dgC_zigR' (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (l : Letter I) :
    dgC P ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] =
      dgC P ν [l.dual] [l.dual] [] := by
  rw [dgC_zigR P hz, dgC_nil]

/-! ## Composition of placements -/

theorem whiskC_congr_left {a b U U' : Obj (psig RD)} (f : P.obj a ⟶ P.obj b)
    (V : List (Col I X)) (h : U = U') :
    P.whisk f U V =
      eqToHom (by rw [h]) ≫ P.whisk f U' V ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Placement is compatible with composition. -/
theorem plcLC_comp (μ : X) (u v : List (Letter I)) {s r t : List (Letter I)}
    (hsr : wt RD (wt RD μ v) r = wt RD (wt RD μ v) s) (hrt : wt RD (wt RD μ v) t = wt RD (wt RD μ v) r)
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) r))
    (g : P.obj (ob RD (wt RD μ v) r) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    plcLC P μ u v s r f ≫ plcLC P μ u v r t g = plcLC P μ u v s t (f ≫ g) := by
  simp only [plcLC, dite_eq_left hsr, dite_eq_left hrt, dite_eq_left (hrt.trans hsr), plcC, LinearMap.coe_mk,
    AddHom.coe_mk, Presentation.whisk_comp]
  rw [whiskC_congr_left P g (wd RD μ v) (show ob RD (wt RD (wt RD μ v) r) u =
    ob RD (wt RD (wt RD μ v) s) u by rw [hsr])]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]


abbrev dgEC (μ : X) (s : List (Letter I)) (ls : List (LayerData I)) :
    End (P.obj (ob RD μ s)) := dgC P μ s s ls

theorem dgEC_pow_single (μ : X) (s : List (Letter I)) (x : LayerData I) (hx : SChain s [x] s)
    (n : ℕ) : (dgEC P μ s [x]) ^ n = dgEC P μ s (List.replicate n x) := by
  induction n with
  | zero => rw [pow_zero, List.replicate_zero, dgEC, dgC_nil]; rfl
  | succ n ih =>
    rw [pow_succ, ih, End.mul_def, dgEC, dgEC, dgEC, dgC_comp hx (hx.replicate_of n),
      List.replicate_succ]
    rfl


theorem linC_cast {a b a' b' : Obj (psig RD)} (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    P.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha).symm ≫ P.lin f ≫
        eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (`bubR`) is its placement. -/
theorem linC_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    P.lin (bubR RD k lam [l] b) = plcLC P lam [l] [] [] [] (P.lin b) := by
  rw [bubR, linC_cast, ← LinDiagram.whisk_of_ok _ (whiskerOK_right RD lam [l]),
    ← Presentation.whisk_lin]
  simp only [plcLC, dite_eq_left, plcC, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- An endomorphism of `1_{μ + l}` placed to the left of the strand `l` (`bubL`) is its
placement. -/
theorem linC_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    P.lin (bubL RD k μ [l] b) = plcLC P μ [] [l] [] [] (P.lin b) := by
  rw [bubL, linC_cast, ← LinDiagram.whisk_of_ok _ (whiskerOK_left RD μ [l]),
    ← Presentation.whisk_lin]
  simp only [plcLC, plcC]
  rw [dite_eq_left trivial]
  rfl

/-- An endomorphism of `1_{μ + l_X}` placed to the left of the strand `l` (rightmost region
`μ`). -/
abbrev bubLC (μ : X) (l : Letter I) (β : End (P.obj (ob RD (wt RD μ [l]) []))) :
    End (P.obj (ob RD μ [l])) :=
  plcLC P μ [] [l] [] [] β

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (rightmost region `λ`). -/
abbrev bubRC (lam : X) (l : Letter I) (β : End (P.obj (ob RD lam []))) :
    End (P.obj (ob RD lam [l])) :=
  plcLC P lam [l] [] [] [] β

theorem signC_even {a b a' b' : Obj (psig RD)} (f : a ⟶ b) (g : a' ⟶ b') :
    ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) = 1 := by
  simp [Diagram.oddCount, Diagram.oddCountList, Signature.IsEven.odd_eq_false]

theorem plcLC_diag_left (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) []) :
    bubLC P μ l (P.diag d) =
      P.diag (Diagram.cast (Diagram.whisker d (ob RD (wt RD μ [l]) []) (wd RD μ [l])
        (whiskerOK_ob RD μ [] [l] [])) (ob_whisker RD μ [] [l] [] [] rfl)
        (ob_whisker RD μ [] [l] [] [] rfl)) := by
  simp only [bubLC, plcLC, plcC]
  rw [dite_eq_left trivial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD μ [] [l] []), Presentation.diag_cast]
  rfl

theorem bubLC_diag_comm (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) [])
    (e : ob RD μ [l] ⟶ ob RD μ [l]) :
    bubLC P μ l (P.diag d) ≫ P.diag e =
      P.diag e ≫ bubLC P μ l (P.diag d) := by
  rw [plcLC_diag_left, ← Presentation.diag_comp, ← Presentation.diag_comp]
  have hc : (ob RD (wt RD μ [l]) []).Composable (ob RD μ [l]) :=
    ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
  have key := P.diag_interchange_of_composable d e hc
  rw [signC_even, one_smul] at key
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
theorem bubLC_comm (μ : X) (l : Letter I) (β : End (P.obj (ob RD (wt RD μ [l]) [])))
    (γ : End (P.obj (ob RD μ [l]))) :
    bubLC P μ l β ≫ γ = γ ≫ bubLC P μ l β := by
  obtain ⟨F, rfl⟩ := P.lin_surjective β
  obtain ⟨G, rfl⟩ := P.lin_surjective γ
  unfold bubLC
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
      exact bubLC_diag_comm P μ l d e

theorem plcLC_diag_right (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam []) :
    bubRC P lam l (P.diag d) =
      P.diag (Diagram.cast (Diagram.whisker d (ob RD lam [l]) []
        (whiskerOK_ob RD lam [l] [] [])) (ob_whisker RD lam [l] [] [] [] rfl)
        (ob_whisker RD lam [l] [] [] [] rfl)) := by
  simp only [bubRC, plcLC, plcC]
  rw [dite_eq_left trivial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob RD lam [l] [] []), Presentation.diag_cast]
  rfl

theorem bubRC_diag_comm (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam [])
    (e : ob RD lam [l] ⟶ ob RD lam [l]) :
    bubRC P lam l (P.diag d) ≫ P.diag e =
      P.diag e ≫ bubRC P lam l (P.diag d) := by
  rw [plcLC_diag_right, ← Presentation.diag_comp, ← Presentation.diag_comp]
  have hc : (ob RD lam [l]).Composable (ob RD lam []) := ⟨ob_wf RD _ _, rfl, ob_wf RD _ _⟩
  have key := P.diag_interchange_of_composable e d hc
  rw [signC_even, one_smul] at key
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
theorem bubRC_comm (lam : X) (l : Letter I) (β : End (P.obj (ob RD lam [])))
    (γ : End (P.obj (ob RD lam [l]))) :
    bubRC P lam l β ≫ γ = γ ≫ bubRC P lam l β := by
  obtain ⟨F, rfl⟩ := P.lin_surjective β
  obtain ⟨G, rfl⟩ := P.lin_surjective γ
  unfold bubRC
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
      exact bubRC_diag_comm P lam l d e

theorem linC_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    P.lin (LinDiagram.of (mkD RD μ ls h)) = dgC P μ s t ls := (dgC_of h).symm

variable {P}

/-! ## Replacing a subdiagram in context -/

/-- A subdiagram `A` may be replaced by `B` in any context if `A` and `B` chain between the same
boundaries and have the same class whenever they chain. -/
theorem dgC_congr_ctx {μ : X} {A B : List (LayerData I)}
    (hc : ∀ s t, SChain s A t → SChain s B t) (hc' : ∀ s t, SChain s B t → SChain s A t)
    (hd : ∀ s t, SChain s A t → dgC P μ s t A = dgC P μ s t B)
    (s₀ t₀ : List (Letter I)) (pre post : List (LayerData I)) :
    dgC P μ s₀ t₀ (pre ++ A ++ post) = dgC P μ s₀ t₀ (pre ++ B ++ post) := by
  by_cases h : SChain s₀ (pre ++ A ++ post) t₀
  · obtain ⟨b, h₁, h₂⟩ := SChain.split h
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    rw [← dgC_comp h₁ h₂, ← dgC_comp h₃ h₄, hd a b h₄, dgC_comp h₃ (hc a b h₄),
      dgC_comp (h₃.append (hc a b h₄)) h₂]
  · rw [dgC_of_not h, dgC_of_not]
    intro h'
    obtain ⟨b, h₁, h₂⟩ := SChain.split h'
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    exact h ((h₃.append (hc' a b h₄)).append h₂)


/-! ## The interchange law at a position -/

/-- **The interchange law at the position `n`**: the layers `n` (generator on the left) and
`n + 1` (generator on the right) of a normal-form diagram are exchanged. -/
theorem dgC_swapLR_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.2.2 = y.1.drop (x.1.length + x.2.1.cod.length) ++ y.2.1.dom ++ y.2.2)
    (hy : y.1 = x.1 ++ x.2.1.cod ++ y.1.drop (x.1.length + x.2.1.cod.length)) :
    dgC P μ s t L = dgC P μ s t (L.take n ++ swapLR x y ++ rest) := by
  rw [congrArg (dgC P μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨a, g, r⟩ := x
  obtain ⟨p, h, b⟩ := y
  simp only [swapLR] at hx hy ⊢
  generalize p.drop (a.length + g.cod.length) = m at hx hy ⊢
  subst hx hy
  exact dgC_congr_ctx (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t => (sChain_swap_iff a m b g h s t).2) (fun s t _ => dgC_swap P μ s t a m b g h)
    s t _ _

/-- **The interchange law at the position `n`**: the layers `n` (generator on the right) and
`n + 1` (generator on the left) of a normal-form diagram are exchanged. -/
theorem dgC_swapRL_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.1 = y.1 ++ y.2.1.dom ++ x.1.drop (y.1.length + y.2.1.dom.length))
    (hy : y.2.2 = x.1.drop (y.1.length + y.2.1.dom.length) ++ x.2.1.cod ++ x.2.2) :
    dgC P μ s t L = dgC P μ s t (L.take n ++ swapRL x y ++ rest) := by
  rw [congrArg (dgC P μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨p, h, b⟩ := x
  obtain ⟨a, g, r⟩ := y
  simp only [swapRL] at hx hy ⊢
  generalize p.drop (a.length + g.dom.length) = m at hx hy ⊢
  subst hx hy
  exact dgC_congr_ctx (fun s t => (sChain_swap_iff a m b g h s t).2)
    (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t _ => (dgC_swap P μ s t a m b g h).symm) s t _ _

/-! ## Local rewriting at a position -/


/-- **One step of a certificate chain at a position**: if `dgC ν s t A = dgC ν s t B`
(`ν = μ + v_X`) and the layers `n, …, n + |A| - 1` of `L` are `A` placed between the strands `u`
and `v`, these layers may be replaced by `B` placed between `u` and `v`. -/
theorem dgC_step_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)}
    (E : dgC P (wt RD μ v) s t A = dgC P (wt RD μ v) s t B)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dgC P μ s₀ t₀ L =
      dgC P μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) :=
  dgC_step P μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length) rfl

/-- One step of a certificate chain at a position, with a linear combination on the right-hand
side (`dgC_stepL`). -/
theorem dgC_stepL_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)}
    {F : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)}
    (E : dgC P (wt RD μ v) s t A = F)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dgC P μ s₀ t₀ L =
      ctxLC P μ s₀ t₀ (L.take n) u v (L.drop (n + A.length)) s t F :=
  dgC_stepL P μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length)



/-- `dswapC n`: exchange the layers `n` and `n + 1` of the left-hand side `dgC μ s t L` of the
goal by the interchange law. -/
macro "dswapC " n:term:max : tactic => `(tactic| (
  first
    | refine Eq.trans (dgC_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl) (by exact rfl)) ?_
    | refine Eq.trans (dgC_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl) (by exact rfl)) ?_
  try dnorm))

/-- `datC n u v E`: rewrite the left-hand side `dgC μ s₀ t₀ L` of the goal with the local
equation `E : dgC ν s t A = dgC ν s t B` placed between the strands `u` and `v`, `A` starting at
the layer `n` of `L`. -/
macro "datC " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine Eq.trans (dgC_step_at _ $n $u $v $E (by (try dnorm); schain) (by (try dnorm); schain)
    (by dnorm)) ?_
  try dnorm))



/-! ## The interchange law for blocks of layers -/

/-- A layer `(a, g, b)` on the left slides past a list of layers `B` on the strands to its right
(interchange law, in any context). -/
theorem dgC_interchange_one {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (a b : List (Letter I)) (g : Shape I) {t₀ t₁ : List (Letter I)} {B : List (LayerData I)}
    (hB : SChain t₀ B t₁) :
    dgC P μ S T (pre ++ [(a, g, b ++ t₀)] ++ B.map (whL (a ++ g.cod ++ b) []) ++ post) =
      dgC P μ S T (pre ++ B.map (whL (a ++ g.dom ++ b) []) ++ [(a, g, b ++ t₁)] ++ post) := by
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
    rw [e₁, dgC_congr_ctx (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).1)
      (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).2)
      (fun s t _ => dgC_swap P μ s t a (b ++ c) d g h) S T pre _, e₂, ih _ hB']
    simp [whL, List.append_assoc]

/-- **The interchange law for blocks of layers**: a diagram `A` (from `s` to `s'`) on the left
and a diagram `B` (from `t` to `t'`) on the right can be exchanged, in any context. -/
theorem dgC_interchange {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    {s s' t t' : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A s')
    (hB : SChain t B t') :
    dgC P μ S T (pre ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post) =
      dgC P μ S T (pre ++ B.map (whL s []) ++ A.map (whL [] t') ++ post) := by
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
    rw [e₁, ih _ hA', e₂, dgC_interchange_one _ _ a b g hB]
    simp [whL, List.append_assoc]


end Categorification.KL3.Diagram.CL
