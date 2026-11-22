/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Upward
import Categorification.Diagrams.KL3.NormalForm

/-!
# A calculus of local rewriting for normal-form diagrams of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.

Diagrams of `U` in normal form (`mkD RD μ ls h`, a list of layers `(u, g, v)` with rightmost
region `μ`, see `Categorification.Diagrams.KL3.Basic`) are manipulated by local moves: a
subdiagram, possibly placed between strands `u` and `v`, is replaced by an equal linear
combination of subdiagrams. The relation-independent part of this calculus is proved once,
for any presentation on the signature of `U`, in `Categorification.Diagrams.KL3.NormalForm`
(lists of layers: `Categorification.Diagrams.KL3.Layers`); here it is specialized to
`pres RD k`, and the relations of `U` are put in normal form:

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

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

instance : NF.HasZigzags (pres RD k) := ⟨zigzags RD k⟩

/-! ## Placement -/

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
      (pres RD k).diag (mkD RD μ (ls.map (whL u v)) (h.whisk u v)) :=
  NF.plc_diag (P := pres RD k) μ u v hst ls h

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
        (pres RD k).diag (mkD RD μ post hpost) :=
  NF.ctx_apply (P := pres RD k) μ pre u v post hpre hpost hst f

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctx_diag (μ : X) {s₀ t₀ s t : List (Letter I)} (pre : List (LayerData I))
    (u v : List (Letter I)) (post : List (LayerData I)) (hpre : SChain s₀ pre (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) post t₀) (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (ls : List (LayerData I)) (h : SChain s ls t) :
    ctx RD k μ pre u v post hpre hpost hst ((pres RD k).diag (mkD RD (wt RD μ v) ls h)) =
      (pres RD k).diag (mkD RD μ (pre ++ ls.map (whL u v) ++ post)
        ((hpre.append (h.whisk u v)).append hpost)) :=
  NF.ctx_diag (P := pres RD k) μ pre u v post hpre hpost hst ls h

/-! ## Diagram classes without typing proofs -/

open Classical in
/-- The class in `U` of the normal-form diagram with layers `ls` from `E_s 1_μ` to `E_t 1_μ`
(rightmost region `μ`), or `0` if the layers do not form such a diagram. -/
def dg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t) :=
  if h : SChain s ls t then (pres RD k).diag (mkD RD μ ls h) else 0

section Dg

variable {RD k}

theorem dg_of {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    dg RD k μ s t ls = (pres RD k).diag (mkD RD μ ls h) :=
  NF.dg_of (P := pres RD k) h

theorem dg_of_not {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : ¬ SChain s ls t) : dg RD k μ s t ls = 0 :=
  NF.dg_of_not (P := pres RD k) h

theorem dg_nil (μ : X) (s : List (Letter I)) : dg RD k μ s s [] = 𝟙 _ :=
  NF.dg_nil (P := pres RD k) μ s

theorem dg_comp {μ : X} {s t r : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A t)
    (hB : SChain t B r) : dg RD k μ s t A ≫ dg RD k μ t r B = dg RD k μ s r (A ++ B) :=
  NF.dg_comp (P := pres RD k) hA hB

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
      dg RD k μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) :=
  NF.plcL_dg (P := pres RD k) μ u v s t A

/-- `plcL_dg` for an empty right context. -/
theorem plcL_dg_nil (μ : X) (u s t : List (Letter I)) (A : List (LayerData I)) :
    plcL RD k μ u [] s t (dg RD k μ s t A) = dg RD k μ (u ++ s ++ []) (u ++ t ++ []) (A.map (whL u [])) :=
  NF.plcL_dg_nil (P := pres RD k) μ u s t A

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
      dg RD k μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) :=
  NF.ctxL_dg (P := pres RD k) μ hpre hpost A

/-- `ctxL_dg` for an empty right context (the region is then unchanged). -/
theorem ctxL_dg_nil (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ [])) (hpost : SChain (u ++ t ++ []) post t₀)
    (A : List (LayerData I)) :
    ctxL RD k μ s₀ t₀ pre u [] post s t (dg RD k μ s t A) =
      dg RD k μ s₀ t₀ (pre ++ A.map (whL u []) ++ post) :=
  NF.ctxL_dg_nil (P := pres RD k) μ hpre hpost A

/-- **The rewriting principle.** If `dg ν s t A = F` (`ν = μ + v_X`), then the diagram
`pre ++ A ++ post`, with `A` placed between the strands `u` and `v`, equals the image of `F`
under `ctxL`. -/
theorem dg_rw (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    {A : List (LayerData I)} {F : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶
      (pres RD k).obj (ob RD (wt RD μ v) t)} (E : dg RD k (wt RD μ v) s t A = F) :
    dg RD k μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) = ctxL RD k μ s₀ t₀ pre u v post s t F :=
  NF.dg_rw (P := pres RD k) μ hpre hpost E

/-- **One step of a certificate chain.** If `dg ν s t A = dg ν s t B` (`ν = μ + v_X`), then
in any diagram in which `A` occurs between the strands `u` and `v` (below it the layers `pre`,
above it the layers `post`), `A` may be replaced by `B`. -/
theorem dg_step (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B L L' : List (LayerData I)}
    (E : dg RD k (wt RD μ v) s t A = dg RD k (wt RD μ v) s t B)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    dg RD k μ s₀ t₀ L = dg RD k μ s₀ t₀ L' :=
  NF.dg_step (P := pres RD k) μ pre post u v E hpre hpost hL hL'

/-- One step of a certificate chain whose right-hand side is a linear combination: the image of
the right-hand side under `ctxL`. -/
theorem dg_stepL (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A L : List (LayerData I)}
    {F : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)}
    (E : dg RD k (wt RD μ v) s t A = F)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) :
    dg RD k μ s₀ t₀ L = ctxL RD k μ s₀ t₀ pre u v post s t F :=
  NF.dg_stepL (P := pres RD k) μ pre post u v E hpre hpost hL

/-! ## The interchange law in normal form -/

/-- The interchange law for two adjacent layers with empty outer context: the generator `g`
on the left, the strands `m`, the generator `h` on the right. -/
theorem swap_diag₀ (ν : X) (m : List (Letter I)) (g h : Shape I) {s t : List (Letter I)}
    (H₁ : SChain s [([], g, m ++ h.dom), (g.cod ++ m, h, [])] t)
    (H₂ : SChain s [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] t) :
    (pres RD k).diag (mkD RD ν _ H₁) = (pres RD k).diag (mkD RD ν _ H₂) :=
  NF.swap_diag₀ (P := pres RD k) ν m g h H₁ H₂

theorem dg_swap₀ (ν : X) (m : List (Letter I)) (g h : Shape I) :
    dg RD k ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [([], g, m ++ h.dom), (g.cod ++ m, h, [])] =
      dg RD k ν (g.dom ++ m ++ h.dom) (g.cod ++ m ++ h.cod)
        [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] :=
  NF.dg_swap₀ (P := pres RD k) ν m g h

/-- **The interchange law in normal form**: two adjacent layers whose generators `g` (left) and
`h` (right) are separated by the strands `m` can be exchanged. -/
theorem dg_swap (μ : X) (s t a m b : List (Letter I)) (g h : Shape I) :
    dg RD k μ s t [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dg RD k μ s t [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] :=
  NF.dg_swap (P := pres RD k) μ s t a m b g h

/-- The interchange law in normal form, with the natural boundaries. -/
theorem dg_swap' (μ : X) (a m b : List (Letter I)) (g h : Shape I) :
    dg RD k μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      dg RD k μ (a ++ g.dom ++ m ++ h.dom ++ b) (a ++ g.cod ++ m ++ h.cod ++ b)
        [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] :=
  NF.dg_swap' (P := pres RD k) μ a m b g h

/-! ## The zigzag relations in normal form -/

/-- **Zigzag relation**, first form: the cup `1 ⟶ l l*` to the left of the strand `l`, followed
by the cap `l* l ⟶ 1`, is the identity of `l`. -/
theorem dg_zigL (ν : X) (l : Letter I) :
    dg RD k ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = 𝟙 _ :=
  NF.dg_zigL (P := pres RD k) ν l

/-- **Zigzag relation**, second form: the cup `1 ⟶ l l*` to the right of the strand `l*`,
followed by the cap `l* l ⟶ 1`, is the identity of `l*`. -/
theorem dg_zigR (ν : X) (l : Letter I) :
    dg RD k ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] = 𝟙 _ :=
  NF.dg_zigR (P := pres RD k) ν l

theorem dg_zigL' (ν : X) (l : Letter I) :
    dg RD k ν [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = dg RD k ν [l] [l] [] :=
  NF.dg_zigL' (P := pres RD k) ν l

theorem dg_zigR' (ν : X) (l : Letter I) :
    dg RD k ν [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] =
      dg RD k ν [l.dual] [l.dual] [] :=
  NF.dg_zigR' (P := pres RD k) ν l

/-! ## Composition of placements -/

theorem whisk_congr_left {a b U U' : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b)
    (V : List (Col I X)) (h : U = U') :
    (pres RD k).whisk f U V =
      eqToHom (by rw [h]) ≫ (pres RD k).whisk f U' V ≫ eqToHom (by rw [h]) :=
  NF.whisk_congr_left (P := pres RD k) f V h

/-- Placement is compatible with composition. -/
theorem plcL_comp (μ : X) (u v : List (Letter I)) {s r t : List (Letter I)}
    (hsr : wt RD (wt RD μ v) r = wt RD (wt RD μ v) s) (hrt : wt RD (wt RD μ v) t = wt RD (wt RD μ v) r)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) r))
    (g : (pres RD k).obj (ob RD (wt RD μ v) r) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) :
    plcL RD k μ u v s r f ≫ plcL RD k μ u v r t g = plcL RD k μ u v s t (f ≫ g) :=
  NF.plcL_comp (P := pres RD k) μ u v hsr hrt f g

/-! ## Bubbles placed next to a strand -/

theorem lin_cast {a b a' b' : Obj (psig RD)} (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    (pres RD k).lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg (pres RD k).obj ha).symm ≫ (pres RD k).lin f ≫
        eqToHom (congrArg (pres RD k).obj hb) :=
  NF.lin_cast (P := pres RD k) f ha hb

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (`bubR`) is its placement. -/
theorem lin_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    (pres RD k).lin (bubR RD k lam [l] b) = plcL RD k lam [l] [] [] [] ((pres RD k).lin b) :=
  NF.lin_bubR (P := pres RD k) lam l b

/-- An endomorphism of `1_{μ + l}` placed to the left of the strand `l` (`bubL`) is its
placement. -/
theorem lin_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    (pres RD k).lin (bubL RD k μ [l] b) = plcL RD k μ [] [l] [] [] ((pres RD k).lin b) :=
  NF.lin_bubL (P := pres RD k) μ l b

/-- An endomorphism of `1_{μ + l_X}` placed to the left of the strand `l` (rightmost region
`μ`). -/
abbrev bubLU (μ : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))) :
    End ((pres RD k).obj (ob RD μ [l])) :=
  plcL RD k μ [] [l] [] [] β

/-- An endomorphism of `1_λ` placed to the right of the strand `l` (rightmost region `λ`). -/
abbrev bubRU (lam : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD lam []))) :
    End ((pres RD k).obj (ob RD lam [l])) :=
  plcL RD k lam [l] [] [] [] β

theorem plcL_diag_left (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) []) :
    bubLU RD k μ l ((pres RD k).diag d) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker d (ob RD (wt RD μ [l]) []) (wd RD μ [l])
        (whiskerOK_ob RD μ [] [l] [])) (ob_whisker RD μ [] [l] [] [] rfl)
        (ob_whisker RD μ [] [l] [] [] rfl)) :=
  NF.plcL_diag_left (P := pres RD k) μ l d

theorem bubLU_diag_comm (μ : X) (l : Letter I) (d : ob RD (wt RD μ [l]) [] ⟶ ob RD (wt RD μ [l]) [])
    (e : ob RD μ [l] ⟶ ob RD μ [l]) :
    bubLU RD k μ l ((pres RD k).diag d) ≫ (pres RD k).diag e =
      (pres RD k).diag e ≫ bubLU RD k μ l ((pres RD k).diag d) :=
  NF.bubLU_diag_comm (P := pres RD k) μ l d e

/-- **Bubbles to the left of a strand are central**: an endomorphism of `1_{μ + l_X}` placed to
the left of the strand `l` commutes with every endomorphism of `E_l 1_μ` (interchange law). -/
theorem bubLU_comm (μ : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD (wt RD μ [l]) [])))
    (γ : End ((pres RD k).obj (ob RD μ [l]))) :
    bubLU RD k μ l β ≫ γ = γ ≫ bubLU RD k μ l β :=
  NF.bubLU_comm (P := pres RD k) μ l β γ

theorem plcL_diag_right (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam []) :
    bubRU RD k lam l ((pres RD k).diag d) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker d (ob RD lam [l]) []
        (whiskerOK_ob RD lam [l] [] [])) (ob_whisker RD lam [l] [] [] [] rfl)
        (ob_whisker RD lam [l] [] [] [] rfl)) :=
  NF.plcL_diag_right (P := pres RD k) lam l d

theorem bubRU_diag_comm (lam : X) (l : Letter I) (d : ob RD lam [] ⟶ ob RD lam [])
    (e : ob RD lam [l] ⟶ ob RD lam [l]) :
    bubRU RD k lam l ((pres RD k).diag d) ≫ (pres RD k).diag e =
      (pres RD k).diag e ≫ bubRU RD k lam l ((pres RD k).diag d) :=
  NF.bubRU_diag_comm (P := pres RD k) lam l d e

/-- **Bubbles to the right of a strand are central** in `END(E_l 1_λ)`. -/
theorem bubRU_comm (lam : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD lam [])))
    (γ : End ((pres RD k).obj (ob RD lam [l]))) :
    bubRU RD k lam l β ≫ γ = γ ≫ bubRU RD k lam l β :=
  NF.bubRU_comm (P := pres RD k) lam l β γ

theorem lin_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    (pres RD k).lin (LinDiagram.of (mkD RD μ ls h)) = dg RD k μ s t ls :=
  NF.lin_of_mkD (P := pres RD k) μ ls h

/-! ## Proving that concrete lists of layers chain -/

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
    (n : ℕ) : (dgE RD k μ s [x]) ^ n = dgE RD k μ s (List.replicate n x) :=
  NF.dgE_pow_single (P := pres RD k) μ s x hx n

/-! ## The relations of `U` in normal form -/

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
    · simp [upLD, upShape_dom]
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
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        upFunctor_diag, upDiag_eq_dg]
      rfl
  rw [e₀, KLR.klQ2]
  split_ifs
  · rw [ncEval_one_aux, dg_nil]; rfl
  · rw [ncEval_X_pow_add_X_pow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
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

theorem lin_ccwReal (ν : X) (i : I) (m : ℕ) :
    (pres RD k).lin (LinDiagram.of (ccwReal RD ν i m)) = dg RD k ν [] [] (ccwLs i m) :=
  NF.lin_ccwReal (P := pres RD k) ν i m

theorem lin_cwReal (ν : X) (i : I) (m : ℕ) :
    (pres RD k).lin (LinDiagram.of (cwReal RD ν i m)) = dg RD k ν [] [] (cwLs i m) :=
  NF.lin_cwReal (P := pres RD k) ν i m

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
  NF.dotsU_eq (P := pres RD k) lam l n

theorem dotsU_add (lam : X) (l : Letter I) (p q : ℕ) :
    dotsU RD k lam l p ≫ dotsU RD k lam l q = dotsU RD k lam l (p + q) :=
  NF.dotsU_add (P := pres RD k) lam l p q

theorem dotsU_zero (lam : X) (l : Letter I) : dotsU RD k lam l 0 = 𝟙 _ :=
  NF.dotsU_zero (P := pres RD k) lam l

/-- The counterclockwise bubble with label `m ∈ ℤ` (real, fake or zero; `ccwL`) in `U`. -/
abbrev ccwU (ν : X) (i : I) (m : ℤ) : End ((pres RD k).obj (ob RD ν [])) :=
  (pres RD k).lin (ccwL RD k ν i m)

/-- The clockwise bubble with label `m ∈ ℤ` (real, fake or zero; `cwL`) in `U`. -/
abbrev cwU (ν : X) (i : I) (m : ℤ) : End ((pres RD k).obj (ob RD ν [])) :=
  (pres RD k).lin (cwL RD k ν i m)

theorem ccwU_of_nonneg (ν : X) (i : I) (m : ℕ) :
    ccwU RD k ν i m = dg RD k ν [] [] (ccwLs i m) :=
  NF.ccwU_of_nonneg (P := pres RD k) ν i m

theorem cwU_of_nonneg (ν : X) (i : I) (m : ℕ) :
    cwU RD k ν i m = dg RD k ν [] [] (cwLs i m) :=
  NF.cwU_of_nonneg (P := pres RD k) ν i m

theorem lin_finsum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    (pres RD k).lin (∑ x ∈ s, f x) = ∑ x ∈ s, (pres RD k).lin (f x) :=
  NF.lin_finsum (P := pres RD k) s f

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

end Categorification.KL3.Diagram
