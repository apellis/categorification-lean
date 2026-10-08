/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SlnEmbedU
import Categorification.QuantumGroup.UDotKL3

/-!
# Relabelling `U(sl₂)` along an `α_i`-string

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, Definition 3.1
(label `def_Ucat`); used for S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of
quantum groups*, arXiv:1111.1431v3, Theorem 1.1, where the relations of `U_Q(g)` involving one
label `i` are deduced from the case `g = sl₂` (§5).

Fix a root datum `RD`, a vertex `i` and a weight `b`. The diagrams of `U(sl₂)` (root datum
`sl2RootDatum`: weights `ℤ`, `α = 2`) are relabelled as diagrams of `U(g)` with all strands
labelled `i`: the region `n` goes to the weight `b + q(n) α_i` (`sw`), for a function `q` with
`q(2 + n) = q(n) + 1` (in the application `q(n) = ⌊(n - ⟨i, b⟩)/2⌋`). This is a map of
signatures (`strSig`, a `StringDiagrams.SigMap`). On the regions `n` with
`⟨i, b + q(n) α_i⟩ = n` (in the application, the regions `n ≡ ⟨i, b⟩ (mod 2)`) every relation of
Definition 3.1 for `sl₂` goes to the corresponding relation for `g` with label `i`
(`strSig_relation`), retyped along the identification of the boundary objects (`Ψ`).

The construction follows `Categorification.Diagrams.KL3.SlnEmbed` and `SlnEmbedU` (the
relabelling `U(sl_{m+1}) → U(sl_{m+2})`), whose generic lemmas on linear combinations of diagrams
are reused.

## Main definitions and results

* `sw`, `sl`, `sC`, `sG`, `strSig`: the relabelling of weights, letters, strands, generators;
* `sO_ob`, `sL_lay`, `Ψ`, `Ψ_of_mkD`: normal forms;
* `Ψ_*`: the relabelling of the diagrams of Definition 3.1;
* `strSig_relation`: the relabelling of the single-label relations.
-/

noncomputable section

namespace Categorification.KL3.Diagram.StringEmbed

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open Categorification.KL3.Diagram.SlnEmbed (linDiagram_induction linCast_comp linCast_self
  linCast_cast linCast_id linCast_sum linCast_zero linAlg linAlg_apply)

universe w u v

local notation "S2" => sl2RootDatum

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (i : I) (b : X) (q : ℤ → ℤ) (hq : ∀ n, q (2 + n) = q n + 1)

/-! ## Weights and letters -/

theorem sh_S2_true : sh S2 ((true, ()) : Letter Unit) = 2 := by
  simp [sh, sl2RootDatum]

theorem sh_S2_false : sh S2 ((false, ()) : Letter Unit) = -2 := by
  simp [sh, sl2RootDatum]

/-- The weight of the region `n`: `b + q(n) α_i`. -/
def sw (n : ℤ) : X := b + q n • RD.iX i

include hq in
theorem q_sub_two (n : ℤ) : q (-2 + n) = q n - 1 := by
  have := hq (-2 + n)
  rw [show 2 + (-2 + n) = n by ring] at this
  omega

/-- The relabelling of letters `(ε, ()) ↦ (ε, i)`. -/
def sl (l : Letter Unit) : Letter I := (l.1, i)

@[simp] theorem sl_mk (e : Bool) (u : Unit) : sl i (e, u) = (e, i) := rfl

@[simp] theorem sl_dual (l : Letter Unit) : sl i l.dual = (sl i l).dual := rfl

include hq in
/-- `sw (sh l + x) = sh (sl l) + sw x`. -/
theorem sh_sl (l : Letter Unit) (x : ℤ) :
    sh RD (sl i l) + sw RD i b q x = sw RD i b q (sh S2 l + x) := by
  obtain ⟨e, u⟩ := l
  cases e
  · rw [sh_S2_false, sw, sw, q_sub_two q hq]
    simp only [sh, sl, sgn_false, neg_smul, one_smul, sub_smul]
    abel
  · rw [sh_S2_true, sw, sw, hq]
    simp only [sh, sl, sgn_true, one_smul, add_smul]
    abel

/-- The relabelling of strand colours `⟨l, r⟩ ↦ ⟨sl l, sw r⟩`. -/
def sC (c : Col Unit ℤ) : Col I X := ⟨sl i c.l, sw RD i b q c.r⟩

include hq in
theorem src_sC (c : Col Unit ℤ) :
    (psig RD).colourSrc (sC RD i b q c) = sw RD i b q ((psig S2).colourSrc c) :=
  sh_sl RD i b q hq c.l c.r

include hq in
theorem dual_sC (c : Col Unit ℤ) :
    (inv RD).dual (sC RD i b q c) = sC RD i b q ((inv S2).dual c) := by
  rw [inv_dual, inv_dual]
  exact Col.ext rfl (sh_sl RD i b q hq c.l c.r)

/-- The relabelling of generators. -/
def sG : (psig S2).Gen → (psig RD).Gen
  | .gen (.dot c) => .gen (.dot (sC RD i b q c))
  | .gen (.cross ε _ _ ν) => .gen (.cross ε i i (sw RD i b q ν))
  | .cup c => .cup (sC RD i b q c)
  | .cap c => .cap (sC RD i b q c)

include hq in
theorem sG_left (g : (psig S2).Gen) :
    (psig RD).left (sG RD i b q g) = sw RD i b q ((psig S2).left g) := by
  rcases g with (⟨c⟩ | ⟨ε, u, u', ν⟩) | c | c
  · exact src_sC RD i b q hq c
  · show sh _ (sl i (ε, u)) + (sh _ (sl i (ε, u')) + sw RD i b q ν) =
      sw RD i b q (sh _ (ε, u) + (sh _ (ε, u') + ν))
    rw [sh_sl RD i b q hq, sh_sl RD i b q hq]
  · exact src_sC RD i b q hq c
  · rfl

include hq in
theorem sG_right (g : (psig S2).Gen) :
    (psig RD).right (sG RD i b q g) = sw RD i b q ((psig S2).right g) := by
  rcases g with (⟨c⟩ | ⟨ε, u, u', ν⟩) | c | c
  · rfl
  · rfl
  · exact src_sC RD i b q hq c
  · rfl

include hq in
theorem sG_dom (g : (psig S2).Gen) :
    (psig RD).dom (sG RD i b q g) = ((psig S2).dom g).map (sC RD i b q) := by
  rcases g with (⟨c⟩ | ⟨ε, u, u', ν⟩) | c | c
  · rfl
  · show [(⟨sl i (ε, u), sh _ (sl i (ε, u')) + sw RD i b q ν⟩ : Col I X),
      ⟨sl i (ε, u'), sw RD i b q ν⟩] =
        [⟨sl i (ε, u), sw RD i b q (sh _ (ε, u') + ν)⟩, ⟨sl i (ε, u'), sw RD i b q ν⟩]
    rw [sh_sl RD i b q hq]
  · rfl
  · show [(inv RD).dual (sC RD i b q c), sC RD i b q c] =
      [sC RD i b q ((inv S2).dual c), sC RD i b q c]
    exact congrArg (fun x => [x, sC RD i b q c]) (dual_sC RD i b q hq c)

include hq in
theorem sG_cod (g : (psig S2).Gen) :
    (psig RD).cod (sG RD i b q g) = ((psig S2).cod g).map (sC RD i b q) := by
  rcases g with (⟨c⟩ | ⟨ε, u, u', ν⟩) | c | c
  · rfl
  · show [(⟨sl i (ε, u'), sh _ (sl i (ε, u)) + sw RD i b q ν⟩ : Col I X),
      ⟨sl i (ε, u), sw RD i b q ν⟩] =
        [⟨sl i (ε, u'), sw RD i b q (sh _ (ε, u) + ν)⟩, ⟨sl i (ε, u), sw RD i b q ν⟩]
    rw [sh_sl RD i b q hq]
  · show [sC RD i b q c, (inv RD).dual (sC RD i b q c)] =
      [sC RD i b q c, sC RD i b q ((inv S2).dual c)]
    exact congrArg (fun x => [sC RD i b q c, x]) (dual_sC RD i b q hq c)
  · rfl

include hq in
/-- **The relabelling of `U(sl₂)` along the `α_i`-string through `b`**, as a map of signatures. -/
def strSig : SigMap (psig S2) (psig RD) where
  region := (sw RD i b q : ℤ → X)
  colour := (sC RD i b q : Col Unit ℤ → Col I X)
  colourSrc := src_sC RD i b q hq
  colourTgt _ := rfl
  gen := sG RD i b q
  dom := sG_dom RD i b q hq
  cod := sG_cod RD i b q hq
  left := sG_left RD i b q hq
  right := sG_right RD i b q hq

/-! ## Normal forms -/

/-- The relabelling of shapes of generators. -/
def sSh : Shape Unit → Shape I
  | .dot l => .dot (sl i l)
  | .cross ε _ _ => .cross ε i i
  | .cup l => .cup (sl i l)
  | .cap l => .cap (sl i l)

theorem sSh_dom (g : Shape Unit) : (sSh i g).dom = g.dom.map (sl i) := by cases g <;> rfl

theorem sSh_cod (g : Shape Unit) : (sSh i g).cod = g.cod.map (sl i) := by cases g <;> rfl

include hq in
theorem wt_map (μ : ℤ) (t : List (Letter Unit)) :
    sw RD i b q (wt S2 μ t) = wt RD (sw RD i b q μ) (t.map (sl i)) := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [wt_cons, List.map_cons, wt_cons, ← ih, sh_sl RD i b q hq]

include hq in
theorem wd_map (μ : ℤ) (t : List (Letter Unit)) :
    (wd S2 μ t).map (sC RD i b q) = wd RD (sw RD i b q μ) (t.map (sl i)) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [wd_cons, List.map_cons, ih, List.map_cons, wd_cons, ← wt_map RD i b q hq]
    rfl

theorem strSig_obj (a : Obj (psig S2)) :
    (strSig RD i b q hq).obj a = ⟨(sw RD i b q a.start : X), a.word.map (sC RD i b q)⟩ := rfl

theorem sO_ob (μ : ℤ) (t : List (Letter Unit)) :
    (strSig RD i b q hq).toLayerMap.obj (ob S2 μ t) = ob RD (sw RD i b q μ) (t.map (sl i)) :=
  Obj.ext (wt_map RD i b q hq μ t) (wd_map RD i b q hq μ t)

include hq in
theorem sG_gen (ν : ℤ) (g : Shape Unit) :
    sG RD i b q (g.gen S2 ν) = (sSh i g).gen RD (sw RD i b q ν) := by
  cases g with
  | dot l => rfl
  | cross ε u u' => rfl
  | cap l => rfl
  | cup l =>
    show PivotalGen.cup (sC RD i b q ⟨l, sh _ l.dual + ν⟩) =
      PivotalGen.cup ⟨sl i l, sh _ (sl i l).dual + sw RD i b q ν⟩
    rw [← sl_dual, sh_sl RD i b q hq]
    rfl

theorem sL_lay (μ : ℤ) (u : List (Letter Unit)) (g : Shape Unit) (v : List (Letter Unit)) :
    (strSig RD i b q hq).layer (lay S2 μ u g v) =
      lay RD (sw RD i b q μ) (u.map (sl i)) (sSh i g) (v.map (sl i)) := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · show sw RD i b q (wt _ μ (u ++ g.dom ++ v)) =
      wt _ (sw RD i b q μ) (u.map (sl i) ++ (sSh i g).dom ++ v.map (sl i))
    rw [wt_map RD i b q hq, sSh_dom, List.map_append, List.map_append]
  · show (strSig RD i b q hq).word (wd _ (wt _ μ (g.dom ++ v)) u) =
      wd _ (wt _ (sw RD i b q μ) ((sSh i g).dom ++ v.map (sl i))) (u.map (sl i))
    show (wd _ (wt _ μ (g.dom ++ v)) u).map (sC RD i b q) = _
    rw [wd_map RD i b q hq, wt_map RD i b q hq, sSh_dom, List.map_append]
  · show sG RD i b q (g.gen _ (wt _ μ v)) = (sSh i g).gen _ (wt _ (sw RD i b q μ) (v.map (sl i)))
    rw [sG_gen RD i b q hq, wt_map RD i b q hq]
  · exact wd_map RD i b q hq μ v

/-- The relabelling of layer data. -/
def sLD (x : LayerData Unit) : LayerData I := (x.1.map (sl i), sSh i x.2.1, x.2.2.map (sl i))

theorem sChain_s {s t : List (Letter Unit)} {ls : List (LayerData Unit)} (h : SChain s ls t) :
    SChain (s.map (sl i)) (ls.map (sLD i)) (t.map (sl i)) := by
  induction ls generalizing s with
  | nil => exact congrArg (List.map (sl i)) h
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [sLD, sSh_dom], ?_⟩
    have := ih h
    simpa [sLD, sSh_cod] using this

theorem layers_map_mkD (μ : ℤ) {s t : List (Letter Unit)} (ls : List (LayerData Unit))
    (h : SChain s ls t) :
    Diagram.layers ((strSig RD i b q hq).toLayerMap.map (mkD S2 μ ls h)) =
      layList RD (sw RD i b q μ) (ls.map (sLD i)) := by
  simp only [LayerMap.layers_map, layers_mkD, layList, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  exact sL_lay RD i b q hq μ x.1 x.2.1 x.2.2


/-! ## Relabelling linear combinations of normal-form diagrams -/

section Psi

variable {K : Type w} [CommRing K]

theorem ip_S2 (u : Unit) (lam : ℤ) : ip S2 u lam = lam := by
  simp [ip, sl2RootDatum]

/-- **The relabelling of linear combinations of normal-form diagrams**, retyped to normal-form
objects along `sO_ob`. -/
def Psi {μ : ℤ} {s t : List (Letter Unit)} (f : LinDiagram K (ob S2 μ s) (ob S2 μ t)) :
    LinDiagram K (ob RD (sw RD i b q μ) (s.map (sl i))) (ob RD (sw RD i b q μ) (t.map (sl i))) :=
  LinDiagram.cast ((strSig RD i b q hq).toLayerMap.lin f) (sO_ob RD i b q hq μ s)
    (sO_ob RD i b q hq μ t)

local notation "Ψ" => Psi RD i b q hq

variable {μ : ℤ} {s r t : List (Letter Unit)}

theorem Ψ_comp (f : LinDiagram K (ob S2 μ s) (ob S2 μ r))
    (g : LinDiagram K (ob S2 μ r) (ob S2 μ t)) : Ψ (f ≫ g) = Ψ f ≫ Ψ g := by
  rw [Psi, LayerMap.lin_comp', linCast_comp _ _ _ (sO_ob RD i b q hq μ r)]; rfl

theorem Ψ_add (f g : LinDiagram K (ob S2 μ s) (ob S2 μ t)) : Ψ (f + g) = Ψ f + Ψ g := by
  rw [Psi, LayerMap.lin_add, LinDiagram.cast_add]; rfl

theorem Ψ_sub (f g : LinDiagram K (ob S2 μ s) (ob S2 μ t)) : Ψ (f - g) = Ψ f - Ψ g := by
  rw [Psi, LayerMap.lin_sub, LinDiagram.cast_sub]; rfl

theorem Ψ_neg (f : LinDiagram K (ob S2 μ s) (ob S2 μ t)) : Ψ (-f) = -Ψ f := by
  rw [Psi, LayerMap.lin_neg, LinDiagram.cast_neg]; rfl

theorem Ψ_smul (c : K) (f : LinDiagram K (ob S2 μ s) (ob S2 μ t)) : Ψ (c • f) = c • Ψ f := by
  rw [Psi, LayerMap.lin_smul, LinDiagram.cast_smul]; rfl

theorem Ψ_zero : Ψ (0 : LinDiagram K (ob S2 μ s) (ob S2 μ t)) = 0 := by
  rw [Psi, LayerMap.lin_zero', linCast_zero]

theorem Ψ_sum {ι : Type*} (T : Finset ι) (f : ι → LinDiagram K (ob S2 μ s) (ob S2 μ t)) :
    Ψ (∑ x ∈ T, f x) = ∑ x ∈ T, Ψ (f x) := by
  rw [Psi, LayerMap.lin_sum, linCast_sum]; rfl

theorem Ψ_id : Ψ (𝟙 (Free.of K (ob S2 μ s))) = 𝟙 _ := by
  show LinDiagram.cast ((strSig RD i b q hq).toLayerMap.lin (LinDiagram.of (𝟙 _))) _ _ = _
  rw [LayerMap.lin_of, LayerMap.map_id]
  exact linCast_id _

theorem Ψ_of_id : Ψ (LinDiagram.of (𝟙 (ob S2 μ s)) : LinDiagram K _ _) = LinDiagram.of (𝟙 _) :=
  Ψ_id RD i b q hq

theorem Ψ_single (d : ob S2 μ s ⟶ ob S2 μ t) (c : K) :
    Ψ (Finsupp.single d c : LinDiagram K (ob S2 μ s) (ob S2 μ t)) =
      Finsupp.single (Diagram.cast ((strSig RD i b q hq).toLayerMap.map d)
        (sO_ob RD i b q hq μ s) (sO_ob RD i b q hq μ t)) c := by
  rw [Psi, LayerMap.lin]
  erw [Finsupp.mapDomain_single]
  rw [LinDiagram.cast_single]

theorem Ψ_of_eq (d : ob S2 μ s ⟶ ob S2 μ t)
    (d' : ob RD (sw RD i b q μ) (s.map (sl i)) ⟶ ob RD (sw RD i b q μ) (t.map (sl i)))
    (h : Diagram.layers d' = (Diagram.layers d).map (strSig RD i b q hq).layer) :
    Ψ (LinDiagram.of d : LinDiagram K _ _) = LinDiagram.of d' := by
  rw [Ψ_single]
  congr 1
  exact Diagram.ext h.symm

theorem Ψ_of_mkD (ls : List (LayerData Unit)) (h : SChain s ls t) :
    Ψ (LinDiagram.of (mkD S2 μ ls h) : LinDiagram K _ _) =
      LinDiagram.of (mkD RD (sw RD i b q μ) (ls.map (sLD i)) (sChain_s i h)) :=
  Ψ_of_eq RD i b q hq _ _ (layers_map_mkD RD i b q hq μ ls h).symm

theorem mkD_congr (ν : X) {s t : List (Letter I)} {ls ls' : List (LayerData I)} (e : ls = ls')
    (h : SChain s ls t) (h' : SChain s ls' t) : mkD RD ν ls h = mkD RD ν ls' h' := by
  subst e; rfl

/-! ### The diagrams of Definition 3.1 -/

variable (K)

theorem Ψ_downDot (u : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (downDot S2 u μ) : LinDiagram K _ _) =
      LinDiagram.of (downDot RD i (sw RD i b q μ)) := by
  unfold downDot; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_rotDotR (u : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (rotDotR S2 u μ) : LinDiagram K _ _) =
      LinDiagram.of (rotDotR RD i (sw RD i b q μ)) := by
  unfold rotDotR; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_rotDotL (u : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (rotDotL S2 u μ) : LinDiagram K _ _) =
      LinDiagram.of (rotDotL RD i (sw RD i b q μ)) := by
  unfold rotDotL; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_downCross (u u' : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (downCross S2 u u' μ) : LinDiagram K _ _) =
      LinDiagram.of (downCross RD i i (sw RD i b q μ)) := by
  unfold downCross; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_rotCrossR (u u' : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (rotCrossR S2 u u' μ) : LinDiagram K _ _) =
      LinDiagram.of (rotCrossR RD i i (sw RD i b q μ)) := by
  unfold rotCrossR; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_rotCrossL (u u' : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (rotCrossL S2 u u' μ) : LinDiagram K _ _) =
      LinDiagram.of (rotCrossL RD i i (sw RD i b q μ)) := by
  unfold rotCrossL; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_crossl (u u' : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (crossl S2 u u' μ) : LinDiagram K _ _) =
      LinDiagram.of (crossl RD i i (sw RD i b q μ)) := by
  unfold crossl; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_crossr (u u' : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (crossr S2 u u' μ) : LinDiagram K _ _) =
      LinDiagram.of (crossr RD i i (sw RD i b q μ)) := by
  unfold crossr; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_curlR (u : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (curlR S2 u μ) : LinDiagram K _ _) =
      LinDiagram.of (curlR RD i (sw RD i b q μ)) := by
  unfold curlR; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_curlL (u : Unit) (μ : ℤ) :
    Ψ (LinDiagram.of (curlL S2 u μ) : LinDiagram K _ _) =
      LinDiagram.of (curlL RD i (sw RD i b q μ)) := by
  unfold curlL; exact Ψ_of_mkD RD i b q hq _ _

theorem Ψ_cwReal (lam : ℤ) (u : Unit) (α : ℕ) :
    Ψ (LinDiagram.of (cwReal S2 lam u α) : LinDiagram K _ _) =
      LinDiagram.of (cwReal RD (sw RD i b q lam) i α) := by
  unfold cwReal; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_ccwReal (lam : ℤ) (u : Unit) (α : ℕ) :
    Ψ (LinDiagram.of (ccwReal S2 lam u α) : LinDiagram K _ _) =
      LinDiagram.of (ccwReal RD (sw RD i b q lam) i α) := by
  unfold ccwReal; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_dotCapEF (lam : ℤ) (u : Unit) (n : ℕ) :
    Ψ (LinDiagram.of (dotCapEF S2 lam u n) : LinDiagram K _ _) =
      LinDiagram.of (dotCapEF RD (sw RD i b q lam) i n) := by
  unfold dotCapEF; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_cupDotEF (lam : ℤ) (u : Unit) (n : ℕ) :
    Ψ (LinDiagram.of (cupDotEF S2 lam u n) : LinDiagram K _ _) =
      LinDiagram.of (cupDotEF RD (sw RD i b q lam) i n) := by
  unfold cupDotEF; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_dotCapFE (lam : ℤ) (u : Unit) (n : ℕ) :
    Ψ (LinDiagram.of (dotCapFE S2 lam u n) : LinDiagram K _ _) =
      LinDiagram.of (dotCapFE RD (sw RD i b q lam) i n) := by
  unfold dotCapFE; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_cupDotFE (lam : ℤ) (u : Unit) (n : ℕ) :
    Ψ (LinDiagram.of (cupDotFE S2 lam u n) : LinDiagram K _ _) =
      LinDiagram.of (cupDotFE RD (sw RD i b q lam) i n) := by
  unfold cupDotFE; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_dots (μ : ℤ) (l : Letter Unit) (n : ℕ) :
    Ψ (LinDiagram.of (dots S2 μ [] l [] n) : LinDiagram K _ _) =
      LinDiagram.of (dots RD (sw RD i b q μ) [] (sl i l) [] n) := by
  unfold dots; refine (Ψ_of_mkD RD i b q hq _ _).trans ?_; congr 1; apply mkD_congr
  simp only [List.map_replicate]; rfl

/-! ### Bubbles -/

/-- `Ψ` on the endomorphisms of `1_λ`, as a ring homomorphism. -/
def Psie (lam : ℤ) : LEnd S2 K (ob S2 lam []) →+* LEnd RD K (ob RD (sw RD i b q lam) []) :=
  (linAlg (R := K) (strSig RD i b q hq).toLayerMap (ob S2 lam [])).toRingHom

theorem Psie_eq (lam : ℤ) (x : LEnd S2 K (ob S2 lam [])) : Psie RD i b q hq K lam x = Ψ x :=
  (linCast_self _ _ _).symm

theorem Ψ_cwR (lam : ℤ) (u : Unit) (n : ℤ) :
    Ψ (cwR S2 K lam u n) = cwR RD K (sw RD i b q lam) i n := by
  unfold cwR; split_ifs
  · exact Ψ_cwReal RD i b q hq K lam u _
  · exact Ψ_zero RD i b q hq

theorem Ψ_ccwR (lam : ℤ) (u : Unit) (n : ℤ) :
    Ψ (ccwR S2 K lam u n) = ccwR RD K (sw RD i b q lam) i n := by
  unfold ccwR; split_ifs
  · exact Ψ_ccwReal RD i b q hq K lam u _
  · exact Ψ_zero RD i b q hq

theorem Ψ_cwL (lam : ℤ) (u : Unit) (n : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (cwL S2 K lam u n) = cwL RD K (sw RD i b q lam) i n := by
  unfold cwL
  rw [hip, ip_S2]
  split_ifs
  · exact Ψ_cwReal RD i b q hq K lam u _
  · rw [← Psie_eq, CL.Rescale.grassInv_map_ringHom]
    congr 1
    funext a
    rw [Psie_eq, Ψ_ccwR]
  · exact Ψ_zero RD i b q hq

theorem Ψ_ccwL (lam : ℤ) (u : Unit) (n : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (ccwL S2 K lam u n) = ccwL RD K (sw RD i b q lam) i n := by
  unfold ccwL
  rw [hip, ip_S2]
  split_ifs
  · exact Ψ_ccwReal RD i b q hq K lam u _
  · rw [← Psie_eq, CL.Rescale.grassInv_map_ringHom]
    congr 1
    funext a
    rw [Psie_eq, Ψ_cwR]
  · exact Ψ_zero RD i b q hq

variable {K}

theorem Ψ_bubR (lam : ℤ) (t : List (Letter Unit)) (x : LinDiagram K (ob S2 lam []) (ob S2 lam [])) :
    Ψ (bubR S2 K lam t x) = bubR RD K (sw RD i b q lam) (t.map (sl i)) (Ψ x) := by
  induction x using linDiagram_induction with
  | zero =>
    simp only [bubR, LinDiagram.whisker_zero, linCast_zero, Ψ_zero]
  | add f g hf hg =>
    simp only [bubR, LinDiagram.whisker_add, LinDiagram.cast_add, Ψ_add] at hf hg ⊢
    rw [hf, hg]
  | single d c =>
    erw [bubR, LinDiagram.whisker_single, LinDiagram.cast_single, Ψ_single, Ψ_single, bubR,
      LinDiagram.whisker_single, LinDiagram.cast_single]
    congr 1
    apply Diagram.ext
    simp only [Diagram.layers_cast, Diagram.layers_whisker, LayerMap.layers_map, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    show (strSig RD i b q hq).layer (L.whisker _ _) = ((strSig RD i b q hq).layer L).whisker _ _
    rw [SigMap.layer_whisker]
    congr 1
    exact sO_ob RD i b q hq lam t

include hq in
theorem hwt (μ : ℤ) (t : List (Letter Unit)) :
    ob RD (sw RD i b q (wt S2 μ t)) [] = ob RD (wt RD (sw RD i b q μ) (t.map (sl i))) [] := by
  rw [wt_map RD i b q hq]

omit [AddCommGroup Y] in
theorem bubL_zero' {I' : Type*} {C' : CartanDatum I'} {X' Y' : Type v} [AddCommGroup X']
    [AddCommGroup Y'] (RD' : RootDatum C' X' Y') (μ : X') (t : List (Letter I')) :
    bubL RD' K μ t 0 = 0 := by
  simp only [bubL]
  erw [LinDiagram.whisker_zero, linCast_zero]

omit [AddCommGroup Y] in
theorem bubL_add' {I' : Type*} {C' : CartanDatum I'} {X' Y' : Type v} [AddCommGroup X']
    [AddCommGroup Y'] (RD' : RootDatum C' X' Y') (μ : X') (t : List (Letter I'))
    (f g : LEnd RD' K (ob RD' (wt RD' μ t) [])) :
    bubL RD' K μ t (f + g) = bubL RD' K μ t f + bubL RD' K μ t g := by
  simp only [bubL]
  erw [LinDiagram.whisker_add, LinDiagram.cast_add]

theorem Ψ_bubL (μ : ℤ) (t : List (Letter Unit))
    (x : LinDiagram K (ob S2 (wt S2 μ t) []) (ob S2 (wt S2 μ t) [])) :
    Ψ (bubL S2 K μ t x) =
      bubL RD K (sw RD i b q μ) (t.map (sl i))
        (LinDiagram.cast (Ψ x) (hwt RD i b q hq μ t) (hwt RD i b q hq μ t)) := by
  induction x using linDiagram_induction with
  | zero =>
    rw [bubL_zero', Ψ_zero, Ψ_zero, linCast_zero, bubL_zero']
  | add f g hf hg =>
    rw [bubL_add', Ψ_add, hf, hg, Ψ_add, LinDiagram.cast_add, bubL_add']
  | single d c =>
    erw [bubL, LinDiagram.whisker_single, LinDiagram.cast_single, Ψ_single, Ψ_single,
      LinDiagram.cast_single, bubL, LinDiagram.whisker_single, LinDiagram.cast_single]
    congr 1
    apply Diagram.ext
    simp only [Diagram.layers_cast, LayerMap.layers_map]
    erw [Diagram.layers_whisker, Diagram.layers_whisker]
    simp only [Diagram.layers_cast, LayerMap.layers_map, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    show (strSig RD i b q hq).layer (L.whisker _ _) = ((strSig RD i b q hq).layer L).whisker _ _
    refine (SigMap.layer_whisker (strSig RD i b q hq) L _ _).trans ?_
    congr 1
    · exact Obj.ext (wt_map RD i b q hq μ t) rfl
    · exact wd_map RD i b q hq μ t

theorem linCast_ccwL {ρ ρ' : X} (h : ρ = ρ') (e e' : ob RD ρ [] = ob RD ρ' []) (n : ℤ) :
    LinDiagram.cast (ccwL RD K ρ i n) e e' = ccwL RD K ρ' i n := by
  subst h; exact linCast_self _ _ _


/-! ### Composite diagrams of the relations -/

variable (K)

theorem Ψ_curlRHS (u : Unit) (lam : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (curlRHS S2 K u lam) = curlRHS RD K i (sw RD i b q lam) := by
  unfold curlRHS
  rw [hip, ip_S2, Ψ_neg, Ψ_sum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Ψ_comp, Ψ_bubR, Ψ_cwL RD i b q hq K lam u _ hip, Ψ_dots]
  rfl

theorem Ψ_curlLHS (u : Unit) (μ : ℤ)
    (hip : ip RD i (sw RD i b q (wt S2 μ [up u])) = wt S2 μ [up u]) :
    Ψ (curlLHS S2 K u μ) = curlLHS RD K i (sw RD i b q μ) := by
  have hw : sw RD i b q (wt S2 μ [up u]) = wt RD (sw RD i b q μ) [up i] :=
    wt_map RD i b q hq μ [up u]
  have hip' : ip RD i (wt RD (sw RD i b q μ) [up i]) = ip S2 u (wt S2 μ [up u]) := by
    rw [← hw, hip, ip_S2]
  unfold curlLHS
  rw [Ψ_sum, hip']
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Ψ_comp, Ψ_bubL, ip_S2, Ψ_ccwL RD i b q hq K _ u _ hip]
  erw [linCast_ccwL RD i hw]
  rw [Ψ_dots]
  rfl

theorem Ψ_decompEFSum (u : Unit) (lam : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (decompEFSum S2 K u lam) = decompEFSum RD K i (sw RD i b q lam) := by
  unfold decompEFSum
  rw [hip, ip_S2, Ψ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Ψ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Ψ_comp, Ψ_comp, Ψ_dotCapEF, Ψ_ccwL RD i b q hq K lam u _ hip, Ψ_cupDotEF]
  rfl

theorem Ψ_decompFESum (u : Unit) (lam : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (decompFESum S2 K u lam) = decompFESum RD K i (sw RD i b q lam) := by
  unfold decompFESum
  rw [hip, ip_S2, Ψ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Ψ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Ψ_comp, Ψ_comp, Ψ_dotCapFE, Ψ_cwL RD i b q hq K lam u _ hip, Ψ_cupDotFE]
  rfl

/-! ### KLR diagrams on upward strands -/

/-- The relabelling of KLR generators `() ↦ i`. -/
def klrGenS : KLR.Diagram.Gen Unit → KLR.Diagram.Gen I
  | .dot _ => .dot i
  | .cross _ _ => .cross i i

/-- The relabelling `() ↦ i` of the KLR signature. -/
def klrS : SigMap (KLR.Diagram.sig Unit) (KLR.Diagram.sig I) where
  region := id
  colour _ := i
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen := klrGenS i
  dom g := by cases g <;> rfl
  cod g := by cases g <;> rfl
  left _ := rfl
  right _ := rfl

theorem sSh_upShape (g : KLR.Diagram.Gen Unit) : sSh i (upShape g) = upShape (klrGenS i g) := by
  cases g <;> rfl

theorem ups_map (w : List Unit) : (ups w).map (sl i) = ups (w.map fun _ => i) := by
  simp only [ups, List.map_map]; rfl

theorem sL_upLay (μ : ℤ) (L : Layer (KLR.Diagram.sig Unit)) :
    (strSig RD i b q hq).layer (upLay S2 μ L) = upLay RD (sw RD i b q μ) ((klrS i).layer L) := by
  rw [upLay, sL_lay, upLay, ups_map, ups_map, sSh_upShape]; rfl

theorem Ψ_upDiag {a₀ b₀ : Obj (KLR.Diagram.sig Unit)} (d : a₀ ⟶ b₀)
    {a' b' : Obj (KLR.Diagram.sig I)} (d' : a' ⟶ b') (hd : Diagram.layers d' = (Diagram.layers d).map (klrS i).layer)
    (ha : (ups a₀.word).map (sl i) = ups a'.word) (hb : (ups b₀.word).map (sl i) = ups b'.word) :
    Ψ (LinDiagram.of (upDiag S2 μ d) : LinDiagram K _ _) =
      LinDiagram.cast (LinDiagram.of (upDiag RD (sw RD i b q μ) d')) (by rw [ha]) (by rw [hb]) := by
  rw [Ψ_single, LinDiagram.cast_single]
  congr 1
  apply Diagram.ext
  simp only [Diagram.layers_cast, LayerMap.layers_map, layers_upDiag, List.map_map, hd]
  refine List.map_congr_left fun L _ => ?_
  exact sL_upLay RD i b q hq μ L


end Psi


/-! ## The relations -/

section Relations

variable {K : Type w} [CommRing K]

local notation "Ψ" => Psi RD i b q hq

theorem Ψ_sub_eq {μ : ℤ} {s t : List (Letter Unit)} {f g : LinDiagram K (ob S2 μ s) (ob S2 μ t)}
    {f' g' : LinDiagram K (ob RD (sw RD i b q μ) (s.map (sl i))) (ob RD (sw RD i b q μ) (t.map (sl i)))}
    (hf : Ψ f = f') (hg : Ψ g = g') : Ψ (f - g) = f' - g' := by
  rw [Ψ_sub, hf, hg]

theorem Ψ_add_eq {μ : ℤ} {s t : List (Letter Unit)} {f g : LinDiagram K (ob S2 μ s) (ob S2 μ t)}
    {f' g' : LinDiagram K (ob RD (sw RD i b q μ) (s.map (sl i))) (ob RD (sw RD i b q μ) (t.map (sl i)))}
    (hf : Ψ f = f') (hg : Ψ g = g') : Ψ (f + g) = f' + g' := by
  rw [Ψ_add, hf, hg]

theorem Ψ_of_comp_eq {μ : ℤ} {s r t : List (Letter Unit)} {d : ob S2 μ s ⟶ ob S2 μ r}
    {e : ob S2 μ r ⟶ ob S2 μ t}
    {d' : ob RD (sw RD i b q μ) (s.map (sl i)) ⟶ ob RD (sw RD i b q μ) (r.map (sl i))}
    {e' : ob RD (sw RD i b q μ) (r.map (sl i)) ⟶ ob RD (sw RD i b q μ) (t.map (sl i))}
    (hd : Ψ (LinDiagram.of d : LinDiagram K _ _) = LinDiagram.of d')
    (he : Ψ (LinDiagram.of e : LinDiagram K _ _) = LinDiagram.of e') :
    Ψ (LinDiagram.of (d ≫ e) : LinDiagram K _ _) = LinDiagram.of (d' ≫ e') := by
  rw [LinDiagram.of_comp, Ψ_comp, hd, he, LinDiagram.of_comp]

variable (K)

theorem Ψ_rel_cycDotR (u : Unit) (μ : ℤ) :
    Ψ (relation K (.cycDotR u μ : Rel S2)) = relation K (.cycDotR i (sw RD i b q μ) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_rotDotR RD i b q hq K u μ) (Ψ_downDot RD i b q hq K u μ)

theorem Ψ_rel_cycDotL (u : Unit) (μ : ℤ) :
    Ψ (relation K (.cycDotL u μ : Rel S2)) = relation K (.cycDotL i (sw RD i b q μ) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_rotDotL RD i b q hq K u μ) (Ψ_downDot RD i b q hq K u μ)

theorem Ψ_rel_cycCrossR (u u' : Unit) (μ : ℤ) :
    Ψ (relation K (.cycCrossR u u' μ : Rel S2)) =
      relation K (.cycCrossR i i (sw RD i b q μ) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_rotCrossR RD i b q hq K u u' μ) (Ψ_downCross RD i b q hq K u u' μ)

theorem Ψ_rel_cycCrossL (u u' : Unit) (μ : ℤ) :
    Ψ (relation K (.cycCrossL u u' μ : Rel S2)) =
      relation K (.cycCrossL i i (sw RD i b q μ) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_rotCrossL RD i b q hq K u u' μ) (Ψ_downCross RD i b q hq K u u' μ)

theorem Ψ_rel_cwNeg (u : Unit) (lam : ℤ) (α : ℕ) (h : (α : ℤ) < ip S2 u lam - 1)
    (h' : (α : ℤ) < ip RD i (sw RD i b q lam) - 1) :
    Ψ (relation K (.cwNeg u lam α h : Rel S2)) =
      relation K (.cwNeg i (sw RD i b q lam) α h' : Rel RD) :=
  Ψ_cwReal RD i b q hq K lam u α

theorem Ψ_rel_ccwNeg (u : Unit) (lam : ℤ) (α : ℕ) (h : (α : ℤ) < -ip S2 u lam - 1)
    (h' : (α : ℤ) < -ip RD i (sw RD i b q lam) - 1) :
    Ψ (relation K (.ccwNeg u lam α h : Rel S2)) =
      relation K (.ccwNeg i (sw RD i b q lam) α h' : Rel RD) :=
  Ψ_ccwReal RD i b q hq K lam u α

theorem Ψ_rel_cwOne (u : Unit) (lam : ℤ) (h : 1 ≤ ip S2 u lam)
    (h' : 1 ≤ ip RD i (sw RD i b q lam)) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (relation K (.cwOne u lam h : Rel S2)) =
      relation K (.cwOne i (sw RD i b q lam) h' : Rel RD) := by
  refine Ψ_sub_eq RD i b q hq ?_ (Ψ_of_id RD i b q hq)
  show Ψ (LinDiagram.of (cwReal S2 lam u (ip S2 u lam - 1).toNat)) =
    LinDiagram.of (cwReal RD (sw RD i b q lam) i (ip RD i (sw RD i b q lam) - 1).toNat)
  rw [hip, ip_S2]
  exact Ψ_cwReal RD i b q hq K lam u _

theorem Ψ_rel_ccwOne (u : Unit) (lam : ℤ) (h : ip S2 u lam ≤ -1)
    (h' : ip RD i (sw RD i b q lam) ≤ -1) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (relation K (.ccwOne u lam h : Rel S2)) =
      relation K (.ccwOne i (sw RD i b q lam) h' : Rel RD) := by
  refine Ψ_sub_eq RD i b q hq ?_ (Ψ_of_id RD i b q hq)
  show Ψ (LinDiagram.of (ccwReal S2 lam u (-ip S2 u lam - 1).toNat)) =
    LinDiagram.of (ccwReal RD (sw RD i b q lam) i (-ip RD i (sw RD i b q lam) - 1).toNat)
  rw [hip, ip_S2]
  exact Ψ_ccwReal RD i b q hq K lam u _

theorem Ψ_rel_curlR (u : Unit) (lam : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (relation K (.curlR u lam : Rel S2)) = relation K (.curlR i (sw RD i b q lam) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_curlR RD i b q hq K u lam) (Ψ_curlRHS RD i b q hq K u lam hip)

theorem Ψ_rel_curlL (u : Unit) (μ : ℤ)
    (hip : ip RD i (sw RD i b q (wt S2 μ [up u])) = wt S2 μ [up u]) :
    Ψ (relation K (.curlL u μ : Rel S2)) = relation K (.curlL i (sw RD i b q μ) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_curlL RD i b q hq K u μ) (Ψ_curlLHS RD i b q hq K u μ hip)

theorem Ψ_rel_decompEF (u : Unit) (lam : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (relation K (.decompEF u lam : Rel S2)) =
      relation K (.decompEF i (sw RD i b q lam) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_add_eq RD i b q hq (Ψ_of_id RD i b q hq)
      (Ψ_of_comp_eq RD i b q hq (Ψ_crossl RD i b q hq K u u lam) (Ψ_crossr RD i b q hq K u u lam)))
    (Ψ_decompEFSum RD i b q hq K u lam hip)

theorem Ψ_rel_decompFE (u : Unit) (lam : ℤ) (hip : ip RD i (sw RD i b q lam) = lam) :
    Ψ (relation K (.decompFE u lam : Rel S2)) =
      relation K (.decompFE i (sw RD i b q lam) : Rel RD) :=
  Ψ_sub_eq RD i b q hq (Ψ_add_eq RD i b q hq (Ψ_of_id RD i b q hq)
      (Ψ_of_comp_eq RD i b q hq (Ψ_crossr RD i b q hq K u u lam) (Ψ_crossl RD i b q hq K u u lam)))
    (Ψ_decompFESum RD i b q hq K u lam hip)

theorem Ψ_upDiag' {μ : ℤ} (c : List Unit) {c' : List I} (hc : (ups c).map (sl i) = ups c')
    (d : KLR.Diagram.ob c ⟶ KLR.Diagram.ob c) (d' : KLR.Diagram.ob c' ⟶ KLR.Diagram.ob c')
    (hd : Diagram.layers d' = (Diagram.layers d).map (klrS i).layer) :
    Ψ (upLin S2 K μ (LinDiagram.of d)) =
      LinDiagram.cast (upLin RD K (sw RD i b q μ) (LinDiagram.of d'))
        (congrArg (ob RD (sw RD i b q μ)) hc).symm (congrArg (ob RD (sw RD i b q μ)) hc).symm := by
  rw [upLin_of, upLin_of]
  exact Ψ_upDiag RD i b q hq K d d' hd hc hc

open KLR.Diagram in
theorem Ψ_rel_klr_sqEq (u : Unit) (μ : ℤ) :
    Ψ (relation K (.klr μ (.sqEq u) : Rel S2)) =
      relation K (.klr (sw RD i b q μ) (.sqEq i) : Rel RD) := by
  show Ψ (upLin S2 K μ (LinDiagram.of (X2 u u ≫ X2 u u))) =
    upLin RD K (sw RD i b q μ) (LinDiagram.of (X2 i i ≫ X2 i i))
  rw [Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (X2 i i ≫ X2 i i) rfl]
  exact linCast_self _ _ _

open KLR.Diagram in
theorem Ψ_rel_klr_slideLEq (u : Unit) (μ : ℤ) :
    Ψ (relation K (.klr μ (.slideLEq u) : Rel S2)) =
      relation K (.klr (sw RD i b q μ) (.slideLEq i) : Rel RD) := by
  simp only [relation, KLR.Diagram.relation]
  erw [upLin_sub, upLin_sub, upLin_sub, upLin_sub, Ψ_sub, Ψ_sub,
    Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (X2 i i ≫ D0 i i) rfl,
    Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (D1 i i ≫ X2 i i) rfl,
    Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (𝟙 _) rfl, linCast_self, linCast_self, linCast_self]
  try rfl

open KLR.Diagram in
theorem Ψ_rel_klr_slideREq (u : Unit) (μ : ℤ) :
    Ψ (relation K (.klr μ (.slideREq u) : Rel S2)) =
      relation K (.klr (sw RD i b q μ) (.slideREq i) : Rel RD) := by
  simp only [relation, KLR.Diagram.relation]
  erw [upLin_sub, upLin_sub, upLin_sub, upLin_sub, Ψ_sub, Ψ_sub,
    Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (D0 i i ≫ X2 i i) rfl,
    Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (X2 i i ≫ D1 i i) rfl,
    Ψ_upDiag' RD i b q hq K [u, u] (c' := [i, i]) rfl _ (𝟙 _) rfl, linCast_self, linCast_self, linCast_self]
  try rfl

open KLR.Diagram in
theorem Ψ_rel_klr_braid (u : Unit) (μ : ℤ) (h : ¬ (u = u ∧ u ≠ u)) (h' : ¬ (i = i ∧ i ≠ i)) :
    Ψ (relation K (.klr μ (.braid u u u h) : Rel S2)) =
      relation K (.klr (sw RD i b q μ) (.braid i i i h') : Rel RD) := by
  simp only [relation, KLR.Diagram.relation]
  erw [upLin_sub, upLin_sub, Ψ_sub,
    Ψ_upDiag' RD i b q hq K [u, u, u] (c' := [i, i, i]) rfl _ (braidL i i i) rfl,
    Ψ_upDiag' RD i b q hq K [u, u, u] (c' := [i, i, i]) rfl _ (braidR i i i) rfl, linCast_self, linCast_self]
  rfl

end Relations

end Categorification.KL3.Diagram.StringEmbed

end
