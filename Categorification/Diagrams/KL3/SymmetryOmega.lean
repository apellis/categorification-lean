/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Rotation
import Categorification.Diagrams.KL3.Symmetries
import Categorification.Diagrams.KL3.SpanningBasic

/-!
# The symmetry `ω̃` of `U`: inversion of orientations

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(TeX label `sec_symm`), paragraph "Rescale, invert the orientation, and send `λ ↦ -λ`",
eq. (3.43), and the relations (3.45).

KL III: "Consider the operation on the diagrammatic calculus that rescales the `ii`-crossing
`ψ_{i,i,λ} ↦ -ψ_{i,i,λ}` for all `i ∈ I` and `λ ∈ X`, inverts the orientation of each strand and
sends `λ ↦ -λ` [...] This transformation preserves the degree of a diagram, so by extending to
sums of diagrams we get a 2-functor `ω̃ : U → U`, `λ ↦ -λ`,
`1_μ E_s 1_λ {t} ↦ 1_{-μ} E_{-s} 1_{-λ} {t}`. It is straight forward to check that `ω̃` is a strict
2-functor. In fact, it is a 2-isomorphism since its square is the identity."

## Conventions

A strand `⟨l, r⟩` (letter `l`, right region `r`) goes to `⟨l*, -r⟩` (`Omega.col`); words keep
their order (`Omega.word`), objects are read from the negated left region (`Omega.obj`). On
generators (`Omega.gen`, on shapes `Omega.shape`): the dot on `l` goes to the dot on `l*`, the
crossing `(ε,i)(ε,j) ⟶ (ε,j)(ε,i)` goes to `(-ε,i)(-ε,j) ⟶ (-ε,j)(-ε,i)`, the cup
`1 ⟶ l l*` to the cup `1 ⟶ l* l`, the cap `l* l ⟶ 1` to the cap `l l* ⟶ 1`; a diagram is
multiplied by `(-1)` to the number of its crossings of two strands with the same label
(`Sig.sgn`; KL III rescale the upward `ii`-crossing, and hence, by the cyclicity relation
`eq_cyclic_cross-gen`, the downward one: both are rescaled here).

## Construction

`ω̃` is `Presentation.lift` of the signed orientation reversal `omegaFree` of the free
2-category. The zigzag relations and the interchange law are mapped to zigzag relations and
the interchange law. For the other relations of Definition 3.1 the images are relations on
strands of the opposite orientation (downward KLR relations, downward curl relations, the
sideways crossings described by downward crossings, …), which are not relations of the
presentation. We check them all at once: **on diagrams, `ω̃` agrees with the composite
`ψ̃ ∘ τ ∘ σ̃`** (`omegaL_eq_phi`) of the reflection `σ̃` in a vertical axis, the rotation `τ` by
`180°` (the mate for the nested cups and caps, `rotU`, `rotU_dg`) and the reflection `ψ̃` in a
horizontal axis: this is KL III's remark that `ψ̃ ω̃ σ̃` is "given by rotating diagrams by `180°`".
As `σ̃`, `τ` and `ψ̃` are well defined on `U`, every relation is mapped to zero.

## Main results

* `omegaU RD k : (pres RD k).Presented ⥤ (pres RD k).Presented`, `k`-linear; `omegaU_diag`,
  `omegaU_dg` (normal forms), `omegaU_whisk` (a strict 2-functor);
* `omegaU_omegaU`: `ω̃² = 1`;
* `omegaU_sigU`, `omegaU_psiU`: `ω̃ σ̃ = σ̃ ω̃` and `ω̃ ψ̃ = ψ̃ ω̃` (KL III (3.45); the first equality
  is printed `ω̃σ̃ = ω̃σ̃`, evidently a typo);
* `omegaU_homDeg`: `ω̃` preserves degrees;
* `omegaU_cwU`, `omegaU_ccwU`: `ω̃` exchanges clockwise and counterclockwise bubbles (real and
  fake) with the same label, `λ ↦ -λ`;
* `downFunctor`, `downFunctor_diag`, `downFunctor_dot`, `downFunctor_cross`: **the relations of
  `R(ν)` hold on downward strands** (with the crossings of equally labelled strands rescaled by
  `-1`): `ω̃ ∘ ϕ` is a functor out of the diagrammatic KLR category;
* `dg_curlR_down`: **the right curl relation on a downward strand**, the `ω̃`-image of the right
  curl relation of Definition 3.1 iv).

## Interpretation

KL III rescale "the `ii`-crossing `ψ_{i,i,λ}`", drawn upward. On diagrams containing downward
crossings we rescale the downward `ii`-crossings as well; this is forced, since the downward
crossing is the rotation of the upward one (`eq_cyclic_cross-gen`), and it is what makes `ω̃`
agree with `ψ̃ τ σ̃` (whose sign comes from `σ̃` alone).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

namespace Omega

variable {RD}

/-! ## Inversion of colours, words, objects, generators and layers -/

/-- A region of `psig RD`, as a weight. -/
abbrev rX (r : (psig RD).Region) : X := r

/-- The colour with inverted orientation: `⟨l, r⟩ ↦ ⟨l*, -r⟩`. -/
def col (c : Col I X) : Col I X := ⟨c.l.dual, -c.r⟩

/-- The word with inverted orientations (same order). -/
def word (w : List (Col I X)) : List (Col I X) := w.map col

@[simp] theorem word_nil : word ([] : List (Col I X)) = [] := rfl

theorem word_cons (c : Col I X) (w : List (Col I X)) :
    word (c :: w) = col c :: word w := rfl

theorem word_append (w w' : List (Col I X)) :
    word (w ++ w') = word w ++ word w' := List.map_append

theorem col_col (c : Col I X) : col (col c) = c := by
  obtain ⟨l, r⟩ := c
  simp [col]

theorem word_word (w : List (Col I X)) : word (word w) = w := by
  simp [word, List.map_map, Function.comp_def, col_col]

theorem col_src (c : Col I X) : (psig RD).colourSrc (col c) = -(sh RD c.l + c.r) := by
  show sh RD c.l.dual + -c.r = -(sh RD c.l + c.r)
  rw [sh_dual]; abel

theorem ok_word (r : X) (w : List (Col I X)) (h : (psig RD).ok r w) :
    (psig RD).ok (-r) (word w) ∧
      (psig RD).endR (-r) (word w) = (-Sig.eR (RD := RD) r w : X) := by
  induction w generalizing r with
  | nil => exact ⟨trivial, rfl⟩
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    obtain ⟨ih₁, ih₂⟩ := ih c.r hw
    refine ⟨⟨?_, ih₁⟩, ih₂⟩
    show (psig RD).colourSrc (col c) = -r
    rw [col_src]; exact congrArg (fun x : X => -x) hc

theorem inv_dual_col (c : Col I X) : (inv RD).dual (col c) = col ((inv RD).dual c) := by
  rw [inv_dual, inv_dual]
  refine Col.ext rfl ?_
  show sh RD c.l.dual + -c.r = -(sh RD c.l + c.r)
  rw [sh_dual]; abel

variable (RD) in
/-- The object with inverted orientations. -/
def obj (a : Obj (psig RD)) : Obj (psig RD) := ⟨-rX a.start, word a.word⟩

@[simp] theorem obj_start (a : Obj (psig RD)) : (obj RD a).start = -rX a.start := rfl
@[simp] theorem obj_word (a : Obj (psig RD)) : (obj RD a).word = word a.word := rfl

theorem obj_obj (a : Obj (psig RD)) : obj RD (obj RD a) = a :=
  Obj.ext (neg_neg (rX a.start)) (word_word _)

/-- The generator with inverted orientation and `λ ↦ -λ`. -/
def gen : (psig RD).Gen → (psig RD).Gen
  | .gen (.dot c) => .gen (.dot (col c))
  | .gen (.cross ε i j ν) => .gen (.cross (!ε) i j (-ν))
  | .cup c => .cup (col c)
  | .cap c => .cap (col c)

theorem gen_gen (g : (psig RD).Gen) : gen (gen g) = g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · show PivotalGen.gen (Gen0.dot (col (col c))) = _
    rw [col_col]
  · show PivotalGen.gen (Gen0.cross (!!ε) i j (- -ν)) = _
    rw [Bool.not_not, neg_neg]
  · show PivotalGen.cup (col (col c)) = _
    rw [col_col]
  · show PivotalGen.cap (col (col c)) = _
    rw [col_col]

theorem sh_not (ε : Bool) (i : I) : sh RD (!ε, i) = -sh RD (ε, i) := sh_dual RD (ε, i)

theorem gen_left (g : (psig RD).Gen) : (psig RD).left (gen g) = (-Sig.lR (RD := RD) g : X) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · exact col_src c
  · show sh RD (!ε, i) + (sh RD (!ε, j) + -ν) = -(sh RD (ε, i) + (sh RD (ε, j) + ν))
    rw [sh_not, sh_not]; abel
  · exact col_src c
  · rfl

theorem gen_right (g : (psig RD).Gen) :
    (psig RD).right (gen g) = (-Sig.rR (RD := RD) g : X) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · exact col_src c
  · rfl

theorem gen_dom (g : (psig RD).Gen) : (psig RD).dom (gen g) = word ((psig RD).dom g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨(!ε, i), sh RD (!ε, j) + -ν⟩ : Col I X), ⟨(!ε, j), -ν⟩] =
      [⟨(!ε, i), -(sh RD (ε, j) + ν)⟩, ⟨(!ε, j), -ν⟩]
    rw [sh_not]; congr 2; abel
  · rfl
  · show [(inv RD).dual (col c), col c] = [col ((inv RD).dual c), col c]
    rw [inv_dual_col]

theorem gen_cod (g : (psig RD).Gen) : (psig RD).cod (gen g) = word ((psig RD).cod g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨(!ε, j), sh RD (!ε, i) + -ν⟩ : Col I X), ⟨(!ε, i), -ν⟩] =
      [⟨(!ε, j), -(sh RD (ε, i) + ν)⟩, ⟨(!ε, i), -ν⟩]
    rw [sh_not]; congr 2; abel
  · show [col c, (inv RD).dual (col c)] = [col c, col ((inv RD).dual c)]
    rw [inv_dual_col]
  · rfl

theorem deg_gen (g : (psig RD).Gen) : deg RD (gen g) = deg RD g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · obtain ⟨⟨s, i⟩, r⟩ := c
    show di C i * (1 - sgn (!s) * RD.pair (RD.iY i) (sh RD (!s, i) + -r)) =
      di C i * (1 - sgn s * RD.pair (RD.iY i) (sh RD (s, i) + r))
    rw [sh_not]
    cases s <;> simp only [Bool.not_false, Bool.not_true, sgn_true, sgn_false, map_add, map_neg] <;>
      ring
  · obtain ⟨⟨s, i⟩, r⟩ := c
    show di C i * (1 + sgn (!s) * RD.pair (RD.iY i) (-r)) =
      di C i * (1 + sgn s * RD.pair (RD.iY i) r)
    cases s <;> simp only [Bool.not_false, Bool.not_true, sgn_true, sgn_false, map_neg] <;> ring

/-- The layer with inverted orientations. -/
def rlay (L : Layer (psig RD)) : Layer (psig RD) :=
  ⟨-rX L.start, word L.left, gen L.gen, word L.right⟩

theorem rlay_rlay (L : Layer (psig RD)) : rlay (rlay L) = L :=
  Layer.ext (neg_neg (rX L.start)) (word_word _) (gen_gen _) (word_word _)

theorem rlay_valid {L : Layer (psig RD)} (hv : L.Valid) : (rlay L).Valid := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hv
  refine ⟨(ok_word _ _ h₁).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (psig RD).endR (-rX L.start) (word L.left) = (psig RD).left (gen L.gen)
    rw [(ok_word _ _ h₁).2, gen_left]; exact congrArg (fun x : X => -x) h₂
  · show (psig RD).ok ((psig RD).left (gen L.gen)) ((psig RD).dom (gen L.gen))
    rw [gen_left, gen_dom]; exact (ok_word _ _ h₃).1
  · show (psig RD).endR ((psig RD).left (gen L.gen)) ((psig RD).dom (gen L.gen)) =
      (psig RD).right (gen L.gen)
    rw [gen_left, gen_dom, gen_right, (ok_word _ _ h₃).2]; exact congrArg (fun x : X => -x) h₄
  · show (psig RD).ok ((psig RD).left (gen L.gen)) ((psig RD).cod (gen L.gen))
    rw [gen_left, gen_cod]; exact (ok_word _ _ h₅).1
  · show (psig RD).endR ((psig RD).left (gen L.gen)) ((psig RD).cod (gen L.gen)) =
      (psig RD).right (gen L.gen)
    rw [gen_left, gen_cod, gen_right, (ok_word _ _ h₅).2]; exact congrArg (fun x : X => -x) h₆
  · show (psig RD).ok ((psig RD).right (gen L.gen)) (word L.right)
    rw [gen_right]; exact (ok_word _ _ h₇).1

theorem rlay_dom (L : Layer (psig RD)) : (rlay L).dom = obj RD L.dom :=
  Obj.ext rfl (by simp only [Layer.dom_word, rlay, obj_word, gen_dom, word, List.map_append])

theorem rlay_cod (L : Layer (psig RD)) : (rlay L).cod = obj RD L.cod :=
  Obj.ext rfl (by simp only [Layer.cod_word, rlay, obj_word, gen_cod, word, List.map_append])

theorem rlay_whisker (L : Layer (psig RD)) (u : Obj (psig RD)) (v : List (psig RD).Colour) :
    rlay (L.whisker u v) = (rlay L).whisker (obj RD u) (word v) := by
  simp only [rlay, Layer.whisker, word, List.map_append, obj_start, obj_word]

theorem chain_map {a b : Obj (psig RD)} {ls : List (Layer (psig RD))} (h : Chain a ls b) :
    Chain (obj RD a) (ls.map rlay) (obj RD b) := by
  induction ls generalizing a with
  | nil => exact congrArg (obj RD) h
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨rlay_valid hv, rlay_dom L, by rw [rlay_cod]; exact ih hc⟩

/-- The diagram with inverted orientations. -/
def reflD {a b : Obj (psig RD)} (d : a ⟶ b) : obj RD a ⟶ obj RD b :=
  Diagram.mk ((Diagram.layers d).map rlay) (chain_map (Diagram.chain d))

@[simp] theorem layers_reflD {a b : Obj (psig RD)} (d : a ⟶ b) :
    Diagram.layers (reflD d) = (Diagram.layers d).map rlay := rfl

theorem reflD_id (a : Obj (psig RD)) : reflD (𝟙 a) = 𝟙 (obj RD a) := rfl

theorem reflD_comp {a b c : Obj (psig RD)} (f : a ⟶ b) (g : b ⟶ c) :
    reflD (f ≫ g) = reflD f ≫ reflD g := by
  apply Diagram.ext; simp

theorem degree_reflD {a b : Obj (psig RD)} (d : a ⟶ b) :
    Diagram.degree (deg RD) (reflD d) = Diagram.degree (deg RD) d := by
  simp only [Diagram.degree, layers_reflD, List.map_map, Function.comp_def, rlay, deg_gen]

theorem whiskerOK_obj {a u : Obj (psig RD)} {v : List (psig RD).Colour} (ha : a.WF)
    (hw : a.WhiskerOK u v) : (obj RD a).WhiskerOK (obj RD u) (word v) := by
  obtain ⟨hu, hue, hv⟩ := hw
  refine ⟨(ok_word _ _ hu).1, ?_, ?_⟩
  · show (psig RD).endR (-rX u.start) (word u.word) = (-rX a.start : X)
    rw [(ok_word _ _ hu).2]; exact congrArg (fun x : X => -x) hue
  · show (psig RD).ok ((psig RD).endR (-rX a.start) (word a.word)) (word v)
    rw [(ok_word _ _ ha).2]; exact (ok_word _ _ hv).1

theorem obj_whisker (a u : Obj (psig RD)) (v : List (psig RD).Colour) :
    (obj RD a).whisker (obj RD u) (word v) = obj RD (a.whisker u v) :=
  Obj.ext rfl (by simp [Obj.whisker, word, List.map_append, List.append_assoc])

theorem reflD_whisker {a b : Obj (psig RD)} (d : a ⟶ b) (ha : a.WF) {u : Obj (psig RD)}
    {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    reflD (Diagram.whisker d u v hw) =
      Diagram.cast (Diagram.whisker (reflD d) (obj RD u) (word v) (whiskerOK_obj ha hw))
        (obj_whisker a u v) (obj_whisker b u v) := by
  apply Diagram.ext
  simp only [layers_reflD, Diagram.layers_whisker, Diagram.layers_cast, List.map_map]
  refine List.map_congr_left fun L _ => ?_
  simp only [Function.comp_apply, rlay_whisker]

variable [DecidableEq I]

theorem sgnG_gen (g : (psig RD).Gen) : Sig.sgnG (gen g) = Sig.sgnG g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c <;> rfl

theorem sgn_map_rlay (ls : List (Layer (psig RD))) : Sig.sgn (ls.map rlay) = Sig.sgn ls := by
  simp only [Sig.sgn, List.map_map, Function.comp_def, rlay, sgnG_gen]

/-! ## Normal forms -/

omit [DecidableEq I] in
theorem wt_map_dual (μ : X) (t : List (Letter I)) :
    wt RD (-μ) (t.map Letter.dual) = -wt RD μ t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih, sh_dual]; abel

omit [DecidableEq I] in
theorem word_wd (μ : X) (t : List (Letter I)) : word (wd RD μ t) = wd RD (-μ) (t.map Letter.dual) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [wd_cons, word_cons, ih, List.map_cons, wd_cons, wt_map_dual (RD := RD)]
    rfl

omit [DecidableEq I] in
/-- The object `E_t 1_μ` with inverted orientations, in normal form: `E_{t'} 1_{-μ}` with the
dual letters `t' = t.map dual` in the same order. -/
theorem trO (μ : X) (t : List (Letter I)) :
    obj RD (ob RD μ t) = ob RD (-μ) (t.map Letter.dual) :=
  Obj.ext (wt_map_dual μ t).symm (word_wd μ t)

/-- The shape of a generator with inverted orientation. -/
def shape : Shape I → Shape I
  | .dot l => .dot l.dual
  | .cross ε i j => .cross (!ε) i j
  | .cup l => .cup l.dual
  | .cap l => .cap l.dual

omit [DecidableEq I] in
theorem shape_dom (g : Shape I) : (shape g).dom = g.dom.map Letter.dual := by
  cases g <;> simp [shape]

omit [DecidableEq I] in
theorem shape_cod (g : Shape I) : (shape g).cod = g.cod.map Letter.dual := by
  cases g <;> simp [shape]

omit [DecidableEq I] in
theorem gen_shape (ν : X) (g : Shape I) : gen (g.gen RD ν) = (shape g).gen RD (-ν) := by
  cases g with
  | dot l => rfl
  | cross ε i j => rfl
  | cup l =>
    show PivotalGen.cup (col ⟨l, sh RD l.dual + ν⟩) = PivotalGen.cup ⟨l.dual, sh RD l.dual.dual + -ν⟩
    congr 1
    refine Col.ext rfl ?_
    show -(sh RD l.dual + ν) = sh RD l.dual.dual + -ν
    rw [Letter.dual_dual, sh_dual]; abel
  | cap l => rfl

/-- The inversion of a layer datum. -/
def ld (x : LayerData I) : LayerData I :=
  (x.1.map Letter.dual, shape x.2.1, x.2.2.map Letter.dual)

/-- The inversion of a normal-form list of layers (same order). -/
def wls (ls : List (LayerData I)) : List (LayerData I) := ls.map ld

omit [DecidableEq I] in
theorem sChain_wls {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    SChain (s.map Letter.dual) (wls ls) (t.map Letter.dual) := by
  induction ls generalizing s with
  | nil => exact congrArg (List.map Letter.dual) h
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [ld, shape_dom], ?_⟩
    have := ih h
    simpa [ld, shape_cod] using this

omit [DecidableEq I] in
theorem rlay_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    rlay (lay RD μ u g v) =
      lay RD (-μ) (u.map Letter.dual) (shape g) (v.map Letter.dual) := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · show -wt RD μ (u ++ g.dom ++ v) = wt RD (-μ) (u.map Letter.dual ++ (shape g).dom ++
      v.map Letter.dual)
    rw [shape_dom, ← List.map_append, ← List.map_append, wt_map_dual]
  · show word (wd RD (wt RD μ (g.dom ++ v)) u) =
      wd RD (wt RD (-μ) ((shape g).dom ++ v.map Letter.dual)) (u.map Letter.dual)
    rw [word_wd, shape_dom, ← List.map_append, wt_map_dual]
  · show gen (g.gen RD (wt RD μ v)) = (shape g).gen RD (wt RD (-μ) (v.map Letter.dual))
    rw [wt_map_dual, gen_shape]
  · exact word_wd μ v

omit [DecidableEq I] in
theorem layers_reflD_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) : Diagram.layers (reflD (mkD RD μ ls h)) = layList RD (-μ) (wls ls) := by
  simp only [layers_reflD, layers_mkD, layList, wls, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, rlay_lay, ld]

theorem sgnSh_shape (g : Shape I) : Sig.sgnSh (shape g) = Sig.sgnSh g := by
  cases g <;> rfl

theorem sgnS_wls (ls : List (LayerData I)) : Sig.sgnS (wls ls) = Sig.sgnS ls := by
  simp only [Sig.sgnS, wls, List.map_map, Function.comp_def, ld, sgnSh_shape]

end Omega

open Omega

/-! ## The inversion functor on the free 2-category -/

section Signed

variable [DecidableEq I]

/-- The signed inversion of orientations on the free 2-category. -/
def omegaFree : Obj (psig RD) ⥤ (pres RD k).Presented where
  obj a := (pres RD k).obj (Omega.obj RD a)
  map d := ((Sig.sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (Omega.reflD d)
  map_id a := by
    rw [Diagram.layers_id, Sig.sgn_nil, Int.cast_one, one_smul, Omega.reflD_id,
      Presentation.diag_id]
  map_comp f g := by
    rw [Diagram.layers_comp, Sig.sgn_append, Omega.reflD_comp, Presentation.diag_comp, Int.cast_mul,
      Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

/-- The signed inversion of linear combinations of diagrams, in `U`. -/
abbrev omegaL {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k).obj (Omega.obj RD a) ⟶ (pres RD k).obj (Omega.obj RD b) :=
  (freeLift k (omegaFree RD k)).map f

variable {RD k}

theorem omegaL_of {a b : Obj (psig RD)} (d : a ⟶ b) :
    omegaL RD k (LinDiagram.of d) =
      ((Sig.sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (Omega.reflD d) :=
  freeLift_map_of _ d

theorem omegaL_zero {a b : Obj (psig RD)} : omegaL RD k (0 : LinDiagram k a b) = 0 :=
  Functor.map_zero _ _ _

theorem omegaL_add {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    omegaL RD k (f + g) = omegaL RD k f + omegaL RD k g := Functor.map_add _

theorem omegaL_sub {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    omegaL RD k (f - g) = omegaL RD k f - omegaL RD k g := Functor.map_sub _

theorem omegaL_smul {a b : Obj (psig RD)} (r : k) (f : LinDiagram k a b) :
    omegaL RD k (r • f) = r • omegaL RD k f := Functor.map_smul _ _ _

theorem omegaL_comp {a b c : Obj (psig RD)} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    omegaL RD k (f ≫ g) = omegaL RD k f ≫ omegaL RD k g := Functor.map_comp _ _ _

theorem omegaL_id (a : Obj (psig RD)) : omegaL RD k (𝟙 (Free.of k a)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

theorem omegaL_single {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    omegaL RD k (Finsupp.single d r : (a ⟶ b) →₀ k) =
      r • ((Sig.sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (Omega.reflD d) :=
  freeLift_map_single _ d r

/-- `ω̃` on a normal-form diagram. -/
theorem omegaL_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) :
    omegaL RD k (LinDiagram.of (mkD RD μ ls h)) =
      ((Sig.sgnS ls : ℤ) : k) • TR RD k (Omega.trO μ s) (Omega.trO μ t)
        (dg RD k (-μ) (s.map Letter.dual) (t.map Letter.dual) (wls ls)) := by
  rw [omegaL_of, layers_mkD, Sig.sgn_layList, dg_of (sChain_wls h), TR_diag]
  congr 1
  apply (pres RD k).diag_eq_of_layers_eq
  rw [Diagram.layers_cast]
  exact Omega.layers_reflD_mkD (RD := RD) μ ls h

end Signed

/-! ## `ω̃ = ψ̃ ∘ τ ∘ σ̃` on diagrams -/

section Phi

variable [DecidableEq I] {RD k}

variable (RD k) in
/-- `σ̃` on morphisms of `U`, as a `k`-linear map. -/
def sigLin (a b : Obj (psig RD)) :
    ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Sig.obj RD a) ⟶ (pres RD k).obj (Sig.obj RD b)) where
  toFun f := (sigU RD k).map f
  map_add' _ _ := Functor.map_add _
  map_smul' _ _ := Functor.map_smul _ _ _

variable (RD k) in
/-- `ψ̃` on morphisms of `U`, as a `k`-linear map. -/
def psiUnop (a b : Obj (psig RD)) :
    ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k] ((pres RD k).obj b ⟶ (pres RD k).obj a) where
  toFun f := ((psiU RD k).map f).unop
  map_add' f g := by rw [Functor.map_add, unop_add]
  map_smul' r f := by rw [Functor.map_smul, unop_smul']; rfl

omit [DecidableEq I] in
theorem rd_reverse (t : List (Letter I)) : rd t.reverse = t.map Letter.dual := by
  simp [rd, List.map_reverse]

omit [DecidableEq I] in
theorem wt_neg_reverse (μ : X) (s t : List (Letter I)) (hst : wt RD μ s = wt RD μ t) :
    wt RD (-wt RD μ s) t.reverse = -μ := by
  rw [wt_eq_add_wX, Sig.wX_reverse, hst, wt_eq_add_wX]; abel

omit [DecidableEq I] in
theorem TR_TR {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b') (ea' : a' = a)
    (eb' : b' = b) (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    TR RD k ea eb (TR RD k ea' eb' f) = f := by
  subst ea eb; simp [TR_apply]

omit [DecidableEq I] in
theorem TR_dg (ν : X) {a a' b b' : List (Letter I)} (ha : a = a') (hb : b = b')
    (L : List (LayerData I)) :
    TR RD k (congrArg (ob RD ν) ha) (congrArg (ob RD ν) hb) (dg RD k ν a' b' L) = dg RD k ν a b L := by
  subst ha hb; exact TR_rfl _

omit [DecidableEq I] in
/-- The composite of the reflections in the two axes and the rotation by `180°`, on layers. -/
theorem rls_rotLs_sls (ls : List (LayerData I)) : Psi.rls (rotLs (Sig.sls ls)) = wls ls := by
  simp only [Psi.rls, rotLs, Sig.sls, wls, List.map_reverse, List.reverse_reverse, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨u, g, v⟩ := x
  simp only [Function.comp_apply, Sig.ld, rotLD, Psi.ld, Omega.ld, rd_reverse]
  congr 2
  cases g <;> simp [Omega.shape]

variable (RD k) in
/-- The composite `ψ̃ ∘ τ ∘ σ̃` on the morphisms `E_s 1_μ ⟶ E_t 1_μ`: the reflection `σ̃` in a
vertical axis, the rotation `τ` by `180°` (`rotU`) and the reflection `ψ̃` in a horizontal axis,
with the objects identified with normal forms. -/
def phiU (μ : X) (s t : List (Letter I)) (hst : wt RD μ s = wt RD μ t) :
    ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) →ₗ[k]
      ((pres RD k).obj (ob RD (-μ) (s.map Letter.dual)) ⟶
        (pres RD k).obj (ob RD (-μ) (t.map Letter.dual))) :=
  (TR RD k (congrArg (ob RD (-μ)) (rd_reverse s).symm)
      (congrArg (ob RD (-μ)) (rd_reverse t).symm)).comp
    ((psiUnop RD k _ _).comp
      ((rotU RD k (-wt RD μ s) (-μ) s.reverse t.reverse (wt_neg_reverse μ s s rfl)
          (wt_neg_reverse μ s t hst)).comp
        ((TR RD k (Sig.trO μ _ s rfl).symm (Sig.trO μ _ t (by rw [hst])).symm).comp
          (sigLin RD k _ _))))

theorem phiU_dg (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t)
    (hst : wt RD μ s = wt RD μ t) :
    phiU RD k μ s t hst (dg RD k μ s t ls) =
      ((Sig.sgnS ls : ℤ) : k) • dg RD k (-μ) (s.map Letter.dual) (t.map Letter.dual) (wls ls) := by
  simp only [phiU, LinearMap.comp_apply]
  have hσ : TR RD k (Sig.trO μ _ s rfl).symm (Sig.trO μ _ t (by rw [hst])).symm
      (sigLin RD k _ _ (dg RD k μ s t ls)) =
        ((Sig.sgnS ls : ℤ) : k) • dg RD k (-wt RD μ s) s.reverse t.reverse (Sig.sls ls) := by
    rw [show sigLin RD k _ _ (dg RD k μ s t ls) = (sigU RD k).map (dg RD k μ s t ls) from rfl,
      sigU_dg μ (-wt RD μ s) s.reverse t.reverse ls h rfl rfl rfl, map_smul]
    congr 1
    exact TR_TR _ _ _ _ _
  rw [hσ, map_smul, rotU_dg _ _ (Sig.sls ls) (Sig.sChain_sls h), map_smul, map_smul]
  congr 1
  show TR RD k _ _ ((psiU RD k).map (dg RD k (-μ) (rd t.reverse) (rd s.reverse)
    (rotLs (Sig.sls ls)))).unop = _
  rw [psiU_dg, Quiver.Hom.unop_op, rls_rotLs_sls]
  exact TR_dg (-μ) (rd_reverse s).symm (rd_reverse t).symm _

/-- **`ω̃` agrees with `ψ̃ ∘ τ ∘ σ̃`** on all linear combinations of diagrams between normal-form
objects (KL III: "The composite 2-functor `ψ̃ω̃σ̃` [...] is given on 2-morphisms by rotating
diagrams by `180°`"). -/
theorem omegaL_eq_phi (μ : X) {s t : List (Letter I)} (f : LinDiagram k (ob RD μ s) (ob RD μ t))
    (hst : wt RD μ s = wt RD μ t) :
    omegaL RD k f = TR RD k (Omega.trO μ s) (Omega.trO μ t)
      (phiU RD k μ s t hst ((pres RD k).lin f)) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [omegaL_zero, Presentation.lin_zero, map_zero, map_zero]
  | add f g hf hg => rw [omegaL_add, hf, hg, Presentation.lin_add, map_add, map_add]
  | single d r =>
    rw [omegaL_single, Presentation.lin_single, map_smul, map_smul, ← omegaL_of]
    obtain ⟨ls, h, rfl⟩ := exists_mkD RD μ d
    rw [← dg_of h, phiU_dg μ ls h hst, map_smul]
    congr 1
    exact omegaL_of_mkD μ ls h

omit [DecidableEq I] in
theorem isEmpty_hom_ob {μ : X} {s t : List (Letter I)} (hst : ¬ wt RD μ s = wt RD μ t) :
    IsEmpty (ob RD μ s ⟶ ob RD μ t) := by
  refine ⟨fun d => hst ?_⟩
  obtain ⟨ls, h, -⟩ := exists_mkD RD μ d
  exact (SChain.wt_eq RD μ h).symm

/-- `ω̃` kills every linear combination of diagrams between normal-form objects which vanishes in
`U`. -/
theorem omegaL_eq_zero_of_ob (μ : X) {s t : List (Letter I)}
    (f : LinDiagram k (ob RD μ s) (ob RD μ t)) (hf : (pres RD k).lin f = 0) :
    omegaL RD k f = 0 := by
  by_cases hst : wt RD μ s = wt RD μ t
  · rw [omegaL_eq_phi μ f hst, hf, map_zero, map_zero]
  · have := isEmpty_hom_ob (RD := RD) hst
    rw [show f = 0 from Finsupp.ext (α := ob RD μ s ⟶ ob RD μ t) fun d => (IsEmpty.false d).elim,
      omegaL_zero]

omit [DecidableEq I] in
theorem wf_eq_ob' : ∀ (st : X) (w : List (Col I X)), (psig RD).ok st w →
    (⟨st, w⟩ : Obj (psig RD)) = ob RD (Sig.eR (RD := RD) st w) (w.map Col.l)
  | _, [], _ => rfl
  | st, c :: w, ⟨hc, hw⟩ => by
    have := wf_eq_ob' c.r w hw
    simp only [ob, Obj.mk.injEq] at this
    refine Obj.ext ?_ ?_
    · show st = sh RD c.l + wt RD (Sig.eR (RD := RD) c.r w) (w.map Col.l)
      rw [← this.1]; exact hc.symm
    · show c :: w = ⟨c.l, wt RD (Sig.eR (RD := RD) c.r w) (w.map Col.l)⟩ ::
        wd RD (Sig.eR (RD := RD) c.r w) (w.map Col.l)
      rw [← this.1, ← this.2]

omit [DecidableEq I] in
/-- Every well-formed object is in normal form. -/
theorem wf_eq_ob (a : Obj (psig RD)) (ha : a.WF) :
    a = ob RD (Sig.eR (RD := RD) a.start a.word) (a.word.map Col.l) :=
  wf_eq_ob' (X := X) (RD := RD) a.start a.word ha

/-- `ω̃` kills every linear combination of diagrams starting at a well-formed object which
vanishes in `U`. -/
theorem omegaL_eq_zero_of_wf {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hf : (pres RD k).lin f = 0) : omegaL RD k f = 0 := by
  by_cases he : IsEmpty (a ⟶ b)
  · rw [show f = 0 from Finsupp.ext (α := a ⟶ b) fun d => (IsEmpty.false d).elim, omegaL_zero]
  obtain ⟨d⟩ := not_isEmpty_iff.1 he
  have hb := (Diagram.chain d).wf ha
  obtain ⟨μ, s, rfl⟩ : ∃ μ s, a = ob RD μ s := ⟨_, _, wf_eq_ob a ha⟩
  obtain ⟨ν, t, rfl⟩ : ∃ ν t, b = ob RD ν t := ⟨_, _, wf_eq_ob b hb⟩
  have e : ν = μ := by
    have := (Diagram.chain d).endR_eq
    rwa [ob_endR, ob_endR] at this
  subst e
  exact omegaL_eq_zero_of_ob ν f hf

end Phi

/-! ## The 2-functor `ω̃ : U → U` -/

section Functor

variable [DecidableEq I] {RD k}

omit [DecidableEq I] in
theorem whisker_wf {a u : Obj (psig RD)} {v : List (psig RD).Colour} (ha : a.WF)
    (hw : a.WhiskerOK u v) : (a.whisker u v).WF := by
  obtain ⟨hu, hue, hv⟩ := hw
  show (psig RD).ok u.start (u.word ++ a.word ++ v)
  rw [List.append_assoc, Signature.ok_append, Signature.ok_append]
  refine ⟨hu, ?_, ?_⟩
  · rw [show (psig RD).endR u.start u.word = a.start from hue]; exact ha
  · rw [show (psig RD).endR u.start u.word = a.start from hue]; exact hv

variable (RD k)

/-- The signed inversion of orientations on the free 2-category respects all the relations of
`U` and the interchange law: every whiskered relation vanishes in `U`, hence its image under
`ψ̃ ∘ τ ∘ σ̃` vanishes (`omegaL_eq_zero_of_wf`). -/
theorem omegaFree_respects : (pres RD k).Respects (omegaFree RD k) where
  rel r u v hw := omegaL_eq_zero_of_wf _ (whisker_wf (pres_dom_wf r) hw)
    ((pres RD k).lin_rel r u v hw)
  interchange x hx u v hw := by
    have hwf : x.dom.WF := by
      have := hx.gh₁.wf_dom
      simpa [Obj.WF, Layer.dom, InterchangeData.gh₁, InterchangeData.dom, List.append_assoc]
        using this
    exact omegaL_eq_zero_of_wf _ (whisker_wf hwf hw) ((pres RD k).lin_interchange x hx u v hw)

/-- **The symmetry `ω̃ : U → U` of KL III (3.43)**: inversion of the orientation of every strand,
`λ ↦ -λ`, and the sign `-1` on every crossing of two strands with the same label. It preserves
the order of 1-morphisms and of 2-morphisms. -/
def omegaU : (pres RD k).Presented ⥤ (pres RD k).Presented :=
  (pres RD k).lift (omegaFree_respects RD k)

instance : (omegaU RD k).Additive := by unfold omegaU; infer_instance

instance : (omegaU RD k).Linear k := by unfold omegaU; infer_instance

variable {RD k}

@[simp] theorem omegaU_obj (a : Obj (psig RD)) :
    (omegaU RD k).obj ((pres RD k).obj a) = (pres RD k).obj (Omega.obj RD a) := rfl

theorem omegaU_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (omegaU RD k).map ((pres RD k).lin f) = omegaL RD k f := by
  unfold omegaU; rw [Presentation.lift_lin]

/-- `ω̃` on a diagram: the diagram with inverted orientations, with the sign
`(-1)^{#ii-crossings}`. -/
theorem omegaU_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (omegaU RD k).map ((pres RD k).diag d) =
      ((Sig.sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (Omega.reflD d) := by
  unfold omegaU; rw [Presentation.lift_diag]; rfl

/-- `ω̃` on normal-form diagrams: the layers `(u, g, v)` become `(u*, Omega.shape g, v*)`
(letters dualized, same order), the rightmost region becomes `-μ`, and the diagram is multiplied
by the sign `(-1)^{#ii-crossings}`. -/
theorem omegaU_dg (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    (omegaU RD k).map (dg RD k μ s t ls) =
      ((Sig.sgnS ls : ℤ) : k) • TR RD k (Omega.trO μ s) (Omega.trO μ t)
        (dg RD k (-μ) (s.map Letter.dual) (t.map Letter.dual) (wls ls)) := by
  rw [dg_of h, show (pres RD k).diag (mkD RD μ ls h) =
    (pres RD k).lin (LinDiagram.of (mkD RD μ ls h)) from rfl, omegaU_lin, omegaL_of_mkD]

/-- `ω̃` on endomorphisms of `1_λ` (no transport needed: `ω̃(1_λ) = 1_{-λ}` on the nose). -/
theorem omegaU_dg_nil (lam : X) (ls : List (LayerData I)) (h : SChain [] ls []) :
    (omegaU RD k).map (dg RD k lam [] [] ls) =
      ((Sig.sgnS ls : ℤ) : k) • dg RD k (-lam) [] [] (wls ls) := by
  rw [omegaU_dg lam ls h]
  congr 1
  exact TR_self _ _ _

theorem omegaL_omegaL_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (omegaU RD k).map ((omegaU RD k).map ((pres RD k).diag d)) =
      TR RD k (Omega.obj_obj a) (Omega.obj_obj b) ((pres RD k).diag d) := by
  rw [omegaU_diag, Functor.map_smul, omegaU_diag, Omega.layers_reflD, Omega.sgn_map_rlay,
    smul_smul, ← Int.cast_mul, Sig.sgn_sq, Int.cast_one, one_smul, TR_diag]
  apply (pres RD k).diag_eq_of_layers_eq
  simp only [Omega.layers_reflD, List.map_map, Diagram.layers_cast]
  conv_rhs => rw [← List.map_id (Diagram.layers d)]
  exact List.map_congr_left fun L _ => Omega.rlay_rlay L

/-- **`ω̃² = 1`** (KL III: "it is a 2-isomorphism since its square is the identity"), up to the
canonical identification `ω̃(ω̃(x)) = x` of objects (`Omega.obj_obj`). -/
theorem omegaU_omegaU {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    (omegaU RD k).map ((omegaU RD k).map f) =
      TR RD k (Omega.obj_obj a) (Omega.obj_obj b) f := by
  let φ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD (Omega.obj RD a)) ⟶
        (pres RD k).obj (Omega.obj RD (Omega.obj RD b))) :=
    ((omegaU RD k).mapLinearMap k).comp ((omegaU RD k).mapLinearMap k)
  have key : φ = TR RD k (Omega.obj_obj a) (Omega.obj_obj b) :=
    hom_ext_diag RD k _ _ fun d => omegaL_omegaL_diag d
  exact LinearMap.congr_fun key f

/-- **`ω̃` preserves degrees** (KL III (3.43): `{t} ↦ {t}`). -/
theorem omegaU_homDeg {a b : Obj (psig RD)} {f : (pres RD k).obj a ⟶ (pres RD k).obj b} {t : ℤ}
    (hf : f ∈ (pres RD k).homDeg (deg RD) a b t) :
    (omegaU RD k).map f ∈ (pres RD k).homDeg (deg RD) (Omega.obj RD a) (Omega.obj RD b) t := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  clear hf
  rw [omegaU_lin]
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [omegaL_single]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Presentation.diag_mem_homDeg' ((Omega.degree_reflD d).trans hd)
  | zero => rw [omegaL_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [omegaL_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [omegaL_smul]; exact Submodule.smul_mem _ r hx

end Functor

/-! ## `ω̃` is a strict 2-functor -/

section Whisker

variable [DecidableEq I] {RD k}

theorem omegaL_whisker {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    {u : Obj (psig RD)} {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    omegaL RD k (LinDiagram.whisker f u v hw) =
      eqToHom (congrArg (pres RD k).obj (Omega.obj_whisker a u v).symm) ≫
        (pres RD k).whisk (omegaL RD k f) (Omega.obj RD u) (Omega.word v) ≫
          eqToHom (congrArg (pres RD k).obj (Omega.obj_whisker b u v)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      omegaL_zero, omegaL_zero, Presentation.whisk_zero, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    rw [LinDiagram.whisker_add, omegaL_add, hf, hg, omegaL_add, Presentation.whisk_add,
      Preadditive.add_comp, Preadditive.comp_add]
  | single d r =>
    rw [LinDiagram.whisker_single, omegaL_single, omegaL_single, Diagram.layers_whisker,
      Sig.sgn_map_whisker, Omega.reflD_whisker d ha hw, Presentation.diag_cast,
      Presentation.whisk_smul, Presentation.whisk_smul,
      Presentation.whisk_diag _ _ _ _ (Omega.whiskerOK_obj ha hw)]
    simp only [Linear.smul_comp, Linear.comp_smul]

/-- **`ω̃` is a strict 2-functor**: it commutes with whiskering (horizontal composition with
identity 2-morphisms), preserving the order of 1-morphisms. -/
theorem omegaU_whisk {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b)
    (ha : a.WF) {u : Obj (psig RD)} {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    (omegaU RD k).map ((pres RD k).whisk f u v) =
      eqToHom (congrArg (pres RD k).obj (Omega.obj_whisker a u v).symm) ≫
        (pres RD k).whisk ((omegaU RD k).map f) (Omega.obj RD u) (Omega.word v) ≫
          eqToHom (congrArg (pres RD k).obj (Omega.obj_whisker b u v)) := by
  obtain ⟨g, rfl⟩ := (pres RD k).lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, omegaU_lin, omegaU_lin,
    omegaL_whisker g ha hw]

end Whisker

/-! ## The relations (3.45) -/

section Commute

namespace Omega

variable {RD}

theorem endR_word (r : X) (w : List (Col I X)) :
    Sig.eR (RD := RD) (-r) (word w) = -Sig.eR (RD := RD) r w := by
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => exact ih c.r

theorem col_sig_col (c : Col I X) : col (Sig.col (RD := RD) c) = Sig.col (RD := RD) (col c) := by
  obtain ⟨l, r⟩ := c
  refine Col.ext rfl ?_
  show - -(sh RD l + r) = -(sh RD l.dual + -r)
  rw [sh_dual]; abel

theorem word_sig_word (w : List (Col I X)) : word (Sig.word RD w) = Sig.word RD (word w) := by
  simp [word, Sig.word, List.map_reverse, List.map_map, Function.comp_def, col_sig_col]

/-- `ω̃ σ̃` and `σ̃ ω̃` agree on objects. -/
theorem obj_sig_obj (a : Obj (psig RD)) :
    obj RD (Sig.obj RD a) = Sig.obj RD (obj RD a) := by
  refine Obj.ext ?_ (word_sig_word _)
  show - -Sig.eR (RD := RD) a.start a.word = -Sig.eR (RD := RD) (-rX a.start) (word a.word)
  rw [endR_word, neg_neg]

theorem gen_sig_gen (g : (psig RD).Gen) : gen (Sig.gen g) = Sig.gen (gen g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · show PivotalGen.gen (Gen0.dot (col (Sig.col c))) = PivotalGen.gen (Gen0.dot (Sig.col (col c)))
    rw [col_sig_col]
  · show PivotalGen.gen (Gen0.cross (!ε) j i (- -(sh RD (ε, i) + (sh RD (ε, j) + ν)))) =
      PivotalGen.gen (Gen0.cross (!ε) j i (-(sh RD (!ε, i) + (sh RD (!ε, j) + -ν))))
    rw [sh_not, sh_not]
    congr 2
    abel
  · rfl
  · rfl

theorem rlay_sig_rlay (L : Layer (psig RD)) : rlay (Sig.rlay L) = Sig.rlay (rlay L) := by
  refine Layer.ext ?_ (word_sig_word _) (gen_sig_gen _) (word_sig_word _)
  show - -Sig.eR (RD := RD) ((psig RD).right L.gen) L.right =
    -Sig.eR (RD := RD) ((psig RD).right (gen L.gen)) (word L.right)
  rw [gen_right, endR_word, neg_neg]

theorem gen_psi_gen (g : (psig RD).Gen) : gen (Psi.gen g) = Psi.gen (gen g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · show PivotalGen.cap (col ((inv RD).dual c)) = PivotalGen.cap ((inv RD).dual (col c))
    rw [inv_dual_col]
  · show PivotalGen.cup (col ((inv RD).dual c)) = PivotalGen.cup ((inv RD).dual (col c))
    rw [inv_dual_col]

theorem rlay_psi_rlay (L : Layer (psig RD)) : rlay (Psi.rlay L) = Psi.rlay (rlay L) :=
  Layer.ext rfl rfl (gen_psi_gen _) rfl

end Omega

variable [DecidableEq I] {RD k}

/-- **`ω̃ ψ̃ = ψ̃ ω̃`** (KL III (3.45), third equality). -/
theorem omegaU_psiU {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    ((psiU RD k).map ((omegaU RD k).map f)).unop = (omegaU RD k).map ((psiU RD k).map f).unop := by
  let φ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD b) ⟶ (pres RD k).obj (Omega.obj RD a)) :=
    (psiUnop RD k _ _).comp ((omegaU RD k).mapLinearMap k)
  let ψ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD b) ⟶ (pres RD k).obj (Omega.obj RD a)) :=
    ((omegaU RD k).mapLinearMap k).comp (psiUnop RD k _ _)
  have key : φ = ψ := by
    refine hom_ext_diag RD k _ _ fun d => ?_
    show ((psiU RD k).map ((omegaU RD k).map ((pres RD k).diag d))).unop =
      (omegaU RD k).map ((psiU RD k).map ((pres RD k).diag d)).unop
    rw [omegaU_diag, Functor.map_smul, psiU_diag, psiU_diag, Quiver.Hom.unop_op, omegaU_diag,
      unop_smul', Quiver.Hom.unop_op, Psi.layers_reflD, sgn_rrev]
    congr 1
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [Psi.layers_reflD, Omega.layers_reflD, Psi.rrev, List.map_reverse, List.map_map,
      Function.comp_def, Omega.rlay_psi_rlay]
  exact LinearMap.congr_fun key f

/-- **`ω̃ σ̃ = σ̃ ω̃`** (KL III (3.45), first equality, printed there as `ω̃σ̃ = ω̃σ̃`), up to the
identification `ω̃(σ̃(x)) = σ̃(ω̃(x))` of objects (`Omega.obj_sig_obj`). -/
theorem omegaU_sigU {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    (omegaU RD k).map ((sigU RD k).map f) =
      TR RD k (Omega.obj_sig_obj a) (Omega.obj_sig_obj b) ((sigU RD k).map ((omegaU RD k).map f)) := by
  let φ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD (Sig.obj RD a)) ⟶
        (pres RD k).obj (Omega.obj RD (Sig.obj RD b))) :=
    ((omegaU RD k).mapLinearMap k).comp ((sigU RD k).mapLinearMap k)
  let ψ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD (Sig.obj RD a)) ⟶
        (pres RD k).obj (Omega.obj RD (Sig.obj RD b))) :=
    (TR RD k (Omega.obj_sig_obj a) (Omega.obj_sig_obj b)).comp
      (((sigU RD k).mapLinearMap k).comp ((omegaU RD k).mapLinearMap k))
  have key : φ = ψ := by
    refine hom_ext_diag RD k _ _ fun d => ?_
    show (omegaU RD k).map ((sigU RD k).map ((pres RD k).diag d)) =
      TR RD k (Omega.obj_sig_obj a) (Omega.obj_sig_obj b)
        ((sigU RD k).map ((omegaU RD k).map ((pres RD k).diag d)))
    rw [sigU_diag, Functor.map_smul, omegaU_diag, omegaU_diag, Functor.map_smul, sigU_diag,
      map_smul, map_smul, Sig.layers_reflD, Sig.sgn_map_rlay, Omega.layers_reflD,
      Omega.sgn_map_rlay, TR_diag]
    congr 2
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [Omega.layers_reflD, Sig.layers_reflD, Diagram.layers_cast, List.map_map,
      Function.comp_def, Omega.rlay_sig_rlay]
  exact LinearMap.congr_fun key f

end Commute

/-! ## Bubbles -/

section Bubbles

variable [DecidableEq I] {RD k}

/-- `ω̃` sends the clockwise bubble with `m` dots in the region `λ` to the counterclockwise
bubble with `m` dots in the region `-λ` (the dots stay on the second strand). -/
theorem omegaL_cwReal (lam : X) (i : I) (m : ℕ) :
    omegaL RD k (LinDiagram.of (cwReal RD lam i m)) = dg RD k (-lam) [] [] (ccwLs i m) := by
  rw [cwReal, omegaL_of_mkD, sgnS_bubble, Int.cast_one, one_smul]
  refine (TR_self _ _ _).trans ?_
  simp [wls, Omega.ld, Omega.shape, ccwLs, List.map_replicate]

/-- `ω̃` sends the counterclockwise bubble with `m` dots in the region `λ` to the clockwise
bubble with `m` dots in the region `-λ`. -/
theorem omegaL_ccwReal (lam : X) (i : I) (m : ℕ) :
    omegaL RD k (LinDiagram.of (ccwReal RD lam i m)) = dg RD k (-lam) [] [] (cwLs i m) := by
  rw [ccwReal, omegaL_of_mkD, sgnS_bubble, Int.cast_one, one_smul]
  refine (TR_self _ _ _).trans ?_
  simp [wls, Omega.ld, Omega.shape, cwLs, List.map_replicate]

variable (RD k) in
/-- `ω̃` on `END(1_λ)`: a ring homomorphism to `END(1_{-λ})`. -/
def omegaEnd (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k).obj (ob RD (-lam) [])) :=
  (functorEndAlg k (freeLift k (omegaFree RD k)) (Free.of k (ob RD lam []))).toRingHom

theorem omegaEnd_apply (lam : X) (f : LEnd RD k (ob RD lam [])) :
    omegaEnd RD k lam f = omegaL RD k f := rfl

theorem omegaL_ccwR (lam : X) (i : I) (m : ℤ) :
    omegaL RD k (ccwR RD k lam i m) = (pres RD k).lin (cwR RD k (-lam) i m) := by
  unfold ccwR cwR
  split_ifs
  · rw [omegaL_ccwReal, lin_cwReal]
  · rw [omegaL_zero, Presentation.lin_zero]

theorem omegaL_cwR (lam : X) (i : I) (m : ℤ) :
    omegaL RD k (cwR RD k lam i m) = (pres RD k).lin (ccwR RD k (-lam) i m) := by
  unfold ccwR cwR
  split_ifs
  · rw [omegaL_cwReal, lin_ccwReal]
  · rw [omegaL_zero, Presentation.lin_zero]

/-- **`ω̃` sends the clockwise bubble with label `m` in the region `λ` to the counterclockwise
bubble with label `m` in the region `-λ`**, real or fake. -/
theorem omegaL_cwL (lam : X) (i : I) (m : ℤ) :
    omegaL RD k (cwL RD k lam i m) = ccwU RD k (-lam) i m := by
  unfold ccwU cwL ccwL
  simp only [ip_neg, ← sub_eq_add_neg, neg_neg]
  split_ifs
  · rw [omegaL_cwReal, lin_ccwReal]
  · show omegaEnd RD k lam _ = linEnd RD k (-lam) _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    rw [omegaEnd_apply, omegaL_ccwR]
    rfl
  · rw [omegaL_zero, Presentation.lin_zero]

/-- **`ω̃` sends the counterclockwise bubble with label `m` in the region `λ` to the clockwise
bubble with label `m` in the region `-λ`**, real or fake. -/
theorem omegaL_ccwL (lam : X) (i : I) (m : ℤ) :
    omegaL RD k (ccwL RD k lam i m) = cwU RD k (-lam) i m := by
  unfold cwU cwL ccwL
  simp only [ip_neg, ← sub_eq_add_neg, neg_neg, sub_neg_eq_add]
  split_ifs
  · rw [omegaL_ccwReal, lin_cwReal]
  · show omegaEnd RD k lam _ = linEnd RD k (-lam) _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    rw [omegaEnd_apply, omegaL_cwR]
    rfl
  · rw [omegaL_zero, Presentation.lin_zero]

/-- **`ω̃` sends the clockwise bubble with label `m` in the region `λ` to the counterclockwise
bubble with label `m` in the region `-λ`** (real and fake bubbles). -/
theorem omegaU_cwU (lam : X) (i : I) (m : ℤ) :
    (omegaU RD k).map (cwU RD k lam i m) = ccwU RD k (-lam) i m := by
  rw [cwU, omegaU_lin, omegaL_cwL]

/-- **`ω̃` sends the counterclockwise bubble with label `m` in the region `λ` to the clockwise
bubble with label `m` in the region `-λ`** (real and fake bubbles). -/
theorem omegaU_ccwU (lam : X) (i : I) (m : ℤ) :
    (omegaU RD k).map (ccwU RD k lam i m) = cwU RD k (-lam) i m := by
  rw [ccwU, omegaU_lin, omegaL_ccwL]

end Bubbles

/-! ## The KLR relations on downward strands -/

section Downward

variable [DecidableEq I] {RD k}

/-- Downward strands `F_i`. -/
abbrev dns (l : List I) : List (Letter I) := l.map dn

/-- The shape of a KLR generator, on downward strands. -/
def dnShape : KLR.Diagram.Gen I → Shape I
  | .dot c => .dot (dn c)
  | .cross c d => .cross false c d

/-- A KLR layer as a normal-form layer on downward strands. -/
def dnLD (L : Layer (KLR.Diagram.sig I)) : LayerData I := (dns L.left, dnShape L.gen, dns L.right)

omit [DecidableEq I] in
theorem map_dual_ups (l : List I) : (ups l).map Letter.dual = dns l := by
  simp [ups, dns, List.map_map, Function.comp_def]

omit [DecidableEq I] in
theorem wls_map_upLD (ls : List (Layer (KLR.Diagram.sig I))) :
    wls (ls.map upLD) = ls.map dnLD := by
  simp only [wls, List.map_map]
  refine List.map_congr_left fun L _ => ?_
  obtain ⟨_, l, g, r⟩ := L
  cases g <;> simp [Omega.ld, upLD, dnLD, upShape, dnShape, Omega.shape, map_dual_ups]

omit [DecidableEq I] in
/-- `ω̃(E_{+w} 1_{-μ}) = E_{-w} 1_μ`. -/
theorem omega_ob_ups (μ : X) (w : List I) : Omega.obj RD (ob RD (-μ) (ups w)) = ob RD μ (dns w) := by
  rw [Omega.trO, neg_neg, map_dual_ups]

omit [DecidableEq I] in
theorem TR_dg_congr {ν ν' : X} (hν : ν = ν') {a a' b b' : List (Letter I)} (ha : a = a')
    (hb : b = b') {A B : Obj (psig RD)} (eA : A = ob RD ν a) (eB : B = ob RD ν b)
    (eA' : A = ob RD ν' a') (eB' : B = ob RD ν' b') (L : List (LayerData I)) :
    TR RD k eA eB (dg RD k ν a b L) = TR RD k eA' eB' (dg RD k ν' a' b' L) := by
  subst hν ha hb; rfl

variable (RD k) in
/-- **The KLR 2-morphisms on downward strands**: `ω̃` composed with the placement of KLR diagrams
on upward strands with rightmost region `-μ` (`upFunctor`). It sends the sequence `i` to
`E_{-i} 1_μ` (`omega_ob_ups`), and a KLR diagram to the same diagram on downward strands with the
sign `(-1)^{#ii-crossings}` (`downFunctor_diag`). As a functor out of the diagrammatic KLR
category (KL II relations, `Q = klQ2`), it expresses that **the relations of `R(ν)` hold on
downward strands, with every crossing of equally labelled strands rescaled by `-1`**. -/
def downFunctor (μ : X) : (KLR.Diagram.pres k (KLR.klQ2 k C)).Presented ⥤ (pres RD k).Presented :=
  upFunctor RD k (-μ) ⋙ omegaU RD k

instance (μ : X) : (downFunctor RD k μ).Additive := by unfold downFunctor; infer_instance

instance (μ : X) : (downFunctor RD k μ).Linear k := by unfold downFunctor; infer_instance

/-- `downFunctor` on a KLR diagram: the diagram on downward strands (`dnLD`), with the sign
`(-1)^{#ii-crossings}`. -/
theorem downFunctor_diag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d) =
      ((Sig.sgnS ((Diagram.layers d).map upLD) : ℤ) : k) •
        TR RD k (omega_ob_ups μ a.word) (omega_ob_ups μ b.word)
          (dg RD k μ (dns a.word) (dns b.word) ((Diagram.layers d).map dnLD)) := by
  rw [show (downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d) =
      (omegaU RD k).map ((upFunctor RD k (-μ)).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d))
      from rfl, upFunctor_diag, upDiag_eq_dg,
    omegaU_dg _ _ (sChain_upLD (Diagram.chain d)), wls_map_upLD]
  congr 1
  exact TR_dg_congr (neg_neg μ) (map_dual_ups _) (map_dual_ups _) _ _ _ _ _

/-- The downward dot. -/
theorem downFunctor_dot (μ : X) (c : I) :
    (downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag
      (KLR.Diagram.dl [] (.dot c) [] (a := KLR.Diagram.ob [c]) (b := KLR.Diagram.ob [c]) rfl rfl)) =
      TR RD k (omega_ob_ups μ [c]) (omega_ob_ups μ [c])
        (dg RD k μ [dn c] [dn c] [([], .dot (dn c), [])]) := by
  rw [downFunctor_diag]
  simp [Sig.sgnS, Sig.sgnSh, upLD, upShape, dnLD, dnShape, KLR.Diagram.lay]

/-- The downward crossing, with the sign `-1` if the labels agree. -/
theorem downFunctor_cross (μ : X) (c d : I) :
    (downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag (KLR.Diagram.X2 c d)) =
      ((if c = d then -1 else 1 : ℤ) : k) •
        TR RD k (omega_ob_ups μ [c, d]) (omega_ob_ups μ [d, c])
          (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) := by
  rw [downFunctor_diag]
  simp [Sig.sgnS, Sig.sgnSh, upLD, upShape, dnLD, dnShape, KLR.Diagram.lay]

end Downward

/-! ## The curl relations on downward strands -/

section DownCurl

variable [DecidableEq I] {RD k}

omit [DecidableEq I] in
theorem wls_map_whL_left (l : Letter I) (ls : List (LayerData I)) :
    wls (ls.map (whL [l] [])) = (wls ls).map (whL [l.dual] []) := by
  simp [wls, Omega.ld, whL, List.map_map, Function.comp_def]

theorem sgnS_map_whL (u v : List (Letter I)) (ls : List (LayerData I)) :
    Sig.sgnS (ls.map (whL u v)) = Sig.sgnS ls := by
  simp [Sig.sgnS, whL, List.map_map, Function.comp_def]

/-- `ω̃` on dots: `n` dots on `l` go to `n` dots on `l*`. -/
theorem omegaU_dotsU (lam : X) (l : Letter I) (n : ℕ) :
    (omegaU RD k).map (dotsU RD k lam l n) =
      TR RD k (Omega.trO lam [l]) (Omega.trO lam [l]) (dotsU RD k (-lam) l.dual n) := by
  rw [dotsU, omegaU_dg lam _
    (show SChain [l] (List.replicate n ([], .dot l, [])) [l] from SChain.replicate n [] l [])]
  have hs : Sig.sgnS (List.replicate n (([] : List (Letter I)), Shape.dot l, ([] : List (Letter I))))
      = 1 := by simp [Sig.sgnS, Sig.sgnSh, List.map_replicate, List.prod_replicate]
  rw [hs, Int.cast_one, one_smul]
  simp [wls, Omega.ld, Omega.shape, List.map_replicate]

/-- `ω̃` on endomorphisms of `1_λ` placed to the right of a strand `l`. -/
theorem omegaU_bubRU (lam : X) (l : Letter I) (β : End ((pres RD k).obj (ob RD lam []))) :
    (omegaU RD k).map (bubRU RD k lam l β) =
      TR RD k (Omega.trO lam [l]) (Omega.trO lam [l])
        (bubRU RD k (-lam) l.dual ((omegaU RD k).map β)) := by
  let φ : End ((pres RD k).obj (ob RD lam [])) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD (ob RD lam [l])) ⟶
        (pres RD k).obj (Omega.obj RD (ob RD lam [l]))) :=
    ((omegaU RD k).mapLinearMap k).comp (plcL RD k lam [l] [] [] [])
  let ψ : End ((pres RD k).obj (ob RD lam [])) →ₗ[k]
      ((pres RD k).obj (Omega.obj RD (ob RD lam [l])) ⟶
        (pres RD k).obj (Omega.obj RD (ob RD lam [l]))) :=
    (TR RD k (Omega.trO lam [l]) (Omega.trO lam [l])).comp
      ((plcL RD k (-lam) [l.dual] [] [] []).comp ((omegaU RD k).mapLinearMap k))
  have key : φ = ψ := by
    refine hom_ext_dg RD k lam φ ψ fun ls h => ?_
    show (omegaU RD k).map (plcL RD k lam [l] [] [] [] (dg RD k (wt RD lam []) [] [] ls)) =
      TR RD k (Omega.trO lam [l]) (Omega.trO lam [l])
        (plcL RD k (-lam) [l.dual] [] [] [] ((omegaU RD k).map (dg RD k lam [] [] ls)))
    rw [plcL_dg, omegaU_dg lam _ (h.whisk [l] []), omegaU_dg_nil lam ls h, map_smul,
      show plcL RD k (-lam) [l.dual] [] [] [] (dg RD k (-lam) [] [] (wls ls)) =
        dg RD k (-lam) [l.dual] [l.dual] ((wls ls).map (whL [l.dual] [])) from plcL_dg RD k (-lam) [l.dual] [] [] [] (wls ls),
      map_smul, sgnS_map_whL, wls_map_whL_left]
    rfl
  exact LinearMap.congr_fun key β

omit [DecidableEq I] in
theorem ip_neg' (i : I) (lam : X) : ip RD i (-lam) = -ip RD i lam := map_neg _ _

/-- **The right curl relation on a downward strand** (the `ω̃`-image of the right curl relation
of KL III, item iv), first display, with `λ ↦ -λ`): a downward strand `F_i` with a curl on its
right (outer region `λ` on the right, `n = ⟨i, λ⟩`) equals
`∑_{f=0}^{n} x^{n-f} ⊗ ccw_{-n-1+f}`, the counterclockwise bubbles to the right of the strand.
(The sign: the curl contains one `ii`-crossing.) -/
theorem dg_curlR_down (i : I) (lam : X) :
    dg RD k lam [dn i] [dn i]
        [([dn i], .cup (dn i), []), ([], .cross false i i, [up i]), ([dn i], .cap (up i), [])] =
      ∑ f ∈ Finset.range (ip RD i lam + 1).toNat,
        bubRU RD k lam (dn i) (ccwU RD k lam i (-ip RD i lam - 1 + f)) ≫
          dotsU RD k lam (dn i) (ip RD i lam - f).toNat := by
  obtain ⟨μ, rfl⟩ : ∃ μ, lam = -μ := ⟨-lam, (neg_neg lam).symm⟩
  have key := congrArg (omegaU RD k).map (dg_curlR RD k i μ)
  rw [omegaU_dg μ _ (by schain), Functor.map_neg, Functor.map_sum] at key
  have hs : Sig.sgnS [([up i], Shape.cup (up i), ([] : List (Letter I))),
      (([] : List (Letter I)), Shape.cross true i i, [dn i]), ([up i], Shape.cap (dn i), [])] =
      -1 := by simp [Sig.sgnS, Sig.sgnSh]
  rw [hs] at key
  simp only [Functor.map_comp, omegaU_bubRU, omegaU_dotsU, omegaU_cwU, TR_comp] at key
  rw [← map_sum (TR RD k (Omega.trO μ [up i]) (Omega.trO μ [up i])),
    ← map_neg (TR RD k (Omega.trO μ [up i]) (Omega.trO μ [up i])), ← map_smul] at key
  have key' := congrArg (TR RD k (Omega.trO μ [up i]).symm (Omega.trO μ [up i]).symm) key
  rw [TR_TR, TR_TR, Int.cast_neg, Int.cast_one, neg_smul, one_smul, neg_inj] at key'
  simp only [ip_neg', neg_neg]
  refine Eq.trans ?_ (key'.trans ?_)
  · simp [wls, Omega.ld, Omega.shape]
    rfl
  · refine Finset.sum_congr rfl fun f _ => ?_
    simp only [ip_neg', Letter.dual_up]

end DownCurl

end Categorification.KL3.Diagram
