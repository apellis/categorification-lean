/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryPsi
import Categorification.KLR.Symmetries

/-!
# The symmetry `σ̃` of `U`: reflection in a vertical axis

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(TeX label `sec_symm`), paragraph "Rescale, reflect across the `y`-axis, and send
`λ ↦ -λ`".

KL III: "The operation on diagrams that rescales the `ii`-crossing `ψ_{i,i,λ} ↦ -ψ_{i,i,λ}` for all
`i ∈ I` and `λ ∈ X`, reflects a diagram across the y-axis, and sends `λ` to `-λ` leaves invariant
the relations on the 2-morphisms of `U`. This operation [...] is contravariant for composition of
1-morphisms, covariant for composition of 2-morphisms, and preserves the degree of a diagram.
Hence, this symmetry gives a 2-isomorphism `σ̃ : U → U^op`, `λ ↦ -λ`,
`1_μ E_{s_1} ⋯ E_{s_m} 1_λ {t} ↦ 1_{-λ} E_{s_m} ⋯ E_{s_1} 1_{-μ} {t}` [...] The square of `σ̃` is
the identity."

## Conventions

A strand keeps its label and orientation; its left region `sh l + r` becomes the negative of its
right region, so the colour `⟨l, r⟩` goes to `⟨l, -(sh l + r)⟩` (`Sig.col`), and words are
reversed (`Sig.word`). An object (a word read from its leftmost region `s`, with rightmost region
`e`) goes to the reversed word read from `-e` (`Sig.obj`). On generators (`Sig.gen`, on shapes
`Sig.shape`): dots are fixed, the crossing `(ε,i)(ε,j) ⟶ (ε,j)(ε,i)` goes to
`(ε,j)(ε,i) ⟶ (ε,i)(ε,j)`, the cup `1 ⟶ l l*` goes to the cup `1 ⟶ l* l` and the cap
`l* l ⟶ 1` to the cap `l l* ⟶ 1`; a diagram is multiplied by `(-1)` to the number of its
crossings of two strands with the same label (`Sig.sgn`).

The library's words are read from left to right, so `σ̃` reverses the order of 1-morphisms: on
1-morphisms it is contravariant, on 2-morphisms covariant. It is constructed as a `k`-linear
functor `sigU RD k : (pres RD k).Presented ⥤ (pres RD k).Presented` with `Presentation.lift`;
`sigU_whisk` expresses that it reverses horizontal composition.

## Construction

The functor is `Presentation.lift` of the signed reflection `sigFree` of the free 2-category.
The soundness hypotheses are checked relation by relation (`sigL_relation`, `sigL_zigL`,
`sigL_zigR`, `sigL_interchange`): (3.3) `cycDotR ↔ cycDotL`; `eq_cyclic_cross-gen`
`cycCrossR j i ↔ cycCrossL i j`; `eq_downup_ij-gen` `downupEF ↔ downupFE`; clockwise and
counterclockwise bubbles are exchanged with `λ ↦ -λ` after sliding the dots around a cup
(`sigL_cwReal`), also for fake bubbles (`sigL_cwL`); the right curl relation goes to the left curl
relation (and back), with the bubble moving from one side of the strand to the other
(`sigL_bubR`, `sigL_bubL`) and the sign `-1` of the `ii`-crossing; `eq_ident_decomp` for `E F`
goes to the one for `F E`. The relations of `R(ν)` on upward strands are reflected to relations
of `R(ν)` (`KSig.ksL_relation`: `eq_nil_dotslide` and `eq_dot_slide_ij-gen` are exchanged,
`eq_r2_ij-gen` uses `Q_ij(u,v) = Q_ji(v,u)`, `eq_r3_hard-gen` uses the symmetry of `Q̄` in its
outer variables, `KLR.qbar_rename_rev`). Objects are compared with normal forms along
`Sig.trO` and the transport `TR`.

## Main results

* `sigU RD k`, `sigU_diag` (on a diagram: the signed reflected diagram), `sigU_dg` (in normal
  form), `sigU_whisk`;
* `sigU_homDeg`: `σ̃` preserves degrees;
* on bubbles: `sigU_cwU`, `sigU_ccwU`: `σ̃` exchanges clockwise and counterclockwise bubbles
  (real and fake) with the same label, `λ ↦ -λ`;
* `KSig.ksL_relation`: the vertical flip with signs is a symmetry of the diagrammatic KLR
  relations for the KL II polynomials `klQ2`.

`σ̃² = 1` and `σ̃ ψ̃ = ψ̃ σ̃` are in `Categorification.Diagrams.KL3.Symmetries`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

namespace Sig

variable {RD}

/-! ## Reflection of colours, words and objects -/

/-- The reflected colour: the same letter, with right region the negative of the left region. -/
def col (c : Col I X) : Col I X := ⟨c.l, -(sh RD c.l + c.r)⟩

variable (RD) in
/-- The reflected word: reversed, each colour reflected. -/
def word (w : List (Col I X)) : List (Col I X) := (w.map (col (RD := RD))).reverse

@[simp] theorem word_nil : word RD [] = [] := rfl

@[simp] theorem word_nil' : word RD ([] : List (psig RD).Colour) = [] := rfl

theorem word_cons (c : (psig RD).Colour) (w : List (psig RD).Colour) :
    word RD (c :: w) = word RD w ++ [col (RD := RD) c] := by
  simp [word]

theorem word_append (w w' : List (psig RD).Colour) :
    word RD (w ++ w') = word RD w' ++ word RD w := by
  simp [word]

theorem col_src (c : Col I X) : (psig RD).colourSrc (col (RD := RD) c) = -c.r := by
  show sh RD c.l + -(sh RD c.l + c.r) = -c.r
  abel

theorem col_tgt (c : Col I X) :
    (psig RD).colourTgt (col (RD := RD) c) = -(sh RD c.l + c.r) := rfl

/-- `endR` as an element of `X`. -/
abbrev eR (r : X) (w : List (Col I X)) : X := (psig RD).endR r w

/-- The right region of a generator, as an element of `X`. -/
abbrev rR (g : (psig RD).Gen) : X := (psig RD).right g

/-- The left region of a generator, as an element of `X`. -/
abbrev lR (g : (psig RD).Gen) : X := (psig RD).left g

theorem ok_word (r : X) (w : List (Col I X)) (h : (psig RD).ok r w) :
    (psig RD).ok (-eR (RD := RD) r w) (word RD w) ∧
      (psig RD).endR (-eR (RD := RD) r w) (word RD w) = -r := by
  induction w generalizing r with
  | nil => exact ⟨trivial, rfl⟩
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    obtain ⟨ih₁, ih₂⟩ := ih c.r hw
    have e : eR (RD := RD) r (c :: w) = eR (RD := RD) c.r w := rfl
    rw [e, word_cons, Signature.ok_append, Signature.endR_append, ih₂]
    refine ⟨⟨ih₁, col_src c, trivial⟩, ?_⟩
    show -(sh RD c.l + c.r) = -r
    rw [← hc]; rfl

variable (RD) in
/-- The reflected object: the reversed reflected word, read from the negative of the rightmost
region. -/
def obj (a : Obj (psig RD)) : Obj (psig RD) := ⟨-eR (RD := RD) a.start a.word, word RD a.word⟩

@[simp] theorem obj_start (a : Obj (psig RD)) :
    (obj RD a).start = -eR (RD := RD) a.start a.word := rfl
@[simp] theorem obj_word (a : Obj (psig RD)) : (obj RD a).word = word RD a.word := rfl

/-! ## Reflection of generators and layers -/

/-- The reflection of a generator across the `y`-axis with `λ ↦ -λ`. -/
def gen : (psig RD).Gen → (psig RD).Gen
  | .gen (.dot c) => .gen (.dot (col (RD := RD) c))
  | .gen (.cross ε i j ν) => .gen (.cross ε j i (-(sh RD (ε, i) + (sh RD (ε, j) + ν))))
  | .cup c => .cup ⟨c.l.dual, -c.r⟩
  | .cap c => .cap ⟨c.l.dual, -c.r⟩

theorem gen_left (g : (psig RD).Gen) : (psig RD).left (gen g) = -rR (RD := RD) g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · exact col_src c
  · show sh RD (ε, j) + (sh RD (ε, i) + -(sh RD (ε, i) + (sh RD (ε, j) + ν))) = -ν
    abel
  · show sh RD c.l.dual + -c.r = -(sh RD c.l + c.r)
    rw [sh_dual]; abel
  · rfl

theorem gen_right (g : (psig RD).Gen) : (psig RD).right (gen g) = -lR (RD := RD) g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · show sh RD c.l.dual + -c.r = -(sh RD c.l + c.r)
    rw [sh_dual]; abel
  · rfl

theorem gen_dom (g : (psig RD).Gen) : (psig RD).dom (gen g) = word RD ((psig RD).dom g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨(ε, j), sh RD (ε, i) + -(sh RD (ε, i) + (sh RD (ε, j) + ν))⟩ : Col I X),
      ⟨(ε, i), -(sh RD (ε, i) + (sh RD (ε, j) + ν))⟩] =
      [⟨(ε, j), -(sh RD (ε, j) + ν)⟩, ⟨(ε, i), -(sh RD (ε, i) + (sh RD (ε, j) + ν))⟩]
    congr 2; abel
  · rfl
  · obtain ⟨l, r⟩ := c
    show [(⟨l.dual.dual, sh RD l.dual + -r⟩ : Col I X), ⟨l.dual, -r⟩] =
      [⟨l, -(sh RD l + r)⟩, ⟨l.dual, -(sh RD l.dual + (sh RD l + r))⟩]
    rw [Letter.dual_dual, sh_dual]
    congr 3 <;> abel

theorem gen_cod (g : (psig RD).Gen) : (psig RD).cod (gen g) = word RD ((psig RD).cod g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨(ε, i), sh RD (ε, j) + -(sh RD (ε, i) + (sh RD (ε, j) + ν))⟩ : Col I X),
      ⟨(ε, j), -(sh RD (ε, i) + (sh RD (ε, j) + ν))⟩] =
      [⟨(ε, i), -(sh RD (ε, i) + ν)⟩, ⟨(ε, j), -(sh RD (ε, j) + (sh RD (ε, i) + ν))⟩]
    congr 3 <;> abel
  · obtain ⟨l, r⟩ := c
    show [(⟨l.dual, -r⟩ : Col I X), ⟨l.dual.dual, sh RD l.dual + -r⟩] =
      [⟨l.dual, -(sh RD l.dual + (sh RD l + r))⟩, ⟨l, -(sh RD l + r)⟩]
    rw [Letter.dual_dual, sh_dual]
    congr 3 <;> abel
  · rfl

theorem deg_gen (g : (psig RD).Gen) : deg RD (gen g) = deg RD g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show -C.dot j i = -C.dot i j
    rw [C.symm]
  · obtain ⟨⟨s, i⟩, r⟩ := c
    show di C i * (1 - sgn (!s) * RD.pair (RD.iY i) (sh RD (!s, i) + -r)) =
      di C i * (1 - sgn s * RD.pair (RD.iY i) (sh RD (s, i) + r))
    rw [show ((!s, i) : Letter I) = Letter.dual (s, i) from rfl, sh_dual]
    cases s <;> simp only [Bool.not_false, Bool.not_true, sgn_true, sgn_false, map_add, map_neg] <;>
      ring
  · obtain ⟨⟨s, i⟩, r⟩ := c
    show di C i * (1 + sgn (!s) * RD.pair (RD.iY i) (-r)) =
      di C i * (1 + sgn s * RD.pair (RD.iY i) r)
    cases s <;> simp only [Bool.not_false, Bool.not_true, sgn_true, sgn_false, map_neg] <;> ring

/-- The reflection of a layer: the strands to the right become the reversed strands to the left. -/
def rlay (L : Layer (psig RD)) : Layer (psig RD) :=
  ⟨-eR (RD := RD) ((psig RD).right L.gen) L.right, word RD L.right, gen L.gen, word RD L.left⟩

theorem rlay_valid {L : Layer (psig RD)} (hv : L.Valid) : (rlay L).Valid := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hv
  have h₂' : eR (RD := RD) L.start L.left = lR (RD := RD) L.gen := h₂
  have h₄' : eR (RD := RD) (lR (RD := RD) L.gen) ((psig RD).dom L.gen) = rR (RD := RD) L.gen := h₄
  have h₆' : eR (RD := RD) (lR (RD := RD) L.gen) ((psig RD).cod L.gen) = rR (RD := RD) L.gen := h₆
  refine ⟨(ok_word _ _ h₇).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (psig RD).endR (-eR (RD := RD) ((psig RD).right L.gen) L.right) (word RD L.right) =
      (psig RD).left (gen L.gen)
    rw [(ok_word _ _ h₇).2, gen_left]
  · show (psig RD).ok ((psig RD).left (gen L.gen)) ((psig RD).dom (gen L.gen))
    rw [gen_left, gen_dom, ← h₄']; exact (ok_word _ _ h₃).1
  · show (psig RD).endR ((psig RD).left (gen L.gen)) ((psig RD).dom (gen L.gen)) =
      (psig RD).right (gen L.gen)
    rw [gen_left, gen_dom, gen_right, ← h₄', (ok_word _ _ h₃).2]
  · show (psig RD).ok ((psig RD).left (gen L.gen)) ((psig RD).cod (gen L.gen))
    rw [gen_left, gen_cod, ← h₆']; exact (ok_word _ _ h₅).1
  · show (psig RD).endR ((psig RD).left (gen L.gen)) ((psig RD).cod (gen L.gen)) =
      (psig RD).right (gen L.gen)
    rw [gen_left, gen_cod, gen_right, ← h₆', (ok_word _ _ h₅).2]
  · show (psig RD).ok ((psig RD).right (gen L.gen)) (word RD L.left)
    rw [gen_right, ← h₂']; exact (ok_word _ _ h₁).1

theorem rlay_dom {L : Layer (psig RD)} (hv : L.Valid) : (rlay L).dom = obj RD L.dom := by
  refine Obj.ext ?_ ?_
  · show -eR (RD := RD) ((psig RD).right L.gen) L.right = -eR (RD := RD) L.dom.start L.dom.word
    rw [show eR (RD := RD) L.dom.start L.dom.word = L.dom.endR from rfl, hv.endR_dom]
  · simp only [Layer.dom_word, rlay, obj_word, gen_dom, word_append, List.append_assoc]

theorem rlay_cod {L : Layer (psig RD)} (hv : L.Valid) : (rlay L).cod = obj RD L.cod := by
  refine Obj.ext ?_ ?_
  · show -eR (RD := RD) ((psig RD).right L.gen) L.right = -eR (RD := RD) L.cod.start L.cod.word
    rw [show eR (RD := RD) L.cod.start L.cod.word = L.cod.endR from rfl, hv.endR_cod]
  · simp only [Layer.cod_word, rlay, obj_word, gen_cod, word_append, List.append_assoc]

theorem rlay_whisker (L : Layer (psig RD)) (u : Obj (psig RD)) (v : List (psig RD).Colour) :
    rlay (L.whisker u v) = (rlay L).whisker
      ⟨-eR (RD := RD) (eR (RD := RD) ((psig RD).right L.gen) L.right) v, word RD v⟩
      (word RD u.word) := by
  simp only [rlay, Layer.whisker, word_append, Signature.endR_append]

theorem chain_map {a b : Obj (psig RD)} {ls : List (Layer (psig RD))} (h : Chain a ls b) :
    Chain (obj RD a) (ls.map rlay) (obj RD b) := by
  induction ls generalizing a with
  | nil => exact congrArg (obj RD) h
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨rlay_valid hv, rlay_dom hv, by rw [rlay_cod hv]; exact ih hc⟩

/-- The reflection of a diagram. -/
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

/-! ## Whiskering -/

theorem chain_mem {a b : Obj (psig RD)} {ls : List (Layer (psig RD))} (h : Chain a ls b)
    {L : Layer (psig RD)} (hL : L ∈ ls) : L.Valid ∧ L.dom.endR = a.endR := by
  induction ls generalizing a with
  | nil => cases hL
  | cons L' ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rcases List.mem_cons.1 hL with rfl | hL
    · exact ⟨hv, rfl⟩
    · obtain ⟨h₁, h₂⟩ := ih hc hL
      exact ⟨h₁, h₂.trans hv.endR_eq⟩

/-- The object by which a reflected diagram is whiskered on the left, when the original one is
whiskered by `v` on the right. -/
def sigW (a : Obj (psig RD)) (v : List (psig RD).Colour) : Obj (psig RD) :=
  ⟨-eR (RD := RD) (eR (RD := RD) a.start a.word) v, word RD v⟩

theorem whiskerOK_obj {a u : Obj (psig RD)} {v : List (psig RD).Colour} (ha : a.WF)
    (hw : a.WhiskerOK u v) : (obj RD a).WhiskerOK (sigW a v) (word RD u.word) := by
  obtain ⟨hu, hue, hv⟩ := hw
  refine ⟨(ok_word _ _ hv).1, (ok_word _ _ hv).2, ?_⟩
  show (psig RD).ok ((psig RD).endR (-eR (RD := RD) a.start a.word) (word RD a.word))
    (word RD u.word)
  rw [(ok_word _ _ ha).2, ← hue]
  exact (ok_word _ _ hu).1

theorem obj_whisker {a u : Obj (psig RD)} {v : List (psig RD).Colour} (hue : u.endR = a.start) :
    (obj RD a).whisker (sigW a v) (word RD u.word) = obj RD (a.whisker u v) := by
  refine Obj.ext ?_ ?_
  · show -eR (RD := RD) (eR (RD := RD) a.start a.word) v =
      -eR (RD := RD) u.start (u.word ++ a.word ++ v)
    simp only [eR, Signature.endR_append]
    rw [show (psig RD).endR u.start u.word = a.start from hue]
  · simp [Obj.whisker, sigW, word_append, List.append_assoc]

theorem obj_whisker_cod {a b u : Obj (psig RD)} {v : List (psig RD).Colour}
    (hs : b.start = a.start) (he : b.endR = a.endR) (hue : u.endR = a.start) :
    (obj RD b).whisker (sigW a v) (word RD u.word) = obj RD (b.whisker u v) := by
  have e : sigW a v = sigW b v := by
    show (⟨-eR (RD := RD) a.endR v, word RD v⟩ : Obj (psig RD)) = ⟨-eR (RD := RD) b.endR v, word RD v⟩
    rw [he]
  rw [e]
  exact obj_whisker (hue.trans hs.symm)

theorem reflD_whisker {a b : Obj (psig RD)} (d : a ⟶ b) (ha : a.WF) {u : Obj (psig RD)}
    {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    reflD (Diagram.whisker d u v hw) =
      Diagram.cast (Diagram.whisker (reflD d) (sigW a v) (word RD u.word) (whiskerOK_obj ha hw))
        (obj_whisker hw.2.1)
        (obj_whisker_cod (Diagram.chain d).start_eq (Diagram.chain d).endR_eq hw.2.1) := by
  apply Diagram.ext
  simp only [layers_reflD, Diagram.layers_whisker, Diagram.layers_cast, List.map_map]
  refine List.map_congr_left fun L hL => ?_
  simp only [Function.comp_apply, rlay_whisker]
  obtain ⟨hv, he⟩ := chain_mem (Diagram.chain d) hL
  congr 2
  show -eR (RD := RD) (eR (RD := RD) ((psig RD).right L.gen) L.right) v =
    -eR (RD := RD) (eR (RD := RD) a.start a.word) v
  rw [show eR (RD := RD) ((psig RD).right L.gen) L.right = L.dom.endR from hv.endR_dom.symm, he]
  rfl

/-! ## Signs -/

variable [DecidableEq I]

/-- The sign of a generator: `-1` for a crossing of two strands with the same label. -/
def sgnG : (psig RD).Gen → ℤ
  | .gen (.cross _ i j _) => if i = j then -1 else 1
  | _ => 1

theorem sgnG_gen (g : (psig RD).Gen) : sgnG (gen g) = sgnG g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show (if j = i then -1 else 1 : ℤ) = if i = j then -1 else 1
    simp only [eq_comm]
  · rfl
  · rfl

/-- The sign of a list of layers. -/
def sgn (ls : List (Layer (psig RD))) : ℤ := (ls.map fun L => sgnG L.gen).prod

@[simp] theorem sgn_nil : sgn ([] : List (Layer (psig RD))) = 1 := rfl

theorem sgn_append (ls ms : List (Layer (psig RD))) : sgn (ls ++ ms) = sgn ls * sgn ms := by
  simp [sgn]

theorem sgn_map_whisker (ls : List (Layer (psig RD))) (u : Obj (psig RD))
    (v : List (psig RD).Colour) : sgn (ls.map (·.whisker u v)) = sgn ls := by
  simp [sgn, Function.comp_def, Layer.whisker]

theorem sgn_sq (ls : List (Layer (psig RD))) : sgn ls * sgn ls = 1 := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    have : sgnG L.gen * sgnG L.gen = 1 := by
      unfold sgnG; split <;> (try split) <;> norm_num
    simp only [sgn, List.map_cons, List.prod_cons] at ih ⊢
    calc sgnG L.gen * (ls.map fun L => sgnG L.gen).prod *
          (sgnG L.gen * (ls.map fun L => sgnG L.gen).prod) =
        (sgnG L.gen * sgnG L.gen) * ((ls.map fun L => sgnG L.gen).prod *
          (ls.map fun L => sgnG L.gen).prod) := by ring
      _ = 1 := by rw [this, ih, one_mul]

end Sig

open Sig

/-! ## The reflection functor on the free 2-category -/

section Signed

variable [DecidableEq I]

/-- The signed reflection on the free 2-category. -/
def sigFree : Obj (psig RD) ⥤ (pres RD k).Presented where
  obj a := (pres RD k).obj (obj RD a)
  map d := ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (reflD d)
  map_id a := by
    rw [Diagram.layers_id, sgn_nil, Int.cast_one, one_smul, reflD_id, Presentation.diag_id]
  map_comp f g := by
    rw [Diagram.layers_comp, sgn_append, reflD_comp, Presentation.diag_comp, Int.cast_mul,
      Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

/-- The signed reflection of linear combinations of diagrams, in `U`. -/
abbrev sigL {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k).obj (obj RD a) ⟶ (pres RD k).obj (obj RD b) :=
  (freeLift k (sigFree RD k)).map f

variable {RD k}

theorem sigL_of {a b : Obj (psig RD)} (d : a ⟶ b) :
    sigL RD k (LinDiagram.of d) = ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (reflD d) :=
  freeLift_map_of _ d

theorem sigL_single {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    sigL RD k (Finsupp.single d r) =
      r • ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (reflD d) :=
  freeLift_map_single _ d r

theorem sigL_add' {a b : Obj (psig RD)} (f g : (a ⟶ b) →₀ k) :
    sigL RD k (f + g : (a ⟶ b) →₀ k) = sigL RD k f + sigL RD k g := Functor.map_add _

theorem sigL_single' {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    sigL RD k (Finsupp.single d r : (a ⟶ b) →₀ k) =
      r • ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (reflD d) :=
  freeLift_map_single _ d r

theorem sigL_zero {a b : Obj (psig RD)} : sigL RD k (0 : LinDiagram k a b) = 0 :=
  Functor.map_zero _ _ _

theorem sigL_add {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    sigL RD k (f + g) = sigL RD k f + sigL RD k g := Functor.map_add _

theorem sigL_sub {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    sigL RD k (f - g) = sigL RD k f - sigL RD k g := Functor.map_sub _

theorem sigL_neg {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    sigL RD k (-f) = -sigL RD k f := Functor.map_neg _

theorem sigL_smul {a b : Obj (psig RD)} (r : k) (f : LinDiagram k a b) :
    sigL RD k (r • f) = r • sigL RD k f := Functor.map_smul _ _ _

theorem sigL_comp {a b c : Obj (psig RD)} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    sigL RD k (f ≫ g) = sigL RD k f ≫ sigL RD k g := Functor.map_comp _ _ _

theorem sigL_id (a : Obj (psig RD)) : sigL RD k (𝟙 (Free.of k a)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

theorem sigL_sum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    sigL RD k (∑ x ∈ s, f x) = ∑ x ∈ s, sigL RD k (f x) :=
  Functor.map_sum _ _ _

/-! ## Whiskering -/


theorem sigL_whisker {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hs : b.start = a.start) (he : b.endR = a.endR) {u : Obj (psig RD)}
    {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    sigL RD k (LinDiagram.whisker f u v hw) =
      eqToHom (congrArg (pres RD k).obj (obj_whisker hw.2.1).symm) ≫
        (pres RD k).whisk (sigL RD k f) (sigW a v) (word RD u.word) ≫
          eqToHom (congrArg (pres RD k).obj (obj_whisker_cod hs he hw.2.1)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      sigL_zero, sigL_zero, Presentation.whisk_zero, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    rw [LinDiagram.whisker_add, sigL_add, hf, hg, sigL_add, Presentation.whisk_add,
      Preadditive.add_comp, Preadditive.comp_add]
  | single d r =>
    rw [LinDiagram.whisker_single, sigL_single, sigL_single, Diagram.layers_whisker,
      sgn_map_whisker, reflD_whisker d ha hw, Presentation.diag_cast, Presentation.whisk_smul,
      Presentation.whisk_smul, Presentation.whisk_diag _ _ _ _ (whiskerOK_obj ha hw)]
    simp only [Linear.smul_comp, Linear.comp_smul]
    rfl

theorem sigL_whisker_eq_zero {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hf : sigL RD k f = 0) {u : Obj (psig RD)} {v : List (psig RD).Colour}
    (hw : a.WhiskerOK u v) : sigL RD k (LinDiagram.whisker f u v hw) = 0 := by
  by_cases h0 : f = 0
  · subst h0
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      sigL_zero]
  · obtain ⟨d, -⟩ := Finsupp.ne_iff.mp h0
    rw [sigL_whisker f ha (Diagram.chain d).start_eq (Diagram.chain d).endR_eq hw, hf,
      Presentation.whisk_zero, Limits.zero_comp, Limits.comp_zero]

end Signed

/-! ## Normal forms -/

namespace Sig

variable {RD}

/-- The reflection of the shape of a generator. -/
def shape : Shape I → Shape I
  | .dot l => .dot l
  | .cross ε i j => .cross ε j i
  | .cup l => .cup l.dual
  | .cap l => .cap l.dual

@[simp] theorem shape_dot (l : Letter I) : shape (.dot l) = .dot l := rfl
@[simp] theorem shape_cross (ε : Bool) (i j : I) : shape (.cross ε i j) = .cross ε j i := rfl
@[simp] theorem shape_cup (l : Letter I) : shape (.cup l) = .cup l.dual := rfl
@[simp] theorem shape_cap (l : Letter I) : shape (.cap l) = .cap l.dual := rfl

theorem shape_dom (g : Shape I) : (shape g).dom = g.dom.reverse := by
  cases g <;> simp

theorem shape_cod (g : Shape I) : (shape g).cod = g.cod.reverse := by
  cases g <;> simp

/-- The reflection of a layer datum. -/
def ld (x : LayerData I) : LayerData I := (x.2.2.reverse, shape x.2.1, x.1.reverse)

/-- The reflection of a normal-form list of layers. -/
def sls (ls : List (LayerData I)) : List (LayerData I) := ls.map ld

theorem sls_append (ls ms : List (LayerData I)) : sls (ls ++ ms) = sls ls ++ sls ms :=
  List.map_append

theorem sls_replicate (n : ℕ) (x : LayerData I) : sls (List.replicate n x) = List.replicate n (ld x) :=
  List.map_replicate

theorem sChain_sls {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    SChain s.reverse (sls ls) t.reverse := by
  induction ls generalizing s with
  | nil => exact congrArg List.reverse h
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [ld, shape_dom], ?_⟩
    have := ih h
    simpa [ld, shape_cod] using this

/-- The sign of a shape. -/
def sgnSh [DecidableEq I] : Shape I → ℤ
  | .cross _ i j => if i = j then -1 else 1
  | _ => 1

/-- The sign of a normal-form list of layers. -/
def sgnS [DecidableEq I] (ls : List (LayerData I)) : ℤ := (ls.map fun x => sgnSh x.2.1).prod

theorem sgnG_gen_shape [DecidableEq I] (ν : X) (g : Shape I) :
    sgnG (g.gen RD ν) = sgnSh g := by
  cases g <;> rfl

theorem sgn_layList [DecidableEq I] (μ : X) (ls : List (LayerData I)) :
    sgn (layList RD μ ls) = sgnS ls := by
  simp only [sgn, layList, sgnS, List.map_map, Function.comp_def, lay, sgnG_gen_shape]

theorem wX_reverse (t : List (Letter I)) : RD.wX t.reverse = RD.wX t := by
  simp [UDot.RootDatum.wX, List.map_reverse, List.sum_reverse]

theorem word_wd (μ : X) (t : List (Letter I)) :
    word RD (wd RD μ t) = wd RD (-wt RD μ t) t.reverse := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [wd_cons, word_cons, ih, List.reverse_cons, wd_append]
    simp only [wd_cons, wd_nil, wt_cons, wt_nil, col]
    congr 2
    abel

/-- The reflection of the object `E_t 1_μ`, in normal form: `E_{t^rev} 1_ν` with
`ν = -(μ + t_X)`. -/
theorem trO (μ ν : X) (t : List (Letter I)) (h : ν = -wt RD μ t) :
    obj RD (ob RD μ t) = ob RD ν t.reverse := by
  subst h
  refine Obj.ext ?_ ?_
  · show -eR (RD := RD) (wt RD μ t) (wd RD μ t) = wt RD (-wt RD μ t) t.reverse
    rw [show eR (RD := RD) (wt RD μ t) (wd RD μ t) = μ from endR_wd RD μ t, wt_eq_add_wX,
      wt_eq_add_wX, wX_reverse]
    abel
  · exact word_wd μ t

theorem rlay_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    rlay (lay RD μ u g v) = lay RD (-wt RD μ (u ++ g.dom ++ v)) v.reverse (shape g) u.reverse := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · show -eR (RD := RD) ((psig RD).right (g.gen RD (wt RD μ v))) (wd RD μ v) =
      wt RD (-wt RD μ (u ++ g.dom ++ v)) (v.reverse ++ (shape g).dom ++ u.reverse)
    rw [Shape.right_gen, show eR (RD := RD) (wt RD μ v) (wd RD μ v) = μ from endR_wd RD μ v,
      wt_eq_add_wX, wt_eq_add_wX]
    simp only [UDot.RootDatum.wX_append, shape_dom, wX_reverse]
    abel
  · show word RD (wd RD μ v) = wd RD (wt RD (-wt RD μ (u ++ g.dom ++ v)) ((shape g).dom ++ u.reverse))
      v.reverse
    rw [word_wd]
    congr 1
    rw [wt_eq_add_wX, wt_eq_add_wX, wt_eq_add_wX]
    simp only [UDot.RootDatum.wX_append, shape_dom, wX_reverse]
    abel
  · show gen (g.gen RD (wt RD μ v)) = (shape g).gen RD (wt RD (-wt RD μ (u ++ g.dom ++ v)) u.reverse)
    have e : wt RD (-wt RD μ (u ++ g.dom ++ v)) u.reverse = -wt RD μ (g.dom ++ v) := by
      rw [wt_eq_add_wX, wt_eq_add_wX, wt_eq_add_wX]
      simp only [UDot.RootDatum.wX_append, wX_reverse]
      abel
    rw [e]
    cases g with
    | dot l => rfl
    | cross ε i j => rfl
    | cup l =>
      show (PivotalGen.cup (⟨l.dual, -(sh RD l.dual + wt RD μ v)⟩ : Col I X) : (psig RD).Gen) =
        PivotalGen.cup (⟨l.dual, sh RD l.dual.dual + -wt RD μ ([] ++ v)⟩ : Col I X)
      rw [Letter.dual_dual, sh_dual, List.nil_append, neg_add, neg_neg]
    | cap l =>
      simp only [Shape.gen, gen, shape_cap, Shape.dom_cap, List.cons_append, List.nil_append,
        wt_cons, sh_dual_add_sh_add]
  · show word RD (wd RD (wt RD μ (g.dom ++ v)) u) = wd RD (-wt RD μ (u ++ g.dom ++ v)) u.reverse
    rw [word_wd, List.append_assoc, wt_append RD μ u]

theorem layers_reflD_mkD (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) (hν : ν = -wt RD μ s) :
    Diagram.layers (reflD (mkD RD μ ls h)) = layList RD ν (sls ls) := by
  simp only [layers_reflD, layers_mkD, layList, sls, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  simp only [Function.comp_apply, rlay_lay, ld]
  rw [SChain.wt_mem RD μ h x hx, ← hν]

theorem reflD_mkD (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) (hν : ν = -wt RD μ s) :
    reflD (mkD RD μ ls h) = Diagram.cast (mkD RD ν (sls ls) (sChain_sls h))
      (trO μ ν s hν).symm (trO μ ν t (hν.trans (by rw [SChain.wt_eq RD μ h]))).symm :=
  Diagram.ext (layers_reflD_mkD μ ν ls h hν)

end Sig

open Sig

/-! ## Transport along equalities of objects -/

/-- Transport of 2-morphisms along equalities of their boundary objects. -/
def TR {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b') :
    ((pres RD k).obj a' ⟶ (pres RD k).obj b') →ₗ[k] ((pres RD k).obj a ⟶ (pres RD k).obj b) where
  toFun f := eqToHom (congrArg (pres RD k).obj ea) ≫ f ≫ eqToHom (congrArg (pres RD k).obj eb.symm)
  map_add' f g := by rw [Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [Linear.smul_comp, Linear.comp_smul]; rfl

variable {RD k}

theorem TR_apply {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    (f : (pres RD k).obj a' ⟶ (pres RD k).obj b') :
    TR RD k ea eb f =
      eqToHom (congrArg (pres RD k).obj ea) ≫ f ≫ eqToHom (congrArg (pres RD k).obj eb.symm) :=
  rfl

theorem TR_comp {a a' b b' c c' : Obj (psig RD)} (ea : a = a') (eb : b = b') (ec : c = c')
    (f : (pres RD k).obj a' ⟶ (pres RD k).obj b') (g : (pres RD k).obj b' ⟶ (pres RD k).obj c') :
    TR RD k ea eb f ≫ TR RD k eb ec g = TR RD k ea ec (f ≫ g) := by
  subst ea eb ec; simp [TR_apply]

theorem TR_diag {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b') (f : a' ⟶ b') :
    TR RD k ea eb ((pres RD k).diag f) = (pres RD k).diag (Diagram.cast f ea.symm eb.symm) := by
  rw [Presentation.diag_cast]; rfl

theorem TR_eq_zero {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    {f : (pres RD k).obj a' ⟶ (pres RD k).obj b'} : TR RD k ea eb f = 0 ↔ f = 0 := by
  subst ea eb; simp [TR_apply]

theorem TR_add_sub {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    (x y z : (pres RD k).obj a' ⟶ (pres RD k).obj b') :
    TR RD k ea eb x + TR RD k ea eb y - TR RD k ea eb z = TR RD k ea eb (x + y - z) := by
  rw [map_sub, map_add]

theorem TR_id {a a' : Obj (psig RD)} (ea : a = a') : TR RD k ea ea (𝟙 _) = 𝟙 _ := by
  subst ea; simp [TR_apply]

theorem TR_rfl {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    TR RD k rfl rfl f = f := by simp [TR_apply]

section Signed

variable [DecidableEq I]

/-- **`σ̃` on normal-form diagrams**: the reflected layers `(v^rev, shape g, u^rev)` with
rightmost region `ν = -(μ + s_X)`, times the sign, up to the identification of the reflected
objects with normal forms (`Sig.trO`). -/
theorem sigL_of_mkD (μ ν : X) {s t : List (Letter I)} (s' t' : List (Letter I))
    (ls : List (LayerData I)) (h : SChain s ls t) (hν : ν = -wt RD μ s) (hs : s.reverse = s')
    (ht : t.reverse = t') :
    sigL RD k (LinDiagram.of (mkD RD μ ls h)) =
      ((sgnS ls : ℤ) : k) • TR RD k (hs ▸ trO μ ν s hν)
        (ht ▸ trO μ ν t (hν.trans (by rw [SChain.wt_eq RD μ h])))
        (dg RD k ν s' t' (sls ls)) := by
  subst hs ht
  rw [sigL_of, layers_mkD, sgn_layList, reflD_mkD μ ν ls h hν, Presentation.diag_cast,
    dg_of (sChain_sls h)]
  rfl

end Signed


/-! ## The reflected relations hold -/

section Relations

variable [DecidableEq I]

omit [DecidableEq I] in
theorem ip_neg (i : I) (lam : X) : ip RD i (-lam) = -ip RD i lam := map_neg _ _

/-- Computes reflected normal-form lists of layers and their signs. -/
macro "sls_nf" : tactic => `(tactic| simp only [sls, ld, List.map_cons, List.map_nil,
  List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append,
  shape_dot, shape_cross, shape_cup, shape_cap, Letter.dual_up, Letter.dual_dn, sgnS, sgnSh,
  List.prod_cons, List.prod_nil, mul_one, one_mul, Int.cast_one, one_smul, if_pos, if_true,
  ite_true, Int.cast_neg, neg_smul, List.append_nil, eq_self_iff_true, ↓reduceIte])

theorem sigL_cycDotR (i : I) (μ : X) : sigL RD k (relation k (.cycDotR i μ : Rel RD)) = 0 := by
  have H := dg_cycDotL RD k i (-wt RD μ [dn i])
  rw [relation, sigL_sub, rotDotR, downDot, sigL_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl,
    sigL_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl]
  sls_nf
  rw [← H, sub_self]

theorem sigL_cycDotL (i : I) (μ : X) : sigL RD k (relation k (.cycDotL i μ : Rel RD)) = 0 := by
  have H := dg_cycDotR RD k i (-wt RD μ [dn i])
  rw [relation, sigL_sub, rotDotL, downDot, sigL_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl,
    sigL_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl]
  sls_nf
  rw [← H, sub_self]

theorem sigL_cycCrossR (j i : I) (μ : X) :
    sigL RD k (relation k (.cycCrossR j i μ : Rel RD)) = 0 := by
  have H := dg_cycCrossL RD k i j (-wt RD μ [dn j, dn i])
  rw [relation, sigL_sub, rotCrossR, downCross,
    sigL_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl,
    sigL_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl]
  sls_nf
  rw [← H, sub_self]

theorem sigL_cycCrossL (j i : I) (μ : X) :
    sigL RD k (relation k (.cycCrossL j i μ : Rel RD)) = 0 := by
  have H := dg_cycCrossR RD k i j (-wt RD μ [dn j, dn i])
  rw [relation, sigL_sub, rotCrossL, downCross,
    sigL_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl,
    sigL_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl]
  sls_nf
  rw [← H, sub_self]

theorem sigL_downupEF (i j : I) (h : i ≠ j) (μ : X) :
    sigL RD k (relation k (.downupEF i j h μ : Rel RD)) = 0 := by
  have H := dg_downupFE RD k j i (Ne.symm h) (-wt RD μ [up i, dn j])
  have e : -wt RD μ [up i, dn j] = -wt RD μ [dn j, up i] := by
    simp only [wt_cons, wt_nil]; abel
  rw [relation, sigL_sub, LinDiagram.of_comp, sigL_comp, crossl, crossr,
    sigL_of_mkD μ _ [dn j, up i] [up i, dn j] _ _ rfl rfl rfl,
    sigL_of_mkD μ _ [up i, dn j] [dn j, up i] _ _ e rfl rfl]
  sls_nf
  simp only [if_neg (Ne.symm h), if_neg h, Int.cast_one, one_smul]
  rw [TR_comp, dg_comp (by schain) (by schain)]
  erw [H, dg_nil, TR_id]
  rw [show (LinDiagram.of (𝟙 (ob RD μ [up i, dn j])) : LinDiagram k _ _) = 𝟙 (Free.of k _) from rfl,
    sub_eq_zero]
  exact (sigL_id _).symm

theorem sigL_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    sigL RD k (relation k (.downupFE i j h μ : Rel RD)) = 0 := by
  have H := dg_downupEF RD k j i (Ne.symm h) (-wt RD μ [dn i, up j])
  have e : -wt RD μ [dn i, up j] = -wt RD μ [up j, dn i] := by
    simp only [wt_cons, wt_nil]; abel
  rw [relation, sigL_sub, LinDiagram.of_comp, sigL_comp, crossl, crossr,
    sigL_of_mkD μ _ [up j, dn i] [dn i, up j] _ _ rfl rfl rfl,
    sigL_of_mkD μ _ [dn i, up j] [up j, dn i] _ _ e rfl rfl]
  sls_nf
  simp only [if_neg (Ne.symm h), if_neg h, Int.cast_one, one_smul]
  rw [TR_comp, dg_comp (by schain) (by schain)]
  erw [H, dg_nil, TR_id]
  rw [show (LinDiagram.of (𝟙 (ob RD μ [dn i, up j])) : LinDiagram k _ _) = 𝟙 (Free.of k _) from rfl,
    sub_eq_zero]
  exact (sigL_id _).symm

/-! ### Bubbles -/

omit [DecidableEq I] in
theorem TR_self {a b : Obj (psig RD)} (ea : a = a) (eb : b = b)
    (f : (pres RD k).obj a ⟶ (pres RD k).obj b) : TR RD k ea eb f = f := by
  simp [TR_apply]

theorem sgnS_bubble (l l' l'' : Letter I) (m : ℕ) (u u' v v' : List (Letter I)) :
    sgnS ([(u, .cup l, v)] ++ List.replicate m (u', .dot l', v') ++ [([], .cap l'', [])]) = 1 := by
  simp [sgnS, sgnSh, List.map_replicate, List.prod_replicate]

/-- `σ̃` sends the clockwise bubble with `m` dots in the region `λ` to the counterclockwise bubble
with `m` dots in the region `-λ`. -/
theorem sigL_cwReal (lam : X) (i : I) (m : ℕ) :
    sigL RD k (LinDiagram.of (cwReal RD lam i m)) = dg RD k (-lam) [] [] (ccwLs i m) := by
  rw [cwReal, sigL_of_mkD lam (-lam) [] [] _ _ rfl rfl rfl, sgnS_bubble, Int.cast_one, one_smul]
  refine (TR_self _ _ _).trans ?_
  rw [sls_append, sls_append, sls_replicate]
  show dg RD k (-lam) [] [] ([([], .cup (dn i), [])] ++ List.replicate m ([], .dot (dn i), [up i]) ++
    [([], .cap (up i), [])]) = _
  dstep [] [([], .cap (up i), [])] [] [] (dg_dots_cupDn RD k i (-lam) m).symm
  simp [ccwLs]

/-- `σ̃` sends the counterclockwise bubble with `m` dots in the region `λ` to the clockwise
bubble with `m` dots in the region `-λ`. -/
theorem sigL_ccwReal (lam : X) (i : I) (m : ℕ) :
    sigL RD k (LinDiagram.of (ccwReal RD lam i m)) = dg RD k (-lam) [] [] (cwLs i m) := by
  rw [ccwReal, sigL_of_mkD lam (-lam) [] [] _ _ rfl rfl rfl, sgnS_bubble, Int.cast_one, one_smul]
  refine (TR_self _ _ _).trans ?_
  rw [sls_append, sls_append, sls_replicate]
  show dg RD k (-lam) [] [] ([([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i]) ++
    [([], .cap (dn i), [])]) = _
  dstep [] [([], .cap (dn i), [])] [] [] (dg_dots_cupUp RD k i (-lam) m).symm
  simp [cwLs]

variable (RD k) in
/-- `σ̃` on `END(1_λ)`: a ring homomorphism to `END(1_{-λ})`. -/
def sigEnd (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k).obj (ob RD (-lam) [])) :=
  (functorEndAlg k (freeLift k (sigFree RD k)) (Free.of k (ob RD lam []))).toRingHom

theorem sigEnd_apply (lam : X) (f : LEnd RD k (ob RD lam [])) : sigEnd RD k lam f = sigL RD k f :=
  rfl

theorem sigL_ccwR (lam : X) (i : I) (m : ℤ) :
    sigL RD k (ccwR RD k lam i m) = (pres RD k).lin (cwR RD k (-lam) i m) := by
  unfold ccwR cwR
  split_ifs
  · rw [sigL_ccwReal, lin_cwReal]
  · rw [sigL_zero, Presentation.lin_zero]

theorem sigL_cwR (lam : X) (i : I) (m : ℤ) :
    sigL RD k (cwR RD k lam i m) = (pres RD k).lin (ccwR RD k (-lam) i m) := by
  unfold ccwR cwR
  split_ifs
  · rw [sigL_cwReal, lin_ccwReal]
  · rw [sigL_zero, Presentation.lin_zero]

/-- **`σ̃` sends the clockwise bubble with label `m` in the region `λ` to the counterclockwise
bubble with label `m` in the region `-λ`**, real or fake. -/
theorem sigL_cwL (lam : X) (i : I) (m : ℤ) :
    sigL RD k (cwL RD k lam i m) = ccwU RD k (-lam) i m := by
  unfold ccwU cwL ccwL
  simp only [ip_neg, ← sub_eq_add_neg, neg_neg]
  split_ifs
  · rw [sigL_cwReal, lin_ccwReal]
  · show sigEnd RD k lam _ = linEnd RD k (-lam) _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    rw [sigEnd_apply, sigL_ccwR]
    rfl
  · rw [sigL_zero, Presentation.lin_zero]

/-- **`σ̃` sends the counterclockwise bubble with label `m` in the region `λ` to the clockwise
bubble with label `m` in the region `-λ`**, real or fake. -/
theorem sigL_ccwL (lam : X) (i : I) (m : ℤ) :
    sigL RD k (ccwL RD k lam i m) = cwU RD k (-lam) i m := by
  unfold cwU cwL ccwL
  simp only [ip_neg, ← sub_eq_add_neg, neg_neg, sub_neg_eq_add]
  split_ifs
  · rw [sigL_ccwReal, lin_cwReal]
  · show sigEnd RD k lam _ = linEnd RD k (-lam) _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    rw [sigEnd_apply, sigL_cwR]
    rfl
  · rw [sigL_zero, Presentation.lin_zero]

theorem sigL_cwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < ip RD i lam - 1) :
    sigL RD k (relation k (.cwNeg i lam α h : Rel RD)) = 0 := by
  rw [relation, sigL_cwReal]
  exact dg_ccwNeg RD k (-lam) i α (by rw [ip_neg]; omega)

theorem sigL_ccwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < -ip RD i lam - 1) :
    sigL RD k (relation k (.ccwNeg i lam α h : Rel RD)) = 0 := by
  rw [relation, sigL_ccwReal]
  exact dg_cwNeg RD k (-lam) i α (by rw [ip_neg]; omega)

theorem sigL_cwOne (i : I) (lam : X) (h : 1 ≤ ip RD i lam) :
    sigL RD k (relation k (.cwOne i lam h : Rel RD)) = 0 := by
  rw [relation, sigL_sub, sigL_cwReal, sub_eq_zero]
  have H := dg_ccwOne RD k (-lam) i (by rw [ip_neg]; omega)
  rw [ip_neg, neg_neg, dg_nil] at H
  exact H.trans (sigL_id (RD := RD) (k := k) (ob RD lam [])).symm

theorem sigL_ccwOne (i : I) (lam : X) (h : ip RD i lam ≤ -1) :
    sigL RD k (relation k (.ccwOne i lam h : Rel RD)) = 0 := by
  rw [relation, sigL_sub, sigL_ccwReal, sub_eq_zero]
  have H := dg_cwOne RD k (-lam) i (by rw [ip_neg]; omega)
  rw [ip_neg, dg_nil] at H
  exact H.trans (sigL_id (RD := RD) (k := k) (ob RD lam [])).symm

/-! ### Bubbles next to strands -/

omit [DecidableEq I] in
theorem reflD_cast {a b a' b' : Obj (psig RD)} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    reflD (Diagram.cast f ha hb) = Diagram.cast (reflD f) (congrArg (obj RD) ha)
      (congrArg (obj RD) hb) :=
  Diagram.ext rfl

omit [DecidableEq I] in
theorem bubR_zero (lam : X) (t : List (Letter I)) : bubR RD k lam t 0 = 0 := by
  simp [bubR, LinDiagram.whisker, LinDiagram.cast]

omit [DecidableEq I] in
theorem bubR_add (lam : X) (t : List (Letter I)) (f g : (ob RD lam [] ⟶ ob RD lam []) →₀ k) :
    bubR RD k lam t (f + g) = bubR RD k lam t f + bubR RD k lam t g := by
  simp only [bubR, LinDiagram.cast, LinDiagram.whisker, Finsupp.mapDomain_add]

omit [DecidableEq I] in
theorem bubL_zero (μ : X) (t : List (Letter I)) : bubL RD k μ t 0 = 0 := by
  simp [bubL, LinDiagram.whisker, LinDiagram.cast]

omit [DecidableEq I] in
theorem bubL_add (μ : X) (t : List (Letter I))
    (f g : (ob RD (wt RD μ t) [] ⟶ ob RD (wt RD μ t) []) →₀ k) :
    bubL RD k μ t (f + g) = bubL RD k μ t f + bubL RD k μ t g := by
  simp only [bubL, LinDiagram.cast, LinDiagram.whisker, Finsupp.mapDomain_add]

omit [DecidableEq I] in
/-- The region of the bubble in the reflection of a bubble to the right of a strand. -/
theorem region_bubR (lam : X) (l : Letter I) :
    ob RD (wt RD (-wt RD lam [l]) [l]) [] = ob RD (-lam) [] :=
  Obj.ext (by simp only [ob_start, wt_cons, wt_nil]; abel) rfl

/-- **`σ̃` moves a bubble to the right of a strand to its left** (and `λ ↦ -λ`). -/
theorem sigL_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    sigL RD k (bubR RD k lam [l] b) =
      TR RD k (trO lam (-wt RD lam [l]) [l] rfl) (trO lam (-wt RD lam [l]) [l] rfl)
        (bubLU RD k (-wt RD lam [l]) l
          (TR RD k (region_bubR lam l) (region_bubR lam l) (sigL RD k b))) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [bubR_zero, sigL_zero, map_zero]
  | add f g hf hg =>
    rw [bubR_add, sigL_add, hf, hg, sigL_add' f g]
    simp only [bubLU, map_add]
  | single d r =>
    have e : bubR RD k lam [l] (Finsupp.single d r) = Finsupp.single (Diagram.cast
        (Diagram.whisker d (ob RD lam [l]) [] (whiskerOK_right RD lam [l]))
        (whisker_right_eq RD lam [l]) (whisker_right_eq RD lam [l])) r := by
      simp only [bubR, LinDiagram.cast, LinDiagram.whisker, Finsupp.mapDomain_single]
    rw [e, sigL_single, sigL_single', Diagram.layers_cast, Diagram.layers_whisker,
      sgn_map_whisker]
    simp only [bubLU, map_smul]
    congr 2
    rw [TR_diag, plcL_diag, TR_diag, reflD_cast, reflD_whisker d trivial]
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [Diagram.layers_cast, Diagram.layers_whisker]
    congr 1
    funext L
    congr 1
    exact Obj.ext (by simp only [sigW, ob_start, wt_nil]; simp; abel) rfl

/-- **`σ̃` moves a bubble to the left of a strand to its right** (and `λ ↦ -λ`). -/
theorem sigL_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    sigL RD k (bubL RD k μ [l] b) =
      TR RD k (trO μ (-wt RD μ [l]) [l] rfl) (trO μ (-wt RD μ [l]) [l] rfl)
        (bubRU RD k (-wt RD μ [l]) l (sigL RD k b)) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [bubL_zero, sigL_zero, map_zero]
  | add f g hf hg =>
    rw [bubL_add, sigL_add, hf, hg, sigL_add' f g]
    simp only [bubRU, map_add]
  | single d r =>
    have e : bubL RD k μ [l] (Finsupp.single d r) = Finsupp.single (Diagram.cast
        (Diagram.whisker d (ob RD (wt RD μ [l]) []) (wd RD μ [l]) (whiskerOK_left RD μ [l]))
        (whisker_left_eq RD μ [l]) (whisker_left_eq RD μ [l])) r := by
      simp only [bubL, LinDiagram.cast, LinDiagram.whisker, Finsupp.mapDomain_single]
    rw [e, sigL_single, sigL_single', Diagram.layers_cast, Diagram.layers_whisker,
      sgn_map_whisker]
    simp only [bubRU, map_smul]
    congr 2
    rw [plcL_diag, TR_diag, reflD_cast, reflD_whisker d trivial]
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [Diagram.layers_cast, Diagram.layers_whisker]
    congr 1
    funext L
    congr 1
    exact Obj.ext (by simp only [sigW, ob_start, wt_nil]; simp; abel) rfl

/-! ### Curls -/

theorem sigL_dots (lam : X) (l : Letter I) (m : ℕ) :
    sigL RD k (LinDiagram.of (dots RD lam [] l [] m)) =
      TR RD k (trO lam (-wt RD lam [l]) [l] rfl) (trO lam (-wt RD lam [l]) [l] rfl)
        (dotsU RD k (-wt RD lam [l]) l m) := by
  rw [dots, sigL_of_mkD lam _ [l] [l] _ _ rfl rfl rfl]
  have hs : sgnS (List.replicate m (([] : List (Letter I)), Shape.dot l, ([] : List (Letter I)))) = 1 := by
    simp [sgnS, sgnSh, List.map_replicate, List.prod_replicate]
  rw [hs, Int.cast_one, one_smul, sls_replicate]
  rfl

omit [DecidableEq I] in
theorem ccwU_TR {ρ ρ' : X} (h : ob RD ρ [] = ob RD ρ' []) (i : I) (m : ℤ) :
    TR RD k h h (ccwU RD k ρ' i m) = ccwU RD k ρ i m := by
  obtain rfl : ρ = ρ' := congrArg Obj.start h
  exact TR_self _ _ _

omit [DecidableEq I] in
theorem cwU_TR {ρ ρ' : X} (h : ob RD ρ [] = ob RD ρ' []) (i : I) (m : ℤ) :
    TR RD k h h (cwU RD k ρ' i m) = cwU RD k ρ i m := by
  obtain rfl : ρ = ρ' := congrArg Obj.start h
  exact TR_self _ _ _

theorem sigL_curlR (i : I) (lam : X) : sigL RD k (relation k (.curlR i lam : Rel RD)) = 0 := by
  have H := dg_curlL RD k i (-wt RD lam [up i])
  have hip : ip RD i (wt RD (-wt RD lam [up i]) [up i]) = -ip RD i lam := by
    rw [show wt RD (-wt RD lam [up i]) [up i] = -lam by simp only [wt_cons, wt_nil]; abel, ip_neg]
  rw [hip] at H
  simp only [neg_neg] at H
  have hsum : sigL RD k (curlRHS RD k i lam) =
      -TR RD k (trO lam (-wt RD lam [up i]) [up i] rfl) (trO lam (-wt RD lam [up i]) [up i] rfl)
        (∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
          bubLU RD k (-wt RD lam [up i]) (up i)
            (ccwU RD k (wt RD (-wt RD lam [up i]) [up i]) i (ip RD i lam - 1 + f)) ≫
          dotsU RD k (-wt RD lam [up i]) (up i) (-ip RD i lam - f).toNat) := by
    rw [curlRHS, sigL_neg, sigL_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigL_comp, sigL_bubR, sigL_cwL, sigL_dots, TR_comp, ccwU_TR]
  rw [relation, sigL_sub, curlR, sigL_of_mkD lam _ [up i] [up i] _ _ rfl rfl rfl, hsum]
  sls_nf
  rw [H, sub_neg_eq_add]
  exact neg_add_cancel _

theorem sigL_curlL (i : I) (μ : X) : sigL RD k (relation k (.curlL i μ : Rel RD)) = 0 := by
  have H := dg_curlR RD k i (-wt RD μ [up i])
  have hip : ip RD i (-wt RD μ [up i]) = -ip RD i (wt RD μ [up i]) := ip_neg i _
  rw [hip] at H
  simp only [neg_neg] at H
  have hsum : sigL RD k (curlLHS RD k i μ) =
      TR RD k (trO μ (-wt RD μ [up i]) [up i] rfl) (trO μ (-wt RD μ [up i]) [up i] rfl)
        (∑ g ∈ Finset.range (ip RD i (wt RD μ [up i]) + 1).toNat,
          bubRU RD k (-wt RD μ [up i]) (up i)
            (cwU RD k (-wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)) ≫
          dotsU RD k (-wt RD μ [up i]) (up i) (ip RD i (wt RD μ [up i]) - g).toNat) := by
    rw [curlLHS, sigL_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigL_comp, sigL_bubL, sigL_ccwL, sigL_dots, TR_comp]
  rw [relation, sigL_sub, curlL, sigL_of_mkD μ _ [up i] [up i] _ _ rfl rfl rfl, hsum]
  sls_nf
  rw [H, map_neg, neg_neg]
  exact sub_self _

/-! ### The decompositions of `1_{EF1_λ}` and `1_{FE1_λ}` -/

omit [DecidableEq I] in
theorem TR_comp_mid {a a' b c c' : Obj (psig RD)} (ea : a = a') (eb : b = b) (ec : c = c')
    (f : (pres RD k).obj a' ⟶ (pres RD k).obj b) (x : (pres RD k).obj b ⟶ (pres RD k).obj b)
    (g : (pres RD k).obj b ⟶ (pres RD k).obj c') :
    TR RD k ea eb f ≫ x ≫ TR RD k eb ec g = TR RD k ea ec (f ≫ x ≫ g) := by
  subst ea ec; simp [TR_apply]

theorem sgnS_dots_cap (m : ℕ) (x y : LayerData I) (hx' : ∃ l, x.2.1 = .dot l)
    (hy : ∃ l, y.2.1 = .cap l) :
    sgnS (List.replicate m x ++ [y]) = 1 := by
  obtain ⟨l, hl⟩ := hx'
  obtain ⟨l', hl'⟩ := hy
  simp [sgnS, sgnSh, List.map_replicate, List.prod_replicate, hl, hl']

theorem sgnS_cup_dots (m : ℕ) (x y : LayerData I) (hx' : ∃ l, x.2.1 = .dot l)
    (hy : ∃ l, y.2.1 = .cup l) : sgnS ([y] ++ List.replicate m x) = 1 := by
  obtain ⟨l, hl⟩ := hx'
  obtain ⟨l', hl'⟩ := hy
  simp [sgnS, sgnSh, List.map_replicate, List.prod_replicate, hl, hl']

theorem sigL_of_dotCapEF (i : I) (lam : X) (h : -lam = -wt RD lam [up i, dn i]) (m : ℕ) :
    sigL RD k (LinDiagram.of (dotCapEF RD lam i m)) =
      TR RD k (trO lam (-lam) [up i, dn i] h) (trO lam (-lam) [] rfl)
        (dg RD k (-lam) [dn i, up i] [] (dotCapFELs i m)) := by
  rw [dotCapEF, sigL_of_mkD lam (-lam) [dn i, up i] [] _ _ h rfl rfl,
    sgnS_dots_cap m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul,
    sls_append, sls_replicate]
  congr 1
  exact (dg_dots_cap_up RD k (-lam) i m).symm

theorem sigL_of_cupDotEF (i : I) (lam : X) (h : -lam = -wt RD lam [up i, dn i]) (m : ℕ) :
    sigL RD k (LinDiagram.of (cupDotEF RD lam i m)) =
      TR RD k (trO lam (-lam) [] rfl) (trO lam (-lam) [up i, dn i] h)
        (dg RD k (-lam) [] [dn i, up i] (cupDotFELs i m)) := by
  rw [cupDotEF, sigL_of_mkD lam (-lam) [] [dn i, up i] _ _ rfl rfl rfl,
    sgnS_cup_dots m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul, sls_append, sls_replicate]
  congr 1
  exact (dg_dots_cupDn RD k i (-lam) m).symm

theorem sigL_of_dotCapFE (i : I) (lam : X) (h : -lam = -wt RD lam [dn i, up i]) (m : ℕ) :
    sigL RD k (LinDiagram.of (dotCapFE RD lam i m)) =
      TR RD k (trO lam (-lam) [dn i, up i] h) (trO lam (-lam) [] rfl)
        (dg RD k (-lam) [up i, dn i] [] (dotCapEFLs i m)) := by
  rw [dotCapFE, sigL_of_mkD lam (-lam) [up i, dn i] [] _ _ h rfl rfl,
    sgnS_dots_cap m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul,
    sls_append, sls_replicate]
  congr 1
  exact dg_dots_cap_dn RD k (-lam) i m

theorem sigL_of_cupDotFE (i : I) (lam : X) (h : -lam = -wt RD lam [dn i, up i]) (m : ℕ) :
    sigL RD k (LinDiagram.of (cupDotFE RD lam i m)) =
      TR RD k (trO lam (-lam) [] rfl) (trO lam (-lam) [dn i, up i] h)
        (dg RD k (-lam) [] [up i, dn i] (cupDotEFLs i m)) := by
  rw [cupDotFE, sigL_of_mkD lam (-lam) [] [up i, dn i] _ _ rfl rfl rfl,
    sgnS_cup_dots m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul, sls_append, sls_replicate]
  congr 1
  exact (dg_dots_cupUp RD k i (-lam) m).symm

theorem sigL_decompEF (i : I) (lam : X) :
    sigL RD k (relation k (.decompEF i lam : Rel RD)) = 0 := by
  have h1 : -lam = -wt RD lam [up i, dn i] := by simp
  have h2 : -lam = -wt RD lam [dn i, up i] := by simp
  have H := dg_decompFE RD k i (-lam)
  simp only [ip_neg, neg_neg] at H
  have hsum : sigL RD k (decompEFSum RD k i lam) =
      TR RD k (trO lam (-lam) [up i, dn i] h1) (trO lam (-lam) [up i, dn i] h1)
        (∑ f ∈ Finset.range (ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          dg RD k (-lam) [dn i, up i] [] (dotCapFELs i (f - g)) ≫
            cwU RD k (-lam) i (-ip RD i lam - 1 + g) ≫
              dg RD k (-lam) [] [dn i, up i] (cupDotFELs i ((ip RD i lam).toNat - 1 - f))) := by
    unfold decompEFSum
    rw [sigL_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigL_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [sigL_comp, sigL_comp, sigL_of_dotCapEF i lam h1, sigL_ccwL, sigL_of_cupDotEF i lam h1]
    exact TR_comp_mid _ _ _ _ _ _
  have hid : sigL RD k (LinDiagram.of (𝟙 (ob RD lam [up i, dn i]))) =
      TR RD k (trO lam (-lam) [up i, dn i] h1) (trO lam (-lam) [up i, dn i] h1)
        (dg RD k (-lam) [dn i, up i] [dn i, up i] []) := by
    rw [dg_nil]; exact (sigL_id _).trans (TR_id _).symm
  have hcross : sigL RD k (LinDiagram.of (crossl RD i i lam)) ≫
      sigL RD k (LinDiagram.of (crossr RD i i lam)) =
      TR RD k (trO lam (-lam) [up i, dn i] h1) (trO lam (-lam) [up i, dn i] h1)
        (dg RD k (-lam) [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i)) := by
    rw [crossl, crossr, sigL_of_mkD lam (-lam) [dn i, up i] [up i, dn i] _ _ h1 rfl rfl,
      sigL_of_mkD lam (-lam) [up i, dn i] [dn i, up i] _ _ h2 rfl rfl]
    sls_nf
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, TR_comp,
      dg_comp (by schain) (by schain)]
    rfl
  rw [relation, sigL_sub, sigL_add, hid, LinDiagram.of_comp, sigL_comp, hcross, hsum]
  refine (TR_add_sub _ _ _ _ _).trans ?_
  rw [TR_eq_zero, H]
  abel

theorem sigL_decompFE (i : I) (lam : X) :
    sigL RD k (relation k (.decompFE i lam : Rel RD)) = 0 := by
  have h1 : -lam = -wt RD lam [dn i, up i] := by simp
  have h2 : -lam = -wt RD lam [up i, dn i] := by simp
  have H := dg_decompEF RD k i (-lam)
  simp only [ip_neg, neg_neg] at H
  have hsum : sigL RD k (decompFESum RD k i lam) =
      TR RD k (trO lam (-lam) [dn i, up i] h1) (trO lam (-lam) [dn i, up i] h1)
        (∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          dg RD k (-lam) [up i, dn i] [] (dotCapEFLs i (f - g)) ≫
            ccwU RD k (-lam) i (ip RD i lam - 1 + g) ≫
              dg RD k (-lam) [] [up i, dn i] (cupDotEFLs i ((-ip RD i lam).toNat - 1 - f))) := by
    unfold decompFESum
    rw [sigL_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigL_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [sigL_comp, sigL_comp, sigL_of_dotCapFE i lam h1, sigL_cwL, sigL_of_cupDotFE i lam h1]
    exact TR_comp_mid _ _ _ _ _ _
  have hid : sigL RD k (LinDiagram.of (𝟙 (ob RD lam [dn i, up i]))) =
      TR RD k (trO lam (-lam) [dn i, up i] h1) (trO lam (-lam) [dn i, up i] h1)
        (dg RD k (-lam) [up i, dn i] [up i, dn i] []) := by
    rw [dg_nil]; exact (sigL_id _).trans (TR_id _).symm
  have hcross : sigL RD k (LinDiagram.of (crossr RD i i lam)) ≫
      sigL RD k (LinDiagram.of (crossl RD i i lam)) =
      TR RD k (trO lam (-lam) [dn i, up i] h1) (trO lam (-lam) [dn i, up i] h1)
        (dg RD k (-lam) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i)) := by
    rw [crossr, crossl, sigL_of_mkD lam (-lam) [up i, dn i] [dn i, up i] _ _ h1 rfl rfl,
      sigL_of_mkD lam (-lam) [dn i, up i] [up i, dn i] _ _ h2 rfl rfl]
    sls_nf
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, TR_comp,
      dg_comp (by schain) (by schain)]
    rfl
  rw [relation, sigL_sub, sigL_add, hid, LinDiagram.of_comp, sigL_comp, hcross, hsum]
  refine (TR_add_sub _ _ _ _ _).trans ?_
  rw [TR_eq_zero, H]
  abel

end Relations

/-! ## The reflection of KLR diagrams across the `y`-axis -/

/-- Reordering commuting variables: `ncEval (y ∘ f) p = ncEval y (rename f p)` for a family `y`
of pairwise commuting elements. -/
theorem ncEval_rename_of_commute {A : Type*} [Ring A] [Algebra k A] {n m : ℕ} (y : Fin n → A)
    (hc : ∀ a b, Commute (y a) (y b)) (f : Fin m → Fin n) (p : MvPolynomial (Fin m) k) :
    KLR.ncEval (fun a => y (f a)) p = KLR.ncEval y (MvPolynomial.rename f p) := by
  letI : CommRing (Algebra.adjoin k (Set.range y)) :=
    Algebra.adjoinCommRingOfComm k (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hc a b)
  let y' : Fin n → Algebra.adjoin k (Set.range y) := fun a => ⟨y a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
  let φ : MvPolynomial (Fin n) k →ₐ[k] A :=
    (Algebra.adjoin k (Set.range y)).val.comp (MvPolynomial.aeval y')
  have hφ : ∀ a, φ (MvPolynomial.X a) = y a := by
    intro a; simp [φ, y']
  have h1 := KLR.ncEval_algHom_X φ f p
  have h2 := KLR.ncEval_algHom_X φ id (MvPolynomial.rename f p)
  simp only [hφ, id] at h1 h2
  rw [h1, h2, MvPolynomial.rename_id]
  rfl

namespace KSig

/-- The reflection of a KLR generator across the `y`-axis. -/
def kgen : KLR.Diagram.Gen I → KLR.Diagram.Gen I
  | .dot c => .dot c
  | .cross c d => .cross d c

theorem kgen_dom (g : KLR.Diagram.Gen I) : (kgen g).dom = g.dom.reverse := by cases g <;> rfl
theorem kgen_cod (g : KLR.Diagram.Gen I) : (kgen g).cod = g.cod.reverse := by cases g <;> rfl

/-- The reflection of a KLR layer. -/
def klay (L : Layer (KLR.Diagram.sig I)) : Layer (KLR.Diagram.sig I) :=
  ⟨(), L.right.reverse, kgen L.gen, L.left.reverse⟩

/-- The reflection of a KLR object: the reversed sequence. -/
def kobj (a : Obj (KLR.Diagram.sig I)) : Obj (KLR.Diagram.sig I) := ⟨(), a.word.reverse⟩

theorem klay_dom (L : Layer (KLR.Diagram.sig I)) : (klay L).dom = kobj L.dom :=
  KLR.Diagram.obj_ext (by simp [klay, kobj, Layer.dom, kgen_dom])

theorem klay_cod (L : Layer (KLR.Diagram.sig I)) : (klay L).cod = kobj L.cod :=
  KLR.Diagram.obj_ext (by simp [klay, kobj, Layer.cod, kgen_cod])

theorem chain_map {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) : Chain (kobj a) (ls.map klay) (kobj b) := by
  induction ls generalizing a with
  | nil => exact congrArg kobj h
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    exact ⟨Layer.valid_of_subsingleton _, klay_dom L, by rw [klay_cod]; exact ih hc⟩

/-- The reflection of a KLR diagram. -/
def ksD {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) : kobj a ⟶ kobj b :=
  Diagram.mk ((Diagram.layers d).map klay) (chain_map (Diagram.chain d))

theorem ksD_comp {a b c : Obj (KLR.Diagram.sig I)} (f : a ⟶ b) (g : b ⟶ c) :
    ksD (f ≫ g) = ksD f ≫ ksD g := by
  apply Diagram.ext; simp [ksD]

variable [DecidableEq I]

/-- The sign of a KLR generator: `-1` for a crossing of two strands with the same label. -/
def ksg : KLR.Diagram.Gen I → ℤ
  | .dot _ => 1
  | .cross c d => if c = d then -1 else 1

/-- The sign of a list of KLR layers. -/
def ksgn (ls : List (Layer (KLR.Diagram.sig I))) : ℤ := (ls.map fun L => ksg L.gen).prod

theorem ksgn_append (ls ms : List (Layer (KLR.Diagram.sig I))) :
    ksgn (ls ++ ms) = ksgn ls * ksgn ms := by
  simp [ksgn]

variable (Q : I → I → MvPolynomial (Fin 2) k)

/-- The signed reflection of KLR diagrams, with values in the presented KLR category. -/
def ksFree : Obj (KLR.Diagram.sig I) ⥤ (KLR.Diagram.pres k Q).Presented where
  obj a := (KLR.Diagram.pres k Q).obj (kobj a)
  map d := ((ksgn (Diagram.layers d) : ℤ) : k) • (KLR.Diagram.pres k Q).diag (ksD d)
  map_id a := by
    show ((ksgn [] : ℤ) : k) • (KLR.Diagram.pres k Q).diag (ksD (𝟙 a)) = _
    rw [show ksgn ([] : List (Layer (KLR.Diagram.sig I))) = 1 from rfl, Int.cast_one, one_smul,
      show ksD (𝟙 a) = 𝟙 (kobj a) from rfl, Presentation.diag_id]
  map_comp f g := by
    rw [Diagram.layers_comp, ksgn_append, ksD_comp, Presentation.diag_comp, Int.cast_mul,
      Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

/-- The signed reflection of linear combinations of KLR diagrams. -/
abbrev ksL {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    (KLR.Diagram.pres k Q).obj (kobj a) ⟶ (KLR.Diagram.pres k Q).obj (kobj b) :=
  (freeLift k (ksFree Q)).map f

variable {Q}

theorem ksL_of {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    ksL Q (LinDiagram.of d) =
      ((ksgn (Diagram.layers d) : ℤ) : k) • (KLR.Diagram.pres k Q).diag (ksD d) :=
  freeLift_map_of _ d

theorem ksL_sub {a b : Obj (KLR.Diagram.sig I)} (f g : LinDiagram k a b) :
    ksL Q (f - g) = ksL Q f - ksL Q g := Functor.map_sub _

theorem ksL_one (a : Obj (KLR.Diagram.sig I)) :
    ksL Q (LinDiagram.of (𝟙 a)) = 𝟙 _ := by
  rw [ksL_of]
  show ((ksgn [] : ℤ) : k) • (KLR.Diagram.pres k Q).diag (ksD (𝟙 a)) = _
  rw [show ksgn ([] : List (Layer (KLR.Diagram.sig I))) = 1 from rfl, Int.cast_one, one_smul,
    show ksD (𝟙 a) = 𝟙 (kobj a) from rfl, Presentation.diag_id]

variable (Q) in
/-- The signed reflection on endomorphism algebras. -/
def ksEnd (w : Obj (KLR.Diagram.sig I)) :
    End (Free.of k w) →ₐ[k] End ((KLR.Diagram.pres k Q).obj (kobj w)) :=
  functorEndAlg k (freeLift k (ksFree Q)) (Free.of k w)

theorem ksEnd_apply (w : Obj (KLR.Diagram.sig I)) (f : End (Free.of k w)) :
    ksEnd Q w f = ksL Q f := rfl

open KLR.Diagram in
theorem ksL_lpoly {w : Obj (KLR.Diagram.sig I)} {n : ℕ} (y : Fin n → (w ⟶ w))
    (p : MvPolynomial (Fin n) k) :
    ksL Q (lpoly k y p) = KLR.ncEval (A := End ((KLR.Diagram.pres k Q).obj (kobj w)))
      (fun a => ksL Q (LinDiagram.of (y a))) p := by
  rw [← ksEnd_apply, lpoly, AlgHom.map_ncEval]
  rfl

open KLR.Diagram in
/-- **The KLR relations with the KL II polynomials are symmetric under the reflection across the
`y`-axis with the sign `-1` on every crossing of equally labelled strands** (KL I, end of §2.1,
the involution `σ`; KL III §3.3.2). -/
theorem ksL_relation (r : KLR.Diagram.Rel I) :
    ksL (KLR.klQ2 k C) (KLR.Diagram.relation k (KLR.klQ2 k C) r) = 0 := by
  cases r with
  | sqEq c =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (X2 c c ≫ X2 c c)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.sqEq c)
    show ksL _ (LinDiagram.of (X2 c c ≫ X2 c c)) = 0
    rw [ksL_of, show ksD (X2 c c ≫ X2 c c) = X2 c c ≫ X2 c c from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, if_pos rfl]
    norm_num
    rw [← Presentation.diag_comp]
    exact H
  | sqNe c d h =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (X2 d c ≫ X2 c d) -
        lpoly k ![D0 d c, D1 d c] (KLR.klQ2 k C d c)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.sqNe d c (Ne.symm h))
    rw [Presentation.lin_sub, Presentation.lin_of, ← KLR.Diagram.linAlg_apply, lpoly,
      AlgHom.map_ncEval] at H
    show ksL _ (LinDiagram.of (X2 c d ≫ X2 d c) - lpoly k ![D0 c d, D1 c d] (KLR.klQ2 k C c d)) = 0
    rw [ksL_sub, ksL_of, ksL_lpoly,
      show ksD (X2 c d ≫ X2 d c) = X2 d c ≫ X2 c d from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, if_neg h,
      if_neg (Ne.symm h), mul_one, Int.cast_one, one_smul]
    rw [sub_eq_zero] at H ⊢
    rw [H]
    have e : (fun a => ksL (KLR.klQ2 k C) (LinDiagram.of ((![D0 c d, D1 c d] : Fin 2 → _) a))) =
        ![(KLR.Diagram.pres k (KLR.klQ2 k C)).diag (D1 d c),
          (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (D0 d c)] := by
      funext a
      fin_cases a
      · show ksL _ (LinDiagram.of (D0 c d)) = (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (D1 d c)
        rw [ksL_of, show ksD (D0 c d) = D1 d c from Diagram.ext rfl]
        simp [ksgn, ksg]
      · show ksL _ (LinDiagram.of (D1 c d)) = (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (D0 d c)
        rw [ksL_of, show ksD (D1 c d) = D0 d c from Diagram.ext rfl]
        simp [ksgn, ksg]
    rw [e]
    simp only [KLR.Diagram.linAlg_apply, Presentation.lin_of]
    unfold KLR.klQ2
    by_cases hcd : C.dot c d = 0
    · rw [if_pos hcd, if_pos (by rw [C.symm]; exact hcd), ncEval_one_aux, ncEval_one_aux]
    · rw [if_neg hcd, if_neg (by rw [C.symm]; exact hcd), ncEval_X_pow_add_X_pow,
        ncEval_X_pow_add_X_pow]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact add_comm _ _
  | slideLEq c =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (D0 c c ≫ X2 c c) -
        LinDiagram.of (X2 c c ≫ D1 c c) - LinDiagram.of (𝟙 _)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.slideREq c)
    rw [Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of,
      Presentation.lin_of, Presentation.diag_id] at H
    show ksL _ (LinDiagram.of (X2 c c ≫ D0 c c) - LinDiagram.of (D1 c c ≫ X2 c c) -
      LinDiagram.of (𝟙 _)) = 0
    have h1 : ksL (KLR.klQ2 k C) (LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c]))) =
        𝟙 ((KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob [c, c])) := ksL_one _
    have s1 : ksgn (Diagram.layers (X2 c c ≫ D0 c c)) = -1 := by simp [ksgn, ksg]
    have s2 : ksgn (Diagram.layers (D1 c c ≫ X2 c c)) = -1 := by simp [ksgn, ksg]
    rw [ksL_sub, ksL_sub, ksL_of, ksL_of, h1, s1, s2,
      show ksD (X2 c c ≫ D0 c c) = X2 c c ≫ D1 c c from Diagram.ext rfl,
      show ksD (D1 c c ≫ X2 c c) = D0 c c ≫ X2 c c from Diagram.ext rfl, ← H]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    have key : ∀ x y z : (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob [c, c]) ⟶
        (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob [c, c]),
        -x - -y - z = y - x - z := fun x y z => by abel
    exact key _ _ _
  | slideLNe c d h =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (D0 d c ≫ X2 d c) -
        LinDiagram.of (X2 d c ≫ D1 c d)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.slideRNe d c (Ne.symm h))
    rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of] at H
    show ksL _ (LinDiagram.of (X2 c d ≫ D0 d c) - LinDiagram.of (D1 c d ≫ X2 c d)) = 0
    rw [ksL_sub, ksL_of, ksL_of,
      show ksD (X2 c d ≫ D0 d c) = X2 d c ≫ D1 c d from Diagram.ext rfl,
      show ksD (D1 c d ≫ X2 c d) = D0 d c ≫ X2 d c from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, if_neg h, mul_one,
      one_mul, Int.cast_one, one_smul]
    rw [← neg_eq_zero, neg_sub]
    exact H
  | slideREq c =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (X2 c c ≫ D0 c c) -
        LinDiagram.of (D1 c c ≫ X2 c c) - LinDiagram.of (𝟙 _)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.slideLEq c)
    rw [Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of,
      Presentation.lin_of, Presentation.diag_id] at H
    show ksL _ (LinDiagram.of (D0 c c ≫ X2 c c) - LinDiagram.of (X2 c c ≫ D1 c c) -
      LinDiagram.of (𝟙 _)) = 0
    have h1 : ksL (KLR.klQ2 k C) (LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c]))) =
        𝟙 ((KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob [c, c])) := ksL_one _
    have s1 : ksgn (Diagram.layers (D0 c c ≫ X2 c c)) = -1 := by simp [ksgn, ksg]
    have s2 : ksgn (Diagram.layers (X2 c c ≫ D1 c c)) = -1 := by simp [ksgn, ksg]
    rw [ksL_sub, ksL_sub, ksL_of, ksL_of, h1, s1, s2,
      show ksD (D0 c c ≫ X2 c c) = D1 c c ≫ X2 c c from Diagram.ext rfl,
      show ksD (X2 c c ≫ D1 c c) = X2 c c ≫ D0 c c from Diagram.ext rfl, ← H]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    have key : ∀ x y z : (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob [c, c]) ⟶
        (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob [c, c]),
        -x - -y - z = y - x - z := fun x y z => by abel
    exact key _ _ _
  | slideRNe c d h =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (X2 d c ≫ D0 c d) -
        LinDiagram.of (D1 d c ≫ X2 d c)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.slideLNe d c (Ne.symm h))
    rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of] at H
    show ksL _ (LinDiagram.of (D0 c d ≫ X2 c d) - LinDiagram.of (X2 c d ≫ D1 d c)) = 0
    rw [ksL_sub, ksL_of, ksL_of,
      show ksD (D0 c d ≫ X2 c d) = D1 d c ≫ X2 d c from Diagram.ext rfl,
      show ksD (X2 c d ≫ D1 d c) = X2 d c ≫ D0 c d from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, if_neg h, mul_one,
      one_mul, Int.cast_one, one_smul]
    rw [← neg_eq_zero, neg_sub]
    exact H
  | braid c d e h =>
    have h' : ¬ (e = c ∧ e ≠ d) := fun ⟨h₁, h₂⟩ => h ⟨h₁.symm, h₁ ▸ h₂⟩
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (braidL e d c) -
        LinDiagram.of (braidR e d c)) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.braid e d c h')
    rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of] at H
    show ksL _ (LinDiagram.of (braidL c d e) - LinDiagram.of (braidR c d e)) = 0
    rw [ksL_sub, ksL_of, ksL_of,
      show ksD (braidL c d e) = braidR e d c from Diagram.ext rfl,
      show ksD (braidR c d e) = braidL e d c from Diagram.ext rfl]
    have hs : ksgn (Diagram.layers (braidR c d e)) = ksgn (Diagram.layers (braidL c d e)) := by
      simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.prod_cons, List.prod_nil]
      ring
    rw [hs, ← smul_sub, ← neg_sub, smul_neg, H, smul_zero, neg_zero]
  | braidQ c d h =>
    have H : (KLR.Diagram.pres k (KLR.klQ2 k C)).lin (LinDiagram.of (braidL c d c) -
        LinDiagram.of (braidR c d c) -
        lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (KLR.klQ2 k C c d))) = 0 :=
      (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_rel_self (.braidQ c d h)
    rw [Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of,
      ← KLR.Diagram.linAlg_apply, lpoly, AlgHom.map_ncEval] at H
    show ksL _ (LinDiagram.of (braidL c d c) - LinDiagram.of (braidR c d c) -
      lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (KLR.klQ2 k C c d))) = 0
    rw [ksL_sub, ksL_sub, ksL_of, ksL_of, ksL_lpoly,
      show ksD (braidL c d c) = braidR c d c from Diagram.ext rfl,
      show ksD (braidR c d c) = braidL c d c from Diagram.ext rfl]
    have hs₁ : ksgn (Diagram.layers (braidL c d c)) = -1 := by
      simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, if_neg h,
        if_neg (Ne.symm h), if_pos rfl]
      norm_num
    have hs₂ : ksgn (Diagram.layers (braidR c d c)) = -1 := by
      simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, if_neg h,
        if_neg (Ne.symm h), if_pos rfl]
      norm_num
    have e : (fun a => ksL (KLR.klQ2 k C)
        (LinDiagram.of ((![E0 c d c, E1 c d c, E2 c d c] : Fin 3 → _) a))) =
        fun a => (KLR.Diagram.pres k (KLR.klQ2 k C)).diag
          ((![E0 c d c, E1 c d c, E2 c d c] : Fin 3 → _) (![2, 1, 0] a)) := by
      funext a
      fin_cases a
      · show ksL _ (LinDiagram.of (E0 c d c)) = (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (E2 c d c)
        rw [ksL_of, show ksD (E0 c d c) = E2 c d c from Diagram.ext rfl]
        simp [ksgn, ksg]
      · show ksL _ (LinDiagram.of (E1 c d c)) = (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (E1 c d c)
        rw [ksL_of, show ksD (E1 c d c) = E1 c d c from Diagram.ext rfl]
        simp [ksgn, ksg]
      · show ksL _ (LinDiagram.of (E2 c d c)) = (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (E0 c d c)
        rw [ksL_of, show ksD (E2 c d c) = E0 c d c from Diagram.ext rfl]
        simp [ksgn, ksg]
    rw [hs₁, hs₂, e, ncEval_rename_of_commute _
      (KPsi.commute_diag_dots3 (KLR.klQ2 k C) c d), KLR.qbar_rename_rev]
    simp only [KLR.Diagram.linAlg_apply, Presentation.lin_of] at H
    rw [← H]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    congr 1
    abel

end KSig


open KSig

/-! ## The upward KLR relations in `U` -/

section Upward

variable [DecidableEq I]

omit [DecidableEq I] in
theorem sig_shape_upShape (g : KLR.Diagram.Gen I) : Sig.shape (upShape g) = upShape (kgen g) := by
  cases g <;> rfl

theorem sgnG_upLay (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    sgnG (upLay RD μ L).gen = ksg L.gen := by
  obtain ⟨_, l, g, r⟩ := L
  cases g <;> rfl

omit [DecidableEq I] in
theorem obj_ups (μ : X) (a : Obj (KLR.Diagram.sig I)) :
    obj RD (ob RD μ (ups a.word)) = ob RD (-wt RD μ (ups a.word)) (ups (kobj a).word) := by
  rw [trO μ _ _ rfl]
  simp [kobj, ups, List.map_reverse]

theorem sigL_upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (hab : wt RD μ (ups b.word) = wt RD μ (ups a.word)) :
    sigL RD k (upLin RD k μ f) =
      TR RD k (obj_ups μ a) (by rw [obj_ups μ b, hab]; rfl)
        ((upFunctor RD k (-wt RD μ (ups a.word))).map (ksL (KLR.klQ2 k C) f)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [upLin, Finsupp.mapDomain_zero, sigL_zero,
      show ksL (KLR.klQ2 k C) (0 : (a ⟶ b) →₀ k) = 0 from Functor.map_zero _ _ _,
      Functor.map_zero, map_zero]
  | add f g hf hg =>
    rw [upLin, Finsupp.mapDomain_add, ← upLin, ← upLin, sigL_add, hf, hg]
    rw [show ksL (KLR.klQ2 k C) (f + g : (a ⟶ b) →₀ k) = ksL (KLR.klQ2 k C) f +
      ksL (KLR.klQ2 k C) g from Functor.map_add _, Functor.map_add, map_add]
  | single d r =>
    rw [upLin, Finsupp.mapDomain_single, sigL_single', layers_upDiag,
      show ksL (KLR.klQ2 k C) (Finsupp.single d r : (a ⟶ b) →₀ k) =
        r • ((ksgn (Diagram.layers d) : ℤ) : k) •
          (KLR.Diagram.pres k (KLR.klQ2 k C)).diag (ksD d) from freeLift_map_single _ d r,
      Functor.map_smul, Functor.map_smul, upFunctor_diag, map_smul, map_smul]
    have hs : Sig.sgn ((Diagram.layers d).map (upLay RD μ)) = ksgn (Diagram.layers d) := by
      simp only [Sig.sgn, ksgn, List.map_map, Function.comp_def, sgnG_upLay]
    rw [hs, TR_diag]
    congr 2
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [layers_reflD, layers_upDiag, Diagram.layers_cast, ksD, Diagram.layers_mk,
      List.map_map]
    refine List.map_congr_left fun L hL => ?_
    obtain ⟨_, l, g, rr⟩ := L
    simp only [Function.comp_apply, upLay, klay, rlay_lay, sig_shape_upShape, upShape_dom]
    have hw := (chain_wsum RD (Diagram.chain d)).2 _ hL
    simp only [KLR.Diagram.Layer.dom_word'] at hw
    congr 1
    · rw [← ups_append, ← ups_append, wt_ups, wt_ups, hw]
      rfl
    · simp [ups, List.map_reverse]
    · simp [ups, List.map_reverse]

theorem sigL_klr (μ : X) (r : KLR.Diagram.Rel I) :
    sigL RD k (relation k (.klr μ r : Rel RD)) = 0 := by
  rw [relation, sigL_upLin μ _ (by rw [wt_ups, wt_ups, wsum_relation_cod]), ksL_relation,
    Functor.map_zero, map_zero]

end Upward


/-! ## The zigzag relations and the interchange law -/

section Zigzag

variable [DecidableEq I]

omit [DecidableEq I] in
theorem col_eq_dual (c : Col I X) :
    col (RD := RD) c = (inv RD).dual ⟨c.l.dual, -c.r⟩ := by
  rw [inv_dual]
  refine Col.ext (show c.l = c.l.dual.dual by rw [Letter.dual_dual]) ?_
  show -(sh RD c.l + c.r) = sh RD c.l.dual + -c.r
  rw [sh_dual]; abel

omit [DecidableEq I] in
theorem col_dual_eq (c : Col I X) :
    col (RD := RD) ((inv RD).dual c) = ⟨c.l.dual, -c.r⟩ := by
  rw [inv_dual]
  refine Col.ext rfl ?_
  show -(sh RD c.l.dual + (sh RD c.l + c.r)) = -c.r
  rw [sh_dual_add_sh_add]

omit [DecidableEq I] in
theorem region_dual (c : Col I X) : -(sh RD c.l + c.r) = sh RD c.l.dual + -c.r := by
  rw [sh_dual]; abel

/-- The reflection of the left zigzag of `c` is the right zigzag of `⟨c.l*, -c.r⟩`. -/
theorem sigL_zigL (c : Col I X) :
    sigL RD k (LinDiagram.of (Pivotal.zigL (inv RD).toColourDuality c)) = 𝟙 _ := by
  rw [sigL_of, show sgn (Diagram.layers (Pivotal.zigL (inv RD).toColourDuality c)) = 1 from rfl,
    Int.cast_one, one_smul]
  have hw : word RD [c] = [(inv RD).dual ⟨c.l.dual, -c.r⟩] := by
    show [col c] = _; rw [col_eq_dual]
  refine (pres RD k).diag_eq_id_of_layers _
    (Pivotal.zigR (inv RD).toColourDuality ⟨c.l.dual, -c.r⟩) (Obj.ext rfl hw) ?_
    ((zigzags RD k) _).2
  simp only [layers_reflD, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Layer.wl, Layer.wr, List.append_nil]
  refine List.cons_eq_cons.2 ⟨Layer.ext rfl hw rfl rfl,
    List.cons_eq_cons.2 ⟨Layer.ext rfl rfl rfl hw, rfl⟩⟩

/-- The reflection of the right zigzag of `c` is the left zigzag of `⟨c.l*, -c.r⟩`. -/
theorem sigL_zigR (c : Col I X) :
    sigL RD k (LinDiagram.of (Pivotal.zigR (inv RD).toColourDuality c)) = 𝟙 _ := by
  rw [sigL_of, show sgn (Diagram.layers (Pivotal.zigR (inv RD).toColourDuality c)) = 1 from rfl,
    Int.cast_one, one_smul]
  have hw : word RD [(inv RD).dual c] = [⟨c.l.dual, -c.r⟩] := by
    show [col ((inv RD).dual c)] = _; rw [col_dual_eq]
  refine (pres RD k).diag_eq_id_of_layers _
    (Pivotal.zigL (inv RD).toColourDuality ⟨c.l.dual, -c.r⟩) (Obj.ext (region_dual c) hw) ?_
    ((zigzags RD k) _).1
  simp only [layers_reflD, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Layer.wl, Layer.wr, List.append_nil]
  refine List.cons_eq_cons.2 ⟨Layer.ext (region_dual c) rfl rfl hw,
    List.cons_eq_cons.2 ⟨Layer.ext (region_dual c) hw rfl rfl, rfl⟩⟩

/-- The reflection of the interchange law is the interchange law (with the generators
exchanged). -/
theorem sigL_interchange (x : InterchangeData (psig RD)) (hx : x.Valid) :
    sigL RD k (InterchangeData.rel k hx) = 0 := by
  obtain ⟨start, g, mid, h⟩ := x
  have g₁ : start = (psig RD).left g := hx.gh₁.left_end
  have g₂ : (psig RD).endR ((psig RD).left g) ((psig RD).dom g) = (psig RD).right g :=
    hx.gh₁.dom_end
  have g₃ : (psig RD).endR ((psig RD).left g) ((psig RD).cod g) = (psig RD).right g :=
    hx.gh₁.cod_end
  have h₁ : (psig RD).endR start ((psig RD).cod g ++ mid) = (psig RD).left h := hx.gh₂.left_end
  have h₂ : (psig RD).endR ((psig RD).left h) ((psig RD).dom h) = (psig RD).right h :=
    hx.gh₂.dom_end
  have h₃ : (psig RD).endR ((psig RD).left h) ((psig RD).cod h) = (psig RD).right h :=
    hx.gh₂.cod_end
  have eg : (psig RD).endR ((psig RD).right g) mid = (psig RD).left h := by
    rw [Signature.endR_append, g₁, g₃] at h₁; exact h₁
  have e₁ : eR (RD := RD) ((psig RD).right g) (mid ++ (psig RD).dom h) = rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, eg]; exact h₂
  have e₂ : eR (RD := RD) ((psig RD).right g) (mid ++ (psig RD).cod h) = rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, eg]; exact h₃
  have e₃ : eR (RD := RD) start ((psig RD).dom g ++ mid ++ (psig RD).dom h) = rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, Signature.endR_append, g₁, g₂, eg]; exact h₂
  have e₄ : eR (RD := RD) start ((psig RD).cod g ++ mid ++ (psig RD).cod h) =
      rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, Signature.endR_append, g₁, g₃, eg]; exact h₃
  let x : InterchangeData (psig RD) := ⟨start, g, mid, h⟩
  let x' : InterchangeData (psig RD) := ⟨-rR (RD := RD) h, gen h, word RD mid, gen g⟩
  have f₁ : x'.gh₁ = rlay x.hg₁ := by
    simp [x, x', InterchangeData.gh₁, InterchangeData.hg₁, rlay, gen_dom, word_append, word_nil']
  have f₂ : x'.gh₂ = rlay x.hg₂ := by
    simp only [x, x', InterchangeData.gh₂, InterchangeData.hg₂, rlay, gen_cod, word_append]
    rw [e₂]; rfl
  have f₃ : x'.hg₁ = rlay x.gh₁ := by
    simp only [x, x', InterchangeData.hg₁, InterchangeData.gh₁, rlay, gen_dom, word_append]
    rw [e₁]; rfl
  have f₄ : x'.hg₂ = rlay x.gh₂ := by
    simp [x, x', InterchangeData.hg₂, InterchangeData.gh₂, rlay, gen_cod, word_append, word_nil']
  have hx' : x'.Valid := ⟨f₁ ▸ rlay_valid hx.hg₁, f₂ ▸ rlay_valid hx.hg₂, f₃ ▸ rlay_valid hx.gh₁,
    f₄ ▸ rlay_valid hx.gh₂⟩
  have hw : x'.dom.WhiskerOK (Obj.nil x'.start) [] := ⟨trivial, rfl, trivial⟩
  have ha : x'.dom.whisker (Obj.nil x'.start) [] = obj RD x.dom :=
    Obj.ext (by
        show -rR (RD := RD) h =
          -eR (RD := RD) start ((psig RD).dom g ++ mid ++ (psig RD).dom h)
        rw [e₃])
      (by simp [x', x, InterchangeData.dom, Obj.whisker, Obj.nil, gen_dom, word_append])
  have hb : x'.cod.whisker (Obj.nil x'.start) [] = obj RD x.cod :=
    Obj.ext (by
        show -rR (RD := RD) h =
          -eR (RD := RD) start ((psig RD).cod g ++ mid ++ (psig RD).cod h)
        rw [e₄])
      (by simp [x', x, InterchangeData.cod, Obj.whisker, Obj.nil, gen_cod, word_append])
  have key := (pres RD k).diag_interchange x' hx' (Obj.nil x'.start) [] hw ha hb
  have hsg : ∀ y : InterchangeData (psig RD), ((y.sign : ℤ) : k) = 1 := by
    intro y; simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]
  rw [hsg, one_smul] at key
  have hs : sgn (Diagram.layers (InterchangeData.hgDiagram hx)) =
      sgn (Diagram.layers (InterchangeData.ghDiagram hx)) := by
    simp only [Sig.sgn, InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, InterchangeData.gh₁,
      InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂]
    ring
  have d₁ : (pres RD k).diag (reflD (InterchangeData.ghDiagram hx)) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker (InterchangeData.hgDiagram hx')
        (Obj.nil x'.start) [] hw) ha hb) := by
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [layers_reflD, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons,
      List.map_nil]
    rw [show (⟨start, g, mid, h⟩ : InterchangeData (psig RD)) = x from rfl, ← f₃, ← f₄]
    simp [Layer.whisker, Obj.nil]
    exact ⟨rfl, rfl⟩
  have d₂ : (pres RD k).diag (reflD (InterchangeData.hgDiagram hx)) =
      (pres RD k).diag (Diagram.cast (Diagram.whisker (InterchangeData.ghDiagram hx')
        (Obj.nil x'.start) [] hw) ha hb) := by
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [layers_reflD, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons,
      List.map_nil]
    rw [show (⟨start, g, mid, h⟩ : InterchangeData (psig RD)) = x from rfl, ← f₁, ← f₂]
    simp [Layer.whisker, Obj.nil]
    exact ⟨rfl, rfl⟩
  rw [InterchangeData.rel, sigL_sub, sigL_smul, sigL_of, sigL_of, hsg, one_smul, hs, d₁, d₂, key,
    sub_self]

end Zigzag


/-! ## The 2-functor `σ̃ : U → U^op` -/

section Functor

variable [DecidableEq I]

/-- **Every relation of Definition 3.1, reflected across the `y`-axis with `λ ↦ -λ` and the sign
`-1` on crossings of equally labelled strands, holds in `U`.** -/
theorem sigL_relation (r : Rel RD) : sigL RD k (relation k r) = 0 := by
  cases r with
  | cycDotR i μ => exact sigL_cycDotR i μ
  | cycDotL i μ => exact sigL_cycDotL i μ
  | cwNeg i lam α h => exact sigL_cwNeg i lam α h
  | ccwNeg i lam α h => exact sigL_ccwNeg i lam α h
  | cwOne i lam h => exact sigL_cwOne i lam h
  | ccwOne i lam h => exact sigL_ccwOne i lam h
  | curlR i lam => exact sigL_curlR i lam
  | curlL i μ => exact sigL_curlL i μ
  | decompEF i lam => exact sigL_decompEF i lam
  | decompFE i lam => exact sigL_decompFE i lam
  | cycCrossR j i μ => exact sigL_cycCrossR j i μ
  | cycCrossL j i μ => exact sigL_cycCrossL j i μ
  | downupEF i j h μ => exact sigL_downupEF i j h μ
  | downupFE i j h μ => exact sigL_downupFE i j h μ
  | klr μ r => exact sigL_klr μ r

theorem sigL_rel (r : (pres RD k).Rel) : sigL RD k ((pres RD k).rel r) = 0 := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · show sigL RD k (LinDiagram.of (Pivotal.zigL _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [sigL_sub, sigL_zigL, sub_eq_zero]
    exact (sigL_id _).symm
  · show sigL RD k (LinDiagram.of (Pivotal.zigR _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [sigL_sub, sigL_zigR, sub_eq_zero]
    exact (sigL_id _).symm
  · exact sigL_relation r

omit [DecidableEq I] in
theorem pres_dom_wf (r : (pres RD k).Rel) : ((pres RD k).dom r).WF := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · exact Pivotal.colourObj_wf _ c
  · exact Pivotal.dualObj_wf _ c
  · cases r <;> exact ob_wf RD _ _

variable (RD k)

/-- The signed reflection on the free 2-category respects all the relations of `U`. -/
theorem sigFree_respects : (pres RD k).Respects (sigFree RD k) where
  rel r u v hw := sigL_whisker_eq_zero _ (pres_dom_wf r) (sigL_rel r) hw
  interchange x hx u v hw := by
    have hwf : x.dom.WF := by
      have := hx.gh₁.wf_dom
      simpa [Obj.WF, Layer.dom, InterchangeData.gh₁, InterchangeData.dom, List.append_assoc]
        using this
    exact sigL_whisker_eq_zero _ hwf (sigL_interchange x hx) hw

/-- **The symmetry `σ̃ : U → U^op` of KL III §3.3.2**: reflection of diagrams across the
`y`-axis, `λ ↦ -λ`, and the sign `-1` on every crossing of two strands with the same label. It
reverses the order of 1-morphisms (`Sig.obj`) and preserves the order of composition of
2-morphisms. -/
def sigU : (pres RD k).Presented ⥤ (pres RD k).Presented :=
  (pres RD k).lift (sigFree_respects RD k)

instance : (sigU RD k).Additive := by unfold sigU; infer_instance

instance : (sigU RD k).Linear k := by unfold sigU; infer_instance

variable {RD k}

@[simp] theorem sigU_obj (a : Obj (psig RD)) :
    (sigU RD k).obj ((pres RD k).obj a) = (pres RD k).obj (obj RD a) := rfl

theorem sigU_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (sigU RD k).map ((pres RD k).lin f) = sigL RD k f := by
  unfold sigU; rw [Presentation.lift_lin]

/-- `σ̃` on a diagram: the reflected diagram, with the sign `(-1)^{#ii-crossings}`. -/
theorem sigU_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (sigU RD k).map ((pres RD k).diag d) =
      ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k).diag (reflD d) := by
  unfold sigU; rw [Presentation.lift_diag]; rfl

/-- `σ̃` on normal-form diagrams: the layers `(u, g, v)` become `(v^rev, Sig.shape g, u^rev)`,
the rightmost region becomes `ν = -(μ + s_X)`, and the diagram is multiplied by the sign
`(-1)^{#ii-crossings}`; the reflected objects are identified with normal forms by `Sig.trO`. -/
theorem sigU_dg (μ ν : X) {s t : List (Letter I)} (s' t' : List (Letter I))
    (ls : List (LayerData I)) (h : SChain s ls t) (hν : ν = -wt RD μ s) (hs : s.reverse = s')
    (ht : t.reverse = t') :
    (sigU RD k).map (dg RD k μ s t ls) =
      ((sgnS ls : ℤ) : k) • TR RD k (hs ▸ trO μ ν s hν)
        (ht ▸ trO μ ν t (hν.trans (by rw [SChain.wt_eq RD μ h])))
        (dg RD k ν s' t' (sls ls)) := by
  rw [dg_of h, show (pres RD k).diag (mkD RD μ ls h) =
    (pres RD k).lin (LinDiagram.of (mkD RD μ ls h)) from rfl, sigU_lin]
  exact sigL_of_mkD μ ν s' t' ls h hν hs ht

/-- **`σ̃` reverses horizontal composition**: whiskering by `u` on the left and `v` on the right
becomes whiskering by the reflection of `v` on the left and the reflection of `u` on the right
(up to the canonical identification of objects). -/
theorem sigU_whisk {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b)
    (ha : a.WF) (hs : b.start = a.start) (he : b.endR = a.endR) {u : Obj (psig RD)}
    {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    (sigU RD k).map ((pres RD k).whisk f u v) =
      eqToHom (congrArg (pres RD k).obj (obj_whisker hw.2.1).symm) ≫
        (pres RD k).whisk ((sigU RD k).map f) (sigW a v) (word RD u.word) ≫
          eqToHom (congrArg (pres RD k).obj (obj_whisker_cod hs he hw.2.1)) := by
  obtain ⟨g, rfl⟩ := (pres RD k).lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, sigU_lin, sigU_lin,
    sigL_whisker g ha hs he hw]

/-- **`σ̃` preserves degrees.** -/
theorem sigU_homDeg {a b : Obj (psig RD)} {f : (pres RD k).obj a ⟶ (pres RD k).obj b} {t : ℤ}
    (hf : f ∈ (pres RD k).homDeg (deg RD) a b t) :
    (sigU RD k).map f ∈ (pres RD k).homDeg (deg RD) (obj RD a) (obj RD b) t := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  clear hf
  rw [sigU_lin]
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [sigL_single']
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Presentation.diag_mem_homDeg' ((degree_reflD d).trans hd)
  | zero => rw [sigL_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [sigL_add' x y]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [sigL_smul]; exact Submodule.smul_mem _ r hx

/-- **`σ̃` sends the clockwise bubble with label `m` in the region `λ` to the counterclockwise
bubble with label `m` in the region `-λ`** (real and fake bubbles). -/
theorem sigU_cwU (lam : X) (i : I) (m : ℤ) :
    (sigU RD k).map (cwU RD k lam i m) = ccwU RD k (-lam) i m := by
  rw [cwU, sigU_lin, sigL_cwL]

/-- **`σ̃` sends the counterclockwise bubble with label `m` in the region `λ` to the clockwise
bubble with label `m` in the region `-λ`** (real and fake bubbles). -/
theorem sigU_ccwU (lam : X) (i : I) (m : ℤ) :
    (sigU RD k).map (ccwU RD k lam i m) = cwU RD k (-lam) i m := by
  rw [ccwU, sigU_lin, sigL_ccwL]

end Functor

end Categorification.KL3.Diagram
