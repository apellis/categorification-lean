/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.ChordU

/-!
# The canonical span, filtered by the number of crossings

Khovanov–Lauda's spanning set for `HOM_U(1_μ, E_v 1_μ)` (KL III Prop. 3.11, in the form
`mem_canonSpan`) is refined here by the number of crossings: a diagram with at most `c`
crossings lies in the span of the canonical diagrams with at most `c` crossings
(`mem_canonSpanLe`). As a consequence, a dot on a canonical diagram may be moved to the left end
of its arc modulo canonical diagrams with strictly fewer crossings
(`canon_dot_sub_lEnd_mem_canonSpanLe`). These are the inputs of the triangularity argument in the
proof of Webster arXiv:1309.3796v2, Lemma 3.29, where dots with integer exponents are moved along
arcs in the localization `U′`.

## Main results

* `canonSpanLe`: the span of the canonical diagrams with at most `c` crossings.
* `mem_canonSpanLe`: `dg L ∈ canonSpanLe c` when `L` has at most `c` crossings.
* `lo_le_canonSpanLe`: `Lo (c + 1) ≤ canonSpanLe c`.
* `canon_dot_sub_lEnd_mem_canonSpanLe`: moving one dot to the left end of its arc changes a
  canonical diagram with `n + 1` crossings by an element of `canonSpanLe n`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open StringDiagrams.Chord (Move Step Rw Fits lstep canon run Same Valid Lettered)

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

section Filtered

variable [DecidableEq I]

variable (RD k) in
/-- The span of the canonical diagrams with at most `c` crossings, with dots at the left ends of
their arcs, followed by elements of the image of `Π_μ` on the far right. -/
def canonSpanLe (μ : X) (v : List (Letter I)) (c : ℕ) :
    Submodule k ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v)) :=
  Submodule.span k {f | ∃ (s : List (ℕ × Letter I)) (is : List ℕ)
    (β : End ((pres RD k).obj (ob RD μ []))), Valid s ∧ Lettered Letter.dual s ∧
      s.map Prod.snd = v ∧ (∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) ∧
      IsBub RD k μ β ∧ ncr (canon s) ≤ c ∧
      f = dg RD k μ [] v (chL [] (canon s) ++ dotsL v is) ≫ bubAt RD k μ v β}

omit [DecidableEq I] in
theorem canonSpanLe_mono (μ : X) (v : List (Letter I)) {c d : ℕ} (h : c ≤ d) :
    canonSpanLe RD k μ v c ≤ canonSpanLe RD k μ v d := by
  refine Submodule.span_mono ?_
  rintro _ ⟨s, is, β, h1, h2, h3, h4, h5, h6, rfl⟩
  exact ⟨s, is, β, h1, h2, h3, h4, h5, h6.trans h, rfl⟩

omit [DecidableEq I] in
theorem canonSpanLe_le_canonSpan (μ : X) (v : List (Letter I)) (c : ℕ) :
    canonSpanLe RD k μ v c ≤ CanonSpan RD k μ v := by
  refine Submodule.span_mono ?_
  rintro _ ⟨s, is, β, h1, h2, h3, h4, h5, -, rfl⟩
  exact ⟨s, is, β, h1, h2, h3, h4, h5, rfl⟩

/-- **A move diagram with bubbles lies in the filtered canonical span modulo lower terms.** -/
theorem mvSp_gen_mem_le (μ : X) {v : List (Letter I)} {ms : List (Mv I)} (hch : MvChain [] ms v)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    dg RD k μ [] v (mvLay ms) ≫ bubAt RD k μ v β ∈
      canonSpanLe RD k μ v (ccnt (mvLay ms)) ⊔ Lo RD k μ [] v (ccnt (mvLay ms)) := by
  obtain ⟨D, is, hD, hlet, hn, his, hdiff⟩ := mv_to_chord (RD := RD) (k := k) μ ms hch
  have hsD : SChain [] (chL [] D) v := by
    have := sChain_chL (l := []) hD; rwa [hlet] at this
  have e1 : dg RD k μ [] v (mvLay ms) ≫ bubAt RD k μ v β =
      (dg RD k μ [] v (mvLay ms) - dg RD k μ [] v (chL [] D ++ dotsL v is)) ≫ bubAt RD k μ v β +
        dg RD k μ [] v (chL [] D) ≫ dg RD k μ v v (dotsL v is) ≫ bubAt RD k μ v β := by
    rw [Preadditive.sub_comp, dg_append_of_left hsD, Category.assoc, sub_add_cancel]
  rw [e1]
  refine Submodule.add_mem _ (Submodule.mem_sup_right (lo_comp_bubAt_mem_of hdiff hβ)) ?_
  rcases chL_normal_form (RD := RD) (k := k) hD μ v with h | ⟨hfc, hnc, hdc⟩
  · refine Submodule.mem_sup_right ?_
    rw [← Category.assoc]
    have := lo_comp_bubAt_mem_of (lo_comp_dg (r := v) h (dotsL v is)) hβ
    rwa [ccnt_dotsL, add_zero, hn] at this
  · obtain ⟨s, hs⟩ : ∃ s, s = run Letter.dual D := ⟨_, rfl⟩
    rw [← hs] at hfc hnc hdc
    have hvs : Valid s := hs ▸ (Chord.inv_run hD).1
    have hls : Lettered Letter.dual s := hs ▸ Chord.lettered_run dual_involutive hD
    have hsv : s.map Prod.snd = v := by rw [hs, Chord.snd_run, ← hlet]
    have hsc : SChain [] (chL [] (canon s)) v := by
      have := sChain_chL (l := []) hfc
      rwa [(canon_letters hvs hls).2, hsv] at this
    have e2 : dg RD k μ [] v (chL [] D) ≫ dg RD k μ v v (dotsL v is) ≫ bubAt RD k μ v β =
        ((dg RD k μ [] v (chL [] D) - dg RD k μ [] v (chL [] (canon s))) ≫
          dg RD k μ v v (dotsL v is)) ≫ bubAt RD k μ v β +
        ((dg RD k μ [] v (chL [] (canon s) ++ dotsL v is) -
          dg RD k μ [] v (chL [] (canon s) ++ dotsL v (is.map (lEnd s)))) ≫ bubAt RD k μ v β +
        dg RD k μ [] v (chL [] (canon s) ++ dotsL v (is.map (lEnd s))) ≫ bubAt RD k μ v β) := by
      rw [dg_append_of_left hsc]
      simp only [Preadditive.sub_comp, Category.assoc]
      abel
    rw [e2]
    refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.add_mem _
      (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left (Submodule.subset_span ?_)))
    · have := lo_comp_bubAt_mem_of (lo_comp_dg (r := v) hdc (dotsL v is)) hβ
      rwa [ccnt_dotsL, add_zero, hn] at this
    · have his' : ∀ i ∈ is, i < s.length := by rw [← hsv] at his; simpa using his
      have := dots_left (RD := RD) (k := k) μ hvs hls is his' [] v
      rw [hsv] at this
      simp only [List.append_nil, ccnt_nil, add_zero, hnc, hn] at this
      exact lo_comp_bubAt_mem_of this hβ
    · refine ⟨s, is.map (lEnd s), β, hvs, hls, hsv, fun i hi => ?_, hβ, by omega, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      have hj' : j < s.length := by rw [← hsv] at his; simpa using his j hj
      exact ⟨lEnd_lt hj', lEnd_isLeft hvs j⟩

variable {k : Type w} [Field k]

/-- **Filtered canonical spanning**: a diagram with at most `c` crossings is a linear combination
of canonical diagrams with at most `c` crossings, with dots at the left ends of their arcs,
followed by elements of the image of `Π_μ` (KL III Prop. 3.11, with the crossing filtration). -/
theorem mem_canonSpanLe (μ : X) (v : List (Letter I)) :
    ∀ c (L : List (LayerData I)), ccnt L ≤ c → dg RD k μ [] v L ∈ canonSpanLe RD k μ v c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro L hL
  have hlo : ∀ n ≤ c, Lo RD k μ [] v n ≤ canonSpanLe RD k μ v c := by
    intro n hn
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L', hL', rfl⟩
    exact canonSpanLe_mono μ v (by omega) (ihc (ccnt L') (by omega) L' le_rfl)
  have hcap := capElim (RD := RD) (k := k) (μ := μ) (w₀ := []) c v L hL
  rw [CapTarget, thruShort_nil, sup_bot_eq, MvSp] at hcap
  generalize dg RD k μ [] v L = x at hcap
  induction hcap using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hx
    have h := mvSp_gen_mem_le (RD := RD) (k := k) μ hch hβ
    exact (sup_le (canonSpanLe_mono μ v hcc) (hlo _ hcc)) h
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ r hx

/-- Lower terms with fewer than `c + 1` crossings lie in the filtered canonical span. -/
theorem lo_le_canonSpanLe (μ : X) (v : List (Letter I)) (c : ℕ) :
    Lo RD k μ [] v (c + 1) ≤ canonSpanLe RD k μ v c := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨L, hL, rfl⟩
  exact mem_canonSpanLe μ v c L (by omega)

/-- **Triangularity of dots on canonical diagrams**: moving the dots at positions `is` of a
canonical diagram with `n + 1` crossings to the left ends of their arcs changes it by an element of
the filtered canonical span of level `n`. -/
theorem canon_dot_sub_lEnd_mem_canonSpanLe (μ : X) {s : List (ℕ × Letter I)} (hv : Valid s)
    (hl : Lettered Letter.dual s) (is : List ℕ) (his : ∀ i ∈ is, i < s.length) {n : ℕ}
    (hn : ncr (canon s) = n + 1) :
    dg RD k μ [] (s.map Prod.snd) (chL [] (canon s) ++ dotsL (s.map Prod.snd) is) -
        dg RD k μ [] (s.map Prod.snd)
          (chL [] (canon s) ++ dotsL (s.map Prod.snd) (is.map (lEnd s))) ∈
      canonSpanLe RD k μ (s.map Prod.snd) n := by
  have := dots_left (RD := RD) (k := k) μ hv hl is his [] (s.map Prod.snd)
  simp only [List.append_nil, ccnt_nil, add_zero, hn] at this
  exact lo_le_canonSpanLe μ _ n this

end Filtered

end Categorification.KL3.Diagram
