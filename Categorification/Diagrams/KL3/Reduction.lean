/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningPhi

/-!
# Reductions: closed diagrams, single strands and upward hom spaces

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1
(Proposition 3.6, label `prop_bubbles_same_orient`) and §3.2.2 (Lemma 3.9, label
`lem_surjective`; Proposition 3.10). The TeX locators refer to
`sources/klr/kl3/0807.3250v1.txt`, lines 1690–1790.

KL III prove Proposition 3.6 ("`Π_λ → HOM_U(1_λ, 1_λ)` is surjective") and Lemma 3.9 ("`ϕ_{i,j,λ}`
is surjective") by the same reduction of crossings, following A. Lauda, *A categorification of
quantum sl(2)*, arXiv:0803.3652v3, §8 (TeX `src/Udot.tex`, `\section{Size of 2-category}`,
proof of `prop_closed_bubble`). This file shows that both statements follow from a single
diagrammatic statement, and that Proposition 3.6 needs only its one-strand case:

* `UpSpanDiag RD k μ`: **KL III Lemma 3.9 in diagrammatic form** — every normal-form diagram of
  `U` between two upward sequences (rightmost region `μ`) is a linear combination of upward
  diagrams followed by bubble monomials on the far right (the span `upSpan` of
  `Categorification.Diagrams.KL3.SpanningPhi`).
* `EndUpSpan RD k μ i`: its one-strand case: every endomorphism of `E_i 1_μ` is a linear
  combination of dots on the strand times bubble monomials to its right (`slideSetR`).

## Closing a closed diagram along its lowest cup

Every nonempty closed normal-form diagram `D` begins with a cup. If it is the cup `1 → E_i F_i`,
then `D` is the right closure (`closeRight`, a clockwise loop) of an endomorphism of the upward
strand `E_i`: bend the downward leg of the cup up to the top with a second cup and straighten
with the zigzag relation (`dg_cupUp_eq_closeRight`). If it is the cup `1 → F_i E_i`, then `D` is
the left closure (`closeLeft`, a counterclockwise loop) of an endomorphism of `E_i`
(`dg_cupDn_eq_closeLeft`). The closure of dots times bubble monomials is a dotted bubble times
bubble monomials (`closeRight_bubLU`, `closeLeft_bubRU` of
`Categorification.Diagrams.KL3.Grassmannian`, with the bubble slides of
`Categorification.Diagrams.KL3.SpanningBasic` to move bubbles to the outside of the loop).

## Main results

* `prop36_of_endUpSpan`: **Proposition 3.6 follows from the one-strand case of Lemma 3.9**:
  if `EndUpSpan RD k μ i` holds for all `μ` and `i`, then `Prop36 RD k λ` holds for all `λ`
  (simply-laced Cartan data, as for the bubble slides).
* `endUpSpan_of_upSpanDiag`, `prop310_of_upSpanDiag`, `prop36_of_upSpanDiag`: `UpSpanDiag`
  implies its one-strand case, Proposition 3.10 (`Prop310`, for every `ν`) and Proposition 3.6.
* `endUpSpan_of_prop310`, `prop36_of_prop310`: **Proposition 3.10 for one-vertex `ν` implies
  Proposition 3.6**.

The remaining input, `UpSpanDiag` (equivalently KL III's reduction of crossings, cups and caps in
diagrams between upward sequences), is not proved here.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## The statements -/

/-- **KL III Lemma 3.9, diagrammatic form** (rightmost region `μ`): every normal-form diagram of
`U` from an upward sequence `s` to an upward sequence `t` is a linear combination of upward
diagrams followed by bubble monomials on the far right. -/
def UpSpanDiag (μ : X) : Prop :=
  ∀ (s t : List (Letter I)) (ls : List (LayerData I)), Positive s → Positive t → SChain s ls t →
    dg RD k μ s t ls ∈ upSpan RD k μ s t

/-- The one-strand case of Lemma 3.9: every endomorphism of `E_i 1_μ` is a linear combination of
dots on the strand times bubble monomials to its right. -/
def EndUpSpan (μ : X) (i : I) : Prop :=
  ∀ f : End ((pres RD k).obj (ob RD μ [up i])), f ∈ slideSetR RD k μ (up i)

/-! ## Bending a closed diagram along its lowest cup -/

section Bend

variable (lam : X) (i : I)

/-- **A closed diagram beginning with the cup `1 → E_i F_i` is a right closure**: bending the
downward leg of the first cup up to the top (a second cup and the zigzag relation) exhibits it
as the clockwise closure of an endomorphism of `E_i`. -/
theorem dg_cupUp_eq_closeRight (rest : List (LayerData I)) (h : SChain [up i, dn i] rest []) :
    dg RD k lam [] [] (([], .cup (up i), []) :: rest) =
      closeRight RD k lam i (dg RD k (wt RD lam [dn i]) [up i] [up i]
        (([up i], .cup (dn i), []) :: rest.map (whL [] [up i]))) := by
  have hA : SChain [up i] (([up i], .cup (dn i), []) :: rest.map (whL [] [up i])) [up i] :=
    ⟨rfl, by simpa using h.whisk [] [up i]⟩
  have hA' := hA.whisk [] [dn i]
  simp only [List.nil_append, List.singleton_append] at hA'
  rw [closeRight_apply, plcL_dg]
  show _ = dg RD k lam [] [up i, dn i] _ ≫ dg RD k lam [up i, dn i] [up i, dn i] _ ≫
    dg RD k lam [up i, dn i] [] _
  rw [dg_comp hA' (by schain), dg_comp (by schain) (hA'.append (by schain))]
  -- move the final cap below `rest` (interchange law), then straighten the zigzag
  have e := dg_interchange (RD := RD) (k := k) (μ := lam) (S := []) (T := [])
    [([], .cup (up i), []), ([up i], .cup (dn i), [dn i])] [] h
    (B := [([], .cap (dn i), [])]) (t := [up i, dn i]) (t' := []) (by schain)
  wnf at e
  wnf
  rw [e]
  symm
  refine (dg_step RD k lam [([], .cup (up i), [])] rest [up i] []
    (dg_zigL' RD k (wt RD lam []) (dn i)) (by schain) h (by simp [whL]) rfl).trans ?_
  simp

/-- **A closed diagram beginning with the cup `1 → F_i E_i` is a left closure**: the
counterclockwise closure of an endomorphism of `E_i`. -/
theorem dg_cupDn_eq_closeLeft (rest : List (LayerData I)) (h : SChain [dn i, up i] rest []) :
    dg RD k lam [] [] (([], .cup (dn i), []) :: rest) =
      closeLeft RD k lam i (dg RD k lam [up i] [up i]
        (([], .cup (up i), [up i]) :: rest.map (whL [up i] []))) := by
  have hA : SChain [up i] (([], .cup (up i), [up i]) :: rest.map (whL [up i] [])) [up i] :=
    ⟨rfl, by simpa using h.whisk [up i] []⟩
  have hA' := hA.whisk [dn i] []
  simp only [List.append_nil, List.singleton_append] at hA'
  rw [closeLeft_apply, plcL_dg_nil]
  show _ = dg RD k lam [] [dn i, up i] _ ≫ dg RD k lam [dn i, up i] [dn i, up i] _ ≫
    dg RD k lam [dn i, up i] [] _
  rw [dg_comp hA' (by schain), dg_comp (by schain) (hA'.append (by schain))]
  -- move the final cap below `rest` (interchange law), then straighten the zigzag
  have e := dg_interchange (RD := RD) (k := k) (μ := lam) (S := []) (T := [])
    [([], .cup (dn i), []), ([dn i], .cup (up i), [up i])] []
    (A := [([], .cap (up i), [])]) (s := [dn i, up i]) (s' := []) (by schain) h
  wnf at e
  wnf
  rw [← e]
  symm
  refine (dg_step RD k lam [([], .cup (dn i), [])] rest [] [up i]
    (dg_zigR' RD k (wt RD lam [up i]) (up i)) (by schain) h (by simp [whL]) rfl).trans ?_
  simp

end Bend

/-! ## Closures of dots times bubble monomials -/

section Closures

variable {RD k}

/-- For an upward strand, dots times bubble monomials on the right are also dots times bubble
monomials on the left (bubble slides, KL III Propositions 3.3 and 3.4). -/
theorem slideSetR_le_slideSetL_up (hSL : SimplyLaced C) (μ : X) (j : I) :
    slideSetR RD k μ (up j) ≤ slideSetL RD k μ (up j) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, γ, hγ, rfl⟩
  have hd : dotsU RD k μ (up j) a ∈ slideSetL RD k μ (up j) := by
    have := mem_slideSetL (RD := RD) (k := k) (μ := μ) (l := up j) (a := a) (IsBub.id)
    rwa [bubLU_id, Category.comp_id] at this
  exact slideSetL_comp hd (bubRU_up_mem hSL μ j hγ)

variable (hSL : SimplyLaced C) (lam : X) (i : I)
include hSL

/-- The right closure of dots times bubble monomials is a bubble monomial times a dotted
clockwise bubble. -/
theorem isBub_closeRight {g : End ((pres RD k).obj (ob RD (wt RD lam [dn i]) [up i]))}
    (hg : g ∈ slideSetR RD k (wt RD lam [dn i]) (up i)) :
    IsBub RD k lam (closeRight RD k lam i g) := by
  have hg' := slideSetR_le_slideSetL_up hSL (wt RD lam [dn i]) i hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    rw [← bubLU_comm, closeRight_bubLU]
    exact IsBub.comp (IsBub.wtTransport _ hγ) (cwU_isBub _ _)
  | zero => rw [map_zero]; exact IsBub.zero
  | add x y _ _ hx hy => rw [map_add]; exact IsBub.add hx hy
  | smul r x _ hx => rw [map_smul]; exact IsBub.smul r hx

omit hSL in
/-- The left closure of dots times bubble monomials is a bubble monomial times a dotted
counterclockwise bubble. -/
theorem isBub_closeLeft {g : End ((pres RD k).obj (ob RD lam [up i]))}
    (hg : g ∈ slideSetR RD k lam (up i)) :
    IsBub RD k lam (closeLeft RD k lam i g) := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    rw [← bubRU_comm, closeLeft_bubRU]
    exact IsBub.comp hγ (ccwU_isBub _ _)
  | zero => rw [map_zero]; exact IsBub.zero
  | add x y _ _ hx hy => rw [map_add]; exact IsBub.add hx hy
  | smul r x _ hx => rw [map_smul]; exact IsBub.smul r hx

end Closures

/-! ## Proposition 3.6 from the one-strand case of Lemma 3.9 -/

theorem Shape.eq_cup_of_dom_nil {g : Shape I} (h : g.dom = []) : ∃ l, g = .cup l := by
  cases g with
  | cup l => exact ⟨l, rfl⟩
  | dot l => simp at h
  | cross ε a b => simp at h
  | cap l => simp at h

/-- **KL III Proposition 3.6 from the one-strand case of Lemma 3.9** (simply-laced Cartan data):
if every endomorphism of every upward strand `E_i 1_μ` is a linear combination of dots times
bubble monomials, then `Π_λ → END_U(1_λ)` is surjective for every `λ`. A closed diagram is the
closure of an endomorphism of an upward strand along its lowest cup (`dg_cupUp_eq_closeRight`,
`dg_cupDn_eq_closeLeft`), and closures of dots times bubble monomials are bubble monomials. -/
theorem prop36_of_endUpSpan (hSL : SimplyLaced C) (H : ∀ (μ : X) (i : I), EndUpSpan RD k μ i)
    (lam : X) : Prop36 RD k lam := by
  rw [prop36_iff_dg]
  intro ls hls
  cases ls with
  | nil => rw [dg_nil]; exact IsBub.id
  | cons x rest =>
    obtain ⟨a, g, b⟩ := x
    obtain ⟨h₀, h⟩ := hls
    have ha : a = [] := by
      have := congrArg List.length h₀; simp at this; exact List.eq_nil_of_length_eq_zero (by omega)
    have hb : b = [] := by
      have := congrArg List.length h₀; simp at this; exact List.eq_nil_of_length_eq_zero (by omega)
    subst ha hb
    have hg : g.dom = [] := by simpa using h₀.symm
    obtain ⟨⟨ε, i⟩, rfl⟩ := Shape.eq_cup_of_dom_nil hg
    cases ε with
    | true =>
      rw [dg_cupUp_eq_closeRight RD k lam i rest h]
      exact isBub_closeRight hSL lam i (H _ i _)
    | false =>
      rw [dg_cupDn_eq_closeLeft RD k lam i rest h]
      exact isBub_closeLeft lam i (H _ i _)

/-! ## Upward hom spaces -/

section UpSpan

variable {RD k}

/-- An upward endomorphism of a single upward strand consists of dots. -/
theorem upward_single_strand {i : I} {A : List (LayerData I)} (hA : Upward A)
    (h : SChain [up i] A [up i]) : A = List.replicate A.length ([], .dot (up i), []) := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    obtain ⟨a, g, b⟩ := x
    obtain ⟨h₀, h⟩ := h
    have hg : g.isUp = true := hA _ List.mem_cons_self
    have hl := congrArg List.length h₀
    simp only [List.length_cons, List.length_nil, List.length_append] at hl
    cases g with
    | cross ε c d => simp only [Shape.dom_cross, List.length_cons, List.length_nil] at hl; omega
    | cup l => simp [Shape.isUp] at hg
    | cap l => simp [Shape.isUp] at hg
    | dot l =>
      simp only [Shape.dom_dot, List.length_singleton] at hl
      have ha : a = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hb : b = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst ha hb
      have hl' : l = up i := by simpa using h₀.symm
      subst hl'
      rw [ih (fun y hy => hA y (List.mem_cons_of_mem _ hy)) h]
      simp [List.replicate_succ]

variable (RD k)

/-- Bubbles placed on the far right of a single strand. -/
theorem bubAt_single (μ : X) (l : Letter I) (γ : End ((pres RD k).obj (ob RD μ []))) :
    bubAt RD k μ [l] γ = bubRU RD k μ l γ := by
  have key := hom_ext_dg RD k μ (s := []) (t := []) (bubAt RD k μ [l]) (plcL RD k μ [l] [] [] [])
    (fun B _ => ?_)
  · exact LinearMap.congr_fun key γ
  exact (bubAt_dg RD k μ [l] B).trans (plcL_dg RD k μ [l] [] [] [] B).symm

/-- Upward diagrams on a single strand followed by bubble monomials are dots times bubble
monomials. -/
theorem upSpan_single_le (μ : X) (i : I) :
    upSpan RD k μ [up i] [up i] ≤ slideSetR RD k μ (up i) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨A, γ, hA, h, hγ, rfl⟩
  rw [upward_single_strand hA h, bubAt_single]
  exact mem_slideSetR hγ

theorem positive_ups (w : List I) : Positive (ups w) := by
  intro l hl
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
  rfl

/-- `UpSpanDiag` implies its one-strand case. -/
theorem endUpSpan_of_upSpanDiag {μ : X} (H : UpSpanDiag RD k μ) (i : I) : EndUpSpan RD k μ i := by
  intro f
  refine upSpan_single_le RD k μ i ?_
  refine Submodule.span_le.mpr ?_ (mem_span_dg RD k μ (s := [up i]) (t := [up i]) f)
  rintro _ ⟨ls, hls, rfl⟩
  exact H _ _ ls (positive_ups [i]) (positive_ups [i]) hls

/-- **Proposition 3.6 from Lemma 3.9 in diagrammatic form.** -/
theorem prop36_of_upSpanDiag (hSL : SimplyLaced C) (H : ∀ μ : X, UpSpanDiag RD k μ) (lam : X) :
    Prop36 RD k lam :=
  prop36_of_endUpSpan RD k hSL (fun μ i => endUpSpan_of_upSpanDiag RD k (H μ) i) lam

end UpSpan

/-! ## Proposition 3.10 and upward hom spaces -/

section Prop310

open KLR.Diagram MatEnd
open scoped TensorProduct

variable [DecidableEq I] (μ : X) (ν : Multiset I)

omit [DecidableEq I] in
/-- The image under `upFunctor` of a morphism of the diagrammatic KLR category lies in `upSpan`. -/
theorem upFunctor_map_mem_upSpan {a b : Obj (KLR.Diagram.sig I)}
    (F : (KLR.Diagram.pres k (KLR.klQ2 k C)).obj a ⟶ (KLR.Diagram.pres k (KLR.klQ2 k C)).obj b) :
    (upFunctor RD k μ).map F ∈ upSpan RD k μ (ups a.word) (ups b.word) := by
  obtain ⟨G, rfl⟩ := (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_surjective F
  induction G using Finsupp.induction_linear with
  | zero => rw [Presentation.lin_zero, Functor.map_zero]; exact Submodule.zero_mem _
  | add G₁ G₂ h₁ h₂ =>
    rw [Presentation.lin_add, Functor.map_add]; exact Submodule.add_mem _ h₁ h₂
  | single d c =>
    rw [Presentation.lin_single, Functor.map_smul, upFunctor_diag, upDiag_eq_dg]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨_, 𝟙 _, ?_, sChain_upLD
      (Diagram.chain d), IsBub.id, by rw [bubAt_id, Category.comp_id]⟩)
    intro x hx
    obtain ⟨L, -, rfl⟩ := List.mem_map.1 hx
    cases h : L.gen <;> simp [upLD, upShape, h, Shape.isUp]

/-- The entries of the image of `ϕ_{ν,μ}` lie in `upSpan`. -/
theorem phi_apply_mem_upSpan (x : KLR.R2 k C ν ⊗[k] PiLam I k) (s t : KLR.Seq ν) :
    phi RD k μ ν x s t ∈ upSpan RD k μ (ups (word s)) (ups (word t)) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r p =>
    rw [phi_tmul, mul_apply, Finset.sum_eq_single s]
    · rw [bubDiag_apply, sum_apply, Finset.sum_eq_single s]
      · rw [single_apply_self, bubAt_comm]
        have hF : (toUEnd RD k μ ν r) s t ∈ upSpan RD k μ (ups (word s)) (ups (word t)) :=
          upFunctor_map_mem_upSpan RD k μ ((diagREquiv k (KLR.klQ2 k C) ν r) s t)
        generalize (toUEnd RD k μ ν r) s t = F at hF ⊢
        induction hF using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
          rw [Category.assoc, ← bubAt_comp]
          exact Submodule.subset_span ⟨A, _, hA, h, IsBub.comp hγ ⟨p, rfl⟩, rfl⟩
        | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
        | add f g _ _ hf hg => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hf hg
        | smul c f _ hf => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hf
      · intro j _ hj
        rw [single_apply_of_ne _ (fun h => hj h.1.symm)]
      · simp
    · intro j _ hj
      rw [bubDiag_apply, sum_apply, Finset.sum_eq_single j]
      · rw [single_apply_of_ne _ (fun h => hj h.1.symm), Limits.zero_comp]
      · intro m _ hm
        rw [single_apply_of_ne _ (fun h => hm h.2.symm)]
      · simp
    · simp

/-- **Proposition 3.10 in terms of upward hom spaces**: `ϕ_{ν,μ}` is surjective if and only if
every 2-morphism `E_s 1_μ ⟶ E_t 1_μ` (`s, t ∈ Seq ν`) is a linear combination of upward
diagrams followed by bubble monomials on the far right (KL III Lemma 3.9 for `Seq ν`). -/
theorem prop310_iff_upSpan : Prop310 RD k μ ν ↔ ∀ (s t : KLR.Seq ν)
    (f : (pres RD k).obj (ob RD μ (ups (word s))) ⟶ (pres RD k).obj (ob RD μ (ups (word t)))),
      f ∈ upSpan RD k μ (ups (word s)) (ups (word t)) := by
  constructor
  · intro h s t f
    obtain ⟨x, hx⟩ := h (single s t f)
    have := phi_apply_mem_upSpan RD k μ ν x s t
    rwa [hx, single_apply_self] at this
  · intro h M
    have hM : M ∈ (phi RD k μ ν).range := by
      rw [eq_sum_single M]
      refine Subalgebra.sum_mem _ fun s _ => Subalgebra.sum_mem _ fun t _ => ?_
      exact single_upSpan_mem_range RD k μ ν s t (h s t _)
    obtain ⟨x, hx⟩ := hM
    exact ⟨x, hx⟩

/-- **Proposition 3.10 from Lemma 3.9 in diagrammatic form.** -/
theorem prop310_of_upSpanDiag (H : UpSpanDiag RD k μ) : Prop310 RD k μ ν := by
  rw [prop310_iff_upSpan]
  intro s t f
  refine Submodule.span_le.mpr ?_ (mem_span_dg RD k μ f)
  rintro _ ⟨ls, hls, rfl⟩
  exact H _ _ ls (positive_ups _) (positive_ups _) hls

omit [DecidableEq I] in
theorem endUpSpan_of_word {i : I} {w : List (Letter I)} (hw : w = [up i])
    (H : ∀ f : End ((pres RD k).obj (ob RD μ w)), f ∈ upSpan RD k μ w w) : EndUpSpan RD k μ i := by
  subst hw
  exact fun f => upSpan_single_le RD k μ i (H f)

/-- **Proposition 3.10 for a one-vertex `ν = {i}` implies the one-strand case of Lemma 3.9.** -/
theorem endUpSpan_of_prop310 (i : I) (h : Prop310 RD k μ {i}) : EndUpSpan RD k μ i := by
  let s : KLR.Seq ({i} : Multiset I) := ⟨fun _ => i, by simp⟩
  refine endUpSpan_of_word RD k μ (w := ups (word s)) (by simp [s, word, ups]) ?_
  intro f
  exact (prop310_iff_upSpan RD k μ {i}).1 h s s f

/-- **KL III Proposition 3.6 from Proposition 3.10** (for one-vertex `ν`; simply-laced Cartan
data): if `ϕ_{{i},μ} : R(i) ⊗ Π_μ → END_U(E_i 1_μ)` is surjective for all `i` and `μ`, then
`Π_λ → END_U(1_λ)` is surjective for all `λ`. -/
theorem prop36_of_prop310 (hSL : SimplyLaced C) (h : ∀ (μ : X) (i : I), Prop310 RD k μ {i})
    (lam : X) : Prop36 RD k lam :=
  prop36_of_endUpSpan RD k hSL (fun μ i => endUpSpan_of_prop310 RD k μ i (h μ i)) lam

end Prop310

end Categorification.KL3.Diagram
