/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SpanningPhi
import Categorification.Diagrams.KL3.Reduction

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

* `UpSpanDiag RD k sc μ`: **KL III Lemma 3.9 in diagrammatic form** — every normal-form diagram of
  `U` between two upward sequences (rightmost region `μ`) is a linear combination of upward
  diagrams followed by bubble monomials on the far right (the span `upSpan` of
  `Categorification.Diagrams.KL3.SpanningPhi`).
* `EndUpSpan RD k sc μ i`: its one-strand case: every endomorphism of `E_i 1_μ` is a linear
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
  if `EndUpSpan RD k sc μ i` holds for all `μ` and `i`, then `Prop36 RD k sc λ` holds for all `λ`.
* `endUpSpan_of_upSpanDiag`, `prop310_of_upSpanDiag`, `prop36_of_upSpanDiag`: `UpSpanDiag`
  implies its one-strand case, Proposition 3.10 (`Prop310`, for every `ν`) and Proposition 3.6.
* `endUpSpan_of_prop310`, `prop36_of_prop310`: **Proposition 3.10 for one-vertex `ν` implies
  Proposition 3.6**.

The remaining input, `UpSpanDiag` (equivalently KL III's reduction of crossings, cups and caps in
diagrams between upward sequences), is proved for every Cartan datum in
`Categorification.Diagrams.KL3.Lemma39` (`upSpanDiag`, `prop36`,
`prop310`).
-/

-- Elaborate the diagram functor transports through semireducible definitions.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## The statements -/

/-- **KL III Lemma 3.9, diagrammatic form** (rightmost region `μ`): every normal-form diagram of
`U` from an upward sequence `s` to an upward sequence `t` is a linear combination of upward
diagrams followed by bubble monomials on the far right. -/
def UpSpanDiag (μ : X) : Prop :=
  ∀ (s t : List (Letter I)) (ls : List (LayerData I)), Positive s → Positive t → SChain s ls t →
    NF.dg (pres RD k sc) μ s t ls ∈ upSpan RD k sc μ s t

/-- The one-strand case of Lemma 3.9: every endomorphism of `E_i 1_μ` is a linear combination of
dots on the strand times bubble monomials to its right. -/
def EndUpSpan (μ : X) (i : I) : Prop :=
  ∀ f : End ((pres RD k sc).obj (ob RD μ [up i])), f ∈ slideSetR RD k sc μ (up i)

/-! ## Bending a closed diagram along its lowest cup -/

section Bend

variable (lam : X) (i : I)

/-- **A closed diagram beginning with the cup `1 → E_i F_i` is a right closure**: bending the
downward leg of the first cup up to the top (a second cup and the zigzag relation) exhibits it
as the clockwise closure of an endomorphism of `E_i`. -/
theorem dg_cupUp_eq_closeRight (rest : List (LayerData I)) (h : SChain [up i, dn i] rest []) :
    NF.dg (pres RD k sc) lam [] [] (([], .cup (up i), []) :: rest) =
      closeRight RD k sc lam i (NF.dg (pres RD k sc) (wt RD lam [dn i]) [up i] [up i]
        (([up i], .cup (dn i), []) :: rest.map (whL [] [up i]))) := by
  have hA : SChain [up i] (([up i], .cup (dn i), []) :: rest.map (whL [] [up i])) [up i] :=
    ⟨rfl, by simpa using h.whisk [] [up i]⟩
  have hA' := hA.whisk [] [dn i]
  simp only [List.nil_append, List.singleton_append] at hA'
  rw [closeRight_apply, NF.plcL_dg]
  show _ = NF.dg (pres RD k sc) lam [] [up i, dn i] _ ≫ NF.dg (pres RD k sc) lam [up i, dn i] [up i, dn i] _ ≫
    NF.dg (pres RD k sc) lam [up i, dn i] [] _
  rw [NF.dg_comp hA' (by schain), NF.dg_comp (by schain) (hA'.append (by schain))]
  -- move the final cap below `rest` (interchange law), then straighten the zigzag
  have e := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := []) (T := [])
    [([], .cup (up i), []), ([up i], .cup (dn i), [dn i])] [] h
    (B := [([], .cap (dn i), [])]) (t := [up i, dn i]) (t' := []) (by schain)
  wnf at e
  wnf
  rw [e]
  symm
  refine (NF.dg_step (pres RD k sc) lam [([], .cup (up i), [])] rest [up i] []
    (NF.dg_zigL' (pres RD k sc) (wt RD lam []) (dn i)) (by schain) h (by simp [whL]) rfl).trans ?_
  simp

/-- **A closed diagram beginning with the cup `1 → F_i E_i` is a left closure**: the
counterclockwise closure of an endomorphism of `E_i`. -/
theorem dg_cupDn_eq_closeLeft (rest : List (LayerData I)) (h : SChain [dn i, up i] rest []) :
    NF.dg (pres RD k sc) lam [] [] (([], .cup (dn i), []) :: rest) =
      closeLeft RD k sc lam i (NF.dg (pres RD k sc) lam [up i] [up i]
        (([], .cup (up i), [up i]) :: rest.map (whL [up i] []))) := by
  have hA : SChain [up i] (([], .cup (up i), [up i]) :: rest.map (whL [up i] [])) [up i] :=
    ⟨rfl, by simpa using h.whisk [up i] []⟩
  have hA' := hA.whisk [dn i] []
  simp only [List.append_nil, List.singleton_append] at hA'
  rw [closeLeft_apply, NF.plcL_dg_nil]
  show _ = NF.dg (pres RD k sc) lam [] [dn i, up i] _ ≫ NF.dg (pres RD k sc) lam [dn i, up i] [dn i, up i] _ ≫
    NF.dg (pres RD k sc) lam [dn i, up i] [] _
  rw [NF.dg_comp hA' (by schain), NF.dg_comp (by schain) (hA'.append (by schain))]
  -- move the final cap below `rest` (interchange law), then straighten the zigzag
  have e := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := []) (T := [])
    [([], .cup (dn i), []), ([dn i], .cup (up i), [up i])] []
    (A := [([], .cap (up i), [])]) (s := [dn i, up i]) (s' := []) (by schain) h
  wnf at e
  wnf
  rw [← e]
  symm
  refine (NF.dg_step (pres RD k sc) lam [([], .cup (dn i), [])] rest [] [up i]
    (NF.dg_zigR' (pres RD k sc) (wt RD lam [up i]) (up i)) (by schain) h (by simp [whL]) rfl).trans ?_
  simp

end Bend

/-! ## Closures of dots times bubble monomials -/

section Closures

variable {RD k sc}

/-- For an upward strand, dots times bubble monomials on the right are also dots times bubble
monomials on the left (bubble slides, KL III Propositions 3.3 and 3.4). -/
theorem slideSetR_le_slideSetL_up (μ : X) (j : I) :
    slideSetR RD k sc μ (up j) ≤ slideSetL RD k sc μ (up j) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, γ, hγ, rfl⟩
  have hd : NF.dotsU (pres RD k sc) μ (up j) a ∈ slideSetL RD k sc μ (up j) := by
    have := mem_slideSetL (RD := RD) (k := k) (sc := sc) (μ := μ) (l := up j) (a := a) (IsBub.id)
    rwa [bubLU_id, Category.comp_id] at this
  exact slideSetL_comp hd (bubRU_up_mem_gen μ j hγ)

variable (lam : X) (i : I)

/-- The right closure of dots times bubble monomials is a bubble monomial times a dotted
clockwise bubble. -/
theorem isBub_closeRight {g : End ((pres RD k sc).obj (ob RD (wt RD lam [dn i]) [up i]))}
    (hg : g ∈ slideSetR RD k sc (wt RD lam [dn i]) (up i)) :
    IsBub RD k sc lam (closeRight RD k sc lam i g) := by
  have hg' := slideSetR_le_slideSetL_up (wt RD lam [dn i]) i hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    rw [← NF.bubLU_comm, closeRight_bubLU]
    exact IsBub.comp (IsBub.wtTransport _ hγ) (cwU_isBub _ _)
  | zero => rw [map_zero]; exact IsBub.zero
  | add x y _ _ hx hy => rw [map_add]; exact IsBub.add hx hy
  | smul r x _ hx => rw [map_smul]; exact IsBub.smul r hx

/-- The left closure of dots times bubble monomials is a bubble monomial times a dotted
counterclockwise bubble. -/
theorem isBub_closeLeft {g : End ((pres RD k sc).obj (ob RD lam [up i]))}
    (hg : g ∈ slideSetR RD k sc lam (up i)) :
    IsBub RD k sc lam (closeLeft RD k sc lam i g) := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    rw [← NF.bubRU_comm, closeLeft_bubRU]
    exact IsBub.comp hγ (ccwU_isBub _ _)
  | zero => rw [map_zero]; exact IsBub.zero
  | add x y _ _ hx hy => rw [map_add]; exact IsBub.add hx hy
  | smul r x _ hx => rw [map_smul]; exact IsBub.smul r hx

end Closures

/-! ## Proposition 3.6 from the one-strand case of Lemma 3.9 -/


/-- **KL III Proposition 3.6 from the one-strand case of Lemma 3.9**:
if every endomorphism of every upward strand `E_i 1_μ` is a linear combination of dots times
bubble monomials, then `Π_λ → END_U(1_λ)` is surjective for every `λ`. A closed diagram is the
closure of an endomorphism of an upward strand along its lowest cup (`dg_cupUp_eq_closeRight`,
`dg_cupDn_eq_closeLeft`), and closures of dots times bubble monomials are bubble monomials. -/
theorem prop36_of_endUpSpan (H : ∀ (μ : X) (i : I), EndUpSpan RD k sc μ i)
    (lam : X) : Prop36 RD k sc lam := by
  rw [prop36_iff_dg]
  intro ls hls
  cases ls with
  | nil => rw [NF.dg_nil]; exact IsBub.id
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
      rw [dg_cupUp_eq_closeRight RD k sc lam i rest h]
      exact isBub_closeRight lam i (H _ i _)
    | false =>
      rw [dg_cupDn_eq_closeLeft RD k sc lam i rest h]
      exact isBub_closeLeft lam i (H _ i _)

/-! ## Upward hom spaces -/

section UpSpan

variable {RD k sc}


variable (RD k sc)

/-- Bubbles placed on the far right of a single strand. -/
theorem bubAt_single (μ : X) (l : Letter I) (γ : End ((pres RD k sc).obj (ob RD μ []))) :
    bubAt RD k sc μ [l] γ = NF.bubRU (pres RD k sc) μ l γ := by
  have key := hom_ext_dg RD k sc μ (s := []) (t := []) (bubAt RD k sc μ [l]) (NF.plcL (pres RD k sc) μ [l] [] [] [])
    (fun B _ => ?_)
  · exact LinearMap.congr_fun key γ
  exact (bubAt_dg RD k sc μ [l] B).trans (NF.plcL_dg (pres RD k sc) μ [l] [] [] [] B).symm

/-- Upward diagrams on a single strand followed by bubble monomials are dots times bubble
monomials. -/
theorem upSpan_single_le (μ : X) (i : I) :
    upSpan RD k sc μ [up i] [up i] ≤ slideSetR RD k sc μ (up i) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨A, γ, hA, h, hγ, rfl⟩
  rw [upward_single_strand hA h, bubAt_single]
  exact mem_slideSetR hγ


/-- `UpSpanDiag` implies its one-strand case. -/
theorem endUpSpan_of_upSpanDiag {μ : X} (H : UpSpanDiag RD k sc μ) (i : I) : EndUpSpan RD k sc μ i := by
  intro f
  refine upSpan_single_le RD k sc μ i ?_
  refine Submodule.span_le.mpr ?_ (mem_span_dg RD k sc μ (s := [up i]) (t := [up i]) f)
  rintro _ ⟨ls, hls, rfl⟩
  exact H _ _ ls (positive_ups [i]) (positive_ups [i]) hls

/-- **Proposition 3.6 from Lemma 3.9 in diagrammatic form.** -/
theorem prop36_of_upSpanDiag (H : ∀ μ : X, UpSpanDiag RD k sc μ) (lam : X) :
    Prop36 RD k sc lam :=
  prop36_of_endUpSpan RD k sc (fun μ i => endUpSpan_of_upSpanDiag RD k sc (H μ) i) lam

end UpSpan

/-! ## Proposition 3.10 and upward hom spaces -/

section Prop310

open KLR.Diagram MatEnd
open scoped TensorProduct

variable [DecidableEq I] (μ : X) (ν : Multiset I)

omit [DecidableEq I] in
/-- The image under `upFunctor` of a morphism of the diagrammatic KLR category lies in `upSpan`. -/
theorem upFunctor_map_mem_upSpan {a b : Obj (KLR.Diagram.sig I)}
    (F : (KLR.Diagram.pres k (CL.qCL sc)).obj a ⟶ (KLR.Diagram.pres k (CL.qCL sc)).obj b) :
    (upFunctor RD k sc μ).map F ∈ upSpan RD k sc μ (ups a.word) (ups b.word) := by
  obtain ⟨G, rfl⟩ := (KLR.Diagram.pres k (CL.qCL sc)).lin_surjective F
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
theorem phi_apply_mem_upSpan (x : KLR.KLRAlgebra k (CL.qCL sc) ν ⊗[k] PiLam I k) (s t : KLR.Seq ν) :
    phi RD k sc μ ν x s t ∈ upSpan RD k sc μ (ups (word s)) (ups (word t)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r p =>
    rw [phi_tmul, mul_apply, Finset.sum_eq_single s]
    · rw [bubDiag_apply, MatEnd.sum_apply, Finset.sum_eq_single s]
      · rw [single_apply_self, bubAt_comm]
        have hF : (toUEnd RD k sc μ ν r) s t ∈ upSpan RD k sc μ (ups (word s)) (ups (word t)) :=
          upFunctor_map_mem_upSpan RD k sc μ ((diagREquiv k (CL.qCL sc) ν r) s t)
        generalize (toUEnd RD k sc μ ν r) s t = F at hF ⊢
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
      rw [bubDiag_apply, MatEnd.sum_apply, Finset.sum_eq_single j]
      · rw [single_apply_of_ne _ (fun h => hj h.1.symm), Limits.zero_comp]
      · intro m _ hm
        rw [single_apply_of_ne _ (fun h => hm h.2.symm)]
      · simp
    · simp

/-- **Proposition 3.10 in terms of upward hom spaces**: `ϕ_{ν,μ}` is surjective if and only if
every 2-morphism `E_s 1_μ ⟶ E_t 1_μ` (`s, t ∈ Seq ν`) is a linear combination of upward
diagrams followed by bubble monomials on the far right (KL III Lemma 3.9 for `Seq ν`). -/
theorem prop310_iff_upSpan : Prop310 RD k sc μ ν ↔ ∀ (s t : KLR.Seq ν)
    (f : (pres RD k sc).obj (ob RD μ (ups (word s))) ⟶ (pres RD k sc).obj (ob RD μ (ups (word t)))),
      f ∈ upSpan RD k sc μ (ups (word s)) (ups (word t)) := by
  constructor
  · intro h s t f
    obtain ⟨x, hx⟩ := h (single s t f)
    have := phi_apply_mem_upSpan RD k sc μ ν x s t
    rwa [hx, single_apply_self] at this
  · intro h M
    have hM : M ∈ (phi RD k sc μ ν).range := by
      rw [eq_sum_single M]
      refine Subalgebra.sum_mem _ fun s _ => Subalgebra.sum_mem _ fun t _ => ?_
      exact single_upSpan_mem_range RD k sc μ ν s t (h s t _)
    obtain ⟨x, hx⟩ := hM
    exact ⟨x, hx⟩

/-- **Proposition 3.10 from Lemma 3.9 in diagrammatic form.** -/
theorem prop310_of_upSpanDiag (H : UpSpanDiag RD k sc μ) : Prop310 RD k sc μ ν := by
  rw [prop310_iff_upSpan]
  intro s t f
  refine Submodule.span_le.mpr ?_ (mem_span_dg RD k sc μ f)
  rintro _ ⟨ls, hls, rfl⟩
  exact H _ _ ls (positive_ups _) (positive_ups _) hls

omit [DecidableEq I] in
theorem endUpSpan_of_word {i : I} {w : List (Letter I)} (hw : w = [up i])
    (H : ∀ f : End ((pres RD k sc).obj (ob RD μ w)), f ∈ upSpan RD k sc μ w w) : EndUpSpan RD k sc μ i := by
  subst hw
  exact fun f => upSpan_single_le RD k sc μ i (H f)

/-- **Proposition 3.10 for a one-vertex `ν = {i}` implies the one-strand case of Lemma 3.9.** -/
theorem endUpSpan_of_prop310 (i : I) (h : Prop310 RD k sc μ {i}) : EndUpSpan RD k sc μ i := by
  let s : KLR.Seq ({i} : Multiset I) := ⟨fun _ => i, by simp⟩
  refine endUpSpan_of_word RD k sc μ (w := ups (word s)) (by simp [s, word, ups]) ?_
  intro f
  exact (prop310_iff_upSpan RD k sc μ {i}).1 h s s f

/-- **KL III Proposition 3.6 from Proposition 3.10** (for one-vertex `ν`):
if `ϕ_{{i},μ} : R(i) ⊗ Π_μ → END_U(E_i 1_μ)` is surjective for all `i` and `μ`, then
`Π_λ → END_U(1_λ)` is surjective for all `λ`. -/
theorem prop36_of_prop310 (h : ∀ (μ : X) (i : I), Prop310 RD k sc μ {i})
    (lam : X) : Prop36 RD k sc lam :=
  prop36_of_endUpSpan RD k sc (fun μ i => endUpSpan_of_prop310 RD k sc μ i (h μ i)) lam

end Prop310

end Categorification.KL3.Diagram.CLQ
