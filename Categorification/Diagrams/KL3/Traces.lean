/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Markov

/-!
# Partial traces of upward diagrams and Proposition 3.6 for traces

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1
(Proposition 3.6, label `prop_bubbles_same_orient`) and §3.2.2 (Lemma 3.9, label
`lem_surjective`); TeX locators `sources/klr/kl3/0807.3250v1.txt`, lines 1690–1790.

The Markov lemma (`ptrLast_upward_mem_upSpan`, `Categorification.Diagrams.KL3.Markov`) closes the
last strand of an upward diagram. Here it is extended to upward diagrams followed by bubble
monomials (`ptrLast_mem_upSpan`: the bubbles inside the closed loop slide out across its
downward strand, KL III Propositions 3.3 and 3.4, simply-laced case), so that the partial trace
over the last strand preserves the span `upSpan` of upward diagrams times bubble monomials. This is
KL III's Lemma 3.9 for all diagrams obtained by closing strands of upward diagrams on the right.

Iterating, the **right trace** (`trR`: all strands closed on the right by nested cups and caps)
of any upward diagram with bubble monomials lies in the image of `Π_λ` (`trR_isBub`): KL III's
Proposition 3.6 for all closed diagrams that are right closures of upward diagrams
(`trR_dg_isBub`), e.g. the closures of arbitrary braid-like KLR diagrams.

## Main definitions

* `upsR r`, `innerR μ r`: the upward word `E_{r.reverse}` and the region to its right inside the
  right closure (the colours `r` in reverse order).
* `trR RD k μ r`: the right trace, closing the strands of `E_{r.reverse}` one after another.

## Main results

* `ptrLast_mem_upSpan`: the partial trace over the last strand maps `upSpan` to `upSpan`.
* `trR_isBub`, `trR_dg_isBub`: right traces of upward diagrams with bubble monomials are
  bubble monomials.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Bubbles inside the closed loop -/

section BubblesInside

variable (μ : X) (j : I)

/-- A bubble monomial on the far right inside the closed loop is an insertion in the region
between the closed strand and its downward return strand. -/
theorem ptrLast_bubAt_eq_ctxL {s t : List (Letter I)} (A : List (LayerData I))
    (hA : SChain (s ++ [up j]) A (t ++ [up j]))
    (γ : End ((pres RD k).obj (ob RD (wt RD μ [dn j]) []))) :
    ptrLast RD k μ s t j (dg RD k (wt RD μ [dn j]) (s ++ [up j]) (t ++ [up j]) A ≫
        bubAt RD k (wt RD μ [dn j]) (t ++ [up j]) γ) =
      ctxL RD k μ s t ([(s, .cup (up j), [])] ++ A.map (whL [] [dn j])) (t ++ [up j]) [dn j]
        [(t, .cap (dn j), [])] [] [] γ := by
  have hpre : SChain s ([(s, .cup (up j), [])] ++ A.map (whL [] [dn j])) (t ++ [up j] ++ [dn j]) :=
    (show SChain s [(s, .cup (up j), [])] (s ++ [up j] ++ [dn j]) from ⟨by simp, by simp⟩).append
      (by simpa using hA.whisk [] [dn j])
  have hpost : SChain (t ++ [up j] ++ [] ++ [dn j]) [(t, .cap (dn j), [])] t := ⟨by simp, by simp⟩
  have key := hom_ext_dg RD k (wt RD μ [dn j]) (s := []) (t := [])
    ((ptrLast RD k μ s t j).comp ((Linear.leftComp k _
      (dg RD k (wt RD μ [dn j]) (s ++ [up j]) (t ++ [up j]) A)).comp
        (bubAt RD k (wt RD μ [dn j]) (t ++ [up j]))))
    (ctxL RD k μ s t ([(s, .cup (up j), [])] ++ A.map (whL [] [dn j])) (t ++ [up j]) [dn j]
      [(t, .cap (dn j), [])] [] []) (fun B hB => ?_)
  · exact LinearMap.congr_fun key γ
  change ptrLast RD k μ s t j (dg RD k (wt RD μ [dn j]) (s ++ [up j]) (t ++ [up j]) A ≫
    bubAt RD k (wt RD μ [dn j]) (t ++ [up j]) (dg RD k (wt RD μ [dn j]) [] [] B)) = _
  have hB' : SChain (t ++ [up j]) (B.map (whL (t ++ [up j]) [])) (t ++ [up j]) := by
    simpa using hB.whisk (t ++ [up j]) []
  rw [bubAt_dg, dg_comp hA hB', ptrLast_dg, ctxL_dg RD k μ (by simpa using hpre) hpost]
  unfold closeLs
  wnf
  simp only [List.replicate_zero, List.nil_append, List.append_nil, List.map_map,
    Function.comp_def]

/-- A bubble monomial in the outer region, after the cap, is a bubble monomial on the far
right. -/
theorem ctxL_outer_eq {s t : List (Letter I)} (pre : List (LayerData I))
    (hpre : SChain s pre (t ++ [up j] ++ [dn j]))
    (δ : End ((pres RD k).obj (ob RD μ []))) :
    ctxL RD k μ s t pre (t ++ [up j] ++ [dn j]) [] [(t, .cap (dn j), [])] [] [] δ =
      dg RD k μ s t (pre ++ [(t, .cap (dn j), [])]) ≫ bubAt RD k μ t δ := by
  have hcap : SChain (t ++ [up j] ++ [dn j]) [(t, .cap (dn j), [])] t := ⟨by simp, by simp⟩
  have key := hom_ext_dg RD k μ (s := []) (t := [])
    (ctxL RD k μ s t pre (t ++ [up j] ++ [dn j]) [] [(t, .cap (dn j), [])] [] [])
    ((Linear.leftComp k _ (dg RD k μ s t (pre ++ [(t, .cap (dn j), [])]))).comp
      (bubAt RD k μ t)) (fun B hB => ?_)
  · exact LinearMap.congr_fun key δ
  change ctxL RD k μ s t pre (t ++ [up j] ++ [dn j]) [] [(t, .cap (dn j), [])] [] []
    (dg RD k μ [] [] B) =
    dg RD k μ s t (pre ++ [(t, .cap (dn j), [])]) ≫ bubAt RD k μ t (dg RD k μ [] [] B)
  have hBt : SChain t (B.map (whL t [])) t := by simpa using hB.whisk t []
  have hpre' : SChain s pre ((t ++ [up j] ++ [dn j]) ++ [] ++ []) := by simp only [List.append_nil]; exact hpre
  have hcap' : SChain ((t ++ [up j] ++ [dn j]) ++ [] ++ []) [(t, .cap (dn j), [])] t := by
    simp only [List.append_nil]; exact hcap
  rw [ctxL_dg_nil RD k μ (u := t ++ [up j] ++ [dn j]) (s := []) (t := []) hpre' hcap', bubAt_dg,
    dg_comp (hpre.append hcap) hBt]
  have e := dg_closed_left (RD := RD) (k := k) μ (S := s) (T := t) pre [] (s := t ++ [up j] ++ [dn j])
    (s' := t) [] hB (A := [([], .cap (dn j), [])].map (whL t [])) (by simp)
  wnf at e ⊢
  exact e.symm

variable {RD k}

/-- **The partial trace over the last strand preserves `upSpan`** (simply-laced Cartan data):
closing the last strand of an upward diagram followed by bubble monomials gives a linear
combination of upward diagrams followed by bubble monomials. -/
theorem ptrLast_mem_upSpan (hSL : SimplyLaced C) (a b : List I) {f}
    (hf : f ∈ upSpan RD k (wt RD μ [dn j]) (ups a ++ [up j]) (ups b ++ [up j]))
    [DecidableEq I] : ptrLast RD k μ (ups a) (ups b) j f ∈ upSpan RD k μ (ups a) (ups b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    rw [ptrLast_bubAt_eq_ctxL RD k μ j A h γ]
    have hpre : SChain (ups a) ([(ups a, .cup (up j), [])] ++ A.map (whL [] [dn j]))
        (ups b ++ [up j] ++ [dn j]) :=
      (show SChain (ups a) [(ups a, .cup (up j), [])] (ups a ++ [up j] ++ [dn j]) from
        ⟨by simp, by simp⟩).append (by simpa using h.whisk [] [dn j])
    rw [ctxL_cons RD k μ (by simpa using hpre) (by exact ⟨by simp, by simp⟩)]
    have hmem := bubLU_mem_slideSetR hSL (wt RD μ []) (dn j) (β := γ) hγ
    generalize bubLU RD k (wt RD μ []) (dn j) γ = g at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n, δ, hδ, rfl⟩ := hg
      rw [ctxL_dots_bubRU RD k μ (by simpa using hpre) (by exact ⟨by simp, by simp⟩)]
      have hpre' : SChain (ups a) ([(ups a, .cup (up j), [])] ++ A.map (whL [] [dn j]) ++
          List.replicate n (ups b ++ [up j], .dot (dn j), [])) (ups b ++ [up j] ++ [dn j]) :=
        hpre.append (SChain.replicate_of ⟨by simp, by simp⟩ n)
      rw [ctxL_outer_eq RD k μ j _ hpre' δ]
      -- the dots on the downward strand move to the closed strand
      have hdots : dg RD k μ (ups a) (ups b) ([(ups a, .cup (up j), [])] ++ A.map (whL [] [dn j]) ++
          List.replicate n (ups b ++ [up j], .dot (dn j), []) ++ [(ups b, .cap (dn j), [])]) =
          ptrLast RD k μ (ups a) (ups b) j (dg RD k (wt RD μ [dn j]) (ups a ++ [up j])
            (ups b ++ [up j]) (A ++ List.replicate n (ups b, .dot (up j), []))) := by
        rw [ptrLast_dg]
        refine (dg_step RD k μ (s₀ := ups a) (t₀ := ups b)
          ([(ups a, .cup (up j), [])] ++ A.map (whL [] [dn j])) [] (ups b) []
          (dg_dots_cap_dn RD k (wt RD μ []) j n) (by simpa using hpre) (by simp)
          (by simp [whL]) rfl).trans ?_
        unfold closeLs
        simp [whL, List.map_replicate]
      rw [hdots]
      have hA' : Upward (A ++ List.replicate n (ups b, .dot (up j), [])) := by
        refine hA.append fun x hx => ?_
        rw [List.eq_of_mem_replicate hx]; rfl
      have hch : SChain (ups a ++ [up j]) (A ++ List.replicate n (ups b, .dot (up j), []))
          (ups b ++ [up j]) := h.append (SChain.replicate_of ⟨by simp, by simp⟩ n)
      have hM := ptrLast_upward_mem_upSpan RD k μ a b j hA' hch
      generalize ptrLast RD k μ (ups a) (ups b) j (dg RD k (wt RD μ [dn j]) (ups a ++ [up j])
        (ups b ++ [up j]) (A ++ List.replicate n (ups b, .dot (up j), []))) = F at hM ⊢
      induction hM using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨A₁, γ₁, hA₁, h₁, hγ₁, rfl⟩ := hf
        rw [Category.assoc, ← bubAt_comp]
        exact Submodule.subset_span ⟨A₁, _, hA₁, h₁, IsBub.comp hγ₁ hδ, rfl⟩
      | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end BubblesInside

/-- The partial trace over the last strand maps `upSpan` to `upSpan`, for arbitrary upward
words. -/
theorem ptrLast_mem_upSpan' (hSL : SimplyLaced C) [DecidableEq I] (μ : X) (j : I)
    {s t : List (Letter I)} (hs : Positive s) (ht : Positive t) {f}
    (hf : f ∈ upSpan RD k (wt RD μ [dn j]) (s ++ [up j]) (t ++ [up j])) :
    ptrLast RD k μ s t j f ∈ upSpan RD k μ s t := by
  obtain ⟨a, rfl⟩ : ∃ a, ups a = s := ⟨_, ups_map_snd hs⟩
  obtain ⟨b, rfl⟩ : ∃ b, ups b = t := ⟨_, ups_map_snd ht⟩
  exact ptrLast_mem_upSpan μ j hSL a b hf

/-! ## Right traces -/

section Trace

variable (μ : X)

/-- The upward word `E_{r.reverse}` (the colours `r` in reverse order). -/
def upsR : List I → List (Letter I)
  | [] => []
  | j :: r => upsR r ++ [up j]

/-- The region to the right of `E_{r.reverse}` inside its right closure with outer region `μ`. -/
def innerR : List I → X
  | [] => μ
  | j :: r => wt RD (innerR r) [dn j]

theorem positive_upsR (r : List I) : Positive (upsR r) := by
  induction r with
  | nil => intro l hl; simp [upsR] at hl
  | cons j r ih =>
    intro l hl
    simp only [upsR, List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact ih l hl
    · rfl

/-- **The right trace**: the strands of `E_{r.reverse}` closed on the right by nested cups and
caps, the last strand innermost (the partial traces `ptrLast`, iterated). -/
def trR : (r : List I) →
    (End ((pres RD k).obj (ob RD (innerR RD μ r) (upsR r)))) →ₗ[k] End ((pres RD k).obj (ob RD μ []))
  | [] => LinearMap.id
  | j :: r => (trR r).comp (ptrLast RD k (innerR RD μ r) (upsR r) (upsR r) j)

/-- The layers of the right trace. -/
def trLs : (r : List I) → List (LayerData I) → List (LayerData I)
  | [], A => A
  | j :: r, A => trLs r (closeLs j (upsR r) (upsR r) A 0)

theorem trR_dg (r : List I) (A : List (LayerData I)) :
    trR RD k μ r (dg RD k (innerR RD μ r) (upsR r) (upsR r) A) = dg RD k μ [] [] (trLs r A) := by
  induction r generalizing A with
  | nil => rfl
  | cons j r ih =>
    show trR RD k μ r (ptrLast RD k (innerR RD μ r) (upsR r) (upsR r) j
      (dg RD k (wt RD (innerR RD μ r) [dn j]) (upsR r ++ [up j]) (upsR r ++ [up j]) A)) = _
    rw [ptrLast_dg, ih]
    rfl

theorem upSpan_nil_isBub {f : End ((pres RD k).obj (ob RD μ []))}
    (hf : f ∈ upSpan RD k μ [] []) : IsBub RD k μ f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hup, h, hγ, rfl⟩ := hf
    have hA : A = [] := by
      cases A with
      | nil => rfl
      | cons x A =>
        exfalso
        obtain ⟨a, g, b⟩ := x
        have hg : g.isUp = true := hup _ List.mem_cons_self
        have := congrArg List.length h.1
        cases g with
        | dot l => simp at this; omega
        | cross ε c d => simp at this; omega
        | cup l => simp [Shape.isUp] at hg
        | cap l => simp [Shape.isUp] at hg
    subst hA
    have hb : bubAt RD k μ [] γ = γ := by
      have key := hom_ext_dg RD k μ (s := []) (t := []) (bubAt RD k μ []) LinearMap.id
        (fun B _ => by
          change bubAt RD k μ [] (dg RD k μ [] [] B) = dg RD k μ [] [] B
          rw [bubAt_dg]; simp)
      exact LinearMap.congr_fun key γ
    rw [dg_nil]
    erw [Category.id_comp, hb]
    exact hγ
  | zero => exact IsBub.zero
  | add x y _ _ hx hy => exact IsBub.add hx hy
  | smul r x _ hx => exact IsBub.smul r hx

variable {RD k}

/-- **Right traces of upward diagrams with bubble monomials are bubble monomials** (KL III
Proposition 3.6 for right traces; simply-laced Cartan data). -/
theorem trR_isBub (hSL : SimplyLaced C) [DecidableEq I] (r : List I)
    {f : End ((pres RD k).obj (ob RD (innerR RD μ r) (upsR r)))}
    (hf : f ∈ upSpan RD k (innerR RD μ r) (upsR r) (upsR r)) : IsBub RD k μ (trR RD k μ r f) := by
  induction r with
  | nil => exact upSpan_nil_isBub RD k μ hf
  | cons j r ih =>
    exact ih (ptrLast_mem_upSpan' RD k hSL (innerR RD μ r) j (positive_upsR r) (positive_upsR r) hf)

/-- **KL III Proposition 3.6 for right traces of upward diagrams**: the closed diagram obtained by
closing all strands of an upward diagram on the right (nested cups and caps) lies in the image of
`Π_λ → END_U(1_λ)` (simply-laced Cartan data). -/
theorem trR_dg_isBub (hSL : SimplyLaced C) [DecidableEq I] (r : List I) {A : List (LayerData I)}
    (hA : Upward A) (h : SChain (upsR r) A (upsR r)) :
    IsBub RD k μ (dg RD k μ [] [] (trLs r A)) := by
  rw [← trR_dg]
  refine trR_isBub μ hSL r (Submodule.subset_span ⟨A, 𝟙 _, hA, h, IsBub.id, ?_⟩)
  rw [bubAt_id, Category.comp_id]

end Trace

end Categorification.KL3.Diagram
