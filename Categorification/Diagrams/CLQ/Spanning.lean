/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SpanningBasic
import Categorification.Diagrams.KL3.Spanning

/-!
# Closed crossingless diagrams of `U` are linear combinations of bubble monomials

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1,
Proposition 3.6 (label `prop_bubbles_same_orient`). KL III's proof has three steps:

1. "By induction on the number of crossings of a closed diagram `D` representing an
   endomorphism of `1_λ` one can reduce `D` to a linear combination of crossingless diagrams
   following the methods of [Lau1, Section 8]."
2. "Crossingless diagrams that contain nested bubbles can be written as linear combinations of
   crossingless nonnested diagrams using the bubble slide equations in Propositions 3.3 and
   3.4."
3. "Using the Grassmannian relations (3.7) all dotted bubbles with the same label `i` can be
   made to have the same orientation given by (3.24)."

This file proves steps 2 and 3 for arbitrary closed crossingless diagrams (`crossFree_isBub`):
every closed diagram of `U` with outer region `λ` whose layers are dots, cups and caps (in any
order and any nesting) is a linear combination of bubble monomials, i.e. lies in the image of
`Π_λ`. Step 1 (the reduction of crossings) is not formalized here; `Prop36` records the full
statement and `prop36_iff` its reduction to closed normal-form diagrams.

## The argument

A closed crossingless diagram in normal form (a list of layers from the empty word to the
empty word) is reduced by induction on its number of cups and caps. Its lowest cap is moved
down (interchange law) past everything that does not touch its two strands, collecting the dots
on its strands into a block of dots on its left strand (cyclicity of dots, `dg_dotR_cap`), until
it meets the cup that created one of its strands. Then either
* the cup creates both strands: cup, dots and cap form a dotted bubble (`isBub_bubLs`) placed in
  some region between the strands `u` and `v`; it is moved to the rightmost region across the
  strands of `v`, one strand at a time, by the bubble slides (`slideOut`, using
  `bubLU_mem_slideSetR`), which leaves dots on these strands and a bubble monomial in the outer
  region; or
* the cup and the cap form a zigzag (`dg_zig₁`, `dg_zig₂`), which is removed.
In both cases the number of cups and caps drops by two.

The bubble slides of KL III are stated for simply-laced Cartan data; for an arbitrary Cartan
datum we use the bubble slides in all degrees of
`Categorification.Diagrams.KL3.BubbleSlidesGen` (through `bubLU_mem_slideSetR_gen`), so the
results hold for every Cartan datum.

## Main results

* `slideOut`: an element of the image of `Π` placed anywhere in a diagram can be moved to the
  outer region, leaving dots behind.
* `crossFree_isBub`: **closed crossingless diagrams lie in the image of `Π_λ`** (KL III
  Proposition 3.6, steps 2 and 3 of its proof).
* `Prop36`, `prop36_iff_dg`: Proposition 3.6 (surjectivity of `Π_λ → END_U(1_λ)`) and its
  equivalence with the statement that every closed normal-form diagram lies in the image.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Crossingless diagrams -/

namespace Shape




end Shape













/-! ## Positions of a generator relative to a cap -/



/-! ## Local moves -/

section Local

variable (ν : X)

/-- A dot on the right strand of a cap below a block of dots on its left strand joins the block
(cyclicity of dots, KL III (3.3)). -/
theorem dg_dotR_cap (l : Letter I) (m : ℕ) :
    NF.dg (pres RD k sc) ν [l.dual, l] [] ([([l.dual], .dot l, [])] ++
        List.replicate m ([], .dot l.dual, [l]) ++ [([], .cap l, [])]) =
      NF.dg (pres RD k sc) ν [l.dual, l] [] (List.replicate (m + 1) ([], .dot l.dual, [l]) ++
        [([], .cap l, [])]) := by
  obtain ⟨b, i⟩ := l
  cases b
  · -- `l = F_i`, cap `E_i F_i → 1`
    show NF.dg (pres RD k sc) ν [up i, dn i] [] ([([up i], .dot (dn i), [])] ++
        List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]) =
      NF.dg (pres RD k sc) ν [up i, dn i] [] (List.replicate (m + 1) ([], .dot (up i), [dn i]) ++
        [([], .cap (dn i), [])])
    dstepQ [] [([], .cap (dn i), [])] [] [] (NF.dg_swap_dots (pres RD k sc) ν [] [] [] (up i) (dn i) 1 m)
    dstepQ (List.replicate m ([], .dot (up i), [dn i])) [] [] [] (dg_dot_cap_dn RD k sc ν i)
    simp [List.replicate_succ']
  · -- `l = E_i`, cap `F_i E_i → 1`
    show NF.dg (pres RD k sc) ν [dn i, up i] [] ([([dn i], .dot (up i), [])] ++
        List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]) =
      NF.dg (pres RD k sc) ν [dn i, up i] [] (List.replicate (m + 1) ([], .dot (dn i), [up i]) ++
        [([], .cap (up i), [])])
    dstepQ [] [([], .cap (up i), [])] [] [] (NF.dg_swap_dots (pres RD k sc) ν [] [] [] (dn i) (up i) 1 m)
    dstepQ (List.replicate m ([], .dot (dn i), [up i])) [] [] [] (dg_dot_cap_up RD k sc ν i).symm
    simp [List.replicate_succ']

/-- The first zigzag with dots on its middle segment is a strand with dots. -/
theorem dg_zig₁ (l : Letter I) (m : ℕ) :
    NF.dg (pres RD k sc) ν [l] [l] ([([], .cup l, [l])] ++ List.replicate m ([l], .dot l.dual, [l]) ++
        [([l], .cap l, [])]) =
      NF.dg (pres RD k sc) ν [l] [l] (List.replicate m ([], .dot l, [])) := by
  obtain ⟨b, i⟩ := l
  cases b
  · show NF.dg (pres RD k sc) ν [dn i] [dn i] ([([], .cup (dn i), [dn i])] ++
        List.replicate m ([dn i], .dot (up i), [dn i]) ++ [([dn i], .cap (dn i), [])]) =
      NF.dg (pres RD k sc) ν [dn i] [dn i] (List.replicate m ([], .dot (dn i), []))
    dstepQ [] [([dn i], .cap (dn i), [])] [] [dn i] (dg_dots_cupDn RD k sc i (wt RD ν [dn i]) m)
    dstepQ [([], .cup (dn i), [dn i])] [] [] []
      (NF.dg_swap_rep' (pres RD k sc) ν [] [] [] (.cap (dn i)) (.dot (dn i)) rfl m)
    dstepQ [] (List.replicate m ([], .dot (dn i), [])) [] [] (NF.dg_zigL' (pres RD k sc) ν (dn i))
    simp
  · show NF.dg (pres RD k sc) ν [up i] [up i] ([([], .cup (up i), [up i])] ++
        List.replicate m ([up i], .dot (dn i), [up i]) ++ [([up i], .cap (up i), [])]) =
      NF.dg (pres RD k sc) ν [up i] [up i] (List.replicate m ([], .dot (up i), []))
    dstepQ [] [([up i], .cap (up i), [])] [] [up i] (dg_dots_cupUp RD k sc i (wt RD ν [up i]) m)
    dstepQ [([], .cup (up i), [up i])] [] [] []
      (NF.dg_swap_rep' (pres RD k sc) ν [] [] [] (.cap (up i)) (.dot (up i)) rfl m)
    dstepQ [] (List.replicate m ([], .dot (up i), [])) [] [] (NF.dg_zigL' (pres RD k sc) ν (up i))
    simp

/-- The second zigzag, with dots on the strand below it, is a strand with dots. -/
theorem dg_zig₂ (l : Letter I) (m : ℕ) :
    NF.dg (pres RD k sc) ν [l.dual] [l.dual] ([([l.dual], .cup l, [])] ++
        List.replicate m ([], .dot l.dual, [l, l.dual]) ++ [([], .cap l, [l.dual])]) =
      NF.dg (pres RD k sc) ν [l.dual] [l.dual] (List.replicate m ([], .dot l.dual, [])) := by
  dstepQ [] [([], .cap l, [l.dual])] [] []
    (NF.dg_swap_rep' (pres RD k sc) ν [] [] [] (.cup l) (.dot l.dual) rfl m).symm
  dstepQ (List.replicate m ([], .dot l.dual, [])) [] [] [] (NF.dg_zigR' (pres RD k sc) ν l)
  simp

/-- A cup, dots on its left leg and a cap form a dotted bubble, which lies in the image of
`Π_ν`. -/
theorem isBub_bubLs (l : Letter I) (m : ℕ) :
    IsBub RD k sc ν (NF.dg (pres RD k sc) ν [] [] ([([], .cup l.dual, [])] ++
      List.replicate m ([], .dot l.dual, [l]) ++ [([], .cap l, [])])) := by
  obtain ⟨b, i⟩ := l
  cases b
  · have e : NF.dg (pres RD k sc) ν [] [] ([([], .cup (up i), [])] ++
        List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]) =
        NF.dg (pres RD k sc) ν [] [] (cwLs i m) := by
      rw [cwLs, dg_cw_dots]
    exact e ▸ dg_cwLs_isBub i m
  · have e : NF.dg (pres RD k sc) ν [] [] ([([], .cup (dn i), [])] ++
        List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]) =
        NF.dg (pres RD k sc) ν [] [] (ccwLs i m) := by
      rw [ccwLs]
      dstepQ [([], .cup (dn i), [])] [] [] [] (dg_dots_cap_up RD k sc ν i m)
      simp
    exact e ▸ dg_ccwLs_isBub i m

end Local

/-! ## Moving a bubble monomial to the outer region -/

section SlideOut

variable (lam : X)

theorem ctxL_cons {S T : List (Letter I)} {pre post : List (LayerData I)} {u v' : List (Letter I)}
    {l : Letter I} (hpre : SChain S pre (u ++ l :: v')) (hpost : SChain (u ++ l :: v') post T)
    (β : End ((pres RD k sc).obj (ob RD (wt RD lam (l :: v')) []))) :
    NF.ctxL (pres RD k sc) lam S T pre u (l :: v') post [] [] β =
      NF.ctxL (pres RD k sc) lam S T pre u v' post [l] [l] (NF.bubLU (pres RD k sc) (wt RD lam v') l β) := by
  have key := hom_ext_dg RD k sc (wt RD lam (l :: v')) (s := []) (t := [])
    (NF.ctxL (pres RD k sc) lam S T pre u (l :: v') post [] [])
    ((NF.ctxL (pres RD k sc) lam S T pre u v' post [l] [l]).comp (NF.plcL (pres RD k sc) (wt RD lam v') [] [l] [] []))
    (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  have e : NF.plcL (pres RD k sc) (wt RD lam v') [] [l] [] [] (NF.dg (pres RD k sc) (wt RD lam (l :: v')) [] [] B) =
      NF.dg (pres RD k sc) (wt RD lam v') [l] [l] (B.map (whL [] [l])) := NF.plcL_dg (pres RD k sc) (wt RD lam v') [] [l] [] [] B
  change NF.ctxL (pres RD k sc) lam S T pre u (l :: v') post [] [] (NF.dg (pres RD k sc) (wt RD lam (l :: v')) [] [] B) =
    NF.ctxL (pres RD k sc) lam S T pre u v' post [l] [l]
      (NF.plcL (pres RD k sc) (wt RD lam v') [] [l] [] [] (NF.dg (pres RD k sc) (wt RD lam (l :: v')) [] [] B))
  rw [e, NF.ctxL_dg (pres RD k sc) lam (by simpa using hpre) (by simpa using hpost),
    NF.ctxL_dg (pres RD k sc) lam (by simpa using hpre) (by simpa using hpost)]
  wnf

theorem ctxL_dots_bubRU {S T : List (Letter I)} {pre post : List (LayerData I)}
    {u v' : List (Letter I)} {l : Letter I} (hpre : SChain S pre (u ++ l :: v'))
    (hpost : SChain (u ++ l :: v') post T) (a : ℕ)
    (γ : End ((pres RD k sc).obj (ob RD (wt RD lam v') []))) :
    NF.ctxL (pres RD k sc) lam S T pre u v' post [l] [l]
        (NF.dotsU (pres RD k sc) (wt RD lam v') l a ≫ NF.bubRU (pres RD k sc) (wt RD lam v') l γ) =
      NF.ctxL (pres RD k sc) lam S T (pre ++ List.replicate a (u, .dot l, v')) (u ++ [l]) v' post [] [] γ := by
  have key := hom_ext_dg RD k sc (wt RD lam v') (s := []) (t := [])
    ((NF.ctxL (pres RD k sc) lam S T pre u v' post [l] [l]).comp
      ((Linear.leftComp k _ (NF.dotsU (pres RD k sc) (wt RD lam v') l a)).comp
        (NF.plcL (pres RD k sc) (wt RD lam v') [l] [] [] [])))
    (NF.ctxL (pres RD k sc) lam S T (pre ++ List.replicate a (u, .dot l, v')) (u ++ [l]) v' post [] [])
    (fun G hG => ?_)
  · exact LinearMap.congr_fun key γ
  have e : NF.plcL (pres RD k sc) (wt RD lam v') [l] [] [] [] (NF.dg (pres RD k sc) (wt RD lam v') [] [] G) =
      NF.dg (pres RD k sc) (wt RD lam v') [l] [l] (G.map (whL [l] [])) := NF.plcL_dg (pres RD k sc) (wt RD lam v') [l] [] [] [] G
  have hrep : SChain [l] (List.replicate a ([], .dot l, [])) [l] := SChain.replicate_of (by schain) a
  have hG' : SChain [l] (G.map (whL [l] [])) [l] := by simpa using hG.whisk [l] []
  have hrep' : SChain (u ++ l :: v') (List.replicate a (u, .dot l, v')) (u ++ l :: v') :=
    SChain.replicate_of ⟨by simp, by simp⟩ a
  change NF.ctxL (pres RD k sc) lam S T pre u v' post [l] [l]
      (NF.dotsU (pres RD k sc) (wt RD lam v') l a ≫ NF.plcL (pres RD k sc) (wt RD lam v') [l] [] [] []
        (NF.dg (pres RD k sc) (wt RD lam v') [] [] G)) = _
  rw [e, NF.dotsU, NF.dg_comp hrep hG', NF.ctxL_dg (pres RD k sc) lam (by simpa using hpre) (by simpa using hpost),
    NF.ctxL_dg (pres RD k sc) lam (by simpa using hpre.append hrep') (by simpa using hpost)]
  wnf

variable (M : ℕ)
  (IH : ∀ ls : List (LayerData I), ncc ls ≤ M → CrossFree ls → SChain [] ls [] →
    IsBub RD k sc lam (NF.dg (pres RD k sc) lam [] [] ls))
include IH

/-- **A bubble monomial placed anywhere in a closed crossingless diagram can be moved to the
outer region** (bubble slides across each strand to its right), leaving dots on these strands:
if all closed crossingless diagrams with at most `M` cups and caps lie in the image of `Π_λ`,
then so does every closed crossingless diagram with at most `M` cups and caps with an element
of the image of `Π` inserted in one of its regions. -/
theorem slideOut : ∀ (v u : List (Letter I)) (pre post : List (LayerData I)),
    SChain [] pre (u ++ v) → SChain (u ++ v) post [] → CrossFree pre → CrossFree post →
    ncc pre + ncc post ≤ M → ∀ β : End ((pres RD k sc).obj (ob RD (wt RD lam v) [])),
    IsBub RD k sc (wt RD lam v) β → IsBub RD k sc lam (NF.ctxL (pres RD k sc) lam [] [] pre u v post [] [] β) := by
  intro v
  induction v with
  | nil =>
    intro u pre post hpre hpost hcpre hcpost hn β hβ
    have hpp : SChain [] (pre ++ post) [] := hpre.append hpost
    have key := hom_ext_dg RD k sc (wt RD lam []) (s := []) (t := [])
      (NF.ctxL (pres RD k sc) lam [] [] pre u [] post [] [])
      (Linear.rightComp k _ (NF.dg (pres RD k sc) lam [] [] (pre ++ post))) (fun B hB => ?_)
    · rw [LinearMap.congr_fun key β]
      exact IsBub.comp hβ (IH _ (by simpa using hn) (hcpre.append hcpost) hpp)
    rw [NF.ctxL_dg (pres RD k sc) lam (by simpa using hpre) (by simpa using hpost)]
    change _ = NF.dg (pres RD k sc) lam [] [] B ≫ NF.dg (pres RD k sc) lam [] [] (pre ++ post)
    rw [NF.dg_comp hB hpp]
    have e := dg_closed_left (RD := RD) (k := k) (sc := sc) lam (S := []) (T := []) [] post (s := [])
      (s' := u) [] hB (by simpa using hpre)
    wnf at e
    wnf
    exact e
  | cons l v' ih =>
    intro u pre post hpre hpost hcpre hcpost hn β hβ
    rw [ctxL_cons RD k sc lam hpre hpost]
    have hmem := bubLU_mem_slideSetR_gen (wt RD lam v') l (β := β) hβ
    generalize NF.bubLU (pres RD k sc) (wt RD lam v') l β = f at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, γ, hγ, rfl⟩ := hf
      rw [ctxL_dots_bubRU RD k sc lam hpre hpost]
      have hrep' : SChain (u ++ l :: v') (List.replicate a (u, .dot l, v')) (u ++ l :: v') :=
        SChain.replicate_of ⟨by simp, by simp⟩ a
      exact ih (u ++ [l]) _ post (by simpa using hpre.append hrep') (by simpa using hpost)
        (hcpre.append (crossFree_replicate_dot _ _ _ _)) hcpost (by simpa using hn) γ hγ
    | zero => rw [map_zero]; exact IsBub.zero
    | add x y _ _ hx hy => rw [map_add]; exact IsBub.add hx hy
    | smul r x _ hx => rw [map_smul]; exact IsBub.smul r hx

end SlideOut

/-! ## Sinking the lowest cap -/



section Sink

variable (lam : X)



/-- **Sinking the lowest cap.** Let `K` bound the number of cups and caps of the diagrams
below, and assume that every closed crossingless diagram with at most `K - 2` cups and caps lies
in the image of `Π_λ`. Then every closed crossingless diagram consisting of cup-and-dot layers
`pre`, a block of `m` dots on the left strand of a cap, the cap, and arbitrary crossingless
layers `post`, with at most `K - 1` cups and caps, lies in the image of `Π_λ`. -/
theorem sink (K : ℕ)
    (IH : ∀ ls : List (LayerData I), ncc ls + 2 ≤ K → CrossFree ls → SChain [] ls [] →
      IsBub RD k sc lam (NF.dg (pres RD k sc) lam [] [] ls)) :
    ∀ (pre : List (LayerData I)) (m : ℕ) (u v : List (Letter I)) (l : Letter I)
      (post : List (LayerData I)), CapFree pre → CrossFree pre → CrossFree post →
      ncc pre + ncc post + 2 ≤ K → SChain [] pre (u ++ [l.dual, l] ++ v) →
      SChain (u ++ v) post [] →
      IsBub RD k sc lam (NF.dg (pres RD k sc) lam [] [] (pre ++ List.replicate m (u, .dot l.dual, l :: v) ++
        [(u, .cap l, v)] ++ post)) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro m u v l post _ _ _ _ hpre _
    have := congrArg List.length (hpre : ([] : List (Letter I)) = u ++ [l.dual, l] ++ v)
    simp at this
  | append_singleton pre' y ih =>
    intro m u v l post hcap hcr hcpost hn hpre hpost
    obtain ⟨w, hpre', hy⟩ := SChain.split hpre
    obtain ⟨a, g, b⟩ := y
    obtain ⟨rfl, hW⟩ := hy
    have hW' : a ++ g.cod ++ b = u ++ [l.dual, l] ++ v := hW
    have hcap' : CapFree pre' := fun x hx => hcap x (List.mem_append_left _ hx)
    have hcr' : CrossFree pre' := hcr.of_append_left
    have hgcap : g.isCap = false := hcap _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hgcr : g.isCross = false := hcr _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hn' : ncc pre' + (if g.isCupCap then 1 else 0) + ncc post + 2 ≤ K := by
      simpa [ncc_append] using hn
    cases g with
    | cross ε i j => simp [Shape.isCross] at hgcr
    | cap l' => simp [Shape.isCap] at hgcap
    | dot l' =>
      simp only [Shape.cod_dot] at hW'
      simp only [Shape.isCupCap] at hn'
      rcases pos_dot_cases hW' with ⟨c, rfl, rfl⟩ | ⟨ha, hx, hb⟩ | ⟨ha, hx, hb⟩ | ⟨c, rfl, rfl⟩
      · -- the dot is to the left of the cap
        have hB : SChain (c ++ l.dual :: l :: v)
            (List.replicate m (c, .dot l.dual, l :: v) ++ [(c, .cap l, v)]) (c ++ v) := by
          simpa using sChain_block (u := c) (v := v) (l := l) m
        have e := NF.dg_interchange_one (P := pres RD k sc) (μ := lam) (S := []) (T := []) pre' post
          a [] (.dot l') hB
        have h := ih m (a ++ l' :: c) v l ((a, .dot l', c ++ v) :: post) hcap' hcr'
          (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact hcpost x hx)
          (by simpa [Shape.isCupCap] using hn') (by simpa using hpre') (by
            refine ⟨by simp, ?_⟩
            simpa using hpost)
        lnorm at e h ⊢
        rw [e]; exact h
      · -- the dot is on the left strand of the cap: it joins the block
        subst u l' b
        have h := ih (m + 1) a v l post hcap' hcr' hcpost (by simpa [Shape.isCupCap] using hn')
          (by simpa using hpre') hpost
        rw [List.replicate_succ] at h
        lnorm at h ⊢
        exact h
      · -- the dot is on the right strand of the cap: it moves to the left strand
        subst a l' v
        have h := ih (m + 1) u b l post hcap' hcr' hcpost (by simpa [Shape.isCupCap] using hn')
          (by simpa using hpre') hpost
        have e := NF.dg_step (pres RD k sc) lam (s₀ := []) (t₀ := []) pre' post u b
          (dg_dotR_cap RD k sc (wt RD lam b) l m) (by simpa using hpre')
          (by simpa using hpost) (L := pre' ++ [(u ++ [l.dual], .dot l, b)] ++
            List.replicate m (u, .dot l.dual, l :: b) ++ [(u, .cap l, b)] ++ post)
          (by lnorm) rfl
        rw [e]
        lnorm at h ⊢
        exact h
      · -- the dot is to the right of the cap
        have hA : SChain (u ++ [l.dual, l]) (List.replicate m (u, .dot l.dual, [l]) ++
            [(u, .cap l, [])]) u := by
          simpa using sChain_block (u := u) (v := []) (l := l) m
        have e := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := []) (T := []) pre' post
          hA (B := [(c, .dot l', b)]) (t := c ++ l' :: b) (t' := c ++ l' :: b) ⟨by simp, by simp⟩
        have h := ih m u (c ++ l' :: b) l ((u ++ c, .dot l', b) :: post) hcap' hcr'
          (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact hcpost x hx)
          (by simpa [Shape.isCupCap] using hn') (by simpa using hpre') (by
            refine ⟨by simp, ?_⟩
            simpa using hpost)
        lnorm at e h ⊢
        rw [← e]; exact h
    | cup l' =>
      simp only [Shape.cod_cup] at hW'
      simp only [Shape.isCupCap, ite_true] at hn'
      rcases pos_cup_cases hW' with ⟨c, rfl, rfl⟩ | ⟨hu, hl, hb⟩ | ⟨ha, hx, hl, hb⟩ |
          ⟨ha, hx, hv⟩ | ⟨c, rfl, rfl⟩
      · -- the cup is to the left of the cap
        have hB : SChain (c ++ l.dual :: l :: v)
            (List.replicate m (c, .dot l.dual, l :: v) ++ [(c, .cap l, v)]) (c ++ v) := by
          simpa using sChain_block (u := c) (v := v) (l := l) m
        have e := NF.dg_interchange_one (P := pres RD k sc) (μ := lam) (S := []) (T := []) pre' post
          a [] (.cup l') hB
        have h := ih m (a ++ c) v l ((a, .cup l', c ++ v) :: post) hcap' hcr'
          (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact hcpost x hx)
          (by simp [Shape.isCupCap]; omega) (by simpa using hpre') (by
            refine ⟨by simp, ?_⟩
            simpa using hpost)
        lnorm at e h ⊢
        rw [e]; exact h
      · -- zigzag: the right leg of the cup is the left strand of the cap
        subst u b
        have hl' : l' = l := by
          have := congrArg Letter.dual hl; simpa using this
        subst l
        have e := NF.dg_step (pres RD k sc) lam (s₀ := []) (t₀ := []) pre' post a v
          (dg_zig₁ RD k sc (wt RD lam v) l' m) (by simpa using hpre') (by simpa using hpost)
          (L := pre' ++ [(a, .cup l', l' :: v)] ++
            List.replicate m (a ++ [l'], .dot l'.dual, l' :: v) ++ [(a ++ [l'], .cap l', v)] ++ post)
          (by lnorm) rfl
        have hrep : SChain (a ++ l' :: v) (List.replicate m (a, .dot l', v)) (a ++ l' :: v) :=
          SChain.replicate_of ⟨by simp, by simp⟩ m
        have h := IH (pre' ++ List.replicate m (a, .dot l', v) ++ post)
          (by simp; omega) (hcr'.append (crossFree_replicate_dot _ _ _ _) |>.append hcpost)
          ((hpre'.append (by simpa using hrep)).append (by simpa using hpost))
        lnorm at h e ⊢
        rw [e]; exact h
      · -- the cup creates both strands of the cap: a bubble
        subst u v l'
        have hbub := isBub_bubLs RD k sc (wt RD lam b) l m
        have e := NF.ctxL_dg (pres RD k sc) lam (s₀ := []) (t₀ := []) (pre := pre') (post := post) (u := a)
          (v := b) (s := []) (t := []) (by simpa using hpre') (by simpa using hpost)
          ([([], .cup l.dual, [])] ++ List.replicate m ([], .dot l.dual, [l]) ++ [([], .cap l, [])])
        have h := slideOut RD k sc lam (ncc pre' + ncc post) (fun ls hls hcls hch =>
          IH ls (by omega) hcls hch) b a pre' post (by simpa using hpre') (by simpa using hpost)
          hcr' hcpost le_rfl _ hbub
        rw [e] at h
        lnorm at h ⊢
        exact h
      · -- zigzag: the left leg of the cup is the right strand of the cap
        subst a l' v
        have e := NF.dg_step (pres RD k sc) lam (s₀ := []) (t₀ := []) pre' post u b
          (dg_zig₂ RD k sc (wt RD lam b) l m) (by simpa using hpre') (by simpa using hpost)
          (L := pre' ++ [(u ++ [l.dual], .cup l, b)] ++
            List.replicate m (u, .dot l.dual, l :: l.dual :: b) ++ [(u, .cap l, l.dual :: b)] ++
              post)
          (by lnorm) rfl
        have hrep : SChain (u ++ l.dual :: b) (List.replicate m (u, .dot l.dual, b))
            (u ++ l.dual :: b) := SChain.replicate_of ⟨by simp, by simp⟩ m
        have h := IH (pre' ++ List.replicate m (u, .dot l.dual, b) ++ post)
          (by simp; omega) (hcr'.append (crossFree_replicate_dot _ _ _ _) |>.append hcpost)
          ((hpre'.append (by simpa using hrep)).append (by simpa using hpost))
        lnorm at h e ⊢
        rw [e]; exact h
      · -- the cup is to the right of the cap
        have hA : SChain (u ++ [l.dual, l]) (List.replicate m (u, .dot l.dual, [l]) ++
            [(u, .cap l, [])]) u := by
          simpa using sChain_block (u := u) (v := []) (l := l) m
        have e := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := []) (T := []) pre' post
          hA (B := [(c, .cup l', b)]) (t := c ++ b) (t' := c ++ l' :: l'.dual :: b)
          ⟨by simp, by simp⟩
        have h := ih m u (c ++ b) l ((u ++ c, .cup l', b) :: post) hcap' hcr'
          (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact hcpost x hx)
          (by simp [Shape.isCupCap]; omega) (by simpa using hpre') (by
            refine ⟨by simp, ?_⟩
            simpa using hpost)
        lnorm at e h ⊢
        rw [← e]; exact h

end Sink

/-! ## Closed crossingless diagrams -/

section Main





variable (lam : X)

/-- **KL III Proposition 3.6 for crossingless diagrams** (steps 2 and 3 of KL III's proof): for
every Cartan datum, every closed normal-form diagram of `U` with outer region `λ` whose
layers are dots, cups and caps is a linear combination of bubble monomials, i.e. lies in the
image of `Π_λ → END_U(1_λ)`. -/
theorem crossFree_isBub (ls : List (LayerData I)) (hc : CrossFree ls) :
    IsBub RD k sc lam (NF.dg (pres RD k sc) lam [] [] ls) := by
  induction hn : ncc ls using Nat.strong_induction_on generalizing ls with
  | _ n ihn =>
    by_cases hch : SChain [] ls []
    · by_cases hcap : ∃ x ∈ ls, x.2.1.isCap = true
      · obtain ⟨pre, ⟨u, g, v⟩, post, rfl, hpre, hx⟩ := exists_first_cap hcap
        obtain ⟨l, rfl⟩ := Shape.eq_cap_of_isCap hx
        obtain ⟨w, h₁, h₂⟩ := SChain.split hch
        obtain ⟨hw, h₃⟩ := h₂
        subst hw
        have hcpre : CrossFree pre := hc.of_append_left
        have hcpost : CrossFree post := fun y hy =>
          hc y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
        have hnn : ncc pre + ncc post + 1 = n := by
          rw [← hn]; simp [Shape.isCupCap]; omega
        have := sink RD k sc lam (n + 1) (fun ls' hls' hcls' hch' => ihn (ncc ls') (by omega) ls' hcls' rfl)
          pre 0 u v l post hpre hcpre hcpost (by omega) (by simpa using h₁) (by simpa using h₃)
        simpa using this
      · push Not at hcap
        have : ls = [] := capFree_closed_nil (fun x hx => by simpa using hcap x hx) hc hch
        subst this
        rw [NF.dg_nil]; exact IsBub.id
    · rw [NF.dg_of_not hch]; exact IsBub.zero

/-- **KL III Proposition 3.6 for crossingless diagrams**, for arbitrary diagrams of the presented
2-category: every closed diagram of `U` with outer region `λ` none of whose generators is a
crossing lies in the image of `Π_λ` (any Cartan datum). -/
theorem crossFree_diag_isBub (d : ob RD lam [] ⟶ ob RD lam [])
    (hd : ∀ L ∈ Diagram.layers d, ∀ ε i j ν, L.gen ≠ .gen (.cross ε i j ν)) :
    IsBub RD k sc lam ((pres RD k sc).diag d) := by
  obtain ⟨ls, h, rfl⟩ := exists_mkD RD lam d
  rw [← NF.dg_of h]
  refine crossFree_isBub RD k sc lam ls fun x hx => ?_
  obtain ⟨a, g, b⟩ := x
  cases g with
  | cross ε i j =>
    exact absurd rfl (hd _ (List.mem_map.2 ⟨_, hx, rfl⟩) ε i j (wt RD lam b))
  | _ => rfl

end Main

/-! ## Proposition 3.6 -/

/-- **KL III Proposition 3.6** (label `prop_bubbles_same_orient`): the homomorphism
`Π_λ → HOM_U(1_λ, 1_λ)` of eq. (3.25) is surjective. -/
def Prop36 (lam : X) : Prop := Function.Surjective (bubMap RD k sc lam)

/-- Proposition 3.6 holds iff every closed normal-form diagram with outer region `λ` lies in the
image of `Π_λ`. -/
theorem prop36_iff_dg (lam : X) :
    Prop36 RD k sc lam ↔ ∀ ls, SChain [] ls [] → IsBub RD k sc lam (NF.dg (pres RD k sc) lam [] [] ls) := by
  constructor
  · intro h ls _
    obtain ⟨p, hp⟩ := h (EndOne.of (NF.dg (pres RD k sc) lam [] [] ls))
    exact ⟨p, hp⟩
  · intro h y
    have hy : IsBub RD k sc lam y.val := by
      have hmem := mem_span_dg RD k sc lam (s := []) (t := []) y.val
      rw [isBub_iff_mem_bubSubmodule]
      refine Submodule.span_le.mpr ?_ hmem
      rintro _ ⟨ls, hls, rfl⟩
      exact h ls hls
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, hp⟩

/-- Proposition 3.6 holds iff every closed diagram lies in the image of `Π_λ`; by
`crossFree_isBub` it suffices to reduce closed diagrams with crossings to closed crossingless
diagrams modulo the image of `Π_λ` (step 1 of KL III's proof). -/
theorem prop36_of_reduction (lam : X)
    (hred : ∀ ls, SChain [] ls [] → NF.dg (pres RD k sc) lam [] [] ls ∈
      Submodule.span k {x | ∃ ls', CrossFree ls' ∧ x = NF.dg (pres RD k sc) lam [] [] ls'}) :
    Prop36 RD k sc lam := by
  rw [prop36_iff_dg]
  intro ls hls
  rw [isBub_iff_mem_bubSubmodule]
  refine Submodule.span_le.mpr ?_ (hred ls hls)
  rintro _ ⟨ls', hls', rfl⟩
  exact crossFree_isBub RD k sc lam ls' hls'

end Categorification.KL3.Diagram.CLQ
