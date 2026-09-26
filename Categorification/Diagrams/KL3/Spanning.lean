/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningBasic

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

The bubble slides of KL III are stated for simply-laced Cartan data; accordingly the main
theorem assumes `SimplyLaced C`.

## Main results

* `slideOut`: an element of the image of `Π` placed anywhere in a diagram can be moved to the
  outer region, leaving dots behind.
* `crossFree_isBub`: **closed crossingless diagrams lie in the image of `Π_λ`** (KL III
  Proposition 3.6, steps 2 and 3 of its proof).
* `Prop36`, `prop36_iff_dg`: Proposition 3.6 (surjectivity of `Π_λ → END_U(1_λ)`) and its
  equivalence with the statement that every closed normal-form diagram lies in the image.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Crossingless diagrams -/

namespace Shape

/-- The shape is a crossing. -/
def isCross : Shape I → Bool
  | .cross _ _ _ => true
  | _ => false

/-- The shape is a cap. -/
def isCap : Shape I → Bool
  | .cap _ => true
  | _ => false

/-- The shape is a cup or a cap. -/
def isCupCap : Shape I → Bool
  | .cup _ => true
  | .cap _ => true
  | _ => false

end Shape

/-- A list of layers without crossings. -/
def CrossFree (ls : List (LayerData I)) : Prop := ∀ x ∈ ls, x.2.1.isCross = false

/-- A list of layers without caps. -/
def CapFree (ls : List (LayerData I)) : Prop := ∀ x ∈ ls, x.2.1.isCap = false

/-- The number of cups and caps in a list of layers. -/
def ncc (ls : List (LayerData I)) : ℕ := ls.countP fun x => x.2.1.isCupCap

@[simp] theorem ncc_nil : ncc ([] : List (LayerData I)) = 0 := rfl

@[simp] theorem ncc_append (a b : List (LayerData I)) : ncc (a ++ b) = ncc a + ncc b :=
  List.countP_append

@[simp] theorem ncc_cons (x : LayerData I) (ls : List (LayerData I)) :
    ncc (x :: ls) = ncc ls + if x.2.1.isCupCap then 1 else 0 := by
  simp [ncc, List.countP_cons]

@[simp] theorem ncc_replicate_dot (m : ℕ) (a b : List (Letter I)) (l : Letter I) :
    ncc (List.replicate m (a, Shape.dot l, b)) = 0 := by
  simp [ncc, List.countP_replicate, Shape.isCupCap]

theorem CrossFree.append {a b : List (LayerData I)} (ha : CrossFree a) (hb : CrossFree b) :
    CrossFree (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem CrossFree.of_append_left {a b : List (LayerData I)} (h : CrossFree (a ++ b)) :
    CrossFree a := fun x hx => h x (List.mem_append_left _ hx)

theorem CrossFree.of_append_right {a b : List (LayerData I)} (h : CrossFree (a ++ b)) :
    CrossFree b := fun x hx => h x (List.mem_append_right _ hx)

theorem crossFree_replicate_dot (m : ℕ) (a b : List (Letter I)) (l : Letter I) :
    CrossFree (List.replicate m (a, Shape.dot l, b)) := by
  intro x hx
  rw [List.eq_of_mem_replicate hx]; rfl

theorem crossFree_singleton {x : LayerData I} (h : x.2.1.isCross = false) : CrossFree [x] := by
  intro y hy; rw [List.mem_singleton.1 hy]; exact h

/-! ## Positions of a generator relative to a cap -/

/-- The positions of a one-strand generator relative to a pair of adjacent strands `y z`: to
the left, on `y`, on `z`, or to the right. -/
theorem pos_dot_cases {α : Type*} {a b u v : List α} {x y z : α} (h : a ++ [x] ++ b = u ++ [y, z] ++ v) :
    (∃ c, u = a ++ x :: c ∧ b = c ++ y :: z :: v) ∨ (a = u ∧ x = y ∧ b = z :: v) ∨
      (a = u ++ [y] ∧ x = z ∧ b = v) ∨ (∃ c, a = u ++ y :: z :: c ∧ v = c ++ x :: b) := by
  simp only [List.append_assoc, List.singleton_append, List.cons_append] at h
  rcases List.append_eq_append_iff.1 h with ⟨as, hu, hb⟩ | ⟨bs, ha, hv⟩
  · rcases as with _ | ⟨x', c⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at hu hb
      exact Or.inr (Or.inl ⟨hu.symm, hb.1, hb.2⟩)
    · simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact Or.inl ⟨c, hu, rfl⟩
  · rcases bs with _ | ⟨y', _ | ⟨z', c⟩⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at ha hv
      exact Or.inr (Or.inl ⟨ha, hv.1.symm, hv.2.symm⟩)
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inl ⟨ha, rfl, rfl⟩))
    · simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inr ⟨c, ha, rfl⟩))

/-- The positions of a cup (creating the strands `x x'`) relative to a pair of adjacent strands
`y z`: to the left, sharing its right leg with `y`, equal, sharing its left leg with `z`, or to
the right. -/
theorem pos_cup_cases {α : Type*} {a b u v : List α} {x x' y z : α}
    (h : a ++ [x, x'] ++ b = u ++ [y, z] ++ v) :
    (∃ c, u = a ++ x :: x' :: c ∧ b = c ++ y :: z :: v) ∨ (u = a ++ [x] ∧ x' = y ∧ b = z :: v) ∨
      (a = u ∧ x = y ∧ x' = z ∧ b = v) ∨ (a = u ++ [y] ∧ x = z ∧ v = x' :: b) ∨
      (∃ c, a = u ++ y :: z :: c ∧ v = c ++ x :: x' :: b) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  rcases List.append_eq_append_iff.1 h with ⟨as, hu, hb⟩ | ⟨bs, ha, hv⟩
  · rcases as with _ | ⟨p, _ | ⟨q, c⟩⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at hu hb
      exact Or.inr (Or.inr (Or.inl ⟨hu.symm, hb.1, hb.2.1, hb.2.2⟩))
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      exact Or.inr (Or.inl ⟨hu, rfl, rfl⟩)
    · simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      exact Or.inl ⟨c, hu, rfl⟩
  · rcases bs with _ | ⟨p, _ | ⟨q, c⟩⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at ha hv
      exact Or.inr (Or.inr (Or.inl ⟨ha, hv.1.symm, hv.2.1.symm, hv.2.2.symm⟩))
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, rfl, rfl⟩)))
    · simp only [List.cons_append, List.cons.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, ha, rfl⟩)))

/-! ## Local moves -/

section Local

variable (ν : X)

/-- A dot on the right strand of a cap below a block of dots on its left strand joins the block
(cyclicity of dots, KL III (3.3)). -/
theorem dg_dotR_cap (l : Letter I) (m : ℕ) :
    dg RD k ν [l.dual, l] [] ([([l.dual], .dot l, [])] ++
        List.replicate m ([], .dot l.dual, [l]) ++ [([], .cap l, [])]) =
      dg RD k ν [l.dual, l] [] (List.replicate (m + 1) ([], .dot l.dual, [l]) ++
        [([], .cap l, [])]) := by
  obtain ⟨b, i⟩ := l
  cases b
  · -- `l = F_i`, cap `E_i F_i → 1`
    show dg RD k ν [up i, dn i] [] ([([up i], .dot (dn i), [])] ++
        List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]) =
      dg RD k ν [up i, dn i] [] (List.replicate (m + 1) ([], .dot (up i), [dn i]) ++
        [([], .cap (dn i), [])])
    dstep [] [([], .cap (dn i), [])] [] [] (dg_swap_dots RD k ν [] [] [] (up i) (dn i) 1 m)
    dstep (List.replicate m ([], .dot (up i), [dn i])) [] [] [] (dg_dot_cap_dn RD k ν i)
    simp [List.replicate_succ']
  · -- `l = E_i`, cap `F_i E_i → 1`
    show dg RD k ν [dn i, up i] [] ([([dn i], .dot (up i), [])] ++
        List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]) =
      dg RD k ν [dn i, up i] [] (List.replicate (m + 1) ([], .dot (dn i), [up i]) ++
        [([], .cap (up i), [])])
    dstep [] [([], .cap (up i), [])] [] [] (dg_swap_dots RD k ν [] [] [] (dn i) (up i) 1 m)
    dstep (List.replicate m ([], .dot (dn i), [up i])) [] [] [] (dg_dot_cap_up RD k ν i).symm
    simp [List.replicate_succ']

/-- The first zigzag with dots on its middle segment is a strand with dots. -/
theorem dg_zig₁ (l : Letter I) (m : ℕ) :
    dg RD k ν [l] [l] ([([], .cup l, [l])] ++ List.replicate m ([l], .dot l.dual, [l]) ++
        [([l], .cap l, [])]) =
      dg RD k ν [l] [l] (List.replicate m ([], .dot l, [])) := by
  obtain ⟨b, i⟩ := l
  cases b
  · show dg RD k ν [dn i] [dn i] ([([], .cup (dn i), [dn i])] ++
        List.replicate m ([dn i], .dot (up i), [dn i]) ++ [([dn i], .cap (dn i), [])]) =
      dg RD k ν [dn i] [dn i] (List.replicate m ([], .dot (dn i), []))
    dstep [] [([dn i], .cap (dn i), [])] [] [dn i] (dg_dots_cupDn RD k i (wt RD ν [dn i]) m)
    dstep [([], .cup (dn i), [dn i])] [] [] []
      (dg_swap_rep' RD k ν [] [] [] (.cap (dn i)) (.dot (dn i)) rfl m)
    dstep [] (List.replicate m ([], .dot (dn i), [])) [] [] (dg_zigL' RD k ν (dn i))
    simp
  · show dg RD k ν [up i] [up i] ([([], .cup (up i), [up i])] ++
        List.replicate m ([up i], .dot (dn i), [up i]) ++ [([up i], .cap (up i), [])]) =
      dg RD k ν [up i] [up i] (List.replicate m ([], .dot (up i), []))
    dstep [] [([up i], .cap (up i), [])] [] [up i] (dg_dots_cupUp RD k i (wt RD ν [up i]) m)
    dstep [([], .cup (up i), [up i])] [] [] []
      (dg_swap_rep' RD k ν [] [] [] (.cap (up i)) (.dot (up i)) rfl m)
    dstep [] (List.replicate m ([], .dot (up i), [])) [] [] (dg_zigL' RD k ν (up i))
    simp

/-- The second zigzag, with dots on the strand below it, is a strand with dots. -/
theorem dg_zig₂ (l : Letter I) (m : ℕ) :
    dg RD k ν [l.dual] [l.dual] ([([l.dual], .cup l, [])] ++
        List.replicate m ([], .dot l.dual, [l, l.dual]) ++ [([], .cap l, [l.dual])]) =
      dg RD k ν [l.dual] [l.dual] (List.replicate m ([], .dot l.dual, [])) := by
  dstep [] [([], .cap l, [l.dual])] [] []
    (dg_swap_rep' RD k ν [] [] [] (.cup l) (.dot l.dual) rfl m).symm
  dstep (List.replicate m ([], .dot l.dual, [])) [] [] [] (dg_zigR' RD k ν l)
  simp

/-- A cup, dots on its left leg and a cap form a dotted bubble, which lies in the image of
`Π_ν`. -/
theorem isBub_bubLs (l : Letter I) (m : ℕ) :
    IsBub RD k ν (dg RD k ν [] [] ([([], .cup l.dual, [])] ++
      List.replicate m ([], .dot l.dual, [l]) ++ [([], .cap l, [])])) := by
  obtain ⟨b, i⟩ := l
  cases b
  · have e : dg RD k ν [] [] ([([], .cup (up i), [])] ++
        List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]) =
        dg RD k ν [] [] (cwLs i m) := by
      rw [cwLs, dg_cw_dots]
    exact e ▸ dg_cwLs_isBub i m
  · have e : dg RD k ν [] [] ([([], .cup (dn i), [])] ++
        List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]) =
        dg RD k ν [] [] (ccwLs i m) := by
      rw [ccwLs]
      dstep [([], .cup (dn i), [])] [] [] [] (dg_dots_cap_up RD k ν i m)
      simp
    exact e ▸ dg_ccwLs_isBub i m

end Local

/-! ## Moving a bubble monomial to the outer region -/

section SlideOut

variable (lam : X)

theorem ctxL_cons {S T : List (Letter I)} {pre post : List (LayerData I)} {u v' : List (Letter I)}
    {l : Letter I} (hpre : SChain S pre (u ++ l :: v')) (hpost : SChain (u ++ l :: v') post T)
    (β : End ((pres RD k).obj (ob RD (wt RD lam (l :: v')) []))) :
    ctxL RD k lam S T pre u (l :: v') post [] [] β =
      ctxL RD k lam S T pre u v' post [l] [l] (bubLU RD k (wt RD lam v') l β) := by
  have key := hom_ext_dg RD k (wt RD lam (l :: v')) (s := []) (t := [])
    (ctxL RD k lam S T pre u (l :: v') post [] [])
    ((ctxL RD k lam S T pre u v' post [l] [l]).comp (plcL RD k (wt RD lam v') [] [l] [] []))
    (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  have e : plcL RD k (wt RD lam v') [] [l] [] [] (dg RD k (wt RD lam (l :: v')) [] [] B) =
      dg RD k (wt RD lam v') [l] [l] (B.map (whL [] [l])) := plcL_dg RD k (wt RD lam v') [] [l] [] [] B
  change ctxL RD k lam S T pre u (l :: v') post [] [] (dg RD k (wt RD lam (l :: v')) [] [] B) =
    ctxL RD k lam S T pre u v' post [l] [l]
      (plcL RD k (wt RD lam v') [] [l] [] [] (dg RD k (wt RD lam (l :: v')) [] [] B))
  rw [e, ctxL_dg RD k lam (by simpa using hpre) (by simpa using hpost),
    ctxL_dg RD k lam (by simpa using hpre) (by simpa using hpost)]
  wnf

theorem ctxL_dots_bubRU {S T : List (Letter I)} {pre post : List (LayerData I)}
    {u v' : List (Letter I)} {l : Letter I} (hpre : SChain S pre (u ++ l :: v'))
    (hpost : SChain (u ++ l :: v') post T) (a : ℕ)
    (γ : End ((pres RD k).obj (ob RD (wt RD lam v') []))) :
    ctxL RD k lam S T pre u v' post [l] [l]
        (dotsU RD k (wt RD lam v') l a ≫ bubRU RD k (wt RD lam v') l γ) =
      ctxL RD k lam S T (pre ++ List.replicate a (u, .dot l, v')) (u ++ [l]) v' post [] [] γ := by
  have key := hom_ext_dg RD k (wt RD lam v') (s := []) (t := [])
    ((ctxL RD k lam S T pre u v' post [l] [l]).comp
      ((Linear.leftComp k _ (dotsU RD k (wt RD lam v') l a)).comp
        (plcL RD k (wt RD lam v') [l] [] [] [])))
    (ctxL RD k lam S T (pre ++ List.replicate a (u, .dot l, v')) (u ++ [l]) v' post [] [])
    (fun G hG => ?_)
  · exact LinearMap.congr_fun key γ
  have e : plcL RD k (wt RD lam v') [l] [] [] [] (dg RD k (wt RD lam v') [] [] G) =
      dg RD k (wt RD lam v') [l] [l] (G.map (whL [l] [])) := plcL_dg RD k (wt RD lam v') [l] [] [] [] G
  have hrep : SChain [l] (List.replicate a ([], .dot l, [])) [l] := SChain.replicate_of (by schain) a
  have hG' : SChain [l] (G.map (whL [l] [])) [l] := by simpa using hG.whisk [l] []
  have hrep' : SChain (u ++ l :: v') (List.replicate a (u, .dot l, v')) (u ++ l :: v') :=
    SChain.replicate_of ⟨by simp, by simp⟩ a
  change ctxL RD k lam S T pre u v' post [l] [l]
      (dotsU RD k (wt RD lam v') l a ≫ plcL RD k (wt RD lam v') [l] [] [] []
        (dg RD k (wt RD lam v') [] [] G)) = _
  rw [e, dotsU, dg_comp hrep hG', ctxL_dg RD k lam (by simpa using hpre) (by simpa using hpost),
    ctxL_dg RD k lam (by simpa using hpre.append hrep') (by simpa using hpost)]
  wnf

variable (hSL : SimplyLaced C) (M : ℕ)
  (IH : ∀ ls : List (LayerData I), ncc ls ≤ M → CrossFree ls → SChain [] ls [] →
    IsBub RD k lam (dg RD k lam [] [] ls))
include hSL IH

/-- **A bubble monomial placed anywhere in a closed crossingless diagram can be moved to the
outer region** (bubble slides across each strand to its right), leaving dots on these strands:
if all closed crossingless diagrams with at most `M` cups and caps lie in the image of `Π_λ`,
then so does every closed crossingless diagram with at most `M` cups and caps with an element
of the image of `Π` inserted in one of its regions. -/
theorem slideOut : ∀ (v u : List (Letter I)) (pre post : List (LayerData I)),
    SChain [] pre (u ++ v) → SChain (u ++ v) post [] → CrossFree pre → CrossFree post →
    ncc pre + ncc post ≤ M → ∀ β : End ((pres RD k).obj (ob RD (wt RD lam v) [])),
    IsBub RD k (wt RD lam v) β → IsBub RD k lam (ctxL RD k lam [] [] pre u v post [] [] β) := by
  intro v
  induction v with
  | nil =>
    intro u pre post hpre hpost hcpre hcpost hn β hβ
    have hpp : SChain [] (pre ++ post) [] := hpre.append hpost
    have key := hom_ext_dg RD k (wt RD lam []) (s := []) (t := [])
      (ctxL RD k lam [] [] pre u [] post [] [])
      (Linear.rightComp k _ (dg RD k lam [] [] (pre ++ post))) (fun B hB => ?_)
    · rw [LinearMap.congr_fun key β]
      exact IsBub.comp hβ (IH _ (by simpa using hn) (hcpre.append hcpost) hpp)
    rw [ctxL_dg RD k lam (by simpa using hpre) (by simpa using hpost)]
    change _ = dg RD k lam [] [] B ≫ dg RD k lam [] [] (pre ++ post)
    rw [dg_comp hB hpp]
    have e := dg_closed_left (RD := RD) (k := k) lam (S := []) (T := []) [] post (s := [])
      (s' := u) [] hB (by simpa using hpre)
    wnf at e
    wnf
    exact e
  | cons l v' ih =>
    intro u pre post hpre hpost hcpre hcpost hn β hβ
    rw [ctxL_cons RD k lam hpre hpost]
    have hmem := bubLU_mem_slideSetR hSL (wt RD lam v') l (β := β) hβ
    generalize bubLU RD k (wt RD lam v') l β = f at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, γ, hγ, rfl⟩ := hf
      rw [ctxL_dots_bubRU RD k lam hpre hpost]
      have hrep' : SChain (u ++ l :: v') (List.replicate a (u, .dot l, v')) (u ++ l :: v') :=
        SChain.replicate_of ⟨by simp, by simp⟩ a
      exact ih (u ++ [l]) _ post (by simpa using hpre.append hrep') (by simpa using hpost)
        (hcpre.append (crossFree_replicate_dot _ _ _ _)) hcpost (by simpa using hn) γ hγ
    | zero => rw [map_zero]; exact IsBub.zero
    | add x y _ _ hx hy => rw [map_add]; exact IsBub.add hx hy
    | smul r x _ hx => rw [map_smul]; exact IsBub.smul r hx

end SlideOut

/-! ## Sinking the lowest cap -/

theorem sChain_block {u v : List (Letter I)} {l : Letter I} (m : ℕ) :
    SChain (u ++ [l.dual, l] ++ v) (List.replicate m (u, .dot l.dual, l :: v) ++ [(u, .cap l, v)])
      (u ++ v) :=
  (SChain.replicate_of ⟨by simp, by simp⟩ m).append ⟨by simp, by simp⟩


section Sink

variable (hSL : SimplyLaced C) (lam : X)
include hSL

/-- Normalization of lists of layers in the sinking argument. -/
syntax "lnorm" (ppSpace Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| lnorm $[$loc]?) => `(tactic| simp only [List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append, List.append_nil, List.map_append, List.map_cons,
      List.map_nil, List.map_replicate, whL_mk, Letter.dual_dual, Shape.dom_dot, Shape.cod_dot,
      Shape.dom_cup, Shape.cod_cup, Shape.dom_cap, Shape.cod_cap] $[$loc]?)

/-- **Sinking the lowest cap.** Let `K` bound the number of cups and caps of the diagrams
below, and assume that every closed crossingless diagram with at most `K - 2` cups and caps lies
in the image of `Π_λ`. Then every closed crossingless diagram consisting of cup-and-dot layers
`pre`, a block of `m` dots on the left strand of a cap, the cap, and arbitrary crossingless
layers `post`, with at most `K - 1` cups and caps, lies in the image of `Π_λ`. -/
theorem sink (K : ℕ)
    (IH : ∀ ls : List (LayerData I), ncc ls + 2 ≤ K → CrossFree ls → SChain [] ls [] →
      IsBub RD k lam (dg RD k lam [] [] ls)) :
    ∀ (pre : List (LayerData I)) (m : ℕ) (u v : List (Letter I)) (l : Letter I)
      (post : List (LayerData I)), CapFree pre → CrossFree pre → CrossFree post →
      ncc pre + ncc post + 2 ≤ K → SChain [] pre (u ++ [l.dual, l] ++ v) →
      SChain (u ++ v) post [] →
      IsBub RD k lam (dg RD k lam [] [] (pre ++ List.replicate m (u, .dot l.dual, l :: v) ++
        [(u, .cap l, v)] ++ post)) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro m u v l post _ _ _ _ hpre _
    have := congrArg List.length (hpre : ([] : List (Letter I)) = u ++ [l.dual, l] ++ v)
    simp at this; omega
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
      simp only [Shape.isCupCap, if_false, add_zero] at hn'
      rcases pos_dot_cases hW' with ⟨c, rfl, rfl⟩ | ⟨ha, hx, hb⟩ | ⟨ha, hx, hb⟩ | ⟨c, rfl, rfl⟩
      · -- the dot is to the left of the cap
        have hB : SChain (c ++ l.dual :: l :: v)
            (List.replicate m (c, .dot l.dual, l :: v) ++ [(c, .cap l, v)]) (c ++ v) := by
          simpa using sChain_block (u := c) (v := v) (l := l) m
        have e := dg_interchange_one (RD := RD) (k := k) (μ := lam) (S := []) (T := []) pre' post
          a [] (.dot l') hB
        have h := ih m (a ++ l' :: c) v l ((a, .dot l', c ++ v) :: post) hcap' hcr'
          (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact hcpost x hx)
          (by simpa using hn') (by simpa using hpre') (by
            refine ⟨by simp, ?_⟩
            simpa using hpost)
        lnorm at e h ⊢
        rw [e]; exact h
      · -- the dot is on the left strand of the cap: it joins the block
        subst u l' b
        have h := ih (m + 1) a v l post hcap' hcr' hcpost (by simpa using hn')
          (by simpa using hpre') hpost
        rw [List.replicate_succ] at h
        lnorm at h ⊢
        exact h
      · -- the dot is on the right strand of the cap: it moves to the left strand
        subst a l' v
        have h := ih (m + 1) u b l post hcap' hcr' hcpost (by simpa using hn')
          (by simpa using hpre') hpost
        have e := dg_step RD k lam (s₀ := []) (t₀ := []) pre' post u b
          (dg_dotR_cap RD k (wt RD lam b) l m) (by simpa using hpre')
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
        have e := dg_interchange (RD := RD) (k := k) (μ := lam) (S := []) (T := []) pre' post
          hA (B := [(c, .dot l', b)]) (t := c ++ l' :: b) (t' := c ++ l' :: b) ⟨by simp, by simp⟩
        have h := ih m u (c ++ l' :: b) l ((u ++ c, .dot l', b) :: post) hcap' hcr'
          (by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact hcpost x hx)
          (by simpa using hn') (by simpa using hpre') (by
            refine ⟨by simp, ?_⟩
            simpa using hpost)
        lnorm at e h ⊢
        rw [← e]; exact h
    | cup l' =>
      simp only [Shape.cod_cup] at hW'
      simp only [Shape.isCupCap, if_true] at hn'
      rcases pos_cup_cases hW' with ⟨c, rfl, rfl⟩ | ⟨hu, hl, hb⟩ | ⟨ha, hx, hl, hb⟩ |
          ⟨ha, hx, hv⟩ | ⟨c, rfl, rfl⟩
      · -- the cup is to the left of the cap
        have hB : SChain (c ++ l.dual :: l :: v)
            (List.replicate m (c, .dot l.dual, l :: v) ++ [(c, .cap l, v)]) (c ++ v) := by
          simpa using sChain_block (u := c) (v := v) (l := l) m
        have e := dg_interchange_one (RD := RD) (k := k) (μ := lam) (S := []) (T := []) pre' post
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
        have e := dg_step RD k lam (s₀ := []) (t₀ := []) pre' post a v
          (dg_zig₁ RD k (wt RD lam v) l' m) (by simpa using hpre') (by simpa using hpost)
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
        have hbub := isBub_bubLs RD k (wt RD lam b) l m
        have e := ctxL_dg RD k lam (s₀ := []) (t₀ := []) (pre := pre') (post := post) (u := a)
          (v := b) (s := []) (t := []) (by simpa using hpre') (by simpa using hpost)
          ([([], .cup l.dual, [])] ++ List.replicate m ([], .dot l.dual, [l]) ++ [([], .cap l, [])])
        have h := slideOut RD k lam hSL (ncc pre' + ncc post) (fun ls hls hcls hch =>
          IH ls (by omega) hcls hch) b a pre' post (by simpa using hpre') (by simpa using hpost)
          hcr' hcpost le_rfl _ hbub
        rw [e] at h
        lnorm at h ⊢
        exact h
      · -- zigzag: the left leg of the cup is the right strand of the cap
        subst a l' v
        have e := dg_step RD k lam (s₀ := []) (t₀ := []) pre' post u b
          (dg_zig₂ RD k (wt RD lam b) l m) (by simpa using hpre') (by simpa using hpost)
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
        have e := dg_interchange (RD := RD) (k := k) (μ := lam) (S := []) (T := []) pre' post
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

theorem capFree_length {s t : List (Letter I)} {ls : List (LayerData I)} (hcap : CapFree ls)
    (hcr : CrossFree ls) (h : SChain s ls t) : t.length = s.length + 2 * ncc ls := by
  induction ls generalizing s with
  | nil => cases h; simp
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    have hx1 : x.2.1.isCap = false := hcap x List.mem_cons_self
    have hx2 : x.2.1.isCross = false := hcr x List.mem_cons_self
    rw [ih (fun y hy => hcap y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcr y (List.mem_cons_of_mem _ hy)) h, ncc_cons]
    obtain ⟨a, g, b⟩ := x
    cases g <;> simp_all [Shape.isCap, Shape.isCross, Shape.isCupCap]
    omega

theorem capFree_closed_nil {ls : List (LayerData I)} (hcap : CapFree ls) (hcr : CrossFree ls)
    (h : SChain [] ls []) : ls = [] := by
  have hl := capFree_length hcap hcr h
  simp only [List.length_nil, zero_add] at hl
  cases ls with
  | nil => rfl
  | cons x ls =>
    exfalso
    obtain ⟨hx, -⟩ := h
    obtain ⟨a, g, b⟩ := x
    have hx1 : g.isCap = false := hcap _ List.mem_cons_self
    have hx2 : g.isCross = false := hcr _ List.mem_cons_self
    rw [ncc_cons] at hl
    cases g with
    | dot l' => have := congrArg List.length hx; simp at this; omega
    | cross ε i j => simp [Shape.isCross] at hx2
    | cup l' => simp [Shape.isCupCap] at hl
    | cap l' => simp [Shape.isCap] at hx1

theorem exists_first_cap {ls : List (LayerData I)} (h : ∃ x ∈ ls, x.2.1.isCap = true) :
    ∃ pre x post, ls = pre ++ x :: post ∧ CapFree pre ∧ x.2.1.isCap = true := by
  induction ls with
  | nil => simp at h
  | cons y ls ih =>
    by_cases hy : y.2.1.isCap = true
    · exact ⟨[], y, ls, rfl, fun _ h => by simp at h, hy⟩
    · obtain ⟨x, hx, hx'⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hx' hy
      · obtain ⟨pre, x, post, rfl, hpre, hcx⟩ := ih ⟨x, hx, hx'⟩
        refine ⟨y :: pre, x, post, rfl, fun z hz => ?_, hcx⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · simpa using hy
        · exact hpre z hz

theorem Shape.eq_cap_of_isCap {g : Shape I} (h : g.isCap = true) : ∃ l, g = .cap l := by
  cases g <;> simp_all [Shape.isCap]

variable (hSL : SimplyLaced C) (lam : X)
include hSL

/-- **KL III Proposition 3.6 for crossingless diagrams** (steps 2 and 3 of KL III's proof): for a
simply-laced Cartan datum, every closed normal-form diagram of `U` with outer region `λ` whose
layers are dots, cups and caps is a linear combination of bubble monomials, i.e. lies in the
image of `Π_λ → END_U(1_λ)`. -/
theorem crossFree_isBub (ls : List (LayerData I)) (hc : CrossFree ls) :
    IsBub RD k lam (dg RD k lam [] [] ls) := by
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
        have := sink RD k hSL lam (n + 1) (fun ls' hls' hcls' hch' => ihn (ncc ls') (by omega) ls' hcls' rfl)
          pre 0 u v l post hpre hcpre hcpost (by omega) (by simpa using h₁) (by simpa using h₃)
        simpa using this
      · push_neg at hcap
        have : ls = [] := capFree_closed_nil (fun x hx => by simpa using hcap x hx) hc hch
        subst this
        rw [dg_nil]; exact IsBub.id
    · rw [dg_of_not hch]; exact IsBub.zero

/-- **KL III Proposition 3.6 for crossingless diagrams**, for arbitrary diagrams of the presented
2-category: every closed diagram of `U` with outer region `λ` none of whose generators is a
crossing lies in the image of `Π_λ` (simply-laced Cartan data). -/
theorem crossFree_diag_isBub (d : ob RD lam [] ⟶ ob RD lam [])
    (hd : ∀ L ∈ Diagram.layers d, ∀ ε i j ν, L.gen ≠ .gen (.cross ε i j ν)) :
    IsBub RD k lam ((pres RD k).diag d) := by
  obtain ⟨ls, h, rfl⟩ := exists_mkD RD lam d
  rw [← dg_of h]
  refine crossFree_isBub RD k hSL lam ls fun x hx => ?_
  obtain ⟨a, g, b⟩ := x
  cases g with
  | cross ε i j =>
    exact absurd rfl (hd _ (List.mem_map.2 ⟨_, hx, rfl⟩) ε i j (wt RD lam b))
  | _ => rfl

end Main

/-! ## Proposition 3.6 -/

/-- **KL III Proposition 3.6** (label `prop_bubbles_same_orient`): the homomorphism
`Π_λ → HOM_U(1_λ, 1_λ)` of eq. (3.25) is surjective. -/
def Prop36 (lam : X) : Prop := Function.Surjective (bubMap RD k lam)

/-- Proposition 3.6 holds iff every closed normal-form diagram with outer region `λ` lies in the
image of `Π_λ`. -/
theorem prop36_iff_dg (lam : X) :
    Prop36 RD k lam ↔ ∀ ls, SChain [] ls [] → IsBub RD k lam (dg RD k lam [] [] ls) := by
  constructor
  · intro h ls _
    obtain ⟨p, hp⟩ := h (EndOne.of (dg RD k lam [] [] ls))
    exact ⟨p, hp⟩
  · intro h y
    have hy : IsBub RD k lam y.val := by
      have hmem := mem_span_dg RD k lam (s := []) (t := []) y.val
      rw [isBub_iff_mem_bubSubmodule]
      refine Submodule.span_le.mpr ?_ hmem
      rintro _ ⟨ls, hls, rfl⟩
      exact h ls hls
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, hp⟩

/-- Proposition 3.6 holds iff every closed diagram lies in the image of `Π_λ`; by
`crossFree_isBub` it suffices to reduce closed diagrams with crossings to closed crossingless
diagrams modulo the image of `Π_λ` (step 1 of KL III's proof). -/
theorem prop36_of_reduction (hSL : SimplyLaced C) (lam : X)
    (hred : ∀ ls, SChain [] ls [] → dg RD k lam [] [] ls ∈
      Submodule.span k {x | ∃ ls', CrossFree ls' ∧ x = dg RD k lam [] [] ls'}) :
    Prop36 RD k lam := by
  rw [prop36_iff_dg]
  intro ls hls
  rw [isBub_iff_mem_bubSubmodule]
  refine Submodule.span_le.mpr ?_ (hred ls hls)
  rintro _ ⟨ls', hls', rfl⟩
  exact crossFree_isBub RD k hSL lam ls' hls'

end Categorification.KL3.Diagram
