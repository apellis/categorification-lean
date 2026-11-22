/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Traces
import Categorification.Diagrams.KL3.MarkovLeft

/-!
# The left Markov lemma: closing the first strand of an upward diagram

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1
(Proposition 3.6) and §3.2.2 (Lemma 3.9); TeX locators `sources/klr/kl3/0807.3250v1.txt`,
lines 1690–1790.

The mirror image of `Categorification.Diagrams.KL3.Markov`: the first strand `E_j` of an upward
diagram is closed on its left by the cup `1 → F_j E_j` and the cap `F_j E_j → 1`
(`ptrFirst`). The upward diagram is written in the normal form of KL I, Theorem 2.5, for the
reflected canonical words (`canWordL`: the canonical word of `w₀ w w₀` with the positions
reflected), whose first descending run moves one strand to the first position; the other
crossings leave the closure, dots on the closed strand move around it, and what remains is a
left curl with dots on its loop (`curlL_mem_slideSetL`, from the left curl relation) or a
dotted counterclockwise bubble. The bubbles produced on the left slide to the far right
(`slideOutUp`). Result: `ptrFirst_mem_upSpan`, the left partial trace preserves `upSpan`.

## Main results

* `TypeA` reflection: `wordProd_reflW`, `isReduced_reflW`, `canWordL`.
* `curlL_mem_slideSetL`: the left curl with dots on its loop is a combination of bubble
  monomials to the left times dots.
* `ptrFirst_upward_mem_upSpan`, `ptrFirst_mem_upSpan`: **the left Markov lemma**.
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

/-! ## Reflection of words in adjacent transpositions -/

section Reflection

open Equiv TypeA













end Reflection

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Crossings away from the first position -/

section Shift








end Shift

/-! ## Closing the first strand on the left -/

section CloseLeft

variable (μ : X) (j : I)



/-- Upward layers not involving the closed strand leave the closure, below. -/
theorem dg_closeLsL_peel {s s' t : List (Letter I)} (L M : List (LayerData I))
    (hL : SChain s L s') (hM : SChain ([up j] ++ s') M ([up j] ++ t)) (e : ℕ) :
    NF.dg (pres RD k sc) μ s t (closeLsL j s t (L.map (whL [up j] []) ++ M) e) =
      NF.dg (pres RD k sc) μ s s' L ≫ NF.dg (pres RD k sc) μ s' t (closeLsL j s' t M e) := by
  have ei := NF.dg_interchange (P := pres RD k sc) (μ := μ) (S := s) (T := t) []
    (M.map (whL [dn j] []) ++ List.replicate e ([dn j], .dot (up j), t) ++ [([], .cap (up j), t)])
    (A := [([], .cup (dn j), [])]) (s := []) (s' := [dn j, up j]) (by schain) hL
  rw [NF.dg_comp hL (sChain_closeLsL hM e)]
  unfold closeLsL
  wnf at ei ⊢
  rw [ei]

/-- Upward layers not involving the closed strand leave the closure, above. -/
theorem dg_closeLsL_peel_top {s t t' : List (Letter I)} (M P : List (LayerData I))
    (hM : SChain ([up j] ++ s) M ([up j] ++ t')) (hP : SChain t' P t) :
    NF.dg (pres RD k sc) μ s t (closeLsL j s t (M ++ P.map (whL [up j] [])) 0) =
      NF.dg (pres RD k sc) μ s t' (closeLsL j s t' M 0) ≫ NF.dg (pres RD k sc) μ t' t P := by
  have ei := NF.dg_interchange (P := pres RD k sc) (μ := μ) (S := s) (T := t)
    ([([], .cup (dn j), s)] ++ M.map (whL [dn j] [])) []
    (A := [([], .cap (up j), [])]) (s := [dn j, up j]) (s' := []) (by schain) hP
  rw [NF.dg_comp (sChain_closeLsL hM 0) hP]
  unfold closeLsL
  simp only [List.replicate_zero, List.append_nil] at ei ⊢
  wnf at ei ⊢
  rw [← ei]

/-- A dot on the closed strand at the bottom moves around the closure to the top. -/
theorem dg_closeLsL_rotate {s t : List (Letter I)} (M : List (LayerData I))
    (hM : SChain ([up j] ++ s) M ([up j] ++ t)) (e : ℕ) :
    NF.dg (pres RD k sc) μ s t (closeLsL j s t (([], .dot (up j), s) :: M) e) =
      NF.dg (pres RD k sc) μ s t (closeLsL j s t M (e + 1)) := by
  have hM' : SChain (dn j :: up j :: s) (M.map (whL [dn j] [])) (dn j :: up j :: t) := by
    simpa using hM.whisk [dn j] []
  have hdots : SChain (dn j :: up j :: t) (List.replicate e ([dn j], .dot (up j), t))
      (dn j :: up j :: t) :=
    SChain.replicate_of (x := ([dn j], Shape.dot (up j), t)) ⟨by simp, by simp⟩ e
  have hcap : SChain (dn j :: up j :: t) [([], .cap (up j), t)] t := ⟨by simp, by simp⟩
  unfold closeLsL
  -- the dot moves from the upward leg of the cup to its downward leg
  refine (NF.dg_step (pres RD k sc) μ (s₀ := s) (t₀ := t) []
    (M.map (whL [dn j] []) ++ List.replicate e ([dn j], .dot (up j), t) ++ [([], .cap (up j), t)])
    [] s (dg_dot_cupDn RD k sc j (wt RD μ s)) (by simp)
    (by simpa using (hM'.append hdots).append hcap) (by simp [whL]) rfl).trans ?_
  -- past the layers of `M`
  have ei := NF.dg_interchange (P := pres RD k sc) (μ := μ) (S := s) (T := t)
    [([], .cup (dn j), s)] (List.replicate e ([dn j], .dot (up j), t) ++ [([], .cap (up j), t)])
    (A := [([], .dot (dn j), [])]) (s := [dn j]) (s' := [dn j]) (by schain) hM
  wnf at ei ⊢
  rw [ei]
  -- past the dots on the closed strand
  have hpre : SChain s (([], .cup (dn j), s) :: M.map (whL [dn j] [])) (dn j :: up j :: t) :=
    (show SChain s [([], .cup (dn j), s)] (dn j :: up j :: s) from ⟨by simp, by simp⟩).append hM'
  refine (NF.dg_step (pres RD k sc) μ (s₀ := s) (t₀ := t) (([], .cup (dn j), s) :: M.map (whL [dn j] []))
    [([], .cap (up j), t)] [] t (NF.dg_swap_dots (pres RD k sc) (wt RD μ t) [] [] [] (dn j) (up j) e 1).symm
    (by simpa using hpre) (by simp) (by simp [whL]) rfl).trans ?_
  -- around the cap
  refine (NF.dg_step (pres RD k sc) μ (s₀ := s) (t₀ := t) ((([], .cup (dn j), s) :: M.map (whL [dn j] [])) ++
    List.replicate e ([dn j], .dot (up j), t)) [] [] t (dg_dot_cap_up RD k sc (wt RD μ t) j)
    (by simpa using hpre.append hdots) (by simp) (by simp [whL]) rfl).trans ?_
  simp [whL, List.replicate_succ']

theorem dg_closeLsL_nil (s : List (Letter I)) (e : ℕ) :
    NF.dg (pres RD k sc) μ s s (closeLsL j s s [] e) =
      NF.plcL (pres RD k sc) μ [] s [] [] (NF.dg (pres RD k sc) (wt RD μ s) [] [] (ccwLs j e)) := by
  rw [NF.plcL_dg]
  simp [closeLsL, ccwLs, whL]



theorem dg_closeLsL_curl (s₁ : List (Letter I)) (e : ℕ) :
    NF.dg (pres RD k sc) μ ([] ++ [up j] ++ s₁) ([] ++ [up j] ++ s₁)
      (closeLsL j ([up j] ++ s₁) ([up j] ++ s₁) [([], .cross true j j, s₁)] e) =
      NF.plcL (pres RD k sc) μ [] s₁ [up j] [up j] (NF.dg (pres RD k sc) (wt RD μ s₁) [up j] [up j] (curlLLs j e)) := by
  rw [NF.plcL_dg]
  simp [closeLsL, curlLLs, whL]

theorem dotsU_mem_slideSetL (ν : X) (l : Letter I) (a : ℕ) : NF.dotsU (pres RD k sc) ν l a ∈ slideSetL RD k sc ν l := by
  have := mem_slideSetL (RD := RD) (k := k) (sc := sc) (μ := ν) (l := l) (a := a) IsBub.id
  rwa [bubLU_id, Category.comp_id] at this

/-- The counterclockwise bubble with `e` dots to the left of `E_j`. -/
theorem dg_ccw_left (ν : X) (e : ℕ) :
    NF.dg (pres RD k sc) ν [up j] [up j] ([([], .cup (dn j), [up j])] ++
        List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])]) =
      NF.bubLU (pres RD k sc) ν (up j) (NF.ccwU (pres RD k sc) (wt RD ν [up j]) j e) := by
  rw [NF.ccwU_of_nonneg, NF.bubLU, NF.plcL_dg]
  simp [ccwLs, whL]

/-- **The left curl with dots on its loop** is a linear combination of bubble monomials to the
left of the strand times dots (the left curl relation and the nilHecke relation). -/
theorem curlL_mem_slideSetL (ν : X) (e : ℕ) :
    NF.dg (pres RD k sc) ν [up j] [up j] (curlLLs j e) ∈ slideSetL RD k sc ν (up j) := by
  induction e with
  | zero =>
    have h := dg_curlL RD k sc j ν
    rw [show curlLLs j 0 = [([], .cup (dn j), [up j]), ([dn j], .cross true j j, []),
      ([], .cap (up j), [up j])] from rfl, h]
    exact Submodule.sum_mem _ fun g _ => mem_slideSetL' (ccwU_isBub _ _)
  | succ e ih =>
    have E : NF.dg (pres RD k sc) ν [up j, up j] [up j, up j]
        [([], .cross true j j, []), ([], .dot (up j), [up j])] =
        NF.dg (pres RD k sc) ν [up j, up j] [up j, up j]
          [([up j], .dot (up j), []), ([], .cross true j j, [])] +
        NF.dg (pres RD k sc) ν [up j, up j] [up j, up j] [] := dg_slideLEq RD k sc ν j
    have key := NF.dg_stepL (pres RD k sc) ν (s₀ := [up j]) (t₀ := [up j])
      [([], .cup (dn j), [up j])]
      (List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])]) [dn j] []
      (L := curlLLs j (e + 1)) E (by schain) (by schain)
      (by simp [curlLLs, whL, List.replicate_succ])
    rw [key, map_add, NF.ctxL_dg_nil (pres RD k sc) ν (by schain) (by schain),
      NF.ctxL_dg_nil (pres RD k sc) ν (by schain) (by schain)]
    simp only [whL, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_nil]
    refine add_mem ?_ ?_
    · have e2 : NF.dg (pres RD k sc) ν [up j] [up j] (([], .cup (dn j), [up j]) ::
          ([dn j, up j], .dot (up j), []) :: ([dn j], .cross true j j, []) ::
            (List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])])) =
          NF.dotsU (pres RD k sc) ν (up j) 1 ≫ NF.dg (pres RD k sc) ν [up j] [up j] (curlLLs j e) := by
        rw [NF.dotsU, NF.dg_comp (by schain) (sChain_curlLLs j e)]
        dstepQ [] (([dn j], .cross true j j, []) ::
            (List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])])) [] []
          (NF.dg_swap' (pres RD k sc) (wt RD (wt RD ν []) []) [] [] [] (.cup (dn j)) (.dot (up j)))
        simp [curlLLs]
      rw [e2]
      exact slideSetL_comp (dotsU_mem_slideSetL RD k sc ν _ 1) ih
    · have hm := mem_slideSetL_bub (RD := RD) (k := k) (sc := sc) (μ := ν) (l := up j)
        (ccwU_isBub (RD := RD) (k := k) (sc := sc) (lam := wt RD ν [up j]) j e)
      rw [← dg_ccw_left] at hm
      exact hm

end CloseLeft

/-! ## Placing dots and bubbles to the left of upward strands -/

section PlaceLeft

variable (μ : X)

theorem plcL_bubLU_eq_ctxL (s₁ : List (Letter I)) (c : I)
    (δ : End ((pres RD k sc).obj (ob RD (wt RD (wt RD μ s₁) [up c]) []))) :
    NF.plcL (pres RD k sc) μ [] s₁ [up c] [up c] (NF.bubLU (pres RD k sc) (wt RD μ s₁) (up c) δ) =
      NF.ctxL (pres RD k sc) μ (up c :: s₁) (up c :: s₁) [] [] (up c :: s₁) [] [] [] δ := by
  have key := hom_ext_dg RD k sc (wt RD (wt RD μ s₁) [up c]) (s := []) (t := [])
    ((NF.plcL (pres RD k sc) μ [] s₁ [up c] [up c]).comp (NF.plcL (pres RD k sc) (wt RD μ s₁) [] [up c] [] []))
    (NF.ctxL (pres RD k sc) μ (up c :: s₁) (up c :: s₁) [] [] (up c :: s₁) [] [] []) (fun B hB => ?_)
  · exact LinearMap.congr_fun key δ
  change NF.plcL (pres RD k sc) μ [] s₁ [up c] [up c] (NF.plcL (pres RD k sc) (wt RD μ s₁) [] [up c] [] []
    (NF.dg (pres RD k sc) (wt RD (wt RD μ s₁) [up c]) [] [] B)) =
    NF.ctxL (pres RD k sc) μ (up c :: s₁) (up c :: s₁) [] [] (up c :: s₁) [] [] []
      (NF.dg (pres RD k sc) (wt RD μ (up c :: s₁)) [] [] B)
  rw [NF.plcL_dg]
  simp only [List.nil_append]
  erw [NF.plcL_dg]
  rw [NF.ctxL_dg (pres RD k sc) μ (s := []) (t := []) (by simp) (by simp)]
  simp only [List.nil_append, List.append_nil, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨a', g, b'⟩ := x
  simp [whL]

variable {RD k sc}

/-- Dots on the first strand and bubble monomials to its left, placed to the left of the upward
strands `s₁`, lie in `upSpan` (the bubbles slide to the far right, `slideOutUp`). -/
theorem plcL_slideSetL_mem_upSpan (s₁ : List (Letter I))
    (hs₁ : Positive s₁) (c : I) {f : End ((pres RD k sc).obj (ob RD (wt RD μ s₁) [up c]))}
    (hf : f ∈ slideSetL RD k sc (wt RD μ s₁) (up c)) :
    NF.plcL (pres RD k sc) μ [] s₁ [up c] [up c] f ∈ upSpan RD k sc μ (up c :: s₁) (up c :: s₁) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, δ, hδ, rfl⟩ := hf
    rw [← NF.plcL_comp (pres RD k sc) μ [] s₁ rfl rfl, plcL_bubLU_eq_ctxL, NF.dotsU, NF.plcL_dg]
    have hrep : SChain [up c] (List.replicate a ([], .dot (up c), [])) [up c] :=
      SChain.replicate_of (by schain) a
    have hrep' : SChain (up c :: s₁) ((List.replicate a ([], .dot (up c), [])).map (whL [] s₁))
        (up c :: s₁) := by simpa using hrep.whisk [] s₁
    refine upSpan_comp_left (fun x hx => ?_) hrep' ?_
    · rw [List.map_replicate] at hx
      rw [List.eq_of_mem_replicate hx]; rfl
    · refine slideOutUp RD k sc μ (up c :: s₁) [] [] [] (by simp) (by simp)
        (fun x hx => by simp at hx) (fun x hx => by simp at hx) ?_ δ hδ
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · rfl
      · exact hs₁ l hl
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end PlaceLeft

/-! ## The left Markov lemma -/

section MarkovLeft

variable (μ : X)

/-- **The left partial trace**: closing the first strand `E_j` of a 2-morphism
`E_{j a} 1_μ ⟶ E_{j b} 1_μ` on its left, with the cup `1 → F_j E_j` and the cap
`F_j E_j → 1`. -/
def ptrFirst (a b : List (Letter I)) (j : I) :
    ((pres RD k sc).obj (ob RD (wt RD μ []) ([up j] ++ a)) ⟶
      (pres RD k sc).obj (ob RD (wt RD μ []) ([up j] ++ b))) →ₗ[k]
      ((pres RD k sc).obj (ob RD μ a) ⟶ (pres RD k sc).obj (ob RD μ b)) where
  toFun f := NF.dg (pres RD k sc) μ a ([dn j] ++ ([up j] ++ a) ++ []) [([], .cup (dn j), a)] ≫
    NF.plcL (pres RD k sc) μ [dn j] [] ([up j] ++ a) ([up j] ++ b) f ≫
      NF.dg (pres RD k sc) μ ([dn j] ++ ([up j] ++ b) ++ []) b [([], .cap (up j), b)]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ptrFirst_dg (a b : List (Letter I)) (j : I) (A : List (LayerData I)) :
    ptrFirst RD k sc μ a b j (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ a) ([up j] ++ b) A) =
      NF.dg (pres RD k sc) μ a b (closeLsL j a b A 0) := by
  show NF.dg (pres RD k sc) μ a _ _ ≫ NF.plcL (pres RD k sc) μ [dn j] [] _ _ (NF.dg (pres RD k sc) (wt RD μ []) _ _ A) ≫ _ = _
  rw [NF.plcL_dg]
  have h1 : SChain a [([], .cup (dn j), a)] ([dn j] ++ ([up j] ++ a) ++ []) := ⟨by simp, by simp⟩
  have h3 : SChain ([dn j] ++ ([up j] ++ b) ++ []) [([], .cap (up j), b)] b := ⟨by simp, by simp⟩
  by_cases hA : SChain ([up j] ++ a) A ([up j] ++ b)
  · have h2 := hA.whisk [dn j] []
    rw [NF.dg_comp h2 h3, NF.dg_comp h1 (h2.append h3)]
    simp [closeLsL]
  · rw [NF.dg_of_not (fun h => hA h.of_whisk), Limits.zero_comp, Limits.comp_zero, NF.dg_of_not]
    intro h
    unfold closeLsL at h
    simp only [List.replicate_zero, List.append_nil] at h
    obtain ⟨m₂, h₁₂, h₃'⟩ := SChain.split h
    obtain ⟨m₁, h₁', h₂'⟩ := SChain.split h₁₂
    obtain rfl := h₁'.eq_target h1
    obtain rfl := h₃'.eq_source h3
    exact hA h₂'.of_whisk

variable {RD k sc} (j : I)

/-- Dots at the bottom of a left closure leave it (or move around it to the top). -/
theorem closeLsL_dots_mem {s t : List (Letter I)} (N : List (LayerData I))
    (hN : SChain ([up j] ++ s) N ([up j] ++ t))
    (hbase : ∀ e, NF.dg (pres RD k sc) μ s t (closeLsL j s t N e) ∈ upSpan RD k sc μ s t) :
    ∀ (Dl : List (LayerData I)), DotsOnly Dl → SChain ([up j] ++ s) Dl ([up j] ++ s) →
      ∀ e, NF.dg (pres RD k sc) μ s t (closeLsL j s t (Dl ++ N) e) ∈ upSpan RD k sc μ s t := by
  intro Dl
  induction Dl with
  | nil => intro _ _ e; exact hbase e
  | cons d Dl ih =>
    intro hD hDc e
    obtain ⟨u, g, v⟩ := d
    obtain ⟨l, hgl, hl⟩ := hD _ List.mem_cons_self
    simp only at hgl
    subst hgl
    obtain ⟨h₀, hDc'⟩ := hDc
    simp only [Shape.cod_dot, Shape.dom_dot] at h₀ hDc'
    rw [← h₀] at hDc'
    have hD' : DotsOnly Dl := fun x hx => hD x (List.mem_cons_of_mem _ hx)
    rcases u with _ | ⟨u₀, u⟩
    · -- a dot on the closed strand: it moves around the closure
      simp only [List.nil_append, List.singleton_append, List.cons.injEq] at h₀
      obtain ⟨rfl, rfl⟩ := h₀
      rw [List.cons_append, dg_closeLsL_rotate RD k sc μ j _ (hDc'.append hN)]
      exact ih hD' hDc' (e + 1)
    · -- a dot on another strand: it leaves the closure
      simp only [List.cons_append, List.cons.injEq] at h₀
      obtain ⟨rfl, hs⟩ := h₀
      have hd : SChain s [(u, Shape.dot l, v)] s := ⟨hs, hs.symm⟩
      have hform : ((up j :: u, Shape.dot l, v) :: Dl) ++ N =
          [(u, Shape.dot l, v)].map (whL [up j] []) ++ (Dl ++ N) := by simp [whL]
      rw [hform, dg_closeLsL_peel RD k sc μ j _ _ hd (hDc'.append hN)]
      refine upSpan_comp_left (fun x hx => ?_) hd (ih hD' hDc' e)
      rw [List.mem_singleton.1 hx]; exact hl


theorem closeLsL_nil_mem (s : List (Letter I)) (hs : Positive s) (e : ℕ) :
    NF.dg (pres RD k sc) μ s s (closeLsL j s s [] e) ∈ upSpan RD k sc μ s s := by
  rw [dg_closeLsL_nil]
  have hc : NF.plcL (pres RD k sc) μ [] s [] [] (NF.dg (pres RD k sc) (wt RD μ s) [] [] (ccwLs j e)) =
      NF.ctxL (pres RD k sc) μ s s [] [] s [] [] [] (NF.dg (pres RD k sc) (wt RD μ s) [] [] (ccwLs j e)) := by
    show _ = NF.dg (pres RD k sc) μ s s [] ≫ NF.plcL (pres RD k sc) μ [] s [] [] _ ≫ NF.dg (pres RD k sc) μ s s []
    rw [NF.dg_nil]
    erw [Category.id_comp, Category.comp_id]
  rw [hc]
  refine slideOutUp RD k sc μ s [] [] [] (by simp) (by simp) (fun x hx => by simp at hx)
    (fun x hx => by simp at hx) hs _ ?_
  rw [← NF.ccwU_of_nonneg]
  exact ccwU_isBub _ _

variable [DecidableEq I]

/-- **The left Markov lemma**: closing the first strand of an upward diagram on its left gives a
linear combination of upward diagrams followed by bubble monomials on the far right. -/
theorem ptrFirst_upward_mem_upSpan (a b : List I) {A : List (LayerData I)} (hA : Upward A)
    (h : SChain ([up j] ++ ups a) A ([up j] ++ ups b)) :
    ptrFirst RD k sc μ (ups a) (ups b) j
      (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ ups a) ([up j] ++ ups b) A) ∈ upSpan RD k sc μ (ups a) (ups b) := by
  have hperm : ([j] ++ a).Perm ([j] ++ b) := upward_perm hA (by simpa [ups] using h)
  set ν : Multiset I := (([j] ++ a : List I) : Multiset I)
  let i := seqOfEq ν ([j] ++ a) rfl
  let i' := seqOfEq ν ([j] ++ b) (Multiset.coe_eq_coe.2 hperm.symm)
  have hi : KLR.Diagram.word i = [j] ++ a := word_seqOfEq _ _ _
  have hi' : KLR.Diagram.word i' = [j] ++ b := word_seqOfEq _ _ _
  have hm : Multiset.card ν = a.length + 1 := by simp [ν]
  have hmem := upward_mem_span_nf' RD k sc (wt RD μ []) (canWordL (Multiset.card ν))
    (fun w => ⟨isReduced_canWordL _ w, wordProd_canWordL _ w⟩) i i'
    (S := [up j] ++ ups a) (T := [up j] ++ ups b) (by rw [hi]; simp [ups])
    (by rw [hi']; simp [ups]) hA h
  refine (Submodule.span_le (p := (upSpan RD k sc μ (ups a) (ups b)).comap
    (ptrFirst RD k sc μ (ups a) (ups b) j))).mpr ?_ hmem
  rintro _ ⟨w, D, hw, hD, rfl⟩
  show ptrFirst RD k sc μ (ups a) (ups b) j (D ≫ _) ∈ upSpan RD k sc μ (ups a) (ups b)
  obtain ⟨l, σ, hl, hσ, hcan⟩ := canWordL_reverse_split a.length _ hm w
  set x := ([j] ++ a).take l with hx
  set y := ([j] ++ a).drop (l + 1) with hy
  have hxl : x.length = l := by
    simp only [hx, List.length_take, List.length_append, List.length_singleton]; omega
  obtain ⟨c₀, hsplit⟩ : ∃ c₀, [j] ++ a = x ++ [c₀] ++ y :=
    ⟨([j] ++ a)[l]'(by simp; omega),
      (KLR.Diagram.take_append_drop_get ([j] ++ a) l (by simp; omega)).symm⟩
  have hrun := crossLs_leftRun x c₀ y
  have hrest := crossLs_cons_shift c₀ (x ++ y) σ
  have e1 : crossLs (x ++ [c₀] ++ y) ((List.range' 0 l).reverse ++ σ.map (· + 1)) =
      leftRunLs x c₀ y ++ crossLs ([c₀] ++ x ++ y) (σ.map (· + 1)) := by
    rw [crossLs_append, ← hxl, hrun.1, hrun.2]
  have e2 : crossLs ([c₀] ++ x ++ y) (σ.map (· + 1)) = (crossLs (x ++ y) σ).map (whL [up c₀] []) :=
    hrest.1
  have hcross : crossLs (KLR.Diagram.word i) (canWordL (Multiset.card ν) w).reverse =
      leftRunLs x c₀ y ++ (crossLs (x ++ y) σ).map (whL [up c₀] []) := by
    rw [hi, hcan, hsplit, e1, e2]
  have e3 : applyW (x ++ [c₀] ++ y) ((List.range' 0 l).reverse ++ σ.map (· + 1)) =
      c₀ :: applyW (x ++ y) σ := by
    rw [applyW_append, ← hxl, hrun.2]; exact hrest.2
  have hfin : c₀ :: applyW (x ++ y) σ = j :: b := by
    have e4 := word_wordProd_smul (canWordL (Multiset.card ν) w) i
    rw [wordProd_canWordL, hw, hi', hi, hcan, hsplit, e3] at e4
    exact e4.symm
  obtain ⟨hc₀, hb⟩ := List.cons.inj hfin
  subst c₀
  have hP : SChain (ups (x ++ y)) (crossLs (x ++ y) σ) (ups b) := by
    rw [← hb]; exact sChain_crossLs _ _
  have hS : [up j] ++ ups a = ups (x ++ [j] ++ y) := by
    rw [← hsplit]; simp [ups]
  have hS' : [up j] ++ ups (x ++ y) = ups ([j] ++ x ++ y) := by simp [ups]
  -- the closed part
  have hclosed : ∀ (Dl : List (LayerData I)), DotsOnly Dl →
      SChain ([up j] ++ ups a) Dl ([up j] ++ ups a) →
      NF.dg (pres RD k sc) μ (ups a) (ups (x ++ y)) (closeLsL j (ups a) (ups (x ++ y)) (Dl ++ leftRunLs x j y) 0) ∈
        upSpan RD k sc μ (ups a) (ups (x ++ y)) := by
    have hN : SChain ([up j] ++ ups a) (leftRunLs x j y) ([up j] ++ ups (x ++ y)) := by
      rw [hS, hS']; exact sChain_leftRunLs x j y
    intro Dl hDl hDlc
    refine closeLsL_dots_mem μ j (leftRunLs x j y) hN ?_ Dl hDl hDlc 0
    intro e
    rcases hxz : x with _ | ⟨x₀, x'⟩
    · -- no run: a dotted counterclockwise bubble
      rw [hxz] at hsplit
      have ha : a = y := by simpa using hsplit
      rw [List.nil_append, ← ha]
      simp only [leftRunLs]
      exact closeLsL_nil_mem μ j (ups a) (positive_ups a) e
    · -- a run followed by a left curl
      rw [hxz] at hsplit
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨hj, ha⟩ := hsplit
      subst hj
      have ha' : a = x' ++ [j] ++ y := by simpa using ha
      have hL := sChain_leftRunLs x' j y
      have hcore : SChain ([up j] ++ ups ([j] ++ x' ++ y))
          [([], .cross true j j, ups (x' ++ y))] ([up j] ++ ups (j :: x' ++ y)) :=
        ⟨by simp [ups], by simp [ups]⟩
      simp only [leftRunLs]
      rw [ha', dg_closeLsL_peel RD k sc μ j _ _ hL hcore]
      refine upSpan_comp_left (upward_leftRunLs x' j y) hL ?_
      have hm := plcL_slideSetL_mem_upSpan μ (ups (x' ++ y)) (positive_ups _) j
        (curlL_mem_slideSetL RD k sc j (wt RD μ (ups (x' ++ y))) e)
      rw [← dg_closeLsL_curl] at hm
      exact dg_mem_upSpan_congr RD k sc μ (by simp [ups]) (by simp [ups]) hm
  -- assemble
  induction hD using Submodule.span_induction with
  | mem D hD =>
    obtain ⟨Dl, hDl, hDlc, rfl⟩ := hD
    have hR : SChain ([up j] ++ ups a) (leftRunLs x j y) ([up j] ++ ups (x ++ y)) := by
      rw [hS, hS']; exact sChain_leftRunLs x j y
    have hP' : SChain ([up j] ++ ups (x ++ y)) ((crossLs (x ++ y) σ).map (whL [up j] []))
        ([up j] ++ ups b) := by simpa using hP.whisk [up j] []
    have hC : SChain ([up j] ++ ups a)
        (crossLs (KLR.Diagram.word i) (canWordL (Multiset.card ν) w).reverse)
        ([up j] ++ ups b) := by rw [hcross]; exact hR.append hP'
    rw [NF.dg_comp hDlc hC, ptrFirst_dg, hcross, ← List.append_assoc,
      dg_closeLsL_peel_top RD k sc μ j _ _ (hDlc.append hR) hP]
    exact upSpan_comp_right (upward_crossLs _ _) hP (hclosed Dl hDl hDlc)
  | zero => rw [Limits.zero_comp, map_zero]; exact Submodule.zero_mem _
  | add D₁ D₂ _ _ h₁ h₂ => rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul r D _ hD' => rw [Linear.smul_comp, map_smul]; exact Submodule.smul_mem _ r hD'

omit [DecidableEq I] in
/-- A bubble monomial on the far right stays outside the left closure. -/
theorem ptrFirst_bubAt {s t : List (Letter I)} (A : List (LayerData I))
    (hA : SChain ([up j] ++ s) A ([up j] ++ t)) (γ : End ((pres RD k sc).obj (ob RD μ []))) :
    ptrFirst RD k sc μ s t j (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A ≫
        bubAt RD k sc (wt RD μ []) ([up j] ++ t) γ) =
      ptrFirst RD k sc μ s t j (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A) ≫
        bubAt RD k sc μ t γ := by
  have key := hom_ext_dg RD k sc μ (s := []) (t := [])
    ((ptrFirst RD k sc μ s t j).comp ((Linear.leftComp k _
      (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A)).comp
        (bubAt RD k sc (wt RD μ []) ([up j] ++ t))))
    ((Linear.leftComp k _ (ptrFirst RD k sc μ s t j
      (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A))).comp (bubAt RD k sc μ t))
    (fun B hB => ?_)
  · exact LinearMap.congr_fun key γ
  change ptrFirst RD k sc μ s t j (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A ≫
      bubAt RD k sc (wt RD μ []) ([up j] ++ t) (NF.dg (pres RD k sc) (wt RD μ []) [] [] B)) =
    ptrFirst RD k sc μ s t j (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A) ≫
      bubAt RD k sc μ t (NF.dg (pres RD k sc) μ [] [] B)
  have hB1 : SChain ([up j] ++ t) (B.map (whL ([up j] ++ t) [])) ([up j] ++ t) := by
    simpa using hB.whisk ([up j] ++ t) []
  have hBt : SChain t (B.map (whL t [])) t := by simpa using hB.whisk t []
  rw [bubAt_dg, bubAt_dg, NF.dg_comp hA hB1]
  rw [ptrFirst_dg, ptrFirst_dg, NF.dg_comp (sChain_closeLsL hA 0) hBt]
  have e := dg_closed_left (RD := RD) (k := k) (sc := sc) μ (S := s) (T := t)
    ([([], .cup (dn j), s)] ++ A.map (whL [dn j] [])) [] (s := [dn j, up j] ++ t) (s' := t) []
    hB (A := [([], .cap (up j), t)]) ⟨by simp, by simp⟩
  unfold closeLsL
  wnf at e ⊢
  simp only [List.replicate_zero, List.nil_append] at e ⊢
  exact e.symm

/-- **The left partial trace preserves `upSpan`.** -/
theorem ptrFirst_mem_upSpan (a b : List I) {f}
    (hf : f ∈ upSpan RD k sc (wt RD μ []) ([up j] ++ ups a) ([up j] ++ ups b)) :
    ptrFirst RD k sc μ (ups a) (ups b) j f ∈ upSpan RD k sc μ (ups a) (ups b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    rw [ptrFirst_bubAt (RD := RD) (k := k) (sc := sc) μ j A h γ]
    have hM := ptrFirst_upward_mem_upSpan (RD := RD) (k := k) (sc := sc) μ j a b hA h
    generalize ptrFirst RD k sc μ (ups a) (ups b) j
      (NF.dg (pres RD k sc) (wt RD μ []) ([up j] ++ ups a) ([up j] ++ ups b) A) = F at hM ⊢
    induction hM using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨A₁, γ₁, hA₁, h₁, hγ₁, rfl⟩ := hf
      rw [Category.assoc, ← bubAt_comp]
      exact Submodule.subset_span ⟨A₁, _, hA₁, h₁, IsBub.comp hγ₁ hγ, rfl⟩
    | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end MarkovLeft


end Categorification.KL3.Diagram.CLQ
