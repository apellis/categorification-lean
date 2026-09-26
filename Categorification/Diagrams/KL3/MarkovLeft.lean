/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Traces

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

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

/-! ## Reflection of words in adjacent transpositions -/

section Reflection

open Equiv TypeA

/-- The reflection `t ↦ m - 2 - t` of the letters of a word for `Fin m`. -/
def reflW (m : ℕ) (ρ : List ℕ) : List ℕ := ρ.map (fun t => m - 2 - t)

theorem sadj_refl {m t : ℕ} (h : t + 1 < m) :
    sadj m (m - 2 - t) = Fin.revPerm * sadj m t * Fin.revPerm := by
  ext i
  have h' : m - 2 - t + 1 < m := by omega
  simp only [Perm.mul_apply, Fin.revPerm_apply, sadj_val_of_lt h', Fin.val_rev,
    sadj_val_of_lt h]
  have := i.2
  unfold swapNat
  split_ifs <;> omega

theorem revPerm_mul_revPerm (m : ℕ) : (Fin.revPerm : Perm (Fin m)) * Fin.revPerm = 1 := by
  ext i; simp

theorem validWord_reflW {m : ℕ} {ρ : List ℕ} (h : ValidWord m ρ) : ValidWord m (reflW m ρ) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
  have := h s hs
  omega

theorem wordProd_reflW {m : ℕ} {ρ : List ℕ} (h : ValidWord m ρ) :
    wordProd m (reflW m ρ) = Fin.revPerm * wordProd m ρ * Fin.revPerm := by
  induction ρ with
  | nil => simp [reflW, revPerm_mul_revPerm]
  | cons t ρ ih =>
    have ht : t + 1 < m := h t List.mem_cons_self
    have h' : ValidWord m ρ := fun s hs => h s (List.mem_cons_of_mem _ hs)
    simp only [reflW, List.map_cons] at ih ⊢
    rw [wordProd_cons, ih h', sadj_refl ht, wordProd_cons]
    simp only [mul_assoc]
    rw [← mul_assoc Fin.revPerm Fin.revPerm, revPerm_mul_revPerm, one_mul]

theorem length_revConj_le (m : ℕ) (w : Perm (Fin m)) :
    length m (Fin.revPerm * w * Fin.revPerm) ≤ length m w := by
  obtain ⟨ρ, hρ, rfl⟩ := exists_reduced m w
  calc length m (Fin.revPerm * wordProd m ρ * Fin.revPerm)
      ≤ (reflW m ρ).length :=
        length_le_of_wordProd_eq (validWord_reflW hρ.1) (wordProd_reflW hρ.1)
    _ = ρ.length := by simp [reflW]
    _ = length m (wordProd m ρ) := hρ.2

theorem length_revConj (m : ℕ) (w : Perm (Fin m)) :
    length m (Fin.revPerm * w * Fin.revPerm) = length m w := by
  refine le_antisymm (length_revConj_le m w) ?_
  have := length_revConj_le m (Fin.revPerm * w * Fin.revPerm)
  simp only [mul_assoc, revPerm_mul_revPerm, mul_one] at this
  rwa [← mul_assoc, revPerm_mul_revPerm, one_mul] at this

theorem isReduced_reflW {m : ℕ} {ρ : List ℕ} (h : IsReduced m ρ) : IsReduced m (reflW m ρ) := by
  refine ⟨validWord_reflW h.1, ?_⟩
  rw [wordProd_reflW h.1, length_revConj]
  simp [reflW, h.2]

/-- The reflected canonical word of `w`: the canonical word of `w₀ w w₀` with the positions
reflected. -/
noncomputable def canWordL (m : ℕ) (w : Perm (Fin m)) : List ℕ :=
  reflW m (canWord m (Fin.revPerm * w * Fin.revPerm))

theorem isReduced_canWordL (m : ℕ) (w : Perm (Fin m)) : IsReduced m (canWordL m w) :=
  isReduced_reflW (isReduced_canWord m _)

theorem wordProd_canWordL (m : ℕ) (w : Perm (Fin m)) : wordProd m (canWordL m w) = w := by
  rw [canWordL, wordProd_reflW (validWord_canWord m _), wordProd_canWord]
  simp only [← mul_assoc, revPerm_mul_revPerm, one_mul]
  rw [mul_assoc, revPerm_mul_revPerm, mul_one]

/-- The reflected canonical word, from the bottom: a run moving the strand at the position
`l` to the first position, then crossings avoiding the first position. -/
theorem canWordL_reverse_split (n m : ℕ) (hm : m = n + 1) (w : Perm (Fin m)) :
    ∃ (l : ℕ) (σ : List ℕ), l ≤ n ∧ (∀ t ∈ σ, t + 2 < m) ∧
      (canWordL m w).reverse = (List.range' 0 l).reverse ++ σ.map (· + 1) := by
  obtain ⟨b₀, ρ', hb₀, hρ', hcan⟩ := canWord_reverse_split n m hm (Fin.revPerm * w * Fin.revPerm)
  refine ⟨n - b₀, ρ'.map (fun t => n - 2 - t), by omega, fun t ht => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    have := hρ' s hs; omega
  · rw [canWordL, reflW, ← List.map_reverse, hcan, List.map_append]
    congr 1
    · subst hm
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.length_map, List.length_range'] at h1
      simp [List.getElem_reverse]
      omega
    · subst hm
      simp only [List.map_map, Function.comp_def]
      refine List.map_congr_left fun t ht => ?_
      have := hρ' t ht
      omega

end Reflection

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Crossings away from the first position -/

section Shift

theorem swapAt_cons (z : I) (w : List I) (t : ℕ) : swapAt (z :: w) (t + 1) = z :: swapAt w t := by
  unfold swapAt
  simp only [List.drop_succ_cons, List.take_succ_cons]
  split <;> rfl

theorem crossAt_cons (z : I) (w : List I) (t : ℕ) :
    crossAt (z :: w) (t + 1) = (crossAt w t).map (whL [up z] []) := by
  unfold crossAt
  simp only [List.drop_succ_cons, List.take_succ_cons]
  split <;> simp [whL, ups]

/-- Crossings avoiding the first position are whiskered by the first strand. -/
theorem crossLs_cons_shift (z : I) (w : List I) (σ : List ℕ) :
    crossLs (z :: w) (σ.map (· + 1)) = (crossLs w σ).map (whL [up z] []) ∧
      applyW (z :: w) (σ.map (· + 1)) = z :: applyW w σ := by
  induction σ generalizing w with
  | nil => simp
  | cons t σ ih =>
    simp only [List.map_cons, crossLs_cons, applyW_cons, swapAt_cons, crossAt_cons,
      (ih (swapAt w t)).1, (ih (swapAt w t)).2, List.map_append]
    simp

/-- The upward strand `c`, between the strands `x` and `y`, crossing all the strands of `x` to
become the first strand. -/
def leftRunLs : List I → I → List I → List (LayerData I)
  | [], _, _ => []
  | x₀ :: x, c, y => (leftRunLs x c y).map (whL [up x₀] []) ++ [([], .cross true x₀ c, ups (x ++ y))]

/-- The descending run `l - 1, …, 1, 0` moves the strand at the position `l` to the first
position. -/
theorem crossLs_leftRun (x : List I) (c : I) (y : List I) :
    crossLs (x ++ [c] ++ y) (List.range' 0 x.length).reverse = leftRunLs x c y ∧
      applyW (x ++ [c] ++ y) (List.range' 0 x.length).reverse = [c] ++ x ++ y := by
  induction x with
  | nil => simp [leftRunLs]
  | cons x₀ x ih =>
    have hr : (List.range' 0 (x.length + 1)).reverse =
        ((List.range' 0 x.length).reverse).map (· + 1) ++ [0] := by
      rw [List.range'_succ, List.reverse_cons]
      congr 1
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.length_reverse, List.length_range'] at h1
      simp [List.getElem_reverse]
      omega
    have hs := crossLs_cons_shift x₀ (x ++ [c] ++ y) (List.range' 0 x.length).reverse
    rw [List.length_cons, hr, crossLs_append, applyW_append]
    simp only [List.cons_append] at hs ⊢
    rw [hs.1, hs.2, ih.1, ih.2]
    have hd : (x₀ :: ([c] ++ x ++ y)).drop 0 = x₀ :: c :: (x ++ y) := by simp
    refine ⟨?_, ?_⟩
    · simp only [crossLs_cons, crossLs_nil, List.append_nil, crossAt_eq hd]
      simp [leftRunLs, ups]
    · simp only [applyW_cons, applyW_nil, swapAt_eq hd]
      simp

theorem sChain_leftRunLs (x : List I) (c : I) (y : List I) :
    SChain (ups (x ++ [c] ++ y)) (leftRunLs x c y) (ups ([c] ++ x ++ y)) := by
  have := sChain_crossLs (x ++ [c] ++ y) (List.range' 0 x.length).reverse
  rwa [(crossLs_leftRun x c y).1, (crossLs_leftRun x c y).2] at this

theorem upward_leftRunLs (x : List I) (c : I) (y : List I) : Upward (leftRunLs x c y) := by
  rw [← (crossLs_leftRun x c y).1]; exact upward_crossLs _ _

end Shift

/-! ## Closing the first strand on the left -/

section CloseLeft

variable (μ : X) (j : I)

/-- The left closure of the first strand `E_j` of the layers `M` (from `[E_j] ++ s` to
`[E_j] ++ t`), with `e` dots on the closed strand at the top: the cup `1 → F_j E_j` on the
left, `M`, `e` dots, the cap `F_j E_j → 1`. -/
def closeLsL (s t : List (Letter I)) (M : List (LayerData I)) (e : ℕ) : List (LayerData I) :=
  [([], .cup (dn j), s)] ++ M.map (whL [dn j] []) ++ List.replicate e ([dn j], .dot (up j), t) ++
    [([], .cap (up j), t)]

variable {j} in
theorem sChain_closeLsL {s t : List (Letter I)} {M : List (LayerData I)}
    (hM : SChain ([up j] ++ s) M ([up j] ++ t)) (e : ℕ) : SChain s (closeLsL j s t M e) t := by
  have h1 : SChain s [([], .cup (dn j), s)] ([dn j] ++ ([up j] ++ s)) := ⟨by simp, by simp⟩
  have h2 := hM.whisk [dn j] []
  simp only [List.append_nil] at h2
  have h3 : SChain ([dn j] ++ ([up j] ++ t)) (List.replicate e ([dn j], .dot (up j), t))
      ([dn j] ++ ([up j] ++ t)) :=
    SChain.replicate_of (x := ([dn j], Shape.dot (up j), t)) ⟨by simp, by simp⟩ e
  have h4 : SChain ([dn j] ++ ([up j] ++ t)) [([], .cap (up j), t)] t := ⟨by simp, by simp⟩
  exact ((h1.append h2).append h3).append h4

/-- Upward layers not involving the closed strand leave the closure, below. -/
theorem dg_closeLsL_peel {s s' t : List (Letter I)} (L M : List (LayerData I))
    (hL : SChain s L s') (hM : SChain ([up j] ++ s') M ([up j] ++ t)) (e : ℕ) :
    dg RD k μ s t (closeLsL j s t (L.map (whL [up j] []) ++ M) e) =
      dg RD k μ s s' L ≫ dg RD k μ s' t (closeLsL j s' t M e) := by
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t) []
    (M.map (whL [dn j] []) ++ List.replicate e ([dn j], .dot (up j), t) ++ [([], .cap (up j), t)])
    (A := [([], .cup (dn j), [])]) (s := []) (s' := [dn j, up j]) (by schain) hL
  rw [dg_comp hL (sChain_closeLsL hM e)]
  unfold closeLsL
  wnf at ei ⊢
  rw [ei]

/-- Upward layers not involving the closed strand leave the closure, above. -/
theorem dg_closeLsL_peel_top {s t t' : List (Letter I)} (M P : List (LayerData I))
    (hM : SChain ([up j] ++ s) M ([up j] ++ t')) (hP : SChain t' P t) :
    dg RD k μ s t (closeLsL j s t (M ++ P.map (whL [up j] [])) 0) =
      dg RD k μ s t' (closeLsL j s t' M 0) ≫ dg RD k μ t' t P := by
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
    ([([], .cup (dn j), s)] ++ M.map (whL [dn j] [])) []
    (A := [([], .cap (up j), [])]) (s := [dn j, up j]) (s' := []) (by schain) hP
  rw [dg_comp (sChain_closeLsL hM 0) hP]
  unfold closeLsL
  simp only [List.replicate_zero, List.append_nil] at ei ⊢
  wnf at ei ⊢
  rw [← ei]

/-- A dot on the closed strand at the bottom moves around the closure to the top. -/
theorem dg_closeLsL_rotate {s t : List (Letter I)} (M : List (LayerData I))
    (hM : SChain ([up j] ++ s) M ([up j] ++ t)) (e : ℕ) :
    dg RD k μ s t (closeLsL j s t (([], .dot (up j), s) :: M) e) =
      dg RD k μ s t (closeLsL j s t M (e + 1)) := by
  have hM' : SChain (dn j :: up j :: s) (M.map (whL [dn j] [])) (dn j :: up j :: t) := by
    simpa using hM.whisk [dn j] []
  have hdots : SChain (dn j :: up j :: t) (List.replicate e ([dn j], .dot (up j), t))
      (dn j :: up j :: t) :=
    SChain.replicate_of (x := ([dn j], Shape.dot (up j), t)) ⟨by simp, by simp⟩ e
  have hcap : SChain (dn j :: up j :: t) [([], .cap (up j), t)] t := ⟨by simp, by simp⟩
  unfold closeLsL
  -- the dot moves from the upward leg of the cup to its downward leg
  refine (dg_step RD k μ (s₀ := s) (t₀ := t) []
    (M.map (whL [dn j] []) ++ List.replicate e ([dn j], .dot (up j), t) ++ [([], .cap (up j), t)])
    [] s (dg_dot_cupDn RD k j (wt RD μ s)) (by simp)
    (by simpa using (hM'.append hdots).append hcap) (by simp [whL]) rfl).trans ?_
  -- past the layers of `M`
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
    [([], .cup (dn j), s)] (List.replicate e ([dn j], .dot (up j), t) ++ [([], .cap (up j), t)])
    (A := [([], .dot (dn j), [])]) (s := [dn j]) (s' := [dn j]) (by schain) hM
  wnf at ei ⊢
  rw [ei]
  -- past the dots on the closed strand
  have hpre : SChain s (([], .cup (dn j), s) :: M.map (whL [dn j] [])) (dn j :: up j :: t) :=
    (show SChain s [([], .cup (dn j), s)] (dn j :: up j :: s) from ⟨by simp, by simp⟩).append hM'
  refine (dg_step RD k μ (s₀ := s) (t₀ := t) (([], .cup (dn j), s) :: M.map (whL [dn j] []))
    [([], .cap (up j), t)] [] t (dg_swap_dots RD k (wt RD μ t) [] [] [] (dn j) (up j) e 1).symm
    (by simpa using hpre) (by simp) (by simp [whL]) rfl).trans ?_
  -- around the cap
  refine (dg_step RD k μ (s₀ := s) (t₀ := t) ((([], .cup (dn j), s) :: M.map (whL [dn j] [])) ++
    List.replicate e ([dn j], .dot (up j), t)) [] [] t (dg_dot_cap_up RD k (wt RD μ t) j)
    (by simpa using hpre.append hdots) (by simp) (by simp [whL]) rfl).trans ?_
  simp [whL, List.replicate_succ']

theorem dg_closeLsL_nil (s : List (Letter I)) (e : ℕ) :
    dg RD k μ s s (closeLsL j s s [] e) =
      plcL RD k μ [] s [] [] (dg RD k (wt RD μ s) [] [] (ccwLs j e)) := by
  rw [plcL_dg]
  simp [closeLsL, ccwLs, whL]

/-- The layers of the left curl on `E_j` with `e` dots on its loop. -/
def curlLLs (e : ℕ) : List (LayerData I) :=
  [([], .cup (dn j), [up j]), ([dn j], .cross true j j, [])] ++
    List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])]

theorem sChain_curlLLs (e : ℕ) : SChain [up j] (curlLLs j e) [up j] := by
  unfold curlLLs; schain

theorem dg_closeLsL_curl (s₁ : List (Letter I)) (e : ℕ) :
    dg RD k μ ([] ++ [up j] ++ s₁) ([] ++ [up j] ++ s₁)
      (closeLsL j ([up j] ++ s₁) ([up j] ++ s₁) [([], .cross true j j, s₁)] e) =
      plcL RD k μ [] s₁ [up j] [up j] (dg RD k (wt RD μ s₁) [up j] [up j] (curlLLs j e)) := by
  rw [plcL_dg]
  simp [closeLsL, curlLLs, whL]

theorem dotsU_mem_slideSetL (ν : X) (l : Letter I) (a : ℕ) : dotsU RD k ν l a ∈ slideSetL RD k ν l := by
  have := mem_slideSetL (RD := RD) (k := k) (μ := ν) (l := l) (a := a) IsBub.id
  rwa [bubLU_id, Category.comp_id] at this

/-- The counterclockwise bubble with `e` dots to the left of `E_j`. -/
theorem dg_ccw_left (ν : X) (e : ℕ) :
    dg RD k ν [up j] [up j] ([([], .cup (dn j), [up j])] ++
        List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])]) =
      bubLU RD k ν (up j) (ccwU RD k (wt RD ν [up j]) j e) := by
  rw [ccwU_of_nonneg, bubLU, plcL_dg]
  simp [ccwLs, whL]

/-- **The left curl with dots on its loop** is a linear combination of bubble monomials to the
left of the strand times dots (the left curl relation and the nilHecke relation). -/
theorem curlL_mem_slideSetL (ν : X) (e : ℕ) :
    dg RD k ν [up j] [up j] (curlLLs j e) ∈ slideSetL RD k ν (up j) := by
  induction e with
  | zero =>
    have h := dg_curlL RD k j ν
    rw [show curlLLs j 0 = [([], .cup (dn j), [up j]), ([dn j], .cross true j j, []),
      ([], .cap (up j), [up j])] from rfl, h]
    exact Submodule.sum_mem _ fun g _ => mem_slideSetL' (ccwU_isBub _ _)
  | succ e ih =>
    have E : dg RD k ν [up j, up j] [up j, up j]
        [([], .cross true j j, []), ([], .dot (up j), [up j])] =
        dg RD k ν [up j, up j] [up j, up j]
          [([up j], .dot (up j), []), ([], .cross true j j, [])] +
        dg RD k ν [up j, up j] [up j, up j] [] := dg_slideLEq RD k ν j
    have key := dg_stepL RD k ν (s₀ := [up j]) (t₀ := [up j])
      [([], .cup (dn j), [up j])]
      (List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])]) [dn j] []
      (L := curlLLs j (e + 1)) E (by schain) (by schain)
      (by simp [curlLLs, whL, List.replicate_succ])
    rw [key, map_add, ctxL_dg_nil RD k ν (by schain) (by schain),
      ctxL_dg_nil RD k ν (by schain) (by schain)]
    simp only [whL, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.singleton_append, List.append_assoc, List.append_nil]
    refine add_mem ?_ ?_
    · have e2 : dg RD k ν [up j] [up j] (([], .cup (dn j), [up j]) ::
          ([dn j, up j], .dot (up j), []) :: ([dn j], .cross true j j, []) ::
            (List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])])) =
          dotsU RD k ν (up j) 1 ≫ dg RD k ν [up j] [up j] (curlLLs j e) := by
        rw [dotsU, dg_comp (by schain) (sChain_curlLLs j e)]
        dstep [] (([dn j], .cross true j j, []) ::
            (List.replicate e ([dn j], .dot (up j), [up j]) ++ [([], .cap (up j), [up j])])) [] []
          (dg_swap' RD k (wt RD (wt RD ν []) []) [] [] [] (.cup (dn j)) (.dot (up j)))
        simp [curlLLs]
      rw [e2]
      exact slideSetL_comp (dotsU_mem_slideSetL RD k ν _ 1) ih
    · have hm := mem_slideSetL_bub (RD := RD) (k := k) (μ := ν) (l := up j)
        (ccwU_isBub (RD := RD) (k := k) (lam := wt RD ν [up j]) j e)
      rw [← dg_ccw_left] at hm
      exact hm

end CloseLeft

/-! ## Placing dots and bubbles to the left of upward strands -/

section PlaceLeft

variable (μ : X)

theorem plcL_bubLU_eq_ctxL (s₁ : List (Letter I)) (c : I)
    (δ : End ((pres RD k).obj (ob RD (wt RD (wt RD μ s₁) [up c]) []))) :
    plcL RD k μ [] s₁ [up c] [up c] (bubLU RD k (wt RD μ s₁) (up c) δ) =
      ctxL RD k μ (up c :: s₁) (up c :: s₁) [] [] (up c :: s₁) [] [] [] δ := by
  have key := hom_ext_dg RD k (wt RD (wt RD μ s₁) [up c]) (s := []) (t := [])
    ((plcL RD k μ [] s₁ [up c] [up c]).comp (plcL RD k (wt RD μ s₁) [] [up c] [] []))
    (ctxL RD k μ (up c :: s₁) (up c :: s₁) [] [] (up c :: s₁) [] [] []) (fun B hB => ?_)
  · exact LinearMap.congr_fun key δ
  change plcL RD k μ [] s₁ [up c] [up c] (plcL RD k (wt RD μ s₁) [] [up c] [] []
    (dg RD k (wt RD (wt RD μ s₁) [up c]) [] [] B)) =
    ctxL RD k μ (up c :: s₁) (up c :: s₁) [] [] (up c :: s₁) [] [] []
      (dg RD k (wt RD μ (up c :: s₁)) [] [] B)
  rw [plcL_dg]
  simp only [List.nil_append]
  erw [plcL_dg]
  rw [ctxL_dg RD k μ (s := []) (t := []) (by simp) (by simp)]
  simp only [List.nil_append, List.append_nil, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨a', g, b'⟩ := x
  simp [whL]

variable {RD k}

/-- Dots on the first strand and bubble monomials to its left, placed to the left of the upward
strands `s₁`, lie in `upSpan` (the bubbles slide to the far right, `slideOutUp`). -/
theorem plcL_slideSetL_mem_upSpan (hSL : SimplyLaced C) (s₁ : List (Letter I))
    (hs₁ : Positive s₁) (c : I) {f : End ((pres RD k).obj (ob RD (wt RD μ s₁) [up c]))}
    (hf : f ∈ slideSetL RD k (wt RD μ s₁) (up c)) :
    plcL RD k μ [] s₁ [up c] [up c] f ∈ upSpan RD k μ (up c :: s₁) (up c :: s₁) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, δ, hδ, rfl⟩ := hf
    rw [← plcL_comp RD k μ [] s₁ rfl rfl, plcL_bubLU_eq_ctxL, dotsU, plcL_dg]
    have hrep : SChain [up c] (List.replicate a ([], .dot (up c), [])) [up c] :=
      SChain.replicate_of (by schain) a
    have hrep' : SChain (up c :: s₁) ((List.replicate a ([], .dot (up c), [])).map (whL [] s₁))
        (up c :: s₁) := by simpa using hrep.whisk [] s₁
    refine upSpan_comp_left (fun x hx => ?_) hrep' ?_
    · rw [List.map_replicate] at hx
      rw [List.eq_of_mem_replicate hx]; rfl
    · refine slideOutUp RD k μ hSL (up c :: s₁) [] [] [] (by simp) (by simp)
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
    ((pres RD k).obj (ob RD (wt RD μ []) ([up j] ++ a)) ⟶
      (pres RD k).obj (ob RD (wt RD μ []) ([up j] ++ b))) →ₗ[k]
      ((pres RD k).obj (ob RD μ a) ⟶ (pres RD k).obj (ob RD μ b)) where
  toFun f := dg RD k μ a ([dn j] ++ ([up j] ++ a) ++ []) [([], .cup (dn j), a)] ≫
    plcL RD k μ [dn j] [] ([up j] ++ a) ([up j] ++ b) f ≫
      dg RD k μ ([dn j] ++ ([up j] ++ b) ++ []) b [([], .cap (up j), b)]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ptrFirst_dg (a b : List (Letter I)) (j : I) (A : List (LayerData I)) :
    ptrFirst RD k μ a b j (dg RD k (wt RD μ []) ([up j] ++ a) ([up j] ++ b) A) =
      dg RD k μ a b (closeLsL j a b A 0) := by
  show dg RD k μ a _ _ ≫ plcL RD k μ [dn j] [] _ _ (dg RD k (wt RD μ []) _ _ A) ≫ _ = _
  rw [plcL_dg]
  have h1 : SChain a [([], .cup (dn j), a)] ([dn j] ++ ([up j] ++ a) ++ []) := ⟨by simp, by simp⟩
  have h3 : SChain ([dn j] ++ ([up j] ++ b) ++ []) [([], .cap (up j), b)] b := ⟨by simp, by simp⟩
  by_cases hA : SChain ([up j] ++ a) A ([up j] ++ b)
  · have h2 := hA.whisk [dn j] []
    rw [dg_comp h2 h3, dg_comp h1 (h2.append h3)]
    simp [closeLsL]
  · rw [dg_of_not (fun h => hA h.of_whisk), Limits.zero_comp, Limits.comp_zero, dg_of_not]
    intro h
    unfold closeLsL at h
    simp only [List.replicate_zero, List.append_nil] at h
    obtain ⟨m₂, h₁₂, h₃'⟩ := SChain.split h
    obtain ⟨m₁, h₁', h₂'⟩ := SChain.split h₁₂
    obtain rfl := h₁'.eq_target h1
    obtain rfl := h₃'.eq_source h3
    exact hA h₂'.of_whisk

variable {RD k} (j : I)

/-- Dots at the bottom of a left closure leave it (or move around it to the top). -/
theorem closeLsL_dots_mem {s t : List (Letter I)} (N : List (LayerData I))
    (hN : SChain ([up j] ++ s) N ([up j] ++ t))
    (hbase : ∀ e, dg RD k μ s t (closeLsL j s t N e) ∈ upSpan RD k μ s t) :
    ∀ (Dl : List (LayerData I)), DotsOnly Dl → SChain ([up j] ++ s) Dl ([up j] ++ s) →
      ∀ e, dg RD k μ s t (closeLsL j s t (Dl ++ N) e) ∈ upSpan RD k μ s t := by
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
      rw [List.cons_append, dg_closeLsL_rotate RD k μ j _ (hDc'.append hN)]
      exact ih hD' hDc' (e + 1)
    · -- a dot on another strand: it leaves the closure
      simp only [List.singleton_append, List.cons_append, List.cons.injEq] at h₀
      obtain ⟨rfl, hs⟩ := h₀
      have hd : SChain s [(u, Shape.dot l, v)] s := ⟨hs, hs.symm⟩
      have hform : ((up j :: u, Shape.dot l, v) :: Dl) ++ N =
          [(u, Shape.dot l, v)].map (whL [up j] []) ++ (Dl ++ N) := by simp [whL]
      rw [hform, dg_closeLsL_peel RD k μ j _ _ hd (hDc'.append hN)]
      refine upSpan_comp_left (fun x hx => ?_) hd (ih hD' hDc' e)
      rw [List.mem_singleton.1 hx]; exact hl

variable (hSL : SimplyLaced C)
include hSL

theorem closeLsL_nil_mem (s : List (Letter I)) (hs : Positive s) (e : ℕ) :
    dg RD k μ s s (closeLsL j s s [] e) ∈ upSpan RD k μ s s := by
  rw [dg_closeLsL_nil]
  have hc : plcL RD k μ [] s [] [] (dg RD k (wt RD μ s) [] [] (ccwLs j e)) =
      ctxL RD k μ s s [] [] s [] [] [] (dg RD k (wt RD μ s) [] [] (ccwLs j e)) := by
    show _ = dg RD k μ s s [] ≫ plcL RD k μ [] s [] [] _ ≫ dg RD k μ s s []
    rw [dg_nil]
    erw [Category.id_comp, Category.comp_id]
  rw [hc]
  refine slideOutUp RD k μ hSL s [] [] [] (by simp) (by simp) (fun x hx => by simp at hx)
    (fun x hx => by simp at hx) hs _ ?_
  rw [← ccwU_of_nonneg]
  exact ccwU_isBub _ _

variable [DecidableEq I]

/-- **The left Markov lemma**: closing the first strand of an upward diagram on its left gives a
linear combination of upward diagrams followed by bubble monomials on the far right. -/
theorem ptrFirst_upward_mem_upSpan (a b : List I) {A : List (LayerData I)} (hA : Upward A)
    (h : SChain ([up j] ++ ups a) A ([up j] ++ ups b)) :
    ptrFirst RD k μ (ups a) (ups b) j
      (dg RD k (wt RD μ []) ([up j] ++ ups a) ([up j] ++ ups b) A) ∈ upSpan RD k μ (ups a) (ups b) := by
  have hperm : ([j] ++ a).Perm ([j] ++ b) := upward_perm hA (by simpa [ups] using h)
  set ν : Multiset I := (([j] ++ a : List I) : Multiset I)
  let i := seqOfEq ν ([j] ++ a) rfl
  let i' := seqOfEq ν ([j] ++ b) (Multiset.coe_eq_coe.2 hperm.symm)
  have hi : KLR.Diagram.word i = [j] ++ a := word_seqOfEq _ _ _
  have hi' : KLR.Diagram.word i' = [j] ++ b := word_seqOfEq _ _ _
  have hm : Multiset.card ν = a.length + 1 := by simp [ν, add_comm]
  have hmem := upward_mem_span_nf' RD k (wt RD μ []) (canWordL (Multiset.card ν))
    (fun w => ⟨isReduced_canWordL _ w, wordProd_canWordL _ w⟩) i i'
    (S := [up j] ++ ups a) (T := [up j] ++ ups b) (by rw [hi]; simp [ups])
    (by rw [hi']; simp [ups]) hA h
  refine (Submodule.span_le (p := (upSpan RD k μ (ups a) (ups b)).comap
    (ptrFirst RD k μ (ups a) (ups b) j))).mpr ?_ hmem
  rintro _ ⟨w, D, hw, hD, rfl⟩
  show ptrFirst RD k μ (ups a) (ups b) j (D ≫ _) ∈ upSpan RD k μ (ups a) (ups b)
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
      dg RD k μ (ups a) (ups (x ++ y)) (closeLsL j (ups a) (ups (x ++ y)) (Dl ++ leftRunLs x j y) 0) ∈
        upSpan RD k μ (ups a) (ups (x ++ y)) := by
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
      exact closeLsL_nil_mem μ j hSL (ups a) (positive_ups a) e
    · -- a run followed by a left curl
      rw [hxz] at hsplit
      simp only [List.singleton_append, List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨hj, ha⟩ := hsplit
      subst hj
      have ha' : a = x' ++ [j] ++ y := by simpa using ha
      have hL := sChain_leftRunLs x' j y
      have hcore : SChain ([up j] ++ ups ([j] ++ x' ++ y))
          [([], .cross true j j, ups (x' ++ y))] ([up j] ++ ups (j :: x' ++ y)) :=
        ⟨by simp [ups], by simp [ups]⟩
      simp only [leftRunLs]
      rw [ha', dg_closeLsL_peel RD k μ j _ _ hL hcore]
      refine upSpan_comp_left (upward_leftRunLs x' j y) hL ?_
      have hm := plcL_slideSetL_mem_upSpan μ hSL (ups (x' ++ y)) (positive_ups _) j
        (curlL_mem_slideSetL RD k j (wt RD μ (ups (x' ++ y))) e)
      rw [← dg_closeLsL_curl] at hm
      exact dg_mem_upSpan_congr RD k μ (by simp [ups]) (by simp [ups]) hm
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
    rw [dg_comp hDlc hC, ptrFirst_dg, hcross, ← List.append_assoc,
      dg_closeLsL_peel_top RD k μ j _ _ (hDlc.append hR) hP]
    exact upSpan_comp_right (upward_crossLs _ _) hP (hclosed Dl hDl hDlc)
  | zero => rw [Limits.zero_comp, map_zero]; exact Submodule.zero_mem _
  | add D₁ D₂ _ _ h₁ h₂ => rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul r D _ hD' => rw [Linear.smul_comp, map_smul]; exact Submodule.smul_mem _ r hD'

omit hSL [DecidableEq I] in
/-- A bubble monomial on the far right stays outside the left closure. -/
theorem ptrFirst_bubAt {s t : List (Letter I)} (A : List (LayerData I))
    (hA : SChain ([up j] ++ s) A ([up j] ++ t)) (γ : End ((pres RD k).obj (ob RD μ []))) :
    ptrFirst RD k μ s t j (dg RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A ≫
        bubAt RD k (wt RD μ []) ([up j] ++ t) γ) =
      ptrFirst RD k μ s t j (dg RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A) ≫
        bubAt RD k μ t γ := by
  have key := hom_ext_dg RD k μ (s := []) (t := [])
    ((ptrFirst RD k μ s t j).comp ((Linear.leftComp k _
      (dg RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A)).comp
        (bubAt RD k (wt RD μ []) ([up j] ++ t))))
    ((Linear.leftComp k _ (ptrFirst RD k μ s t j
      (dg RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A))).comp (bubAt RD k μ t))
    (fun B hB => ?_)
  · exact LinearMap.congr_fun key γ
  change ptrFirst RD k μ s t j (dg RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A ≫
      bubAt RD k (wt RD μ []) ([up j] ++ t) (dg RD k (wt RD μ []) [] [] B)) =
    ptrFirst RD k μ s t j (dg RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t) A) ≫
      bubAt RD k μ t (dg RD k μ [] [] B)
  have hB1 : SChain ([up j] ++ t) (B.map (whL ([up j] ++ t) [])) ([up j] ++ t) := by
    simpa using hB.whisk ([up j] ++ t) []
  have hBt : SChain t (B.map (whL t [])) t := by simpa using hB.whisk t []
  rw [bubAt_dg, bubAt_dg, dg_comp hA hB1]
  rw [ptrFirst_dg, ptrFirst_dg, dg_comp (sChain_closeLsL hA 0) hBt]
  have e := dg_closed_left (RD := RD) (k := k) μ (S := s) (T := t)
    ([([], .cup (dn j), s)] ++ A.map (whL [dn j] [])) [] (s := [dn j, up j] ++ t) (s' := t) []
    hB (A := [([], .cap (up j), t)]) ⟨by simp, by simp⟩
  unfold closeLsL
  wnf at e ⊢
  simp only [List.replicate_zero, List.nil_append, List.append_nil] at e ⊢
  exact e.symm

/-- **The left partial trace preserves `upSpan`.** -/
theorem ptrFirst_mem_upSpan (a b : List I) {f}
    (hf : f ∈ upSpan RD k (wt RD μ []) ([up j] ++ ups a) ([up j] ++ ups b)) :
    ptrFirst RD k μ (ups a) (ups b) j f ∈ upSpan RD k μ (ups a) (ups b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    rw [ptrFirst_bubAt (RD := RD) (k := k) μ j A h γ]
    have hM := ptrFirst_upward_mem_upSpan (RD := RD) (k := k) μ j hSL a b hA h
    generalize ptrFirst RD k μ (ups a) (ups b) j
      (dg RD k (wt RD μ []) ([up j] ++ ups a) ([up j] ++ ups b) A) = F at hM ⊢
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


end Categorification.KL3.Diagram
