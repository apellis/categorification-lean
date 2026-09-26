/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Reduction

/-!
# Normal forms of upward diagrams in `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1 (the
relations of `R(ν)` on upward strands) and M. Khovanov, A. Lauda, *A diagrammatic approach to
categorification of quantum groups I*, arXiv:0803.4121v2, Theorem 2.5 (spanning half).

The basis theorem of KL I says that `R(ν)` is spanned by the elements `ψ_{ρ w} x^u e_i`, for any
choice of reduced words `ρ w`. Transported to `U` along `toUEnd`
(`Categorification.Diagrams.KL3.Upward`), it says that every upward diagram of `U` between the
sequences `i` and `j` is a linear combination of *normal-form* upward diagrams: dots at the bottom,
followed by the crossings of a reduced word (`upward_mem_span_nf`).

## Main definitions

* `crossAt w t`, `crossLs w σ`: the upward crossings at the positions `σ` (the head of `σ` at the
  bottom), starting from the colours `w`; `applyW w σ` is the resulting sequence of colours.
* `DotsOnly`: a list of layers of upward dots.

## Main results

* `toUEnd_ψw_apply`: the entries of the image of `ψ_σ` in `END_U(E_ν 1_μ)` are the diagrams
  `crossLs (word i) σ.reverse`.
* `toUEnd_pol_mul_e`: the image of `p(x) e_i` is a linear combination of dots.
* `upward_mem_span_nf`: every upward diagram from `E_i 1_μ` to `E_j 1_μ` is a linear
  combination of diagrams `D ++ crossLs (word i) (ρ w).reverse`, `D` dots, for any choice of
  reduced words `ρ`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Crossings at given positions -/

section CrossLs

/-- The colours `w` with the entries at the positions `t`, `t + 1` exchanged (unchanged if `t + 1`
is out of range). -/
def swapAt (w : List I) (t : ℕ) : List I :=
  match w.drop t with
  | c :: d :: r => w.take t ++ d :: c :: r
  | _ => w

/-- The upward crossing at the positions `t`, `t + 1` of the colours `w`, as a list of layer data
(empty if `t + 1` is out of range). -/
def crossAt (w : List I) (t : ℕ) : List (LayerData I) :=
  match w.drop t with
  | c :: d :: r => [(ups (w.take t), .cross true c d, ups r)]
  | _ => []

/-- The colours after the crossings at the positions `σ` (the head of `σ` first). -/
def applyW : List I → List ℕ → List I
  | w, [] => w
  | w, t :: σ => applyW (swapAt w t) σ

/-- The upward crossings at the positions `σ` (the head of `σ` at the bottom), starting from the
colours `w`. -/
def crossLs : List I → List ℕ → List (LayerData I)
  | _, [] => []
  | w, t :: σ => crossAt w t ++ crossLs (swapAt w t) σ

@[simp] theorem applyW_nil (w : List I) : applyW w [] = w := rfl
@[simp] theorem applyW_cons (w : List I) (t : ℕ) (σ : List ℕ) :
    applyW w (t :: σ) = applyW (swapAt w t) σ := rfl
@[simp] theorem crossLs_nil (w : List I) : crossLs w [] = [] := rfl
@[simp] theorem crossLs_cons (w : List I) (t : ℕ) (σ : List ℕ) :
    crossLs w (t :: σ) = crossAt w t ++ crossLs (swapAt w t) σ := rfl

theorem applyW_append (w : List I) (σ τ : List ℕ) :
    applyW w (σ ++ τ) = applyW (applyW w σ) τ := by
  induction σ generalizing w with
  | nil => rfl
  | cons t σ ih => exact ih _

theorem crossLs_append (w : List I) (σ τ : List ℕ) :
    crossLs w (σ ++ τ) = crossLs w σ ++ crossLs (applyW w σ) τ := by
  induction σ generalizing w with
  | nil => rfl
  | cons t σ ih => simp [ih]

theorem swapAt_eq {w : List I} {t : ℕ} {c d : I} {r : List I} (h : w.drop t = c :: d :: r) :
    swapAt w t = w.take t ++ d :: c :: r := by
  unfold swapAt; rw [h]

theorem crossAt_eq {w : List I} {t : ℕ} {c d : I} {r : List I} (h : w.drop t = c :: d :: r) :
    crossAt w t = [(ups (w.take t), .cross true c d, ups r)] := by
  unfold crossAt; rw [h]

theorem swapAt_of_le {w : List I} {t : ℕ} (h : w.length ≤ t + 1) : swapAt w t = w := by
  unfold swapAt
  split
  · rename_i c d r hd
    have := congrArg List.length hd
    simp at this; omega
  · rfl

theorem crossAt_of_le {w : List I} {t : ℕ} (h : w.length ≤ t + 1) : crossAt w t = [] := by
  unfold crossAt
  split
  · rename_i c d r hd
    have := congrArg List.length hd
    simp at this; omega
  · rfl

theorem drop_eq_cons_cons {w : List I} {t : ℕ} (h : t + 1 < w.length) :
    ∃ c d r, w.drop t = c :: d :: r := by
  rcases hw : w.drop t with _ | ⟨c, _ | ⟨d, r⟩⟩
  · have := congrArg List.length hw; simp at this; omega
  · have := congrArg List.length hw; simp at this; omega
  · exact ⟨c, d, r, rfl⟩

theorem length_swapAt (w : List I) (t : ℕ) : (swapAt w t).length = w.length := by
  by_cases h : t + 1 < w.length
  · obtain ⟨c, d, r, hd⟩ := drop_eq_cons_cons h
    rw [swapAt_eq hd]
    have := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at this
    simp only [List.length_append, List.length_take, List.length_cons]
    omega
  · rw [swapAt_of_le (by omega)]

theorem length_applyW (w : List I) (σ : List ℕ) : (applyW w σ).length = w.length := by
  induction σ generalizing w with
  | nil => rfl
  | cons t σ ih => rw [applyW_cons, ih, length_swapAt]

theorem sChain_crossAt (w : List I) (t : ℕ) :
    SChain (ups w) (crossAt w t) (ups (swapAt w t)) := by
  by_cases h : t + 1 < w.length
  · obtain ⟨c, d, r, hd⟩ := drop_eq_cons_cons h
    rw [crossAt_eq hd, swapAt_eq hd]
    have hw : w = w.take t ++ c :: d :: r := by rw [← hd, List.take_append_drop]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [hw]
      simp [ups]
    · simp [ups]
  · rw [crossAt_of_le (by omega), swapAt_of_le (by omega)]; rfl

theorem sChain_crossLs (w : List I) (σ : List ℕ) :
    SChain (ups w) (crossLs w σ) (ups (applyW w σ)) := by
  induction σ generalizing w with
  | nil => rfl
  | cons t σ ih => exact (sChain_crossAt w t).append (ih _)

theorem upward_crossAt (w : List I) (t : ℕ) : Upward (crossAt w t) := by
  by_cases h : t + 1 < w.length
  · obtain ⟨c, d, r, hd⟩ := drop_eq_cons_cons h
    rw [crossAt_eq hd]
    intro x hx
    rw [List.mem_singleton.1 hx]; rfl
  · rw [crossAt_of_le (by omega)]; intro x hx; simp at hx

theorem upward_crossLs (w : List I) (σ : List ℕ) : Upward (crossLs w σ) := by
  induction σ generalizing w with
  | nil => intro x hx; simp at hx
  | cons t σ ih => exact (upward_crossAt w t).append (ih _)

/-! ## Runs -/

/-- The upward strand `c`, between the strands `x` and `y`, crossing all the strands of `y` to
become the last strand. -/
def runLs : List I → I → List I → List (LayerData I)
  | _, _, [] => []
  | x, c, d :: y => (ups x, .cross true c d, ups y) :: runLs (x ++ [d]) c y

theorem sChain_runLs (x : List I) (c : I) (y : List I) :
    SChain (ups (x ++ [c] ++ y)) (runLs x c y) (ups (x ++ y ++ [c])) := by
  induction y generalizing x with
  | nil => simp [runLs]
  | cons d y ih =>
    refine ⟨by simp [ups], ?_⟩
    have := ih (x ++ [d])
    simpa [ups] using this

theorem upward_runLs (x : List I) (c : I) (y : List I) : Upward (runLs x c y) := by
  induction y generalizing x with
  | nil => intro z hz; simp [runLs] at hz
  | cons d y ih =>
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · rfl
    · exact ih _ z hz

theorem runLs_append_single (x : List I) (c : I) (y : List I) (d : I) :
    runLs x c (y ++ [d]) = (runLs x c y).map (whL [] [up d]) ++ [(ups (x ++ y), .cross true c d, [])] := by
  induction y generalizing x with
  | nil => simp [runLs, whL]
  | cons e y ih => simp [runLs, ih, whL, ups]

/-- The crossings at the positions `|x|, |x| + 1, …` move the strand `c` to the end. -/
theorem crossLs_range' (x : List I) (c : I) (y : List I) :
    crossLs (x ++ [c] ++ y) (List.range' x.length y.length) = runLs x c y ∧
      applyW (x ++ [c] ++ y) (List.range' x.length y.length) = x ++ y ++ [c] := by
  induction y generalizing x with
  | nil => simp [runLs]
  | cons d y ih =>
    have hd : (x ++ [c] ++ d :: y).drop x.length = c :: d :: y := by simp
    rw [List.length_cons, List.range'_succ, crossLs_cons, applyW_cons, crossAt_eq hd,
      swapAt_eq hd]
    have e : (x ++ [c] ++ d :: y).take x.length ++ d :: c :: y = (x ++ [d]) ++ [c] ++ y := by simp
    have hx : (x ++ [d]).length = x.length + 1 := by simp
    rw [e, ← hx, (ih (x ++ [d])).1, (ih (x ++ [d])).2]
    simp [runLs]

theorem swapAt_append (w : List I) (z : List I) {t : ℕ} (ht : t + 1 < w.length) :
    swapAt (w ++ z) t = swapAt w t ++ z ∧
      crossAt (w ++ z) t = (crossAt w t).map (whL [] (ups z)) := by
  obtain ⟨c, d, r, hd⟩ := drop_eq_cons_cons ht
  have hd' : (w ++ z).drop t = c :: d :: (r ++ z) := by
    rw [List.drop_append_of_le_length (by omega), hd]; rfl
  have ht' : (w ++ z).take t = w.take t := List.take_append_of_le_length (by omega)
  rw [swapAt_eq hd', swapAt_eq hd, crossAt_eq hd', crossAt_eq hd, ht']
  simp [whL, ups]

/-- Crossings that do not involve the strands `z` on the right are whiskered by `z`. -/
theorem crossLs_append_right (w z : List I) (σ : List ℕ) (hσ : ∀ t ∈ σ, t + 1 < w.length) :
    crossLs (w ++ z) σ = (crossLs w σ).map (whL [] (ups z)) ∧
      applyW (w ++ z) σ = applyW w σ ++ z := by
  induction σ generalizing w with
  | nil => simp
  | cons t σ ih =>
    have ht := hσ t List.mem_cons_self
    obtain ⟨h1, h2⟩ := swapAt_append w z ht
    have hσ' : ∀ t' ∈ σ, t' + 1 < (swapAt w t).length := by
      rw [length_swapAt]; exact fun t' h' => hσ t' (List.mem_cons_of_mem _ h')
    rw [crossLs_cons, crossLs_cons, applyW_cons, applyW_cons, h1, h2, (ih _ hσ').1,
      (ih _ hσ').2, List.map_append]
    exact ⟨rfl, rfl⟩

end CrossLs

/-! ## Dots -/

/-- A list of layers of upward dots. -/
def DotsOnly (ls : List (LayerData I)) : Prop := ∀ x ∈ ls, ∃ l, x.2.1 = .dot l ∧ l.1 = true

theorem DotsOnly.append {a b : List (LayerData I)} (ha : DotsOnly a) (hb : DotsOnly b) :
    DotsOnly (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem DotsOnly.upward {a : List (LayerData I)} (ha : DotsOnly a) : Upward a := by
  intro x hx
  obtain ⟨l, h1, h2⟩ := ha x hx
  rw [h1]; exact h2

/-- The span of the classes of lists of dots, as endomorphisms of `E_s 1_μ`. -/
def dotSpan (μ : X) (s : List (Letter I)) : Submodule k (End ((pres RD k).obj (ob RD μ s))) :=
  Submodule.span k {f | ∃ D, DotsOnly D ∧ SChain s D s ∧ f = dg RD k μ s s D}

variable {RD k} in
theorem dotSpan_comp {μ : X} {s : List (Letter I)} {f g : End ((pres RD k).obj (ob RD μ s))}
    (hf : f ∈ dotSpan RD k μ s) (hg : g ∈ dotSpan RD k μ s) : f ≫ g ∈ dotSpan RD k μ s := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨D, hD, hDs, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨E, hE, hEs, rfl⟩ := hg
      exact Submodule.subset_span ⟨D ++ E, hD.append hE, hDs.append hEs, dg_comp hDs hEs⟩
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem id_mem_dotSpan (μ : X) (s : List (Letter I)) : 𝟙 _ ∈ dotSpan RD k μ s :=
  Submodule.subset_span ⟨[], fun _ h => by simp at h, rfl, (dg_nil μ s).symm⟩

/-! ## The right curl with dots on its loop -/

section Curl

variable (μ : X) (j : I)

/-- The layers of the right curl on `E_j` with `e` dots on its loop (on the strand that is
capped). -/
def curlLs (e : ℕ) : List (LayerData I) :=
  [([up j], .cup (up j), []), ([], .cross true j j, [dn j])] ++
    List.replicate e ([up j], .dot (up j), [dn j]) ++ [([up j], .cap (dn j), [])]

theorem sChain_curlLs (e : ℕ) : SChain [up j] (curlLs j e) [up j] := by
  unfold curlLs; schain

theorem dotsU_mem_slideSetR (l : Letter I) (a : ℕ) : dotsU RD k μ l a ∈ slideSetR RD k μ l := by
  have := mem_slideSetR (RD := RD) (k := k) (μ := μ) (l := l) (a := a) IsBub.id
  rwa [bubRU_id, Category.comp_id] at this

/-- A clockwise bubble with `e` dots on its upward strand, to the right of `E_j`. -/
theorem dg_cwE_right (e : ℕ) :
    dg RD k μ [up j] [up j] ([([up j], .cup (up j), [])] ++
        List.replicate e ([up j], .dot (up j), [dn j]) ++ [([up j], .cap (dn j), [])]) =
      bubRU RD k μ (up j) (cwU RD k μ j e) := by
  rw [cwU_of_nonneg, cwLs, dg_cw_dots, bubRU, plcL_dg_nil]
  simp [whL]

/-- **The right curl with dots on its loop** is a linear combination of dots on the strand
times bubbles to its right (the curl relation and the nilHecke relation). -/
theorem curl_mem_slideSetR (e : ℕ) :
    dg RD k μ [up j] [up j] (curlLs j e) ∈ slideSetR RD k μ (up j) := by
  induction e with
  | zero =>
    have h := dg_curlR RD k j μ
    rw [show curlLs j 0 = [([up j], .cup (up j), []), ([], .cross true j j, [dn j]),
      ([up j], .cap (dn j), [])] from rfl, h]
    refine neg_mem (Submodule.sum_mem _ fun f _ => mem_slideSetR' (cwU_isBub _ _))
  | succ e ih =>
    have E : dg RD k (wt RD μ [dn j]) [up j, up j] [up j, up j]
        [([], .cross true j j, []), ([up j], .dot (up j), [])] =
        dg RD k (wt RD μ [dn j]) [up j, up j] [up j, up j]
          [([], .dot (up j), [up j]), ([], .cross true j j, [])] -
        dg RD k (wt RD μ [dn j]) [up j, up j] [up j, up j] [] := by
      rw [dg_slideREq]; abel
    have key := dg_stepL RD k μ (s₀ := [up j]) (t₀ := [up j]) [([up j], .cup (up j), [])]
      (List.replicate e ([up j], .dot (up j), [dn j]) ++ [([up j], .cap (dn j), [])]) [] [dn j]
      (L := curlLs j (e + 1)) E (by schain) (by schain) (by simp [curlLs, whL, List.replicate_succ])
    rw [key, map_sub, ctxL_dg RD k μ (by schain) (by schain),
      ctxL_dg RD k μ (by schain) (by schain)]
    simp only [whL, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.singleton_append, List.append_assoc, List.append_nil]
    refine sub_mem ?_ ?_
    · have e2 : dg RD k μ [up j] [up j] (([up j], .cup (up j), []) ::
          ([], .dot (up j), [up j, dn j]) :: ([], .cross true j j, [dn j]) ::
            (List.replicate e ([up j], .dot (up j), [dn j]) ++ [([up j], .cap (dn j), [])])) =
          dotsU RD k μ (up j) 1 ≫ dg RD k μ [up j] [up j] (curlLs j e) := by
        rw [dotsU, dg_comp (by schain) (sChain_curlLs j e)]
        dstep [] (([], .cross true j j, [dn j]) ::
            (List.replicate e ([up j], .dot (up j), [dn j]) ++ [([up j], .cap (dn j), [])])) [] []
          (dg_swap' RD k (wt RD μ []) [] [] [] (.dot (up j)) (.cup (up j))).symm
        simp [curlLs]
      rw [e2]
      exact slideSetR_comp (dotsU_mem_slideSetR RD k μ _ 1) ih
    · have hm := mem_slideSetR_bub (RD := RD) (k := k) (μ := μ) (l := up j)
        (cwU_isBub (RD := RD) (k := k) (lam := μ) j e)
      rw [← dg_cwE_right] at hm
      exact hm

end Curl

/-! ## Placing dots and bubbles to the right of upward strands -/

/-- Dots and bubble monomials placed to the right of the upward strands `u` lie in `upSpan`. -/
theorem plcL_slideSetR_mem_upSpan (μ : X) (u : List (Letter I)) (c : I)
    {f : End ((pres RD k).obj (ob RD μ [up c]))} (hf : f ∈ slideSetR RD k μ (up c)) :
    plcL RD k μ u [] [up c] [up c] f ∈ upSpan RD k μ (u ++ [up c] ++ []) (u ++ [up c] ++ []) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    have key := hom_ext_dg RD k μ (s := []) (t := [])
      ((plcL RD k μ u [] [up c] [up c]).comp ((Linear.leftComp k _ (dotsU RD k μ (up c) a)).comp
        (plcL RD k μ [up c] [] [] [])))
      ((Linear.leftComp k _ (dg RD k μ (u ++ [up c] ++ []) (u ++ [up c] ++ [])
        ((List.replicate a ([], .dot (up c), [])).map (whL u [])))).comp
          (bubAt RD k μ (u ++ [up c] ++ [])))
      (fun B hB => ?_)
    · have e : plcL RD k μ u [] [up c] [up c] (dotsU RD k μ (up c) a ≫ bubRU RD k μ (up c) γ) =
          dg RD k μ (u ++ [up c] ++ []) (u ++ [up c] ++ [])
            ((List.replicate a ([], .dot (up c), [])).map (whL u [])) ≫
            bubAt RD k μ (u ++ [up c] ++ []) γ := LinearMap.congr_fun key γ
      rw [e]
      refine Submodule.subset_span ⟨(List.replicate a ([], .dot (up c), [])).map (whL u []),
        γ, ?_, ?_, hγ, rfl⟩
      · intro x hx
        rw [List.map_replicate] at hx
        rw [List.eq_of_mem_replicate hx]; rfl
      · rw [List.map_replicate]
        exact SChain.replicate_of ⟨by simp [whL], by simp [whL]⟩ a
    · change plcL RD k μ u [] [up c] [up c] (dotsU RD k μ (up c) a ≫
          plcL RD k μ [up c] [] [] [] (dg RD k μ [] [] B)) =
        dg RD k μ (u ++ [up c] ++ []) (u ++ [up c] ++ [])
            ((List.replicate a ([], .dot (up c), [])).map (whL u [])) ≫
          bubAt RD k μ (u ++ [up c] ++ []) (dg RD k μ [] [] B)
      have hrep : SChain [up c] (List.replicate a ([], .dot (up c), [])) [up c] :=
        SChain.replicate_of (by schain) a
      have hB' : SChain [up c] (B.map (whL [up c] [])) [up c] := by simpa using hB.whisk [up c] []
      have hrep' := hrep.whisk u []
      have hB'' := hB.whisk (u ++ [up c] ++ []) []
      simp only [List.append_nil] at hB''
      rw [plcL_dg_nil]
      show plcL RD k μ u [] [up c] [up c] (dg RD k μ [up c] [up c] _ ≫
        dg RD k μ [up c] [up c] (B.map (whL [up c] []))) = _
      rw [dg_comp hrep hB', plcL_dg_nil, bubAt_dg]
      rw [show u ++ [up c] ++ [] = u ++ [up c] from List.append_nil _] at hrep' ⊢
      rw [dg_comp hrep' hB'']
      simp only [whL, List.map_map, Function.comp_def, List.map_replicate, List.append_nil,
        List.nil_append, List.map_append]
      congr 2
      refine List.map_congr_left fun x _ => ?_
      obtain ⟨a', g, b'⟩ := x
      simp [whL]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-! ## Sequences from lists, and upward diagrams preserve colours -/

section SeqOfList

theorem ofFn_getElem_cast (w : List I) (n : ℕ) (h : n = w.length) :
    List.ofFn (fun t : Fin n => w[(t : ℕ)]'(h ▸ t.2)) = w := by
  subst h; exact List.ofFn_getElem w

/-- The sequence of weight `ν` with colours `w` (if `w` has weight `ν`). -/
def seqOfEq (ν : Multiset I) (w : List I) (h : (w : Multiset I) = ν) : KLR.Seq ν :=
  ⟨fun t => w[(t : ℕ)]'(by
      have h2 : Multiset.card ν = w.length := by rw [← h, Multiset.coe_card]
      exact h2 ▸ t.2), by
    subst h
    rw [Fin.univ_val_map, ofFn_getElem_cast w _ (Multiset.coe_card w)]⟩

theorem word_seqOfEq (ν : Multiset I) (w : List I) (h : (w : Multiset I) = ν) :
    KLR.Diagram.word (seqOfEq ν w h) = w := by
  subst h
  exact ofFn_getElem_cast w _ (Multiset.coe_card w)

/-- Upward diagrams permute the colours. -/
theorem upward_perm {a b : List I} {A : List (LayerData I)} (hA : Upward A)
    (h : SChain (ups a) A (ups b)) : a.Perm b := by
  induction A generalizing a with
  | nil =>
    have : ups a = ups b := h
    have hab : a = b := by
      have := congrArg (List.map Prod.snd) this
      simpa [ups, Function.comp_def] using this
    rw [hab]
  | cons x A ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨h₀, h⟩ := h
    have hg : g.isUp = true := hA _ List.mem_cons_self
    have hpos : Positive (u ++ g.cod ++ v) := by
      obtain ⟨-, hcod, -⟩ := upShape_dom_positive hg
      have hu : Positive (ups a) := positive_ups a
      rw [h₀] at hu
      intro l hl
      simp only [List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact hu l (by simp [hl])
      · exact hcod l hl
      · exact hu l (by simp [hl])
    have e : ups ((u ++ g.cod ++ v).map Prod.snd) = u ++ g.cod ++ v := ups_map_snd hpos
    have hA' : Upward A := fun y hy => hA y (List.mem_cons_of_mem _ hy)
    have hp := ih hA' (a := (u ++ g.cod ++ v).map Prod.snd) (by rw [e]; exact h)
    refine List.Perm.trans ?_ hp
    have ha : a = (u ++ g.dom ++ v).map Prod.snd := by
      have := congrArg (List.map Prod.snd) h₀
      simpa [ups, Function.comp_def] using this
    rw [ha]
    cases g with
    | dot l => rfl
    | cross ε c d =>
      simp only [Shape.dom_cross, Shape.cod_cross, List.map_append, List.map_cons, List.map_nil]
      exact List.Perm.append_right _ (List.Perm.append_left _ (List.Perm.swap _ _ _))
    | cup l => simp [Shape.isUp] at hg
    | cap l => simp [Shape.isUp] at hg

end SeqOfList

/-! ## Canonical words -/

theorem canWord_reverse_split (n m : ℕ) (hm : m = n + 1) (w : Equiv.Perm (Fin m)) :
    ∃ (b₀ : ℕ) (ρ' : List ℕ), b₀ ≤ n ∧ (∀ t ∈ ρ', t + 1 < n) ∧
      (TypeA.canWord m w).reverse = List.range' b₀ (n - b₀) ++ ρ' := by
  subst hm
  have hl := TypeA.length_code (n + 1) w
  have hc := TypeA.isCode_code (n + 1) w
  unfold TypeA.canWord
  generalize TypeA.code (n + 1) w = c at hl hc
  cases c with
  | nil =>
    simp only [List.length_nil] at hl
    refine ⟨0, [], by omega, by simp, ?_⟩
    simp [show n = 0 by omega]
  | cons b₀ c =>
    simp only [List.length_cons] at hl
    rw [TypeA.isCode_cons] at hc
    refine ⟨b₀, (TypeA.codeWord c).reverse, by omega, fun t ht => ?_, ?_⟩
    · have := TypeA.lt_of_mem_codeWord (List.mem_reverse.1 ht)
      omega
    · rw [TypeA.codeWord_cons, List.reverse_append, TypeA.descRun, List.reverse_reverse,
        show c.length + 1 - b₀ = n - b₀ by omega]

/-! ## Closing the last strand on the right -/

section Close

variable (μ : X) (j : I)

/-- The right closure of the last strand `E_j` of the layers `M` (from `s ++ [E_j]` to
`t ++ [E_j]`), with `e` dots on the closed strand at the top: the cup `1 → E_j F_j` on the right,
`M`, `e` dots, the cap `E_j F_j → 1`. -/
def closeLs (s t : List (Letter I)) (M : List (LayerData I)) (e : ℕ) : List (LayerData I) :=
  [(s, .cup (up j), [])] ++ M.map (whL [] [dn j]) ++ List.replicate e (t, .dot (up j), [dn j]) ++
    [(t, .cap (dn j), [])]

variable {j} in
theorem sChain_closeLs {s t : List (Letter I)} {M : List (LayerData I)}
    (hM : SChain (s ++ [up j]) M (t ++ [up j])) (e : ℕ) : SChain s (closeLs j s t M e) t := by
  have h1 : SChain s [(s, .cup (up j), [])] (s ++ [up j] ++ [dn j]) := ⟨by simp, by simp⟩
  have h2 := hM.whisk [] [dn j]
  simp only [List.nil_append] at h2
  have h3 : SChain (t ++ [up j] ++ [dn j]) (List.replicate e (t, .dot (up j), [dn j]))
      (t ++ [up j] ++ [dn j]) :=
    SChain.replicate_of (x := (t, Shape.dot (up j), [dn j])) ⟨by simp, by simp⟩ e
  have h4 : SChain (t ++ [up j] ++ [dn j]) [(t, .cap (dn j), [])] t := ⟨by simp, by simp⟩
  exact ((h1.append h2).append h3).append h4

/-- Upward layers below the closed strand leave the closure. -/
theorem dg_closeLs_peel {s s' t : List (Letter I)} (L M : List (LayerData I))
    (hL : SChain s L s') (hM : SChain (s' ++ [up j]) M (t ++ [up j])) (e : ℕ) :
    dg RD k μ s t (closeLs j s t (L.map (whL [] [up j]) ++ M) e) =
      dg RD k μ s s' L ≫ dg RD k μ s' t (closeLs j s' t M e) := by
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t) []
    (M.map (whL [] [dn j]) ++ List.replicate e (t, .dot (up j), [dn j]) ++ [(t, .cap (dn j), [])])
    hL (B := [([], .cup (up j), [])]) (t := []) (t' := [up j, dn j]) (by schain)
  rw [dg_comp hL (sChain_closeLs hM e)]
  unfold closeLs
  wnf at ei ⊢
  rw [← ei]

/-- Upward layers above the closed strand leave the closure. -/
theorem dg_closeLs_peel_top {s t t' : List (Letter I)} (M P : List (LayerData I))
    (hM : SChain (s ++ [up j]) M (t' ++ [up j])) (hP : SChain t' P t) :
    dg RD k μ s t (closeLs j s t (M ++ P.map (whL [] [up j])) 0) =
      dg RD k μ s t' (closeLs j s t' M 0) ≫ dg RD k μ t' t P := by
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
    ([(s, .cup (up j), [])] ++ M.map (whL [] [dn j])) [] hP (B := [([], .cap (dn j), [])])
    (t := [up j, dn j]) (t' := []) (by schain)
  rw [dg_comp (sChain_closeLs hM 0) hP]
  unfold closeLs
  simp only [List.replicate_zero, List.append_nil] at ei ⊢
  wnf at ei ⊢
  rw [ei]

/-- A dot on the closed strand at the bottom moves around the closure to the top. -/
theorem dg_closeLs_rotate {s t : List (Letter I)} (M : List (LayerData I))
    (hM : SChain (s ++ [up j]) M (t ++ [up j])) (e : ℕ) :
    dg RD k μ s t (closeLs j s t ((s, .dot (up j), []) :: M) e) =
      dg RD k μ s t (closeLs j s t M (e + 1)) := by
  have hM' : SChain (s ++ [up j, dn j]) (M.map (whL [] [dn j])) (t ++ [up j, dn j]) := by
    simpa using hM.whisk [] [dn j]
  have hdots : SChain (t ++ [up j, dn j]) (List.replicate e (t, .dot (up j), [dn j]))
      (t ++ [up j, dn j]) :=
    SChain.replicate_of (x := (t, Shape.dot (up j), [dn j])) ⟨by simp, by simp⟩ e
  have hcap : SChain (t ++ [up j, dn j]) [(t, .cap (dn j), [])] t := ⟨by simp, by simp⟩
  have hFdot : SChain (s ++ [up j, dn j]) [(s ++ [up j], .dot (dn j), [])] (s ++ [up j, dn j]) :=
    ⟨by simp, by simp⟩
  unfold closeLs
  -- the dot moves from the upward leg of the cup to its downward leg
  refine (dg_step RD k μ (s₀ := s) (t₀ := t) []
    (M.map (whL [] [dn j]) ++ List.replicate e (t, .dot (up j), [dn j]) ++ [(t, .cap (dn j), [])])
    s [] (dg_dot_cupUp RD k j (wt RD μ [])).symm (by simp)
    (by simpa using (hM'.append hdots).append hcap) (by simp [whL]) rfl).trans ?_
  -- past the layers of `M`
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
    [(s, .cup (up j), [])] (List.replicate e (t, .dot (up j), [dn j]) ++ [(t, .cap (dn j), [])])
    hM (B := [([], .dot (dn j), [])]) (t := [dn j]) (t' := [dn j]) (by schain)
  wnf at ei ⊢
  rw [← ei]
  -- past the dots on the closed strand
  have hpre : SChain s ((s, .cup (up j), []) :: M.map (whL [] [dn j])) (t ++ [up j, dn j]) :=
    (show SChain s [(s, .cup (up j), [])] (s ++ [up j, dn j]) from ⟨by simp, by simp⟩).append hM'
  refine (dg_step RD k μ (s₀ := s) (t₀ := t) ((s, .cup (up j), []) :: M.map (whL [] [dn j]))
    [(t, .cap (dn j), [])] t [] (dg_swap_dots RD k (wt RD μ []) [] [] [] (up j) (dn j) 1 e)
    (by simpa using hpre) (by simp) (by simp [whL]) rfl).trans ?_
  -- around the cap
  refine (dg_step RD k μ (s₀ := s) (t₀ := t) ((s, .cup (up j), []) :: M.map (whL [] [dn j]) ++
    List.replicate e (t, .dot (up j), [dn j])) [] t [] (dg_dot_cap_dn RD k (wt RD μ []) j)
    (by simp only [List.append_nil]; exact hpre.append hdots) (by simp) (by simp [whL]) rfl).trans ?_
  simp [whL, List.replicate_succ']

/-- The closure of dots on the closed strand only is a dotted clockwise bubble on the right. -/
theorem dg_closeLs_nil (s : List (Letter I)) (e : ℕ) :
    dg RD k μ s s (closeLs j s s [] e) = bubAt RD k μ s (cwU RD k μ j e) := by
  rw [cwU_of_nonneg, cwLs, dg_cw_dots, bubAt_dg]
  simp [closeLs, whL]

/-- The closure with one crossing of two strands `E_j` is a placed dotted curl. -/
theorem dg_closeLs_curl (s₁ : List (Letter I)) (e : ℕ) :
    dg RD k μ (s₁ ++ [up j] ++ []) (s₁ ++ [up j] ++ [])
      (closeLs j (s₁ ++ [up j]) (s₁ ++ [up j]) [(s₁, .cross true j j, [])] e) =
      plcL RD k μ s₁ [] [up j] [up j] (dg RD k μ [up j] [up j] (curlLs j e)) := by
  rw [plcL_dg_nil]
  simp [closeLs, curlLs, whL]

end Close

/-! ## `upSpan` is closed under composition with upward diagrams -/

section UpSpanComp

variable {RD k}

theorem upSpan_comp_left {μ : X} {s s' t : List (Letter I)} {L : List (LayerData I)}
    (hL : Upward L) (hLs : SChain s L s') {f} (hf : f ∈ upSpan RD k μ s' t) :
    dg RD k μ s s' L ≫ f ∈ upSpan RD k μ s t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    rw [← Category.assoc, dg_comp hLs h]
    exact Submodule.subset_span ⟨L ++ A, γ, hL.append hA, hLs.append h, hγ, rfl⟩
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx

theorem upSpan_comp_right {μ : X} {s t t' : List (Letter I)} {P : List (LayerData I)}
    (hP : Upward P) (hPs : SChain t P t') {f} (hf : f ∈ upSpan RD k μ s t) :
    f ≫ dg RD k μ t t' P ∈ upSpan RD k μ s t' := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, h, hγ, rfl⟩ := hf
    rw [Category.assoc, bubAt_comm, ← Category.assoc, dg_comp h hPs]
    exact Submodule.subset_span ⟨A ++ P, γ, hA.append hP, h.append hPs, hγ, rfl⟩
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

end UpSpanComp

/-! ## Entries of the images of `ψ_σ` and of polynomials -/

section Entries

open KLR.Diagram MatEnd

variable [DecidableEq I] (μ : X) {ν : Multiset I}

omit [DecidableEq I] in
theorem drop_word (i : KLR.Seq ν) {t : ℕ} (h : t + 1 < Multiset.card ν) :
    (word i).drop t = i.1 ⟨t, by omega⟩ :: i.1 ⟨t + 1, h⟩ :: (word i).drop (t + 2) := by
  rw [List.drop_eq_getElem_cons (by simp; omega), List.drop_eq_getElem_cons (by simp; omega),
    getElem_word, getElem_word]

omit [DecidableEq I] in
theorem word_sadj_smul (i : KLR.Seq ν) (t : ℕ) :
    word (TypeA.sadj (Multiset.card ν) t • i) = swapAt (word i) t := by
  by_cases h : t + 1 < Multiset.card ν
  · rw [word_sadj i h, swapAt_eq (drop_word i h)]
    simp
  · rw [TypeA.sadj_of_not_lt h, one_smul, swapAt_of_le (by simp; omega)]

omit [DecidableEq I] in
theorem word_wordProd_smul (σ : List ℕ) (i : KLR.Seq ν) :
    word (TypeA.wordProd (Multiset.card ν) σ • i) = applyW (word i) σ.reverse := by
  induction σ with
  | nil => simp
  | cons t σ ih =>
    rw [TypeA.wordProd_cons, mul_smul, word_sadj_smul, ih, List.reverse_cons, applyW_append]
    rfl

omit [DecidableEq I] in
theorem upFunctor_crossE (i : KLR.Seq ν) {t : ℕ} (h : t + 1 < Multiset.card ν) :
    (upFunctor RD k μ).map (crossE k (KLR.klQ2 k C) i t) =
      dg RD k μ (ups (word i)) (ups (word (TypeA.sadj (Multiset.card ν) t • i)))
        (crossAt (word i) t) := by
  rw [crossE_def _ h, upFunctor_diag, upDiag_eq_dg, crossAt_eq (drop_word i h)]
  rfl

omit [DecidableEq I] in
theorem upFunctor_dotE (i : KLR.Seq ν) (a : Fin (Multiset.card ν)) :
    (upFunctor RD k μ).map (dotE k (KLR.klQ2 k C) i a) =
      dg RD k μ (ups (word i)) (ups (word i))
        [(ups ((word i).take a), .dot (up (i.1 a)), ups ((word i).drop (a + 1)))] := by
  rw [dotE, upFunctor_diag, upDiag_eq_dg]
  rfl

theorem toUEnd_ψ_apply (t : ℕ) (h : t + 1 < Multiset.card ν) (j j' : KLR.Seq ν) :
    toUEnd RD k μ ν (KLR.KLRAlgebra.ψ t) j j' =
      if j' = TypeA.sadj (Multiset.card ν) t • j then
        dg RD k μ (ups (word j)) (ups (word j')) (crossAt (word j) t) else 0 := by
  rw [toUEnd_ψ, sum_apply, Finset.sum_eq_single j]
  · rw [single_apply]
    split_ifs with h₁ h₂ h₂
    · obtain ⟨-, rfl⟩ := h₁
      rw [upFunctor_crossE RD k μ j h]
      simp
    · exact absurd h₁.2 h₂
    · exact absurd ⟨rfl, h₂⟩ h₁
    · rfl
  · intro l _ hl
    rw [single_apply_of_ne _ (fun h' => hl h'.1.symm)]
  · simp

theorem toUEnd_ψw_apply (σ : List ℕ) (hσ : TypeA.ValidWord (Multiset.card ν) σ)
    (i j : KLR.Seq ν) :
    toUEnd RD k μ ν (KLR.KLRAlgebra.ψw σ) i j =
      if j = TypeA.wordProd (Multiset.card ν) σ • i then
        dg RD k μ (ups (word i)) (ups (word j)) (crossLs (word i) σ.reverse) else 0 := by
  induction σ generalizing j with
  | nil =>
    rw [KLR.KLRAlgebra.ψw_nil, map_one, one_apply]
    simp only [TypeA.wordProd_nil, one_smul, List.reverse_nil, crossLs_nil]
    split_ifs with h₁ h₂ h₂
    · subst h₁; simp [dg_nil]
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · rfl
  | cons t σ ih =>
    have ht : t + 1 < Multiset.card ν := hσ t List.mem_cons_self
    have hσ' : TypeA.ValidWord (Multiset.card ν) σ := fun x hx => hσ x (List.mem_cons_of_mem _ hx)
    rw [KLR.KLRAlgebra.ψw_cons, map_mul, mul_apply,
      Finset.sum_eq_single (TypeA.wordProd (Multiset.card ν) σ • i)]
    · rw [ih hσ', if_pos rfl, toUEnd_ψ_apply RD k μ t ht, TypeA.wordProd_cons, mul_smul]
      split_ifs with h₁
      · subst h₁
        have hw := word_wordProd_smul σ i
        rw [dg_comp (by rw [hw]; exact sChain_crossLs _ _)
          (by rw [word_sadj_smul, hw]; exact sChain_crossAt _ _)]
        congr 1
        rw [List.reverse_cons, crossLs_append, hw]
        simp
      · simp
    · intro l _ hl
      rw [ih hσ', if_neg hl, Limits.zero_comp]
    · simp

theorem toUEnd_pol_mul_e (p : MvPolynomial (Fin (Multiset.card ν)) k) (i : KLR.Seq ν) :
    ∃ D ∈ dotSpan RD k μ (ups (word i)),
      toUEnd RD k μ ν (KLR.KLRAlgebra.pol p * KLR.KLRAlgebra.e i) = single i i D := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a • 𝟙 _, Submodule.smul_mem _ a (id_mem_dotSpan RD k μ _), ?_⟩
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_smul, toUEnd_e, single_smul]
  | add p q hp hq =>
    obtain ⟨D, hD, e1⟩ := hp
    obtain ⟨E, hE, e2⟩ := hq
    exact ⟨D + E, Submodule.add_mem _ hD hE, by rw [map_add, add_mul, map_add, e1, e2, single_add]⟩
  | mul_X p a hp =>
    obtain ⟨D, hD, e1⟩ := hp
    have hdot : (upFunctor RD k μ).map (dotE k (KLR.klQ2 k C) i a) ∈ dotSpan RD k μ (ups (word i)) := by
      rw [upFunctor_dotE]
      refine Submodule.subset_span ⟨_, ?_, ?_, rfl⟩
      · intro x hx
        rw [List.mem_singleton.1 hx]
        exact ⟨_, rfl, rfl⟩
      · have hw : ups ((word i).take a) ++ [up (i.1 a)] ++ ups ((word i).drop (a + 1)) =
            ups (word i) := by
          conv_rhs => rw [← word_split i a]
          simp [ups]
        exact ⟨hw.symm, hw⟩
    refine ⟨(upFunctor RD k μ).map (dotE k (KLR.klQ2 k C) i a) ≫ D, dotSpan_comp hdot hD, ?_⟩
    have e2 : (KLR.KLRAlgebra.pol (p * MvPolynomial.X a) * KLR.KLRAlgebra.e i : KLR.R2 k C ν) =
        (KLR.KLRAlgebra.pol p * KLR.KLRAlgebra.e i) * (KLR.KLRAlgebra.x a * KLR.KLRAlgebra.e i) := by
      rw [map_mul, KLR.KLRAlgebra.pol_X]
      calc KLR.KLRAlgebra.pol p * KLR.KLRAlgebra.x a * KLR.KLRAlgebra.e i
          = KLR.KLRAlgebra.pol p * (KLR.KLRAlgebra.e i * KLR.KLRAlgebra.x a) := by
            rw [mul_assoc, KLR.KLRAlgebra.x_mul_e]
        _ = KLR.KLRAlgebra.pol p * (KLR.KLRAlgebra.e i * KLR.KLRAlgebra.e i * KLR.KLRAlgebra.x a) := by
            rw [KLR.KLRAlgebra.e_mul_self]
        _ = (KLR.KLRAlgebra.pol p * KLR.KLRAlgebra.e i) * (KLR.KLRAlgebra.e i * KLR.KLRAlgebra.x a) := by
            simp only [mul_assoc]
        _ = _ := by rw [KLR.KLRAlgebra.x_mul_e]
    rw [e2, map_mul, e1, map_mul, toUEnd_e, toUEnd_x, Finset.sum_mul, Finset.sum_eq_single i,
      single_mul_single]
    · rw [single_mul_single]
      erw [Category.id_comp]
    · intro l _ hl
      exact single_mul_single_of_ne _ _ (Ne.symm hl)
    · simp

/-- Evaluation of a matrix of morphisms at an entry, as a linear map. -/
def evalL {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [Linear k 𝒞] (Z : ι → 𝒞) (i j : ι) : MatEnd Z →ₗ[k] (Z i ⟶ Z j) where
  toFun f := f i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Upward diagrams in normal form** (KL I, Theorem 2.5, spanning half, transported to `U`):
for any choice of reduced words `ρ w`, every upward diagram from `E_i 1_μ` to `E_j 1_μ` is a
linear combination of dots on `E_i 1_μ` followed by the crossings `crossLs (word i) (ρ w).reverse`
(`w • i = j`). -/
theorem upward_mem_span_nf (ρ : Equiv.Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card ν) (ρ w) ∧ TypeA.wordProd (Multiset.card ν) (ρ w) = w)
    (i j : KLR.Seq ν) {A : List (LayerData I)} (hA : Upward A)
    (h : SChain (ups (word i)) A (ups (word j))) :
    dg RD k μ (ups (word i)) (ups (word j)) A ∈ Submodule.span k
      {f | ∃ (w : Equiv.Perm (Fin (Multiset.card ν)))
        (D : End ((pres RD k).obj (ob RD μ (ups (word i))))),
        w • i = j ∧ D ∈ dotSpan RD k μ (ups (word i)) ∧
        f = D ≫ dg RD k μ (ups (word i)) (ups (word j)) (crossLs (word i) (ρ w).reverse)} := by
  obtain ⟨d, hd⟩ := dg_upward_eq RD k μ h hA
  rw [hd, ← upFunctor_diag]
  set F := (KLR.Diagram.pres k (KLR.klQ2 k C)).diag d
  let r : KLR.R2 k C ν := (diagREquiv k (KLR.klQ2 k C) ν).symm (single i j F)
  have hr : KLR.KLRAlgebra.e j * r * KLR.KLRAlgebra.e i = r := by
    apply (diagREquiv k (KLR.klQ2 k C) ν).injective
    simp only [r, map_mul, AlgEquiv.apply_symm_apply, diagREquiv_e]
    rw [DiagR.E_eq, DiagR.E_eq, single_mul_single, single_mul_single]
    erw [Category.id_comp, Category.comp_id]
  have hF : (upFunctor RD k μ).map F = toUEnd RD k μ ν r i j := by
    show _ = (upFunctor RD k μ).map ((diagREquiv k (KLR.klQ2 k C) ν r) i j)
    rw [AlgEquiv.apply_symm_apply, single_apply_self]
  rw [hF]
  have hmem := KLR.KLRAlgebra.mem_span_corner' ρ hρ i j hr
  let Φ : KLR.R2 k C ν →ₗ[k] _ := (evalL k _ i j).comp (toUEnd RD k μ ν).toLinearMap
  have hΦ := Submodule.mem_map_of_mem (f := Φ) hmem
  rw [Submodule.map_span] at hΦ
  refine Submodule.span_mono ?_ hΦ
  rintro _ ⟨_, ⟨w, u, hw, rfl⟩, rfl⟩
  obtain ⟨D, hD, eD⟩ := toUEnd_pol_mul_e RD k μ (MvPolynomial.monomial u 1) i
  refine ⟨w, D, hw, hD, ?_⟩
  show toUEnd RD k μ ν (KLR.KLRAlgebra.ψw (ρ w) * KLR.KLRAlgebra.pol (MvPolynomial.monomial u 1) *
    KLR.KLRAlgebra.e i) i j = _
  rw [mul_assoc, map_mul, eD, mul_apply, Finset.sum_eq_single i, single_apply_self,
    toUEnd_ψw_apply RD k μ _ (hρ w).1.1, (hρ w).2, if_pos hw.symm]
  · intro l _ hl
    rw [single_apply_of_ne _ (fun h' => hl h'.2), Limits.zero_comp]
  · simp

theorem upward_mem_span_nf' (ρ : Equiv.Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card ν) (ρ w) ∧ TypeA.wordProd (Multiset.card ν) (ρ w) = w)
    (i j : KLR.Seq ν) {S T : List (Letter I)} (hS : ups (word i) = S) (hT : ups (word j) = T)
    {A : List (LayerData I)} (hA : Upward A) (h : SChain S A T) :
    dg RD k μ S T A ∈ Submodule.span k
      {f | ∃ (w : Equiv.Perm (Fin (Multiset.card ν))) (D : End ((pres RD k).obj (ob RD μ S))),
        w • i = j ∧ D ∈ dotSpan RD k μ S ∧
        f = D ≫ dg RD k μ S T (crossLs (word i) (ρ w).reverse)} := by
  subst hS hT
  exact upward_mem_span_nf RD k μ ρ hρ i j hA h

end Entries

/-! ## Closures of upward diagrams -/

section ClosedPart

variable (μ : X) (j : I)

/-- Dots at the bottom of a closure leave it (or move around it to the top). -/
theorem closeLs_dots_mem {s t : List (Letter I)} (N : List (LayerData I))
    (hN : SChain (s ++ [up j]) N (t ++ [up j]))
    (hbase : ∀ e, dg RD k μ s t (closeLs j s t N e) ∈ upSpan RD k μ s t) :
    ∀ (Dl : List (LayerData I)), DotsOnly Dl → SChain (s ++ [up j]) Dl (s ++ [up j]) →
      ∀ e, dg RD k μ s t (closeLs j s t (Dl ++ N) e) ∈ upSpan RD k μ s t := by
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
    rcases List.eq_nil_or_concat v with rfl | ⟨v₀, lv, rfl⟩
    · -- a dot on the closed strand: it moves around the closure
      have e1 : u = s ∧ l = up j := by
        have := h₀.symm
        simp only [List.append_nil] at this
        obtain ⟨h1, h2⟩ := List.append_inj' this rfl
        exact ⟨h1, by simpa using h2⟩
      obtain ⟨rfl, rfl⟩ := e1
      rw [List.cons_append, dg_closeLs_rotate RD k μ j _ (hDc'.append hN)]
      exact ih hD' hDc' (e + 1)
    · -- a dot on another strand: it leaves the closure
      simp only [List.concat_eq_append] at h₀ hD ⊢
      have e1 : u ++ [l] ++ v₀ = s ∧ lv = up j := by
        have := h₀.symm
        rw [show u ++ [l] ++ (v₀ ++ [lv]) = (u ++ [l] ++ v₀) ++ [lv] by simp] at this
        obtain ⟨h1, h2⟩ := List.append_inj' this rfl
        exact ⟨h1, by simpa using h2⟩
      obtain ⟨hs, rfl⟩ := e1
      have hd : SChain s [(u, Shape.dot l, v₀)] s := ⟨by rw [← hs]; rfl, by rw [← hs]; rfl⟩
      have hform : ((u, Shape.dot l, v₀ ++ [up j]) :: Dl) ++ N =
          [(u, Shape.dot l, v₀)].map (whL [] [up j]) ++ (Dl ++ N) := by simp [whL]
      rw [hform, dg_closeLs_peel RD k μ j _ _ hd (hDc'.append hN)]
      refine upSpan_comp_left (fun x hx => ?_) hd (ih hD' hDc' e)
      rw [List.mem_singleton.1 hx]; exact hl

theorem closeLs_nil_mem (s : List (Letter I)) (e : ℕ) :
    dg RD k μ s s (closeLs j s s [] e) ∈ upSpan RD k μ s s := by
  rw [dg_closeLs_nil]
  refine Submodule.subset_span ⟨[], cwU RD k μ j e, fun _ h => by simp at h, rfl,
    cwU_isBub _ _, ?_⟩
  rw [dg_nil, Category.id_comp]

theorem dg_mem_upSpan_congr {S S' T T' : List (Letter I)} (hS : S = S') (hT : T = T')
    {L : List (LayerData I)} (h : dg RD k μ S T L ∈ upSpan RD k μ S T) :
    dg RD k μ S' T' L ∈ upSpan RD k μ S' T' := by
  subst hS hT; exact h

theorem closeLs_run_mem (x y' : List I) (e : ℕ) :
    dg RD k μ (ups (x ++ [j] ++ y')) (ups (x ++ y' ++ [j]))
      (closeLs j (ups (x ++ [j] ++ y')) (ups (x ++ y' ++ [j])) (runLs x j (y' ++ [j])) e) ∈
      upSpan RD k μ (ups (x ++ [j] ++ y')) (ups (x ++ y' ++ [j])) := by
  have hrun := sChain_runLs x j y'
  have hcore : SChain (ups (x ++ y' ++ [j]) ++ [up j]) [(ups (x ++ y'), .cross true j j, [])]
      (ups (x ++ y' ++ [j]) ++ [up j]) := ⟨by simp [ups], by simp [ups]⟩
  rw [runLs_append_single, dg_closeLs_peel RD k μ j _ _ hrun hcore]
  refine upSpan_comp_left (upward_runLs x j y') hrun ?_
  have e1 : ups (x ++ y') ++ [up j] = ups (x ++ y' ++ [j]) := by simp [ups]
  have hm := plcL_slideSetR_mem_upSpan RD k μ (ups (x ++ y')) j (curl_mem_slideSetR RD k μ j e)
  rw [← dg_closeLs_curl, e1] at hm
  exact dg_mem_upSpan_congr RD k μ (List.append_nil _) (List.append_nil _) hm

end ClosedPart

/-! ## The partial trace and the Markov lemma -/

section Markov

variable (μ : X)

/-- **The right partial trace** (over the last strand): closing the last strand `E_j` of a 2-morphism
`E_{a j} 1_{μ - j_X} ⟶ E_{b j} 1_{μ - j_X}` on its right, with the cup `1 → E_j F_j` and the
cap `E_j F_j → 1` (outer region `μ`). -/
def ptrLast (a b : List (Letter I)) (j : I) :
    ((pres RD k).obj (ob RD (wt RD μ [dn j]) (a ++ [up j])) ⟶
      (pres RD k).obj (ob RD (wt RD μ [dn j]) (b ++ [up j]))) →ₗ[k]
      ((pres RD k).obj (ob RD μ a) ⟶ (pres RD k).obj (ob RD μ b)) where
  toFun f := dg RD k μ a ([] ++ (a ++ [up j]) ++ [dn j]) [(a, .cup (up j), [])] ≫
    plcL RD k μ [] [dn j] (a ++ [up j]) (b ++ [up j]) f ≫
      dg RD k μ ([] ++ (b ++ [up j]) ++ [dn j]) b [(b, .cap (dn j), [])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem ptrLast_dg (a b : List (Letter I)) (j : I) (A : List (LayerData I)) :
    ptrLast RD k μ a b j (dg RD k (wt RD μ [dn j]) (a ++ [up j]) (b ++ [up j]) A) =
      dg RD k μ a b (closeLs j a b A 0) := by
  show dg RD k μ a _ _ ≫ plcL RD k μ [] [dn j] _ _ (dg RD k (wt RD μ [dn j]) _ _ A) ≫ _ = _
  rw [plcL_dg]
  have h1 : SChain a [(a, .cup (up j), [])] ([] ++ (a ++ [up j]) ++ [dn j]) := ⟨by simp, by simp⟩
  have h3 : SChain ([] ++ (b ++ [up j]) ++ [dn j]) [(b, .cap (dn j), [])] b :=
    ⟨by simp, by simp⟩
  by_cases hA : SChain (a ++ [up j]) A (b ++ [up j])
  · have h2 := hA.whisk [] [dn j]
    rw [dg_comp h2 h3, dg_comp h1 (h2.append h3)]
    simp [closeLs]
  · rw [dg_of_not (fun h => hA h.of_whisk), Limits.zero_comp, Limits.comp_zero, dg_of_not]
    intro h
    unfold closeLs at h
    simp only [List.replicate_zero, List.append_nil] at h
    obtain ⟨m₂, h₁₂, h₃'⟩ := SChain.split h
    obtain ⟨m₁, h₁', h₂'⟩ := SChain.split h₁₂
    obtain rfl := h₁'.eq_target h1
    obtain rfl := h₃'.eq_source h3
    exact hA h₂'.of_whisk

variable [DecidableEq I]

/-- **The Markov lemma**: closing the last strand of an upward diagram on its right gives a
linear combination of upward diagrams followed by bubble monomials on the far right. The
upward diagram is written in the normal form of KL I, Theorem 2.5, for the canonical reduced
words (whose last descending run moves one strand to the last position); the crossings not
involving the last position leave the closure, dots on the closed strand move around it, and
what remains is a right curl with dots on its loop (`curl_mem_slideSetR`) or a dotted bubble. -/
theorem ptrLast_upward_mem_upSpan (a b : List I) (j : I) {A : List (LayerData I)} (hA : Upward A)
    (h : SChain (ups a ++ [up j]) A (ups b ++ [up j])) :
    ptrLast RD k μ (ups a) (ups b) j (dg RD k (wt RD μ [dn j]) (ups a ++ [up j]) (ups b ++ [up j]) A) ∈
      upSpan RD k μ (ups a) (ups b) := by
  have hperm : (a ++ [j]).Perm (b ++ [j]) :=
    upward_perm hA (by simpa [ups] using h)
  set ν : Multiset I := ((a ++ [j] : List I) : Multiset I)
  let i := seqOfEq ν (a ++ [j]) rfl
  let i' := seqOfEq ν (b ++ [j]) (Multiset.coe_eq_coe.2 hperm.symm)
  have hi : KLR.Diagram.word i = a ++ [j] := word_seqOfEq _ _ _
  have hi' : KLR.Diagram.word i' = b ++ [j] := word_seqOfEq _ _ _
  have hm : Multiset.card ν = a.length + 1 := by simp [ν]
  have hmem := upward_mem_span_nf' RD k (wt RD μ [dn j]) (TypeA.canWord (Multiset.card ν))
    (fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩) i i'
    (S := ups a ++ [up j]) (T := ups b ++ [up j]) (by rw [hi]; simp [ups])
    (by rw [hi']; simp [ups]) hA h
  refine (Submodule.span_le (p := (upSpan RD k μ (ups a) (ups b)).comap
    (ptrLast RD k μ (ups a) (ups b) j))).mpr ?_ hmem
  rintro _ ⟨w, D, hw, hD, rfl⟩
  show ptrLast RD k μ (ups a) (ups b) j (D ≫ _) ∈ upSpan RD k μ (ups a) (ups b)
  -- the canonical word: a run moving one strand to the end, then crossings avoiding it
  obtain ⟨b₀, ρ', hb₀, hρ', hcan⟩ : ∃ (b₀ : ℕ) (ρ' : List ℕ), b₀ ≤ a.length ∧
      (∀ t ∈ ρ', t + 1 < a.length) ∧
      (TypeA.canWord (Multiset.card ν) w).reverse = List.range' b₀ (a.length - b₀) ++ ρ' :=
    canWord_reverse_split a.length _ hm w
  set x := (a ++ [j]).take b₀ with hx
  set y := (a ++ [j]).drop (b₀ + 1) with hy
  have hxl : x.length = b₀ := by
    simp only [hx, List.length_take, List.length_append, List.length_singleton]; omega
  have hyl : y.length = a.length - b₀ := by
    simp only [hy, List.length_drop, List.length_append, List.length_singleton]; omega
  obtain ⟨c₀, hsplit⟩ : ∃ c₀, a ++ [j] = x ++ [c₀] ++ y := by
    refine ⟨(a ++ [j])[b₀]'(by simp; omega), ?_⟩
    rw [hx, hy, List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons,
      List.take_append_drop]
  have hrun := crossLs_range' x c₀ y
  have hrest := crossLs_append_right (x ++ y) [c₀] ρ' (by
    simp only [List.length_append, hxl, hyl]; intro t ht; have := hρ' t ht; omega)
  have hcross : crossLs (KLR.Diagram.word i) (TypeA.canWord (Multiset.card ν) w).reverse =
      runLs x c₀ y ++ (crossLs (x ++ y) ρ').map (whL [] [up c₀]) := by
    rw [hi, hcan, hsplit, crossLs_append, ← hyl, ← hxl, hrun.1, hrun.2, hrest.1]
    simp [ups]
  -- the final colours
  have hfin : applyW (x ++ y) ρ' ++ [c₀] = b ++ [j] := by
    rw [← hrest.2, ← hrun.2, ← hi', hw.symm, ← TypeA.wordProd_canWord (Multiset.card ν) w,
      word_wordProd_smul, hi, hsplit, hcan, applyW_append, hxl, hyl]
  obtain ⟨hb, hc₀⟩ : applyW (x ++ y) ρ' = b ∧ c₀ = j := by
    obtain ⟨h1, h2⟩ := List.append_inj' hfin rfl
    exact ⟨h1, by simpa using h2⟩
  subst c₀
  have hP : SChain (ups (x ++ y)) (crossLs (x ++ y) ρ') (ups b) := by
    rw [← hb]; exact sChain_crossLs _ _
  have hS : ups a ++ [up j] = ups (x ++ [j] ++ y) := by
    rw [← hsplit]; simp [ups]
  -- the closed part
  have hclosed : ∀ (Dl : List (LayerData I)), DotsOnly Dl →
      SChain (ups a ++ [up j]) Dl (ups a ++ [up j]) →
      dg RD k μ (ups a) (ups (x ++ y)) (closeLs j (ups a) (ups (x ++ y)) (Dl ++ runLs x j y) 0) ∈
        upSpan RD k μ (ups a) (ups (x ++ y)) := by
    have hN : SChain (ups a ++ [up j]) (runLs x j y) (ups (x ++ y) ++ [up j]) := by
      rw [hS]; simpa [ups] using sChain_runLs x j y
    intro Dl hDl hDlc
    refine closeLs_dots_mem RD k μ j (runLs x j y) hN ?_ Dl hDl hDlc 0
    intro e
    rcases List.eq_nil_or_concat y with hy0 | ⟨y', lj, hy0⟩
    · -- `y = []`: a dotted bubble
      have ha : a = x := by
        rw [hy0, List.append_nil] at hsplit
        exact List.append_inj_left' hsplit rfl
      rw [hy0, List.append_nil, ← ha]
      simp only [runLs]
      exact closeLs_nil_mem RD k μ j (ups a) e
    · -- `y = y' ++ [j]`: a run followed by a curl
      rw [List.concat_eq_append] at hy0
      have hsplit' := hsplit
      rw [hy0, ← List.append_assoc] at hsplit'
      obtain ⟨ha, hlj⟩ := List.append_inj' hsplit' rfl
      simp only [List.cons.injEq, and_true] at hlj
      subst hlj
      rw [hy0, ha, ← List.append_assoc]
      exact closeLs_run_mem RD k μ j x y' e
  -- assemble
  induction hD using Submodule.span_induction with
  | mem D hD =>
    obtain ⟨Dl, hDl, hDlc, rfl⟩ := hD
    have hR : SChain (ups a ++ [up j]) (runLs x j y) (ups (x ++ y) ++ [up j]) := by
      rw [hS]; simpa [ups] using sChain_runLs x j y
    have hP' : SChain (ups (x ++ y) ++ [up j]) ((crossLs (x ++ y) ρ').map (whL [] [up j]))
        (ups b ++ [up j]) := by simpa using hP.whisk [] [up j]
    have hC : SChain (ups a ++ [up j])
        (crossLs (KLR.Diagram.word i) (TypeA.canWord (Multiset.card ν) w).reverse)
        (ups b ++ [up j]) := by rw [hcross]; exact hR.append hP'
    rw [dg_comp hDlc hC, ptrLast_dg, hcross, ← List.append_assoc,
      dg_closeLs_peel_top RD k μ j _ _ (hDlc.append hR) hP]
    exact upSpan_comp_right (upward_crossLs _ _) hP (hclosed Dl hDl hDlc)
  | zero => rw [Limits.zero_comp, map_zero]; exact Submodule.zero_mem _
  | add D₁ D₂ _ _ h₁ h₂ => rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul r D _ hD' => rw [Linear.smul_comp, map_smul]; exact Submodule.smul_mem _ r hD'

end Markov

end Categorification.KL3.Diagram
