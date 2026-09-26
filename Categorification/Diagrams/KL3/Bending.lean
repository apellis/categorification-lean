/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Straighten
import Categorification.Diagrams.KL3.SymmetryOmega

/-!
# Bending blocks of downward strands, and traces over blocks of strands

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1
(biadjointness, eqs. (3.1), (3.2)) and §3.2 (proof of Lemma 3.9, label `lem_surjective`; TeX
locators `sources/klr/kl3/0807.3250v1.txt`, lines 1690–1790).

For a word `w` let `cupA w : 1 → w w*` be the nested cups and `capA w : w* w → 1` the nested
caps (`w* = rd w`, the reversed sequence of dual letters). They satisfy the zigzag relations for
blocks (`dg_zigA`, `dg_zigB`). With them we define, for a list of colours `b` (the block of
downward strands `F_b = dns b`, with dual block `E_{b̄} = rd (dns b)`):

* `unbendR μ b s a : HOM(E_{s b̄}, E_a) → HOM(E_s, E_a F_b)`: the downward strands on the top
  right come from nested cups on the bottom right (the inverse of bending them down);
* `unbendL μ d s c : HOM(E_{d̄ s}, E_c) → HOM(E_s, F_d E_c)`: the same on the left;
* `ptrRL μ b X Y`: the right partial trace over the block `E_{b̄}` (nested cups `1 → E F`
  and caps `E F → 1` on the right); it is the iterated partial trace `ptrLast`, hence preserves
  `upSpan` (**Markov lemma for blocks**, `ptrRL_mem_upSpan`);
* `ptrLL μ d X Y`: the left partial trace over the block `E_{d̄}` (nested cups `1 → F E` and caps
  `F E → 1` on the left); the iterated `ptrFirst`, `ptrLL_mem_upSpan`.

A diagram `M : x q → p y` is bent on both sides by `sharpL` (the block `q` at its bottom right up
on the right, the block `p` at its top left down on the left) and a diagram `(rd p) x → y (rd q)`
by `flatL`; unbending a bent diagram gives it back (`dg_unbend_sharp`, `dg_unbend_flat`,
`dg_unbendR_bendR`). These identities use only the interchange law and the zigzag relations.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Nested cups and caps -/

/-- Nested cups `1 → w (rd w)`, the outermost first. -/
def cupA : List (Letter I) → List (LayerData I)
  | [] => []
  | l :: w => ([], .cup l, []) :: (cupA w).map (whL [l] [l.dual])

/-- Nested caps `(rd w) w → 1`, the innermost first. -/
def capA : List (Letter I) → List (LayerData I)
  | [] => []
  | l :: w => (rd w, .cap l, w) :: capA w

@[simp] theorem cupA_nil : cupA ([] : List (Letter I)) = [] := rfl
@[simp] theorem capA_nil : capA ([] : List (Letter I)) = [] := rfl

theorem sChain_cupA : ∀ w : List (Letter I), SChain [] (cupA w) (w ++ rd w)
  | [] => rfl
  | l :: w => ⟨rfl, by simpa [whL] using (sChain_cupA w).whisk [l] [l.dual]⟩

theorem sChain_capA : ∀ w : List (Letter I), SChain (rd w ++ w) (capA w) []
  | [] => rfl
  | l :: w => ⟨by simp, by simpa using sChain_capA w⟩

theorem cupA_append_single (l : Letter I) :
    ∀ w : List (Letter I), cupA (w ++ [l]) = cupA w ++ [(w, .cup l, rd w)]
  | [] => rfl
  | l' :: w => by
    simp only [List.cons_append, cupA, cupA_append_single l w, List.map_append, List.map_cons,
      List.map_nil, whL_mk, rd_cons, List.cons.injEq, true_and]
    simp

theorem allSh_cupA {p : Shape I → Bool} :
    ∀ w : List (Letter I), (∀ l ∈ w, p (.cup l) = true) → AllSh p (cupA w)
  | [] => fun _ x hx => by simp at hx
  | l :: w => fun h x hx => by
    simp only [cupA, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact h l List.mem_cons_self
    · exact allSh_cupA w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) y hy

theorem allSh_capA {p : Shape I → Bool} :
    ∀ w : List (Letter I), (∀ l ∈ w, p (.cap l) = true) → AllSh p (capA w)
  | [] => fun _ x hx => by simp at hx
  | l :: w => fun h x hx => by
    simp only [capA, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h l List.mem_cons_self
    · exact allSh_capA w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) x hx

theorem whL_def (u v : List (Letter I)) : whL u v = fun x => (u ++ x.1, x.2.1, x.2.2 ++ v) := rfl

/-- Normalization of lists of placed layers. -/
macro "laysimp" : tactic => `(tactic| simp [List.map_map, Function.comp_def, whL_def,
  List.append_assoc, cupA, capA])

/-! ## Zigzag relations for blocks -/

/-- **Zigzag relation for blocks**, first form: nested cups to the left of `w`, then nested caps,
is the identity of `w`. -/
theorem dg_zigA : ∀ (w : List (Letter I)) (μ : X),
    dg RD k μ w w ((cupA w).map (whL [] w) ++ (capA w).map (whL w [])) = dg RD k μ w w []
  | [] => fun μ => rfl
  | l :: w => fun μ => by
    have hc := (sChain_cupA w).whisk [l] []
    have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := l :: w) (T := l :: w)
      [([], .cup l, l :: w)] ((capA w).map (whL (l :: w) []))
      (A := (cupA w).map (whL [l] [])) (s := [l]) (s' := [l] ++ (w ++ rd w))
      (by simpa using hc) (B := [([], .cap l, w)]) (t := [l.dual, l] ++ w) (t' := w)
      ⟨by simp, by simp⟩
    have hz1 := dg_step RD k μ (s₀ := l :: w) (t₀ := l :: w) []
      ((cupA w).map (whL [l] w) ++ (capA w).map (whL (l :: w) [])) [] w (dg_zigL' RD k _ l)
      (by simp) (by
        have h1 := (sChain_cupA w).whisk [l] w
        have h2 := (sChain_capA w).whisk (l :: w) []
        simpa using h1.append (by simpa using h2)) rfl rfl
    have hz2 := dg_step RD k μ (s₀ := l :: w) (t₀ := l :: w) [] [] [l] [] (dg_zigA w μ)
      (by simp) (by simp) rfl rfl
    calc dg RD k μ (l :: w) (l :: w)
          ((cupA (l :: w)).map (whL [] (l :: w)) ++ (capA (l :: w)).map (whL (l :: w) []))
        = dg RD k μ (l :: w) (l :: w) ([([], .cup l, l :: w)] ++
            ((cupA w).map (whL [l] [])).map (whL [] ([l.dual, l] ++ w)) ++
              [([], Shape.cap l, w)].map (whL ([l] ++ (w ++ rd w)) []) ++
                (capA w).map (whL (l :: w) [])) := dg_list_eq (by laysimp)
      _ = _ := ei
      _ = dg RD k μ (l :: w) (l :: w) ([] ++ [([], Shape.cup l, [l]), ([l], .cap l, [])].map
            (whL [] w) ++ ((cupA w).map (whL [l] w) ++ (capA w).map (whL (l :: w) []))) :=
          dg_list_eq (by laysimp)
      _ = _ := hz1
      _ = dg RD k μ (l :: w) (l :: w) ([] ++ ((cupA w).map (whL [] w) ++
            (capA w).map (whL w [])).map (whL [l] []) ++ []) := dg_list_eq (by laysimp)
      _ = _ := hz2
      _ = dg RD k μ (l :: w) (l :: w) [] := dg_list_eq (by laysimp)

/-- **Zigzag relation for blocks**, second form: nested cups to the right of `rd w`, then nested
caps, is the identity of `rd w`. -/
theorem dg_zigB : ∀ (w : List (Letter I)) (μ : X),
    dg RD k μ (rd w) (rd w) ((cupA w).map (whL (rd w) []) ++ (capA w).map (whL [] (rd w))) =
      dg RD k μ (rd w) (rd w) []
  | [] => fun μ => rfl
  | l :: w => fun μ => by
    have hc := (sChain_cupA w).whisk [] [l.dual]
    have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := rd w ++ [l.dual])
      (T := rd w ++ [l.dual]) [(rd w ++ [l.dual], .cup l, [])]
      ((capA w).map (whL [] (rd w ++ [l.dual])))
      (A := [(rd w, .cap l, [])]) (s := rd w ++ [l.dual, l]) (s' := rd w) ⟨by simp, by simp⟩
      (B := (cupA w).map (whL [] [l.dual])) (t := [l.dual]) (t' := w ++ rd w ++ [l.dual])
      (by simpa using hc)
    have hz1 := dg_step RD k μ (s₀ := rd w ++ [l.dual]) (t₀ := rd w ++ [l.dual]) []
      ((cupA w).map (whL (rd w) [l.dual]) ++ (capA w).map (whL [] (rd w ++ [l.dual]))) (rd w) []
      (dg_zigR' RD k _ l) (by simp) (by
        have h1 := (sChain_cupA w).whisk (rd w) [l.dual]
        have h2 := (sChain_capA w).whisk [] (rd w ++ [l.dual])
        simpa using h1.append (by simpa using h2)) rfl rfl
    have hz2 := dg_step RD k μ (s₀ := rd w ++ [l.dual]) (t₀ := rd w ++ [l.dual]) [] [] []
      [l.dual] (dg_zigB w (wt RD μ [l.dual])) (by simp) (by simp) rfl rfl
    rw [show rd (l :: w) = rd w ++ [l.dual] from rd_cons l w]
    calc dg RD k μ (rd w ++ [l.dual]) (rd w ++ [l.dual])
          ((cupA (l :: w)).map (whL (rd w ++ [l.dual]) []) ++
            (capA (l :: w)).map (whL [] (rd w ++ [l.dual])))
        = dg RD k μ (rd w ++ [l.dual]) (rd w ++ [l.dual]) ([(rd w ++ [l.dual], .cup l, [])] ++
            ((cupA w).map (whL [] [l.dual])).map (whL (rd w ++ [l.dual, l]) []) ++
              [(rd w, Shape.cap l, [])].map (whL [] (w ++ rd w ++ [l.dual])) ++
                (capA w).map (whL [] (rd w ++ [l.dual]))) := dg_list_eq (by laysimp)
      _ = _ := ei.symm
      _ = dg RD k μ (rd w ++ [l.dual]) (rd w ++ [l.dual]) ([] ++
            [([l.dual], Shape.cup l, []), ([], .cap l, [l.dual])].map (whL (rd w) []) ++
              ((cupA w).map (whL (rd w) [l.dual]) ++ (capA w).map (whL [] (rd w ++ [l.dual])))) :=
          dg_list_eq (by laysimp)
      _ = _ := hz1
      _ = dg RD k μ (rd w ++ [l.dual]) (rd w ++ [l.dual]) ([] ++ ((cupA w).map (whL (rd w) []) ++
            (capA w).map (whL [] (rd w))).map (whL [] [l.dual]) ++ []) := dg_list_eq (by laysimp)
      _ = _ := hz2
      _ = dg RD k μ (rd w ++ [l.dual]) (rd w ++ [l.dual]) [] := dg_list_eq (by laysimp)

theorem capA_append_single (l : Letter I) :
    ∀ w : List (Letter I), capA (w ++ [l]) = (capA w).map (whL [l.dual] [l]) ++ [([], .cap l, [])]
  | [] => rfl
  | l' :: w => by
    simp [capA, capA_append_single l w]

theorem positive_rd_dns (b : List I) : Positive (rd (dns b)) := by
  intro l hl
  simp only [rd, List.mem_reverse, List.mem_map] at hl
  obtain ⟨_, ⟨j, -, rfl⟩, rfl⟩ := hl
  rfl

/-! ## `upSpan` and rewriting in context -/

/-- Placing an element of `upSpan` between upward diagrams (with no strands on its right) gives an
element of `upSpan`. -/
theorem upSpan_ctxL {μ : X} {s₀ t₀ u S T : List (Letter I)} {pre post : List (LayerData I)}
    (hpu : Upward pre) (hqu : Upward post) (hpre : SChain s₀ pre (u ++ S ++ []))
    (hpost : SChain (u ++ T ++ []) post t₀) {h} (hh : h ∈ upSpan RD k μ S T) :
    ctxL RD k μ s₀ t₀ pre u [] post S T h ∈ upSpan RD k μ s₀ t₀ := by
  dsimp only [wt_nil] at *
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, hc, hγ, rfl⟩ := hf
    have hc' : SChain s₀ (pre ++ A.map (whL u []) ++ post) t₀ := by
      refine (hpre.append ?_).append hpost
      simpa using hc.whisk u []
    have key := hom_ext_dg RD k μ (s := []) (t := [])
      ((ctxL RD k μ s₀ t₀ pre u [] post S T).comp
        (Linear.leftComp k _ (dg RD k μ S T A) ∘ₗ bubAt RD k μ T))
      (Linear.leftComp k _ (dg RD k μ s₀ t₀ (pre ++ A.map (whL u []) ++ post)) ∘ₗ bubAt RD k μ t₀)
      (fun B hB => ?_)
    · have e := LinearMap.congr_fun key γ
      simp only [LinearMap.comp_apply, Linear.leftComp_apply] at e
      erw [e]
      exact Submodule.subset_span ⟨_, γ, (hpu.append (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hA y hy)).append hqu, hc', hγ, rfl⟩
    simp only [LinearMap.comp_apply, Linear.leftComp_apply]
    have hBT : SChain T (B.map (whL T [])) T := by simpa using hB.whisk T []
    have hBt : SChain t₀ (B.map (whL t₀ [])) t₀ := by simpa using hB.whisk t₀ []
    erw [bubAt_dg, bubAt_dg, dg_comp hc hBT, dg_comp hc' hBt,
      ctxL_dg RD k μ hpre hpost]
    have e := dg_closed_left (RD := RD) (k := k) μ (S := s₀) (T := t₀)
      (pre ++ A.map (whL u [])) [] (s := u ++ T) (s' := t₀) [] hB (by simpa using hpost)
    simp only [List.map_append, map_whL_whL, List.append_assoc, map_whL_nil_nil,
      List.append_nil] at e ⊢
    exact e.symm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-! ## Traces over blocks of strands -/

variable (RD k) in
/-- **The right partial trace over a block**: the upward strands `E_{b̄}` (`b̄ = rd (dns b)`) at
the right of a 2-morphism `E_S 1_ν ⟶ E_T 1_ν` (`S = s₀ b̄`, `T = t₀ b̄`, `ν = μ + (F_b)_X`) are
closed on the right by nested cups `1 → E F` and caps `E F → 1`. -/
def ptrRL (μ : X) (b : List I) (s₀ t₀ S T : List (Letter I)) :
    ((pres RD k).obj (ob RD (wt RD μ (dns b)) S) ⟶ (pres RD k).obj (ob RD (wt RD μ (dns b)) T))
      →ₗ[k] ((pres RD k).obj (ob RD μ s₀) ⟶ (pres RD k).obj (ob RD μ t₀)) :=
  ctxL RD k μ s₀ t₀ ((cupA (rd (dns b))).map (whL s₀ [])) [] (dns b)
    ((capA (dns b)).map (whL t₀ [])) S T

variable (RD k) in
/-- **The left partial trace over a block**: the upward strands `E_{d̄}` at the left of a
2-morphism `E_S 1_μ ⟶ E_T 1_μ` (`S = d̄ s₀`, `T = d̄ t₀`) are closed on the left by nested cups
`1 → F E` and caps `F E → 1`. -/
def ptrLL (μ : X) (d : List I) (s₀ t₀ S T : List (Letter I)) :
    ((pres RD k).obj (ob RD (wt RD μ []) S) ⟶ (pres RD k).obj (ob RD (wt RD μ []) T))
      →ₗ[k] ((pres RD k).obj (ob RD μ s₀) ⟶ (pres RD k).obj (ob RD μ t₀)) :=
  ctxL RD k μ s₀ t₀ ((cupA (dns d)).map (whL [] s₀)) (dns d) []
    ((capA (rd (dns d))).map (whL [] t₀)) S T

theorem sChain_cupA_R (b : List I) (s₀ S : List (Letter I)) (hS : S = s₀ ++ rd (dns b)) :
    SChain s₀ ((cupA (rd (dns b))).map (whL s₀ [])) ([] ++ S ++ dns b) := by
  subst hS; simpa using (sChain_cupA (rd (dns b))).whisk s₀ []

theorem sChain_capA_R (b : List I) (t₀ T : List (Letter I)) (hT : T = t₀ ++ rd (dns b)) :
    SChain ([] ++ T ++ dns b) ((capA (dns b)).map (whL t₀ [])) t₀ := by
  subst hT; simpa using (sChain_capA (dns b)).whisk t₀ []

theorem sChain_cupA_L (d : List I) (s₀ S : List (Letter I)) (hS : S = rd (dns d) ++ s₀) :
    SChain s₀ ((cupA (dns d)).map (whL [] s₀)) (dns d ++ S ++ []) := by
  subst hS; simpa using (sChain_cupA (dns d)).whisk [] s₀

theorem sChain_capA_L (d : List I) (t₀ T : List (Letter I)) (hT : T = rd (dns d) ++ t₀) :
    SChain (dns d ++ T ++ []) ((capA (rd (dns d))).map (whL [] t₀)) t₀ := by
  subst hT; simpa using (sChain_capA (rd (dns d))).whisk [] t₀

theorem ptrRL_dg (μ : X) (b : List I) {s₀ t₀ S T : List (Letter I)} (hS : S = s₀ ++ rd (dns b))
    (hT : T = t₀ ++ rd (dns b)) (A : List (LayerData I)) :
    ptrRL RD k μ b s₀ t₀ S T (dg RD k (wt RD μ (dns b)) S T A) =
      dg RD k μ s₀ t₀ ((cupA (rd (dns b))).map (whL s₀ []) ++ A.map (whL [] (dns b)) ++
        (capA (dns b)).map (whL t₀ [])) :=
  ctxL_dg RD k μ (sChain_cupA_R b s₀ S hS) (sChain_capA_R b t₀ T hT) A

theorem ptrLL_dg (μ : X) (d : List I) {s₀ t₀ S T : List (Letter I)} (hS : S = rd (dns d) ++ s₀)
    (hT : T = rd (dns d) ++ t₀) (A : List (LayerData I)) :
    ptrLL RD k μ d s₀ t₀ S T (dg RD k (wt RD μ []) S T A) =
      dg RD k μ s₀ t₀ ((cupA (dns d)).map (whL [] s₀) ++ A.map (whL (dns d) []) ++
        (capA (rd (dns d))).map (whL [] t₀)) :=
  ctxL_dg RD k μ (sChain_cupA_L d s₀ S hS) (sChain_capA_L d t₀ T hT) A

/-- The block trace is the iterated partial trace `ptrLast`, the first colour innermost. -/
theorem ptrRL_cons (μ : X) (j : I) (b : List I) (s₀ t₀ : List (Letter I))
    (h : (pres RD k).obj (ob RD (wt RD μ (dns (j :: b))) ((s₀ ++ rd (dns b)) ++ [up j])) ⟶
      (pres RD k).obj (ob RD (wt RD μ (dns (j :: b))) ((t₀ ++ rd (dns b)) ++ [up j]))) :
    ptrRL RD k μ (j :: b) s₀ t₀ _ _ h =
      ptrRL RD k μ b s₀ t₀ (s₀ ++ rd (dns b)) (t₀ ++ rd (dns b))
        (ptrLast RD k (wt RD μ (dns b)) (s₀ ++ rd (dns b)) (t₀ ++ rd (dns b)) j h) := by
  have key := hom_ext_dg RD k (wt RD μ (dns (j :: b)))
    (s := (s₀ ++ rd (dns b)) ++ [up j]) (t := (t₀ ++ rd (dns b)) ++ [up j])
    (ptrRL RD k μ (j :: b) s₀ t₀ _ _)
    ((ptrRL RD k μ b s₀ t₀ (s₀ ++ rd (dns b)) (t₀ ++ rd (dns b))).comp
      (ptrLast RD k (wt RD μ (dns b)) (s₀ ++ rd (dns b)) (t₀ ++ rd (dns b)) j))
    (fun A hA => ?_)
  · exact LinearMap.congr_fun key h
  rw [LinearMap.comp_apply, ptrRL_dg μ (j :: b) (by simp) (by simp)]
  erw [ptrLast_dg]
  rw [ptrRL_dg μ b rfl rfl]
  refine dg_list_eq ?_
  simp only [dns, List.map_cons, rd_cons, cupA_append_single, rd_rd, capA, closeLs]
  laysimp

/-- The left block trace is the iterated partial trace `ptrFirst`, the first colour outermost. -/
theorem ptrLL_cons (μ : X) (j : I) (d : List I) (s₀ t₀ : List (Letter I))
    (h : (pres RD k).obj (ob RD (wt RD μ []) (rd (dns d) ++ up j :: s₀)) ⟶
      (pres RD k).obj (ob RD (wt RD μ []) (rd (dns d) ++ up j :: t₀))) :
    ptrLL RD k μ (j :: d) s₀ t₀ _ _ h =
      ptrFirst RD k μ s₀ t₀ j (ptrLL RD k μ d (up j :: s₀) (up j :: t₀) _ _ h) := by
  have key := hom_ext_dg RD k (wt RD μ [])
    (s := rd (dns d) ++ up j :: s₀) (t := rd (dns d) ++ up j :: t₀)
    (ptrLL RD k μ (j :: d) s₀ t₀ _ _)
    ((ptrFirst RD k μ s₀ t₀ j).comp (ptrLL RD k μ d (up j :: s₀) (up j :: t₀) _ _))
    (fun A hA => ?_)
  · exact LinearMap.congr_fun key h
  rw [LinearMap.comp_apply, ptrLL_dg μ (j :: d) (by simp) (by simp)]
  erw [ptrLL_dg μ d (s₀ := up j :: s₀) (t₀ := up j :: t₀) rfl rfl]
  erw [ptrFirst_dg]
  refine dg_list_eq ?_
  simp only [dns, List.map_cons, rd_cons, capA_append_single, rd_rd, cupA, closeLsL]
  laysimp

theorem ptrLast_mem_upSpan'' (hSL : SimplyLaced C) [DecidableEq I] (ν : X) (j : I)
    {s t : List (Letter I)} (hs : Positive s) (ht : Positive t) {f}
    (hf : f ∈ upSpan RD k (wt RD ν [dn j]) (s ++ [up j]) (t ++ [up j])) :
    ptrLast RD k ν s t j f ∈ upSpan RD k ν s t :=
  ptrLast_mem_upSpan' RD k hSL ν j hs ht hf

theorem ptrFirst_mem_upSpan' (hSL : SimplyLaced C) [DecidableEq I] (μ : X) (j : I)
    {s t : List (Letter I)} (hs : Positive s) (ht : Positive t) {f}
    (hf : f ∈ upSpan RD k (wt RD μ []) ([up j] ++ s) ([up j] ++ t)) :
    ptrFirst RD k μ s t j f ∈ upSpan RD k μ s t := by
  obtain ⟨a, rfl⟩ : ∃ a, ups a = s := ⟨_, ups_map_snd hs⟩
  obtain ⟨b, rfl⟩ : ∃ b, ups b = t := ⟨_, ups_map_snd ht⟩
  exact ptrFirst_mem_upSpan μ j hSL a b hf

/-- **The Markov lemma for blocks of strands, on the right**: the right partial trace over a
block of strands preserves `upSpan` (simply-laced Cartan data). -/
theorem ptrRL_mem_upSpan (hSL : SimplyLaced C) [DecidableEq I] :
    ∀ (b : List I) (μ : X) {s₀ t₀ : List (Letter I)}, Positive s₀ → Positive t₀ →
      ∀ {S T : List (Letter I)}, S = s₀ ++ rd (dns b) → T = t₀ ++ rd (dns b) →
        ∀ {h}, h ∈ upSpan RD k (wt RD μ (dns b)) S T →
          ptrRL RD k μ b s₀ t₀ S T h ∈ upSpan RD k μ s₀ t₀
  | [] => by
    intro μ s₀ t₀ _ _ S T hS hT h hh
    simp only [rd_nil, dns, List.map_nil, List.append_nil] at hS hT
    subst hS hT
    exact upSpan_ctxL (fun x hx => by simp at hx) (fun x hx => by simp at hx)
      (by simp) (by simp) hh
  | j :: b => by
    intro μ s₀ t₀ hs ht S T hS hT h hh
    obtain rfl : S = (s₀ ++ rd (dns b)) ++ [up j] := by rw [hS]; simp
    obtain rfl : T = (t₀ ++ rd (dns b)) ++ [up j] := by rw [hT]; simp
    rw [ptrRL_cons]
    refine ptrRL_mem_upSpan hSL b μ hs ht rfl rfl ?_
    exact ptrLast_mem_upSpan'' hSL _ j (positive_append.2 ⟨hs, positive_rd_dns b⟩)
      (positive_append.2 ⟨ht, positive_rd_dns b⟩) hh

/-- **The Markov lemma for blocks of strands, on the left**: the left partial trace over a block
of strands preserves `upSpan` (simply-laced Cartan data). -/
theorem ptrLL_mem_upSpan (hSL : SimplyLaced C) [DecidableEq I] :
    ∀ (d : List I) (μ : X) {s₀ t₀ : List (Letter I)}, Positive s₀ → Positive t₀ →
      ∀ {S T : List (Letter I)}, S = rd (dns d) ++ s₀ → T = rd (dns d) ++ t₀ →
        ∀ {h}, h ∈ upSpan RD k (wt RD μ []) S T →
          ptrLL RD k μ d s₀ t₀ S T h ∈ upSpan RD k μ s₀ t₀
  | [] => by
    intro μ s₀ t₀ _ _ S T hS hT h hh
    simp only [rd_nil, dns, List.map_nil, List.nil_append] at hS hT
    subst hS hT
    exact upSpan_ctxL (fun x hx => by simp at hx) (fun x hx => by simp at hx)
      (by simp) (by simp) hh
  | j :: d => by
    intro μ s₀ t₀ hs ht S T hS hT h hh
    obtain rfl : S = rd (dns d) ++ up j :: s₀ := by rw [hS]; simp
    obtain rfl : T = rd (dns d) ++ up j :: t₀ := by rw [hT]; simp
    rw [ptrLL_cons]
    refine ptrFirst_mem_upSpan' hSL μ j hs ht ?_
    exact ptrLL_mem_upSpan hSL d μ (positive_cons.2 ⟨rfl, hs⟩) (positive_cons.2 ⟨rfl, ht⟩)
      rfl rfl hh

/-! ## Unbending -/

variable (RD k) in
/-- **Unbending on the right**: a 2-morphism `E_{s b̄} 1_ν ⟶ E_a 1_ν` (`ν = μ + (F_b)_X`,
`b̄ = rd (dns b)`) gives `E_s 1_μ ⟶ E_a F_b 1_μ`: nested cups `1 → E_{b̄} F_b` on the right,
then the 2-morphism next to the downward strands `F_b`. -/
def unbendR (μ : X) (b : List I) (s a : List (Letter I)) :
    ((pres RD k).obj (ob RD (wt RD μ (dns b)) (s ++ rd (dns b))) ⟶
        (pres RD k).obj (ob RD (wt RD μ (dns b)) a)) →ₗ[k]
      ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ (a ++ dns b))) :=
  ctxL RD k μ s (a ++ dns b) ((cupA (rd (dns b))).map (whL s [])) [] (dns b) [] (s ++ rd (dns b)) a

variable (RD k) in
/-- **Unbending on the left**: a 2-morphism `E_{d̄ s} 1_μ ⟶ E_c 1_μ` (`d̄ = rd (dns d)`) gives
`E_s 1_μ ⟶ F_d E_c 1_μ`: nested cups `1 → F_d E_{d̄}` on the left, then the 2-morphism next to
the downward strands `F_d`. -/
def unbendL (μ : X) (d : List I) (s c : List (Letter I)) :
    ((pres RD k).obj (ob RD (wt RD μ []) (rd (dns d) ++ s)) ⟶
        (pres RD k).obj (ob RD (wt RD μ []) c)) →ₗ[k]
      ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ (dns d ++ c))) :=
  ctxL RD k μ s (dns d ++ c) ((cupA (dns d)).map (whL [] s)) (dns d) [] [] (rd (dns d) ++ s) c

theorem unbendR_dg (μ : X) (b : List I) (s a : List (Letter I)) (A : List (LayerData I)) :
    unbendR RD k μ b s a (dg RD k (wt RD μ (dns b)) (s ++ rd (dns b)) a A) =
      dg RD k μ s (a ++ dns b) ((cupA (rd (dns b))).map (whL s []) ++ A.map (whL [] (dns b))) := by
  have := ctxL_dg RD k μ (sChain_cupA_R b s _ rfl) (show SChain ([] ++ a ++ dns b) [] (a ++ dns b)
    by simp) A
  simpa using this

theorem unbendL_dg (μ : X) (d : List I) (s c : List (Letter I)) (B : List (LayerData I)) :
    unbendL RD k μ d s c (dg RD k (wt RD μ []) (rd (dns d) ++ s) c B) =
      dg RD k μ s (dns d ++ c) ((cupA (dns d)).map (whL [] s) ++ B.map (whL (dns d) [])) := by
  have := ctxL_dg RD k μ (sChain_cupA_L d s _ rfl) (show SChain (dns d ++ c ++ []) [] (dns d ++ c)
    by simp) B
  simpa using this

/-! ## Bending and unbending on both sides -/

/-- A diagram `x q → p y` with the block `q` at the bottom right bent up on the right (nested
cups `1 → q (rd q)`) and the block `p` at the top left bent down on the left (nested caps
`(rd p) p → 1`): a diagram `(rd p) x → y (rd q)`. -/
def sharpL (p q x y : List (Letter I)) (M : List (LayerData I)) : List (LayerData I) :=
  (cupA q).map (whL (rd p ++ x) []) ++ M.map (whL (rd p) (rd q)) ++
    (capA p).map (whL [] (y ++ rd q))

/-- A diagram `(rd p) x → y (rd q)` with the block `rd p` at the bottom left bent up on the left
(nested cups `1 → p (rd p)`) and the block `rd q` at the top right bent down on the right (nested
caps `(rd q) q → 1`): a diagram `x q → p y`. -/
def flatL (p q x y : List (Letter I)) (M : List (LayerData I)) : List (LayerData I) :=
  (cupA p).map (whL [] (x ++ q)) ++ M.map (whL p q) ++ (capA q).map (whL (p ++ y) [])

theorem sChain_sharpL {p q x y : List (Letter I)} {M : List (LayerData I)}
    (hM : SChain (x ++ q) M (p ++ y)) : SChain (rd p ++ x) (sharpL p q x y M) (y ++ rd q) := by
  have h1 : SChain (rd p ++ x) ((cupA q).map (whL (rd p ++ x) [])) (rd p ++ (x ++ q) ++ rd q) := by
    simpa using (sChain_cupA q).whisk (rd p ++ x) []
  have h2 : SChain (rd p ++ (x ++ q) ++ rd q) (M.map (whL (rd p) (rd q)))
      ((rd p ++ p) ++ (y ++ rd q)) := by simpa using hM.whisk (rd p) (rd q)
  have h3 : SChain ((rd p ++ p) ++ (y ++ rd q)) ((capA p).map (whL [] (y ++ rd q)))
      (y ++ rd q) := by
    simpa using (sChain_capA p).whisk [] (y ++ rd q)
  exact (h1.append h2).append h3

theorem sChain_flatL {p q x y : List (Letter I)} {M : List (LayerData I)}
    (hM : SChain (rd p ++ x) M (y ++ rd q)) : SChain (x ++ q) (flatL p q x y M) (p ++ y) := by
  have h1 : SChain (x ++ q) ((cupA p).map (whL [] (x ++ q))) (p ++ (rd p ++ x) ++ q) := by
    simpa using (sChain_cupA p).whisk [] (x ++ q)
  have h2 : SChain (p ++ (rd p ++ x) ++ q) (M.map (whL p q)) ((p ++ y) ++ (rd q ++ q)) := by
    simpa using hM.whisk p q
  have h3 : SChain ((p ++ y) ++ (rd q ++ q)) ((capA q).map (whL (p ++ y) [])) (p ++ y) := by
    simpa using (sChain_capA q).whisk (p ++ y) []
  exact (h1.append h2).append h3

/-- **Unbending a bent diagram gives it back** (`sharpL`): zigzag relations for blocks and the
interchange law. -/
theorem dg_unbend_sharp (p q x y : List (Letter I)) {M : List (LayerData I)}
    (hM : SChain (x ++ q) M (p ++ y)) (μ : X) :
    dg RD k μ (x ++ q) (p ++ y) ((cupA p).map (whL [] (x ++ q)) ++
      (sharpL p q x y M).map (whL p q) ++ (capA q).map (whL (p ++ y) [])) =
      dg RD k μ (x ++ q) (p ++ y) M := by
  have hA : SChain (p ++ rd p ++ (x ++ q)) (M.map (whL (p ++ rd p) []) ++
      (capA p).map (whL p y)) (p ++ y) := by
    refine (show SChain (p ++ rd p ++ (x ++ q)) (M.map (whL (p ++ rd p) [])) (p ++ rd p ++ p ++ y)
      by simpa using hM.whisk (p ++ rd p) []).append ?_
    simpa using (sChain_capA p).whisk p y
  have ei1 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := x ++ q) (T := p ++ y)
    ((cupA p).map (whL [] (x ++ q)) ++ (cupA q).map (whL (p ++ rd p ++ x) q)) [] hA
    (B := capA q) (t := rd q ++ q) (t' := []) (sChain_capA q)
  have hz1 := dg_step RD k μ (s₀ := x ++ q) (t₀ := p ++ y) ((cupA p).map (whL [] (x ++ q)))
    (M.map (whL (p ++ rd p) []) ++ (capA p).map (whL p y)) (p ++ rd p ++ x) []
    (dg_zigA q (wt RD μ []))
    (by simpa using (sChain_cupA p).whisk [] (x ++ q)) (by simpa using hA) rfl rfl
  have ei2 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := x ++ q) (T := p ++ y)
    [] ((capA p).map (whL p y)) (sChain_cupA p) (B := M) (t := x ++ q) (t' := p ++ y) hM
  have hz2 := dg_step RD k μ (s₀ := x ++ q) (t₀ := p ++ y) M [] [] y (dg_zigA p (wt RD μ y))
    (by simpa using hM) (by simp) rfl rfl
  calc dg RD k μ (x ++ q) (p ++ y) ((cupA p).map (whL [] (x ++ q)) ++
        (sharpL p q x y M).map (whL p q) ++ (capA q).map (whL (p ++ y) []))
      = dg RD k μ (x ++ q) (p ++ y) (((cupA p).map (whL [] (x ++ q)) ++
          (cupA q).map (whL (p ++ rd p ++ x) q)) ++
          (M.map (whL (p ++ rd p) []) ++ (capA p).map (whL p y)).map (whL [] (rd q ++ q)) ++
            (capA q).map (whL (p ++ y) []) ++ []) := dg_list_eq (by simp [sharpL]; laysimp)
    _ = _ := ei1
    _ = dg RD k μ (x ++ q) (p ++ y) ((cupA p).map (whL [] (x ++ q)) ++
          ((cupA q).map (whL [] q) ++ (capA q).map (whL q [])).map (whL (p ++ rd p ++ x) []) ++
            (M.map (whL (p ++ rd p) []) ++ (capA p).map (whL p y))) :=
        dg_list_eq (by laysimp)
    _ = _ := hz1
    _ = dg RD k μ (x ++ q) (p ++ y) ([] ++ (cupA p).map (whL [] (x ++ q)) ++
          M.map (whL (p ++ rd p) []) ++ (capA p).map (whL p y)) := dg_list_eq (by laysimp)
    _ = _ := ei2
    _ = dg RD k μ (x ++ q) (p ++ y) (M ++ ((cupA p).map (whL [] p) ++
          (capA p).map (whL p [])).map (whL [] y) ++ []) := dg_list_eq (by laysimp)
    _ = _ := hz2
    _ = dg RD k μ (x ++ q) (p ++ y) M := dg_list_eq (by laysimp)

/-- **Unbending a bent diagram gives it back** (`flatL`): zigzag relations for blocks and the
interchange law. -/
theorem dg_unbend_flat (p q x y : List (Letter I)) {M : List (LayerData I)}
    (hM : SChain (rd p ++ x) M (y ++ rd q)) (μ : X) :
    dg RD k μ (rd p ++ x) (y ++ rd q) ((cupA q).map (whL (rd p ++ x) []) ++
      (flatL p q x y M).map (whL (rd p) (rd q)) ++ (capA p).map (whL [] (y ++ rd q))) =
      dg RD k μ (rd p ++ x) (y ++ rd q) M := by
  have hA : SChain (rd p ++ x) ((cupA p).map (whL (rd p) x) ++ M.map (whL (rd p ++ p) []))
      (rd p ++ p ++ (y ++ rd q)) := by
    refine (show SChain (rd p ++ x) ((cupA p).map (whL (rd p) x)) (rd p ++ p ++ (rd p ++ x))
      by simpa using (sChain_cupA p).whisk (rd p) x).append ?_
    simpa using hM.whisk (rd p ++ p) []
  have ei1 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := rd p ++ x) (T := y ++ rd q)
    [] ((capA q).map (whL (rd p ++ p ++ y) (rd q)) ++ (capA p).map (whL [] (y ++ rd q))) hA
    (B := cupA q) (t := []) (t' := q ++ rd q) (sChain_cupA q)
  have hz1 := dg_step RD k μ (s₀ := rd p ++ x) (t₀ := y ++ rd q)
    ((cupA p).map (whL (rd p) x) ++ M.map (whL (rd p ++ p) []))
    ((capA p).map (whL [] (y ++ rd q))) (rd p ++ p ++ y) [] (dg_zigB q (wt RD μ []))
    (by simpa using hA) (by simpa using (sChain_capA p).whisk [] (y ++ rd q)) rfl rfl
  have ei2 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := rd p ++ x) (T := y ++ rd q)
    ((cupA p).map (whL (rd p) x)) [] (sChain_capA p) (B := M) (t := rd p ++ x) (t' := y ++ rd q) hM
  have hz2 := dg_step RD k μ (s₀ := rd p ++ x) (t₀ := y ++ rd q) [] M [] x (dg_zigB p (wt RD μ x))
    (by simp) (by simpa using hM) rfl rfl
  calc dg RD k μ (rd p ++ x) (y ++ rd q) ((cupA q).map (whL (rd p ++ x) []) ++
        (flatL p q x y M).map (whL (rd p) (rd q)) ++ (capA p).map (whL [] (y ++ rd q)))
      = dg RD k μ (rd p ++ x) (y ++ rd q) ([] ++ (cupA q).map (whL (rd p ++ x) []) ++
          ((cupA p).map (whL (rd p) x) ++ M.map (whL (rd p ++ p) [])).map (whL [] (q ++ rd q)) ++
            ((capA q).map (whL (rd p ++ p ++ y) (rd q)) ++ (capA p).map (whL [] (y ++ rd q)))) :=
        dg_list_eq (by simp [flatL]; laysimp)
    _ = _ := ei1.symm
    _ = dg RD k μ (rd p ++ x) (y ++ rd q)
          (((cupA p).map (whL (rd p) x) ++ M.map (whL (rd p ++ p) [])) ++
            ((cupA q).map (whL (rd q) []) ++ (capA q).map (whL [] (rd q))).map
              (whL (rd p ++ p ++ y) []) ++ (capA p).map (whL [] (y ++ rd q))) :=
        dg_list_eq (by laysimp)
    _ = _ := hz1
    _ = dg RD k μ (rd p ++ x) (y ++ rd q) ((cupA p).map (whL (rd p) x) ++
          M.map (whL (rd p ++ p) []) ++ (capA p).map (whL [] (y ++ rd q)) ++ []) :=
        dg_list_eq (by laysimp)
    _ = _ := ei2.symm
    _ = dg RD k μ (rd p ++ x) (y ++ rd q) ([] ++ ((cupA p).map (whL (rd p) []) ++
          (capA p).map (whL [] (rd p))).map (whL [] x) ++ M) := dg_list_eq (by laysimp)
    _ = _ := hz2
    _ = dg RD k μ (rd p ++ x) (y ++ rd q) M := dg_list_eq (by laysimp)

/-- **Unbending on the right after bending on the right is the identity.** -/
theorem dg_unbendR_bendR (q s a : List (Letter I)) {P : List (LayerData I)}
    (hP : SChain s P (a ++ rd q)) (μ : X) :
    dg RD k μ s (a ++ rd q) ((cupA q).map (whL s []) ++
      (P.map (whL [] q) ++ (capA q).map (whL a [])).map (whL [] (rd q))) =
      dg RD k μ s (a ++ rd q) P := by
  have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := a ++ rd q)
    [] ((capA q).map (whL a (rd q))) hP (B := cupA q) (t := []) (t' := q ++ rd q) (sChain_cupA q)
  have hz := dg_step RD k μ (s₀ := s) (t₀ := a ++ rd q) (P.map (whL [] [])) [] a []
    (dg_zigB q (wt RD μ [])) (by simpa using hP) (by simp) rfl rfl
  calc dg RD k μ s (a ++ rd q) ((cupA q).map (whL s []) ++
        (P.map (whL [] q) ++ (capA q).map (whL a [])).map (whL [] (rd q)))
      = dg RD k μ s (a ++ rd q) ([] ++ (cupA q).map (whL s []) ++ P.map (whL [] (q ++ rd q)) ++
          (capA q).map (whL a (rd q))) := dg_list_eq (by laysimp)
    _ = _ := ei.symm
    _ = dg RD k μ s (a ++ rd q) (P.map (whL [] []) ++ ((cupA q).map (whL (rd q) []) ++
          (capA q).map (whL [] (rd q))).map (whL a []) ++ []) := dg_list_eq (by laysimp)
    _ = _ := hz
    _ = dg RD k μ s (a ++ rd q) P := dg_list_eq (by laysimp)

end Categorification.KL3.Diagram
