/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.MarkovLeft
import Categorification.Diagrams.CLQ.Pitchfork
import Categorification.Diagrams.KL3.Straighten

/-!
# Straightening monotone diagrams

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1
(Definition 3.1: biadjointness (3.1), (3.2) and cyclicity (3.3), `eq_cyclic_cross-gen`), used in
§3.2.2 (proof of Lemma 3.9, label `lem_surjective`; TeX locators
`sources/klr/kl3/0807.3250v1.txt`, lines 1690–1790).

A normal-form diagram of `U` is **monotone of type `RL`** if its cups are all of the form
`1 → F_j E_j` and its caps all of the form `E_j F_j → 1` (together with arbitrary dots and
crossings), and **monotone of type `LR`** if its cups are all `1 → E_j F_j` and its caps all
`F_j E_j → 1`. In a monotone diagram every strand turns in the same direction at each cup and
each cap, so that a monotone diagram between two upward sequences is isotopic to an upward
diagram. This file proves this with the relations of `U`:

* downward dots and downward crossings are rotations of upward ones (KL III (3.3),
  `eq_cyclic_cross-gen`), by cups and caps of the same type (`rotRL_dg`, `rotLR_dg`), up to a scalar `t_ij⁻¹` per
  downward crossing (Cautis–Lauda's normalization of the cyclicity relation);
* afterwards a downward strand is never touched between the cup creating it and the cap
  consuming it. All layers in between act either to its left or to its right (`Sep`), so they
  can be moved below the cup or above the cap by the interchange law (`Sep.dg_eq`); the cup and
  the cap then form a zigzag, which is removed (KL III (3.1), (3.2)).

No relation other than the interchange law, the zigzag relations and the cyclicity relations is
used; in particular no relation holds only modulo diagrams with fewer crossings.

## Main results

* `straightenRL`, `straightenLR`: **a monotone diagram (of either type) between two upward
  sequences is a scalar multiple of an upward diagram** (with the same boundary).
* `straightenRL_mem_upSpan`, `straightenLR_mem_upSpan`: such diagrams lie in `upSpan`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-! ## Monotone shapes -/

namespace Shape





end Shape











/-! ## Layers separated by a downward strand -/


/-- **Layers not touching a downward strand split into a left and a right part** (interchange
law): `B` equals its left part (with the strand and everything to its right as spectators)
followed by its right part. -/
theorem Sep.dg_eq {j : I} {L R : List (Letter I)} {B : List (LayerData I)}
    {L' R' : List (Letter I)} (hS : Sep j L R B L' R') :
    ∃ BL BR : List (LayerData I), SChain L BL L' ∧ SChain R BR R' ∧
      List.Perm ((BL ++ BR).map (·.2.1)) (B.map (·.2.1)) ∧
      ∀ (μ : X) (S T : List (Letter I)) (pre post : List (LayerData I)),
        dg RD k sc μ S T (pre ++ B ++ post) =
          dg RD k sc μ S T (pre ++ BL.map (whL [] (dn j :: R)) ++
            BR.map (whL (L' ++ [dn j]) []) ++ post) := by
  induction hS with
  | nil L R => exact ⟨[], [], rfl, rfl, by simp, fun μ S T pre post => by simp⟩
  | left u v R g hS ih =>
    obtain ⟨BL, BR, hL, hR, hp, hd⟩ := ih
    refine ⟨(u, g, v) :: BL, BR, ⟨rfl, hL⟩, hR, ?_, fun μ S T pre post => ?_⟩
    · simpa using hp
    · have e := hd μ S T (pre ++ [(u, g, v ++ dn j :: R)]) post
      simp only [List.append_assoc, List.singleton_append] at e ⊢
      rw [e]
      simp [whL]
  | right L u v g hS ih =>
    rename_i B L' R'
    obtain ⟨BL, BR, hL, hR, hp, hd⟩ := ih
    refine ⟨BL, (u, g, v) :: BR, hL, ⟨rfl, hR⟩, ?_, fun μ S T pre post => ?_⟩
    · simp only [List.map_append, List.map_cons]
      refine List.perm_middle.trans ?_
      simpa using hp
    · have e := hd μ S T (pre ++ [(L ++ dn j :: u, g, v)]) post
      have ei := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := S) (T := T) pre
        (BR.map (whL (L' ++ [dn j]) []) ++ post) hL
        (B := [(dn j :: u, g, v)]) (t := dn j :: (u ++ g.dom ++ v))
        (t' := dn j :: (u ++ g.cod ++ v)) ⟨by simp, by simp⟩
      simp only [List.append_assoc, List.singleton_append] at e ei ⊢
      rw [e]
      simp only [whL, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
        List.nil_append, List.append_assoc] at ei ⊢
      rw [← ei]

/-! ## Locating a strand in a layer -/




/-! ## The first cup and its partner cap -/







/-! ## Removing a downward strand -/

theorem dg_list_eq {μ : X} {s t : List (Letter I)} {L L' : List (LayerData I)} (h : L = L') :
    dg RD k sc μ s t L = dg RD k sc μ s t L' := by rw [h]


/-- **Elimination of downward strands** (type `RL`): a rotated monotone diagram of type `RL`
between upward sequences equals an upward diagram. By induction on the number of cups and caps:
the downward leg of the first cup is untouched until its partner cap (`findPartnerRL`); the
layers in between are moved below the cup or above the cap (`Sep.dg_eq`, interchange law), and
the cup and the cap cancel by a zigzag relation. -/
theorem elimRL : ∀ (n : ℕ) (ls : List (LayerData I)) {s t : List (Letter I)}, ncc ls < n →
    AllSh Shape.isRLu ls → Positive s → Positive t → SChain s ls t →
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∀ μ : X, dg RD k sc μ s t ls = dg RD k sc μ s t A := by
  intro n
  induction n with
  | zero => intro ls s t hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro ls s t hn hls hs ht h
    rcases firstCupRL ls hls hs h with hup | ⟨A₀, w₁, w₂, j, R, rfl, -, hA₀⟩
    · exact ⟨ls, hup, h, fun μ => rfl⟩
    have hR : SChain (w₁ ++ dn j :: up j :: w₂) R t := by
      have h' := (sChain_append_iff A₀ _ _ hA₀).1 h
      simpa using h'.2
    have hlsR : AllSh Shape.isRLu R := allSh_of_mem hls (fun y hy => by simp [hy])
    obtain ⟨B, L₁, R', C, rfl, hS, hC⟩ := findPartnerRL j R w₁ (up j :: w₂) hlsR ht hR
    obtain ⟨BL, BR, hBL, hBR, hp, hd⟩ := CLQ.Sep.dg_eq (RD := RD) (k := k) (sc := sc) hS
    have hB : AllSh Shape.isRLu B := allSh_of_mem hls (fun y hy => by simp [hy])
    have hBLR : AllSh Shape.isRLu (BL ++ BR) := AllSh.of_perm hp hB
    have hls' : AllSh Shape.isRLu (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) := by
      refine ((AllSh.append (allSh_of_mem hls (fun y hy => by simp [hy]))
        ((hBLR.of_append_left).map_whL _ _)).append ((hBLR.of_append_right).map_whL _ _)).append
        (allSh_of_mem hls (fun y hy => by simp [hy]))
    have hn' : ncc (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) < n := by
      have e1 := ncc_eq_of_perm hp
      simp only [ncc_append, ncc_map_whL] at e1 ⊢
      simp only [ncc_append, ncc_cons, Shape.isCupCap, ite_true] at hn
      omega
    have h1 : SChain (w₁ ++ w₂) (BL.map (whL [] w₂)) (L₁ ++ up j :: w₂) := by
      simpa using hBL.whisk [] w₂
    have h2 : SChain (L₁ ++ up j :: w₂) (BR.map (whL L₁ [])) (L₁ ++ R') := by
      simpa using hBR.whisk L₁ []
    have h' : SChain s (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) t :=
      ((hA₀.append h1).append h2).append hC
    obtain ⟨A, hAu, hA, hE⟩ := ih _ hn' hls' hs ht h'
    refine ⟨A, hAu, hA, fun μ => ?_⟩
    rw [← hE μ]
    have ei1 := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := s) (T := t) A₀
      (BR.map (whL (L₁ ++ [up j] ++ [dn j]) []) ++ ([(L₁, .cap (dn j), R')] ++ C)) hBL
      (B := [([], .cup (dn j), w₂)]) (t := w₂) (t' := dn j :: up j :: w₂) ⟨by simp, by simp⟩
    have ei2 := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := s) (T := t)
      (A₀ ++ BL.map (whL [] w₂) ++ [(L₁ ++ [up j], .cup (dn j), w₂)]) C
      (A := [(L₁, .cap (dn j), [])]) (s := L₁ ++ [up j, dn j]) (s' := L₁)
      ⟨by simp, by simp⟩ hBR
    have hz := dg_step RD k sc μ (s₀ := s) (t₀ := t) (A₀ ++ BL.map (whL [] w₂))
      (BR.map (whL L₁ []) ++ C) L₁ w₂ (dg_zigR' RD k sc (wt RD μ w₂) (dn j))
      (by simpa using hA₀.append h1) (by simpa using h2.append hC) rfl rfl
    calc dg RD k sc μ s t (A₀ ++ (w₁, Shape.cup (dn j), w₂) :: (B ++ (L₁, Shape.cap (dn j), R') :: C))
        = dg RD k sc μ s t ((A₀ ++ [(w₁, .cup (dn j), w₂)]) ++ B ++
            ([(L₁, .cap (dn j), R')] ++ C)) := dg_list_eq (by simp)
      _ = dg RD k sc μ s t ((A₀ ++ [(w₁, .cup (dn j), w₂)]) ++
            BL.map (whL [] (dn j :: up j :: w₂)) ++ BR.map (whL (L₁ ++ [up j] ++ [dn j]) []) ++
              ([(L₁, .cap (dn j), R')] ++ C)) := hd μ s t _ _
      _ = dg RD k sc μ s t (A₀ ++ BL.map (whL [] w₂) ++
            [([], Shape.cup (dn j), w₂)].map (whL (L₁ ++ [up j]) []) ++
              (BR.map (whL (L₁ ++ [up j] ++ [dn j]) []) ++ ([(L₁, .cap (dn j), R')] ++ C))) :=
          (dg_list_eq (by simp)).trans ei1.symm
      _ = dg RD k sc μ s t (A₀ ++ BL.map (whL [] w₂) ++ [(L₁ ++ [up j], .cup (dn j), w₂)] ++
            [(L₁, Shape.cap (dn j), [])].map (whL [] (up j :: w₂)) ++ BR.map (whL L₁ []) ++ C) :=
          (dg_list_eq (by simp)).trans ei2.symm
      _ = dg RD k sc μ s t (A₀ ++ BL.map (whL [] w₂) ++ [].map (whL L₁ w₂) ++
            (BR.map (whL L₁ []) ++ C)) := (dg_list_eq (by simp)).trans hz
      _ = dg RD k sc μ s t (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) :=
          dg_list_eq (by simp)

/-- **Elimination of downward strands** (type `LR`), the mirror of `elimRL`: the partner cap is
`F_j E_j → 1` and the zigzag is the other one. -/
theorem elimLR : ∀ (n : ℕ) (ls : List (LayerData I)) {s t : List (Letter I)}, ncc ls < n →
    AllSh Shape.isLRu ls → Positive s → Positive t → SChain s ls t →
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∀ μ : X, dg RD k sc μ s t ls = dg RD k sc μ s t A := by
  intro n
  induction n with
  | zero => intro ls s t hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro ls s t hn hls hs ht h
    rcases firstCupLR ls hls hs h with hup | ⟨A₀, w₁, w₂, j, R, rfl, -, hA₀⟩
    · exact ⟨ls, hup, h, fun μ => rfl⟩
    have hR : SChain ((w₁ ++ [up j]) ++ dn j :: w₂) R t := by
      have h' := (sChain_append_iff A₀ _ _ hA₀).1 h
      simpa using h'.2
    have hlsR : AllSh Shape.isLRu R := allSh_of_mem hls (fun y hy => by simp [hy])
    obtain ⟨B, L', R₁, C, rfl, hS, hC⟩ := findPartnerLR j R (w₁ ++ [up j]) w₂ hlsR ht hR
    obtain ⟨BL, BR, hBL, hBR, hp, hd⟩ := CLQ.Sep.dg_eq (RD := RD) (k := k) (sc := sc) hS
    have hB : AllSh Shape.isLRu B := allSh_of_mem hls (fun y hy => by simp [hy])
    have hBLR : AllSh Shape.isLRu (BL ++ BR) := AllSh.of_perm hp hB
    have hls' : AllSh Shape.isLRu (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) := by
      refine ((AllSh.append (allSh_of_mem hls (fun y hy => by simp [hy]))
        ((hBLR.of_append_right).map_whL _ _)).append ((hBLR.of_append_left).map_whL _ _)).append
        (allSh_of_mem hls (fun y hy => by simp [hy]))
    have hn' : ncc (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) < n := by
      have e1 := ncc_eq_of_perm hp
      simp only [ncc_append, ncc_map_whL] at e1 ⊢
      simp only [ncc_append, ncc_cons, Shape.isCupCap, ite_true] at hn
      omega
    have h1 : SChain (w₁ ++ w₂) (BR.map (whL w₁ [])) (w₁ ++ up j :: R₁) := by
      simpa using hBR.whisk w₁ []
    have h2 : SChain (w₁ ++ up j :: R₁) (BL.map (whL [] R₁)) (L' ++ R₁) := by
      simpa using hBL.whisk [] R₁
    have h' : SChain s (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) t :=
      ((hA₀.append h1).append h2).append hC
    obtain ⟨A, hAu, hA, hE⟩ := ih _ hn' hls' hs ht h'
    refine ⟨A, hAu, hA, fun μ => ?_⟩
    rw [← hE μ]
    have ei1 := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := s) (T := t)
      (A₀ ++ [(w₁, .cup (up j), w₂)]) ([(L', .cap (up j), R₁)] ++ C) hBL
      (B := BR.map (whL [dn j] [])) (t := dn j :: w₂) (t' := dn j :: up j :: R₁)
      (by simpa using hBR.whisk [dn j] [])
    have ei2 := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := s) (T := t) A₀
      (BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C))
      (A := [(w₁, .cup (up j), [])]) (s := w₁) (s' := w₁ ++ [up j, dn j])
      ⟨by simp, by simp⟩ hBR
    have ei3 := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := s) (T := t)
      (A₀ ++ BR.map (whL w₁ []) ++ [(w₁, .cup (up j), up j :: R₁)]) C hBL
      (B := [([], .cap (up j), R₁)]) (t := dn j :: up j :: R₁) (t' := R₁) ⟨by simp, by simp⟩
    have hz := dg_step RD k sc μ (s₀ := s) (t₀ := t) (A₀ ++ BR.map (whL w₁ []))
      (BL.map (whL [] R₁) ++ C) w₁ R₁ (dg_zigL' RD k sc (wt RD μ R₁) (up j))
      (by simpa using hA₀.append h1) (by simpa using h2.append hC) rfl rfl
    calc dg RD k sc μ s t (A₀ ++ (w₁, Shape.cup (up j), w₂) :: (B ++ (L', Shape.cap (up j), R₁) :: C))
        = dg RD k sc μ s t ((A₀ ++ [(w₁, .cup (up j), w₂)]) ++ B ++
            ([(L', .cap (up j), R₁)] ++ C)) := dg_list_eq (by simp)
      _ = dg RD k sc μ s t ((A₀ ++ [(w₁, .cup (up j), w₂)]) ++
            BL.map (whL [] (dn j :: w₂)) ++ BR.map (whL (L' ++ [dn j]) []) ++
              ([(L', .cap (up j), R₁)] ++ C)) := hd μ s t _ _
      _ = dg RD k sc μ s t ((A₀ ++ [(w₁, .cup (up j), w₂)]) ++
            (BR.map (whL [dn j] [])).map (whL (w₁ ++ [up j]) []) ++
              BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C)) :=
          (dg_list_eq (by simp)).trans ei1
      _ = dg RD k sc μ s t (A₀ ++ [(w₁, Shape.cup (up j), [])].map (whL [] w₂) ++
            BR.map (whL (w₁ ++ [up j, dn j]) []) ++
              (BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C))) :=
          dg_list_eq (by simp)
      _ = dg RD k sc μ s t (A₀ ++ BR.map (whL w₁ []) ++
            [(w₁, Shape.cup (up j), [])].map (whL [] (up j :: R₁)) ++
              (BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C))) := ei2
      _ = dg RD k sc μ s t ((A₀ ++ BR.map (whL w₁ []) ++ [(w₁, .cup (up j), up j :: R₁)]) ++
            BL.map (whL [] (dn j :: up j :: R₁)) ++ [([], Shape.cap (up j), R₁)].map (whL L' []) ++
              C) := dg_list_eq (by simp)
      _ = dg RD k sc μ s t ((A₀ ++ BR.map (whL w₁ []) ++ [(w₁, .cup (up j), up j :: R₁)]) ++
            [([], Shape.cap (up j), R₁)].map (whL (w₁ ++ [up j]) []) ++ BL.map (whL [] R₁) ++
              C) := ei3
      _ = dg RD k sc μ s t (A₀ ++ BR.map (whL w₁ []) ++
            [([], Shape.cup (up j), [up j]), ([up j], Shape.cap (up j), [])].map (whL w₁ R₁) ++
              (BL.map (whL [] R₁) ++ C)) := dg_list_eq (by simp)
      _ = dg RD k sc μ s t (A₀ ++ BR.map (whL w₁ []) ++ [].map (whL w₁ R₁) ++
            (BL.map (whL [] R₁) ++ C)) := hz
      _ = dg RD k sc μ s t (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) :=
          dg_list_eq (by simp)


/-! ## Rotating downward dots and crossings -/





/-- One rewriting step with a scalar: if `dg A = c • dg B` then the same holds in any
context (`dg_step`). -/
theorem dg_step_smul (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B L L' : List (LayerData I)} (c : k)
    (E : dg RD k sc (wt RD μ v) s t A = c • dg RD k sc (wt RD μ v) s t B)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    dg RD k sc μ s₀ t₀ L = c • dg RD k sc μ s₀ t₀ L' := by
  rw [hL, hL', ← ctxL_dg RD k sc μ hpre hpost A, E, map_smul, ctxL_dg RD k sc μ hpre hpost B]

/-- Rotating one layer of type `RL`: equal up to a scalar (a power of a `t_ij⁻¹`, from the
cyclicity of the crossing in Cautis–Lauda's normalization). -/
theorem rotRL_dg (x : LayerData I) {s t : List (Letter I)} (h : SChain s [x] t) :
    SChain s (rotRL x) t ∧
      ∃ c : k, ∀ μ : X, dg RD k sc μ s t [x] = c • dg RD k sc μ s t (rotRL x) := by
  obtain ⟨u, g, v⟩ := x
  obtain ⟨rfl, rfl⟩ := h
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    cases b
    · refine ⟨by simp [rotRL], 1, fun μ => ?_⟩
      rw [one_smul]
      exact dg_step RD k sc μ [] [] u v (dg_cycDotL RD k sc i (wt RD μ v)) (by simp) (by simp)
        (by simp) (by simp [rotRL])
    · exact ⟨by simp [rotRL], 1, fun μ => by rw [one_smul]; simp [rotRL]⟩
  | cross ε a c =>
    cases ε
    · refine ⟨by simp [rotRL], (((sc.t a c)⁻¹ : kˣ) : k), fun μ => ?_⟩
      exact dg_step_smul μ [] [] u v _ (dg_cycCrossL RD k sc a c (wt RD μ v)) (by simp)
        (by simp) (by simp) (by simp [rotRL])
    · exact ⟨by simp [rotRL], 1, fun μ => by rw [one_smul]; simp [rotRL]⟩
  | cup l => exact ⟨by simp [rotRL], 1, fun μ => by rw [one_smul]; simp [rotRL]⟩
  | cap l => exact ⟨by simp [rotRL], 1, fun μ => by rw [one_smul]; simp [rotRL]⟩

/-- Rotating one layer of type `LR`: equal up to a scalar. -/
theorem rotLR_dg (x : LayerData I) {s t : List (Letter I)} (h : SChain s [x] t) :
    SChain s (rotLR x) t ∧
      ∃ c : k, ∀ μ : X, dg RD k sc μ s t [x] = c • dg RD k sc μ s t (rotLR x) := by
  obtain ⟨u, g, v⟩ := x
  obtain ⟨rfl, rfl⟩ := h
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    cases b
    · refine ⟨by simp [rotLR], 1, fun μ => ?_⟩
      rw [one_smul]
      exact dg_step RD k sc μ [] [] u v (dg_cycDotR RD k sc i (wt RD μ v)) (by simp) (by simp)
        (by simp) (by simp [rotLR])
    · exact ⟨by simp [rotLR], 1, fun μ => by rw [one_smul]; simp [rotLR]⟩
  | cross ε a c =>
    cases ε
    · refine ⟨by simp [rotLR], (((sc.t c a)⁻¹ : kˣ) : k), fun μ => ?_⟩
      exact dg_step_smul μ [] [] u v _ (dg_cycCrossR RD k sc a c (wt RD μ v)) (by simp)
        (by simp) (by simp) (by simp [rotLR])
    · exact ⟨by simp [rotLR], 1, fun μ => by rw [one_smul]; simp [rotLR]⟩
  | cup l => exact ⟨by simp [rotLR], 1, fun μ => by rw [one_smul]; simp [rotLR]⟩
  | cap l => exact ⟨by simp [rotLR], 1, fun μ => by rw [one_smul]; simp [rotLR]⟩

theorem rotAll_dg (r : LayerData I → List (LayerData I))
    (hr : ∀ (x : LayerData I) {s t : List (Letter I)}, SChain s [x] t →
      SChain s (r x) t ∧ ∃ c : k, ∀ μ : X, dg RD k sc μ s t [x] = c • dg RD k sc μ s t (r x)) :
    ∀ (ls : List (LayerData I)) {s t : List (Letter I)}, SChain s ls t →
      SChain s (rotAll r ls) t ∧
        ∃ c : k, ∀ μ : X, dg RD k sc μ s t ls = c • dg RD k sc μ s t (rotAll r ls) := by
  intro ls
  induction ls with
  | nil => intro s t h; exact ⟨h, 1, fun μ => (one_smul _ _).symm⟩
  | cons x ls ih =>
    intro s t h
    have hx : SChain s [x] (x.1 ++ x.2.1.cod ++ x.2.2) := ⟨h.1, rfl⟩
    obtain ⟨hr1, c₁, hr2⟩ := hr x hx
    obtain ⟨hi1, c₂, hi2⟩ := ih h.2
    refine ⟨hr1.append hi1, c₁ * c₂, fun μ => ?_⟩
    rw [show x :: ls = [x] ++ ls from rfl, ← dg_comp hx h.2, hr2 μ, hi2 μ, Linear.smul_comp,
      Linear.comp_smul, smul_smul, dg_comp hr1 hi1]
    rfl


/-! ## Main results -/

/-- **A monotone diagram of type `RL` between upward sequences is a scalar multiple of an upward diagram**: all
cups are `1 → F_j E_j` and all caps `E_j F_j → 1` (dots and crossings arbitrary). -/
theorem straightenRL {s t : List (Letter I)} (hs : Positive s) (ht : Positive t)
    {ls : List (LayerData I)} (hls : AllSh Shape.isRL ls) (h : SChain s ls t) :
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∃ c : k, ∀ μ : X, dg RD k sc μ s t ls = c • dg RD k sc μ s t A := by
  obtain ⟨h1, c, h2⟩ := rotAll_dg (RD := RD) (k := k) (sc := sc) rotRL (fun x _ _ hx => rotRL_dg x hx) ls h
  obtain ⟨A, hA, hc, he⟩ := elimRL (RD := RD) (k := k) (sc := sc) _ (rotAll rotRL ls) (Nat.lt_succ_self _)
    (allSh_rotAll rotRL allSh_rotRL ls hls) hs ht h1
  exact ⟨A, hA, hc, c, fun μ => by rw [h2 μ, he μ]⟩

/-- **A monotone diagram of type `LR` between upward sequences is a scalar multiple of an upward diagram**: all
cups are `1 → E_j F_j` and all caps `F_j E_j → 1` (dots and crossings arbitrary). -/
theorem straightenLR {s t : List (Letter I)} (hs : Positive s) (ht : Positive t)
    {ls : List (LayerData I)} (hls : AllSh Shape.isLR ls) (h : SChain s ls t) :
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∃ c : k, ∀ μ : X, dg RD k sc μ s t ls = c • dg RD k sc μ s t A := by
  obtain ⟨h1, c, h2⟩ := rotAll_dg (RD := RD) (k := k) (sc := sc) rotLR (fun x _ _ hx => rotLR_dg x hx) ls h
  obtain ⟨A, hA, hc, he⟩ := elimLR (RD := RD) (k := k) (sc := sc) _ (rotAll rotLR ls) (Nat.lt_succ_self _)
    (allSh_rotAll rotLR allSh_rotLR ls hls) hs ht h1
  exact ⟨A, hA, hc, c, fun μ => by rw [h2 μ, he μ]⟩

theorem dg_upward_mem_upSpan {μ : X} {s t : List (Letter I)} {A : List (LayerData I)}
    (hA : Upward A) (h : SChain s A t) : dg RD k sc μ s t A ∈ upSpan RD k sc μ s t :=
  Submodule.subset_span ⟨A, 𝟙 _, hA, h, IsBub.id, by rw [bubAt_id, Category.comp_id]⟩

theorem straightenRL_mem_upSpan (μ : X) {s t : List (Letter I)} (hs : Positive s)
    (ht : Positive t) {ls : List (LayerData I)} (hls : AllSh Shape.isRL ls) (h : SChain s ls t) :
    dg RD k sc μ s t ls ∈ upSpan RD k sc μ s t := by
  obtain ⟨A, hA, hc, c, he⟩ := straightenRL (RD := RD) (k := k) (sc := sc) hs ht hls h
  rw [he μ]
  exact Submodule.smul_mem _ _ (dg_upward_mem_upSpan hA hc)

theorem straightenLR_mem_upSpan (μ : X) {s t : List (Letter I)} (hs : Positive s)
    (ht : Positive t) {ls : List (LayerData I)} (hls : AllSh Shape.isLR ls) (h : SChain s ls t) :
    dg RD k sc μ s t ls ∈ upSpan RD k sc μ s t := by
  obtain ⟨A, hA, hc, c, he⟩ := straightenLR (RD := RD) (k := k) (sc := sc) hs ht hls h
  rw [he μ]
  exact Submodule.smul_mem _ _ (dg_upward_mem_upSpan hA hc)

end Categorification.KL3.Diagram.CLQ
