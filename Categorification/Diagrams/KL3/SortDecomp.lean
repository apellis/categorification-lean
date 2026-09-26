/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Bending

/-!
# Sorting 1-morphisms of `U` by the decompositions of `E_i F_j` and `F_j E_i`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1: the relations `eq_downup_ij-gen` (`i ≠ j`) and `eq_ident_decomp` (`i = j`),
and §3.1.2, Propositions 3.3, 3.4 (bubble slides); used in §3.2.2 (proof of Lemma 3.9, label
`lem_surjective`; TeX locators `sources/klr/kl3/0807.3250v1.txt`, lines 1690–1790).

The identity of `F_j E_i 1_λ` factors through `E_i F_j 1_λ` (for `i ≠ j` the sideways crossings
are inverse isomorphisms; for `i = j`, `1 = -crossr ≫ crossl` plus terms factoring through `1_λ`,
with bubbles). Repeating this, the identity of every `E_w 1_μ` is a linear combination of
composites

`E_w → E_τ → E_w`, with `τ = E_a F_b` **sorted to the right** (all upward letters first),

in which the first map consists of sideways crossings `crossr` (`F E → E F`), caps `F E → 1` and
dots, and the second of sideways crossings `crossl` (`E F → F E`), cups `1 → F E` and dots, with
a bubble monomial on the far right (`decR`). In the terminology of
`Categorification.Diagrams.KL3.Straighten`, the first map is monotone of type `LR` and the
second of type `RL`. Symmetrically (`decL`) the identity factors through words `F_d E_c`
**sorted to the left**, the first map being monotone of type `RL` and the second of type `LR`.

The bubbles produced in the middle of a word are moved to the far right by the bubble slides
across strands of either orientation (`slideOutAny`), leaving dots.

## Main results

* `slideOutAny`: an element of the image of `Π` in any region is a linear combination of dots
  times bubble monomials on the far right.
* `decR`, `decL`: the decompositions of identities (simply-laced Cartan data).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Inversions -/

/-- The number of pairs (downward letter, later upward letter). -/
def invR : List (Letter I) → ℕ
  | [] => 0
  | l :: w => (if l.1 then 0 else w.countP (fun m => m.1)) + invR w

/-- The number of pairs (upward letter, later downward letter). -/
def invL : List (Letter I) → ℕ
  | [] => 0
  | l :: w => (if l.1 then w.countP (fun m => !m.1) else 0) + invL w

theorem countP_ups_dns_fst (a b : List I) :
    (ups a ++ dns b).countP (fun m : Letter I => m.1) = a.length := by
  simp [List.countP_append, List.countP_map, Function.comp_def]

theorem countP_ups_dns_snd (a b : List I) :
    (dns b ++ ups a).countP (fun m : Letter I => !m.1) = b.length := by
  simp [List.countP_append, List.countP_map, Function.comp_def]

theorem invR_eq_zero : ∀ w : List (Letter I), invR w = 0 → ∃ a b : List I, w = ups a ++ dns b
  | [] => fun _ => ⟨[], [], rfl⟩
  | (ε, i) :: w => fun h => by
    simp only [invR] at h
    obtain ⟨a, b, rfl⟩ := invR_eq_zero w (by omega)
    cases ε
    · have h1 : (ups a ++ dns b).countP (fun m : Letter I => m.1) = 0 := by
        simp only [Bool.false_eq_true, ↓reduceIte] at h; omega
      rw [countP_ups_dns_fst] at h1
      obtain rfl := List.eq_nil_of_length_eq_zero h1
      exact ⟨[], i :: b, rfl⟩
    · exact ⟨i :: a, b, rfl⟩

theorem invL_eq_zero : ∀ w : List (Letter I), invL w = 0 → ∃ d c : List I, w = dns d ++ ups c
  | [] => fun _ => ⟨[], [], rfl⟩
  | (ε, i) :: w => fun h => by
    simp only [invL] at h
    obtain ⟨d, c, rfl⟩ := invL_eq_zero w (by omega)
    cases ε
    · exact ⟨i :: d, c, rfl⟩
    · have h1 : (dns d ++ ups c).countP (fun m : Letter I => !m.1) = 0 := by
        simp only [↓reduceIte] at h; omega
      rw [countP_ups_dns_snd] at h1
      obtain rfl := List.eq_nil_of_length_eq_zero h1
      exact ⟨[], i :: c, rfl⟩

theorem invR_pos : ∀ w : List (Letter I), invR w ≠ 0 →
    ∃ (u v : List (Letter I)) (j i : I), w = u ++ dn j :: up i :: v
  | [] => fun h => (h rfl).elim
  | l :: w => fun h => by
    by_cases hw : invR w = 0
    · obtain ⟨a, b, rfl⟩ := invR_eq_zero w hw
      obtain ⟨ε, j⟩ := l
      simp only [invR, hw, add_zero] at h
      cases ε
      · simp only [Bool.false_eq_true, ↓reduceIte, countP_ups_dns_fst] at h
        obtain ⟨i, a, rfl⟩ : ∃ i a', a = i :: a' := by
          cases a with
          | nil => simp at h
          | cons i a' => exact ⟨i, a', rfl⟩
        exact ⟨[], ups a ++ dns b, j, i, rfl⟩
      · simp at h
    · obtain ⟨u, v, j, i, rfl⟩ := invR_pos w hw
      exact ⟨l :: u, v, j, i, rfl⟩

theorem invL_pos : ∀ w : List (Letter I), invL w ≠ 0 →
    ∃ (u v : List (Letter I)) (i j : I), w = u ++ up i :: dn j :: v
  | [] => fun h => (h rfl).elim
  | l :: w => fun h => by
    by_cases hw : invL w = 0
    · obtain ⟨d, c, rfl⟩ := invL_eq_zero w hw
      obtain ⟨ε, i⟩ := l
      simp only [invL, hw, add_zero] at h
      cases ε
      · simp at h
      · simp only [↓reduceIte, countP_ups_dns_snd] at h
        obtain ⟨j, d, rfl⟩ : ∃ j d', d = j :: d' := by
          cases d with
          | nil => simp at h
          | cons j d' => exact ⟨j, d', rfl⟩
        exact ⟨[], dns d ++ ups c, i, j, rfl⟩
    · obtain ⟨u, v, i, j, rfl⟩ := invL_pos w hw
      exact ⟨l :: u, v, i, j, rfl⟩

theorem invR_swap (i j : I) (v : List (Letter I)) :
    ∀ u : List (Letter I), invR (u ++ up i :: dn j :: v) < invR (u ++ dn j :: up i :: v)
  | [] => by simp [invR, List.countP_cons]
  | l :: u => by
    have := invR_swap i j v u
    have e : (u ++ up i :: dn j :: v).countP (fun m : Letter I => m.1) =
        (u ++ dn j :: up i :: v).countP (fun m : Letter I => m.1) := by
      simp [List.countP_append, List.countP_cons]
    simp only [List.cons_append, invR, e]
    omega

theorem invR_del (i j : I) (v : List (Letter I)) :
    ∀ u : List (Letter I), invR (u ++ v) < invR (u ++ dn j :: up i :: v)
  | [] => by simp [invR, List.countP_cons]
  | l :: u => by
    have := invR_del i j v u
    have e : (u ++ v).countP (fun m : Letter I => m.1) ≤
        (u ++ dn j :: up i :: v).countP (fun m : Letter I => m.1) := by
      simp [List.countP_append, List.countP_cons]
    simp only [List.cons_append, invR]
    split_ifs <;> omega

theorem invL_swap (i j : I) (v : List (Letter I)) :
    ∀ u : List (Letter I), invL (u ++ dn j :: up i :: v) < invL (u ++ up i :: dn j :: v)
  | [] => by simp [invL, List.countP_cons]
  | l :: u => by
    have := invL_swap i j v u
    have e : (u ++ dn j :: up i :: v).countP (fun m : Letter I => !m.1) =
        (u ++ up i :: dn j :: v).countP (fun m : Letter I => !m.1) := by
      simp [List.countP_append, List.countP_cons]
    simp only [List.cons_append, invL, e]
    omega

theorem invL_del (i j : I) (v : List (Letter I)) :
    ∀ u : List (Letter I), invL (u ++ v) < invL (u ++ up i :: dn j :: v)
  | [] => by simp [invL, List.countP_cons]
  | l :: u => by
    have := invL_del i j v u
    have e : (u ++ v).countP (fun m : Letter I => !m.1) ≤
        (u ++ up i :: dn j :: v).countP (fun m : Letter I => !m.1) := by
      simp [List.countP_append, List.countP_cons]
    simp only [List.cons_append, invL]
    split_ifs <;> omega

/-! ## Bubbles slide to the far right -/

/-- The shape is a dot. -/
def Shape.isDot : Shape I → Bool
  | .dot _ => true
  | _ => false

theorem Shape.isLR_of_isDot {g : Shape I} (h : g.isDot = true) : g.isLR = true := by
  cases g <;> simp_all [Shape.isDot, Shape.isLR]

theorem Shape.isRL_of_isDot {g : Shape I} (h : g.isDot = true) : g.isRL = true := by
  cases g <;> simp_all [Shape.isDot, Shape.isRL]

variable (RD k) in
/-- Dots on the strands `v` (to the right of `u`), inserted between `pre` and `post`, followed by
a bubble monomial on the far right. -/
def dotBubSpan (μ : X) (S T : List (Letter I)) (pre post : List (LayerData I))
    (u v : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ S) ⟶ (pres RD k).obj (ob RD μ T)) :=
  Submodule.span k {f | ∃ (D : List (LayerData I)) (δ : End ((pres RD k).obj (ob RD μ []))),
    AllSh Shape.isDot D ∧ SChain v D v ∧ IsBub RD k μ δ ∧
      f = dg RD k μ S T (pre ++ D.map (whL u []) ++ post) ≫ bubAt RD k μ T δ}

theorem dotBubSpan_mono (μ : X) (S T : List (Letter I)) (pre post : List (LayerData I))
    (u v' : List (Letter I)) (l : Letter I) (a : ℕ) :
    dotBubSpan RD k μ S T (pre ++ List.replicate a (u, .dot l, v')) post (u ++ [l]) v' ≤
      dotBubSpan RD k μ S T pre post u (l :: v') := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨D, δ, hD, hc, hδ, rfl⟩
  refine Submodule.subset_span ⟨List.replicate a ([], .dot l, v') ++ D.map (whL [l] []), δ,
    ?_, ?_, hδ, ?_⟩
  · refine AllSh.append (fun x hx => ?_) (hD.map_whL _ _)
    rw [List.eq_of_mem_replicate hx]; rfl
  · refine (SChain.replicate_of (x := ([], Shape.dot l, v')) ⟨by simp, by simp⟩ a).append ?_
    simpa using hc.whisk [l] []
  · refine congrArg (· ≫ _) (dg_list_eq ?_)
    simp [List.map_replicate, whL_def, List.map_map, Function.comp_def, List.append_assoc]

/-- **Bubbles slide to the far right across strands of either orientation** (KL III Propositions
3.3, 3.4 and their rotations; simply-laced): an element of the image of `Π` inserted in any
region is a linear combination of dots on the strands to its right times bubble monomials on the
far right. -/
theorem slideOutAny (hSL : SimplyLaced C) (μ : X) :
    ∀ (v u : List (Letter I)) {S T : List (Letter I)} (pre post : List (LayerData I)),
      SChain S pre (u ++ v) → SChain (u ++ v) post T →
      ∀ β : End ((pres RD k).obj (ob RD (wt RD μ v) [])), IsBub RD k (wt RD μ v) β →
        ctxL RD k μ S T pre u v post [] [] β ∈ dotBubSpan RD k μ S T pre post u v := by
  intro v
  induction v with
  | nil =>
    intro u S T pre post hpre hpost β hβ
    have hpp : SChain S (pre ++ post) T := by simpa using hpre.append hpost
    have key := hom_ext_dg RD k (wt RD μ []) (s := []) (t := [])
      (ctxL RD k μ S T pre u [] post [] [])
      (Linear.leftComp k _ (dg RD k μ S T (pre ++ post)) ∘ₗ bubAt RD k μ T) (fun B hB => ?_)
    · rw [LinearMap.congr_fun key β]
      exact Submodule.subset_span ⟨[], β, fun x hx => by simp at hx, rfl, hβ,
        by simp only [List.map_nil, List.append_nil]; rfl⟩
    rw [ctxL_dg RD k μ (by simpa using hpre) (by simpa using hpost)]
    change _ = dg RD k μ S T (pre ++ post) ≫ bubAt RD k μ T (dg RD k μ [] [] B)
    have hBT : SChain T (B.map (whL T [])) T := by simpa using hB.whisk T []
    rw [bubAt_dg, dg_comp hpp hBT]
    have e := dg_closed_left (RD := RD) (k := k) μ (S := S) (T := T) pre [] (s := u) (s' := T) []
      hB (by simpa using hpost)
    wnf at e
    wnf
    exact e.symm
  | cons l v' ih =>
    intro u S T pre post hpre hpost β hβ
    rw [ctxL_cons RD k μ hpre hpost]
    have hmem := bubLU_mem_slideSetR hSL (wt RD μ v') l (β := β) hβ
    generalize bubLU RD k (wt RD μ v') l β = f at hmem ⊢
    induction hmem using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, γ, hγ, rfl⟩ := hf
      rw [ctxL_dots_bubRU RD k μ hpre hpost]
      have hrep' : SChain (u ++ l :: v') (List.replicate a (u, .dot l, v')) (u ++ l :: v') :=
        SChain.replicate_of ⟨by simp, by simp⟩ a
      exact dotBubSpan_mono μ S T pre post u v' l a
        (ih (u ++ [l]) _ post (by simpa using hpre.append hrep') (by simpa using hpost) γ hγ)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- A composite `A ≫ γ ≫ B` (`γ` an endomorphism of `1`) placed between `u` and `v` is `γ` placed
between `u` and `v`, in the context `A`, `B`. -/
theorem ctxL_sandwich (μ : X) (u v s t : List (Letter I)) {s₀ t₀ : List (Letter I)}
    (hs₀ : s₀ = u ++ s ++ v) (ht₀ : t₀ = u ++ t ++ v) {P Q : List (LayerData I)}
    (hP : SChain s P []) (hQ : SChain [] Q t)
    (γ : End ((pres RD k).obj (ob RD (wt RD μ v) []))) :
    ctxL RD k μ s₀ t₀ [] u v [] s t
        (dg RD k (wt RD μ v) s [] P ≫ γ ≫ dg RD k (wt RD μ v) [] t Q) =
      ctxL RD k μ s₀ t₀ (P.map (whL u v)) u v (Q.map (whL u v)) [] [] γ := by
  subst hs₀ ht₀
  have key := hom_ext_dg RD k (wt RD μ v) (s := []) (t := [])
    ((ctxL RD k μ (u ++ s ++ v) (u ++ t ++ v) [] u v [] s t).comp
      (Linear.rightComp k _ (dg RD k (wt RD μ v) [] t Q) ∘ₗ
        Linear.leftComp k _ (dg RD k (wt RD μ v) s [] P)))
    (ctxL RD k μ (u ++ s ++ v) (u ++ t ++ v) (P.map (whL u v)) u v (Q.map (whL u v)) [] [])
    (fun B hB => ?_)
  · have e := LinearMap.congr_fun key γ
    simpa [Category.assoc] using e
  simp only [LinearMap.comp_apply, Linear.leftComp_apply, Linear.rightComp_apply]
  rw [dg_comp hP hB, dg_comp (hP.append hB) hQ,
    ctxL_dg RD k μ (SChain.nil' _) (SChain.nil' _),
    ctxL_dg RD k μ (by simpa using hP.whisk u v) (by simpa using hQ.whisk u v)]
  exact dg_list_eq (by simp [List.append_assoc])

/-! ## Decompositions of identities -/

variable (RD k) in
/-- Composites `E_w → E_{a} F_{b} → E_w` of a monotone diagram of type `LR` and one of type `RL`,
through a word sorted to the right, times a bubble monomial. -/
def decRSet (μ : X) (w : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ w)) :=
  Submodule.span k {f | ∃ (a b : List I) (P Q : List (LayerData I))
    (δ : End ((pres RD k).obj (ob RD μ []))), AllSh Shape.isLR P ∧ SChain w P (ups a ++ dns b) ∧
      AllSh Shape.isRL Q ∧ SChain (ups a ++ dns b) Q w ∧ IsBub RD k μ δ ∧
        f = bubAt RD k μ w δ ≫ dg RD k μ w (ups a ++ dns b) P ≫ dg RD k μ (ups a ++ dns b) w Q}

variable (RD k) in
/-- Composites `E_w → F_{d} E_{c} → E_w` of a monotone diagram of type `RL` and one of type `LR`,
through a word sorted to the left, times a bubble monomial. -/
def decLSet (μ : X) (w : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ w)) :=
  Submodule.span k {f | ∃ (d c : List I) (P Q : List (LayerData I))
    (δ : End ((pres RD k).obj (ob RD μ []))), AllSh Shape.isRL P ∧ SChain w P (dns d ++ ups c) ∧
      AllSh Shape.isLR Q ∧ SChain (dns d ++ ups c) Q w ∧ IsBub RD k μ δ ∧
        f = bubAt RD k μ w δ ≫ dg RD k μ w (dns d ++ ups c) P ≫ dg RD k μ (dns d ++ ups c) w Q}

theorem decRSet_conj (μ : X) {w w' : List (Letter I)} {L₁ L₂ : List (LayerData I)}
    (h₁ : AllSh Shape.isLR L₁) (hc₁ : SChain w L₁ w') (h₂ : AllSh Shape.isRL L₂)
    (hc₂ : SChain w' L₂ w) {δ : End ((pres RD k).obj (ob RD μ []))} (hδ : IsBub RD k μ δ)
    {x} (hx : x ∈ decRSet RD k μ w') :
    bubAt RD k μ w δ ≫ dg RD k μ w w' L₁ ≫ x ≫ dg RD k μ w' w L₂ ∈ decRSet RD k μ w := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, b, P, Q, δ', hP, hcP, hQ, hcQ, hδ', rfl⟩ := hf
    refine Submodule.subset_span ⟨a, b, L₁ ++ P, Q ++ L₂, δ ≫ δ', h₁.append hP, hc₁.append hcP,
      hQ.append h₂, hcQ.append hc₂, hδ.comp hδ', ?_⟩
    have e : dg RD k μ w w' L₁ ≫ bubAt RD k μ w' δ' = bubAt RD k μ w δ' ≫ dg RD k μ w w' L₁ :=
      (bubAt_comm RD k μ δ' _).symm
    calc bubAt RD k μ w δ ≫ dg RD k μ w w' L₁ ≫ (bubAt RD k μ w' δ' ≫
          dg RD k μ w' (ups a ++ dns b) P ≫
          dg RD k μ (ups a ++ dns b) w' Q) ≫ dg RD k μ w' w L₂
        = bubAt RD k μ w δ ≫ (dg RD k μ w w' L₁ ≫ bubAt RD k μ w' δ') ≫
          dg RD k μ w' (ups a ++ dns b) P ≫
          dg RD k μ (ups a ++ dns b) w' Q ≫ dg RD k μ w' w L₂ := by simp only [Category.assoc]
      _ = bubAt RD k μ w δ ≫ (bubAt RD k μ w δ' ≫ dg RD k μ w w' L₁) ≫
          dg RD k μ w' (ups a ++ dns b) P ≫
          dg RD k μ (ups a ++ dns b) w' Q ≫ dg RD k μ w' w L₂ := by rw [e]
      _ = _ := by rw [bubAt_comp, ← dg_comp hc₁ hcP, ← dg_comp hcQ hc₂]; simp only [Category.assoc]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => simp only [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ r hx

theorem decLSet_conj (μ : X) {w w' : List (Letter I)} {L₁ L₂ : List (LayerData I)}
    (h₁ : AllSh Shape.isRL L₁) (hc₁ : SChain w L₁ w') (h₂ : AllSh Shape.isLR L₂)
    (hc₂ : SChain w' L₂ w) {δ : End ((pres RD k).obj (ob RD μ []))} (hδ : IsBub RD k μ δ)
    {x} (hx : x ∈ decLSet RD k μ w') :
    bubAt RD k μ w δ ≫ dg RD k μ w w' L₁ ≫ x ≫ dg RD k μ w' w L₂ ∈ decLSet RD k μ w := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d, c, P, Q, δ', hP, hcP, hQ, hcQ, hδ', rfl⟩ := hf
    refine Submodule.subset_span ⟨d, c, L₁ ++ P, Q ++ L₂, δ ≫ δ', h₁.append hP, hc₁.append hcP,
      hQ.append h₂, hcQ.append hc₂, hδ.comp hδ', ?_⟩
    have e : dg RD k μ w w' L₁ ≫ bubAt RD k μ w' δ' = bubAt RD k μ w δ' ≫ dg RD k μ w w' L₁ :=
      (bubAt_comm RD k μ δ' _).symm
    calc bubAt RD k μ w δ ≫ dg RD k μ w w' L₁ ≫ (bubAt RD k μ w' δ' ≫
          dg RD k μ w' (dns d ++ ups c) P ≫
          dg RD k μ (dns d ++ ups c) w' Q) ≫ dg RD k μ w' w L₂
        = bubAt RD k μ w δ ≫ (dg RD k μ w w' L₁ ≫ bubAt RD k μ w' δ') ≫
          dg RD k μ w' (dns d ++ ups c) P ≫
          dg RD k μ (dns d ++ ups c) w' Q ≫ dg RD k μ w' w L₂ := by simp only [Category.assoc]
      _ = bubAt RD k μ w δ ≫ (bubAt RD k μ w δ' ≫ dg RD k μ w w' L₁) ≫
          dg RD k μ w' (dns d ++ ups c) P ≫
          dg RD k μ (dns d ++ ups c) w' Q ≫ dg RD k μ w' w L₂ := by rw [e]
      _ = _ := by rw [bubAt_comp, ← dg_comp hc₁ hcP, ← dg_comp hcQ hc₂]; simp only [Category.assoc]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => simp only [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ r hx

theorem dotBubSpan_le_decRSet (μ : X) {w u v : List (Letter I)} {pre post : List (LayerData I)}
    (hpre : SChain w pre (u ++ v)) (hpost : SChain (u ++ v) post w) (h₁ : AllSh Shape.isLR pre)
    (h₂ : AllSh Shape.isRL post) (IH : 𝟙 _ ∈ decRSet RD k μ (u ++ v)) :
    dotBubSpan RD k μ w w pre post u v ≤ decRSet RD k μ w := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨D, δ, hD, hcD, hδ, rfl⟩
  have hD' : SChain (u ++ v) (D.map (whL u [])) (u ++ v) := by simpa using hcD.whisk u []
  have hm := decRSet_conj μ (L₁ := pre ++ D.map (whL u [])) (L₂ := post)
    (h₁.append (AllSh.map_whL (p := Shape.isLR) (fun x hx => Shape.isLR_of_isDot (hD x hx)) u []))
    (hpre.append hD') h₂ hpost hδ IH
  rw [Category.id_comp, dg_comp (hpre.append hD') hpost, bubAt_comm] at hm
  exact hm

theorem dotBubSpan_le_decLSet (μ : X) {w u v : List (Letter I)} {pre post : List (LayerData I)}
    (hpre : SChain w pre (u ++ v)) (hpost : SChain (u ++ v) post w) (h₁ : AllSh Shape.isRL pre)
    (h₂ : AllSh Shape.isLR post) (IH : 𝟙 _ ∈ decLSet RD k μ (u ++ v)) :
    dotBubSpan RD k μ w w pre post u v ≤ decLSet RD k μ w := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨D, δ, hD, hcD, hδ, rfl⟩
  have hD' : SChain (u ++ v) (D.map (whL u [])) (u ++ v) := by simpa using hcD.whisk u []
  have hm := decLSet_conj μ (L₁ := pre ++ D.map (whL u [])) (L₂ := post)
    (h₁.append (AllSh.map_whL (p := Shape.isRL) (fun x hx => Shape.isRL_of_isDot (hD x hx)) u []))
    (hpre.append hD') h₂ hpost hδ IH
  rw [Category.id_comp, dg_comp (hpre.append hD') hpost, bubAt_comm] at hm
  exact hm

theorem allSh_crossrL_LR (i j : I) : AllSh Shape.isLR (crossrL i j) := by
  simp [AllSh, crossrL, Shape.isLR]

theorem allSh_crosslL_RL (i j : I) : AllSh Shape.isRL (crosslL i j) := by
  simp [AllSh, crosslL, Shape.isRL]

theorem allSh_crossrL_RL (i j : I) : AllSh Shape.isLR (crossrL i j) := allSh_crossrL_LR i j

/-- **Decomposition of identities through words sorted to the right** (simply-laced): the identity
of `E_w 1_μ` is a linear combination of composites `E_w → E_a F_b → E_w` of a monotone diagram of
type `LR` and one of type `RL`, times a bubble monomial. -/
theorem decR (hSL : SimplyLaced C) (μ : X) :
    ∀ (n : ℕ) (w : List (Letter I)), invR w < n → 𝟙 _ ∈ decRSet RD k μ w
  | 0 => fun w h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun w hw => by
    by_cases h0 : invR w = 0
    · obtain ⟨a, b, rfl⟩ := invR_eq_zero w h0
      refine Submodule.subset_span ⟨a, b, [], [], 𝟙 _, fun x hx => by simp at hx, rfl,
        fun x hx => by simp at hx, rfl, IsBub.id, ?_⟩
      rw [bubAt_id, dg_nil, Category.id_comp, Category.id_comp]
    obtain ⟨u, v, j, i, rfl⟩ := invR_pos w h0
    have hcr : SChain (u ++ dn j :: up i :: v) ((crossrL i j).map (whL u v))
        (u ++ up i :: dn j :: v) := by
      simpa using (show SChain [dn j, up i] (crossrL i j) [up i, dn j] by schain).whisk u v
    have hcl : SChain (u ++ up i :: dn j :: v) ((crosslL i j).map (whL u v))
        (u ++ dn j :: up i :: v) := by
      simpa using (show SChain [up i, dn j] (crosslL i j) [dn j, up i] by schain).whisk u v
    have IH1 : 𝟙 _ ∈ decRSet RD k μ (u ++ up i :: dn j :: v) :=
      decR hSL μ n _ (by have := invR_swap i j v u; omega)
    have T1 : dg RD k μ (u ++ dn j :: up i :: v) (u ++ up i :: dn j :: v)
        ((crossrL i j).map (whL u v)) ≫
        dg RD k μ (u ++ up i :: dn j :: v) (u ++ dn j :: up i :: v) ((crosslL i j).map (whL u v)) ∈
          decRSet RD k μ (u ++ dn j :: up i :: v) := by
      have := decRSet_conj μ ((allSh_crossrL_LR i j).map_whL u v) hcr
        ((allSh_crosslL_RL i j).map_whL u v) hcl IsBub.id IH1
      rwa [bubAt_id, Category.id_comp, Category.id_comp] at this
    by_cases hij : i = j
    · subst hij
      have IH2 : 𝟙 _ ∈ decRSet RD k μ (u ++ v) :=
        decR hSL μ n _ (by have := invR_del i i v u; omega)
      have E := dg_stepL RD k μ (s₀ := u ++ dn i :: up i :: v) (t₀ := u ++ dn i :: up i :: v)
        [] [] u v (A := []) (L := []) (rfl : dg RD k (wt RD μ v) [dn i, up i] [dn i, up i] [] = _)
        (by simp) (by simp) (by simp)
      rw [dg_decompFE, map_add, map_neg, map_sum, ctxL_dg RD k μ (by simp) (by simp)] at E
      rw [← dg_nil (RD := RD) (k := k) μ, E]
      refine Submodule.add_mem _ (Submodule.neg_mem _ ?_)
        (Submodule.sum_mem _ fun f _ => ?_)
      · rw [List.map_append, List.nil_append, List.append_nil, ← dg_comp hcr hcl]
        exact T1
      rw [map_sum]
      refine Submodule.sum_mem _ fun g _ => ?_
      rw [ctxL_sandwich μ u v [dn i, up i] [dn i, up i] (by simp) (by simp) (by schain)
        (by schain)]
      have hpre : SChain (u ++ dn i :: up i :: v) ((dotCapFELs i (f - g)).map (whL u v))
          (u ++ v) := by
        simpa using (show SChain [dn i, up i] (dotCapFELs i (f - g)) [] by schain).whisk u v
      have hpost : SChain (u ++ v) ((cupDotFELs i ((-ip RD i (wt RD μ v)).toNat - 1 - f)).map
          (whL u v)) (u ++ dn i :: up i :: v) := by
        simpa using (show SChain [] (cupDotFELs i ((-ip RD i (wt RD μ v)).toNat - 1 - f))
          [dn i, up i] by schain).whisk u v
      refine dotBubSpan_le_decRSet μ hpre hpost ?_ ?_ IH2
        (slideOutAny hSL μ v u _ _ hpre hpost _ (cwU_isBub i _))
      · refine AllSh.map_whL (fun x hx => ?_) u v
        simp only [dotCapFELs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · rw [List.eq_of_mem_replicate hx]; rfl
        · rfl
      · refine AllSh.map_whL (fun x hx => ?_) u v
        simp only [cupDotFELs, List.mem_append, List.mem_singleton] at hx
        rcases hx with rfl | hx
        · rfl
        · rw [List.eq_of_mem_replicate hx]; rfl
    · have E := dg_step RD k μ (s₀ := u ++ dn j :: up i :: v) (t₀ := u ++ dn j :: up i :: v)
        [] [] u v (dg_downupFE RD k j i (Ne.symm hij) (wt RD μ v)).symm (by simp) (by simp)
        (L := []) (by simp) rfl
      rw [← dg_nil (RD := RD) (k := k) μ, E, List.nil_append, List.append_nil, List.map_append,
        ← dg_comp hcr hcl]
      exact T1

/-- **Decomposition of identities through words sorted to the left** (simply-laced): the identity
of `E_w 1_μ` is a linear combination of composites `E_w → F_d E_c → E_w` of a monotone diagram of
type `RL` and one of type `LR`, times a bubble monomial. -/
theorem decL (hSL : SimplyLaced C) (μ : X) :
    ∀ (n : ℕ) (w : List (Letter I)), invL w < n → 𝟙 _ ∈ decLSet RD k μ w
  | 0 => fun w h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun w hw => by
    by_cases h0 : invL w = 0
    · obtain ⟨d, c, rfl⟩ := invL_eq_zero w h0
      refine Submodule.subset_span ⟨d, c, [], [], 𝟙 _, fun x hx => by simp at hx, rfl,
        fun x hx => by simp at hx, rfl, IsBub.id, ?_⟩
      rw [bubAt_id, dg_nil, Category.id_comp, Category.id_comp]
    obtain ⟨u, v, i, j, rfl⟩ := invL_pos w h0
    have hcl : SChain (u ++ up i :: dn j :: v) ((crosslL i j).map (whL u v))
        (u ++ dn j :: up i :: v) := by
      simpa using (show SChain [up i, dn j] (crosslL i j) [dn j, up i] by schain).whisk u v
    have hcr : SChain (u ++ dn j :: up i :: v) ((crossrL i j).map (whL u v))
        (u ++ up i :: dn j :: v) := by
      simpa using (show SChain [dn j, up i] (crossrL i j) [up i, dn j] by schain).whisk u v
    have IH1 : 𝟙 _ ∈ decLSet RD k μ (u ++ dn j :: up i :: v) :=
      decL hSL μ n _ (by have := invL_swap i j v u; omega)
    have T1 : dg RD k μ (u ++ up i :: dn j :: v) (u ++ dn j :: up i :: v)
        ((crosslL i j).map (whL u v)) ≫
        dg RD k μ (u ++ dn j :: up i :: v) (u ++ up i :: dn j :: v) ((crossrL i j).map (whL u v)) ∈
          decLSet RD k μ (u ++ up i :: dn j :: v) := by
      have := decLSet_conj μ ((allSh_crosslL_RL i j).map_whL u v) hcl
        ((allSh_crossrL_LR i j).map_whL u v) hcr IsBub.id IH1
      rwa [bubAt_id, Category.id_comp, Category.id_comp] at this
    by_cases hij : i = j
    · subst hij
      have IH2 : 𝟙 _ ∈ decLSet RD k μ (u ++ v) :=
        decL hSL μ n _ (by have := invL_del i i v u; omega)
      have E := dg_stepL RD k μ (s₀ := u ++ up i :: dn i :: v) (t₀ := u ++ up i :: dn i :: v)
        [] [] u v (A := []) (L := []) (rfl : dg RD k (wt RD μ v) [up i, dn i] [up i, dn i] [] = _)
        (by simp) (by simp) (by simp)
      rw [dg_decompEF, map_add, map_neg, map_sum, ctxL_dg RD k μ (by simp) (by simp)] at E
      rw [← dg_nil (RD := RD) (k := k) μ, E]
      refine Submodule.add_mem _ (Submodule.neg_mem _ ?_)
        (Submodule.sum_mem _ fun f _ => ?_)
      · rw [List.map_append, List.nil_append, List.append_nil, ← dg_comp hcl hcr]
        exact T1
      rw [map_sum]
      refine Submodule.sum_mem _ fun g _ => ?_
      rw [ctxL_sandwich μ u v [up i, dn i] [up i, dn i] (by simp) (by simp) (by schain)
        (by schain)]
      have hpre : SChain (u ++ up i :: dn i :: v) ((dotCapEFLs i (f - g)).map (whL u v))
          (u ++ v) := by
        simpa using (show SChain [up i, dn i] (dotCapEFLs i (f - g)) [] by schain).whisk u v
      have hpost : SChain (u ++ v) ((cupDotEFLs i ((ip RD i (wt RD μ v)).toNat - 1 - f)).map
          (whL u v)) (u ++ up i :: dn i :: v) := by
        simpa using (show SChain [] (cupDotEFLs i ((ip RD i (wt RD μ v)).toNat - 1 - f))
          [up i, dn i] by schain).whisk u v
      refine dotBubSpan_le_decLSet μ hpre hpost ?_ ?_ IH2
        (slideOutAny hSL μ v u _ _ hpre hpost _ (ccwU_isBub i _))
      · refine AllSh.map_whL (fun x hx => ?_) u v
        simp only [dotCapEFLs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · rw [List.eq_of_mem_replicate hx]; rfl
        · rfl
      · refine AllSh.map_whL (fun x hx => ?_) u v
        simp only [cupDotEFLs, List.mem_append, List.mem_singleton] at hx
        rcases hx with rfl | hx
        · rfl
        · rw [List.eq_of_mem_replicate hx]; rfl
    · have E := dg_step RD k μ (s₀ := u ++ up i :: dn j :: v) (t₀ := u ++ up i :: dn j :: v)
        [] [] u v (dg_downupEF RD k i j hij (wt RD μ v)).symm (by simp) (by simp)
        (L := []) (by simp) rfl
      rw [← dg_nil (RD := RD) (k := k) μ, E, List.nil_append, List.append_nil, List.map_append,
        ← dg_comp hcl hcr]
      exact T1

end Categorification.KL3.Diagram
