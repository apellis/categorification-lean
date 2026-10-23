/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.IntegralNondegeneracy
import Categorification.Diagrams.KL3.SpanningOneSided

/-!
# Integral KL spanning

The integral specialization of the reduction proof of KL III Proposition 3.11.
The existing reduction lemmas work over commutative rings; the final existing
spanning interfaces are field-valued. This file supplies the needed integral
specialization without changing those interfaces or using rational independence.
-/
noncomputable section
namespace Categorification.KL3.Diagram.IntegralSpanning
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Module
open StringDiagrams.Chord (Same Valid Lettered canon ofMatching lettersOf matchingOf)
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} [DecidableEq I]
variable {k : Type w} [CommRing k]

theorem mem_canonSpanRing (μ : X) (v : List (Letter I))
    (f : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v)) :
    f ∈ CanonSpan RD k μ v := by
  have key : ∀ c (L : List (LayerData I)), ccnt L ≤ c → dg RD k μ [] v L ∈ CanonSpan RD k μ v := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
    intro L hL
    have hlo : ∀ n ≤ c, Lo RD k μ [] v n ≤ CanonSpan RD k μ v := by
      intro n hn
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨L', hL', rfl⟩
      exact ihc (ccnt L') (by omega) L' le_rfl
    have hcap := capElim (RD := RD) (k := k) (μ := μ) (w₀ := []) c v L hL
    rw [CapTarget, thruShort_nil, sup_bot_eq, MvSp] at hcap
    generalize dg RD k μ [] v L = x at hcap
    induction hcap using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hx
      have h := mvSp_gen_mem (RD := RD) (k := k) μ hch hβ
      exact (sup_le le_rfl (hlo _ hcc)) h
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hf := mem_span_dg (RD := RD) (k := k) μ f
  refine (Submodule.span_le.mpr ?_) hf
  rintro _ ⟨L, -, rfl⟩
  exact key _ L le_rfl


variable (RD k) in
def oneB (μ : X) (v : List (Letter I)) (x : SpanIdx [] v) :
    (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v) :=
  dg RD k μ [] v (chL [] (canon (pState x.1.1)) ++ dotsL v (arcDots x.2.1)) ≫
    bubAt RD k μ v (bubMon RD k μ x.2.2)

omit [DecidableEq I] in
theorem exists_oneB (μ : X) {v : List (Letter I)} {s : List (ℕ × Letter I)} {is : List ℕ}
    (hv : Valid s) (hl : Lettered Letter.dual s) (hsv : s.map Prod.snd = v)
    (his : ∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) (m : (I × ℕ) →₀ ℕ) :
    ∃ x : SpanIdx [] v, oneB RD k μ v x =
      dg RD k μ [] v (chL [] (canon s) ++ dotsL v is) ≫ bubAt RD k μ v (bubMon RD k μ m) := by
  have hn : s.length = (ρW [] ++ v).length := by
    show s.length = v.length
    rw [← hsv, List.length_map]
  set σ := matchingOf hv hn with hσdef
  have hL : lettersOf s hn = bwL v := by
    funext p
    have hp : p.val < (s.map Prod.snd).length := by rw [List.length_map, hn]; exact p.2
    show (s[p.val]'(by rw [hn]; exact p.2)).2 = v[p.val]'p.2
    have := List.getElem_of_eq hsv hp
    simp only [List.getElem_map] at this
    exact this
  have hσ : σ ∈ pairings [] v := by
    have := isMatching_lettersOf hv hl hn
    rw [hL] at this
    exact mem_matchings.2 this
  have hcanon : canon (pState σ) = canon s := by
    rw [← Chord.canon_ofMatching_matchingOf hv hn, hL]
  -- the strands of the dots
  have hleft : ∀ i ∈ is, ∃ a : Arc [] v σ, a.1.val = i := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := his i hi
    refine ⟨⟨⟨i, by rw [← hn]; exact hi1⟩, ?_⟩, rfl⟩
    have hs := (Chord.same_iff_matchingOf hv hn ⟨i, by rw [← hn]; exact hi1⟩
      (σ ⟨i, by rw [← hn]; exact hi1⟩)).2 rfl
    rcases lt_or_gt_of_ne (show i ≠ (σ ⟨i, _⟩ : ℕ) from hs.1) with h | h
    · exact h
    · exact absurd ⟨_, h, hs⟩ hi2
  refine ⟨⟨⟨σ, hσ⟩, fun a => is.count a.1.val, m⟩, ?_⟩
  have hperm : is.Perm (arcDots (v := v) (σ := σ) fun a => is.count a.1.val) := by
    rw [List.perm_iff_count]
    intro n
    rw [count_dotList]
    by_cases hn' : n ∈ is
    · obtain ⟨a₀, ha₀⟩ := hleft n hn'
      rw [Finset.sum_eq_single a₀ (fun b _ hb => ite_eq_right fun h => hb (Subtype.ext (Fin.ext
        (h.trans ha₀.symm)))) (fun h => absurd (Finset.mem_univ _) h), ite_eq_left ha₀, ha₀]
    · rw [List.count_eq_zero_of_not_mem hn']
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      split_ifs with h
      · rw [h]; exact List.count_eq_zero_of_not_mem hn'
      · rfl
  have hb : ∀ i ∈ is, i < v.length := fun i hi => by
    rw [← hsv, List.length_map]; exact (his i hi).1
  simp only [oneB, hcanon]
  congr 1
  have := dotsL_perm (RD := RD) (k := k) (t := v) hperm hb (chL [] (canon s)) [] μ [] v
  simpa using this.symm

omit [DecidableEq I] in
theorem isBub_mem_span {μ : X} {δ : End ((pres RD k).obj (ob RD μ []))} (h : IsBub RD k μ δ) :
    δ ∈ Submodule.span k (Set.range (bubMon RD k μ)) := by
  obtain ⟨p, hp⟩ := h
  have e : δ = (bubMap RD k μ p).val := (congrArg EndOne.val hp).symm
  rw [e, p.as_sum, map_sum]
  simp only [EndOne.val]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [← mul_one (p.coeff s), ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

/-- The integral one-sided canonical family spans, before invoking independence. -/
theorem span_oneB (μ : X) (v : List (Letter I)) :
    Submodule.span k (Set.range (oneB RD k μ v)) = ⊤ := by
  apply top_unique
  intro f _
  have hspan : CanonSpan RD k μ v ≤ Submodule.span k (Set.range (oneB RD k μ v)) := by
    rw [CanonSpan, Submodule.span_le]
    rintro _ ⟨s, is, β, hv, hl, hsv, his, hβ, rfl⟩
    let Φ := (Linear.leftComp k _ (dg RD k μ [] v (chL [] (canon s) ++ dotsL v is))).comp
      (bubAt RD k μ v)
    have hmem : Φ β ∈ (Submodule.span k (Set.range (bubMon RD k μ))).map Φ :=
      Submodule.mem_map_of_mem (isBub_mem_span hβ)
    rw [Submodule.map_span, ← Set.range_comp] at hmem
    refine Submodule.span_le.2 ?_ hmem
    rintro _ ⟨m, rfl⟩
    obtain ⟨x, hx⟩ := exists_oneB (RD := RD) (k := k) μ hv hl hsv his m
    exact Submodule.subset_span ⟨x, hx⟩
  exact hspan (mem_canonSpanRing μ v f)

variable (RD k) in
/-- The nested-cap bending map, with no field hypothesis. -/
def bendG (μ : X) (s t : List (Letter I)) :
    ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (rd s ++ t))) →ₗ[k]
      ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :=
  ctxL RD k μ s t [] s [] ((capA (rd s)).map (whL [] t)) [] (rd s ++ t)

omit [DecidableEq I] in
/-- Bending has the cup-bending right inverse over every commutative ring. -/
theorem bendG_surjective (μ : X) (s t : List (Letter I)) :
    Function.Surjective (bendG RD k μ s t) := by
  have hpre : SChain [] (cupA (rd s)) (rd s ++ s ++ []) := by simpa using sChain_cupA (rd s)
  have hpostF : SChain (rd s ++ t ++ []) [] (rd s ++ t) := by simp
  have hpreG : SChain s [] (s ++ [] ++ []) := by simp
  have hpostG : SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := by
    simpa using (sChain_capA (rd s)).whisk [] t
  let F := ctxL RD k μ [] (rd s ++ t) (cupA (rd s)) (rd s) [] [] s t
  have key : (bendG RD k μ s t).comp F = LinearMap.id := by
    refine hom_ext_dg RD k μ _ _ (fun A hA => ?_)
    change bendG RD k μ s t (F (dg RD k μ s t A)) = dg RD k μ s t A
    dsimp only [F, bendG]
    erw [ctxL_dg_nil RD k μ hpre hpostF, ctxL_dg_nil RD k μ hpreG hpostG]
    have e := dg_unbend_flat (RD := RD) (k := k) (rd s) [] [] t (M := A) (by simpa using hA) μ
    rw [rd_rd, rd_nil] at e
    repeat rw [List.append_nil] at e
    refine Eq.trans (dg_list_eq ?_) e
    simp [flatL]
  exact fun f => ⟨F f, LinearMap.congr_fun key f⟩

variable (RD k) in
/-- The canonical KL diagram family over a commutative ring. -/
def twoB (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t) :=
  bendG RD k μ s t (oneB RD k μ (rd s ++ t) (oneIdx x))

/-- KL III Proposition 3.11 over a commutative ring, including the integers. -/
theorem span_twoB (μ : X) (s t : List (Letter I)) :
    Submodule.span k (Set.range (twoB RD k μ s t)) = ⊤ := by
  change Submodule.span k (Set.range ((bendG RD k μ s t) ∘ (oneB RD k μ (rd s ++ t)))) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, span_oneB, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (bendG_surjective μ s t)

omit [DecidableEq I] in
/-- **The elements of `B_{∅,v,λ}` are homogeneous of the degrees `spanDeg`**, over every
commutative ring. -/
theorem oneB_mem (μ : X) (v : List (Letter I)) (x : SpanIdx [] v) :
    oneB RD k μ v x ∈ HomD RD k μ [] v (spanDeg C (RD.ellOf μ) x) := by
  have h1 : dg RD k μ [] v (chL [] (canon (pState x.1.1)) ++ dotsL v (arcDots x.2.1)) ∈
      HomD RD k μ [] v (pdeg C (RD.ellOf μ) [] v x.1.1 +
        ∑ a, (x.2.1 a : ℤ) * C.dot (arcCol a) (arcCol a)) := by
    refine dg_mem_homD ?_
    rw [sdegSum_append, sdegSum_canon_pState μ x.1.2, sdegSum_dotsL, sum_dotList]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [dotDeg, show (a.1 : ℕ) < v.length from a.1.2, ↓reduceDIte]
    rfl
  have h2 := bubAt_mem (RD := RD) (k := k) μ v (bubMon_mem (RD := RD) (k := k) μ x.2.2)
  exact comp_mem_homDeg h1 h2

omit [DecidableEq I] in
/-- **The elements of `B_{s,t,λ}` are homogeneous of the degrees `spanDeg`**, over every
commutative ring (KL III §3.2.3). -/
theorem twoB_mem (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    twoB RD k μ s t x ∈ HomD RD k μ s t (spanDeg C (RD.ellOf μ) x) := by
  have hpre : SChain [] (cupA (rd s)) (rd s ++ s ++ []) := by simpa using sChain_cupA (rd s)
  have hpostF : SChain (rd s ++ t ++ []) [] (rd s ++ t) := by simp
  have hpreG : SChain s [] (s ++ [] ++ []) := by simp
  have hpostG : SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := by
    simpa using (sChain_capA (rd s)).whisk [] t
  let F := ctxL RD k μ [] (rd s ++ t) (cupA (rd s)) (rd s) [] [] s t
  let G := bendG RD k μ s t
  set y := oneB RD k μ (rd s ++ t) (oneIdx x) with hy_def
  have hy := oneB_mem (RD := RD) (k := k) μ (rd s ++ t) (oneIdx x)
  rw [← hy_def] at hy
  change G y ∈ _
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]; exact Submodule.zero_mem _
  have keyFG : F.comp G = LinearMap.id := by
    refine hom_ext_dg RD k μ _ _ (fun M hM => ?_)
    change F (G (dg RD k μ [] (rd s ++ t) M)) = dg RD k μ [] (rd s ++ t) M
    dsimp only [F, G, bendG]
    erw [ctxL_dg_nil RD k μ hpreG hpostG, ctxL_dg_nil RD k μ hpre hpostF]
    have e := dg_unbend_sharp (RD := RD) (k := k) (rd s) [] [] t (M := M) (by simpa using hM) μ
    refine Eq.trans (dg_list_eq ?_) e
    simp [sharpL, rd_rd, List.map_map, Function.comp_def, whL_def]
  have hG : G y ∈ HomD RD k μ s t
      (spanDeg C (RD.ellOf μ) (oneIdx x) + (sdegSum RD μ [] + sdegSum RD μ ((capA (rd s)).map (whL [] t)))) :=
    map_ctxL_le μ hpreG hpostG _ ⟨y, hy, rfl⟩
  have hFG : F (G y) ∈ HomD RD k μ [] (rd s ++ t)
      (spanDeg C (RD.ellOf μ) (oneIdx x) + (sdegSum RD μ [] + sdegSum RD μ ((capA (rd s)).map (whL [] t))) +
        (sdegSum RD μ (cupA (rd s)) + sdegSum RD μ [])) :=
    map_ctxL_le μ hpre hpostF _ ⟨G y, hG, rfl⟩
  rw [show F (G y) = y from LinearMap.congr_fun keyFG y] at hFG
  have hcc : sdegSum RD μ ((capA (rd s)).map (whL [] t)) + sdegSum RD μ (cupA (rd s)) = 0 := by
    by_contra hne
    have hdisj := (isInternal_homDeg (RD := RD) (k := k) (ob RD μ []) (ob RD μ (rd s ++ t))
      ).submodule_iSupIndep.pairwiseDisjoint
    have : sdegSum RD μ ([] : List (LayerData I)) = 0 := rfl
    exact hy0 (Submodule.disjoint_def.1 (hdisj (show spanDeg C (RD.ellOf μ) (oneIdx x) ≠ _ by omega)) y hy hFG)
  have hw : wt RD μ s = wt RD μ t := by
    refine wt_eq_of_rd_append ?_
    by_contra hne
    rw [homD_eq_bot_of_wt_ne hne] at hy
    exact hy0 ((Submodule.mem_bot k).1 hy)
  convert hG using 1
  rw [spanDeg_bend, wl_ellOf_eq', ← hw, ← neg_neg (rcx C _ s), ← sdegSum_cupA_rd]
  have : sdegSum RD μ ([] : List (LayerData I)) = 0 := rfl
  congr 1
  omega

end Categorification.KL3.Diagram.IntegralSpanning
