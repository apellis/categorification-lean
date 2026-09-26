/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningPositive

/-!
# Transporting spanning sets `B_{𝐢,𝐣,λ}` along bending

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3
(Proposition 3.11) and §2.2 (the lemma after Lemma 2.8: attaching U-turns gives a bijection
`p(±i 𝐢, 𝐣) ≅ p(𝐢, ∓i 𝐣)` changing the degree by the exponent of `ρ̄`).

For signed sequences `s` (lower) and `t` (upper), the `(s, t)`-pairings and the pairings of the
one-sided boundary word `s* t = rd s ++ t` are the same (`SpanIdx s t` and
`SpanIdx [] (rd s ++ t)` are definitionally the same type), with degrees differing by the degree
of the bending caps (`spanDeg_bend`). On the diagrammatic side, bending the lower endpoints up on
the left (nested cups, `bendF`) and back (nested caps, `bendG`) are mutually inverse graded maps
(biadjointness, `Categorification.Diagrams.KL3.NondegPositive`). Hence spanning families indexed
by `B` transport both ways:

* `isSpanFamily_bendG`: a graded spanning family of `HOM_U(1_λ, E_{s* t} 1_λ)` indexed by
  `B_{∅, s* t, λ}` gives one of `HOM_U(E_s 1_λ, E_t 1_λ)` indexed by `B_{s,t,λ}` (its elements
  are the bent diagrams);
* `isSpanFamily_bendF`: and conversely.

In particular Proposition 3.11 for all pairs `(s, t)` reduces to the one-sided case `s = ∅`
(`prop311_of_oneSided`), and the explicit family `B_{+i,+j,λ}` of
`Categorification.Diagrams.KL3.SpanningPositive` yields graded spanning families indexed by `B`
for every splitting `(s, t)` of the normally ordered boundary words `(-c)(+b)`, e.g. for
`HOM_U(1_λ, F_{c} E_{b} 1_λ)` (`exists_isSpanFamily_negW_posW`, `exists_isSpanFamily_of_normal`).

The one-sided case for boundary words which are not normally ordered (up to the splitting) is
**not** proved here. It cannot be obtained from the normally ordered case by the direct sum
decompositions of KL III Propositions 3.25 and 3.26 alone: `E_{+i-i} 1_μ` is a direct summand of
`E_{-i+i} 1_μ` when `⟨i, μ⟩ < 0`, and for `sl₂` the cyclic boundary word `(+)³(-)³(+)³(-)³`, with
suitable weights, admits no decomposition in the good direction at any adjacent pair. KL III's
proof uses isotopies of dotted diagrams modulo lower terms (A. Lauda, arXiv:0803.3652v3, §8).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Module KLR.Diagram

universe w u v

/-! ## Abstract transport -/

section Abstract

variable {k : Type w} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] (ℳ : ℤ → Submodule k V) (𝒩 : ℤ → Submodule k W)

/-- `b` is a graded spanning family of `𝒩` with degrees `δ`. -/
def IsGradedSpan {J : Type*} (b : J → W) (δ : J → ℤ) : Prop :=
  (∀ x, b x ∈ 𝒩 (δ x)) ∧ ∀ d, Submodule.span k (Set.range fun x : {x // δ x = d} => b x.1) = 𝒩 d

variable {ℳ 𝒩}

/-- If a graded map and a graded map back compose to the identity on a nonzero homogeneous
element, the degree shifts cancel. -/
theorem shift_add_eq_zero (h𝒩 : DirectSum.IsInternal 𝒩) (F : V →ₗ[k] W) (G : W →ₗ[k] V)
    (c c' : ℤ) (hF : ∀ d, (ℳ d).map F ≤ 𝒩 (d + c)) (hG : ∀ e, (𝒩 e).map G ≤ ℳ (e + c'))
    (hFG : ∀ y, F (G y) = y) {e : ℤ} {y : W} (hy : y ∈ 𝒩 e) (hy0 : y ≠ 0) : c + c' = 0 := by
  by_contra hcc
  have h1 : G y ∈ ℳ (e + c') := hG e ⟨y, hy, rfl⟩
  have h2 : F (G y) ∈ 𝒩 (e + c' + c) := hF _ ⟨G y, h1, rfl⟩
  rw [hFG] at h2
  exact hy0 (Submodule.disjoint_def.1
    (h𝒩.submodule_iSupIndep.pairwiseDisjoint (show e ≠ e + c' + c by omega)) y hy h2)

/-- **Transport of graded spanning families along graded mutually inverse maps.** -/
theorem isGradedSpan_transport (hℳ : DirectSum.IsInternal ℳ)
    (F : V →ₗ[k] W) (G : W →ₗ[k] V) (c c' : ℤ) (hF : ∀ d, (ℳ d).map F ≤ 𝒩 (d + c))
    (hG : ∀ e, (𝒩 e).map G ≤ ℳ (e + c')) (hGF : ∀ x, G (F x) = x)
    {J : Type*} {b : J → W} {δ : J → ℤ} (hb : IsGradedSpan 𝒩 b δ) (δ' : J → ℤ)
    (hδ : ∀ x, b x ≠ 0 → δ' x = δ x + c') : IsGradedSpan ℳ (fun x => G (b x)) δ' := by
  have mem : ∀ x, G (b x) ∈ ℳ (δ' x) := fun x => by
    by_cases h0 : b x = 0
    · rw [h0, map_zero]; exact zero_mem _
    · rw [hδ x h0]; exact hG _ ⟨b x, hb.1 x, rfl⟩
  refine ⟨mem, fun d => le_antisymm ?_ fun f hf => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨x, rfl⟩, rfl⟩
    exact mem x
  · by_cases hf0 : f = 0
    · rw [hf0]; exact zero_mem _
    have hFf : F f ∈ 𝒩 (d + c) := hF d ⟨f, hf, rfl⟩
    have hFf0 : F f ≠ 0 := fun h => hf0 (by rw [← hGF f, h, map_zero])
    have hcc := shift_add_eq_zero (ℳ := 𝒩) (𝒩 := ℳ) hℳ G F c' c hG hF hGF hf hf0
    rw [← hb.2 (d + c)] at hFf
    have : G (F f) ∈ (Submodule.span k (Set.range fun x : {x // δ x = d + c} => b x.1)).map G :=
      ⟨F f, hFf, rfl⟩
    rw [hGF, Submodule.map_span, ← Set.range_comp] at this
    rw [← Submodule.span_insert_zero]
    refine Submodule.span_mono ?_ this
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    by_cases h0 : b x = 0
    · simp only [Function.comp_apply, h0, map_zero]; exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨⟨x, ?_⟩, rfl⟩
      rw [hδ x h0, hx]; omega

end Abstract

/-! ## Bending in `U` -/

section Bend

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

variable (RD k) in
/-- Bending the lower endpoints up on the left (nested cups): `HOM(E_s 1_μ, E_t 1_μ) →
HOM(1_μ, E_{s* t} 1_μ)`. -/
def bendF (μ : X) (s t : List (Letter I)) :
    ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) →ₗ[k]
      ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (rd s ++ t))) :=
  ctxL RD k μ [] (rd s ++ t) (cupA (rd s)) (rd s) [] [] s t

variable (RD k) in
/-- Bending back (nested caps): `HOM(1_μ, E_{s* t} 1_μ) → HOM(E_s 1_μ, E_t 1_μ)`. -/
def bendG (μ : X) (s t : List (Letter I)) :
    ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (rd s ++ t))) →ₗ[k]
      ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :=
  ctxL RD k μ s t [] s [] ((capA (rd s)).map (whL [] t)) [] (rd s ++ t)

theorem bend_facts (μ : X) (s t : List (Letter I)) :
    (∀ d, (HomD RD k μ s t d).map (bendF RD k μ s t) ≤
        HomD RD k μ [] (rd s ++ t) (d + (sdegSum RD μ (cupA (rd s)) + sdegSum RD μ []))) ∧
    (∀ e, (HomD RD k μ [] (rd s ++ t) e).map (bendG RD k μ s t) ≤
        HomD RD k μ s t (e + (sdegSum RD μ [] + sdegSum RD μ ((capA (rd s)).map (whL [] t))))) ∧
    (∀ x, bendG RD k μ s t (bendF RD k μ s t x) = x) ∧
    (∀ y, bendF RD k μ s t (bendG RD k μ s t y) = y) := by
  have hpre : SChain [] (cupA (rd s)) (rd s ++ s ++ []) := by simpa using sChain_cupA (rd s)
  have hpostF : SChain (rd s ++ t ++ []) [] (rd s ++ t) := by simp
  have hpreG : SChain s [] (s ++ [] ++ []) := by simp
  have hpostG : SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := by
    simpa using (sChain_capA (rd s)).whisk [] t
  refine ⟨fun d => map_ctxL_le μ hpre hpostF d, fun e => map_ctxL_le μ hpreG hpostG e,
    fun x => ?_, fun y => ?_⟩
  · have keyGF : (bendG RD k μ s t).comp (bendF RD k μ s t) = LinearMap.id := by
      refine hom_ext_dg RD k μ _ _ (fun A hA => ?_)
      simp only [LinearMap.comp_apply, LinearMap.id_apply, bendF, bendG]
      erw [ctxL_dg_nil RD k μ hpre hpostF, ctxL_dg_nil RD k μ hpreG hpostG]
      have e := dg_unbend_flat (RD := RD) (k := k) (rd s) [] [] t (M := A) (by simpa using hA) μ
      rw [rd_rd, rd_nil] at e
      repeat rw [List.append_nil] at e
      refine Eq.trans (dg_list_eq ?_) e
      simp [flatL]
    exact LinearMap.congr_fun keyGF x
  · have keyFG : (bendF RD k μ s t).comp (bendG RD k μ s t) = LinearMap.id := by
      refine hom_ext_dg RD k μ _ _ (fun M hM => ?_)
      simp only [LinearMap.comp_apply, LinearMap.id_apply, bendF, bendG]
      erw [ctxL_dg_nil RD k μ hpreG hpostG, ctxL_dg_nil RD k μ hpre hpostF]
      have e := dg_unbend_sharp (RD := RD) (k := k) (rd s) [] [] t (M := M) (by simpa using hM) μ
      refine Eq.trans (dg_list_eq ?_) e
      simp [sharpL, rd_rd, List.map_map, Function.comp_def, whL_def]
    exact LinearMap.congr_fun keyFG y

/-- The `(s, t)`-pairings are the pairings of the one-sided word `s* t` (definitionally). -/
def oneIdx {s t : List (Letter I)} (x : SpanIdx s t) : SpanIdx [] (rd s ++ t) := x

/-- The degrees of `B_{s,t,λ}` and `B_{∅, s* t, λ}` differ by the degree of the bending caps. -/
theorem spanDeg_bend (ℓ : I → ℤ) {s t : List (Letter I)} (x : SpanIdx s t) :
    spanDeg C ℓ x = spanDeg C ℓ (oneIdx x) + rcx C (wl C ℓ t) s := by
  have h0 : bendDeg C ℓ (fun p : Fin (ρW [] ++ (rd s ++ t)).length => (ρW [] ++ (rd s ++ t)).get p)
      ([] : List (Letter I)).length = 0 := by simp [bendDeg]
  have hp : pdeg C ℓ s t x.1.1 = pdeg C ℓ [] (rd s ++ t) (oneIdx x).1.1 + rcx C (wl C ℓ t) s := by
    rw [pdeg, pdeg, h0, ← bendDeg_eq_rcx C ℓ s t, add_zero]
    rfl
  calc spanDeg C ℓ x = pdeg C ℓ s t x.1.1 +
        (∑ a : Arc [] (rd s ++ t) (oneIdx x).1.1,
          ((oneIdx x).2.1 a : ℤ) * C.dot (arcCol a) (arcCol a)) +
        Finsupp.weight (wPi C) (oneIdx x).2.2 := rfl
    _ = _ := by rw [hp, spanDeg]; ring

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

omit [DecidableEq I] [Finite I] in
theorem wt_eq_of_homD_ne {μ : X} {s w : List (Letter I)} {d : ℤ} {f}
    (hf : f ∈ HomD RD k μ s w d) (hf0 : f ≠ 0) : wt RD μ s = wt RD μ w := by
  by_contra h
  rw [homD_eq_bot_of_wt_ne h d] at hf
  exact hf0 ((Submodule.mem_bot k).1 hf)

omit [DecidableEq I] [Finite I] in
theorem wt_eq_of_rd_append {μ : X} {s t : List (Letter I)} (h : wt RD μ [] = wt RD μ (rd s ++ t)) :
    wt RD μ s = wt RD μ t := by
  rw [wt_append] at h
  have h2 := wt_rd RD μ s
  have h' : wt RD (wt RD μ s) (rd s) = wt RD (wt RD μ t) (rd s) := h2.trans h
  rw [wt_eq_add_wX, wt_eq_add_wX RD (wt RD μ t)] at h'
  exact add_left_cancel h'

omit [DecidableEq I] [Finite I] in
/-- **One-sided spanning families bend to two-sided ones**: a graded spanning family of
`HOM_U(1_μ, E_{s* t} 1_μ)` indexed by `B_{∅, s* t, μ}` gives, by bending the lower endpoints back
down, a graded spanning family of `HOM_U(E_s 1_μ, E_t 1_μ)` indexed by `B_{s,t,μ}`. -/
theorem isSpanFamily_bendG (μ : X) (s t : List (Letter I))
    {b : SpanIdx [] (rd s ++ t) →
      ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (rd s ++ t)))}
    (hb : IsSpanFamily RD k μ [] (rd s ++ t) b) :
    IsSpanFamily RD k μ s t fun x => bendG RD k μ s t (b (oneIdx x)) := by
  obtain ⟨hF, hG, hGF, hFG⟩ := bend_facts (RD := RD) (k := k) μ s t
  refine isGradedSpan_transport (isInternal_homDeg (RD := RD) (k := k) _ _) _ _ _ _ hF hG hGF
    (J := SpanIdx s t) (b := fun x => b (oneIdx x)) (δ := fun x => spanDeg C (RD.ellOf μ) (oneIdx x))
    hb (spanDeg C (RD.ellOf μ)) fun x hx0 => ?_
  have hx := hb.1 (oneIdx x)
  have hcc := shift_add_eq_zero (isInternal_homDeg (RD := RD) (k := k) _ _) _ _ _ _ hF hG hFG hx hx0
  have hw := wt_eq_of_rd_append (wt_eq_of_homD_ne hx hx0)
  beta_reduce
  rw [spanDeg_bend, wl_ellOf_eq', ← hw, ← neg_neg (rcx C _ s), ← sdegSum_cupA_rd]
  have : sdegSum RD μ ([] : List (LayerData I)) = 0 := rfl
  omega

omit [DecidableEq I] [Finite I] in
/-- **Two-sided spanning families bend to one-sided ones.** -/
theorem isSpanFamily_bendF (μ : X) (s t : List (Letter I))
    {b : SpanIdx s t → ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))}
    (hb : IsSpanFamily RD k μ s t b) :
    IsSpanFamily RD k μ [] (rd s ++ t) fun x => bendF RD k μ s t (b x) := by
  obtain ⟨hF, hG, hGF, hFG⟩ := bend_facts (RD := RD) (k := k) μ s t
  refine isGradedSpan_transport (isInternal_homDeg (RD := RD) (k := k) _ _) _ _ _ _ hG hF hFG
    (J := SpanIdx [] (rd s ++ t)) (b := fun x => b x) (δ := fun x => spanDeg C (RD.ellOf μ) (s := s)
      (t := t) x) hb (spanDeg C (RD.ellOf μ)) fun x hx0 => ?_
  have hx := hb.1 x
  have hcc := shift_add_eq_zero (isInternal_homDeg (RD := RD) (k := k) _ _) _ _ _ _ hG hF hGF hx hx0
  have hw := wt_eq_of_homD_ne hx hx0
  have h1 := spanDeg_bend (C := C) (RD.ellOf μ) (s := s) (t := t) x
  simp only [oneIdx] at h1
  rw [wl_ellOf_eq', ← hw, ← neg_neg (rcx C _ s), ← sdegSum_cupA_rd] at h1
  have h2 : sdegSum RD μ ([] : List (LayerData I)) = 0 := rfl
  beta_reduce
  omega

omit [DecidableEq I] [Finite I] in
/-- **Proposition 3.11 reduces to the one-sided case**: if every `HOM_U(1_μ, E_u 1_μ)` has a graded
spanning family indexed by `B_{∅,u,μ}`, then so has every `HOM_U(E_s 1_μ, E_t 1_μ)`. -/
theorem prop311_of_oneSided
    (h : ∀ (μ : X) (u : List (Letter I)), ∃ b, IsSpanFamily RD k μ [] u b) : Prop311 RD k :=
  fun μ s t => by
    obtain ⟨b, hb⟩ := h μ (rd s ++ t)
    exact ⟨_, isSpanFamily_bendG μ s t hb⟩

/-! ## Consequences of the positive case -/

include hSL in
/-- `B_{+c,+b,λ}` spans, for arbitrary lists `c`, `b` (if they do not have the same letters,
`HOM` is zero and so is the family). -/
theorem exists_isSpanFamily_positive (μ : X) (c b : List I) :
    ∃ f, IsSpanFamily RD k μ (posW c) (posW b) f := by
  by_cases hcb : (c : Multiset I) = b
  · have h := isSpanFamily_posB (RD := RD) (k := k) hSL μ (seqOfList c) (hcb.symm ▸ seqOfList b)
    have hj : word (hcb.symm ▸ seqOfList b : KLR.Seq (c : Multiset I)) = b :=
      (word_cast hcb.symm _).trans (word_seqOfList b)
    have h' : ∃ f, IsSpanFamily RD k μ (posW (word (seqOfList c)))
        (posW (word (hcb.symm ▸ seqOfList b : KLR.Seq (c : Multiset I)))) f := ⟨_, h⟩
    rw [word_seqOfList, hj] at h'
    exact h'
  · have hp : ¬ (posW c).Perm (posW b) := fun hp => hcb (Multiset.coe_eq_coe.2 (by
      have := hp.map Prod.snd
      simpa [posW, List.map_map, Function.comp_def] using this))
    refine ⟨0, fun x => zero_mem _, fun d => ?_⟩
    rw [homD_eq_bot_of_not_perm hSL μ (by simp [Positive, posW]) (by simp [Positive, posW]) hp d,
      Submodule.span_eq_bot]
    rintro _ ⟨_, rfl⟩
    rfl

include hSL in
/-- **Proposition 3.11 for the normally ordered one-sided words `F_c E_b`**:
`HOM_U(1_λ, E_{(-c)(+b)} 1_λ)` has a graded spanning family indexed by `B_{∅,(-c)(+b),λ}` (the
bent images of `B_{+c^{rev},+b,λ}`). -/
theorem exists_isSpanFamily_negW_posW (μ : X) (c b : List I) :
    ∃ f, IsSpanFamily RD k μ [] (negW c ++ posW b) f := by
  obtain ⟨f, hf⟩ := exists_isSpanFamily_positive (RD := RD) (k := k) hSL μ c.reverse b
  have h : ∃ f, IsSpanFamily RD k μ [] (rd (posW c.reverse) ++ posW b) f :=
    ⟨_, isSpanFamily_bendF μ _ _ hf⟩
  rwa [rd_posW_reverse] at h

include hSL in
/-- **Proposition 3.11 (in the form `IsSpanFamily`) for every pair `(s, t)` whose one-sided
boundary word `s* t` is normally ordered** (`s* t = (-c)(+b)`; e.g. `s` and `t` positive, or
`s = ∅` and `t = (-c)(+b)`, or `s = (-b')(+c')` and `t` positive). -/
theorem exists_isSpanFamily_of_normal (μ : X) {s t : List (Letter I)} {c b : List I}
    (h : rd s ++ t = negW c ++ posW b) : ∃ f, IsSpanFamily RD k μ s t f := by
  obtain ⟨f, hf⟩ := exists_isSpanFamily_negW_posW (RD := RD) (k := k) hSL μ c b
  have h' : ∃ f, IsSpanFamily RD k μ [] (rd s ++ t) f := by rw [h]; exact ⟨f, hf⟩
  obtain ⟨g, hg⟩ := h'
  exact ⟨_, isSpanFamily_bendG μ s t hg⟩

end Bend

end Categorification.KL3.Diagram
