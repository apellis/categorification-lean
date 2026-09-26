/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SortedSpanWords
import Categorification.Diagrams.KL3.SurjectivityK0

/-!
# The spanning hypothesis `SortedSpan` and KL III Theorem 1.1

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3
(Proposition 3.11: spanning sets of `HOM_U` built from minimal diagrams, obtained by reducing
arbitrary diagrams modulo lower terms), §3.2.4 (the endomorphisms of `E_{ν,-ν'} 1_λ` modulo the
ideal of 2-morphisms factoring through shorter sequences) and §3.8.4 (*Proof of Theorem 1.1*).

We prove the hypothesis `SortedSpan` of `Categorification.Diagrams.KL3.SurjectivityTop`
(`sortedSpan_of_simplyLaced`, simply-laced Cartan data): every endomorphism of a sorted `E_{+a} E_{-b} 1_μ` is a
linear combination of split diagrams followed by bubble monomials, modulo composites of
homogeneous 2-morphisms through sequences of length `< |a| + |b|`.

## The argument

By induction on the number of crossings of a normal-form diagram `E_{+a} E_{-b} 1_μ →
E_{+a} E_{-b} 1_μ`:

* by the elimination of caps (`capElim`), it is a linear combination of move diagrams (dots,
  crossings and cups) followed by bubble monomials, modulo diagrams factoring through shorter
  sequences (`thruShort`, whose elements are sums of composites of homogeneous diagrams,
  `thruShort_le_span_homGen`);
* a move diagram between sequences of the same length has no cups (`noCup_of_mvChain`);
* a diagram of dots and crossings is, modulo diagrams with fewer crossings, dots followed by the
  crossings of a word `ρ` (`pushDots`); if `ρ` is not reduced it gives lower terms (Matsumoto's
  theorem, `xWord_braidEquiv`, `xWord_hasRepeat`); if `ρ` is reduced, the permutation of `ρ`
  preserves the letters of `E_{+a} E_{-b}`, hence the two blocks, so `ρ` is braid equivalent
  to a reduced word of `S_{|a|} × S_{|b|}` (`eq_blockPerm_of_preserves`,
  `TypeA.IsReduced.append_shiftWord`), whose diagram is split (`crossOnly_mem`).

## Main results

* `sortedSpan_of_simplyLaced`: **`SortedSpan RD k`** (simply-laced, `k` a field).
* `gammaUA'_surjective`: **KL III Theorem 1.1**: `γ : _𝒜 U̇ → K₀(U̇)` is surjective
  (simply-laced, `I` finite, `k` a field).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Crossing words on concatenations -/

theorem xAt_of_le : ∀ (s : List (Letter I)) (p : ℕ), ¬ p + 1 < s.length → xAt s p = []
  | a :: b :: s, 0, h => by simp at h
  | a :: s, p + 1, h => by
    rw [xAt, xAt_of_le s p (by simp at h ⊢; omega)]; rfl
  | [], _, _ => by simp [xAt]
  | [a], 0, _ => by simp [xAt]

theorem xWord_append_left (s₁ s₂ : List (Letter I)) : ∀ (α : List ℕ),
    TypeA.ValidWord s₁.length α →
    xWord (s₁ ++ s₂) α = (xWord s₁ α).map (whL [] s₂) ∧
      lapply (s₁ ++ s₂) α = lapply s₁ α ++ s₂
  | [], _ => ⟨rfl, rfl⟩
  | p :: α, hv => by
    rw [TypeA.validWord_cons] at hv
    obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid hv.1
    have e1 : u ++ [a, b] ++ v ++ s₂ = u ++ [a, b] ++ (v ++ s₂) := by simp
    have ih := xWord_append_left (u ++ [b, a] ++ v) s₂ α (by simpa using hv.2)
    have e2 : u ++ [b, a] ++ (v ++ s₂) = u ++ [b, a] ++ v ++ s₂ := by simp
    simp only [xWord, lapply, List.foldl_cons] at ih ⊢
    rw [e1, xAt_mid, lswap_mid, e2, ih.1, xAt_mid, lswap_mid]
    refine ⟨?_, ih.2⟩
    simp only [List.map_append]; wnf

theorem xWord_shift (s₁ s₂ : List (Letter I)) : ∀ (β : List ℕ),
    TypeA.ValidWord s₂.length β →
    xWord (s₁ ++ s₂) (TypeA.shiftWord s₁.length β) = (xWord s₂ β).map (whL s₁ []) ∧
      lapply (s₁ ++ s₂) (TypeA.shiftWord s₁.length β) = s₁ ++ lapply s₂ β
  | [], _ => ⟨rfl, rfl⟩
  | p :: β, hv => by
    rw [TypeA.validWord_cons] at hv
    obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid hv.1
    have ih := xWord_shift s₁ (u ++ [b, a] ++ v) β (by simpa using hv.2)
    have e1 : s₁ ++ (u ++ [a, b] ++ v) = (s₁ ++ u) ++ [a, b] ++ v := by simp
    have e2 : (s₁ ++ u) ++ [b, a] ++ v = s₁ ++ (u ++ [b, a] ++ v) := by simp
    have hsh : TypeA.shiftWord s₁.length (u.length :: β) =
        (s₁ ++ u).length :: TypeA.shiftWord s₁.length β := by
      simp [TypeA.shiftWord]
    rw [hsh]
    simp only [xWord, lapply, List.foldl_cons] at ih ⊢
    rw [e1, xAt_mid, lswap_mid, e2, ih.1, xAt_mid, lswap_mid]
    refine ⟨?_, ih.2⟩
    simp only [List.map_append]; wnf

/-- Crossings of upward strands are upward. -/
theorem upward_xWord : ∀ (s : List (Letter I)) (ρ : List ℕ), Positive s → Upward (xWord s ρ)
  | s, [], _ => fun _ h => by simp [xWord] at h
  | s, p :: ρ, hs => by
    rw [xWord]
    refine Upward.append ?_ (upward_xWord _ ρ (fun l hl => hs l ((lswap_perm s p).subset hl)))
    by_cases hp : p + 1 < s.length
    · obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid hp
      rw [xAt_mid]
      obtain ⟨ea, i⟩ := a; obtain ⟨eb, j⟩ := b
      have ha : ea = true := hs (ea, i) (by simp)
      have hb : eb = true := hs (eb, j) (by simp)
      subst ha hb
      intro x hx
      simp only [xLay_up_up, List.map_cons, List.map_nil, List.mem_singleton] at hx
      subst hx; rfl
    · rw [xAt_of_le s p hp]; intro _ h; simp at h

/-- Crossings of downward strands are downward. -/
theorem downward_xWord : ∀ (s : List (Letter I)) (ρ : List ℕ), Negative s → Downward (xWord s ρ)
  | s, [], _ => fun _ h => by simp [xWord] at h
  | s, p :: ρ, hs => by
    rw [xWord]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · by_cases hp : p + 1 < s.length
      · obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_mid hp
        rw [xAt_mid] at hx
        obtain ⟨ea, i⟩ := a; obtain ⟨eb, j⟩ := b
        have ha : ea = false := hs (ea, i) (by simp)
        have hb : eb = false := hs (eb, j) (by simp)
        subst ha hb
        simp only [xLay_dn_dn, List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx; rfl
      · rw [xAt_of_le s p hp] at hx; simp at hx
    · exact downward_xWord _ ρ (fun l hl => hs l ((lswap_perm s p).subset hl)) x hx

/-! ## Split diagrams -/

section Split

variable {k : Type w} [Field k] {μ : X}

theorem splitSet_comp {a b a₁ b₁ a₂ b₂ : List I} {f g}
    (hf : f ∈ SplitSet RD k μ a b a₁ b₁) (hg : g ∈ SplitSet RD k μ a₁ b₁ a₂ b₂) :
    f ≫ g ∈ SplitSet RD k μ a b a₂ b₂ := by
  obtain ⟨D₁, U₁, hD₁, hU₁, hcD₁, hcU₁, rfl⟩ := hf
  obtain ⟨D₂, U₂, hD₂, hU₂, hcD₂, hcU₂, rfl⟩ := hg
  have c1 : SChain (ups a ++ dns b) (D₁.map (whL (ups a) []) ++ U₁.map (whL [] (dns b₁)))
      (ups a₁ ++ dns b₁) := by
    have h1 : SChain (ups a ++ dns b) (D₁.map (whL (ups a) [])) (ups a ++ dns b₁) := by
      simpa using hcD₁.whisk (ups a) []
    have h2 : SChain (ups a ++ dns b₁) (U₁.map (whL [] (dns b₁))) (ups a₁ ++ dns b₁) := by
      simpa using hcU₁.whisk [] (dns b₁)
    exact h1.append h2
  have c2 : SChain (ups a₁ ++ dns b₁) (D₂.map (whL (ups a₁) []) ++ U₂.map (whL [] (dns b₂)))
      (ups a₂ ++ dns b₂) := by
    have h1 : SChain (ups a₁ ++ dns b₁) (D₂.map (whL (ups a₁) [])) (ups a₁ ++ dns b₂) := by
      simpa using hcD₂.whisk (ups a₁) []
    have h2 : SChain (ups a₁ ++ dns b₂) (U₂.map (whL [] (dns b₂))) (ups a₂ ++ dns b₂) := by
      simpa using hcU₂.whisk [] (dns b₂)
    exact h1.append h2
  refine ⟨D₁ ++ D₂, U₁ ++ U₂, fun x hx => ?_, fun x hx => ?_, hcD₁.append hcD₂,
    hcU₁.append hcU₂, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    exacts [hD₁ x hx, hD₂ x hx]
  · rcases List.mem_append.1 hx with hx | hx
    exacts [hU₁ x hx, hU₂ x hx]
  rw [dg_comp c1 c2]
  have := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := ups a ++ dns b) (t₀ := ups a₂ ++ dns b₂)
    (D₁.map (whL (ups a) [])) (U₂.map (whL [] (dns b₂))) [] [] hcU₁ hcD₂
  simp only [List.map_append, List.append_assoc] at this ⊢
  wnf at this ⊢
  exact this

theorem one_mem_splitSet (a b : List I) :
    𝟙 _ ∈ SplitSet RD k μ a b a b :=
  ⟨[], [], fun _ h => by simp at h, fun _ h => by simp at h, rfl, rfl, by simp [dg_nil]⟩

theorem dot_mem_splitSet {a b : List I} {x : LayerData I} (hx : x.2.1.isDot = true)
    (hc : SChain (ups a ++ dns b) [x] (ups a ++ dns b)) :
    dg RD k μ (ups a ++ dns b) (ups a ++ dns b) [x] ∈ SplitSet RD k μ a b a b := by
  obtain ⟨P, g, Q⟩ := x
  cases g with
  | dot l =>
    have h : P ++ ([l] ++ Q) = ups a ++ dns b := by simpa using hc.1.symm
    rcases List.append_eq_append_iff.1 h with ⟨a', ha, hQ⟩ | ⟨c', hP, hb⟩
    · rcases a' with _ | ⟨l', a''⟩
      · simp at ha hQ
        -- a downward dot at the left end of `dns b`
        subst ha
        refine ⟨[([], .dot l, Q)], [], fun y hy => ?_, fun _ h => by simp at h, ⟨by simp [← hQ],
          by simp [← hQ]⟩, rfl, ?_⟩
        · simp at hy; subst hy
          have : l ∈ dns b := by rw [← hQ]; simp
          obtain ⟨c, -, rfl⟩ := List.mem_map.1 this; rfl
        · simp [whL]
      · simp at hQ
        obtain ⟨rfl, rfl⟩ := hQ
        -- an upward dot
        have hmem : l ∈ ups a := by rw [ha]; simp
        refine ⟨[], [(P, .dot l, a'')], fun _ h => by simp at h, fun y hy => ?_, rfl,
          ⟨by simpa using ha, by simpa using ha.symm⟩, ?_⟩
        · simp at hy; subst hy
          obtain ⟨c, -, rfl⟩ := List.mem_map.1 hmem; rfl
        · simp [whL]
    · subst hP
      have hmem : l ∈ dns b := by rw [hb]; simp
      refine ⟨[(c', .dot l, Q)], [], fun y hy => ?_, fun _ h => by simp at h,
        ⟨by simpa using hb, by simpa using hb.symm⟩, rfl, ?_⟩
      · simp at hy; subst hy
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hmem; rfl
      · simp [whL]
  | _ => simp [Shape.isDot] at hx

theorem dots_mem_splitSet {a b : List I} : ∀ (D : List (LayerData I)), AllSh Shape.isDot D →
    SChain (ups a ++ dns b) D (ups a ++ dns b) →
    dg RD k μ (ups a ++ dns b) (ups a ++ dns b) D ∈ SplitSet RD k μ a b a b
  | [], _, _ => by rw [dg_nil]; exact one_mem_splitSet a b
  | x :: D, hD, hc => by
    have hx : x.2.1.isDot = true := hD x List.mem_cons_self
    have hxc : SChain (ups a ++ dns b) [x] (ups a ++ dns b) := by
      obtain ⟨P, g, Q⟩ := x
      cases g with
      | dot l => exact ⟨hc.1, by simpa using hc.1.symm⟩
      | _ => simp [Shape.isDot] at hx
    have hDc : SChain (ups a ++ dns b) D (ups a ++ dns b) := by
      have h2 := hc.2
      have e : x.1 ++ x.2.1.cod ++ x.2.2 = ups a ++ dns b := hxc.2
      rwa [e] at h2
    rw [show x :: D = [x] ++ D from rfl, dg_append_of_left hxc]
    exact splitSet_comp (dot_mem_splitSet hx hxc)
      (dots_mem_splitSet D (fun y hy => hD y (List.mem_cons_of_mem _ hy)) hDc)

theorem positive_lapply {s : List (Letter I)} (hs : Positive s) (ρ : List ℕ) :
    Positive (lapply s ρ) := fun l hl => hs l ((lapply_perm s ρ).subset hl)

theorem negative_lapply {s : List (Letter I)} (hs : Negative s) (ρ : List ℕ) :
    Negative (lapply s ρ) := fun l hl => hs l ((lapply_perm s ρ).subset hl)

theorem negative_dns (b : List I) : Negative (dns b) := by
  intro l hl; obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl; rfl

/-- Upward crossings are split. -/
theorem upX_mem_splitSet (a b : List I) {α : List ℕ} (hα : TypeA.ValidWord (ups a).length α) :
    dg RD k μ (ups a ++ dns b) (ups ((lapply (ups a) α).map Prod.snd) ++ dns b)
      ((xWord (ups a) α).map (whL [] (dns b))) ∈
      SplitSet RD k μ a b ((lapply (ups a) α).map Prod.snd) b := by
  have e := ups_map_snd (positive_lapply (positive_ups a) α)
  refine ⟨[], xWord (ups a) α, fun _ h => by simp at h, upward_xWord _ _ (positive_ups a), rfl,
    by rw [e]; exact sChain_xWord hα, by simp⟩

/-- Downward crossings are split. -/
theorem dnX_mem_splitSet (a b : List I) {β : List ℕ} (hβ : TypeA.ValidWord (dns b).length β) :
    dg RD k μ (ups a ++ dns b) (ups a ++ dns ((lapply (dns b) β).map Prod.snd))
      ((xWord (dns b) β).map (whL (ups a) [])) ∈
      SplitSet RD k μ a b a ((lapply (dns b) β).map Prod.snd) := by
  have e := dns_map_snd (negative_lapply (negative_dns b) β)
  refine ⟨xWord (dns b) β, [], downward_xWord _ _ (negative_dns b), fun _ h => by simp at h,
    by rw [e]; exact sChain_xWord hβ, rfl, by simp⟩

omit [AddCommGroup X] [AddCommGroup Y] in
theorem ups_dns_inj {a b a' b' : List I} (h : ups a' ++ dns b' = ups a ++ dns b) :
    a' = a ∧ b' = b := by
  have hc : ∀ (a b : List I), (ups a ++ dns b).countP (fun l => l.1) = a.length := by
    intro a b
    simp [List.countP_append, ups, dns, List.countP_map, Function.comp_def, up, dn]
  have hl : a'.length = a.length := by rw [← hc a' b', h, hc]
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  refine ⟨List.map_injective_iff.2 (fun x y hxy => ?_) h1, List.map_injective_iff.2
    (fun x y hxy => ?_) h2⟩
  · simpa [up] using hxy
  · simpa [dn] using hxy

omit [AddCommGroup X] [AddCommGroup Y] in
theorem fst_getElem?_updn (a b : List I) {j : ℕ} (hj : j < a.length + b.length) :
    ((ups a ++ dns b)[j]?).map Prod.fst = some (decide (j < a.length)) := by
  by_cases h : j < a.length
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [ups, up, h]
  · rw [List.getElem?_append_right (by simp; omega)]
    have : j - (ups a).length < b.length := by simp; omega
    simp [dns, dn, h]
    exact ⟨_, List.getElem?_eq_getElem (by simp at this; omega)⟩

omit [AddCommGroup X] [AddCommGroup Y] in
theorem lapply_eq_of_wordProd {α : Type*} {m : ℕ} {s : List α} (hs : s.length = m) {ρ σ : List ℕ}
    (hρ : TypeA.ValidWord m ρ) (hσ : TypeA.ValidWord m σ)
    (h : TypeA.wordProd m ρ = TypeA.wordProd m σ) : lapply s ρ = lapply s σ := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < m
  · have e1 := getElem?_lapply m ρ s hs hρ ⟨i, hi⟩
    have e2 := getElem?_lapply m σ s hs hσ ⟨i, hi⟩
    simp only at e1 e2
    rw [e1, e2, h]
  · rw [List.getElem?_eq_none (by rw [length_lapply]; omega),
      List.getElem?_eq_none (by rw [length_lapply]; omega)]

variable [DecidableEq I]

/-- **Diagrams without caps and cups between sorted sequences** are split diagrams modulo
diagrams with fewer crossings. -/
theorem crossOnly_mem (a b : List I) (ms : List (Mv I))
    (hms : MvChain (ups a ++ dns b) ms (ups a ++ dns b)) (hcup : ∀ m ∈ ms, m.isCup = false) :
    dg RD k μ (ups a ++ dns b) (ups a ++ dns b) (mvLay ms) ∈
      Submodule.span k (SplitSet RD k μ a b a b) ⊔
        Lo RD k μ (ups a ++ dns b) (ups a ++ dns b) (ccnt (mvLay ms)) := by
  obtain ⟨D, ρ, hD, hDc, hv, hl, hm⟩ := pushDots (RD := RD) (k := k) μ ms hms hcup
  rw [← hl] at hm ⊢
  suffices H : dg RD k μ (ups a ++ dns b) (ups a ++ dns b) (D ++ xWord (ups a ++ dns b) ρ) ∈
      Submodule.span k (SplitSet RD k μ a b a b) ⊔
        Lo RD k μ (ups a ++ dns b) (ups a ++ dns b) ρ.length by
    have := Submodule.add_mem _ (Submodule.mem_sup_right hm) H
    simpa using this
  have hD0 : ccnt D = 0 := ccnt_eq_zero_of_dots hD
  rw [dg_append_of_left hDc]
  by_cases hr : TypeA.IsReduced (ups a ++ dns b).length ρ
  · by_cases hch : lapply (ups a ++ dns b) ρ = ups a ++ dns b
    · have hmab : a.length + b.length = (ups a ++ dns b).length := by simp
      have hpres : ∀ i : Fin (ups a ++ dns b).length,
          ((TypeA.wordProd (ups a ++ dns b).length ρ) i).val < a.length ↔ i.val < a.length := by
        intro i
        have e := getElem?_lapply _ ρ (ups a ++ dns b) rfl hv i
        rw [hch] at e
        have e' := congrArg (Option.map Prod.fst) e
        rw [fst_getElem?_updn a b (by simpa using i.2),
          fst_getElem?_updn a b (by simpa using ((TypeA.wordProd _ ρ) i).2)] at e'
        simpa using e'.symm
      obtain ⟨x, y, hxy⟩ := eq_blockPerm_of_preserves hmab _ hpres
      obtain ⟨α, hα, hαx⟩ := TypeA.exists_reduced a.length x
      obtain ⟨β, hβ, hβy⟩ := TypeA.exists_reduced b.length y
      have hαβ := TypeA.IsReduced.append_shiftWord hmab hα hβ
      have hwp : TypeA.wordProd _ (α ++ TypeA.shiftWord a.length β) =
          TypeA.wordProd (ups a ++ dns b).length ρ := by
        rw [TypeA.wordProd_append_shiftWord hmab hα.1 hβ.1, hαx, hβy, hxy]
      have hbe := TypeA.braidEquiv_of_isReduced hr hαβ hwp.symm
      have h1 := xWord_braidEquiv (RD := RD) (k := k) μ hbe (t := ups a ++ dns b) hv
      have happ : lapply (ups a ++ dns b) (α ++ TypeA.shiftWord a.length β) = ups a ++ dns b := by
        exact (lapply_eq_of_wordProd rfl hαβ.1 hv hwp).trans hch
      -- the split diagram
      have hsp : dg RD k μ (ups a ++ dns b) (ups a ++ dns b)
          (xWord (ups a ++ dns b) (α ++ TypeA.shiftWord a.length β)) ∈
            SplitSet RD k μ a b a b := by
        have hαv : TypeA.ValidWord (ups a).length α := by simpa using hα.1
        obtain ⟨e1, e2⟩ := xWord_append_left (ups a) (dns b) α hαv
        have hβv : TypeA.ValidWord (dns b).length β := by simpa using hβ.1
        generalize ha₁ : (lapply (ups a) α).map Prod.snd = a₁
        have hup : lapply (ups a) α = ups a₁ := by
          rw [← ha₁, ups_map_snd (positive_lapply (positive_ups a) α)]
        have hlen : (ups a₁).length = a.length := by
          rw [← hup, length_lapply]; simp
        obtain ⟨e3, e4⟩ := xWord_shift (ups a₁) (dns b) β hβv
        rw [hlen] at e3 e4
        generalize hb₂ : (lapply (dns b) β).map Prod.snd = b₂
        have hdn : lapply (dns b) β = dns b₂ := by
          rw [← hb₂, dns_map_snd (negative_lapply (negative_dns b) β)]
        have hA := upX_mem_splitSet (RD := RD) (k := k) (μ := μ) a b hαv
        rw [ha₁] at hA
        have hB := dnX_mem_splitSet (RD := RD) (k := k) (μ := μ) a₁ b hβv
        rw [hb₂] at hB
        have hAc : SChain (ups a ++ dns b) ((xWord (ups a) α).map (whL [] (dns b)))
            (ups a₁ ++ dns b) := by
          have := (sChain_xWord hαv).whisk [] (dns b)
          rw [hup] at this; simpa using this
        have hfin : ups a₁ ++ dns b₂ = ups a ++ dns b := by
          rw [← happ, lapply_append, e2, hup, e4, hdn]
        rw [xWord_append, e1, e2, hup, e3, dg_append_of_left hAc]
        obtain ⟨h₁, h₂⟩ := ups_dns_inj hfin
        subst h₁ h₂
        exact splitSet_comp hA hB
      -- combine
      have h3 := dg_comp_lo (s := ups a ++ dns b) D h1
      rw [hD0, zero_add, Preadditive.comp_sub] at h3
      have h4 : dg RD k μ (ups a ++ dns b) (ups a ++ dns b) D ≫
          dg RD k μ (ups a ++ dns b) (ups a ++ dns b)
            (xWord (ups a ++ dns b) (α ++ TypeA.shiftWord a.length β)) ∈
          Submodule.span k (SplitSet RD k μ a b a b) :=
        Submodule.subset_span (splitSet_comp (dots_mem_splitSet D hD hDc) hsp)
      have := Submodule.add_mem _ (Submodule.mem_sup_right h3) (Submodule.mem_sup_left h4)
      simpa using this
    · refine Submodule.mem_sup_right ?_
      rw [dg_of_not (show ¬ SChain _ _ _ from fun h => hch (SChain.tgt_unique (sChain_xWord hv) h)),
        Limits.comp_zero]
      exact Submodule.zero_mem _
  · obtain ⟨σ, hbe, hrep⟩ := TypeA.exists_braidEquiv_hasRepeat_of_not_isReduced hv hr
    have h1 := xWord_braidEquiv (RD := RD) (k := k) μ hbe (t := ups a ++ dns b) hv
    have h2 := xWord_hasRepeat (RD := RD) (k := k) μ hrep (t := ups a ++ dns b)
      ((braidEquiv_validWord hbe).1 hv)
    rw [← TypeA.BraidEquiv.length_eq hbe] at h2
    have h3 := Submodule.add_mem _ h1 h2
    rw [sub_add_cancel] at h3
    have h4 := dg_comp_lo (s := ups a ++ dns b) D h3
    rw [hD0, zero_add] at h4
    exact Submodule.mem_sup_right h4

end Split

/-! ## Move diagrams between sequences of the same length have no cups -/

omit [AddCommGroup X] [AddCommGroup Y] in
theorem MvChain.length_eq : ∀ {s t : List (Letter I)} {ms : List (Mv I)}, MvChain s ms t →
    t.length = s.length + 2 * ms.countP (fun m => m.isCup)
  | _, _, [], h => by subst h; simp
  | _, _, m :: ms, ⟨rfl, h⟩ => by
    have ih := MvChain.length_eq h
    rw [ih, List.countP_cons]
    cases m with
    | cup u l v => simp [Mv.src, Mv.tgt, Mv.isCup]; omega
    | _ => simp [Mv.src, Mv.tgt, Mv.isCup]

omit [AddCommGroup X] [AddCommGroup Y] in
theorem noCup_of_mvChain {s : List (Letter I)} {ms : List (Mv I)} (h : MvChain s ms s) :
    ∀ m ∈ ms, m.isCup = false := by
  have := MvChain.length_eq h
  have h0 : ms.countP (fun m => m.isCup) = 0 := by omega
  intro m hm
  simpa using (List.countP_eq_zero.1 h0) m hm

/-! ## Composites through shorter sequences -/

section Thru

variable {k : Type w} [Field k]

theorem comp_mem_span_homGen {μ : X} {w u : List (Letter I)} (hu : u.length < w.length)
    (g : (pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ u))
    (h : (pres RD k).obj (ob RD μ u) ⟶ (pres RD k).obj (ob RD μ w)) :
    g ≫ h ∈ Submodule.span k (homGen RD k μ w {u | u.length < w.length}) := by
  have hg := mem_span_dg (RD := RD) (k := k) μ g
  have hh := mem_span_dg (RD := RD) (k := k) μ h
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨L, hL, rfl⟩ := hg
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨M, hM, rfl⟩ := hh
      exact Submodule.subset_span ⟨u, hu, SChain.wt_eq RD μ hL, sdegSum RD μ L, sdegSum RD μ M, _, _,
        dg_mem_homD rfl, dg_mem_homD rfl, rfl⟩
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem thruShort_le_span_homGen (μ : X) (w : List (Letter I)) :
    thruShort RD k μ w w ≤ Submodule.span k (homGen RD k μ w {u | u.length < w.length}) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, g, h, hu, rfl⟩
  exact comp_mem_span_homGen hu g h

end Thru

/-! ## The spanning hypothesis -/

section Main

variable {k : Type w} [Field k] [DecidableEq I] (hSL : SimplyLaced C)

omit [DecidableEq I] in
theorem lo_comp_bubAt_mem {μ : X} {s : List (Letter I)} {n : ℕ} {f}
    (hf : f ∈ Lo RD k μ s s n) {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    f ≫ bubAt RD k μ s β ∈ Lo RD k μ s s n := by
  have hb : bubAt RD k μ s β ∈ LeL RD k μ s s 0 := by
    have := ctxL_leL (RD := RD) (k := k) (μ := μ) (s₀ := s) (t₀ := s) (pre := []) (post := [])
      (u := s) (v := []) (s := []) (t := []) (isBub_mem_leL hβ)
    simpa using this
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    have := leL_comp (dg_mem_leL (s := s) (t := s) (le_refl (ccnt L))) hb
    exact leL_le_lo (by omega) this
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

include hSL in
/-- **The spanning hypothesis `SortedSpan` holds** (simply-laced Cartan data): every
endomorphism of a sorted `E_{+a} E_{-b} 1_μ` is a linear combination of split diagrams followed by
bubble monomials, modulo composites of homogeneous 2-morphisms through sequences of length
`< |a| + |b|` (KL III §3.2.3–§3.2.4). -/
theorem sortedSpan_of_simplyLaced : SortedSpan RD k := by
  intro μ a b f
  set G := splitBubSpan RD k μ a b ⊔
    Submodule.span k (homGen RD k μ (ups a ++ dns b) {u | u.length < a.length + b.length})
  have hlen : (ups a ++ dns b).length = a.length + b.length := by simp
  have hthru : thruShort RD k μ (ups a ++ dns b) (ups a ++ dns b) ≤ G := by
    refine (thruShort_le_span_homGen μ _).trans ?_
    rw [hlen]; exact le_sup_right
  -- by induction on the number of crossings
  have key : ∀ c (L : List (LayerData I)), ccnt L ≤ c →
      dg RD k μ (ups a ++ dns b) (ups a ++ dns b) L ∈ G := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
    intro L hL
    have hlo : ∀ n ≤ c, Lo RD k μ (ups a ++ dns b) (ups a ++ dns b) n ≤ G := by
      intro n hn
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨L', hL', rfl⟩
      exact ihc (ccnt L') (by omega) L' le_rfl
    have hcap := capElim (RD := RD) (k := k) (hSL := hSL) (μ := μ) (w₀ := ups a ++ dns b) c
      (ups a ++ dns b) L hL
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hcap
    rw [← hxy]
    refine Submodule.add_mem _ ?_ (hthru hy)
    clear hxy hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hx
      have h := crossOnly_mem (RD := RD) (k := k) (μ := μ) a b ms hch (noCup_of_mvChain hch)
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 h
      rw [← hpq, Preadditive.add_comp]
      refine Submodule.add_mem _ ?_ (hlo _ hcc (lo_comp_bubAt_mem hq hβ))
      refine Submodule.mem_sup_left ?_
      clear hpq hq
      induction hp using Submodule.span_induction with
      | mem p hp => exact Submodule.subset_span ⟨p, hp, β, hβ, rfl⟩
      | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hf := mem_span_dg (RD := RD) (k := k) μ f
  refine (Submodule.span_le.mpr ?_) hf
  rintro _ ⟨L, -, rfl⟩
  exact key _ L le_rfl

end Main

section Surj

variable {k : Type w} [Field k] [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

/-- **KL III Theorem 1.1** (simply-laced Cartan data, `I` finite, `k` a field): the map
`γ : _𝒜 U̇ → K₀(U̇)` is surjective. -/
theorem gammaUA'_surjective (lam ρ : X) :
    Function.Surjective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_surjective_of_sortedSpan' hSL (sortedSpan_of_simplyLaced hSL) lam ρ

end Surj

end Categorification.KL3.Diagram
