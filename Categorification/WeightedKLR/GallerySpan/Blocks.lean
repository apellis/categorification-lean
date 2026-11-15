/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GallerySpan.Realize

/-!
# Reversing the hyperplanes through a codimension-two flat

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.13.

A flip of the word of a segment reverses a block `B` of consecutive hyperplanes all passing
through a point `x` of a flat of codimension two, and through no other hyperplane. Under (†)
and the absence of loops of weight `0`, distinct hyperplanes through a common point lie on
distinct pairs of strands, so that a block of length two consists of independent hyperplanes
and a block of length at least three is a triangle `{u, v}, {u, w}, {v, w}` of length exactly
three (`Hyp.triangle`). The square and hexagon relations then show that reversing the block
changes the gallery by an element with fewer steps (`galList_block`), and so do flips and
chains of flips (`galList_flip`, `galList_reflTransGen`).

## Main results

* `Hyp.triangle`: three distinct hyperplanes through a flat of codimension two lie on the three
  pairs of three strands.
* `FullChamber.Adjacent.smul`: relabelling preserves adjacency.
* `galList_block`, `galList_flip`, `galList_reflTransGen`.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

/-! ### The linear parts of the hyperplanes -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem linear_single_eq_zero {h : Hyp Γ ν} {s : Strand ν} (hs : ¬Mem s h) :
    (hypAff h).linear (Pi.single s (1 : 𝕜)) = 0 := by
  rw [hypAff_linear_apply]
  unfold Mem at hs
  push Not at hs
  simp [Ne.symm hs.1, Ne.symm hs.2]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem linear_single_ne_zero {h : Hyp Γ ν} {s : Strand ν} (hs : Mem s h) :
    (hypAff h).linear (Pi.single s (1 : 𝕜)) ≠ 0 := by
  rw [hypAff_linear_apply]
  rcases hs with rfl | rfl
  · simp [h.lo_ne_hi.symm]
  · simp [h.lo_ne_hi]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Distinct hyperplanes through a common point lie on distinct pairs of strands. -/
theorem exists_mem_not_mem (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {h g : Hyp Γ ν}
    {x : Strand ν → 𝕜} (hx : h.val x = 0) (gx : g.val x = 0) (hne : h ≠ g) :
    ∃ s, Mem s h ∧ ¬Mem s g := by
  by_contra hn
  push Not at hn
  exact hne (eq_of_isPair hD hZ hx gx (isPair_self h) (isPair_of_forall_mem hn))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A linear relation `ℓ₃ = α ℓ₁ + β ℓ₂` between the linear parts of three hyperplanes on
distinct pairs of strands forces the three pairs of three strands. -/
theorem triangle_of_rel {h₁ h₂ h₃ : Hyp Γ ν} (d₁₂ : ∃ s, Mem s h₁ ∧ ¬Mem s h₂)
    (d₁₃ : ∃ s, Mem s h₁ ∧ ¬Mem s h₃) (d₃₂ : ∃ s, Mem s h₃ ∧ ¬Mem s h₂) {α β : 𝕜}
    (hrel : ∀ y, (hypAff h₃).linear y = α * (hypAff h₁).linear y + β * (hypAff h₂).linear y) :
    ∃ u v w, h₁.IsPair u v ∧ h₂.IsPair u w ∧ h₃.IsPair v w := by
  have C1 : ∀ s, Mem s h₃ → Mem s h₁ ∨ Mem s h₂ := by
    intro s hs
    by_contra hn
    push Not at hn
    apply linear_single_ne_zero hs
    rw [hrel, linear_single_eq_zero hn.1, linear_single_eq_zero hn.2]
    ring
  have hα : α ≠ 0 := by
    rintro rfl
    obtain ⟨s, hs3, hs2⟩ := d₃₂
    apply linear_single_ne_zero hs3
    rw [hrel, linear_single_eq_zero hs2]
    ring
  have C2 : ∀ s, Mem s h₁ → Mem s h₂ ∨ Mem s h₃ := by
    intro s hs
    by_contra hn
    push Not at hn
    have e := hrel (Pi.single s 1)
    rw [linear_single_eq_zero hn.1, linear_single_eq_zero hn.2] at e
    have h0 : α * (hypAff h₁).linear (Pi.single s 1) = 0 := by linear_combination -e
    exact linear_single_ne_zero hs ((mul_eq_zero.1 h0).resolve_left hα)
  obtain ⟨s, hs1, hs2⟩ := d₁₂
  obtain ⟨t, ht1, ht3⟩ := d₁₃
  have hs3 : Mem s h₃ := (C2 s hs1).resolve_left hs2
  have ht2 : Mem t h₂ := (C2 t ht1).resolve_right ht3
  have hts : t ≠ s := fun e => hs2 (e ▸ ht2)
  have p₁ : h₁.IsPair t s := isPair_of_mem ht1 hs1 hts
  obtain ⟨w, -, p₂⟩ := exists_other ht2
  obtain ⟨c, hcs, p₃⟩ := exists_other hs3
  have hc3 : Mem c h₃ := (p₃.mem_iff c).2 (Or.inr rfl)
  have hct : c ≠ t := fun e => ht3 (e ▸ hc3)
  have hc2 : Mem c h₂ := by
    rcases C1 c hc3 with hc1 | hc2
    · rcases (p₁.mem_iff c).1 hc1 with e | e
      · exact absurd e hct
      · exact absurd e hcs
    · exact hc2
  have hcw : c = w := ((p₂.mem_iff c).1 hc2).resolve_left hct
  exact ⟨t, s, w, p₁, p₂, hcw ▸ p₃⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- In a span of linear parts of dimension two, the linear part of a third hyperplane is a
combination of those of two hyperplanes on distinct pairs of strands. -/
theorem exists_rel_of_finrank {B : List (Hyp Γ ν)}
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (hypAff h).linear) '' {h | h ∈ B})) = 2)
    {h₁ h₂ h₃ : Hyp Γ ν} (m₁ : h₁ ∈ B) (m₂ : h₂ ∈ B) (m₃ : h₃ ∈ B)
    (d₁₂ : ∃ s, Mem s h₁ ∧ ¬Mem s h₂) :
    ∃ α β : 𝕜, ∀ y, (hypAff h₃).linear y = α * (hypAff h₁).linear y +
      β * (hypAff h₂).linear y := by
  have hli : LinearIndependent 𝕜 ![(hypAff h₁).linear, (hypAff h₂).linear] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    obtain ⟨s, hs1, hs2⟩ := d₁₂
    have e := LinearMap.congr_fun hab (Pi.single s 1)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply,
      linear_single_eq_zero hs2, mul_zero, add_zero] at e
    have ha : a = 0 := (mul_eq_zero.1 e).resolve_right (linear_single_ne_zero hs1)
    subst ha
    have e' := LinearMap.congr_fun hab (Pi.single h₂.lo 1)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply,
      zero_mul, zero_add] at e'
    exact ⟨rfl, (mul_eq_zero.1 e').resolve_right (linear_single_ne_zero (Or.inl rfl))⟩
  have hle : Submodule.span 𝕜 (Set.range ![(hypAff h₁).linear, (hypAff h₂).linear]) ≤
      Submodule.span 𝕜 ((fun h => (hypAff h).linear) '' {h | h ∈ B}) := by
    rw [Matrix.range_cons_cons_empty]
    exact Submodule.span_mono (Set.insert_subset_iff.2
      ⟨⟨h₁, m₁, rfl⟩, Set.singleton_subset_iff.2 ⟨h₂, m₂, rfl⟩⟩)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli, hB]; rfl)
  have h3 : (hypAff h₃).linear ∈
      Submodule.span 𝕜 (Set.range ![(hypAff h₁).linear, (hypAff h₂).linear]) :=
    heq ▸ Submodule.subset_span ⟨h₃, m₃, rfl⟩
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at h3
  obtain ⟨α, β, e⟩ := h3
  exact ⟨α, β, fun y => by rw [← e]; rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Three distinct hyperplanes of a block through a flat of codimension two lie on the three
pairs of three strands. -/
theorem triangle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {B : List (Hyp Γ ν)} {x : Strand ν → 𝕜}
    (hx : ∀ h, h.val x = 0 ↔ h ∈ B)
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (hypAff h).linear) '' {h | h ∈ B})) = 2)
    {h₁ h₂ h₃ : Hyp Γ ν} (m₁ : h₁ ∈ B) (m₂ : h₂ ∈ B) (m₃ : h₃ ∈ B) (n₁₂ : h₁ ≠ h₂)
    (n₁₃ : h₁ ≠ h₃) (n₂₃ : h₂ ≠ h₃) :
    ∃ u v w, h₁.IsPair u v ∧ h₂.IsPair u w ∧ h₃.IsPair v w := by
  have z₁ := (hx h₁).2 m₁
  have z₂ := (hx h₂).2 m₂
  have z₃ := (hx h₃).2 m₃
  have d₁₂ := exists_mem_not_mem hD hZ z₁ z₂ n₁₂
  obtain ⟨α, β, hrel⟩ := exists_rel_of_finrank hB m₁ m₂ m₃ d₁₂
  exact triangle_of_rel d₁₂ (exists_mem_not_mem hD hZ z₁ z₃ n₁₃)
    (exists_mem_not_mem hD hZ z₃ z₂ n₂₃.symm) hrel

end Hyp

/-! ### Relabelling the hyperplanes -/

namespace Hyp

open Equiv

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem comap_isPair (g : ColPerm ν) (h : Hyp Γ ν) :
    (h.comap g).IsPair (g.1⁻¹ h.lo) (g.1⁻¹ h.hi) := by
  rcases h with W | d
  · exact Or.inl ⟨rfl, rfl⟩
  · show Hyp.IsPair (Sum.inr (d.comap g).1 : Hyp Γ ν) _ _
    unfold Diag.comap
    split_ifs
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsPair.right_unique {h : Hyp Γ ν} {a b c : Strand ν} (hp : h.IsPair a b)
    (hq : h.IsPair a c) : b = c :=
  ((hq.mem_iff b).1 ((hp.mem_iff b).2 (Or.inr rfl))).resolve_left hp.ne.symm

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Relabelling by the transposition of the strands `a, b` of a diagonal sends a hyperplane on
`a, c` to one on `b, c`. -/
theorem comap_refl_isPair {d : Diag ν} {a b c : Strand ν}
    (hd : Hyp.IsPair (Sum.inr d : Hyp Γ ν) a b) (hca : c ≠ a) (hcb : c ≠ b) {h : Hyp Γ ν}
    (hh : h.IsPair a c) : (h.comap d.refl).IsPair b c := by
  have hsw : ∀ s, d.refl.1⁻¹ s = swap a b s := by
    intro s
    show (swap d.fst d.snd)⁻¹ s = _
    rw [swap_inv]
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · change d.fst = a at h1
      change d.snd = b at h2
      rw [h1, h2]
    · change d.fst = b at h1
      change d.snd = a at h2
      rw [h1, h2, swap_comm]
  have key := comap_isPair d.refl h
  rw [hsw, hsw] at key
  rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, swap_apply_left, swap_apply_of_ne_of_ne hca hcb] at key
    exact key
  · rw [h1, h2, swap_apply_left, swap_apply_of_ne_of_ne hca hcb] at key
    exact key.symm

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem comap_val_eq_zero {g : ColPerm ν} {x : Strand ν → 𝕜} (hg : act g x = x)
    {h : Hyp Γ ν} (hx : h.val x = 0) : (h.comap g).val x = 0 := by
  have := Hyp.val_act g h x
  rw [hg, hx] at this
  split_ifs at this
  · exact neg_eq_zero.1 this.symm
  · exact this.symm

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem act_refl_of_val {d : Diag ν} {x : Strand ν → 𝕜}
    (hx : Hyp.val (Sum.inr d : Hyp Γ ν) x = 0) : act d.refl x = x := by
  have : d.val x = 0 := hx
  rw [Diag.val, sub_eq_zero] at this
  exact Diag.act_refl_of this.symm

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem inr_val_eq_zero_iff {d : Diag ν} {a b : Strand ν}
    (hp : Hyp.IsPair (Sum.inr d : Hyp Γ ν) a b) {x : Strand ν → 𝕜} :
    Hyp.val (Sum.inr d : Hyp Γ ν) x = 0 ↔ x a = x b := by
  rw [val_eq]
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    show x b - x a - 0 = 0 ↔ _
    rw [sub_zero, sub_eq_zero, eq_comm]
  · rw [h1, h2]
    show x a - x b - 0 = 0 ↔ _
    rw [sub_zero, sub_eq_zero]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem inr_colour {d : Diag ν} {a b : Strand ν}
    (hp : Hyp.IsPair (Sum.inr d : Hyp Γ ν) a b) : a.1 = b.1 := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact d.2.1
  · exact d.2.1.symm

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two distinct strands of the same colour are joined by a diagonal. -/
theorem exists_inr_isPair {a b : Strand ν} (hl : a.1 = b.1) (hne : a ≠ b) :
    ∃ d : Diag ν, Hyp.IsPair (Sum.inr d : Hyp Γ ν) a b := by
  rcases lt_trichotomy a.2.val b.2.val with h | h | h
  · exact ⟨⟨(a, b), hl, h⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact absurd (Strand.ext_of hl h) hne
  · exact ⟨⟨(b, a), hl.symm, h⟩, Or.inr ⟨rfl, rfl⟩⟩

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem comap_injective (g : ColPerm ν) : Function.Injective (Hyp.comap (Γ := Γ) g) := by
  intro h h' e
  rcases h with W | d <;> rcases h' with W' | d'
  · have e' := congrArg Subtype.val (Sum.inl_injective e)
    simp only [Wall.comap, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e'
    exact congrArg Sum.inl (Subtype.ext (Prod.ext e'.1 (Prod.ext e'.2.1 e'.2.2)))
  · cases e
  · cases e
  · have e' := Sum.inr_injective e
    unfold Diag.comap at e'
    congr 1
    split_ifs at e' with h1 h2 h2
    · have e'' := congrArg Subtype.val e'
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e''
      exact Subtype.ext (Prod.ext e''.1 e''.2)
    · exfalso
      have e'' := congrArg Subtype.val e'
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e''
      have h3 : d.fst.2.val < d.snd.2.val := d.2.2
      have h4 : d'.fst.2.val < d'.snd.2.val := d'.2.2
      rw [e''.1, e''.2] at h3
      omega
    · exfalso
      have e'' := congrArg Subtype.val e'
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e''
      have h3 : d.fst.2.val < d.snd.2.val := d.2.2
      have h4 : d'.fst.2.val < d'.snd.2.val := d'.2.2
      rw [e''.1, e''.2] at h3
      omega
    · have e'' := congrArg Subtype.val e'
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at e''
      exact Subtype.ext (Prod.ext e''.2 e''.1)

end Hyp

namespace FullChamber

omit [DecidableEq I] in
/-- Relabelling preserves adjacency. -/
theorem Adjacent.smul {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hC : C.Adjacent C' h)
    (g : ColPerm ν) {h' : Hyp Γ ν} (hh : h'.comap g = h) : (g • C).Adjacent (g • C') h' := by
  refine ⟨?_, fun h'' hne => ?_⟩
  · show signMap g C.1 h' ≠ signMap g C'.1 h'
    have := hC.1
    simp only [signMap, hh]
    split_ifs
    · simpa using this
    · exact this
  · show signMap g C.1 h'' = signMap g C'.1 h''
    have : h''.comap g ≠ h := fun e => hne (Hyp.comap_injective g (e.trans hh.symm))
    simp only [signMap, hC.2 _ this]

/-- Across a diagonal `d`, a chamber has the same sign on a wall and on its image under the
transposition of the strands of `d`. -/
theorem Adjacent.inl_eq_comap_refl {C C' : FullChamber Γ ν} {d : Diag ν}
    (hC : C.Adjacent C' (.inr d)) (W : Wall Γ ν) :
    C.1 (.inl W) = C.1 (.inl (W.comap d.refl)) := by
  rw [hC.2 _ Sum.inl_ne_inr, ← hC.refl_smul]
  rfl

end FullChamber

/-! ### Hexagons through a triangle -/

namespace GalleryAlgebra

theorem hexagon_refl_smul (H : Hexagon Γ ν) {d : Diag ν} (e₂ : H.h₂ = .inr d)
    (hc : H.h₃.comap d.refl = H.h₁) : d.refl • H.A₀ = H.A₃ := by
  have a := H.adj₀₁.smul d.refl hc
  have hr : d.refl • H.A₁ = H.A₂ := Adjacent.refl_smul (by rw [← e₂]; exact H.adj₁₂)
  rw [hr] at a
  exact a.symm.eq_of_adjacent H.adj₂₃

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two diagonals sharing a strand force the hyperplane through the other two strands to be a
diagonal. -/
theorem not_two_diags (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {x : Strand ν → 𝕜}
    {a b c : Strand ν} {d₁ d₂ : Diag ν} (p₁ : Hyp.IsPair (Sum.inr d₁ : Hyp Γ ν) a b)
    (p₂ : Hyp.IsPair (Sum.inr d₂ : Hyp Γ ν) a c) (z₁ : Hyp.val (Sum.inr d₁ : Hyp Γ ν) x = 0)
    (z₂ : Hyp.val (Sum.inr d₂ : Hyp Γ ν) x = 0) {W : Wall Γ ν}
    (p₃ : Hyp.IsPair (Sum.inl W : Hyp Γ ν) b c) (z₃ : Hyp.val (Sum.inl W : Hyp Γ ν) x = 0) :
    False := by
  have hl : b.1 = c.1 := (Hyp.inr_colour p₁).symm.trans (Hyp.inr_colour p₂)
  obtain ⟨e, pe⟩ := Hyp.exists_inr_isPair (Γ := Γ) hl p₃.ne
  have ze : Hyp.val (Sum.inr e : Hyp Γ ν) x = 0 :=
    (Hyp.inr_val_eq_zero_iff pe).2 (((Hyp.inr_val_eq_zero_iff p₁).1 z₁).symm.trans
      ((Hyp.inr_val_eq_zero_iff p₂).1 z₂))
  have := Hyp.eq_of_isPair hD hZ ze z₃ pe p₃
  cases this

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hyp_cases (h : Hyp Γ ν) : (∃ W, h = .inl W) ∨ ∃ d, h = .inr d := by
  rcases h with W | d
  · exact .inl ⟨W, rfl⟩
  · exact .inr ⟨d, rfl⟩

/-- Reversing three hyperplanes through a flat of codimension two, on the three pairs of three
strands `u, v, w`, changes the gallery by an element of at most one step. -/
theorem galList_hexagon_block (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (H : Hexagon Γ ν)
    {x : Strand ν → 𝕜} (z₁ : H.h₁.val x = 0) (z₂ : H.h₂.val x = 0) (z₃ : H.h₃.val x = 0)
    {u v w : Strand ν} (p₁ : H.h₁.IsPair u v) (p₂ : H.h₂.IsPair u w) (p₃ : H.h₃.IsPair v w) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] - galList k H.A₀ [H.h₃, H.h₂, H.h₁] ∈
      stepFilt k Γ ν 1 := by
  have nuv := p₁.ne
  have nuw := p₂.ne
  have nvw := p₃.ne
  -- the image of `h₃` under the transposition of the strands of `h₂`, a diagonal, is `h₁`
  have hc₃ : ∀ d, H.h₂ = .inr d → H.h₃.comap d.refl = H.h₁ := fun d e₂ => by
    have pd : Hyp.IsPair (Sum.inr d : Hyp Γ ν) w u := e₂ ▸ p₂.symm
    exact Hyp.eq_of_isPair hD hZ
      (Hyp.comap_val_eq_zero (Hyp.act_refl_of_val (e₂ ▸ z₂)) z₃) z₁
      (Hyp.comap_refl_isPair pd nvw nuv.symm p₃.symm) p₁
  rcases hyp_cases H.h₁ with ⟨W₁, e₁⟩ | ⟨d₁, e₁⟩ <;>
    rcases hyp_cases H.h₂ with ⟨W₂, e₂⟩ | ⟨d₂, e₂⟩ <;>
    rcases hyp_cases H.h₃ with ⟨W₃, e₃⟩ | ⟨d₃, e₃⟩
  · -- three walls
    rw [galList_hex_walls H (by rw [e₁]; rfl) (by rw [e₂]; rfl) (by rw [e₃]; rfl), sub_self]
    exact Submodule.zero_mem _
  · -- a diagonal crossed last
    have pd : Hyp.IsPair (Sum.inr d₃ : Hyp Γ ν) w v := e₃ ▸ p₃.symm
    have h₁eq : H.h₁ = .inl (W₂.comap d₃.refl) :=
      Hyp.eq_of_isPair hD hZ z₁
        (Hyp.comap_val_eq_zero (h := .inl W₂) (Hyp.act_refl_of_val (d := d₃) (e₃ ▸ z₃))
          (e₂ ▸ z₂)) p₁
        (Hyp.comap_refl_isPair (h := .inl W₂) pd nuw nuv (e₂ ▸ p₂.symm)).symm
    have hσ := (show H.A₀.Adjacent H.A₅ (.inr d₃) from e₃ ▸ H.adj₀₅).inl_eq_comap_refl W₂
    rw [galList_hex_end_diag H W₂ d₃ e₂ (.inr ⟨h₁eq, e₃⟩) hσ, sub_self]
    exact Submodule.zero_mem _
  · -- a diagonal crossed in the middle
    have pd : Hyp.IsPair (Sum.inr d₂ : Hyp Γ ν) u w := e₂ ▸ p₂
    have h₃eq : H.h₃ = .inl (W₁.comap d₂.refl) :=
      Hyp.eq_of_isPair hD hZ z₃
        (Hyp.comap_val_eq_zero (h := .inl W₁) (Hyp.act_refl_of_val (d := d₂) (e₂ ▸ z₂))
          (e₁ ▸ z₁)) p₃
        (Hyp.comap_refl_isPair (h := .inl W₁) pd nuv.symm nvw (e₁ ▸ p₁)).symm
    have hA := hexagon_refl_smul H e₂ (hc₃ d₂ e₂)
    have hσ : H.A₀.1 (.inl W₁) ≠ H.A₀.1 (.inl (W₁.comap d₂.refl)) := by
      have s₃ : H.A₃.1 (.inl W₁) = H.A₀.1 (.inl (W₁.comap d₂.refl)) := by rw [← hA]; rfl
      rw [← s₃, ← e₁, ← H.adj₂₃.2 _ H.ne₁₃, ← H.adj₁₂.2 _ H.ne₁₂]
      exact H.adj₀₁.1
    exact stepFilt_mono (Nat.zero_le 1) (galList_hex_mid_diag H W₁ d₂ e₁ e₂ h₃eq hσ hA)
  · -- two diagonals and a wall
    exact (not_two_diags hD hZ (e₂ ▸ p₂.symm) (e₃ ▸ p₃.symm) (e₂ ▸ z₂) (e₃ ▸ z₃)
      (e₁ ▸ p₁) (e₁ ▸ z₁)).elim
  · -- a diagonal crossed first
    have pd : Hyp.IsPair (Sum.inr d₁ : Hyp Γ ν) u v := e₁ ▸ p₁
    have h₃eq : H.h₃ = .inl (W₂.comap d₁.refl) :=
      Hyp.eq_of_isPair hD hZ z₃
        (Hyp.comap_val_eq_zero (h := .inl W₂) (Hyp.act_refl_of_val (d := d₁) (e₁ ▸ z₁))
          (e₂ ▸ z₂)) p₃
        (Hyp.comap_refl_isPair (h := .inl W₂) pd nuw.symm nvw.symm (e₂ ▸ p₂))
    have hσ := (show H.A₀.Adjacent H.A₁ (.inr d₁) from e₁ ▸ H.adj₀₁).inl_eq_comap_refl W₂
    rw [galList_hex_end_diag H W₂ d₁ e₂ (.inl ⟨e₁, h₃eq⟩) hσ, sub_self]
    exact Submodule.zero_mem _
  · exact (not_two_diags hD hZ (e₁ ▸ p₁.symm) (e₃ ▸ p₃) (e₁ ▸ z₁) (e₃ ▸ z₃)
      (e₂ ▸ p₂) (e₂ ▸ z₂)).elim
  · exact (not_two_diags hD hZ (e₁ ▸ p₁) (e₂ ▸ p₂) (e₁ ▸ z₁) (e₂ ▸ z₂)
      (e₃ ▸ p₃) (e₃ ▸ z₃)).elim
  · -- three diagonals
    exact galList_hex_diags H d₁ d₂ d₃ u v w e₁ e₂ e₃ (by rw [e₁] at p₁; exact p₁)
      (by rw [e₂] at p₂; exact p₂) (by rw [e₃] at p₃; exact p₃)
      (hexagon_refl_smul H e₂ (hc₃ d₂ e₂))

end GalleryAlgebra

end Categorification.WeightedKLR
