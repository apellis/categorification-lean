/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GallerySpan.Blocks

/-!
# Flips of galleries

Spanning half of the proof of Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.8. A flip of a word reverses the block of hyperplanes through a
flat of codimension two. Under (†) and the absence of loops of weight `0`, such a block has two
or three hyperplanes: two independent ones (a square) or three on the three pairs of three
strands (a hexagon). The defining relations of the gallery algebra then show that a flip changes
the gallery by an element with fewer steps.

## Main results

* `GalleryAlgebra.galList_block`: reversing a block of hyperplanes through a flat of
  codimension two changes the gallery by an element of `stepFilt (length - 2)`.
* `GalleryAlgebra.galList_flip`, `GalleryAlgebra.galList_reflTransGen`: the same for a flip,
  and for a chain of flips, of a word all of whose prefixes are chambers.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem mem_strands_iff {h : Hyp Γ ν} {s : Strand ν} : s ∈ h.strands ↔ Mem s h := by
  rcases h with w | d <;> simp [Hyp.strands, Mem, lo, hi]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A hyperplane on a strand outside the pair of `h` is not `h`. -/
theorem IsPair.ne_of_not_mem {h g : Hyp Γ ν} {a b c d : Strand ν} (hp : h.IsPair a b)
    (hq : g.IsPair c d) (hca : c ≠ a) (hcb : c ≠ b) : g ≠ h := by
  rintro rfl
  rcases (hp.mem_iff c).1 ((hq.mem_iff c).2 (Or.inl rfl)) with e | e
  · exact hca e
  · exact hcb e

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A diagonal and another hyperplane through a common point and sharing a strand give a third
hyperplane through that point. -/
theorem exists_third_of_shared (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {x : Strand ν → 𝕜}
    {d : Diag ν} {h : Hyp Γ ν} (zd : Hyp.val (Sum.inr d : Hyp Γ ν) x = 0) (zh : h.val x = 0)
    (hne : (Sum.inr d : Hyp Γ ν) ≠ h) {a : Strand ν} (ad : Mem a (Sum.inr d : Hyp Γ ν))
    (ah : Mem a h) : ∃ g : Hyp Γ ν, g.val x = 0 ∧ g ≠ .inr d ∧ g ≠ h := by
  obtain ⟨c, hca, pd⟩ := exists_other ad
  obtain ⟨b, hba, ph⟩ := exists_other ah
  by_cases hbc : b = c
  · subst hbc
    exact absurd (eq_of_isPair hD hZ zd zh pd ph) hne
  have pg := comap_refl_isPair pd hba hbc ph
  exact ⟨_, comap_val_eq_zero (act_refl_of_val zd) zh,
    IsPair.ne_of_not_mem pd pg.symm hba hbc, IsPair.ne_of_not_mem ph pg hca (Ne.symm hbc)⟩

end Hyp

namespace GalleryAlgebra

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two distinct hyperplanes through a point at which no other hyperplane vanishes are
independent. -/
theorem independent_of_pair (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {x : Strand ν → 𝕜}
    {h₁ h₂ : Hyp Γ ν} (hx : ∀ h : Hyp Γ ν, h.val x = 0 ↔ h ∈ [h₁, h₂]) (hne : h₁ ≠ h₂) :
    h₁.Independent h₂ := by
  have z₁ := (hx h₁).2 (by simp)
  have z₂ := (hx h₂).2 (by simp)
  by_cases hl : h₁.isLeft ∧ h₂.isLeft
  · exact .inl hl
  by_cases hdj : Disjoint h₁.strands h₂.strands
  · exact .inr hdj
  exfalso
  obtain ⟨a, a₁, a₂⟩ := Finset.not_disjoint_iff.1 hdj
  rw [Hyp.mem_strands_iff] at a₁ a₂
  have third : ∀ (d : Diag ν) (h : Hyp Γ ν), Hyp.val (Sum.inr d : Hyp Γ ν) x = 0 →
      h.val x = 0 → (Sum.inr d : Hyp Γ ν) ≠ h → Hyp.Mem a (Sum.inr d : Hyp Γ ν) → Hyp.Mem a h →
      ({Sum.inr d, h} : Set (Hyp Γ ν)) = {h₁, h₂} → False := by
    intro d h zd zh n ad ah e
    obtain ⟨g, zg, g₁, g₂⟩ := Hyp.exists_third_of_shared hD hZ zd zh n ad ah
    have hg := (hx g).1 zg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    have : g ∈ ({h₁, h₂} : Set (Hyp Γ ν)) := by rcases hg with rfl | rfl <;> simp
    rw [← e] at this
    rcases this with rfl | rfl
    · exact g₁ rfl
    · exact g₂ rfl
  rcases GalleryAlgebra.hyp_cases h₁ with ⟨W₁, e₁⟩ | ⟨d₁, e₁⟩
  · rcases GalleryAlgebra.hyp_cases h₂ with ⟨W₂, e₂⟩ | ⟨d₂, e₂⟩
    · exact hl ⟨by rw [e₁]; rfl, by rw [e₂]; rfl⟩
    · subst e₁ e₂
      exact third d₂ _ z₂ z₁ (Ne.symm hne) a₂ a₁ (Set.pair_comm _ _)
  · subst e₁
    exact third d₁ h₂ z₁ z₂ hne a₁ a₂ rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A block of a flip has at most three hyperplanes. -/
theorem block_length_le (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {B : List (Hyp Γ ν)}
    {x : Strand ν → 𝕜} (hx : ∀ h : Hyp Γ ν, h.val x = 0 ↔ h ∈ B)
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (hypAff h).linear) '' {h | h ∈ B})) = 2)
    (hn : B.Nodup) : B.length ≤ 3 := by
  match B, hx, hB, hn with
  | [], _, _, _ => simp
  | [_], _, _, _ => simp
  | [_, _], _, _, _ => simp
  | [_, _, _], _, _, _ => simp
  | h₁ :: h₂ :: h₃ :: h₄ :: l, hx, hB, hn =>
    exfalso
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    obtain ⟨⟨n₁₂, n₁₃, n₁₄, -⟩, ⟨n₂₃, n₂₄, -⟩, ⟨n₃₄, -⟩, -⟩ := hn
    obtain ⟨u, v, w, p₁, p₂, p₃⟩ := Hyp.triangle hD hZ hx hB (by simp) (by simp) (by simp)
      n₁₂ n₁₃ n₂₃
    obtain ⟨u', v', w', p₁', p₂', p₄⟩ := Hyp.triangle hD hZ hx hB (by simp) (by simp)
      (h₃ := h₄) (by simp) n₁₂ n₁₄ n₂₄
    have hu : u' = u := by
      rcases (p₁.mem_iff u').1 ((p₁'.mem_iff u').2 (Or.inl rfl)) with e | e
      · exact e
      · exfalso
        subst e
        rcases (p₂.mem_iff u').1 ((p₂'.mem_iff u').2 (Or.inl rfl)) with e' | e'
        · exact p₁.ne e'.symm
        · exact p₃.ne e'
    subst hu
    have hv := p₁.right_unique p₁'
    have hw := p₂.right_unique p₂'
    subst hv hw
    exact n₃₄ (Hyp.eq_of_isPair hD hZ ((hx h₃).2 (by simp)) ((hx h₄).2 (by simp)) p₃ p₄)

/-- Reversing a block of hyperplanes through a flat of codimension two, along a word all of
whose prefixes, read either way, are chambers, changes the gallery by an element with fewer
steps. -/
theorem galList_block (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (E : FullChamber Γ ν)
    {B : List (Hyp Γ ν)} (hlen : 2 ≤ B.length) {x : Strand ν → 𝕜}
    (hx : ∀ h : Hyp Γ ν, h.val x = 0 ↔ h ∈ B)
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (hypAff h).linear) '' {h | h ∈ B})) = 2)
    (hw : GoodWord E.1 B) (hw' : GoodWord E.1 B.reverse) :
    galList k E B - galList k E B.reverse ∈ stepFilt k Γ ν (B.length - 2) := by
  have hle := block_length_le hD hZ hx hB hw.1
  have heq := flips_eq_of_perm hw hw' (List.reverse_perm B).symm
  match B, hlen, hle, hx, hB, hw, hw', heq with
  | [h₁, h₂], _, _, hx, _, hw, hw', heq =>
    have hn : h₁ ≠ h₂ := by simpa using hw.1
    obtain ⟨-, a₁, hw₁⟩ := hw.cons
    obtain ⟨-, a₂, -⟩ := hw₁.cons
    obtain ⟨-, a₃, hw₃⟩ := hw'.cons
    obtain ⟨-, a₄, -⟩ := hw₃.cons
    have hD' : (E.flipH h₂).flipH h₁ = (E.flipH h₁).flipH h₂ := heq.symm
    rw [hD'] at a₄
    have := galList_square (k := k) hn (independent_of_pair hD hZ hx hn) a₁ a₂ a₃ a₄
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [this, sub_self]
    exact Submodule.zero_mem _
  | [h₁, h₂, h₃], _, _, hx, hB, hw, hw', heq =>
    have hn := hw.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨n₁₂, n₁₃⟩, n₂₃, -⟩ := hn
    obtain ⟨-, a₁, hw₁⟩ := hw.cons
    obtain ⟨-, a₂, hw₂⟩ := hw₁.cons
    obtain ⟨-, a₃, -⟩ := hw₂.cons
    obtain ⟨-, a₅, hw₅⟩ := hw'.cons
    obtain ⟨-, a₄, hw₄⟩ := hw₅.cons
    obtain ⟨-, a₆, -⟩ := hw₄.cons
    have hE : ((E.flipH h₃).flipH h₂).flipH h₁ = ((E.flipH h₁).flipH h₂).flipH h₃ := heq.symm
    rw [hE] at a₆
    let H : Hexagon Γ ν :=
      { A₀ := E, A₁ := E.flipH h₁, A₂ := (E.flipH h₁).flipH h₂,
        A₃ := ((E.flipH h₁).flipH h₂).flipH h₃, A₄ := (E.flipH h₃).flipH h₂,
        A₅ := E.flipH h₃, h₁ := h₁, h₂ := h₂, h₃ := h₃, ne₁₂ := n₁₂, ne₁₃ := n₁₃,
        ne₂₃ := n₂₃, adj₀₁ := a₁, adj₁₂ := a₂, adj₂₃ := a₃, adj₀₅ := a₅, adj₅₄ := a₄,
        adj₄₃ := a₆ }
    obtain ⟨u, v, w, p₁, p₂, p₃⟩ := Hyp.triangle hD hZ hx hB (h₁ := h₁) (h₂ := h₂) (h₃ := h₃)
      (by simp) (by simp) (by simp) n₁₂ n₁₃ n₂₃
    have := galList_hexagon_block (k := k) hD hZ H ((hx h₁).2 (by simp)) ((hx h₂).2 (by simp))
      ((hx h₃).2 (by simp)) p₁ p₂ p₃
    simpa using this

theorem stepFilt_sub_mul {m n p : ℕ} {a b c d : GalleryAlgebra k Γ ν}
    (ha : a ∈ stepFilt k Γ ν m) (hbc : b - c ∈ stepFilt k Γ ν n) (hd : d ∈ stepFilt k Γ ν p) :
    a * (b * d) - a * (c * d) ∈ stepFilt k Γ ν (m + (n + p)) := by
  rw [← mul_sub, ← sub_mul]
  exact mul_mem_stepFilt ha (mul_mem_stepFilt hbc hd)

/-- A flip of a word all of whose prefixes are chambers changes the gallery by an element with
fewer steps. -/
theorem galList_flip (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C : FullChamber Γ ν}
    {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w) (hf : Flip (hypAff (Γ := Γ)) C.1 w w') :
    galList k C w - galList k C w' ∈ stepFilt k Γ ν (w.length - 2) := by
  have hw' := hw.flip hf
  obtain ⟨a, B, c, rfl, rfl, hlen, ⟨x, hx, -⟩, hB⟩ := hf
  have g₁ : GoodWord C.1 (a ++ B) := hw.of_append
  have g₂ : GoodWord C.1 (a ++ B.reverse) := hw'.of_append
  have hend : C.flips (a ++ B) = C.flips (a ++ B.reverse) :=
    flips_eq_of_perm g₁ g₂ ((List.reverse_perm B).symm.append_left a)
  have hblock := galList_block (k := k) hD hZ (C.flips a) hlen (x := x) (fun h => hx h) hB
    g₁.append g₂.append
  rw [galList_append C (a ++ B), galList_append C (a ++ B.reverse), galList_append C a B,
    galList_append C a B.reverse, hend]
  refine stepFilt_mono ?_ (stepFilt_sub_mul (galList_mem_stepFilt _ c) hblock
    (galList_mem_stepFilt C a))
  simp only [List.length_append]
  omega

/-- A chain of flips of a word all of whose prefixes are chambers changes the gallery by an
element with fewer steps. -/
theorem galList_reflTransGen (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C : FullChamber Γ ν}
    {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w)
    (hr : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) w w') :
    galList k C w - galList k C w' ∈ stepFilt k Γ ν (w.length - 2) := by
  induction hr with
  | refl => rw [sub_self]; exact Submodule.zero_mem _
  | @tail w₁ w₂ hr hf ih =>
    have hl : w₁.length = w.length := (reflTransGen_flip_perm hr).length_eq.symm
    have := galList_flip (k := k) hD hZ (hw.reflTransGen hr) hf
    rw [hl] at this
    rw [← sub_add_sub_cancel _ (galList k C w₁)]
    exact Submodule.add_mem _ ih this

end GalleryAlgebra

end Categorification.WeightedKLR
