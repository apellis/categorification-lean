/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GallerySpan.Bridge

/-!
# Crossing two neighbouring strands of an evenly spaced configuration

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Proposition 2.14.

Place the strands at the points `s · π t` for an injective `π : Strand ν → ℕ` and a spacing
`s > |ϑ_e|` for every edge. Such a configuration is generic, and each wall and each diagonal is
positive exactly when its two strands are in the order prescribed by `π`. Exchanging two strands
`u, v` with `π v = π u + 1` is the crossing of neighbouring strands used in the proof of
Proposition 2.14: the segment from the configuration to the exchanged one crosses exactly the
hyperplanes joining `u` and `v`, at the times `(s - ϑ_e) / 2s` (the wall where `v` meets the
ghost of `u`), `(s + ϑ_e) / 2s` (the wall where `u` meets the ghost of `v`) and `1 / 2` (the
diagonal). Under Webster's condition (†) and without loops of weight `0` these times are
distinct, so the segment is simple.

## Main results

* `spacedConfig`, `isGeneric_spacedConfig`, `fullSigns_spacedConfig`.
* `separates_spacedConfig_swap_iff`: the hyperplanes separating the configuration from the
  exchanged one are those joining `u` and `v`.
* `crossTime_spacedConfig_swap`, `simple_spacedConfig_swap`: the crossing times, and the
  segment is simple.
-/

namespace Categorification.WeightedKLR

open Equiv Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- The configuration placing the strand `t` at `s · π t`. -/
def spacedConfig (s : 𝕜) (π : Strand ν → ℕ) : Strand ν → 𝕜 := fun t => s * (π t : 𝕜)

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem spacedConfig_comp (s : 𝕜) (π : Strand ν → ℕ) (σ : Perm (Strand ν)) :
    spacedConfig s π ∘ σ = spacedConfig s (π ∘ σ) := rfl

section Spaced

variable {s : 𝕜} {π : Strand ν → ℕ}

omit [DecidableEq I] in
/-- The difference of two values of `s · π`, for distinct values of `π`, has absolute value at
least `s` and the sign of the difference of the values. -/
theorem lt_sub_spacedConfig (hs0 : 0 < s) {a b : Strand ν} (h : π a < π b) :
    s ≤ spacedConfig s π b - spacedConfig s π a := by
  have h' : (π a : 𝕜) + 1 ≤ (π b : 𝕜) := by exact_mod_cast h
  simp only [spacedConfig]
  nlinarith

omit [DecidableEq I] in
theorem wall_val_spacedConfig_pos_iff (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (hπ : Function.Injective π) (w : Wall Γ ν) :
    0 < w.val (spacedConfig s π) ↔ π w.src < π w.tgt := by
  have hne : π w.src ≠ π w.tgt := fun h => w.2.2.2 (hπ h)
  have hϑ := abs_lt.1 (hs w.edge)
  simp only [Wall.val]
  constructor
  · intro h
    by_contra h'
    have := lt_sub_spacedConfig (π := π) hs0 (lt_of_le_of_ne (not_lt.1 h') (Ne.symm hne))
    linarith
  · intro h
    have := lt_sub_spacedConfig (π := π) hs0 h
    linarith

omit [DecidableEq I] in
theorem wall_val_spacedConfig_ne_zero (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (hπ : Function.Injective π) (w : Wall Γ ν) : w.val (spacedConfig s π) ≠ 0 := by
  have hne : π w.src ≠ π w.tgt := fun h => w.2.2.2 (hπ h)
  have hϑ := abs_lt.1 (hs w.edge)
  simp only [Wall.val]
  rcases lt_or_gt_of_ne hne with h | h
  · have := lt_sub_spacedConfig (π := π) hs0 h
    linarith
  · have := lt_sub_spacedConfig (π := π) hs0 h
    linarith

omit [DecidableEq I] in
theorem diag_val_spacedConfig_pos_iff (hs0 : 0 < s) (d : Diag ν) :
    0 < d.val (spacedConfig s π) ↔ π d.fst < π d.snd := by
  simp only [Diag.val, spacedConfig, sub_pos, mul_lt_mul_iff_right₀ hs0, Nat.cast_lt]

omit [DecidableEq I] in
theorem diag_val_spacedConfig_ne_zero (hs0 : 0 < s) (hπ : Function.Injective π) (d : Diag ν) :
    d.val (spacedConfig s π) ≠ 0 := by
  have hne : π d.fst ≠ π d.snd := fun h => d.fst_ne_snd (hπ h)
  simp only [Diag.val]
  rcases lt_or_gt_of_ne hne with h | h
  · have := lt_sub_spacedConfig (π := π) hs0 h
    linarith
  · have := lt_sub_spacedConfig (π := π) hs0 h
    linarith

omit [DecidableEq I] in
/-- The configuration `s · π` is generic. -/
theorem isGeneric_spacedConfig (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (hπ : Function.Injective π) : IsGeneric Γ (spacedConfig s π) := by
  rintro (w | d)
  · exact wall_val_spacedConfig_ne_zero hs0 hs hπ w
  · exact diag_val_spacedConfig_ne_zero hs0 hπ d

omit [DecidableEq I] in
/-- The full chamber of `s · π`: a hyperplane is positive exactly when its two strands are in
the order of `π`. -/
theorem fullSigns_spacedConfig (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (hπ : Function.Injective π) :
    fullSigns (Γ := Γ) (spacedConfig s π) = fun h => match h with
      | .inl w => decide (π w.src < π w.tgt)
      | .inr d => decide (π d.fst < π d.snd) := by
  funext h
  rcases h with w | d
  · simp [fullSigns, wall_val_spacedConfig_pos_iff hs0 hs hπ w]
  · simp [fullSigns, diag_val_spacedConfig_pos_iff (π := π) hs0 d]

end Spaced

section Swap

variable {ι : Type*} [DecidableEq ι] {π : ι → ℕ}

/-- Exchanging two strands that are neighbours for `π` changes the order of two strands `a, b`
only when `{a, b} = {u, v}`. -/
theorem lt_comp_swap_iff (hπ : Function.Injective π) {u v a b : ι} (huv : π v = π u + 1)
    (hab : ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    π (swap u v a) < π (swap u v b) ↔ π a < π b := by
  have hne : u ≠ v := fun h => by rw [h] at huv; omega
  have key : ∀ x y : ι, x ≠ u → x ≠ v → (π (swap u v y) < π x ↔ π y < π x) ∧
      (π x < π (swap u v y) ↔ π x < π y) := by
    intro x y hxu hxv
    have hxu' : π x ≠ π u := fun h => hxu (hπ h)
    have hxv' : π x ≠ π v := fun h => hxv (hπ h)
    by_cases hyu : y = u
    · subst hyu; rw [swap_apply_left]; omega
    by_cases hyv : y = v
    · subst hyv; rw [swap_apply_right]; omega
    rw [swap_apply_of_ne_of_ne hyu hyv]; exact ⟨Iff.rfl, Iff.rfl⟩
  by_cases hau : a = u
  · subst hau
    have hbv : b ≠ v := fun h => hab (Or.inl ⟨rfl, h⟩)
    by_cases hbu : b = a
    · subst hbu; simp
    rw [swap_apply_left, swap_apply_of_ne_of_ne hbu hbv]
    have hb1 : π b ≠ π a := fun h => hbu (hπ h)
    have hb2 : π b ≠ π v := fun h => hbv (hπ h)
    omega
  by_cases hav : a = v
  · subst hav
    have hbu : b ≠ u := fun h => hab (Or.inr ⟨rfl, h⟩)
    by_cases hbv : b = a
    · subst hbv; simp
    rw [swap_apply_right, swap_apply_of_ne_of_ne hbu hbv]
    have hb1 : π b ≠ π a := fun h => hbv (hπ h)
    have hb2 : π b ≠ π u := fun h => hbu (hπ h)
    omega
  rw [swap_apply_of_ne_of_ne hau hav]
  exact (key a b hau hav).2

theorem lt_comp_swap_iff_of_eq (huv : π v = π u + 1) {a b : ι}
    (hab : (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    π (swap u v a) < π (swap u v b) ↔ ¬ π a < π b := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [swap_apply_left, swap_apply_right]; omega
  · rw [swap_apply_left, swap_apply_right]; omega

end Swap

/-- The hyperplane `h` joins the strands `u` and `v`. -/
def Hyp.JoinsPair (h : Hyp Γ ν) (u v : Strand ν) : Prop :=
  match h with
  | .inl w => (w.src = u ∧ w.tgt = v) ∨ (w.src = v ∧ w.tgt = u)
  | .inr d => (d.fst = u ∧ d.snd = v) ∨ (d.fst = v ∧ d.snd = u)

section Separates

variable {s : 𝕜} {π : Strand ν → ℕ}

/-- The hyperplanes separating `s · π` from the configuration with the neighbouring strands `u`
and `v` exchanged are exactly those joining `u` and `v`. -/
theorem separates_spacedConfig_swap_iff (hs0 : 0 < s) (hs : ∀ e, |Γ.weight e| < s)
    (hπ : Function.Injective π) {u v : Strand ν} (huv : π v = π u + 1) (h : Hyp Γ ν) :
    Separates hypAff (spacedConfig s π) (spacedConfig s π ∘ swap u v) h ↔ h.JoinsPair u v := by
  have hπ' : Function.Injective (π ∘ swap u v) := hπ.comp (swap u v).injective
  rw [spacedConfig_comp]
  rcases h with w | d
  · simp only [Separates, hypAff_apply, Hyp.val_inl, Hyp.JoinsPair,
      wall_val_spacedConfig_pos_iff hs0 hs hπ, wall_val_spacedConfig_pos_iff hs0 hs hπ',
      Function.comp_apply]
    by_cases hj : (w.src = u ∧ w.tgt = v) ∨ (w.src = v ∧ w.tgt = u)
    · simp only [hj, iff_true, lt_comp_swap_iff_of_eq huv hj]; tauto
    · simp only [hj, iff_false, lt_comp_swap_iff hπ huv hj]; tauto
  · simp only [Separates, hypAff_apply, Hyp.val_inr, Hyp.JoinsPair,
      diag_val_spacedConfig_pos_iff (π := π) hs0, diag_val_spacedConfig_pos_iff (π := _) hs0,
      Function.comp_apply]
    by_cases hj : (d.fst = u ∧ d.snd = v) ∨ (d.fst = v ∧ d.snd = u)
    · simp only [hj, iff_true, lt_comp_swap_iff_of_eq huv hj]; tauto
    · simp only [hj, iff_false, lt_comp_swap_iff hπ huv hj]; tauto

/-- The signed weight of a hyperplane joining `u` and `v`: `ϑ_e` for the wall where `v` meets the
ghost of `u`, `-ϑ_e` for the wall where `u` meets the ghost of `v`, and `0` for a diagonal. -/
def Hyp.pairWeight (u : Strand ν) : Hyp Γ ν → 𝕜
  | .inl w => if w.src = u then Γ.weight w.edge else -Γ.weight w.edge
  | .inr _ => 0

/-- The time at which the segment exchanging `u` and `v` crosses a hyperplane joining them. -/
theorem crossTime_spacedConfig_swap (hs0 : 0 < s) {u v : Strand ν} (huv : π v = π u + 1)
    {h : Hyp Γ ν} (hj : h.JoinsPair u v) :
    crossTime hypAff (spacedConfig s π) (spacedConfig s π ∘ swap u v) h =
      (s - h.pairWeight u) / (2 * s) := by
  have hne : u ≠ v := fun e => by rw [e] at huv; omega
  have hc : spacedConfig s π v - spacedConfig s π u = s := by
    simp only [spacedConfig, huv, Nat.cast_add, Nat.cast_one]; ring
  have h2 : (2 : 𝕜) * s ≠ 0 := by positivity
  rcases h with w | d
  · rcases hj with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · simp only [crossTime, hypAff_apply, Hyp.val_inl, Wall.val, Function.comp_apply, h1, h2',
        swap_apply_left, swap_apply_right, Hyp.pairWeight, ↓reduceIte]
      rw [div_eq_div_iff (by linarith) h2]
      rw [show spacedConfig s π v = spacedConfig s π u + s by linarith]
      ring
    · simp only [crossTime, hypAff_apply, Hyp.val_inl, Wall.val, Function.comp_apply, h1, h2',
        swap_apply_left, swap_apply_right, Hyp.pairWeight, hne.symm, ↓reduceIte]
      rw [div_eq_div_iff (by linarith) h2]
      rw [show spacedConfig s π v = spacedConfig s π u + s by linarith]
      ring
  · rcases hj with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · simp only [crossTime, hypAff_apply, Hyp.val_inr, Diag.val, Function.comp_apply, h1, h2',
        swap_apply_left, swap_apply_right, Hyp.pairWeight]
      rw [div_eq_div_iff (by linarith) h2]
      rw [show spacedConfig s π v = spacedConfig s π u + s by linarith]
      ring
    · simp only [crossTime, hypAff_apply, Hyp.val_inr, Diag.val, Function.comp_apply, h1, h2',
        swap_apply_left, swap_apply_right, Hyp.pairWeight]
      rw [div_eq_div_iff (by linarith) h2]
      rw [show spacedConfig s π v = spacedConfig s π u + s by linarith]
      ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Under (†) and without loops of weight `0`, two hyperplanes joining `u` and `v` with the same
signed weight are equal. -/
theorem Hyp.eq_of_pairWeight_eq (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {u v : Strand ν}
    {h g : Hyp Γ ν} (hh : h.JoinsPair u v) (hg : g.JoinsPair u v)
    (he : h.pairWeight u = g.pairWeight u) : h = g := by
  have hne : u ≠ v := by
    rcases h with w | d
    · rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro e <;>
        exact (show w.src ≠ w.tgt from w.2.2.2) (by rw [h1, h2, e])
    · rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro e <;>
        exact (show d.fst ≠ d.snd from d.fst_ne_snd) (by rw [h1, h2, e])
  have wext : ∀ w w' : Wall Γ ν, w.edge = w'.edge → w.src = w'.src → w.tgt = w'.tgt → w = w' :=
    fun w w' a b c => Subtype.ext (Prod.ext a (Prod.ext b c))
  have hsrc : ∀ w : Wall Γ ν, w.src.1 = Γ.head w.edge := fun w => w.2.1
  have htgt : ∀ w : Wall Γ ν, w.tgt.1 = Γ.tail w.edge := fun w => w.2.2.1
  -- a wall joining two strands of one colour is a loop, so its weight is non-zero
  have hloop : ∀ (w : Wall Γ ν) (d : Diag ν), Hyp.JoinsPair (Sum.inl w : Hyp Γ ν) u v →
      Hyp.JoinsPair (Sum.inr d : Hyp Γ ν) u v → Γ.weight w.edge ≠ 0 := by
    intro w d hw hd
    have hcol : u.1 = v.1 := by
      rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact d.2.1
      · rw [← h1, ← h2]; exact d.2.1.symm
    apply hZ
    rw [← hsrc, ← htgt]
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hcol]
    · rw [h1, h2, hcol]
  rcases h with w | d <;> rcases g with w' | d'
  · simp only [Hyp.pairWeight] at he
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · simp only [h1, g1, ↓reduceIte] at he
      have := hD.1 _ _ (by rw [← htgt, ← htgt, h2, g2]) (by rw [← hsrc, ← hsrc, h1, g1]) he
      exact congrArg Sum.inl (wext w w' this (h1.trans g1.symm) (h2.trans g2.symm))
    · simp only [h1, g1, hne.symm, ↓reduceIte] at he
      exact absurd (hD.2 w.edge w'.edge (by rw [← htgt, ← hsrc, h2, g1])
        (by rw [← hsrc, ← htgt, h1, g2]) (by rw [he, neg_neg])) id
    · simp only [h1, g1, hne.symm, ↓reduceIte] at he
      exact absurd (hD.2 w.edge w'.edge (by rw [← htgt, ← hsrc, h2, g1])
        (by rw [← hsrc, ← htgt, h1, g2]) he.symm) id
    · simp only [h1, g1, hne.symm, ↓reduceIte] at he
      have := hD.1 _ _ (by rw [← htgt, ← htgt, h2, g2]) (by rw [← hsrc, ← hsrc, h1, g1])
        (neg_inj.1 he)
      exact congrArg Sum.inl (wext w w' this (h1.trans g1.symm) (h2.trans g2.symm))
  · simp only [Hyp.pairWeight] at he
    have := hloop w d' hh hg
    split_ifs at he <;> [exact absurd he this; exact absurd (neg_eq_zero.1 he) this]
  · simp only [Hyp.pairWeight] at he
    have := hloop w' d hg hh
    split_ifs at he <;> [exact absurd he.symm this;
      exact absurd (neg_eq_zero.1 he.symm) this]
  · have dext : ∀ a b : Diag ν, a.fst = b.fst → a.snd = b.snd → a = b :=
      fun a b x y => Subtype.ext (Prod.ext x y)
    have hr : ∀ a : Diag ν, a.fst.2.val < a.snd.2.val := fun a => a.2.2
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact congrArg Sum.inr (dext d d' (h1.trans g1.symm) (h2.trans g2.symm))
    · have := hr d; have := hr d'; rw [h1, h2] at *; rw [g1, g2] at *; omega
    · have := hr d; have := hr d'; rw [h1, h2] at *; rw [g1, g2] at *; omega
    · exact congrArg Sum.inr (dext d d' (h1.trans g1.symm) (h2.trans g2.symm))

variable (Γ) in
/-- **The crossing segment is simple.** Under Webster's condition (†) and without loops of
weight `0`, the segment exchanging two neighbouring strands of an evenly spaced configuration
has generic endpoints and crosses distinct hyperplanes at distinct times. -/
theorem simple_spacedConfig_swap (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hs0 : 0 < s)
    (hs : ∀ e, |Γ.weight e| < s) (hπ : Function.Injective π) {u v : Strand ν}
    (huv : π v = π u + 1) :
    Simple (hypAff (Γ := Γ)) (spacedConfig s π) (spacedConfig s π ∘ swap u v) := by
  refine ⟨isGeneric_spacedConfig hs0 hs hπ, ?_, fun h g hh hg hhg he => hhg ?_⟩
  · rw [spacedConfig_comp]
    exact isGeneric_spacedConfig hs0 hs (hπ.comp (swap u v).injective)
  have hh' := (separates_spacedConfig_swap_iff hs0 hs hπ huv h).1 hh
  have hg' := (separates_spacedConfig_swap_iff hs0 hs hπ huv g).1 hg
  rw [crossTime_spacedConfig_swap hs0 huv hh', crossTime_spacedConfig_swap hs0 huv hg',
    div_left_inj' (by positivity), sub_right_inj] at he
  exact Hyp.eq_of_pairWeight_eq hD hZ hh' hg' he

end Separates

end Categorification.WeightedKLR
