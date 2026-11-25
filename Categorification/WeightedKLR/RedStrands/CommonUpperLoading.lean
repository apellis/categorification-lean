/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationCancel
import Categorification.WeightedKLR.RedStrands.StandardBlocks
import Categorification.WeightedKLR.RedStrands.StandardModule
import Categorification.TypeA.Inversions

/-!
# Diagrams between two loadings pass through a common upper loading

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition 6.10):
at the loading of Figure 5, the standard module agrees with the partial standard of
Lemma 6.8. The comparison rests on a fact about Webster's order (§5.1): for two loadings `s`,
`t` with the same red order, every diagram `e(t) x e(s)` is a sum of diagrams that factor
through loadings `v` lying above both `s` and `t`.

A reduced word for a wiring `w` from `s` to `t` can be chosen so that all crossings in which a
black strand moves left (past a red strand or past another black strand) come first, at the
bottom, and the remaining crossings, in which black strands only move right past red strands,
come last. Moving black strands left does not lower Webster's order, and moving them right
does not raise it; so the intermediate loading lies above `s` and above `t`.

## Main results

* `Stendhal.stendhalLE_sadj_of_black`: moving a black strand one step left does not lower
  the order.
* `Stendhal.stendhalLE_of_no_blackDescent`: a wiring with no descent ending at a black strand
  does not raise the order.
* `Stendhal.exists_reduced_suffix_commonUpper`: the reduced word through a common upper
  loading.
* `Stendhal.e_mul_mul_e_mem_commonUpperSpan`: `e(t) x e(s)` lies in the span of diagrams
  through loading idempotents above `s` and `t`.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- Moving a black strand one position to the left does not lower Webster's order. -/
theorem stendhalLE_sadj_of_black (s : Seq μ) {j : ℕ} (hj : j + 1 < m) {i : I}
    (hi : s.lbl ⟨j + 1, hj⟩ = .inl i) : StendhalLE s (sadj m j • s) := by
  intro r c
  rw [blackCount_sadj]
  refine Finset.card_le_card fun a ha => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  refine ⟨ha.1, fun d hd => ?_⟩
  have had := ha.2 d hd
  have hd1 : d.val ≠ j + 1 := fun e => by
    rw [lbl_eq_of_val s (b := ⟨j + 1, hj⟩) e, hi] at hd
    cases hd
  rw [Fin.lt_def] at had ⊢
  rw [sadj_val_of_lt hj, sadj_val_of_lt hj]
  rcases swapNat_cases j a with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ <;>
    rcases swapNat_cases j d with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩ | ⟨h₄, h₅, h₆⟩ <;> omega

omit [DecidableEq I] in
private theorem lbl_perm_smul' (w : Perm (Fin m)) (s : Seq μ) (a : Fin m) :
    (w • s).lbl a = s.lbl (w⁻¹ a) := rfl

theorem blackCount_eq_card_lt_redPos (s : Seq μ) (r : Fin ℓ) (i : I) :
    blackCount s r i =
      (Finset.univ.filter fun a => s.lbl a = .inl i ∧ a < redPos s r).card := by
  unfold blackCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
  intro _
  exact ⟨fun h => h _ (lbl_redPos s r), fun h b hb => eq_redPos hb ▸ h⟩

/-- If a wiring raises the black count at a red strand, some strand to the right of that red
strand ends to its left. -/
private theorem exists_leftgoing_strand (s : Seq μ) (w : Perm (Fin m)) (r : Fin ℓ) (i : I)
    (h : blackCount s r i < blackCount (w • s) r i) :
    ∃ b, redPos s r < b ∧ w b < w (redPos s r) := by
  classical
  have hrw : redPos (w • s) r = w (redPos s r) :=
    (eq_redPos (s := w • s) (by simp [lbl_redPos])).symm
  rw [blackCount_eq_card_lt_redPos, blackCount_eq_card_lt_redPos, hrw] at h
  let T := Finset.univ.filter fun b : Fin m => s.lbl b = .inl i ∧ w b < w (redPos s r)
  have hT : T.card = (Finset.univ.filter fun a => (w • s).lbl a = .inl i ∧
      a < w (redPos s r)).card := by
    refine Finset.card_bij (fun b _ => w b) ?_ (fun _ _ _ _ he => w.injective he) ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [lbl_perm_smul'] using hb'⟩
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      exact ⟨w⁻¹ a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [lbl_perm_smul'] using ha'⟩, by simp⟩
  rw [← hT] at h
  have hnot : ¬ T ⊆ (Finset.univ.filter fun a => s.lbl a = .inl i ∧ a < redPos s r) :=
    fun hsub => (Nat.not_le_of_lt h) (Finset.card_le_card hsub)
  obtain ⟨b, hb, hb'⟩ := Finset.not_subset.1 hnot
  have hbT := (Finset.mem_filter.mp hb).2
  have hn : ¬ b < redPos s r := fun hlt => hb' (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hbT.1, hlt⟩)
  have hn' : redPos s r ≠ b := fun he => by
    rw [← he, lbl_redPos] at hbT
    cases hbT.1
  exact ⟨b, lt_of_le_of_ne (le_of_not_gt hn) hn', hbT.2⟩

omit [DecidableEq I] in
/-- If a wiring keeps the order of the red strands and some strand right of a red strand ends
left of it, then the wiring has a descent `j` whose strand at `j + 1` is black. -/
theorem exists_blackDescent_of_leftgoing (s : Seq μ) (w : Perm (Fin m))
    (hred : ∀ (a b : Fin m) (r r' : Fin ℓ), s.lbl a = .inr r → s.lbl b = .inr r' → a < b →
      w a < w b)
    {a : Fin m} {r : Fin ℓ} (ha : s.lbl a = .inr r) (b : Fin m) (hab : a < b)
    (hw : w b < w a) :
    ∃ (j : ℕ) (hj : j + 1 < m), w ⟨j + 1, hj⟩ < w ⟨j, by omega⟩ ∧
      (s.lbl ⟨j + 1, hj⟩).isLeft := by
  suffices H : ∀ n (b : Fin m), b.val = n → a < b → w b < w a →
      ∃ (j : ℕ) (hj : j + 1 < m), w ⟨j + 1, hj⟩ < w ⟨j, by omega⟩ ∧
        (s.lbl ⟨j + 1, hj⟩).isLeft from H b.val b rfl hab hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨_ | j, hj⟩ hbn hab hw
  · exact absurd (Fin.lt_def.1 hab) (Nat.not_lt_zero _)
  have hb : (s.lbl ⟨j + 1, hj⟩).isLeft := by
    cases hl : s.lbl ⟨j + 1, hj⟩ with
    | inl _ => rfl
    | inr r' => exact absurd (hred a _ r r' ha hl hab) (lt_asymm hw)
  by_cases hdesc : w ⟨j + 1, hj⟩ < w ⟨j, by omega⟩
  · exact ⟨j, hj, hdesc, hb⟩
  have hac : a < ⟨j, by omega⟩ := by
    by_contra hne
    have he : (⟨j, by omega⟩ : Fin m) = a := by
      rw [Fin.lt_def] at hab hne
      exact Fin.ext (by simp only at hab hne ⊢; omega)
    exact hdesc (by rw [he]; exact hw)
  have hcw : w ⟨j, by omega⟩ < w a := lt_of_le_of_lt (le_of_not_gt hdesc) hw
  subst hbn
  exact ih j (Nat.lt_succ_self j) ⟨j, by omega⟩ rfl hac hcw

/-- A wiring that keeps the red order and has no descent ending at a black strand does not
raise Webster's order: no black strand passes a red strand from right to left. -/
theorem stendhalLE_of_no_blackDescent (s : Seq μ) (w : Perm (Fin m))
    (hred : redWord (w • s) = redWord s)
    (hno : ∀ (j : ℕ) (hj : j + 1 < m), w ⟨j + 1, hj⟩ < w ⟨j, by omega⟩ →
      ¬ (s.lbl ⟨j + 1, hj⟩).isLeft) :
    StendhalLE (w • s) s := by
  have h := (redWord_smul_eq_iff s w 1).1 (by rw [one_smul]; exact hred)
  have hred' : ∀ (a b : Fin m) (r r' : Fin ℓ), s.lbl a = .inr r → s.lbl b = .inr r' →
      a < b → w a < w b := fun a b r r' ha hb hab =>
    (h a b r r' ha hb).2 (by simpa using hab)
  intro r i
  by_contra hlt
  obtain ⟨b, hab, hw⟩ := exists_leftgoing_strand s w r i (lt_of_not_ge hlt)
  obtain ⟨j, hj, hd, hb⟩ := exists_blackDescent_of_leftgoing s w hred' (lbl_redPos s r) b hab hw
  exact hno j hj hd hb

omit [DecidableEq I] in
private theorem reduced_append_of_descent' {w : Perm (Fin m)} {j : ℕ}
    (hj : j + 1 < m) {ρ : List ℕ} (hρ : IsReduced m ρ)
    (hw : wordProd m ρ = w * sadj m j)
    (hd : length m (w * sadj m j) + 1 = length m w) :
    IsReduced m (ρ ++ [j]) ∧ wordProd m (ρ ++ [j]) = w := by
  have hp : wordProd m (ρ ++ [j]) = w := by
    rw [wordProd_append, wordProd_singleton, hw, mul_assoc, TypeA.sadj_mul_self, mul_one]
  refine ⟨⟨validWord_append.2 ⟨hρ.1, validWord_cons.2 ⟨hj, validWord_nil m⟩⟩, ?_⟩, hp⟩
  rw [List.length_append, List.length_singleton, hρ.2, hw, hp, hd]

/-- **A reduced word through a common upper loading.** For a wiring `w` from `s` that keeps
the red order, there is a reduced word `u ++ v` for `w` whose lower part `v` leads from `s` to
a loading of the same red order lying above both `s` and `w • s` in Webster's order. -/
theorem exists_reduced_suffix_commonUpper (s : Seq μ) (w : Perm (Fin m))
    (hred : redWord (w • s) = redWord s) :
    ∃ u v : List ℕ, IsReduced m (u ++ v) ∧ wordProd m (u ++ v) = w ∧
      StendhalLE s (wordProd m v • s) ∧ StendhalLE (w • s) (wordProd m v • s) ∧
      redWord (wordProd m v • s) = redWord s := by
  suffices H : ∀ n (s : Seq μ) (w : Perm (Fin m)), length m w = n →
      redWord (w • s) = redWord s →
      ∃ u v : List ℕ, IsReduced m (u ++ v) ∧ wordProd m (u ++ v) = w ∧
        StendhalLE s (wordProd m v • s) ∧ StendhalLE (w • s) (wordProd m v • s) ∧
        redWord (wordProd m v • s) = redWord s from H _ s w rfl hred
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s w hn hred
  by_cases hd : ∃ (j : ℕ) (hj : j + 1 < m), w ⟨j + 1, hj⟩ < w ⟨j, by omega⟩ ∧
      (s.lbl ⟨j + 1, hj⟩).isLeft
  · obtain ⟨j, hj, hdesc, hb⟩ := hd
    obtain ⟨i, hi⟩ : ∃ i, s.lbl ⟨j + 1, hj⟩ = .inl i := Sum.isLeft_iff.1 hb
    have hlen := length_mul_sadj_of_gt hj hdesc
    have hs' : redWord (sadj m j • s) = redWord s :=
      redWord_sadj_smul s hj fun h => by rw [hi] at h; exact absurd h.2 (by simp)
    have hws : (w * sadj m j) • (sadj m j • s) = w • s := by
      rw [mul_smul, sadj_smul_smul]
    obtain ⟨u, v, huv, hp, hle, hle', hrv⟩ :=
      ih _ (by omega) (sadj m j • s) (w * sadj m j) rfl (by rw [hws, hred, hs'])
    have hr := reduced_append_of_descent' hj huv hp hlen
    have hv : wordProd m (v ++ [j]) • s = wordProd m v • (sadj m j • s) := by
      rw [wordProd_append, wordProd_singleton, mul_smul]
    refine ⟨u, v ++ [j], by simpa only [List.append_assoc] using hr.1,
      by simpa only [List.append_assoc] using hr.2, ?_, ?_, ?_⟩
    · rw [hv]
      exact fun r c => (stendhalLE_sadj_of_black s hj hi r c).trans (hle r c)
    · rw [hv, ← hws]
      exact hle'
    · rw [hv, hrv, hs']
  · obtain ⟨ρ, hρ, hp⟩ := exists_reduced m w
    refine ⟨ρ, [], by simpa only [List.append_nil] using hρ,
      by simpa only [List.append_nil] using hp, ?_, ?_, ?_⟩
    · simp only [wordProd_nil, one_smul]
      exact fun r c => le_rfl
    · simp only [wordProd_nil, one_smul]
      exact stendhalLE_of_no_blackDescent s w hred fun j hj hdj hbl => hd ⟨j, hj, hdj, hbl⟩
    · simp only [wordProd_nil, one_smul]

section Algebra

variable {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ

/-- The span of the diagrams through loading idempotents `e(v)` of the red order of `s` with
`v` above both `s` and `t` in Webster's order. -/
noncomputable def commonUpperSpan (s t : Seq μ) : Submodule k R :=
  Submodule.span k {x | ∃ (v : Seq μ) (a b : R), StendhalLE s v ∧ StendhalLE t v ∧
    redWord v = redWord s ∧ x = a * e v * b}

/-- **Diagrams between two loadings of one red order factor through a common upper loading.**
For loadings `s`, `t` with the same red order, `e(t) x e(s)` is a sum of diagrams
`a e(v) b` with `v` above `s` and `t` in Webster's order (arXiv:1309.3796v2, §5.1). -/
theorem e_mul_mul_e_mem_commonUpperSpan (s t : Seq μ) (hst : redWord t = redWord s) (x : R) :
    e t * x * e s ∈ commonUpperSpan Q Λ s t := by
  classical
  have hw (w : Perm (Fin m)) :
      ∃ ρ : List ℕ, (IsReduced m ρ ∧ wordProd m ρ = w) ∧
        (w • s = t → ∃ u v, ρ = u ++ v ∧ StendhalLE s (wordProd m v • s) ∧
          StendhalLE t (wordProd m v • s) ∧ redWord (wordProd m v • s) = redWord s) := by
    by_cases h : w • s = t
    · obtain ⟨u, v, huv, hp, hle, hle', hrv⟩ :=
        exists_reduced_suffix_commonUpper s w (h.symm ▸ hst)
      exact ⟨u ++ v, ⟨huv, hp⟩, fun _ => ⟨u, v, rfl, hle, h ▸ hle', hrv⟩⟩
    · obtain ⟨ρ, hρ, hp⟩ := exists_reduced m w
      exact ⟨ρ, ⟨hρ, hp⟩, fun he => False.elim (h he)⟩
  let ρ := fun w => (hw w).choose
  have hρ w : IsReduced m (ρ w) ∧ wordProd m (ρ w) = w := (hw w).choose_spec.1
  let f : R →ₗ[k] R := LinearMap.mulLeft k (e t) ∘ₗ LinearMap.mulRight k (e s)
  have hmem : x ∈ Submodule.span k (Set.range (KLRAlgebra.stdElt (Q := stendhalQ Q Λ)
      (ν := μ) ρ)) := by
    rw [KLRAlgebra.span_stdElt ρ hρ]
    exact Submodule.mem_top
  have hbound : Submodule.span k (Set.range (KLRAlgebra.stdElt (Q := stendhalQ Q Λ)
      (ν := μ) ρ)) ≤ Submodule.comap f (commonUpperSpan Q Λ s t) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨j, w, p⟩, rfl⟩
    let g : R := ψw (ρ w) * pol (MvPolynomial.monomial p 1) * e j
    change e t * (g * e s) ∈ commonUpperSpan Q Λ s t
    have hgR : g * e s = if j = s then g else 0 := by
      dsimp only [g]
      rw [mul_assoc, e_mul_e]
      split_ifs <;> simp
    by_cases hj : j = s
    · subst j
      rw [hgR, ite_eq_left rfl]
      have hgL : e (w • s) * g = g := by
        have h : e (wordProd m (ρ w) • s) * g = g := BraidedStendhalAlgebra.e_mul_std (Q := Q) (Λ := Λ) _ _ _
        rwa [(hρ w).2] at h
      by_cases hws : w • s = t
      · have hgt : e t * g = g := by rwa [hws] at hgL
        rw [hgt]
        obtain ⟨u, v, huv, hle, hle', hrv⟩ := (hw w).choose_spec.2 hws
        let c : Seq μ := wordProd m v • s
        let z : R := ψw v * pol (MvPolynomial.monomial p 1) * e s
        have hcut : e c * z = z := BraidedStendhalAlgebra.e_mul_std (Q := Q) (Λ := Λ) _ _ _
        have hfactor : g = ψw u * e c * z := by
          dsimp [g]
          rw [mul_assoc (ψw u), hcut, show ρ w = u ++ v from huv, ψw_append]
          simp [z, mul_assoc]
        rw [hfactor]
        exact Submodule.subset_span ⟨c, ψw u, z, hle, hle', hrv, rfl⟩
      · rw [← hgL, ← mul_assoc, e_mul_e, ite_eq_right (Ne.symm hws), zero_mul]
        exact zero_mem _
    · rw [hgR, ite_eq_right hj, mul_zero]
      exact zero_mem _
  have hx := hbound hmem
  change e t * (x * e s) ∈ commonUpperSpan Q Λ s t at hx
  rwa [← mul_assoc] at hx

end Algebra

end Categorification.Stendhal
