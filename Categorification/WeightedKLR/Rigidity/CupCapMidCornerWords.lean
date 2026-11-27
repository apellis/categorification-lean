/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndWords
import Categorification.WeightedKLR.Rigidity.CupCapMidSlides
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerWindow

/-!
# Loadings of `λ⁺` with the strands at the maximum in the window before `λ_{j+1}`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap after the red strand `λ_j`.
The loading `midSeq j hj s t` of `λ⁺` is the loading `s` of `λ` with the loading `t` of the
strands at the maximum inserted in the window `[c, c + N)`, `c = midPos j s`, just before the red
strand `λ_{j+1}`. These are the loadings of `midSet`; they determine `s` and `t`
(`midSeq_injective`). Permutations of the window act on `t` (`winPerm_smul_midSeq`), and
`midSeq j hj s t` is red-ordered exactly when `s` and `t` are (`isRedOrdered_midSeq`).

## Main definitions

* `CupCap.midSeq`: the loading with the window at `midPos`.

## Main results

* `CupCap.midSeq_injective`, `CupCap.exists_midSeq_of_mem`: the loadings of `midSet`.
* `CupCap.winPerm_smul_midSeq`: the window permutations act on the window.
* `CupCap.isRedOrdered_midSeq`: red order of the two parts.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (j hj) in
/-- The loading of `λ⁺` with the loading `s` of `λ` and the loading `t` of the strands at the
maximum in the window at `midPos j s`, just before the red strand `λ_{j+1}`. -/
def midSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) :=
  insertSeq (j := j) (hj := hj) s (midPos j s) (midPos_le j s) (Seq.map (cupColour j hj) t)

variable (j ν₀) in
theorem midPos_add_N_le (s : Seq (stendhalWeight ℓ ν)) : midPos j s + N ≤ M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have := midPos_le j s
  omega

theorem midSeq_lbl_lt (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (hc : c.val < midPos j s) :
    (midSeq j hj s t).lbl c =
      oldColour j hj (s.lbl ⟨c.val, lt_of_lt_of_le hc (midPos_le j s)⟩) :=
  insertSeq_lbl_lt s (midPos_le j s) _ ⟨c.val, _⟩ hc rfl

theorem midSeq_lbl_ge (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (hc : midPos j s + N ≤ c.val) :
    (midSeq j hj s t).lbl c = oldColour j hj (s.lbl ⟨c.val - N, by
      have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩) :=
  insertSeq_lbl_ge s (midPos_le j s) _ _ (by simp; omega) (by simp; omega)

theorem midSeq_lbl_win (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (h₁ : midPos j s ≤ c.val) (h₂ : c.val < midPos j s + N) :
    (midSeq j hj s t).lbl c = cupColour j hj (t.lbl ⟨c.val - midPos j s, by omega⟩) := by
  have hb : c.val - midPos j s <
      Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) j hj)) := by
    rw [Multiset.card_map]; omega
  rw [midSeq, insertSeq_lbl_win s _ _ ⟨c.val - midPos j s, hb⟩ (by simp; omega), Seq.map_lbl]
  rfl

theorem midSeq_lbl_winPos (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    (b : Fin N) :
    (midSeq j hj s t).lbl (winPos (midPos_add_N_le j ν₀ s) b) = cupColour j hj (t.lbl b) := by
  rw [midSeq_lbl_win s t _ (by simp) (by simp)]
  congr 2
  exact Fin.ext (by simp)

theorem midSeq_lbl_old (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (a : Fin m) :
    (midSeq j hj s t).lbl
        (Fin.cast (card_plus j hj ν ν₀).symm
          (insertPos _ _ (midPos j s) (midPos_le j s) (.inl a))) =
      oldColour j hj (s.lbl a) :=
  insertSeq_lbl_old s _ _ _ a

section Membership

variable [DecidableEq I]

/-- **The loading `midSeq j hj s t` determines `s` and `t`.** -/
theorem midSeq_injective {s s' : Seq (stendhalWeight ℓ ν)} {t t' : Seq (stendhalWeight 2 ν₀)}
    (h : midSeq j hj s t = midSeq j hj s' t') : s = s' ∧ t = t' := by
  have hs : s = s' := by
    by_contra hne
    refine Finset.disjoint_left.1 (disjoint_insertSet_midPos (j := j) (hj := hj) (ν₀ := ν₀) hne)
      (Finset.mem_image_of_mem _ (Finset.mem_univ (Seq.map (cupColour j hj) t))) ?_
    change midSeq j hj s t ∈ _
    rw [h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  subst hs
  exact ⟨rfl, (Seq.map_bijective (cupColour_injective j hj) _).1 (insertSeq_injective s _ h)⟩

theorem midSeq_mem_midSet (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    midSeq j hj s t ∈ midSet j hj ν ν₀ :=
  Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem exists_midSeq_of_mem {u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))}
    (hu : u ∈ midSet j hj ν ν₀) : ∃ s t, midSeq j hj s t = u := by
  obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 hu
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hs
  refine ⟨s, (Seq.mapEquiv (cupColour_injective j hj) _).symm t, ?_⟩
  rw [midSeq, Seq.map_mapEquiv_symm]

end Membership

/-! ### The window permutations -/

/-- Adjacent transpositions of the strands at the maximum act on the sequences of the mapped
colours as on the sequences. -/
theorem sadj_smul_map_cup (t : Seq (stendhalWeight 2 ν₀)) (q : ℕ) :
    sadj (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) j hj))) q •
        Seq.map (cupColour j hj) t = Seq.map (cupColour j hj) (sadj N q • t) := by
  apply Subtype.ext
  funext c
  change (Seq.map _ t).1 ((sadj _ q).symm c) = cupColour j hj ((sadj N q • t).1 (Fin.cast _ c))
  rw [Seq.smul_apply, ← Perm.inv_def, ← Perm.inv_def, sadj_inv, sadj_inv]
  change cupColour j hj (t.1 (Fin.cast _ (sadj _ q c))) = _
  rw [cast_sadj]

theorem smul_midSeq_win (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    {β : List ℕ} (hβ : ValidWord N β) :
    wordProd M (shiftWord (midPos j s) β) • midSeq j hj s t = midSeq j hj s (wordProd N β • t) := by
  induction β with
  | nil => simp [shiftWord]
  | cons q β ih =>
    obtain ⟨hq, hβ⟩ := validWord_cons.1 hβ
    have ih' := ih hβ
    simp only [shiftWord, List.map_cons] at ih' ⊢
    rw [wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih', midSeq, midSeq,
      smul_insertSeq_new _ _ _ (by rw [Multiset.card_map]; exact hq), sadj_smul_map_cup]

/-- **The permutations of the window act on the loading of the strands at the maximum.** -/
theorem winPerm_smul_midSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    (b : Perm (Fin N)) :
    winPerm (midPos_add_N_le j ν₀ s) b • midSeq j hj s t = midSeq j hj s (b • t) := by
  obtain ⟨β, hβ, rfl⟩ := exists_validWord N b
  rw [← wordProd_shiftWord_window _ hβ, smul_midSeq_win _ _ hβ]

/-! ### Red order -/

theorem inr_of_sumMap_eq_inr {ℓ₁ ℓ₂ : ℕ} {f : Fin ℓ₁ → Fin ℓ₂} {x : I ⊕ Fin ℓ₁}
    {r : Fin ℓ₂} (h : Sum.map id f x = .inr r) : ∃ r₀, x = .inr r₀ ∧ f r₀ = r := by
  rcases x with x | x
  · simp at h
  · exact ⟨x, rfl, by simpa using h⟩

/-- In a red-ordered loading of `λ`, the red strands left of `midPos` are `λ_1, …, λ_j`. -/
theorem red_lt_of_lt_midPos {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) {a : Fin m}
    {r : Fin ℓ} (ha : s.lbl a = .inr r) (hlt : a.val < midPos j s) : r.val < j := by
  by_cases h : j < ℓ
  · obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s h
    have := hs a b r ⟨j, h⟩ (Fin.lt_def.2 (by omega)) ha hlb
    exact this
  · have := r.2; omega

/-- In a red-ordered loading of `λ`, the red strands from `midPos` on are `λ_{j+1}, …, λ_ℓ`. -/
theorem le_red_of_midPos_le {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) {a : Fin m}
    {r : Fin ℓ} (ha : s.lbl a = .inr r) (hle : midPos j s ≤ a.val) : j ≤ r.val := by
  by_cases h : j < ℓ
  · obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s h
    rcases eq_or_lt_of_le hle with he | hlt
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      rw [ha] at hlb
      have := congrArg Fin.val (Sum.inr_injective hlb)
      simp at this
      omega
    · have := hs b a ⟨j, h⟩ r (Fin.lt_def.2 (by omega)) hlb ha
      exact this.le
  · rw [midPos_of_not_lt j s h] at hle
    have := a.2; omega

/-- **`midSeq j hj s t` is red-ordered exactly when `s` and `t` are.** -/
theorem isRedOrdered_midSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    IsRedOrdered (midSeq j hj s t) ↔ IsRedOrdered s ∧ IsRedOrdered t := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hc := midPos_le j s
  constructor
  · intro h
    refine ⟨fun a b r r' hab ha hb => ?_, fun a b r r' hab ha hb => ?_⟩
    · have h1 := midSeq_lbl_old (hj := hj) s t a
      have h2 := midSeq_lbl_old (hj := hj) s t b
      rw [ha] at h1
      rw [hb] at h2
      have hlt := h _ _ _ _ (by
        rw [Fin.lt_def, Fin.val_cast, Fin.val_cast, insertPos_inl_val, insertPos_inl_val]
        rw [Fin.lt_def] at hab
        split_ifs <;> omega) h1 h2
      rw [Fin.lt_def] at hlt ⊢
      by_cases hr : r.val < j <;> by_cases hr' : r'.val < j
      · rwa [oldRed_val_of_lt hr, oldRed_val_of_lt hr'] at hlt
      · rw [oldRed_val_of_lt hr, oldRed_val_of_ge (by omega)] at hlt; omega
      · rw [oldRed_val_of_ge (by omega), oldRed_val_of_lt hr'] at hlt; omega
      · rw [oldRed_val_of_ge (by omega), oldRed_val_of_ge (by omega)] at hlt; omega
    · have h1 := midSeq_lbl_winPos (hj := hj) s t a
      have h2 := midSeq_lbl_winPos (hj := hj) s t b
      rw [ha] at h1
      rw [hb] at h2
      have hlt := h _ _ _ _ ((winPos_lt_winPos _).2 hab) h1 h2
      rw [Fin.lt_def, cupRed_val, cupRed_val] at hlt
      exact Fin.lt_def.2 (by omega)
  · rintro ⟨hs, ht⟩ a b r r' hab ha hb
    rw [Fin.lt_def] at hab
    -- the positions of `a` and `b`: left of the window, in it, or right of it
    rcases lt_or_ge b.val (midPos j s) with hb1 | hb1
    · rw [midSeq_lbl_lt s t b hb1] at hb
      rw [midSeq_lbl_lt s t a (by omega)] at ha
      obtain ⟨r₀, hr₀, rfl⟩ := inr_of_sumMap_eq_inr ha
      obtain ⟨r₀', hr₀', rfl⟩ := inr_of_sumMap_eq_inr hb
      have h1 := red_lt_of_lt_midPos (j := j) hs hr₀ (by simp; omega)
      have h2 := red_lt_of_lt_midPos (j := j) hs hr₀' (by simp; omega)
      have := hs _ _ _ _ (Fin.lt_def.2 (by simp; omega)) hr₀ hr₀'
      rw [Fin.lt_def, oldRed_val_of_lt h1, oldRed_val_of_lt h2]
      exact this
    rcases lt_or_ge b.val (midPos j s + N) with hb2 | hb2
    · rw [midSeq_lbl_win s t b hb1 hb2] at hb
      obtain ⟨q', hq', rfl⟩ := inr_of_sumMap_eq_inr hb
      rcases lt_or_ge a.val (midPos j s) with ha1 | ha1
      · rw [midSeq_lbl_lt s t a ha1] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_sumMap_eq_inr ha
        have h1 := red_lt_of_lt_midPos (j := j) hs hr₀ (by simp; omega)
        rw [Fin.lt_def, oldRed_val_of_lt h1, cupRed_val]
        omega
      · rw [midSeq_lbl_win s t a ha1 (by omega)] at ha
        obtain ⟨q, hq, rfl⟩ := inr_of_sumMap_eq_inr ha
        have := ht _ _ _ _ (Fin.lt_def.2 (by simp; omega)) hq hq'
        rw [Fin.lt_def] at this
        rw [Fin.lt_def, cupRed_val, cupRed_val]
        omega
    · rw [midSeq_lbl_ge s t b hb2] at hb
      obtain ⟨r₀', hr₀', rfl⟩ := inr_of_sumMap_eq_inr hb
      have h2 := le_red_of_midPos_le (j := j) hs hr₀' (by simp; omega)
      rcases lt_or_ge a.val (midPos j s) with ha1 | ha1
      · rw [midSeq_lbl_lt s t a ha1] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_sumMap_eq_inr ha
        have h1 := red_lt_of_lt_midPos (j := j) hs hr₀ (by simp; omega)
        rw [Fin.lt_def, oldRed_val_of_lt h1, oldRed_val_of_ge h2]
        omega
      rcases lt_or_ge a.val (midPos j s + N) with ha2 | ha2
      · rw [midSeq_lbl_win s t a ha1 ha2] at ha
        obtain ⟨q, hq, rfl⟩ := inr_of_sumMap_eq_inr ha
        rw [Fin.lt_def, cupRed_val, oldRed_val_of_ge h2]
        have := q.2
        omega
      · rw [midSeq_lbl_ge s t a ha2] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_sumMap_eq_inr ha
        have h1 := le_red_of_midPos_le (j := j) hs hr₀ (by simp; omega)
        have := hs _ _ _ _ (Fin.lt_def.2 (by simp; omega)) hr₀ hr₀'
        rw [Fin.lt_def] at this
        rw [Fin.lt_def, oldRed_val_of_ge h1, oldRed_val_of_ge h2]
        omega

end Categorification.Stendhal.CupCap
