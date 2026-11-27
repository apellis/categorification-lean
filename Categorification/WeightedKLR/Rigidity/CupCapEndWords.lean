/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndFactor
import Categorification.WeightedKLR.Rigidity.CupCapTopBasis

/-!
# Loadings of `λ⁺` split into the strands of `λ` and the strands at the maximum

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. The loading
`endSeq s t` of `λ⁺` puts a loading `s` of `λ` on the first `m` strands and a loading `t` of the
strands at the maximum on the last `N`. Permutations of the two blocks act on the two parts
(`blockPerm_smul_endSeq`), and `endSeq s t` is red-ordered exactly when `s` and `t` are
(`isRedOrdered_endSeq`).

## Main results

* `smul_endSeq_left`, `smul_endSeq_right`, `blockPerm_smul_endSeq`: the two blocks act on the two
  parts.
* `isRedOrdered_endSeq`: red order of the two parts.
* `isRedOrdered_wordProd_smul`: a word exchanging no two red strands keeps the red order.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv

variable {I : Type*} {ℓ : ℕ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

theorem card_plus_end : M = m + N := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)

theorem m_add_N_end : m + N = M := (card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)).symm

/-- The loading of `λ⁺` with the loading `s` of `λ` on the first `m` strands and the loading `t`
of the strands at the maximum on the last `N`. -/
def endSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) :=
  insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl (Seq.map (cupColour ℓ le_rfl) t)

theorem endSeq_lbl_lt (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (hc : c.val < m) : (endSeq s t).lbl c = oldColour ℓ le_rfl (s.lbl ⟨c.val, hc⟩) :=
  insertSeq_lbl_lt s le_rfl _ ⟨c.val, hc⟩ hc rfl

theorem endSeq_lbl_ge (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (hc : m ≤ c.val) :
    (endSeq s t).lbl c = cupColour ℓ le_rfl (t.lbl ⟨c.val - m, by
      have := card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩) := by
  have hb : c.val - m <
      Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) ℓ le_rfl)) := by
    have := card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    rw [Multiset.card_map]; omega
  rw [endSeq, insertSeq_lbl_win s le_rfl _ ⟨c.val - m, hb⟩ (by simp; omega), Seq.map_lbl]
  rfl

theorem endSeq_injective {s s' : Seq (stendhalWeight ℓ ν)} {t t' : Seq (stendhalWeight 2 ν₀)}
    (h : endSeq s t = endSeq s' t') : s = s' ∧ t = t' := by
  have hM := card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  constructor
  · apply Subtype.ext; funext a
    have h1 := endSeq_lbl_lt s t ⟨a.val, by omega⟩ a.2
    have h2 := endSeq_lbl_lt s' t' ⟨a.val, by omega⟩ a.2
    rw [h, h2] at h1
    exact (oldColour_injective ℓ le_rfl h1).symm
  · apply Subtype.ext; funext b
    have h1 := endSeq_lbl_ge s t ⟨m + b.val, by omega⟩ (by simp)
    have h2 := endSeq_lbl_ge s' t' ⟨m + b.val, by omega⟩ (by simp)
    rw [h, h2] at h1
    have := (cupColour_injective (I := I) ℓ le_rfl h1).symm
    simpa using this

theorem endSeq_mem_endSet [DecidableEq I] (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (stendhalWeight 2 ν₀)) : endSeq s t ∈ endSet ν ν₀ :=
  insertSeq_mem_endSet s _

theorem exists_endSeq_of_mem [DecidableEq I] {u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))}
    (hu : u ∈ endSet ν ν₀) : ∃ s t, endSeq s t = u := by
  obtain ⟨s, t, rfl⟩ := mem_endSet.1 hu
  refine ⟨s, (Seq.mapEquiv (cupColour_injective ℓ le_rfl) _).symm t, ?_⟩
  rw [endSeq, Seq.map_mapEquiv_symm]

/-- Adjacent transpositions of the strands at the maximum act on the sequences of the mapped
colours as on the sequences. -/
theorem sadj_smul_map (t : Seq (stendhalWeight 2 ν₀)) (q : ℕ) :
    sadj (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) ℓ le_rfl))) q •
        Seq.map (cupColour ℓ le_rfl) t = Seq.map (cupColour ℓ le_rfl) (sadj N q • t) := by
  apply Subtype.ext
  funext c
  change (Seq.map _ t).1 ((sadj _ q).symm c) = cupColour ℓ le_rfl ((sadj N q • t).1 (Fin.cast _ c))
  rw [Seq.smul_apply, ← Perm.inv_def, ← Perm.inv_def, sadj_inv, sadj_inv]
  change cupColour ℓ le_rfl (t.1 (Fin.cast _ (sadj _ q c))) = _
  rw [cast_sadj]

theorem smul_endSeq_left (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    {α : List ℕ} (hα : ValidWord m α) :
    wordProd M α • endSeq s t = endSeq (wordProd m α • s) t := by
  induction α with
  | nil => simp
  | cons p α ih =>
    obtain ⟨hp, hα⟩ := validWord_cons.1 hα
    have hc : crossPos m (Multiset.card ((stendhalWeight 2 ν₀).map
        (cupColour (I := I) ℓ le_rfl))) p = p := by
      rw [crossPos, ite_eq_left (by omega)]
    have h := smul_insertSeq_old (j := ℓ) (hj := le_rfl) (wordProd m α • s) le_rfl
      (Seq.map (cupColour ℓ le_rfl) t) (Or.inl hp)
    rw [hc] at h
    rw [wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih hα]
    exact h

theorem smul_endSeq_right (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    {β : List ℕ} (hβ : ValidWord N β) :
    wordProd M (shiftWord m β) • endSeq s t = endSeq s (wordProd N β • t) := by
  induction β with
  | nil => simp [shiftWord]
  | cons q β ih =>
    obtain ⟨hq, hβ⟩ := validWord_cons.1 hβ
    have ih' := ih hβ
    simp only [shiftWord, List.map_cons] at ih' ⊢
    rw [wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih', endSeq, endSeq,
      smul_insertSeq_new _ le_rfl _ (by rw [Multiset.card_map]; exact hq), sadj_smul_map]

/-- **Permutations of the two blocks act on the two parts.** -/
theorem blockPerm_smul_endSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    (a : Perm (Fin m)) (b : Perm (Fin N)) :
    blockPerm (m_add_N_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)) a b • endSeq s t =
      endSeq (a • s) (b • t) := by
  obtain ⟨α, hα, rfl⟩ := exists_validWord m a
  obtain ⟨β, hβ, rfl⟩ := exists_validWord N b
  rw [← wordProd_append_shiftWord _ hα hβ, wordProd_append, mul_smul,
    smul_endSeq_right _ _ hβ, smul_endSeq_left _ _ hα]

private theorem inr_of_map_eq_inr {ℓ₁ : ℕ} {f : Fin ℓ₁ → Fin (ℓ + 2)} {x : I ⊕ Fin ℓ₁}
    {r : Fin (ℓ + 2)} (h : Sum.map id f x = .inr r) : ∃ r₀, x = .inr r₀ ∧ f r₀ = r := by
  rcases x with x | x
  · simp at h
  · exact ⟨x, rfl, by simpa using h⟩

theorem oldRed_val (r : Fin ℓ) : (oldRed ℓ le_rfl r).val = r.val :=
  oldRed_val_of_lt (j := ℓ) (hj := le_rfl) r.2

/-- **`endSeq s t` is red-ordered exactly when `s` and `t` are.** -/
theorem isRedOrdered_endSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    IsRedOrdered (endSeq s t) ↔ IsRedOrdered s ∧ IsRedOrdered t := by
  have hM := card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  constructor
  · intro h
    refine ⟨fun a b r r' hab ha hb => ?_, fun a b r r' hab ha hb => ?_⟩
    · have h1 := endSeq_lbl_lt s t ⟨a.val, by omega⟩ a.2
      have h2 := endSeq_lbl_lt s t ⟨b.val, by omega⟩ b.2
      rw [Fin.eta, ha] at h1
      rw [Fin.eta, hb] at h2
      have := h _ _ _ _ (show (⟨a.val, by omega⟩ : Fin M) < ⟨b.val, by omega⟩ from hab) h1 h2
      rw [Fin.lt_def, oldRed_val, oldRed_val] at this
      exact this
    · have h1 := endSeq_lbl_ge s t ⟨m + a.val, by omega⟩ (by simp)
      have h2 := endSeq_lbl_ge s t ⟨m + b.val, by omega⟩ (by simp)
      simp only [Nat.add_sub_cancel_left, Fin.eta, ha, hb] at h1 h2
      have := h _ _ _ _ (show (⟨m + a.val, by omega⟩ : Fin M) < ⟨m + b.val, by
        omega⟩ by rw [Fin.lt_def]; simp; exact hab) h1 h2
      rw [Fin.lt_def, cupRed_val, cupRed_val] at this
      exact Fin.lt_def.2 (by omega)
  · rintro ⟨hs, ht⟩ a b r r' hab ha hb
    rw [Fin.lt_def] at hab
    by_cases hb' : b.val < m
    · rw [endSeq_lbl_lt s t b hb'] at hb
      rw [endSeq_lbl_lt s t a (by omega)] at ha
      obtain ⟨r₀, hr₀, rfl⟩ := inr_of_map_eq_inr ha
      obtain ⟨r₀', hr₀', rfl⟩ := inr_of_map_eq_inr hb
      have := hs _ _ _ _ (show (⟨a.val, by omega⟩ : Fin m) < ⟨b.val, hb'⟩ from hab) hr₀ hr₀'
      rw [Fin.lt_def, oldRed_val, oldRed_val]
      exact this
    · rw [endSeq_lbl_ge s t b (by omega)] at hb
      obtain ⟨r₀', hr₀', rfl⟩ := inr_of_map_eq_inr hb
      by_cases ha' : a.val < m
      · rw [endSeq_lbl_lt s t a ha'] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_map_eq_inr ha
        rw [Fin.lt_def, oldRed_val, cupRed_val]
        omega
      · rw [endSeq_lbl_ge s t a (by omega)] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_map_eq_inr ha
        have := ht _ _ _ _ (show (⟨a.val - m, by omega⟩ : Fin N) < ⟨b.val - m, by omega⟩ by
          rw [Fin.lt_def]; simp; omega) hr₀ hr₀'
        rw [Fin.lt_def, cupRed_val, cupRed_val]
        rw [Fin.lt_def] at this
        omega

/-- A word exchanging no two red strands keeps a red-ordered loading red-ordered. -/
theorem isRedOrdered_wordProd_smul {I : Type} {ℓ₁ : ℕ} {ν₁ : Multiset I}
    {s : Seq (stendhalWeight ℓ₁ ν₁)}
    (hs : IsRedOrdered s) {γ : List ℕ} (hv : ValidWord (Multiset.card (stendhalWeight ℓ₁ ν₁)) γ)
    (hr : NoRedCross γ s) :
    IsRedOrdered (wordProd (Multiset.card (stendhalWeight ℓ₁ ν₁)) γ • s) := by
  induction γ with
  | nil => simpa using hs
  | cons j γ ih =>
    obtain ⟨hj, hv⟩ := validWord_cons.mp hv
    rw [wordProd_cons, mul_smul]
    exact isRedOrdered_sadj (ih hv hr.1) hj (hr.2 hj)

end Categorification.Stendhal.CupCap
