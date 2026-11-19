/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalCrossing

/-!
# Splitting a red strand: loadings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. The red strand `λ_c` of a Stendhal loading with red strands
`λ_1, …, λ_ℓ` is replaced by two adjacent red strands, labelled `c` and `c + 1` among
`ℓ + 1` red strands. This file sets up the combinatorics of this replacement.

## Main definitions

* `splitColor c` : the labels of the old strands among the new labels.
* `redPos c s` : the position of the red strand `λ_c` in `s`.
* `splitLoading c s` : the loading with the red strand `λ_c` replaced by two adjacent ones.
* `splitPos c s a` : the position in `splitLoading c s` of the old strand at `a`.

## Main results

* `stendhalWeight_split` : the new strands are the images of the old ones and one red strand.
* `splitLoading_lbl_splitPos`, `splitLoading_lbl_newPos` : the labels of the new loading.
* `splitLoading_sadj_*` : the effect of an adjacent transposition of the old loading.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ} (c : Fin ℓ) (ν : Multiset I)

/-- The label of an old strand among the labels with one more red strand: the red strands
`λ_r`, `r ≤ c`, keep their index and the others move up by one. The new red strand is
`c + 1`. -/
def splitColor : I ⊕ Fin ℓ → I ⊕ Fin (ℓ + 1)
  | .inl i => .inl i
  | .inr r => .inr (c.succ.succAbove r)

@[simp] theorem splitColor_inl (i : I) : splitColor c (.inl i : I ⊕ Fin ℓ) = .inl i := rfl
@[simp] theorem splitColor_inr (r : Fin ℓ) :
    splitColor (I := I) c (.inr r) = .inr (c.succ.succAbove r) := rfl

theorem splitColor_injective : Function.Injective (splitColor (I := I) c) := by
  rintro (i | r) (i' | r') h <;> simp_all [splitColor]

theorem splitColor_isLeft (x : I ⊕ Fin ℓ) : (splitColor c x).isLeft = x.isLeft := by
  cases x <;> rfl

theorem splitColor_isRight (x : I ⊕ Fin ℓ) : (splitColor c x).isRight = x.isRight := by
  cases x <;> rfl

theorem succAbove_self : c.succ.succAbove c = c.castSucc :=
  Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ

theorem splitColor_ne_new (x : I ⊕ Fin ℓ) : splitColor c x ≠ .inr c.succ := by
  rcases x with i | r
  · simp
  · simp [Fin.succAbove_ne c.succ r]

theorem stendhalWeight_split :
    (stendhalWeight ℓ ν).map (splitColor c) + {.inr c.succ} = stendhalWeight (ℓ + 1) ν := by
  have hu : (Finset.univ : Finset (Fin (ℓ + 1))).val =
      c.succ ::ₘ (Finset.univ.map (Fin.succAboveEmb c.succ)).val := by
    rw [Fin.univ_succAbove ℓ c.succ]; rfl
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_map, hu, Multiset.map_cons,
    Finset.map_val]
  rw [show splitColor c ∘ Sum.inl = (Sum.inl : I → I ⊕ Fin (ℓ + 1)) from rfl,
    show splitColor (I := I) c ∘ Sum.inr = Sum.inr ∘ c.succ.succAboveEmb from rfl,
    ← Multiset.singleton_add]
  abel

variable (ℓ) in
theorem card_split :
    Multiset.card (stendhalWeight (ℓ + 1) ν) = Multiset.card (stendhalWeight ℓ ν) + 1 := by
  simp [stendhalWeight]; omega

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable (ℓ) in
/-- Positions of the new loading, counted as `Fin (m + 1)`. -/
abbrev posEquiv : Fin (Multiset.card μ') ≃ Fin (m + 1) := finCongr (card_split ℓ ν)

variable {ν} [DecidableEq I]

/-- The position of the red strand `λ_c`. -/
def redPos (s : Seq μ) : Fin m := s.posOf (redStrand ν c)

theorem lbl_redPos (s : Seq μ) : s.lbl (redPos c s) = .inr c :=
  s.label_posOf _

theorem eq_redPos {s : Seq μ} {a : Fin m} (h : s.lbl a = .inr c) : a = redPos c s := by
  have e1 := eq_redStrand (ν := ν) (s := s.strandAt a) h
  have e2 := eq_redStrand (ν := ν) (s := s.strandAt (redPos c s)) (lbl_redPos c s)
  exact s.strandAt_injective (e1.trans e2.symm)

/-- The labels of the split loading, as a function on `Fin (m + 1)`. -/
def splitLabels (s : Seq μ) : Fin (m + 1) → I ⊕ Fin (ℓ + 1) :=
  Fin.insertNth (redPos c s).succ (.inr c.succ) (splitColor c ∘ s.1)

theorem splitLabels_weight (s : Seq μ) :
    Finset.univ.val.map (splitLabels c s) = μ' := by
  rw [Fin.univ_succAbove m (redPos c s).succ]
  change ((redPos c s).succ ::ₘ (Finset.univ.map (Fin.succAboveEmb _)).val).map _ = _
  rw [Multiset.map_cons, ← stendhalWeight_split c ν]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def, Fin.coe_succAboveEmb,
    splitLabels, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have h := congrArg (Multiset.map (splitColor c)) s.2
  rw [Multiset.map_map] at h
  rw [← h, ← Multiset.singleton_add]
  exact add_comm _ _

/-- The loading with the red strand `λ_c` replaced by the red strands `c`, `c + 1`. -/
def splitLoading (s : Seq μ) : Seq μ' :=
  ⟨splitLabels c s ∘ posEquiv ℓ ν, by
    rw [← Multiset.map_map]
    have h := congrArg Finset.val (Finset.map_univ_equiv (posEquiv ℓ ν))
    rw [show Finset.univ.val.map (posEquiv ℓ ν) = _ from h, splitLabels_weight]⟩

/-- The position in the split loading of the old strand at `a`. -/
def splitPos (s : Seq μ) (a : Fin m) : Fin (Multiset.card μ') :=
  (posEquiv ℓ ν).symm ((redPos c s).succ.succAbove a)

/-- The position of the new red strand `c + 1`. -/
def newPos (s : Seq μ) : Fin (Multiset.card μ') :=
  (posEquiv ℓ ν).symm (redPos c s).succ

theorem splitPos_val (s : Seq μ) (a : Fin m) :
    (splitPos c s a : ℕ) = if (a : ℕ) ≤ redPos c s then (a : ℕ) else (a : ℕ) + 1 := by
  simp only [splitPos, finCongr_symm, finCongr_apply, Fin.val_cast, Fin.succAbove]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.castSucc_lt_succ_iff.1 h1) h2
  · exact absurd (Fin.castSucc_lt_succ_iff.2 h2) h1
  · simp

theorem newPos_val (s : Seq μ) : (newPos c s : ℕ) = redPos c s + 1 := rfl

theorem splitLoading_lbl_splitPos (s : Seq μ) (a : Fin m) :
    (splitLoading c s).lbl (splitPos c s a) = splitColor c (s.lbl a) := by
  change splitLabels c s ((posEquiv ℓ ν) ((posEquiv ℓ ν).symm _)) = _
  rw [Equiv.apply_symm_apply, splitLabels, Fin.insertNth_apply_succAbove]; rfl

theorem splitLoading_lbl_newPos (s : Seq μ) :
    (splitLoading c s).lbl (newPos c s) = .inr c.succ := by
  change splitLabels c s ((posEquiv ℓ ν) ((posEquiv ℓ ν).symm _)) = _
  rw [Equiv.apply_symm_apply, splitLabels, Fin.insertNth_apply_same]

theorem splitPos_injective (s : Seq μ) : Function.Injective (splitPos c s) :=
  (posEquiv ℓ ν).symm.injective.comp (Fin.succAbove_right_injective)

theorem splitPos_ne_newPos (s : Seq μ) (a : Fin m) : splitPos c s a ≠ newPos c s :=
  fun h => Fin.succAbove_ne _ _ ((posEquiv ℓ ν).symm.injective h)

theorem eq_newPos_or_splitPos (s : Seq μ) (b : Fin (Multiset.card μ')) :
    b = newPos c s ∨ ∃ a, b = splitPos c s a := by
  by_cases h : posEquiv ℓ ν b = (redPos c s).succ
  · exact .inl ((Equiv.eq_symm_apply _).2 h)
  · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h
    exact .inr ⟨a, (Equiv.eq_symm_apply _).2 ha.symm⟩

/-- The labels of the split loading at a position given as a natural number. -/
theorem splitLoading_lbl (s : Seq μ) (b : Fin (Multiset.card μ')) :
    (splitLoading c s).lbl b =
      if h : (b : ℕ) ≤ redPos c s then splitColor c (s.lbl ⟨b, by omega⟩)
      else if (b : ℕ) = redPos c s + 1 then .inr c.succ
      else splitColor c (s.lbl ⟨b - 1, by have := b.2; have := card_split ℓ ν; omega⟩) := by
  rcases eq_newPos_or_splitPos c s b with rfl | ⟨a, rfl⟩
  · have hv := newPos_val c s
    rw [splitLoading_lbl_newPos]
    split_ifs <;> first | rfl | omega
  · rw [splitLoading_lbl_splitPos]
    have hv := splitPos_val c s a
    by_cases h1 : (a : ℕ) ≤ redPos c s <;> simp only [h1, ite_true, ite_false] at hv <;>
      split_ifs <;> first | omega | (congr 2; ext; simp only; omega)


/-! ### Adjacent transpositions -/

omit [DecidableEq I] in
theorem swapNat_lt {n k x : ℕ} (hk : k + 1 < n) (hx : x < n) : swapNat k x < n := by
  unfold swapNat; split_ifs <;> omega

omit [DecidableEq I] in
/-- The labels of `s_k • t`, for `k + 1 < m`, at a position given as a natural number. -/
theorem lbl_sadj_smul {κ : Multiset (I ⊕ Fin ℓ)} (t : Seq κ) {k : ℕ}
    (hk : k + 1 < Multiset.card κ) (b : Fin (Multiset.card κ)) :
    (sadj (Multiset.card κ) k • t).lbl b = t.lbl ⟨swapNat k b, swapNat_lt hk b.2⟩ := by
  change t.1 ((sadj _ k).symm b) = _
  rw [← Perm.inv_def, sadj_inv]
  exact congrArg t.1 (Fin.ext (sadj_val_of_lt hk b))

omit [DecidableEq I] in
theorem lbl_congr {κ : Multiset (I ⊕ Fin ℓ)} (t : Seq κ) {x y : ℕ} (h : x = y)
    (hx : x < Multiset.card κ) (hy : y < Multiset.card κ) : t.lbl ⟨x, hx⟩ = t.lbl ⟨y, hy⟩ := by
  subst h; rfl

theorem redPos_smul (s : Seq μ) (w : Perm (Fin m)) : redPos c (w • s) = w (redPos c s) := by
  symm; apply eq_redPos
  change s.1 (w.symm (w _)) = _
  rw [Equiv.symm_apply_apply]; exact lbl_redPos c s

theorem redPos_sadj_val (s : Seq μ) {j : ℕ} (hj : j + 1 < m) :
    (redPos c (sadj m j • s) : ℕ) = swapNat j (redPos c s) := by
  rw [redPos_smul, sadj_val_of_lt hj]

local notation "m'" => Multiset.card (stendhalWeight (ℓ + 1) ν)

/-- A crossing of two strands to the left of the red strand `λ_c`. -/
theorem splitLoading_sadj_left (s : Seq μ) {j : ℕ} (hj : j + 1 < redPos c s) :
    splitLoading c (sadj m j • s) = sadj m' j • splitLoading c s := by
  have hm : j + 1 < m := by omega
  have hm' : j + 1 < m' := by rw [card_split]; omega
  have hq : (redPos c (sadj m j • s) : ℕ) = redPos c s := by
    rw [redPos_sadj_val c s hm]; unfold swapNat; split_ifs <;> omega
  apply Subtype.ext; funext b
  change (splitLoading c _).lbl b = (sadj m' j • splitLoading c s).lbl b
  rw [lbl_sadj_smul _ hm', splitLoading_lbl, splitLoading_lbl]
  simp only [hq, lbl_sadj_smul _ hm, swapNat]
  split_ifs <;> (try split) <;> (try split) <;>
    first | rfl | omega

/-- A crossing of two strands to the right of the red strand `λ_c`. -/
theorem splitLoading_sadj_right (s : Seq μ) {j : ℕ} (hj : (redPos c s : ℕ) < j)
    (hm : j + 1 < m) :
    splitLoading c (sadj m j • s) = sadj m' (j + 1) • splitLoading c s := by
  have hm' : j + 1 + 1 < m' := by rw [card_split]; omega
  have hq : (redPos c (sadj m j • s) : ℕ) = redPos c s := by
    rw [redPos_sadj_val c s hm]; unfold swapNat; split_ifs <;> omega
  apply Subtype.ext; funext b
  change (splitLoading c _).lbl b = (sadj m' (j + 1) • splitLoading c s).lbl b
  rw [lbl_sadj_smul _ hm', splitLoading_lbl, splitLoading_lbl]
  simp only [hq, lbl_sadj_smul _ hm, swapNat]
  split_ifs <;> (repeat' split) <;>
    first | rfl | omega

/-- A black strand crossing the red strand `λ_c` from the left: in the split loading it
crosses both red strands `λ_c` and `λ_{c+1}`. -/
theorem splitLoading_sadj_cross_left (s : Seq μ) {j : ℕ} (hj : j + 1 = redPos c s) :
    splitLoading c (sadj m j • s) = sadj m' (j + 1) • sadj m' j • splitLoading c s := by
  have hm : j + 1 < m := by omega
  have hm' : j + 1 + 1 < m' := by rw [card_split]; omega
  have hm'' : j + 1 < m' := by omega
  have hq : (redPos c (sadj m j • s) : ℕ) = j := by
    rw [redPos_sadj_val c s hm]; unfold swapNat; split_ifs <;> omega
  apply Subtype.ext; funext b
  change (splitLoading c _).lbl b = (sadj m' (j + 1) • sadj m' j • splitLoading c s).lbl b
  rw [lbl_sadj_smul _ hm', lbl_sadj_smul _ hm'', splitLoading_lbl, splitLoading_lbl]
  simp only [hq, lbl_sadj_smul _ hm, swapNat]
  split_ifs <;> (repeat' split) <;>
    first | rfl | omega

/-- A black strand crossing the red strand `λ_c` from the right: in the split loading it
crosses both red strands `λ_{c+1}` and `λ_c`. -/
theorem splitLoading_sadj_cross_right (s : Seq μ) {j : ℕ} (hj : j = redPos c s)
    (hm : j + 1 < m) :
    splitLoading c (sadj m j • s) = sadj m' j • sadj m' (j + 1) • splitLoading c s := by
  have hm' : j + 1 + 1 < m' := by rw [card_split]; omega
  have hm'' : j + 1 < m' := by omega
  have hq : (redPos c (sadj m j • s) : ℕ) = j + 1 := by
    rw [redPos_sadj_val c s hm]; unfold swapNat; split_ifs <;> omega
  apply Subtype.ext; funext b
  change (splitLoading c _).lbl b = (sadj m' j • sadj m' (j + 1) • splitLoading c s).lbl b
  rw [lbl_sadj_smul _ hm'', lbl_sadj_smul _ hm', splitLoading_lbl, splitLoading_lbl]
  simp only [hq, lbl_sadj_smul _ hm, swapNat]
  split_ifs <;> (repeat' split) <;>
    first | rfl | omega

/-! ### Red order and violation -/

theorem splitPos_lt_splitPos_iff (s : Seq μ) {a b : Fin m} :
    splitPos c s a < splitPos c s b ↔ a < b := by
  rw [Fin.lt_def, Fin.lt_def, splitPos_val, splitPos_val]
  split_ifs <;> omega

omit [DecidableEq I] in
theorem exists_of_splitColor_eq_inr {x : I ⊕ Fin ℓ} {y : Fin (ℓ + 1)}
    (h : splitColor c x = .inr y) : ∃ r, x = .inr r ∧ y = c.succ.succAbove r := by
  cases x with
  | inl i => simp at h
  | inr r => exact ⟨r, rfl, (Sum.inr.inj h).symm⟩

omit [DecidableEq I] in
theorem succ_lt_succAbove {r : Fin ℓ} (h : c < r) : c.succ < c.succ.succAbove r := by
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.2 h)]
  exact Fin.succ_lt_succ_iff.2 h

omit [DecidableEq I] in
theorem succAbove_lt_succ {r : Fin ℓ} (h : r ≤ c) : c.succ.succAbove r < c.succ := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.2 h)]
  exact Fin.castSucc_lt_succ_iff.2 h

/-- Splitting a red strand preserves the order of the red strands. -/
theorem isRedOrdered_splitLoading_iff (s : Seq μ) :
    IsRedOrdered (splitLoading c s) ↔ IsRedOrdered s := by
  constructor
  · intro h a b r r' hab ha hb
    have := h (splitPos c s a) (splitPos c s b) _ _ ((splitPos_lt_splitPos_iff c s).2 hab)
      (by rw [splitLoading_lbl_splitPos, ha]; rfl) (by rw [splitLoading_lbl_splitPos, hb]; rfl)
    exact Fin.succAbove_lt_succAbove_iff.1 this
  · intro h a b r r' hab ha hb
    have hq := lbl_redPos c s
    rcases eq_newPos_or_splitPos c s a with rfl | ⟨a, rfl⟩ <;>
      rcases eq_newPos_or_splitPos c s b with rfl | ⟨b, rfl⟩
    · exact absurd hab (lt_irrefl _)
    · rw [splitLoading_lbl_newPos] at ha
      rw [splitLoading_lbl_splitPos] at hb
      obtain ⟨r₀, hr₀, rfl⟩ := exists_of_splitColor_eq_inr c hb
      cases Sum.inr.inj ha
      have hlt : redPos c s < b := by
        have h1 := splitPos_val c s b; have h2 := newPos_val c s
        rw [Fin.lt_def] at hab ⊢; split_ifs at h1 <;> omega
      exact succ_lt_succAbove c (h _ _ _ _ hlt hq hr₀)
    · rw [splitLoading_lbl_splitPos] at ha
      rw [splitLoading_lbl_newPos] at hb
      obtain ⟨r₀, hr₀, rfl⟩ := exists_of_splitColor_eq_inr c ha
      cases Sum.inr.inj hb
      have hle : a ≤ redPos c s := by
        have h1 := splitPos_val c s a; have h2 := newPos_val c s
        rw [Fin.lt_def] at hab; rw [Fin.le_def]; split_ifs at h1 <;> omega
      apply succAbove_lt_succ
      rcases hle.lt_or_eq with hlt | rfl
      · exact (h _ _ _ _ hlt hr₀ hq).le
      · rw [hq] at hr₀; exact (Sum.inr.inj hr₀).ge
    · rw [splitLoading_lbl_splitPos] at ha hb
      obtain ⟨r₀, hr₀, rfl⟩ := exists_of_splitColor_eq_inr c ha
      obtain ⟨r₁, hr₁, rfl⟩ := exists_of_splitColor_eq_inr c hb
      exact Fin.succAbove_lt_succAbove_iff.2
        (h _ _ _ _ ((splitPos_lt_splitPos_iff c s).1 hab) hr₀ hr₁)

/-- Splitting a red strand preserves violation (the leftmost strand is black). -/
theorem isViolated_splitLoading_iff (s : Seq μ) :
    IsViolated (splitLoading c s) ↔ IsViolated s := by
  have hm : 0 < m := (redPos c s).pos
  have h0 : splitPos c s ⟨0, hm⟩ = ⟨0, by rw [card_split]; omega⟩ := by
    ext; rw [splitPos_val]; simp
  constructor
  · rintro ⟨_, h⟩
    refine ⟨hm, ?_⟩
    rwa [← h0, splitLoading_lbl_splitPos, splitColor_isLeft] at h
  · rintro ⟨_, h⟩
    refine ⟨by rw [card_split]; omega, ?_⟩
    rwa [← h0, splitLoading_lbl_splitPos, splitColor_isLeft]

end Categorification.Stendhal.SplitRed
