/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRed

/-!
# Splitting a red strand: the relations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. The images in the split corner of the generators of the Stendhal algebra of
the merged weights satisfy the defining relations, so splitting the red strand `λ_c` into two
parallel red strands is an algebra map (`splitHom`).

The relations away from the red strand `λ_c` are the corresponding relations in the Stendhal
algebra of `λ'`. Near it, a black strand crossing the merged red strand becomes a black strand
crossing two red strands, and the bigon and triple-point relations (4.2), (4.1a) for
`λ'_c + λ'_{c+1}` follow from those for `λ'_c` and `λ'_{c+1}`.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv MvPolynomial

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (c : Fin ℓ)
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "m'" => Multiset.card (stendhalWeight (ℓ + 1) ν)
local notation "A'" => StendhalAlgebraAllOrders k Q Λ' ν
local notation "e'" => StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ') (ν := ν)
local notation "ψ'" => StendhalAlgebraAllOrders.ψ (k := k) (Q := Q) (Λ := Λ') (ν := ν)
local notation "x'" => StendhalAlgebraAllOrders.x (k := k) (Q := Q) (Λ := Λ') (ν := ν)
local notation "C" => SplitCorner c Q Λ' ν

noncomputable local instance : Algebra k C := KLR.cornerAlgebra _

/-! ### Bookkeeping -/

omit [DecidableEq I] in
theorem swapNat_left (j : ℕ) : swapNat j j = j + 1 := by unfold swapNat; simp

omit [DecidableEq I] in
theorem swapNat_right (j : ℕ) : swapNat j (j + 1) = j := by unfold swapNat; simp

omit [DecidableEq I] in
theorem swapNat_of_ne {j q : ℕ} (h₁ : q ≠ j) (h₂ : q ≠ j + 1) : swapNat j q = q := by
  unfold swapNat; simp [h₁, h₂]

theorem W_of_lt {j q : ℕ} (h : j + 1 < q) : W Q Λ' ν j q = ψ' j := by
  unfold W; simp [h]

theorem W_of_eq_succ {j q : ℕ} (h : j + 1 = q) : W Q Λ' ν j q = ψ' (j + 1) * ψ' j := by
  unfold W; simp [h]

theorem W_of_eq {j q : ℕ} (h : j = q) : W Q Λ' ν j q = ψ' j * ψ' (j + 1) := by
  unfold W; simp [h]

theorem W_of_gt {j q : ℕ} (h : q < j) : W Q Λ' ν j q = ψ' (j + 1) := by
  unfold W
  simp only [show ¬ j + 1 < q by omega, show j + 1 ≠ q by omega, show j ≠ q by omega,
    ↓reduceIte]

theorem cψ (a b : ℕ) (h : a + 1 < b ∨ b + 1 < a) : Commute (ψ' a) (ψ' b) := by
  rcases h with h | h
  · exact aψ_mul_ψ a b h
  · exact (aψ_mul_ψ b a h).symm

theorem W_swap_of_lt {j l : ℕ} (h : j + 1 < l) (q : ℕ) :
    W Q Λ' ν j (swapNat l q) = W Q Λ' ν j q := by
  unfold W swapNat; split_ifs <;> first | rfl | omega

theorem W_swap_of_gt {j l : ℕ} (h : j + 1 < l) (q : ℕ) :
    W Q Λ' ν l (swapNat j q) = W Q Λ' ν l q := by
  unfold W swapNat; split_ifs <;> first | rfl | omega

theorem W_commute {j l : ℕ} (h : j + 1 < l) (q : ℕ) :
    Commute (W Q Λ' ν j q) (W Q Λ' ν l q) := by
  unfold W
  split_ifs <;>
    (repeat' first | apply Commute.mul_left | apply Commute.mul_right) <;>
    exact cψ Λ' _ _ (by omega)

theorem lbl_split (s : Seq μ) (a : Fin m) {b : ℕ} (hb : b = splitPos c s a) (h : b < m') :
    (splitLoading c s).lbl ⟨b, h⟩ = splitColor c (s.lbl a) := by
  rw [← splitLoading_lbl_splitPos c s a]; exact lbl_congr _ hb _ _

theorem lbl_split_le (s : Seq μ) (j : ℕ) (hj : j < m) (hle : j ≤ redPos c s) (h : j < m') :
    (splitLoading c s).lbl ⟨j, h⟩ = splitColor c (s.lbl ⟨j, hj⟩) :=
  lbl_split c s ⟨j, hj⟩ (by rw [splitPos_val]; simp only [hle, ↓reduceIte]) h

theorem lbl_split_gt (s : Seq μ) (j : ℕ) (hj : j < m) (hlt : redPos c s < j)
    (h : j + 1 < m') :
    (splitLoading c s).lbl ⟨j + 1, h⟩ = splitColor c (s.lbl ⟨j, hj⟩) :=
  lbl_split c s ⟨j, hj⟩ (by rw [splitPos_val]; simp only [show ¬ j ≤ redPos c s by omega,
    ↓reduceIte]) h

theorem lbl_split_new (s : Seq μ) {b : ℕ} (hb : b = redPos c s + 1) (h : b < m') :
    (splitLoading c s).lbl ⟨b, h⟩ = .inr c.succ := by
  rw [← splitLoading_lbl_newPos c s]; exact lbl_congr _ (by rw [hb, Fin.val_succ]) _ _

theorem lbl_split_red (s : Seq μ) {b : ℕ} (hb : b = redPos c s) (h : b < m') :
    (splitLoading c s).lbl ⟨b, h⟩ = .inr c.castSucc := by
  rw [lbl_split c s (redPos c s) (by rw [hb, splitPos_val]; simp) h, lbl_redPos,
    splitColor_inr, succAbove_self]

theorem gE_mul_self (s : Seq μ) : (gE c Λ' s : C) * gE c Λ' s = gE c Λ' s := by
  rw [gE_mul_gE]; simp

theorem val_X_mul (a : Fin m) (u : Seq μ) {Y : C} (hY : gE c Λ' u * Y = Y) :
    (polSplit c Λ' (X a) * Y).val = x' (splitPos c u a) * Y.val := by
  rw [val_polSplit_mul c Λ' _ u hY, rename_X, polA_X]

theorem val_gΨ_gΨ_gE (a b : ℕ) (ha : a + 1 < m) (hb : b + 1 < m) (t : Seq μ) :
    (gΨ c Λ' a * gΨ c Λ' b * gE c Λ' t : C).val =
      W Q Λ' ν a (swapNat b (redPos c t)) *
        (W Q Λ' ν b (redPos c t) * e' (splitLoading c t)) := by
  rw [mul_assoc, val_gΨ_mul c Λ' a ha (sadj m b • t)
    (gE_mul_gΨ_mul c Λ' b t (gE_mul_self c Λ' t)), val_gΨ_mul_gE c Λ' b hb,
    redPos_sadj_val c t hb]

/-! ### The easy relations -/

theorem gΨ_comm (j l : ℕ) (h : j + 1 < l) :
    (gΨ c Λ' j * gΨ c Λ' l : C) = gΨ c Λ' l * gΨ c Λ' j := by
  by_cases hl : l + 1 < m
  swap
  · simp [gΨ, hl]
  have hj : j + 1 < m := by omega
  refine ext_gE c Λ' fun t => Corner.ext ?_
  rw [val_gΨ_gΨ_gE c Λ' j l hj hl, val_gΨ_gΨ_gE c Λ' l j hl hj, W_swap_of_lt Λ' h,
    W_swap_of_gt Λ' h, ← mul_assoc, ← mul_assoc, (W_commute Λ' h _).eq]

theorem splitPos_sadj (t : Seq μ) (a : Fin m) (j : ℕ) (hj : j + 1 < m)
    (h₂ : a.val ≠ j + 1) : splitPos c (sadj m j • t) a = splitPos c t a := by
  apply Fin.ext
  rw [splitPos_val, splitPos_val, redPos_sadj_val c t hj]
  unfold swapNat; split_ifs <;> omega

theorem X_gΨ_comm (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (polSplit c Λ' (X a) * gΨ c Λ' j : C) = gΨ c Λ' j * polSplit c Λ' (X a) := by
  by_cases hj : j + 1 < m
  swap
  · simp [gΨ, hj]
  refine ext_gE c Λ' fun t => Corner.ext ?_
  rw [mul_assoc, val_X_mul c Λ' a (sadj m j • t) (gE_mul_gΨ_mul c Λ' j t (gE_mul_self c Λ' t)),
    val_gΨ_mul_gE c Λ' j hj, mul_assoc,
    val_gΨ_mul c Λ' j hj t (gE_mul_polSplit_mul c Λ' _ t (gE_mul_self c Λ' t)),
    val_X_mul c Λ' a t (gE_mul_self c Λ' t), val_gE, splitPos_sadj c t a j hj h₂,
    ← mul_assoc, ← mul_assoc]
  congr 1
  have hp := splitPos_val c t a
  generalize splitPos c t a = p at hp
  have hq := (redPos c t).2
  generalize (redPos c t : ℕ) = q at hp hq
  unfold W
  split_ifs at hp ⊢ <;>
    (repeat' first | apply Commute.mul_left | apply Commute.mul_right) <;>
    exact ax_mul_ψ p _ (by omega) (by omega)

theorem X_mul_gE_of_red (a : Fin m) (s : Seq μ) (h : (s.lbl a).isRight) :
    (polSplit c Λ' (X a) * gE c Λ' s : C) = 0 := by
  apply Corner.ext
  rw [val_X_mul c Λ' a s (gE_mul_self c Λ' s), val_gE, Corner.val_zero]
  apply StendhalAlgebraAllOrders.x_mul_e_of_red
  rw [splitLoading_lbl_splitPos, splitColor_isRight]; exact h


theorem lbl_eq_red_iff (t : Seq μ) (a : Fin m) : t.lbl a = .inr c ↔ (a : ℕ) = redPos c t := by
  constructor
  · intro h; rw [eq_redPos c h]
  · intro h; rw [show a = redPos c t from Fin.ext h]; exact lbl_redPos c t

omit [DecidableEq I] in
theorem splitColor_ne_red (y : I ⊕ Fin ℓ) (hy : y ≠ .inr c) :
    splitColor c y ≠ .inr c.castSucc := by
  rw [← succAbove_self c, ← splitColor_inr]; exact fun h => hy (splitColor_injective c h)

/-- The relation `(x_j ψ_j - ψ_j x_{j+1}) e(t) = [t_j = t_{j+1}] e(t)`. -/
theorem dotCrossLeft (j : ℕ) (h : j + 1 < m) (t : Seq μ) :
    ((polSplit c Λ' (X ⟨j, by omega⟩) * gΨ c Λ' j -
        gΨ c Λ' j * polSplit c Λ' (X ⟨j + 1, h⟩)) * gE c Λ' t : C) =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then gE c Λ' t else 0 := by
  have hm := card_split ℓ ν
  have hq := (redPos c t).2
  have hval : ((if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then gE c Λ' t else 0 : C)).val =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then e' (splitLoading c t) else 0 := by
    split_ifs <;> simp
  by_cases hq1 : j + 1 = redPos c t
  · have hr : t.lbl ⟨j + 1, h⟩ = .inr c := (lbl_eq_red_iff c t _).2 hq1
    have hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩ := by
      rw [hr, Ne, lbl_eq_red_iff]; simp only; omega
    simp only [hne, ↓reduceIte]
    rw [sub_mul, mul_assoc, gΨ_mul_gE, ← mul_assoc, X_mul_gE_of_red, zero_mul, mul_assoc,
      X_mul_gE_of_red, mul_zero, sub_zero]
    · rw [hr]; rfl
    · rw [lbl_sadj_smul t h, lbl_congr t (swapNat_left j) _ h, hr]; rfl
  apply Corner.ext
  rw [hval, sub_mul, Corner.val_sub, mul_assoc, mul_assoc,
    val_X_mul c Λ' _ (sadj m j • t) (gE_mul_gΨ_mul c Λ' j t (gE_mul_self c Λ' t)),
    val_gΨ_mul_gE c Λ' j h,
    val_gΨ_mul c Λ' j h t (gE_mul_polSplit_mul c Λ' _ t (gE_mul_self c Λ' t)),
    val_X_mul c Λ' _ t (gE_mul_self c Λ' t), val_gE]
  rcases lt_trichotomy (j + 1) (redPos c t) with hlt | heq | hgt
  · have h' : j + 1 < m' := by omega
    rw [W_of_lt Λ' hlt,
      show splitPos c (sadj m j • t) ⟨j, by omega⟩ = ⟨j, by omega⟩ from Fin.ext (by
        rw [splitPos_val, redPos_sadj_val c t h]; simp only; unfold swapNat; split_ifs <;> omega),
      show splitPos c t ⟨j + 1, h⟩ = ⟨j + 1, h'⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      ← mul_assoc, ← mul_assoc, ← sub_mul, aDotCrossLeft j h' (splitLoading c t),
      lbl_split_le c t j (by omega) (by omega), lbl_split_le c t (j + 1) h (by omega)]
    simp only [(splitColor_injective c).eq_iff]
  · exact absurd heq hq1
  rcases Nat.lt_or_ge (redPos c t) j with hgt' | hle
  · have h' : j + 1 + 1 < m' := by omega
    rw [W_of_gt Λ' hgt',
      show splitPos c (sadj m j • t) ⟨j, by omega⟩ = ⟨j + 1, by omega⟩ from Fin.ext (by
        rw [splitPos_val, redPos_sadj_val c t h]; simp only; unfold swapNat; split_ifs <;> omega),
      show splitPos c t ⟨j + 1, h⟩ = ⟨j + 1 + 1, h'⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      ← mul_assoc, ← mul_assoc, ← sub_mul, aDotCrossLeft (j + 1) h' (splitLoading c t),
      lbl_split_gt c t j (by omega) hgt', lbl_split_gt c t (j + 1) h (by omega)]
    simp only [(splitColor_injective c).eq_iff]
  -- the dot slides past both red strands
  have hj : j = redPos c t := by omega
  have h' : j + 1 + 1 < m' := by omega
  have hr : t.lbl ⟨j, by omega⟩ = .inr c := (lbl_eq_red_iff c t _).2 hj
  have hb : t.lbl ⟨j + 1, h⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
  have hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩ := by rw [hr]; exact hb.symm
  simp only [hne, ↓reduceIte]
  rw [W_of_eq Λ' hj,
    show splitPos c (sadj m j • t) ⟨j, by omega⟩ = ⟨j, by omega⟩ from Fin.ext (by
      rw [splitPos_val, redPos_sadj_val c t h]; simp only; unfold swapNat; split_ifs <;> omega),
    show splitPos c t ⟨j + 1, h⟩ = ⟨j + 1 + 1, h'⟩ from Fin.ext (by
      rw [splitPos_val]; simp only; split_ifs <;> omega)]
  set T := splitLoading c t
  have l1 : T.lbl ⟨j + 1, by omega⟩ = .inr c.succ := lbl_split_new c t (by omega) _
  have l2 : T.lbl ⟨j + 1 + 1, h'⟩ = splitColor c (t.lbl ⟨j + 1, h⟩) :=
    lbl_split_gt c t (j + 1) h (by omega) h'
  have l0 : T.lbl ⟨j, by omega⟩ = .inr c.castSucc := lbl_split_red c t (by omega) _
  have s1 := slideL (k := k) (Q := Q) (Λ := Λ') (j + 1) h' T (by rw [l1, l2]; exact (splitColor_ne_new c _).symm) 1
  have s2 := aψ_mul_e (Q := Q) (Λ := Λ') (j + 1) T
  have s3 := slideL (k := k) (Q := Q) (Λ := Λ') j (by omega) (sadj m' (j + 1) • T) (by
    rw [lbl_sadj_smul T h', lbl_sadj_smul T h', lbl_congr T (swapNat_of_ne (by simp only; omega)
      (by simp only; omega)) _ (by omega), lbl_congr T (swapNat_left (j + 1)) _ h', l0, l2]
    exact (splitColor_ne_red c _ hb).symm) 1
  simp only [pow_one] at s1 s3
  simp only [mul_assoc] at s1 s2
  rw [sub_eq_zero]
  simp only [mul_assoc]
  rw [s1, s2]
  conv_rhs => rw [← mul_assoc, ← mul_assoc, s3]
  simp only [mul_assoc]

/-- The relation `(ψ_j x_j - x_{j+1} ψ_j) e(t) = [t_j = t_{j+1}] e(t)`. -/
theorem dotCrossRight (j : ℕ) (h : j + 1 < m) (t : Seq μ) :
    ((gΨ c Λ' j * polSplit c Λ' (X ⟨j, by omega⟩) -
        polSplit c Λ' (X ⟨j + 1, h⟩) * gΨ c Λ' j) * gE c Λ' t : C) =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then gE c Λ' t else 0 := by
  have hm := card_split ℓ ν
  have hq := (redPos c t).2
  have hval : ((if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then gE c Λ' t else 0 : C)).val =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then e' (splitLoading c t) else 0 := by
    split_ifs <;> simp
  by_cases hq0 : j = redPos c t
  · have hr : t.lbl ⟨j, by omega⟩ = .inr c := (lbl_eq_red_iff c t _).2 hq0
    have hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩ := by
      rw [hr, Ne, eq_comm, lbl_eq_red_iff]; simp only; omega
    simp only [hne, ↓reduceIte]
    rw [sub_mul, mul_assoc, X_mul_gE_of_red, mul_zero, mul_assoc, gΨ_mul_gE, ← mul_assoc,
      X_mul_gE_of_red, zero_mul, sub_zero]
    · rw [lbl_sadj_smul t h, lbl_congr t (swapNat_right j) _ (by omega), hr]; rfl
    · rw [hr]; rfl
  apply Corner.ext
  rw [hval, sub_mul, Corner.val_sub, mul_assoc, mul_assoc,
    val_gΨ_mul c Λ' j h t (gE_mul_polSplit_mul c Λ' _ t (gE_mul_self c Λ' t)),
    val_X_mul c Λ' _ t (gE_mul_self c Λ' t),
    val_X_mul c Λ' _ (sadj m j • t) (gE_mul_gΨ_mul c Λ' j t (gE_mul_self c Λ' t)),
    val_gΨ_mul_gE c Λ' j h, val_gE]
  rcases lt_trichotomy (j + 1) (redPos c t) with hlt | heq | hgt
  · have h' : j + 1 < m' := by omega
    rw [W_of_lt Λ' hlt,
      show splitPos c t ⟨j, by omega⟩ = ⟨j, by omega⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      show splitPos c (sadj m j • t) ⟨j + 1, h⟩ = ⟨j + 1, h'⟩ from Fin.ext (by
        rw [splitPos_val, redPos_sadj_val c t h]; simp only; unfold swapNat;
        split_ifs <;> omega),
      ← mul_assoc, ← mul_assoc, ← sub_mul, aDotCrossRight j h' (splitLoading c t),
      lbl_split_le c t j (by omega) (by omega), lbl_split_le c t (j + 1) h (by omega)]
    simp only [(splitColor_injective c).eq_iff]
  · -- the dot slides past both red strands
    have h' : j + 1 + 1 < m' := by omega
    have hr : t.lbl ⟨j + 1, h⟩ = .inr c := (lbl_eq_red_iff c t _).2 heq
    have hb : t.lbl ⟨j, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩ := by rw [hr]; exact hb
    simp only [hne, ↓reduceIte]
    rw [W_of_eq_succ Λ' heq,
      show splitPos c t ⟨j, by omega⟩ = ⟨j, by omega⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      show splitPos c (sadj m j • t) ⟨j + 1, h⟩ = ⟨j + 1 + 1, h'⟩ from Fin.ext (by
        rw [splitPos_val, redPos_sadj_val c t h]; simp only; unfold swapNat;
        split_ifs <;> omega)]
    set T := splitLoading c t
    have l0 : T.lbl ⟨j, by omega⟩ = splitColor c (t.lbl ⟨j, by omega⟩) :=
      lbl_split_le c t j (by omega) (by omega) _
    have l1 : T.lbl ⟨j + 1, by omega⟩ = .inr c.castSucc := lbl_split_red c t heq _
    have l2 : T.lbl ⟨j + 1 + 1, h'⟩ = .inr c.succ := lbl_split_new c t (by omega) _
    have s1 := slideR (k := k) (Q := Q) (Λ := Λ') j (by omega) T (by
      rw [l0, l1]; exact splitColor_ne_red c _ hb) 1
    have s2 := aψ_mul_e (Q := Q) (Λ := Λ') j T
    have s3 := slideR (k := k) (Q := Q) (Λ := Λ') (j + 1) h' (sadj m' j • T) (by
      rw [lbl_sadj_smul T (show j + 1 < m' by omega),
        lbl_sadj_smul T (show j + 1 < m' by omega),
        lbl_congr T (swapNat_right j) _ (by omega),
        lbl_congr T (swapNat_of_ne (by omega) (by omega)) _ h', l0, l2]
      exact splitColor_ne_new c _) 1
    simp only [pow_one] at s1 s3
    rw [sub_eq_zero]
    simp only [mul_assoc]
    rw [← mul_assoc (ψ' j), s1]
    simp only [mul_assoc]
    rw [s2]
    conv_lhs => rw [← mul_assoc, ← mul_assoc, s3]
    simp only [mul_assoc]
  have hlt : redPos c t < j := by omega
  have h' : j + 1 + 1 < m' := by omega
  rw [W_of_gt Λ' hlt,
    show splitPos c t ⟨j, by omega⟩ = ⟨j + 1, by omega⟩ from Fin.ext (by
      rw [splitPos_val]; simp only; split_ifs <;> omega),
    show splitPos c (sadj m j • t) ⟨j + 1, h⟩ = ⟨j + 1 + 1, h'⟩ from Fin.ext (by
      rw [splitPos_val, redPos_sadj_val c t h]; simp only; unfold swapNat;
      split_ifs <;> omega),
    ← mul_assoc, ← mul_assoc, ← sub_mul, aDotCrossRight (j + 1) h' (splitLoading c t),
    lbl_split_gt c t j (by omega) hlt, lbl_split_gt c t (j + 1) h (by omega)]
  simp only [(splitColor_injective c).eq_iff]

end Categorification.Stendhal.SplitRed
