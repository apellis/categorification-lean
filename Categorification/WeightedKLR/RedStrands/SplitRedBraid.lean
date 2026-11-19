/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedRelations

/-!
# Splitting a red strand: the braid relation

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. The images of the crossings in the split corner satisfy the braid relation
(KL I (2.7)/(2.8)) of the Stendhal algebra of the merged weights `λ'_c + λ'_{c+1}`.

Away from the red strand `λ_c` this is the braid relation for `λ'`. When the red strand is an
outer strand of the triple point, the two sides agree by two braid moves without correction.
When it is the middle strand, a black strand passes over both red strands `λ'_c`, `λ'_{c+1}`;
the two triple-point corrections `∑ x_j^a x_{j+3}^b` with `a + b = λ'_c - 1` and
`a + b = λ'_{c+1} - 1`, slid through the remaining crossings, add up to the correction for
`λ'_c + λ'_{c+1}`.
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

/-! ### Moves in the Stendhal algebra of `λ'` -/

/-- A braid move without correction, when the outer strands have different labels. -/
theorem braid_of_ne (j : ℕ) (h : j + 2 < m') (T : Seq (stendhalWeight (ℓ + 1) ν))
    (hne : T.lbl ⟨j, by omega⟩ ≠ T.lbl ⟨j + 2, h⟩) (Y : A') (hY : e' T * Y = Y) :
    ψ' j * (ψ' (j + 1) * (ψ' j * Y)) = ψ' (j + 1) * (ψ' j * (ψ' (j + 1) * Y)) := by
  have key := aBraid (k := k) (Q := Q) (Λ := Λ') j h T
  simp only [hne, false_and, ↓reduceIte, sub_mul, sub_eq_zero] at key
  rw [← hY]
  have := congrArg (· * Y) key
  simp only [mul_assoc] at this
  exact this

/-- The idempotent at the target of one crossing. -/
theorem e_mul_ψe (a : ℕ) (T : Seq (stendhalWeight (ℓ + 1) ν)) :
    e' (sadj m' a • T) * (ψ' a * e' T) = ψ' a * e' T := by
  rw [aψ_mul_e, ← mul_assoc, ae_mul_e]
  simp

/-- The idempotent at the target of two crossings. -/
theorem e_mul_ψψe (a b : ℕ) (T : Seq (stendhalWeight (ℓ + 1) ν)) :
    e' (sadj m' a • sadj m' b • T) * (ψ' a * (ψ' b * e' T)) = ψ' a * (ψ' b * e' T) := by
  have h1 := e_mul_ψe (k := k) (Q := Q) Λ' b T
  have h2 := e_mul_ψe (k := k) (Q := Q) Λ' a (sadj m' b • T)
  calc e' (sadj m' a • sadj m' b • T) * (ψ' a * (ψ' b * e' T))
      = e' (sadj m' a • sadj m' b • T) * (ψ' a * e' (sadj m' b • T)) * (ψ' b * e' T) := by
        conv_lhs => rw [← h1]
        simp only [mul_assoc]
    _ = ψ' a * (ψ' b * e' T) := by rw [h2, mul_assoc, h1]

/-- Conjugating a dot on the right strand by a crossing of differently labelled strands. -/
theorem conjL (j : ℕ) (hj : j + 1 < m') (T : Seq (stendhalWeight (ℓ + 1) ν))
    (hT : T.lbl ⟨j, by omega⟩ ≠ T.lbl ⟨j + 1, hj⟩) (a r : ℕ) (b : Fin m') (hb₁ : b.val ≠ j)
    (hb₂ : b.val ≠ j + 1) :
    ψ' j * (x' ⟨j + 1, hj⟩ ^ a * x' b ^ r) * (ψ' j * e' T) =
      x' ⟨j, by omega⟩ ^ a * x' b ^ r * (ψ' j * (ψ' j * e' T)) := by
  have hs : (sadj m' j • T).lbl ⟨j, by omega⟩ ≠ (sadj m' j • T).lbl ⟨j + 1, hj⟩ := by
    rw [lbl_sadj_smul T hj, lbl_sadj_smul T hj, lbl_congr T (swapNat_left j) _ hj,
      lbl_congr T (swapNat_right j) _ (by omega)]
    exact hT.symm
  have cψ : Commute (x' b ^ r) (ψ' j) :=
    Commute.pow_left (ax_mul_ψ (k := k) (Q := Q) (Λ := Λ') b j hb₁ hb₂) r
  have ce : Commute (x' b ^ r) (e' (sadj m' j • T)) :=
    Commute.pow_left (ax_mul_e (k := k) (Q := Q) (Λ := Λ') b _) r
  have s := slideL (k := k) (Q := Q) (Λ := Λ') j hj (sadj m' j • T) hs a
  rw [aψ_mul_e]
  calc ψ' j * (x' ⟨j + 1, hj⟩ ^ a * x' b ^ r) * (e' (sadj m' j • T) * ψ' j)
      = ψ' j * x' ⟨j + 1, hj⟩ ^ a * (x' b ^ r * e' (sadj m' j • T)) * ψ' j := by
        simp only [mul_assoc]
    _ = (ψ' j * x' ⟨j + 1, hj⟩ ^ a * e' (sadj m' j • T)) * (x' b ^ r * ψ' j) := by
        rw [ce.eq]; simp only [mul_assoc]
    _ = x' ⟨j, by omega⟩ ^ a * (ψ' j * (e' (sadj m' j • T) * x' b ^ r)) * ψ' j := by
        rw [s]; simp only [mul_assoc]
    _ = x' ⟨j, by omega⟩ ^ a * x' b ^ r * (ψ' j * (e' (sadj m' j • T) * ψ' j)) := by
        rw [← ce.eq, ← mul_assoc (ψ' j), ← cψ.eq]; simp only [mul_assoc]

/-- Conjugating a dot on the left strand by a crossing of differently labelled strands. -/
theorem conjR (j : ℕ) (hj : j + 1 < m') (T : Seq (stendhalWeight (ℓ + 1) ν))
    (hT : T.lbl ⟨j, by omega⟩ ≠ T.lbl ⟨j + 1, hj⟩) (a r : ℕ) (b : Fin m') (hb₁ : b.val ≠ j)
    (hb₂ : b.val ≠ j + 1) :
    ψ' j * (x' ⟨j, by omega⟩ ^ a * x' b ^ r) * (ψ' j * e' T) =
      x' ⟨j + 1, hj⟩ ^ a * x' b ^ r * (ψ' j * (ψ' j * e' T)) := by
  have hs : (sadj m' j • T).lbl ⟨j, by omega⟩ ≠ (sadj m' j • T).lbl ⟨j + 1, hj⟩ := by
    rw [lbl_sadj_smul T hj, lbl_sadj_smul T hj, lbl_congr T (swapNat_left j) _ hj,
      lbl_congr T (swapNat_right j) _ (by omega)]
    exact hT.symm
  have cψ : Commute (x' b ^ r) (ψ' j) :=
    Commute.pow_left (ax_mul_ψ (k := k) (Q := Q) (Λ := Λ') b j hb₁ hb₂) r
  have ce : Commute (x' b ^ r) (e' (sadj m' j • T)) :=
    Commute.pow_left (ax_mul_e (k := k) (Q := Q) (Λ := Λ') b _) r
  have s := slideR (k := k) (Q := Q) (Λ := Λ') j hj (sadj m' j • T) hs a
  rw [aψ_mul_e]
  calc ψ' j * (x' ⟨j, by omega⟩ ^ a * x' b ^ r) * (e' (sadj m' j • T) * ψ' j)
      = ψ' j * x' ⟨j, by omega⟩ ^ a * (x' b ^ r * e' (sadj m' j • T)) * ψ' j := by
        simp only [mul_assoc]
    _ = (ψ' j * x' ⟨j, by omega⟩ ^ a * e' (sadj m' j • T)) * (x' b ^ r * ψ' j) := by
        rw [ce.eq]; simp only [mul_assoc]
    _ = x' ⟨j + 1, hj⟩ ^ a * (ψ' j * (e' (sadj m' j • T) * x' b ^ r)) * ψ' j := by
        rw [s]; simp only [mul_assoc]
    _ = x' ⟨j + 1, hj⟩ ^ a * x' b ^ r * (ψ' j * (e' (sadj m' j • T) * ψ' j)) := by
        rw [← ce.eq, ← mul_assoc (ψ' j), ← cψ.eq]; simp only [mul_assoc]

/-- A braid move with its correction, applied to a vector `Y = e(T) Y`. -/
theorem braid_mul (j : ℕ) (h : j + 2 < m') (T : Seq (stendhalWeight (ℓ + 1) ν)) (Y : A')
    (hY : e' T * Y = Y) :
    ψ' j * (ψ' (j + 1) * (ψ' j * Y)) = ψ' (j + 1) * (ψ' j * (ψ' (j + 1) * Y)) +
      (if T.lbl ⟨j, by omega⟩ = T.lbl ⟨j + 2, h⟩ ∧
          T.lbl ⟨j, by omega⟩ ≠ T.lbl ⟨j + 1, by omega⟩ then
        polA k Q Λ' ν (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (stendhalQ Q Λ' (T.lbl ⟨j, by omega⟩) (T.lbl ⟨j + 1, by omega⟩))))
      else 0) * Y := by
  have key : (ψ' j * ψ' (j + 1) * ψ' j - ψ' (j + 1) * ψ' j * ψ' (j + 1)) * Y =
      (if T.lbl ⟨j, by omega⟩ = T.lbl ⟨j + 2, h⟩ ∧
          T.lbl ⟨j, by omega⟩ ≠ T.lbl ⟨j + 1, by omega⟩ then
        polA k Q Λ' ν (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (stendhalQ Q Λ' (T.lbl ⟨j, by omega⟩) (T.lbl ⟨j + 1, by omega⟩))))
      else 0) * Y := by
    conv_lhs => rw [← hY, ← mul_assoc, aBraid j h]
    split_ifs <;> simp only [mul_assoc, hY, zero_mul]
  rw [sub_mul, sub_eq_iff_eq_add] at key
  simp only [mul_assoc] at key
  rw [key]; exact add_comm _ _

omit [DecidableEq I] in
theorem lbl_sadj_eq (T : Seq (stendhalWeight (ℓ + 1) ν)) {a p r : ℕ} (ha : a + 1 < m')
    (hp : p < m') (hr : r < m') (h : swapNat a p = r) :
    (sadj m' a • T).lbl ⟨p, hp⟩ = T.lbl ⟨r, hr⟩ := by
  rw [lbl_sadj_smul _ ha]; exact lbl_congr T h _ _

/-- The divided difference of `x^n` evaluated at three dots. -/
theorem polA_rename_qbar_pow (a b d : Fin m') (n : ℕ) :
    polA k Q Λ' ν (rename ![a, b, d] (qbar (X 0 ^ n))) =
      ∑ t ∈ Finset.range n, polA k Q Λ' ν (X a ^ t * X d ^ (n - 1 - t)) := by
  rw [StendhalAlgebraAllOrders.qbar_X_zero_pow, map_sum, map_sum]
  simp [rename_X]

/-! ### The black strand crossing both red strands -/

/-- A dot pair conjugated by the crossing of the right red strand with the black strand to its
right. -/
theorem term_right (j : ℕ) (h : j + 1 + 1 + 1 < m') (T : Seq (stendhalWeight (ℓ + 1) ν))
    (i : I) (r : Fin (ℓ + 1)) (hT2 : T.lbl ⟨j + 1 + 1, by omega⟩ = .inr r)
    (hT3 : T.lbl ⟨j + 1 + 1 + 1, h⟩ = .inl i) (a s : ℕ) :
    ψ' (j + 1 + 1) * (polA k Q Λ' ν (X ⟨j, by omega⟩ ^ a * X ⟨j + 1 + 1, by omega⟩ ^ s) *
        (ψ' (j + 1 + 1) * e' T)) =
      polA k Q Λ' ν (X ⟨j, by omega⟩ ^ a * X ⟨j + 1 + 1 + 1, h⟩ ^ (s + Λ' r i)) * e' T := by
  rw [mul_comm (X _ ^ a), map_mul, map_pow, map_pow, polA_X, polA_X, ← mul_assoc,
    conjR Λ' (j + 1 + 1) h T (by rw [hT2, hT3]; simp) s a ⟨j, by omega⟩ (by dsimp only; omega)
      (by dsimp only; omega),
    ← mul_assoc (ψ' _) (ψ' _), aψ_sq (j + 1 + 1) h T, hT2, hT3]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, map_pow, rename_X,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [← polA_X, ← map_pow, ← map_mul]
  rw [← mul_assoc, ← map_mul, pow_add]
  ring_nf

/-- A dot pair conjugated by the crossing of the black strand with the left red strand. -/
theorem term_left (j : ℕ) (h : j + 1 + 1 + 1 < m') (T : Seq (stendhalWeight (ℓ + 1) ν))
    (i : I) (r : Fin (ℓ + 1)) (hT0 : T.lbl ⟨j, by omega⟩ = .inl i)
    (hT1 : T.lbl ⟨j + 1, by omega⟩ = .inr r) (a s : ℕ) :
    ψ' j * (polA k Q Λ' ν (X ⟨j + 1, by omega⟩ ^ a * X ⟨j + 1 + 1 + 1, h⟩ ^ s) *
        (ψ' j * e' T)) =
      polA k Q Λ' ν (X ⟨j, by omega⟩ ^ (a + Λ' r i) * X ⟨j + 1 + 1 + 1, h⟩ ^ s) * e' T := by
  rw [map_mul, map_pow, map_pow, polA_X, polA_X, ← mul_assoc,
    conjL Λ' j (by omega) T (by rw [hT0, hT1]; simp) a s ⟨j + 1 + 1 + 1, h⟩
      (by dsimp only; omega) (by dsimp only; omega),
    ← mul_assoc (ψ' _) (ψ' _), aψ_sq j (by omega) T, hT0, hT1]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, map_pow, rename_X,
    Matrix.cons_val_zero]
  simp only [← polA_X, ← map_pow, ← map_mul]
  rw [← mul_assoc, ← map_mul, pow_add]
  ring_nf

/-- The two triple-point corrections for a black strand crossing both red strands add up to the
correction for the merged red strand. -/
theorem middle_terms (j : ℕ) (h : j + 1 + 1 + 1 < m') (T : Seq (stendhalWeight (ℓ + 1) ν))
    (i : I) (r₁ r₂ : Fin (ℓ + 1)) (hT0 : T.lbl ⟨j, by omega⟩ = .inl i)
    (hT1 : T.lbl ⟨j + 1, by omega⟩ = .inr r₁) (hT2 : T.lbl ⟨j + 1 + 1, by omega⟩ = .inr r₂)
    (hT3 : T.lbl ⟨j + 1 + 1 + 1, h⟩ = .inl i) :
    ψ' (j + 1 + 1) * (polA k Q Λ' ν (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩,
        ⟨j + 1 + 1, by omega⟩] (qbar (X 0 ^ Λ' r₁ i))) * (ψ' (j + 1 + 1) * e' T)) +
      ψ' j * (polA k Q Λ' ν (rename ![⟨j + 1, by omega⟩, ⟨j + 1 + 1, by omega⟩,
        ⟨j + 1 + 1 + 1, h⟩] (qbar (X 0 ^ Λ' r₂ i))) * (ψ' j * e' T)) =
      polA k Q Λ' ν (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 1 + 1 + 1, h⟩]
        (qbar (X 0 ^ (Λ' r₁ i + Λ' r₂ i)))) * e' T := by
  rw [polA_rename_qbar_pow, polA_rename_qbar_pow, polA_rename_qbar_pow]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_range_add]
  congr 1 <;> refine Finset.sum_congr rfl fun t ht => ?_ <;> rw [Finset.mem_range] at ht
  · rw [term_right Λ' j h T i r₂ hT2 hT3,
      show Λ' r₁ i - 1 - t + Λ' r₂ i = Λ' r₁ i + Λ' r₂ i - 1 - t by omega]
  · rw [term_left Λ' j h T i r₁ hT0 hT1, add_comm t,
      show Λ' r₁ i + Λ' r₂ i - 1 - (Λ' r₁ i + t) = Λ' r₂ i - 1 - t by omega]

/-! ### Three crossings in the corner -/

omit [DecidableEq I] in
theorem lbl_sadj_sadj (T : Seq (stendhalWeight (ℓ + 1) ν)) {a b p r : ℕ} (ha : a + 1 < m')
    (hb : b + 1 < m') (hp : p < m') (hr : r < m') (h : swapNat b (swapNat a p) = r) :
    (sadj m' a • sadj m' b • T).lbl ⟨p, hp⟩ = T.lbl ⟨r, hr⟩ := by
  rw [lbl_sadj_smul _ ha, lbl_sadj_smul _ hb]; exact lbl_congr T h _ _

theorem e_mul_self (T : Seq (stendhalWeight (ℓ + 1) ν)) : e' T * e' T = e' T := by
  rw [ae_mul_e]; simp

theorem val_gΨ_gΨ_gΨ_gE (a b d : ℕ) (ha : a + 1 < m) (hb : b + 1 < m) (hd : d + 1 < m)
    (t : Seq μ) :
    (gΨ c Λ' a * gΨ c Λ' b * gΨ c Λ' d * gE c Λ' t : C).val =
      W Q Λ' ν a (swapNat b (swapNat d (redPos c t))) *
        (W Q Λ' ν b (swapNat d (redPos c t)) *
          (W Q Λ' ν d (redPos c t) * e' (splitLoading c t))) := by
  have h1 := gE_mul_gΨ_mul (k := k) (Q := Q) c Λ' d t (gE_mul_self c Λ' t)
  have h2 := gE_mul_gΨ_mul c Λ' b _ h1
  rw [mul_assoc, mul_assoc, val_gΨ_mul c Λ' a ha _ h2, val_gΨ_mul c Λ' b hb _ h1,
    val_gΨ_mul_gE c Λ' d hd, redPos_sadj_val c _ hb, redPos_sadj_val c t hd]

theorem rename_splitPos_triple (t : Seq μ) (a b d : Fin m) (P : MvPolynomial (Fin 3) k) :
    rename (splitPos c t) (rename ![a, b, d] P) =
      rename ![splitPos c t a, splitPos c t b, splitPos c t d] P := by
  rw [rename_rename]; congr 2; funext i; fin_cases i <;> rfl

/-- The braid relation `(ψ_j ψ_{j+1} ψ_j - ψ_{j+1} ψ_j ψ_{j+1}) e(t)`, with the correction
`Q̄_{t_j t_{j+1}}(x_j, x_{j+1}, x_{j+2}) e(t)` when `t_j = t_{j+2} ≠ t_{j+1}`, for the merged
weights. -/
theorem braid (j : ℕ) (h : j + 2 < m) (t : Seq μ) :
    ((gΨ c Λ' j * gΨ c Λ' (j + 1) * gΨ c Λ' j -
        gΨ c Λ' (j + 1) * gΨ c Λ' j * gΨ c Λ' (j + 1)) * gE c Λ' t : C) =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩ ∧
          t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, by omega⟩ then
        polSplit c Λ' (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (stendhalQ Q (mergeWeights c Λ') (t.lbl ⟨j, by omega⟩)
            (t.lbl ⟨j + 1, by omega⟩)))) * gE c Λ' t
      else 0 := by
  have hm := card_split ℓ ν
  have hq := (redPos c t).2
  apply Corner.ext
  have hval : (if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩ ∧
          t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, by omega⟩ then
        polSplit c Λ' (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (stendhalQ Q (mergeWeights c Λ') (t.lbl ⟨j, by omega⟩)
            (t.lbl ⟨j + 1, by omega⟩)))) * gE c Λ' t
      else 0 : C).val =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩ ∧
          t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, by omega⟩ then
        polA k Q Λ' ν (rename ![splitPos c t ⟨j, by omega⟩, splitPos c t ⟨j + 1, by omega⟩,
            splitPos c t ⟨j + 2, h⟩]
          (qbar (stendhalQ Q (mergeWeights c Λ') (t.lbl ⟨j, by omega⟩)
            (t.lbl ⟨j + 1, by omega⟩)))) * e' (splitLoading c t)
      else 0 := by
    split_ifs
    · rw [val_polSplit_mul c Λ' _ t (gE_mul_self c Λ' t), rename_splitPos_triple, val_gE]
    · simp
  rw [hval, sub_mul, Corner.val_sub, val_gΨ_gΨ_gΨ_gE c Λ' j (j + 1) j (by omega) (by omega)
    (by omega), val_gΨ_gΨ_gΨ_gE c Λ' (j + 1) j (j + 1) (by omega) (by omega) (by omega)]
  set q := (redPos c t : ℕ) with hqdef
  rcases Nat.lt_or_ge (j + 2) q with hfar | hle
  · -- the red strand is to the right
    have h' : j + 2 < m' := by omega
    have hj0 : t.lbl ⟨j, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hj1 : t.lbl ⟨j + 1, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hj2 : t.lbl ⟨j + 2, h⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have s0 : swapNat j q = q := swapNat_of_ne (by omega) (by omega)
    have s1 : swapNat (j + 1) q = q := swapNat_of_ne (by omega) (by omega)
    simp only [s0, s1, W_of_lt Λ' (show j + 1 < q by omega),
      W_of_lt Λ' (show j + 1 + 1 < q by omega)]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_mul,
      aBraid j h' (splitLoading c t),
      lbl_split_le c t j (by omega) (by omega), lbl_split_le c t (j + 1) (by omega) (by omega),
      lbl_split_le c t (j + 2) h (by omega),
      show splitPos c t ⟨j, by omega⟩ = ⟨j, by omega⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      show splitPos c t ⟨j + 1, by omega⟩ = ⟨j + 1, by omega⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      show splitPos c t ⟨j + 2, h⟩ = ⟨j + 2, h'⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      stendhalQ_splitColor c Λ' _ _ hj0 hj1]
    simp only [Ne, (splitColor_injective c).eq_iff]
  rcases Nat.lt_or_ge q j with hnear | hge
  · -- the red strand is to the left
    have h' : j + 3 < m' := by omega
    have hj0 : t.lbl ⟨j, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hj1 : t.lbl ⟨j + 1, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hj2 : t.lbl ⟨j + 2, h⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have s0 : swapNat j q = q := swapNat_of_ne (by omega) (by omega)
    have s1 : swapNat (j + 1) q = q := swapNat_of_ne (by omega) (by omega)
    simp only [s0, s1, W_of_gt Λ' (show q < j by omega), W_of_gt Λ' (show q < j + 1 by omega)]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_mul,
      aBraid (j + 1) h' (splitLoading c t),
      lbl_split_gt c t j (by omega) (by omega) (by omega),
      lbl_split_gt c t (j + 1) (by omega) (by omega) (by omega),
      lbl_split_gt c t (j + 2) h (by omega) (by omega),
      show splitPos c t ⟨j, by omega⟩ = ⟨j + 1, by omega⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      show splitPos c t ⟨j + 1, by omega⟩ = ⟨j + 1 + 1, by omega⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      show splitPos c t ⟨j + 2, h⟩ = ⟨j + 1 + 2, h'⟩ from Fin.ext (by
        rw [splitPos_val]; simp only; split_ifs <;> omega),
      stendhalQ_splitColor c Λ' _ _ hj0 hj1]
    simp only [Ne, (splitColor_injective c).eq_iff]
  have cAC : ∀ Z : A', ψ' j * (ψ' (j + 1 + 1) * Z) = ψ' (j + 1 + 1) * (ψ' j * Z) := fun Z => by
    rw [← mul_assoc, (cψ (k := k) (Q := Q) (ν := ν) Λ' j (j + 1 + 1) (Or.inl (by omega))).eq,
      mul_assoc]
  obtain hq0 | hq1 | hq2 : q = j ∨ q = j + 1 ∨ q = j + 2 := by omega
  · -- the red strand is the left strand of the triple point
    have h' : j + 3 < m' := by omega
    have hj0 : t.lbl ⟨j, by omega⟩ = .inr c := by rw [lbl_eq_red_iff]; simp only; omega
    have hj2 : t.lbl ⟨j + 2, h⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hcond : ¬ (t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩ ∧
        t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, by omega⟩) := fun hh => hj2 (hh.1 ▸ hj0)
    have s0 : swapNat j q = j + 1 := by rw [hq0]; exact swapNat_left j
    have s1 : swapNat (j + 1) q = q := swapNat_of_ne (by omega) (by omega)
    simp only [s0, s1, swapNat_left, W_of_lt Λ' (show j + 1 < j + 1 + 1 by omega),
      W_of_eq Λ' (show j + 1 = j + 1 from rfl), W_of_eq Λ' hq0.symm,
      W_of_gt Λ' (show q < j + 1 by omega), hcond, ↓reduceIte, sub_eq_zero, mul_assoc]
    set T := splitLoading c t
    have br1 := braid_of_ne Λ' j (by omega) (sadj m' (j + 1 + 1) • sadj m' (j + 1) • T)
      (by
        rw [lbl_sadj_sadj T (r := j) (by omega) (by omega) (by omega) (by omega)
            (by unfold swapNat; split_ifs <;> omega),
          lbl_sadj_sadj T (r := j + 2 + 1) (by omega) (by omega) (by omega) (by omega)
            (by unfold swapNat; split_ifs <;> omega),
          lbl_split_red c t (b := j) (by omega), lbl_split_gt c t (j + 2) h (by omega)]
        exact (splitColor_ne_red c _ hj2).symm)
      (ψ' (j + 1 + 1) * (ψ' (j + 1) * e' T)) (e_mul_ψψe Λ' (j + 1 + 1) (j + 1) T)
    have br2 := braid_of_ne Λ' (j + 1) (by omega) T
      (by
        rw [lbl_split_new c t (b := j + 1) (by omega),
          lbl_congr T (show j + 1 + 2 = j + 2 + 1 by omega) _ (by omega),
          lbl_split_gt c t (j + 2) h (by omega)]
        exact (splitColor_ne_new c _).symm)
      (e' T) (e_mul_self Λ' T)
    conv_lhs => rw [← cAC, br1, br2, cAC]
  · -- the red strand is the middle strand: the black strand `t_j` crosses both red strands
    have h' : j + 3 < m' := by omega
    have hj0 : t.lbl ⟨j, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hj1 : t.lbl ⟨j + 1, by omega⟩ = .inr c := by rw [lbl_eq_red_iff]; simp only; omega
    have hj2 : t.lbl ⟨j + 2, h⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have s0 : swapNat j q = j := by rw [hq1]; exact swapNat_right j
    have s1 : swapNat (j + 1) q = j + 1 + 1 := by rw [hq1]; exact swapNat_left (j + 1)
    simp only [s0, s1, swapNat_of_ne (j := j + 1) (q := j) (by omega) (by omega),
      swapNat_of_ne (j := j) (q := j + 1 + 1) (by omega) (by omega),
      W_of_eq Λ' (show j = j from rfl), W_of_gt Λ' (show j < j + 1 by omega),
      W_of_eq_succ Λ' (show j + 1 = q by omega),
      W_of_eq_succ Λ' (show j + 1 + 1 = j + 1 + 1 from rfl),
      W_of_lt Λ' (show j + 1 < j + 1 + 1 by omega), W_of_eq Λ' (show j + 1 = q by omega),
      mul_assoc]
    set T := splitLoading c t
    have hT0 : T.lbl ⟨j, by omega⟩ = splitColor c (t.lbl ⟨j, by omega⟩) :=
      lbl_split_le c t j (by omega) (by omega) (by omega)
    have hT1 : T.lbl ⟨j + 1, by omega⟩ = .inr c.castSucc := lbl_split_red c t (by omega) _
    have hT2 : T.lbl ⟨j + 2, by omega⟩ = .inr c.succ := lbl_split_new c t (by omega) _
    have hT3 : T.lbl ⟨j + 3, h'⟩ = splitColor c (t.lbl ⟨j + 2, h⟩) :=
      lbl_split_gt c t (j + 2) h (by omega) h'
    have hB1 := braid_mul Λ' (j + 1) (by omega) (sadj m' j • T) (ψ' j * e' T)
      (e_mul_ψe Λ' j T)
    rw [lbl_sadj_eq T (r := j) (p := j + 1) (by omega) (by omega) (by omega)
        (by unfold swapNat; split_ifs <;> omega),
      lbl_sadj_eq T (r := j + 2) (p := j + 1 + 1) (by omega) (by omega) (by omega)
        (by unfold swapNat; split_ifs <;> omega),
      lbl_sadj_eq T (r := j + 3) (p := j + 1 + 2) (by omega) (by omega) (by omega)
        (by unfold swapNat; split_ifs <;> omega), hT0, hT2, hT3] at hB1
    have hB0 := braid_mul Λ' j (by omega) (sadj m' (j + 1 + 1) • T) (ψ' (j + 1 + 1) * e' T)
      (e_mul_ψe Λ' (j + 1 + 1) T)
    rw [lbl_sadj_eq T (r := j) (p := j) (by omega) (by omega) (by omega)
        (by unfold swapNat; split_ifs <;> omega),
      lbl_sadj_eq T (r := j + 1) (p := j + 1) (by omega) (by omega) (by omega)
        (by unfold swapNat; split_ifs <;> omega),
      lbl_sadj_eq T (r := j + 3) (p := j + 2) (by omega) (by omega) (by omega)
        (by unfold swapNat; split_ifs <;> omega), hT0, hT1, hT3] at hB0
    conv_lhs => rw [hB1, mul_add, ← cAC (e' T),
      cAC (ψ' (j + 1) * (ψ' j * (ψ' (j + 1 + 1) * e' T))), hB0, mul_add]
    rw [add_assoc, add_sub_cancel_left]
    by_cases hc : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩
    · have hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, by omega⟩ := by rw [hj1]; exact hj0
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨congrArg _ hc, splitColor_ne_red c _ hj0⟩),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨congrArg _ hc, splitColor_ne_new c _⟩),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨hc, hne⟩), hj1,
        show splitPos c t ⟨j, by omega⟩ = ⟨j, by omega⟩ from Fin.ext (by
          rw [splitPos_val]; simp only; split_ifs <;> omega),
        show splitPos c t ⟨j + 1, by omega⟩ = ⟨j + 1, by omega⟩ from Fin.ext (by
          rw [splitPos_val]; simp only; split_ifs <;> omega),
        show splitPos c t ⟨j + 2, h⟩ = ⟨j + 1 + 1 + 1, h'⟩ from Fin.ext (by
          rw [splitPos_val]; simp only; split_ifs <;> omega)]
      rw [← hc] at hT3
      rcases hy : t.lbl ⟨j, by omega⟩ with i | r
      · rw [hy] at hT0 hT3
        simp only [splitColor_inl, stendhalQ_inl_inr, mergeWeights_self, Finsupp.add_apply]
        exact middle_terms Λ' j h' T i _ _ hT0 hT1 hT2 hT3
      · have hq0 : qbar (0 : MvPolynomial (Fin 2) k) = 0 := by
          have h0 := qbar_add (0 : MvPolynomial (Fin 2) k) 0
          rw [add_zero] at h0
          exact add_eq_left.1 h0.symm
        simp only [splitColor_inr, stendhalQ, hq0, map_zero, zero_mul, mul_zero, add_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hh => hc (splitColor_injective c hh.1)),
        ite_eq_right_of_eq_false _ _ (eq_false fun hh => hc (splitColor_injective c hh.1)),
        ite_eq_right_of_eq_false _ _ (eq_false fun hh => hc hh.1)]
      simp
  · -- the red strand is the right strand of the triple point
    have h' : j + 3 < m' := by omega
    have hj0 : t.lbl ⟨j, by omega⟩ ≠ .inr c := by rw [Ne, lbl_eq_red_iff]; simp only; omega
    have hj2 : t.lbl ⟨j + 2, h⟩ = .inr c := by rw [lbl_eq_red_iff]; simp only; omega
    have hcond : ¬ (t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩ ∧
        t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, by omega⟩) := fun hh => hj0 (hh.1 ▸ hj2)
    have s0 : swapNat j q = q := swapNat_of_ne (by omega) (by omega)
    have s1 : swapNat (j + 1) q = j + 1 := by rw [hq2]; exact swapNat_right (j + 1)
    simp only [s0, s1, swapNat_right, W_of_eq_succ Λ' (show j + 1 = j + 1 from rfl),
      W_of_eq_succ Λ' (show j + 1 + 1 = q by omega), W_of_lt Λ' (show j + 1 < q by omega),
      W_of_gt Λ' (show j < j + 1 by omega), hcond, ↓reduceIte, sub_eq_zero, mul_assoc]
    set T := splitLoading c t
    have br1 := braid_of_ne Λ' j (by omega) T
      (by
        rw [lbl_split_le c t j (by omega) (by omega), lbl_split_red c t (b := j + 2) (by omega)]
        exact splitColor_ne_red c _ hj0)
      (e' T) (e_mul_self Λ' T)
    have br2 := braid_of_ne Λ' (j + 1) (by omega) (sadj m' j • sadj m' (j + 1) • T)
      (by
        rw [lbl_sadj_sadj T (r := j) (by omega) (by omega) (by omega) (by omega)
            (by unfold swapNat; split_ifs <;> omega),
          lbl_sadj_sadj T (r := j + 3) (by omega) (by omega) (by omega) (by omega)
            (by unfold swapNat; split_ifs <;> omega),
          lbl_split_le c t j (by omega) (by omega), lbl_split_new c t (b := j + 3) (by omega)]
        exact splitColor_ne_new c _)
      (ψ' j * (ψ' (j + 1) * e' T)) (e_mul_ψψe Λ' j (j + 1) T)
    conv_lhs => rw [cAC, br1, br2, ← cAC]

end Categorification.Stendhal.SplitRed
