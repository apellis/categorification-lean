/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointInductionNeg

/-!
# The adjoint induction for `n ≤ 0`: Corollaries 3.2, 3.3 and Lemma 3.4 (CL Remark 3.11)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Remark 3.11 (`rem:nle0`): "We fix `n ≤ 0`. The induction hypothesis (3.2) is
now for `m < n`. Lemma 3.1 is now for `m ≤ n` [...]. Likewise, Corollary 3.2 is for `m ≤ n+2`."

Lemma 3.1 for `n ≤ 0` is `AdjointInductionNeg.lem1Neg_neg/zero`. Here:

* `cor0Neg_step`: the mirror of the dimension count of Corollary 3.2, obtained by moving the outer
  `E` of `E E 1_m` across its defining right adjoint and the inner one across the left adjoint
  given by (3.2) at `m - 2`: for `m = wt (s + 1)` with `m + 2 ≤ 0` and (3.2) at `m - 2`,
  `dim Hom(E E 1_m, E E 1_m ⟨l⟩) = dim Hom(E E 1_{m-2}, E E 1_{m-2} ⟨l + 2m + 2⟩)
    + ∑_{j=0}^{-m-1} dim Hom(E 1_m, E 1_m ⟨l + 2 - 2j⟩) + ∑_{j=0}^{-m-3} dim Hom(E 1_m, E 1_m ⟨l - 2j⟩)`.
* `cor0Neg_neg`, `cor0Neg_zero` (**Corollary 3.2 for `n ≤ 0`**): under (3.2) for all weights
  `< n ≤ 0`, if `m ≤ n` and `m ≤ -2` then `Hom(E E 1_m, E E 1_m ⟨l⟩)` is zero for `l < -2`, and
  one-dimensional for `l = -2` if `1_m ≠ 0`.
* `lemXXXNeg_neg`, `lemXXXNeg_zero` (**Lemma 3.4 for `n ≤ 0`**): under the same hypotheses, if
  `m ≤ n` then `Hom(E F 1_m, F E 1_m ⟨l⟩)` is zero for `l < 0` and one-dimensional for `l = 0` if
  `1_{m-2} ≠ 0` (by `lemXXX_eq`, which needs no induction hypothesis, and Corollary 3.2 at `m - 2`).
* `cor2Neg` (**the mirror of Corollary 3.3**): under the same hypotheses, if `m ≤ n` and
  `1_{m-2} ≠ 0` then `Hom(F 1_m, F F E 1_m ⟨m - 1⟩) ≅ k` (`F 1_m : m → m - 2`,
  `F F E 1_m : m → m + 2 → m → m - 2`); by the definition of `F` this is `Hom(E F 1_m, F E 1_m)`.

## Precision about Remark 3.11

* The range "Corollary 3.2 is for `m ≤ n + 2`" is not what the mirror argument gives. The count
  above uses (3.2) at `m - 2` (so `m - 2 < n`), Lemma 3.1 at `m` (so `m ≤ n`) and condition (3) at
  the weights `m` and `m + 2` in the form `F E ≅ E F ⊕ [·] 1` (so `m + 2 ≤ 0`): the mirror of
  "`m ≥ n - 2`" is "`m + 2 ≤ n + 2`", i.e. `m ≤ n`, and the induction only covers `m ≤ -2`. For
  `n ≤ -2` this is exactly `m ≤ n`; for `n ∈ {-1, 0}` the weights `m ∈ {-1, 0}` are not covered by
  the `n ≤ 0` count (there `E E 1_m` has top weight `m + 4 ≥ 3`, and CL's `n ≥ 0` argument applies
  instead, under (3.2) at the weights `≥ m + 4`).
* The mirror of Lemma 3.4 obtained here is the *same* Hom space `Hom(E F 1_m, F E 1_m ⟨l⟩)` in the
  range `m ≤ n`; the "other" space `Hom(F E 1_m, E F 1_m ⟨l⟩)` at `m = n` is not accessible
  from (3.2) at the weights `< n` alone (every adjunction moving a factor of `F E 1_n` needs
  either `(E 1_n)_L` or `(1_{n-2} F)_R`, i.e. (3.2) at `n`; see `Biadjoint.lemHoms_FE_EF`), which
  is why CL's Remark 3.11 defines the map `F E 1_{n+2} → E F 1_{n+2}` for `n ≤ -2` by the
  decomposition of `F E 1_{n+2}` rather than by a uniqueness statement.

Indexing: `E E 1_m = E (s + 1) ≫ E (s + 1 + 1)` with `m = wt (s + 1)`; `E F 1_m = F r ≫ E r`,
`F E 1_m = E (r + 1) ≫ F (r + 1)`, `F 1_m = F r`, `F F E 1_m = E (r + 1) ≫ F (r + 1) ≫ F r` with
`m = wt (r + 1)`.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B)

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `F ≫ Z ≅ F⟦-p⟧ ≫ Z⟦p⟧`. -/
def compIsoShiftCompShift {a b c : B} (F : a ⟶ b) (Z : b ⟶ c) (p : ℤ) :
    F ≫ Z ≅ F⟦-p⟧ ≫ Z⟦p⟧ :=
  ((shiftFunctorZero _ ℤ).app (F ≫ Z)).symm ≪≫
    (shiftCompShiftIso F Z (p := -p) (q := p) (s := 0) (by ring)).symm

/-- The dimension count of Corollary 3.2 for `n ≤ 0`: for `m = wt (s + 1)` with `m + 2 ≤ 0`,
given the left adjoint of `E 1_{m-2}` ((3.2) at `m - 2`),
`dim Hom(E E 1_m, E E 1_m ⟨l⟩) = dim Hom(E E 1_{m-2}, E E 1_{m-2} ⟨l + 2m + 2⟩)
  + ∑_{j=0}^{-m-1} dim Hom(E 1_m, E 1_m ⟨l + 2 - 2j⟩) + ∑_{j=0}^{-m-3} dim Hom(E 1_m, E 1_m ⟨l - 2j⟩)`. -/
theorem cor0Neg_step {s : ℤ} (hs : S.wt (s + 1 + 1) ≤ 0) (h : S.AdjHyp s) (l : ℤ) :
    finrank k (S.E (s + 1) ≫ S.E (s + 1 + 1) ⟶ (S.E (s + 1) ≫ S.E (s + 1 + 1))⟦l⟧) =
      finrank k (S.E s ≫ S.E (s + 1) ⟶ (S.E s ≫ S.E (s + 1))⟦l + 2 * S.wt (s + 1) + 2⟧) +
        ∑ j ∈ Finset.range (-S.wt (s + 1)).toNat,
          finrank k (S.E (s + 1) ⟶ (S.E (s + 1))⟦l + 2 - 2 * (j : ℤ)⟧) +
        ∑ j ∈ Finset.range (-S.wt (s + 1 + 1)).toNat,
          finrank k (S.E (s + 1) ⟶ (S.E (s + 1))⟦l - 2 * (j : ℤ)⟧) := by
  have hw1 : S.wt (s + 1) = S.wt s + 2 := S.wt_add_one s
  have hw2 : S.wt (s + 1 + 1) = S.wt s + 4 := by rw [S.wt_add_one, hw1]; ring
  have hM1 : ((-S.wt (s + 1)).toNat : ℤ) = -S.wt (s + 1) := Int.toNat_of_nonneg (by omega)
  have hM2 : ((-S.wt (s + 1 + 1)).toNat : ℤ) = -S.wt (s + 1 + 1) :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨e₂⟩ := S.FE (s + 1) hs
  obtain ⟨e₁⟩ := S.FE s (by change S.wt (s + 1) ≤ 0; omega)
  -- the decomposition of `E (E F) 1_m` (Mathlib: `E1 ≫ (E2 ≫ F2)`)
  have i : S.E (s + 1) ≫ (S.E (s + 1 + 1) ≫ S.F (s + 1 + 1)) ≅
      (((S.F s ≫ S.E s) ≫ S.E (s + 1)) ⊞ qsum 1 (-S.wt (s + 1)).toNat (S.E (s + 1))) ⊞
        qsum 1 (-S.wt (s + 1 + 1)).toNat (S.E (s + 1)) :=
    whiskerLeftIso _ e₂ ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
      biprod.mapIso ((α_ _ _ _).symm ≪≫ whiskerRightIso e₁ _ ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
        biprod.mapIso (Iso.refl _) (qsumCompIso _ _ _)) (compQsumIso _ _ _)
  calc finrank k (S.E (s + 1) ≫ S.E (s + 1 + 1) ⟶ (S.E (s + 1) ≫ S.E (s + 1 + 1))⟦l⟧)
      = finrank k (S.E (s + 1) ≫ S.E (s + 1 + 1) ⟶ S.E (s + 1) ≫ (S.E (s + 1 + 1))⟦l⟧) :=
        finrank_hom_congr_right k _ (whiskerLeftShiftIso _ _ _).symm
    _ = finrank k (S.E (s + 1) ⟶ (S.E (s + 1) ≫ (S.E (s + 1 + 1))⟦l⟧) ≫
          (S.F (s + 1 + 1))⟦S.wt (s + 1 + 1) + 1⟧) :=
        (S.dimAdj (s + 1 + 1)).left _ _
    _ = finrank k (S.E (s + 1) ⟶
          (S.E (s + 1) ≫ (S.E (s + 1 + 1) ≫ S.F (s + 1 + 1)))⟦S.wt (s + 1 + 1) + 1 + l⟧) :=
        finrank_hom_congr_right k _ (α_ _ _ _ ≪≫
          whiskerLeftIso _ (shiftCompShiftIso _ _ (p := l) (q := S.wt (s + 1 + 1) + 1)
            (s := S.wt (s + 1 + 1) + 1 + l) rfl) ≪≫
          whiskerLeftShiftIso _ _ _)
    _ = finrank k ((S.E (s + 1))⟦-(S.wt (s + 1 + 1) + 1 + l)⟧ ⟶
          S.E (s + 1) ≫ (S.E (s + 1 + 1) ≫ S.F (s + 1 + 1))) :=
        finrank_hom_shift_right k _ _ (by ring)
    _ = finrank k ((S.E (s + 1))⟦-(S.wt (s + 1 + 1) + 1 + l)⟧ ⟶
          (((S.F s ≫ S.E s) ≫ S.E (s + 1)) ⊞ qsum 1 (-S.wt (s + 1)).toNat (S.E (s + 1))) ⊞
            qsum 1 (-S.wt (s + 1 + 1)).toNat (S.E (s + 1))) :=
        finrank_hom_congr_right k _ i
    _ = _ := by
      rw [finrank_hom_biprod_right, finrank_hom_biprod_right, finrank_hom_qsum_right,
        finrank_hom_qsum_right]
      refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
      · -- the term `Hom(E 1_m ⟨-t⟩, F E E 1_m)`: move `F` by its left adjoint, (3.2) at `m - 2`
        rw [finrank_hom_congr_right k _ (α_ _ _ _ ≪≫
            compIsoShiftCompShift (S.F s) (S.E s ≫ S.E (s + 1)) (S.wt s + 1)),
          (h.dimAdj S).right, finrank_hom_congr_left k (whiskerLeftShiftIso _ _ _),
          finrank_hom_shift_shift k _ _ (c := l + 2 * S.wt (s + 1) + 2) (by omega)]
      · refine Finset.sum_congr rfl fun j _ => finrank_hom_shift_shift k _ _ ?_
        change _ + -(S.wt (s + 1 + 1) + 1 + l) =
          1 * (((-S.wt (s + 1)).toNat : ℤ) - 1 - 2 * (j : ℤ))
        rw [hM1]; omega
      · refine Finset.sum_congr rfl fun j _ => finrank_hom_shift_shift k _ _ ?_
        change _ + -(S.wt (s + 1 + 1) + 1 + l) =
          1 * (((-S.wt (s + 1 + 1)).toNat : ℤ) - 1 - 2 * (j : ℤ))
        rw [hM2]; omega

/-- **Corollary 3.2 for `n ≤ 0`** (CL Remark 3.11), degrees `< -2`: assuming (3.2) for all weights
`< n = wt r₁ ≤ 0`, if `m = wt r ≤ n` and `m ≤ -2` then `Hom(E E 1_m, E E 1_m ⟨l⟩) = 0` for
`l < -2`. (By increasing induction on `m`.) -/
theorem cor0Neg_neg {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') :
    ∀ r, r ≤ r₁ → S.wt (r + 1) ≤ 0 → ∀ l : ℤ, l < -2 →
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) = 0 := by
  refine S.increasing_induction (P := fun r => r ≤ r₁ → S.wt (r + 1) ≤ 0 → ∀ l : ℤ, l < -2 →
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) = 0) ?_ ?_
  · intro r h _ _ l _
    exact finrank_hom_of_isZero_left k (isZero_comp_left (S.isZero_E_of_left h) _) _
  · intro r ih hr hw l hl
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
    have hw1 : S.wt (s + 1 + 1) = S.wt (s + 1) + 2 := S.wt_add_one _
    rw [S.cor0Neg_step hw (hyp s (by omega)) l, ih s (by omega) (by omega) (by omega) _ (by omega),
      zero_add, Finset.sum_eq_zero fun j _ => S.lem1Neg_neg hn hyp (s + 1) hr _ (by omega),
      Finset.sum_eq_zero fun j _ => S.lem1Neg_neg hn hyp (s + 1) hr _ (by omega), add_zero]

/-- **Corollary 3.2 for `n ≤ 0`** (CL Remark 3.11), degree `-2`: under the same hypotheses, if
`m = wt r ≤ n`, `m ≤ -2` and `1_m ≠ 0` then `Hom(E E 1_m, E E 1_m ⟨-2⟩)` is one-dimensional. -/
theorem cor0Neg_zero {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') {r : ℤ}
    (hr : r ≤ r₁) (hw : S.wt (r + 1) ≤ 0) (h : ¬ IsZero (𝟙 (S.obj r))) :
    finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦-2⟧) = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
  have hw1 : S.wt (s + 1 + 1) = S.wt (s + 1) + 2 := S.wt_add_one _
  have hM1 : ((-S.wt (s + 1)).toNat : ℤ) = -S.wt (s + 1) := Int.toNat_of_nonneg (by omega)
  rw [S.cor0Neg_step hw (hyp s (by omega)) (-2),
    S.cor0Neg_neg hn hyp s (by omega) (by omega) _ (by omega), zero_add,
    Finset.sum_eq_zero (s := Finset.range (-S.wt (s + 1 + 1)).toNat), add_zero,
    Finset.sum_eq_single 0]
  · rw [finrank_hom_shift_zero k _ _ (by simp)]
    exact S.lem1Neg_zero hn hyp hr (by omega) h
  · intro j _ hj
    exact S.lem1Neg_neg hn hyp (s + 1) hr _ (by omega)
  · intro hj
    rw [Finset.mem_range] at hj
    omega
  · intro j _
    exact S.lem1Neg_neg hn hyp (s + 1) hr _ (by omega)

/-- **Lemma 3.4 for `n ≤ 0`**, negative degrees: assuming (3.2) for all weights `< n = wt r₁ ≤ 0`,
if `m = wt (r + 1) ≤ n` then `Hom(E F 1_m, F E 1_m ⟨l⟩) = 0` for `l < 0`. -/
theorem lemXXXNeg_neg {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') {r : ℤ}
    (hr : r + 1 ≤ r₁) {l : ℤ} (hl : l < 0) :
    finrank k (S.F r ≫ S.E r ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦l⟧) = 0 := by
  rw [lemXXX_eq]
  exact S.cor0Neg_neg hn hyp r (by omega) (le_trans (S.wt_le_wt hr) hn) _ (by omega)

/-- **Lemma 3.4 for `n ≤ 0`**, degree zero: under the same hypotheses, if moreover `1_{m-2} ≠ 0`
then `Hom(E F 1_m, F E 1_m)` is one-dimensional. -/
theorem lemXXXNeg_zero {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') {r : ℤ}
    (hr : r + 1 ≤ r₁) (h : ¬ IsZero (𝟙 (S.obj r))) :
    finrank k (S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1)) = 1 := by
  rw [← finrank_hom_shift_zero k _ _ (rfl : (0 : ℤ) = 0), lemXXX_eq,
    finrank_hom_shift_congr k _ _ (by norm_num : (0 : ℤ) - 2 = -2)]
  exact S.cor0Neg_zero hn hyp (by omega) (le_trans (S.wt_le_wt hr) hn) h

/-- **The mirror of Corollary 3.3 for `n ≤ 0`**: assuming (3.2) for all weights `< n = wt r₁ ≤ 0`,
if `m = wt (r + 1) ≤ n` and `1_{m-2} ≠ 0` then `Hom(F 1_m, F F E 1_m ⟨m - 1⟩)` is one-dimensional
(`F 1_m = F r`, `F F E 1_m = E (r + 1) ≫ F (r + 1) ≫ F r`). By the definition of `F` this is
`Hom(E F 1_m, F E 1_m)`, Lemma 3.4. -/
theorem cor2Neg {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') {r : ℤ}
    (hr : r + 1 ≤ r₁) (h : ¬ IsZero (𝟙 (S.obj r))) :
    finrank k (S.F r ⟶ (S.E (r + 1) ≫ S.F (r + 1) ≫ S.F r)⟦S.wt (r + 1) - 1⟧) = 1 := by
  have hp : S.wt (r + 1) - 1 = S.wt r + 1 := by rw [S.wt_add_one]; ring
  rw [hp, finrank_hom_congr_right k _ ((shiftFunctor _ _).mapIso (α_ _ _ _).symm ≪≫
      (whiskerLeftShiftIso _ _ _).symm), ← (S.dimAdj r).left]
  exact S.lemXXXNeg_zero hn hyp hr h

end Categorification.TwoRep.StrongSl2
