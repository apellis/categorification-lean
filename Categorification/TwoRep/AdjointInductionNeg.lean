/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointInduction

/-!
# The adjoint induction for `n ≤ 0`: Lemma 3.1 (CL Remark 3.11)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Remark 3.11 (`rem:nle0`): "We fix `n ≤ 0`. The induction hypothesis (3.2) is
now for `m < n`. Lemma 3.1 is now for `m ≤ n` and one proves it by moving the `E` by adjunction
from the left side to the right side."

* `lem1Neg_step`: the dimension count: for `m = wt (s + 1) ≤ 0`, given
  `(E 1_{m-2})_L ≅ 1_{m-2} F ⟨1-m⟩`,
  `dim Hom(E 1_m, E 1_m ⟨l⟩) = dim Hom(E 1_{m-2}, E 1_{m-2} ⟨l + 2m⟩) +
    ∑_{j=0}^{-m-1} dim Hom(1_m, 1_m ⟨l - 2j⟩)`.
* `lem1Neg_neg`, `lem1Neg_zero` (**Lemma 3.1 for `n ≤ 0`**): under (3.2) for all weights `< n ≤ 0`,
  if `m ≤ n` then `Hom(E 1_m, E 1_m ⟨l⟩) = 0` for `l < 0`, and it is one-dimensional for `l = 0`
  if moreover `m ≤ -1` and `1_m` is nonzero. (For `m = 0` the count gives
  `dim End(E 1_0) = dim End(E 1_{-2})`, `lem1Neg_step`; one-dimensionality there is the `n ≥ 0`
  half, `lem1_zero`, which uses `1_2 ≠ 0`.)
* `finrank_End_E_eq_one`: combining both halves, if (3.2) holds at every weight (the conclusion of
  Proposition 3.9 for all `n`), then `End(E 1_m)` is one-dimensional for every `m` such that the
  weights `m` and `m + 2` are nonzero.
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

/-- The dimension count of Lemma 3.1 for `n ≤ 0` ("moving the `E` by adjunction from the left side
to the right side"): for `m = wt (s + 1) ≤ 0`, given the left adjoint of `E 1_{m-2}`,
`dim Hom(E 1_m, E 1_m ⟨l⟩) = dim Hom(E 1_{m-2}, E 1_{m-2} ⟨l + 2m⟩) +
∑_{j=0}^{-m-1} dim Hom(1_m, 1_m ⟨l - 2j⟩)`. -/
theorem lem1Neg_step {s : ℤ} (hs : S.wt (s + 1) ≤ 0) (h : S.AdjHyp s) (l : ℤ) :
    finrank k (S.E (s + 1) ⟶ (S.E (s + 1))⟦l⟧) =
      finrank k (S.E s ⟶ (S.E s)⟦l + 2 * S.wt (s + 1)⟧) +
        ∑ j ∈ Finset.range (-S.wt (s + 1)).toNat,
          finrank k (𝟙 (S.obj (s + 1)) ⟶ (𝟙 (S.obj (s + 1)))⟦l - 2 * (j : ℤ)⟧) := by
  have hw : S.wt (s + 1) = S.wt s + 2 := S.wt_add_one s
  have hM : ((-S.wt (s + 1)).toNat : ℤ) = -S.wt (s + 1) := Int.toNat_of_nonneg (by omega)
  obtain ⟨e⟩ := S.FE s hs
  calc finrank k (S.E (s + 1) ⟶ (S.E (s + 1))⟦l⟧)
      = finrank k (𝟙 _ ≫ S.E (s + 1) ⟶ (S.E (s + 1))⟦l⟧) :=
        finrank_hom_congr_left k (λ_ _).symm _
    _ = finrank k (𝟙 (S.obj (s + 1)) ⟶ (S.E (s + 1))⟦l⟧ ≫ (S.F (s + 1))⟦S.wt (s + 1) + 1⟧) :=
        (S.dimAdj (s + 1)).left _ _
    _ = finrank k (𝟙 (S.obj (s + 1)) ⟶ (S.E (s + 1) ≫ S.F (s + 1))⟦l + (S.wt (s + 1) + 1)⟧) :=
        finrank_hom_congr_right k _ (shiftCompShiftIso _ _ (by ring))
    _ = finrank k ((𝟙 (S.obj (s + 1)))⟦-(l + (S.wt (s + 1) + 1))⟧ ⟶ S.E (s + 1) ≫ S.F (s + 1)) :=
        finrank_hom_shift_right k _ _ (by ring)
    _ = finrank k ((𝟙 (S.obj (s + 1)))⟦-(l + (S.wt (s + 1) + 1))⟧ ⟶
          (S.F s ≫ S.E s) ⊞ qsum 1 (-S.wt (s + 1)).toNat (𝟙 (S.obj (s + 1)))) :=
        finrank_hom_congr_right k _ e
    _ = _ := by
      rw [finrank_hom_biprod_right, finrank_hom_qsum_right, ← (h.dimAdj S).left,
        finrank_hom_congr_left k (idShiftCompShiftIso (p := -(l + (S.wt (s + 1) + 1)))
          (q := -(S.wt s + 1)) (s := -(l + (S.wt (s + 1) + 1)) + -(S.wt s + 1)) (S.F s)
          (by ring)),
        finrank_hom_shift_left k _ _ (b := l + 2 * S.wt (s + 1)) (by rw [hw]; ring),
        finrank_F_F_eq]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      exact finrank_hom_shift_shift k _ _ (c := l - 2 * (j : ℤ)) (by rw [hM]; ring)

/-- **Lemma 3.1 for `n ≤ 0`** (CL Remark 3.11), negative degrees: assuming the adjoint induction
hypothesis (3.2) for all weights `< n = wt r₁ ≤ 0`, if `m ≤ n` then `Hom(E 1_m, E 1_m ⟨l⟩) = 0`
for `l < 0`. (By increasing induction on `m`.) -/
theorem lem1Neg_neg {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') :
    ∀ r, r ≤ r₁ → ∀ l : ℤ, l < 0 → finrank k (S.E r ⟶ (S.E r)⟦l⟧) = 0 := by
  refine S.increasing_induction
    (P := fun r => r ≤ r₁ → ∀ l : ℤ, l < 0 → finrank k (S.E r ⟶ (S.E r)⟦l⟧) = 0) ?_ ?_
  · intro r h _ l _
    exact finrank_hom_of_isZero_left k (S.isZero_E_of_left h) _
  · intro r ih hr l hl
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
    have hw : S.wt (s + 1) ≤ 0 := le_trans (S.wt_le_wt hr) hn
    rw [S.lem1Neg_step hw (hyp s (by omega)) l, ih s (by omega) (by omega) _ (by omega),
      zero_add]
    refine Finset.sum_eq_zero fun j _ => S.hom_neg _ _ (by omega)

/-- **Lemma 3.1 for `n ≤ 0`** (CL Remark 3.11), degree zero: under the same hypotheses, if
`m ≤ min(n, -1)` and the weight `m` is nonzero, `End(E 1_m)` is one-dimensional. -/
theorem lem1Neg_zero {r₁ : ℤ} (hn : S.wt r₁ ≤ 0) (hyp : ∀ r', r' < r₁ → S.AdjHyp r') {r : ℤ}
    (hr : r ≤ r₁) (hr' : S.wt r ≤ -1) (h : ¬ IsZero (𝟙 (S.obj r))) :
    finrank k (S.E r ⟶ S.E r) = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
  have hM : ((-S.wt (s + 1)).toNat : ℤ) = -S.wt (s + 1) := Int.toNat_of_nonneg (by omega)
  rw [← finrank_hom_shift_zero k _ _ (rfl : (0 : ℤ) = 0),
    S.lem1Neg_step (by omega) (hyp s (by omega)) 0,
    S.lem1Neg_neg hn hyp s (by omega) _ (by omega), zero_add, Finset.sum_eq_single 0]
  · rw [finrank_hom_shift_zero k _ _ (by simp)]
    exact S.hom_zero _ h
  · intro j hj hne
    exact S.hom_neg _ _ (by omega)
  · intro hj
    rw [Finset.mem_range] at hj
    omega

/-- **`E 1_m` is a brick for every nonzero weight pair**: if the adjoint induction hypothesis (3.2)
holds at every weight (the conclusion of Proposition 3.9 for all `n`), then `End(E 1_m)` is
one-dimensional whenever `1_m` and `1_{m+2}` are nonzero. -/
theorem finrank_End_E_eq_one (hall : ∀ r, S.AdjHyp r) {r : ℤ} (h₀ : ¬ IsZero (𝟙 (S.obj r)))
    (h₁ : ¬ IsZero (𝟙 (S.obj (r + 1)))) : finrank k (S.E r ⟶ S.E r) = 1 := by
  by_cases hr : 0 ≤ S.wt r
  · exact S.lem1_zero hr (fun r' _ => hall r') le_rfl h₁
  · exact S.lem1Neg_zero (le_of_lt (not_le.1 hr)) (fun r' _ => hall r') le_rfl (by omega) h₀

end Categorification.TwoRep.StrongSl2
