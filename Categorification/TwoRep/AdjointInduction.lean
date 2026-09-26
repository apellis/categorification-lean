/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Sl2

/-!
# Consequences of the adjoint induction hypothesis (CL §3.2)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.2 (`The adjoint induction hypothesis and its consequences`).

Fix a strong 2-representation `S` of `sl₂` along a weight string (`StrongSl2`), an object `r₀`
of weight `n = wt r₀ ≥ 0`, and assume the adjoint induction hypothesis `eq:ind_hyp` for all
weights `m > n` (`∀ r', r₀ < r' → S.AdjHyp r'`). We prove:

* `lem1_neg`, `lem1_zero` (**Lemma 3.1**, `lem:1`): if `m ≥ n` then `Hom(E 1_m, E 1_m ⟨l⟩)` is
  zero for `l < 0` and one-dimensional for `l = 0`; `finrank_F_F_eq` gives the same for `1_m F`
  ("the result for `F` follows by adjunction"; this needs no induction hypothesis).
* `cor0_neg`, `cor0_zero` (**Corollary 3.2**, `cor:0`): if `m ≥ n - 2` then
  `Hom(E E 1_m, E E 1_m ⟨l⟩)` is zero for `l < -2` and one-dimensional for `l = -2`.
* `cor2` (**Corollary 3.3**, `cor:2`): if `m ≥ n` then `Hom(E 1_m, E E F 1_m ⟨-m-1⟩) ≅ k`.
* `lemXXX_neg`, `lemXXX_zero` (**Lemma 3.4**, `lem:XXX`): if `m ≥ n` then
  `Hom(E F 1_m, F E 1_m ⟨l⟩)` is zero for `l < 0` and one-dimensional for `l = 0`.

Each is proved by the dimension count in CL's proof, which moves 1-morphisms across adjunctions
(`DimAdj`), splits `E F 1_{m}` by condition (3) (`StrongSl2.EF`) and uses condition (2)
(`hom_neg`, `hom_zero`) or the previous results; Lemma 3.1 and Corollary 3.2 are by decreasing
induction on `m` (`StrongSl2.decreasing_induction`), with the zero objects beyond the highest
weight as base case.

## The zero-object convention

CL's "Important convention" (after Definition 1.2): "any statement about a certain Hom being
non-zero (for example, the claims in lemma 3.1 or corollaries 3.2 and 3.3) assumes that all weights
involved are non-zero". The one-dimensionality statements below assume exactly the nonvanishing
that the dimension count uses: `1_{m+2}` nonzero in Lemma 3.1 (`E 1_m : m → m + 2`), `1_{m+4}`
in Corollary 3.2 and Lemma 3.4 for the top weight of `E E 1_m`, `1_{m+2}` in Corollary 3.3. (In
fact nonvanishing of the top weight forces that of the lower ones in this range, by condition (3).)

## Indexing

Object `r` has weight `wt r`; CL's `E 1_m`, `1_m F`, `E F 1_m`, `F E 1_m`, `E E 1_m` at
`m = wt r` are `E r`, `F (r - 1)`, `F (r - 1) ≫ E (r - 1)`, `E r ≫ F r`, `E r ≫ E (r + 1)`; to
avoid `r - 1 + 1`, statements about `E F 1_m`, `F E 1_m`, `E E F 1_m` are made at the object
`r + 1`, with `m = wt (r + 1)`.
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

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `(S.wt (r + 1)).toNat = wt r + 2` as integers, when `wt r ≥ -2`. -/
theorem toNat_wt_succ {r : ℤ} (hr : -2 ≤ S.wt r) : ((S.wt (r + 1)).toNat : ℤ) = S.wt r + 2 := by
  rw [Int.toNat_of_nonneg (by rw [wt_add_one]; omega), wt_add_one]

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The first step of CL's proof of Lemma 3.1: `Hom(E 1_m, E 1_m ⟨l⟩) ≅
Hom(E (E 1_m)_R 1_{m+2}, 1_{m+2} ⟨l⟩) ≅ Hom(E F 1_{m+2} ⟨m+1⟩, 1_{m+2} ⟨l⟩)`. -/
theorem finrank_E_E (r l : ℤ) :
    finrank k (S.E r ⟶ (S.E r)⟦l⟧) =
      finrank k (S.F r ≫ S.E r ⟶ (𝟙 (S.obj (r + 1)))⟦l - (S.wt r + 1)⟧) :=
  calc finrank k (S.E r ⟶ (S.E r)⟦l⟧)
      = finrank k (S.E r ⟶ S.E r ≫ (𝟙 (S.obj (r + 1)))⟦l⟧) :=
        finrank_hom_congr_right k _ (compIdShiftIso (S.E r) l).symm
    _ = finrank k ((S.F r)⟦S.wt r + 1⟧ ≫ S.E r ⟶ (𝟙 (S.obj (r + 1)))⟦l⟧) :=
        (S.dimAdj r).right _ _
    _ = finrank k ((S.F r ≫ S.E r)⟦S.wt r + 1⟧ ⟶ (𝟙 (S.obj (r + 1)))⟦l⟧) :=
        finrank_hom_congr_left k (whiskerRightShiftIso _ _ _) _
    _ = _ := finrank_hom_shift_shift k _ _ (by ring)

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The same space for `1_m F`: `Hom(1_m F, 1_m F ⟨l⟩) ≅ Hom(E F 1_{m+2} ⟨m+1⟩, 1_{m+2} ⟨l⟩)`, using
`(1_m F)_L = E 1_m ⟨m+1⟩`. -/
theorem finrank_F_F (r l : ℤ) :
    finrank k (S.F r ⟶ (S.F r)⟦l⟧) =
      finrank k (S.F r ≫ S.E r ⟶ (𝟙 (S.obj (r + 1)))⟦l - (S.wt r + 1)⟧) :=
  calc finrank k (S.F r ⟶ (S.F r)⟦l⟧)
      = finrank k (S.F r ⟶ (𝟙 (S.obj (r + 1)))⟦l⟧ ≫ S.F r) :=
        finrank_hom_congr_right k _ (idShiftCompIso (S.F r) l).symm
    _ = finrank k (S.F r ≫ (S.E r)⟦S.wt r + 1⟧ ⟶ (𝟙 (S.obj (r + 1)))⟦l⟧) :=
        ((S.dimAdj_EF r).left _ _).symm
    _ = finrank k ((S.F r ≫ S.E r)⟦S.wt r + 1⟧ ⟶ (𝟙 (S.obj (r + 1)))⟦l⟧) :=
        finrank_hom_congr_left k (whiskerLeftShiftIso _ _ _) _
    _ = _ := finrank_hom_shift_shift k _ _ (by ring)

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- **Lemma 3.1 for `F`** ("the result for `F` follows by adjunction"):
`dim Hom(1_m F, 1_m F ⟨l⟩) = dim Hom(E 1_m, E 1_m ⟨l⟩)` for every weight and every `l`. -/
theorem finrank_F_F_eq (r l : ℤ) :
    finrank k (S.F r ⟶ (S.F r)⟦l⟧) = finrank k (S.E r ⟶ (S.E r)⟦l⟧) := by
  rw [finrank_E_E, finrank_F_F]

/-- The dimension count in CL's proof of Lemma 3.1: for `m = wt r ≥ -2`, under the hypothesis
`(E 1_{m+2})_L ≅ 1_{m+2} F ⟨-m-3⟩`,
`dim Hom(E 1_m, E 1_m ⟨l⟩) = dim Hom(E 1_{m+2}, E 1_{m+2} ⟨l-2m-4⟩) +
  ∑_{j=0}^{m+1} dim Hom(1_{m+2}, 1_{m+2} ⟨l-2m-2+2j⟩)`. -/
theorem lem1_step {r : ℤ} (hr : -2 ≤ S.wt r) (h1 : S.AdjHyp (r + 1)) (l : ℤ) :
    finrank k (S.E r ⟶ (S.E r)⟦l⟧) =
      finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦l - 2 * S.wt r - 4⟧) +
        ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
          finrank k (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦l - 2 * S.wt r - 2 + 2 * (j : ℤ)⟧) := by
  have hw : S.wt (r + 1) = S.wt r + 2 := S.wt_add_one r
  have hM := S.toNat_wt_succ hr
  obtain ⟨e⟩ := S.EF r (by rw [← wt, hw]; omega)
  rw [finrank_E_E, finrank_hom_congr_left k e, finrank_hom_biprod_left, finrank_hom_qsum_left]
  congr 1
  · rw [(h1.dimAdjF S).left, finrank_hom_congr_right k _
      (idShiftCompShiftIso (p := l - (S.wt r + 1)) (q := -(S.wt (r + 1) + 1))
        (s := l - 2 * S.wt r - 4) (S.E (r + 1)) (by rw [hw]; ring))]
  · refine Finset.sum_congr rfl fun j _ => finrank_hom_shift_shift k _ _ ?_
    change _ + 1 * (((S.wt (r + 1)).toNat : ℤ) - 1 - 2 * (j : ℤ)) = _
    rw [hM]; ring

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem wt_le_wt {r r' : ℤ} (h : r ≤ r') : S.wt r ≤ S.wt r' := by simp only [wt]; omega

/-- **Lemma 3.1** (CL `lem:1`), negative degrees: assuming the adjoint induction hypothesis
`eq:ind_hyp` for all weights `> n = wt r₀ ≥ 0`, if `m ≥ n` then `Hom(E 1_m, E 1_m ⟨l⟩) = 0` for
`l < 0`. (By decreasing induction on `m`.) -/
theorem lem1_neg {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') :
    ∀ r, r₀ ≤ r → ∀ l : ℤ, l < 0 → finrank k (S.E r ⟶ (S.E r)⟦l⟧) = 0 := by
  refine S.decreasing_induction
    (P := fun r => r₀ ≤ r → ∀ l : ℤ, l < 0 → finrank k (S.E r ⟶ (S.E r)⟦l⟧) = 0) ?_ ?_
  · intro r h _ l _
    exact finrank_hom_of_isZero_left k (S.isZero_E_of_left h) _
  · intro r ih hr l hl
    have hwr := S.wt_le_wt hr
    rw [S.lem1_step (by omega) (hyp _ (by omega)) l, ih (r + 1) (by omega) (by omega) _ (by omega),
      zero_add]
    refine Finset.sum_eq_zero fun j hj => S.hom_neg _ _ ?_
    have := S.toNat_wt_succ (r := r) (by omega)
    rw [Finset.mem_range] at hj
    omega

/-- **Lemma 3.1** (CL `lem:1`), degree zero: under the same hypotheses, if `m ≥ n` and the weight
`m + 2` is nonzero then `Hom(E 1_m, E 1_m ⟨l⟩)` is one-dimensional for `l = 0`. -/
theorem lem1_zero' {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ ≤ r) (h : ¬ IsZero (𝟙 (S.obj (r + 1)))) {l : ℤ} (hl : l = 0) :
    finrank k (S.E r ⟶ (S.E r)⟦l⟧) = 1 := by
  subst hl
  have hwr := S.wt_le_wt hr
  have hM := S.toNat_wt_succ (r := r) (by omega)
  rw [S.lem1_step (by omega) (hyp _ (by omega)) 0,
    S.lem1_neg hn hyp (r + 1) (by omega) _ (by omega), zero_add,
    Finset.sum_eq_single ((S.wt (r + 1)).toNat - 1)]
  · rw [finrank_hom_shift_zero k _ _ (by omega)]
    exact S.hom_zero _ h
  · intro j hj hne
    rw [Finset.mem_range] at hj
    exact S.hom_neg _ _ (by omega)
  · intro hj
    rw [Finset.mem_range] at hj
    omega

/-- **Lemma 3.1** (CL `lem:1`): `End(E 1_m)` is one-dimensional (`E 1_m` is a brick). -/
theorem lem1_zero {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ ≤ r) (h : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    finrank k (S.E r ⟶ S.E r) = 1 := by
  rw [← finrank_hom_shift_zero k _ _ (rfl : (0 : ℤ) = 0)]
  exact S.lem1_zero' hn hyp hr h rfl

/-- The dimension count in CL's proof of Corollary 3.2: for `m = wt r ≥ -2`, under
`(E 1_{m+4})_L ≅ 1_{m+4} F ⟨-m-5⟩`,
`dim Hom(E E 1_m, E E 1_m ⟨l⟩) = dim Hom(E E 1_{m+2}, E E 1_{m+2} ⟨l-2m-6⟩)
  + ∑_{j=0}^{m+3} dim Hom(E 1_{m+2}, E 1_{m+2} ⟨l-2m-4+2j⟩)
  + ∑_{j=0}^{m+1} dim Hom(E 1_{m+2}, E 1_{m+2} ⟨l-2m-2+2j⟩)`. -/
theorem cor0_step {r : ℤ} (hr : -2 ≤ S.wt r) (h2 : S.AdjHyp (r + 1 + 1)) (l : ℤ) :
    finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) =
      finrank k (S.E (r + 1) ≫ S.E (r + 1 + 1) ⟶
          (S.E (r + 1) ≫ S.E (r + 1 + 1))⟦l - 2 * S.wt r - 6⟧) +
        ∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
          finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦l - 2 * S.wt r - 4 + 2 * (j : ℤ)⟧) +
        ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
          finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦l - 2 * S.wt r - 2 + 2 * (j : ℤ)⟧) := by
  have hw1 : S.wt (r + 1) = S.wt r + 2 := S.wt_add_one r
  have hw2 : S.wt (r + 1 + 1) = S.wt r + 4 := by rw [S.wt_add_one, hw1]; ring
  have hM1 := S.toNat_wt_succ hr
  have hM2 : ((S.wt (r + 1 + 1)).toNat : ℤ) = S.wt r + 4 := by
    rw [Int.toNat_of_nonneg (by omega), hw2]
  obtain ⟨e₁⟩ := S.EF r (by rw [← wt, hw1]; omega)
  obtain ⟨e₂⟩ := S.EF (r + 1) (by rw [← wt, hw2]; omega)
  have i₂ : (S.E (r + 1) ≫ S.F (r + 1)) ≫ S.E (r + 1) ≅
      ((S.E (r + 1) ≫ S.E (r + 1 + 1)) ≫ S.F (r + 1 + 1)) ⊞
        qsum 1 (S.wt (r + 1 + 1)).toNat (S.E (r + 1)) :=
    α_ _ _ _ ≪≫ whiskerLeftIso _ e₂ ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _).symm (compQsumIso _ _ _)
  calc finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧)
      = finrank k (S.E r ≫ S.E (r + 1) ⟶ S.E r ≫ (S.E (r + 1))⟦l⟧) :=
        finrank_hom_congr_right k _ (whiskerLeftShiftIso _ _ _).symm
    _ = finrank k ((S.F r)⟦S.wt r + 1⟧ ≫ S.E r ≫ S.E (r + 1) ⟶ (S.E (r + 1))⟦l⟧) :=
        (S.dimAdj r).right _ _
    _ = finrank k (((S.F r ≫ S.E r) ≫ S.E (r + 1))⟦S.wt r + 1⟧ ⟶ (S.E (r + 1))⟦l⟧) :=
        finrank_hom_congr_left k ((α_ _ _ _).symm ≪≫
          whiskerRightIso (whiskerRightShiftIso _ _ _) _ ≪≫ whiskerRightShiftIso _ _ _) _
    _ = finrank k ((S.F r ≫ S.E r) ≫ S.E (r + 1) ⟶ (S.E (r + 1))⟦l - (S.wt r + 1)⟧) :=
        finrank_hom_shift_shift k _ _ (by ring)
    _ = finrank k ((((S.E (r + 1) ≫ S.E (r + 1 + 1)) ≫ S.F (r + 1 + 1)) ⊞
            qsum 1 (S.wt (r + 1 + 1)).toNat (S.E (r + 1))) ⊞
              qsum 1 (S.wt (r + 1)).toNat (S.E (r + 1)) ⟶
            (S.E (r + 1))⟦l - (S.wt r + 1)⟧) :=
        finrank_hom_congr_left k (whiskerRightIso e₁ _ ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
          biprod.mapIso i₂ (qsumCompIso _ _ _)) _
    _ = _ := by
      rw [finrank_hom_biprod_left, finrank_hom_biprod_left, finrank_hom_qsum_left,
        finrank_hom_qsum_left, (h2.dimAdjF S).left, finrank_hom_congr_right k _
          (shiftCompShiftIso (p := l - (S.wt r + 1)) (q := -(S.wt (r + 1 + 1) + 1))
            (s := l - 2 * S.wt r - 6) (S.E (r + 1)) (S.E (r + 1 + 1)) (by rw [hw2]; ring))]
      refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_
      · refine Finset.sum_congr rfl fun j _ => finrank_hom_shift_shift k _ _ ?_
        change _ + 1 * (((S.wt (r + 1 + 1)).toNat : ℤ) - 1 - 2 * (j : ℤ)) = _
        rw [hM2]; ring
      · refine Finset.sum_congr rfl fun j _ => finrank_hom_shift_shift k _ _ ?_
        change _ + 1 * (((S.wt (r + 1)).toNat : ℤ) - 1 - 2 * (j : ℤ)) = _
        rw [hM1]; ring

/-- **Corollary 3.2** (CL `cor:0`), degrees `< -2`: assuming `eq:ind_hyp` for all weights
`> n = wt r₀ ≥ 0`, if `m ≥ n - 2` then `Hom(E E 1_m, E E 1_m ⟨l⟩) = 0` for `l < -2`. -/
theorem cor0_neg {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') :
    ∀ r, r₀ - 1 ≤ r → ∀ l : ℤ, l < -2 →
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) = 0 := by
  refine S.decreasing_induction (P := fun r => r₀ - 1 ≤ r → ∀ l : ℤ, l < -2 →
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) = 0) ?_ ?_
  · intro r h _ l _
    exact finrank_hom_of_isZero_left k (isZero_comp_left (S.isZero_E_of_left h) _) _
  · intro r ih hr l hl
    have hwr : S.wt r₀ - 2 ≤ S.wt r := by simp only [wt]; omega
    have hM1 := S.toNat_wt_succ (r := r) (by omega)
    have hM2 : ((S.wt (r + 1 + 1)).toNat : ℤ) = S.wt r + 4 := by
      rw [Int.toNat_of_nonneg (by rw [S.wt_add_one, S.wt_add_one]; omega), S.wt_add_one,
        S.wt_add_one]; ring
    rw [S.cor0_step (by omega) (hyp _ (by omega)) l, ih (r + 1) (by omega) (by omega) _ (by omega),
      zero_add]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro j hj
      rw [Finset.mem_range] at hj
      exact S.lem1_neg hn hyp (r + 1) (by omega) _ (by omega)
    · intro j hj
      rw [Finset.mem_range] at hj
      exact S.lem1_neg hn hyp (r + 1) (by omega) _ (by omega)

/-- **Corollary 3.2** (CL `cor:0`), degree `-2`: under the same hypotheses, if `m ≥ n - 2` and the
top weight `m + 4` of `E E 1_m` is nonzero, then `Hom(E E 1_m, E E 1_m ⟨-2⟩)` is one-dimensional. -/
theorem cor0_zero {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ - 1 ≤ r) (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) :
    finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦-2⟧) = 1 := by
  have hwr : S.wt r₀ - 2 ≤ S.wt r := by simp only [wt]; omega
  have hM1 := S.toNat_wt_succ (r := r) (by omega)
  have hM2 : ((S.wt (r + 1 + 1)).toNat : ℤ) = S.wt r + 4 := by
    rw [Int.toNat_of_nonneg (by rw [S.wt_add_one, S.wt_add_one]; omega), S.wt_add_one,
      S.wt_add_one]; ring
  rw [S.cor0_step (by omega) (hyp _ (by omega)) (-2),
    S.cor0_neg hn hyp (r + 1) (by omega) _ (by omega), zero_add]
  rw [Finset.sum_eq_zero (s := Finset.range (S.wt (r + 1)).toNat), add_zero,
    Finset.sum_eq_single ((S.wt (r + 1 + 1)).toNat - 1)]
  · exact S.lem1_zero' hn hyp (by omega) h (by omega)
  · intro j hj hne
    rw [Finset.mem_range] at hj
    exact S.lem1_neg hn hyp (r + 1) (by omega) _ (by omega)
  · intro hj
    rw [Finset.mem_range] at hj
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    exact S.lem1_neg hn hyp (r + 1) (by omega) _ (by omega)

/-- **Corollary 3.3** (CL `cor:2`): assuming `eq:ind_hyp` for all weights `> n = wt r₀ ≥ 0`, if
`m ≥ n` (here `m = wt (r + 1)`) and the weight `m + 2` is nonzero, then
`Hom(E 1_m, E E F 1_m ⟨-m-1⟩)` is one-dimensional. -/
theorem cor2 {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ ≤ r + 1) (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) :
    finrank k (S.E (r + 1) ⟶ (S.F r ≫ S.E r ≫ S.E (r + 1))⟦-(S.wt (r + 1) + 1)⟧) = 1 := by
  have hwr : S.wt r₀ ≤ S.wt (r + 1) := S.wt_le_wt hr
  have hw2 : S.wt (r + 1 + 1) = S.wt (r + 1) + 2 := S.wt_add_one _
  have hM1 : ((S.wt (r + 1)).toNat : ℤ) = S.wt (r + 1) := Int.toNat_of_nonneg (by omega)
  have hM2 : ((S.wt (r + 1 + 1)).toNat : ℤ) = S.wt (r + 1) + 2 := by
    rw [Int.toNat_of_nonneg (by omega), hw2]
  obtain ⟨e₁⟩ := S.EF r (by rw [← wt]; omega)
  obtain ⟨e₂⟩ := S.EF (r + 1) (by rw [← wt, hw2]; omega)
  have i₂ : (S.E (r + 1) ≫ S.F (r + 1)) ≫ S.E (r + 1) ≅
      ((S.E (r + 1) ≫ S.E (r + 1 + 1)) ≫ S.F (r + 1 + 1)) ⊞
        qsum 1 (S.wt (r + 1 + 1)).toNat (S.E (r + 1)) :=
    α_ _ _ _ ≪≫ whiskerLeftIso _ e₂ ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _).symm (compQsumIso _ _ _)
  have i : S.F r ≫ S.E r ≫ S.E (r + 1) ≅
      (((S.E (r + 1) ≫ S.E (r + 1 + 1)) ≫ S.F (r + 1 + 1)) ⊞
        qsum 1 (S.wt (r + 1 + 1)).toNat (S.E (r + 1))) ⊞
          qsum 1 (S.wt (r + 1)).toNat (S.E (r + 1)) :=
    (α_ _ _ _).symm ≪≫ whiskerRightIso e₁ _ ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
      biprod.mapIso i₂ (qsumCompIso _ _ _)
  rw [finrank_hom_shift_right k _ _ (b := S.wt (r + 1) + 1) (by ring), finrank_hom_congr_right k _ i,
    finrank_hom_biprod_right, finrank_hom_biprod_right, finrank_hom_qsum_right,
    finrank_hom_qsum_right, ← (S.dimAdj_EF (r + 1 + 1)).left,
    finrank_hom_congr_left k (shiftCompShiftIso (p := S.wt (r + 1) + 1)
      (q := S.wt (r + 1 + 1) + 1) (s := 2 * S.wt (r + 1) + 4) _ _ (by rw [hw2]; ring)),
    finrank_hom_shift_left k _ _ (b := -(2 * S.wt (r + 1) + 4)) (by ring),
    S.cor0_neg hn hyp (r + 1) (by omega) _ (by omega), zero_add]
  rw [Finset.sum_eq_zero (s := Finset.range (S.wt (r + 1)).toNat), add_zero,
    Finset.sum_eq_single 0]
  · rw [finrank_hom_shift_shift k _ _ (c := 0) (by push_cast; rw [hM2]; ring)]
    exact S.lem1_zero' hn hyp hr h rfl
  · intro j hj hne
    rw [Finset.mem_range] at hj
    rw [finrank_hom_shift_shift k _ _ (c := -2 * (j : ℤ)) (by rw [hM2]; ring)]
    exact S.lem1_neg hn hyp (r + 1) hr _ (by omega)
  · intro hj
    rw [Finset.mem_range] at hj
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [finrank_hom_shift_shift k _ _ (c := -2 - 2 * (j : ℤ)) (by rw [hM1]; ring)]
    exact S.lem1_neg hn hyp (r + 1) hr _ (by omega)

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The adjunction count in CL's proof of Lemma 3.4 (`lem:XXX`): "`(F 1_m)_L = 1_m E ⟨m-1⟩` ...
the claim reduces to Corollary 3.2": `dim Hom(E F 1_m, F E 1_m ⟨l⟩) =
dim Hom(E E 1_{m-2}, E E 1_{m-2} ⟨l-2⟩)` (no induction hypothesis needed). -/
theorem lemXXX_eq (r l : ℤ) :
    finrank k (S.F r ≫ S.E r ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦l⟧) =
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l - 2⟧) :=
  calc finrank k (S.F r ≫ S.E r ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦l⟧)
      = finrank k (S.F r ≫ S.E r ⟶ (S.E (r + 1))⟦l⟧ ≫ S.F (r + 1)) :=
        finrank_hom_congr_right k _ (whiskerRightShiftIso _ _ _).symm
    _ = finrank k ((S.F r ≫ S.E r) ≫ (S.E (r + 1))⟦S.wt (r + 1) + 1⟧ ⟶ (S.E (r + 1))⟦l⟧) :=
        ((S.dimAdj_EF (r + 1)).left _ _).symm
    _ = finrank k (S.F r ≫ S.E r ≫ (S.E (r + 1))⟦S.wt (r + 1) + 1⟧ ⟶ (S.E (r + 1))⟦l⟧) :=
        finrank_hom_congr_left k (α_ _ _ _) _
    _ = finrank k (S.E r ≫ (S.E (r + 1))⟦S.wt (r + 1) + 1⟧ ⟶
          (S.E r)⟦S.wt r + 1⟧ ≫ (S.E (r + 1))⟦l⟧) :=
        ((S.dimAdj_EF r).right _ _).symm
    _ = finrank k ((S.E r ≫ S.E (r + 1))⟦S.wt (r + 1) + 1⟧ ⟶
          (S.E r ≫ S.E (r + 1))⟦l + (S.wt r + 1)⟧) :=
        finrank_hom_congr k (whiskerLeftShiftIso _ _ _) (shiftCompShiftIso _ _ rfl)
    _ = _ := finrank_hom_shift_shift k _ _ (by rw [S.wt_add_one]; ring)

/-- **Lemma 3.4** (CL `lem:XXX`), negative degrees: assuming `eq:ind_hyp` for all weights
`> n = wt r₀ ≥ 0`, if `m ≥ n` (here `m = wt (r + 1)`) then `Hom(E F 1_m, F E 1_m ⟨l⟩) = 0` for
`l < 0`. -/
theorem lemXXX_neg {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ ≤ r + 1) {l : ℤ} (hl : l < 0) :
    finrank k (S.F r ≫ S.E r ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦l⟧) = 0 := by
  rw [lemXXX_eq]
  exact S.cor0_neg hn hyp r (by omega) _ (by omega)

/-- **Lemma 3.4** (CL `lem:XXX`), degree zero: under the same hypotheses, if moreover the weight
`m + 2` is nonzero then `Hom(E F 1_m, F E 1_m)` is one-dimensional. -/
theorem lemXXX_zero {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ ≤ r + 1) (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) :
    finrank k (S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1)) = 1 := by
  rw [← finrank_hom_shift_zero k _ _ (rfl : (0 : ℤ) = 0), lemXXX_eq,
    finrank_hom_shift_congr k _ _ (by norm_num : (0 : ℤ) - 2 = -2)]
  exact S.cor0_zero hn hyp (by omega) h

end Categorification.TwoRep.StrongSl2
