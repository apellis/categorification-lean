/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointInduction

/-!
# Units, counits and up-down crossings: dimension counts (CL §3.4–3.5)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3: Corollary 3.10 (`cor:EFidhoms`) and Lemma 3.12 (`lem:homs`).

* `finrank_EF_counit`, `finrank_FE_unit`, `finrank_EF_unit`, `finrank_FE_counit`
  (**Corollary 3.10**): the four spaces `Hom(E F 1_{n+2} ⟨n+1⟩, 1_{n+2})`,
  `Hom(1_n, F E 1_n ⟨n+1⟩)`, `Hom(1_{n+2} ⟨n+1⟩, E F 1_{n+2})`, `Hom(F E 1_n, 1_n ⟨n+1⟩)` all have
  the dimension of `End(E 1_n)`; the first two need only the definition of `F`, the last two the
  left adjoint `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩` (`AdjHyp`, i.e. Proposition 3.9 at `n`). Hence they are
  one-dimensional whenever `End(E 1_n) = k` (`cor_EFidhoms`, via Lemma 3.1).
* `finrank_FF_FF_eq`: `dim Hom(F F 1_n, F F 1_n ⟨l⟩) = dim Hom(E E 1_{n-4}, E E 1_{n-4} ⟨l⟩)` —
  "(the adjoint of) Corollary 3.2" — using only the definition of `F`.
* `lemHoms_EF_FE`, `lemHoms_FE_EF` (**Lemma 3.12**): `Hom(E F 1_m, F E 1_m)` and
  `Hom(F E 1_m, E F 1_m)` both have the dimension of `Hom(E E 1_{m-2}, E E 1_{m-2} ⟨-2⟩)`; the
  second uses the left adjoints of `E 1_m` and `E 1_{m-2}`. With Corollary 3.2 they are
  one-dimensional (`lemHoms_EF_FE_eq_one`, `lemHoms_FE_EF_eq_one`) in the range of weights where
  §3.2 has been carried out (`m ≥ n ≥ 0` under `eq:ind_hyp`).
* `finrank_one_FE`, `finrank_FE_one`, `not_retract_one_FE`: for `n ≥ 0`, `F E 1_n` has no summand
  `1_n ⟨l⟩` (a step in CL's proof of Lemma 3.6, "the space of inclusions `Hom(1_n⟨l⟩, FE1_n)`
  [...] is zero"; in fact the inclusions vanish only for `l > -n-1`, and the projections
  `F E 1_n → 1_n ⟨l⟩` vanish for `l < n + 1`, which together exclude a summand).

CL state Lemma 3.12 "for any `n ∈ ℤ`" after biadjointness has been established for all weights;
the one-dimensionality for weights below the range `m ≥ 0` needs the mirror image (Remark 3.11,
`rem:nle0`) of the §3.2 results for `n ≤ 0`, which is not formalized here.

Indexing as in `AdjointInduction`: at the object `r + 1` of weight `m = wt (r + 1)`,
`E F 1_m = F r ≫ E r` and `F E 1_m = E (r + 1) ≫ F (r + 1)`; at the object `r` of weight
`n = wt r`, `E F 1_{n+2} = F r ≫ E r` and `F E 1_n = E r ≫ F r`.
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
  (S : StrongSl2 k B)

omit [GradedBicategory.IsLinear B k] in
theorem finrank_E_E_zero (r : ℤ) :
    finrank k (S.E r ⟶ (S.E r)⟦(0 : ℤ)⟧) = finrank k (S.E r ⟶ S.E r) :=
  finrank_hom_shift_zero k _ _ rfl

/-- **Corollary 3.10**, first space: `dim Hom(E F 1_{n+2} ⟨n+1⟩, 1_{n+2}) = dim End(E 1_n)`. -/
theorem finrank_EF_counit (r : ℤ) :
    finrank k ((S.F r ≫ S.E r)⟦S.wt r + 1⟧ ⟶ 𝟙 (S.obj (r + 1))) =
      finrank k (S.E r ⟶ S.E r) := by
  rw [finrank_hom_shift_left k _ _ (b := -(S.wt r + 1)) (by ring), ← S.finrank_E_E_zero,
    S.finrank_E_E, finrank_hom_shift_congr k _ _ (by ring : (0 : ℤ) - (S.wt r + 1) =
      -(S.wt r + 1))]

/-- **Corollary 3.10**, second space: `dim Hom(1_n, F E 1_n ⟨n+1⟩) = dim End(E 1_n)`. -/
theorem finrank_FE_unit (r : ℤ) :
    finrank k (𝟙 (S.obj r) ⟶ (S.E r ≫ S.F r)⟦S.wt r + 1⟧) = finrank k (S.E r ⟶ S.E r) := by
  rw [finrank_hom_congr_right k _ (whiskerLeftShiftIso _ _ _).symm, ← (S.dimAdj r).left,
    finrank_hom_congr_left k (λ_ (S.E r))]

/-- **Corollary 3.10**, third space: given `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`,
`dim Hom(1_{n+2} ⟨n+1⟩, E F 1_{n+2}) = dim End(E 1_n)`. -/
theorem finrank_EF_unit {r : ℤ} (h : S.AdjHyp r) :
    finrank k ((𝟙 (S.obj (r + 1)))⟦S.wt r + 1⟧ ⟶ S.F r ≫ S.E r) =
      finrank k (S.E r ⟶ S.E r) := by
  rw [← (h.dimAdj S).left, finrank_hom_congr_left k
      (idShiftCompShiftIso (p := S.wt r + 1) (q := -(S.wt r + 1)) (s := 0) (S.F r) (by ring)),
    finrank_hom_congr_left k ((shiftFunctorZero _ ℤ).app (S.F r)), ← S.finrank_E_E_zero,
    ← S.finrank_F_F_eq, finrank_hom_shift_zero k _ _ rfl]
  rfl

/-- **Corollary 3.10**, fourth space: given `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`,
`dim Hom(F E 1_n, 1_n ⟨n+1⟩) = dim End(E 1_n)`. -/
theorem finrank_FE_counit {r : ℤ} (h : S.AdjHyp r) :
    finrank k (S.E r ≫ S.F r ⟶ (𝟙 (S.obj r))⟦S.wt r + 1⟧) = finrank k (S.E r ⟶ S.E r) := by
  rw [(h.dimAdjF S).left, finrank_hom_congr_right k _
      (idShiftCompShiftIso (p := S.wt r + 1) (q := -(S.wt r + 1)) (s := 0) (S.E r) (by ring)),
    S.finrank_E_E_zero]

/-- **Corollary 3.10** (CL `cor:EFidhoms`): under the adjoint induction hypothesis for the weights
`> n₀ = wt r₀ ≥ 0` and `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩` at `n = wt r ≥ n₀` (Proposition 3.9), with
`1_{n+2}` nonzero, the four spaces of units and counits are one-dimensional, so these 2-morphisms
are unique up to a scalar. -/
theorem cor_EFidhoms [∀ a b : B, HomFinite k (a ⟶ b)] {r₀ : ℤ} (hn : 0 ≤ S.wt r₀)
    (hyp : ∀ r', r₀ < r' → S.AdjHyp r') {r : ℤ}
    (hr : r₀ ≤ r) (hr' : S.AdjHyp r) (h : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    finrank k ((S.F r ≫ S.E r)⟦S.wt r + 1⟧ ⟶ 𝟙 (S.obj (r + 1))) = 1 ∧
      finrank k ((𝟙 (S.obj (r + 1)))⟦S.wt r + 1⟧ ⟶ S.F r ≫ S.E r) = 1 ∧
      finrank k (S.E r ≫ S.F r ⟶ (𝟙 (S.obj r))⟦S.wt r + 1⟧) = 1 ∧
      finrank k (𝟙 (S.obj r) ⟶ (S.E r ≫ S.F r)⟦S.wt r + 1⟧) = 1 := by
  have h1 := S.lem1_zero hn hyp hr h
  exact ⟨by rw [finrank_EF_counit, h1], by rw [S.finrank_EF_unit hr', h1],
    by rw [S.finrank_FE_counit hr', h1], by rw [finrank_FE_unit, h1]⟩

/-- "(The adjoint of) Corollary 3.2": `dim Hom(F F 1_{n+4}, F F 1_{n+4} ⟨l⟩) =
dim Hom(E E 1_n, E E 1_n ⟨l⟩)`; both are `dim Hom(F F E E 1_{n+4} ⟨2n+4⟩, 1_{n+4} ⟨l⟩)`. -/
theorem finrank_FF_FF_eq (r l : ℤ) :
    finrank k (S.F (r + 1) ≫ S.F r ⟶ (S.F (r + 1) ≫ S.F r)⟦l⟧) =
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) := by
  set s := S.wt (r + 1) + 1 + (S.wt r + 1)
  have hFF : finrank k (S.F (r + 1) ≫ S.F r ⟶ (S.F (r + 1) ≫ S.F r)⟦l⟧) =
      finrank k (((S.F (r + 1) ≫ S.F r) ≫ (S.E r ≫ S.E (r + 1)))⟦s⟧ ⟶
        (𝟙 (S.obj (r + 1 + 1)))⟦l⟧) :=
    calc finrank k (S.F (r + 1) ≫ S.F r ⟶ (S.F (r + 1) ≫ S.F r)⟦l⟧)
        = finrank k (S.F (r + 1) ≫ S.F r ⟶ (S.F (r + 1))⟦l⟧ ≫ S.F r) :=
          finrank_hom_congr_right k _ (whiskerRightShiftIso _ _ _).symm
      _ = finrank k ((S.F (r + 1) ≫ S.F r) ≫ (S.E r)⟦S.wt r + 1⟧ ⟶ (S.F (r + 1))⟦l⟧) :=
          ((S.dimAdj_EF r).left _ _).symm
      _ = finrank k ((S.F (r + 1) ≫ S.F r) ≫ (S.E r)⟦S.wt r + 1⟧ ⟶
            (𝟙 (S.obj (r + 1 + 1)))⟦l⟧ ≫ S.F (r + 1)) :=
          finrank_hom_congr_right k _ (idShiftCompIso _ _).symm
      _ = finrank k (((S.F (r + 1) ≫ S.F r) ≫ (S.E r)⟦S.wt r + 1⟧) ≫
            (S.E (r + 1))⟦S.wt (r + 1) + 1⟧ ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦l⟧) :=
          ((S.dimAdj_EF (r + 1)).left _ _).symm
      _ = _ := finrank_hom_congr_left k (α_ _ _ _ ≪≫
          whiskerLeftIso _ (shiftCompShiftIso (S.E r) (S.E (r + 1)) (s := s) (by ring)) ≪≫
          whiskerLeftShiftIso _ _ _) _
  have hEE : finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧) =
      finrank k (((S.F (r + 1) ≫ S.F r) ≫ (S.E r ≫ S.E (r + 1)))⟦s⟧ ⟶
        (𝟙 (S.obj (r + 1 + 1)))⟦l⟧) :=
    calc finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦l⟧)
        = finrank k (S.E r ≫ S.E (r + 1) ⟶ S.E r ≫ (S.E (r + 1))⟦l⟧) :=
          finrank_hom_congr_right k _ (whiskerLeftShiftIso _ _ _).symm
      _ = finrank k ((S.F r)⟦S.wt r + 1⟧ ≫ S.E r ≫ S.E (r + 1) ⟶ (S.E (r + 1))⟦l⟧) :=
          (S.dimAdj r).right _ _
      _ = finrank k ((S.F r)⟦S.wt r + 1⟧ ≫ S.E r ≫ S.E (r + 1) ⟶
            S.E (r + 1) ≫ (𝟙 (S.obj (r + 1 + 1)))⟦l⟧) :=
          finrank_hom_congr_right k _ (compIdShiftIso _ _).symm
      _ = finrank k ((S.F (r + 1))⟦S.wt (r + 1) + 1⟧ ≫ (S.F r)⟦S.wt r + 1⟧ ≫ S.E r ≫
            S.E (r + 1) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦l⟧) :=
          (S.dimAdj (r + 1)).right _ _
      _ = _ := finrank_hom_congr_left k ((α_ _ _ _).symm ≪≫
          whiskerRightIso (shiftCompShiftIso (S.F (r + 1)) (S.F r) (s := s) (by ring)) _ ≪≫
          whiskerRightShiftIso _ _ _) _
  rw [hFF, hEE]

/-- **Lemma 3.12** (CL `lem:homs`), first space: `dim Hom(E F 1_m, F E 1_m) =
dim Hom(E E 1_{m-2}, E E 1_{m-2} ⟨-2⟩)` (`m = wt (r + 1)`). -/
theorem lemHoms_EF_FE (r : ℤ) :
    finrank k (S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1)) =
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦-2⟧) := by
  rw [← finrank_hom_shift_zero k _ _ (rfl : (0 : ℤ) = 0), lemXXX_eq,
    finrank_hom_shift_congr k _ _ (by norm_num : (0 : ℤ) - 2 = -2)]

/-- **Lemma 3.12** (CL `lem:homs`), second space: given the left adjoints
`(E 1_{m-2})_L ≅ 1_{m-2} F ⟨1-m⟩` and `(E 1_m)_L ≅ 1_m F ⟨-m-1⟩`,
`dim Hom(F E 1_m, E F 1_m) = dim Hom(E E 1_{m-2}, E E 1_{m-2} ⟨-2⟩)` (`m = wt (r + 1)`). -/
theorem lemHoms_FE_EF {r : ℤ} (h₀ : S.AdjHyp r) (h₁ : S.AdjHyp (r + 1)) :
    finrank k (S.E (r + 1) ≫ S.F (r + 1) ⟶ S.F r ≫ S.E r) =
      finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦-2⟧) := by
  rw [← (h₀.dimAdj S).left, finrank_hom_congr_left k (α_ _ _ _), ← (h₁.dimAdj S).right,
    finrank_hom_congr_left k (whiskerLeftShiftIso _ _ _),
    finrank_hom_congr_right k _ (whiskerRightShiftIso _ _ _),
    finrank_hom_shift_shift k _ _ (c := -2) (by rw [S.wt_add_one]; ring), finrank_FF_FF_eq]

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **Lemma 3.12** with Corollary 3.2: under `eq:ind_hyp` for the weights `> n = wt r₀ ≥ 0`, if
`m = wt (r + 1) ≥ n` and `1_{m+2}` is nonzero, `Hom(E F 1_m, F E 1_m)` is one-dimensional. -/
theorem lemHoms_EF_FE_eq_one {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r')
    {r : ℤ} (hr : r₀ ≤ r + 1) (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) :
    finrank k (S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1)) = 1 := by
  rw [lemHoms_EF_FE]
  exact S.cor0_zero hn hyp (by omega) h

/-- **Lemma 3.12** with Corollary 3.2, second space: moreover given the left adjoints at the weights
`m - 2` and `m` (Proposition 3.9), `Hom(F E 1_m, E F 1_m)` is one-dimensional. -/
theorem lemHoms_FE_EF_eq_one {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r')
    {r : ℤ} (hr : r₀ ≤ r + 1) (h₀ : S.AdjHyp r) (h₁ : S.AdjHyp (r + 1))
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) :
    finrank k (S.E (r + 1) ≫ S.F (r + 1) ⟶ S.F r ≫ S.E r) = 1 := by
  rw [S.lemHoms_FE_EF h₀ h₁]
  exact S.cor0_zero hn hyp (by omega) h

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `dim Hom(1_n ⟨l⟩, F E 1_n) = dim Hom(E 1_n, E 1_n ⟨-(l + n + 1)⟩)` (definition of `F`). -/
theorem finrank_one_FE (r l : ℤ) :
    finrank k ((𝟙 (S.obj r))⟦l⟧ ⟶ S.E r ≫ S.F r) =
      finrank k (S.E r ⟶ (S.E r)⟦-(l + (S.wt r + 1))⟧) :=
  calc finrank k ((𝟙 (S.obj r))⟦l⟧ ⟶ S.E r ≫ S.F r)
      = finrank k (((𝟙 (S.obj r))⟦l⟧)⟦S.wt r + 1⟧ ⟶ (S.E r ≫ S.F r)⟦S.wt r + 1⟧) :=
        (finrank_hom_shift k _ _ _).symm
    _ = finrank k ((𝟙 (S.obj r))⟦l + (S.wt r + 1)⟧ ⟶ S.E r ≫ (S.F r)⟦S.wt r + 1⟧) :=
        finrank_hom_congr k ((shiftFunctorAdd' _ l (S.wt r + 1) _ rfl).app _).symm
          (whiskerLeftShiftIso _ _ _).symm
    _ = finrank k ((𝟙 (S.obj r))⟦l + (S.wt r + 1)⟧ ≫ S.E r ⟶ S.E r) :=
        ((S.dimAdj r).left _ _).symm
    _ = finrank k ((S.E r)⟦l + (S.wt r + 1)⟧ ⟶ S.E r) :=
        finrank_hom_congr_left k (idShiftCompIso _ _) _
    _ = _ := finrank_hom_shift_left k _ _ (by ring)

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `dim Hom(F E 1_n, 1_n ⟨l⟩) = dim Hom(E 1_n, E 1_n ⟨l - n - 1⟩)`, given
`(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`. -/
theorem finrank_FE_one {r : ℤ} (h : S.AdjHyp r) (l : ℤ) :
    finrank k (S.E r ≫ S.F r ⟶ (𝟙 (S.obj r))⟦l⟧) =
      finrank k (S.E r ⟶ (S.E r)⟦l + -(S.wt r + 1)⟧) := by
  rw [(h.dimAdjF S).left, finrank_hom_congr_right k _
      (idShiftCompShiftIso (p := l) (q := -(S.wt r + 1)) (s := l + -(S.wt r + 1)) (S.E r)
        (by ring))]

/-- **`F E 1_n` has no summand `1_n ⟨l⟩` for `n ≥ 0`** (used in CL's proof of Lemma 3.6: "one
shows using Lemma 3.1 [...] that the space of inclusions `Hom(1_n ⟨l⟩, F E 1_n)` [...] is zero"):
under (3.2) for the weights `> n₀ = wt r₀ ≥ 0` and `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩` at `n = wt r ≥ n₀`,
if `1_n` is nonzero then `1_n ⟨l⟩` is not a retract of `F E 1_n`. (The inclusions vanish for
`l > -n-1` and the projections for `l < n + 1`.) -/
theorem not_retract_one_FE {r₀ : ℤ} (hn : 0 ≤ S.wt r₀) (hyp : ∀ r', r₀ < r' → S.AdjHyp r')
    {r : ℤ} (hr : r₀ ≤ r) (hr' : S.AdjHyp r) (h : ¬ IsZero (𝟙 (S.obj r))) (l : ℤ)
    (i : (𝟙 (S.obj r))⟦l⟧ ⟶ S.E r ≫ S.F r) (p : S.E r ≫ S.F r ⟶ (𝟙 (S.obj r))⟦l⟧) :
    i ≫ p ≠ 𝟙 _ := by
  intro hip
  have hwr : S.wt r₀ ≤ S.wt r := S.wt_le_wt hr
  have hne : ¬ IsZero ((𝟙 (S.obj r))⟦l⟧) := fun hz => by
    have e : 𝟙 (S.obj r) ≅ ((𝟙 (S.obj r))⟦l⟧)⟦-l⟧ :=
      ((shiftFunctorCompIsoId _ l (-l) (by ring)).app _).symm
    exact h (((shiftFunctor _ (-l)).map_isZero hz).of_iso e)
  by_cases hl : 0 < l + (S.wt r + 1)
  · have h0 := S.finrank_one_FE r l
    rw [S.lem1_neg hn hyp r hr _ (by omega)] at h0
    have : i = 0 := by
      haveI := Module.finrank_zero_iff.1 h0
      exact Subsingleton.elim _ _
    exact hne ((IsZero.iff_id_eq_zero _).2 (by rw [← hip, this, zero_comp]))
  · have h0 := S.finrank_FE_one hr' l
    rw [S.lem1_neg hn hyp r hr _ (by omega)] at h0
    have : p = 0 := by
      haveI := Module.finrank_zero_iff.1 h0
      exact Subsingleton.elim _ _
    exact hne ((IsZero.iff_id_eq_zero _).2 (by rw [← hip, this, comp_zero]))

end Categorification.TwoRep.StrongSl2
