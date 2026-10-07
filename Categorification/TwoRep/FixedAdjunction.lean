/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LeftAdjunction

/-!
# Fixing the left adjunctions at the weights `n ≥ -1` (CL §4.1)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §4.1 ("Fixing adjunction maps"), the normalization (4.1) for `n ≥ 1`.

The left adjunction `R_m ⊣ E 1_m` (`StrongSl2.leftAdj`) is determined up to rescaling its unit
by `t` and its counit by `t⁻¹` (`StrongSl2.scaleAdj`). For `m = n - 2 ≥ -1`, CL fix this scalar
so that the clockwise degree-zero bubble at the weight `n ≥ 1` (the left cup of `E 1_m`, then
`n - 1` dots, then the counit of `E 1_m ⊣ R_m`; `StrongSl2.cwBubble`) is the identity of `1_n`.
This is possible because that bubble is nonzero (`topBubble_ne_zero`, CL Corollary 3.7)
and the left cup is unique up to a scalar (`exists_eq_smul_leftAdj_unit`, CL Corollary 3.10):
`StrongSl2.exists_normalized_leftAdj`, and under (BB_w) `StrongSl2.BBw.exists_normalized_leftAdj`.

The counter-clockwise normalization at the weights `n < -1` is in `FixedAdjunctionNeg.lean`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat RightwardCrossing

variable (S : StrongSl2 k B) [GradedBicategory.IsLinear B k]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
/-- **Rescaling an adjunction** of the graded-Hom bicategory: unit `t • η`, counit `t⁻¹ • ε`. -/
def scaleAdj {a b : GradedHomBicat B} {f : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g) {t : k}
    (ht : t ≠ 0) : f ⊣ g where
  unit := t • adj.unit
  counit := t⁻¹ • adj.counit
  left_triangle := by
    rw [← adj.left_triangle]
    simp only [leftZigzag, bicategoricalComp, GradedHomBicat.smul_whiskerRight,
      GradedHomBicat.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
      inv_mul_cancel₀ ht, one_smul]
  right_triangle := by
    rw [← adj.right_triangle]
    simp only [rightZigzag, bicategoricalComp, GradedHomBicat.smul_whiskerRight,
      GradedHomBicat.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
      inv_mul_cancel₀ ht, one_smul]

omit [GradedBicategory.IsLinear B k] in
/-- **The clockwise degree-zero bubble** at the weight `n = wt (r + 1)` of a left cup
`u : 𝟙 ⟶ R_m E_m` (`m = n - 2`): `u`, then `n - 1` (normalized) dots on `E 1_m`, then the counit
of `E 1_m ⊣ R_m`. -/
def cwBubble {r : ℤ} (u : 𝟙 (of (S.obj (r + 1))) ⟶ S.grR r ≫ S.grE r) :
    𝟙 (of (S.obj (r + 1))) ⟶ 𝟙 (of (S.obj (r + 1))) :=
  u ≫ S.grR r ◁ powComp (S.grDotN r) ((S.wt (r + 1)).toNat - 1) ≫ S.grCounit r

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **CL (4.1) for `n ≥ 1`**: at a weight `n = wt (q + 1 + 1) ≥ 1`, given (3.2) at `n - 2` and at
the weights `> n`, its numerical shadow at the weights `≥ n`, and `End(E 1_{n-2}) = k` when
`1_n ≠ 0`, there is a left adjunction `R_{n-2} ⊣ E 1_{n-2}` (homogeneous unit and counit of
degrees `-2(n-2)-2`, `2(n-2)+2`) whose clockwise degree-zero bubble is the identity of `1_n`. -/
theorem exists_normalized_leftAdj [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {q : ℤ}
    (hn : 1 ≤ S.wt (q + 1 + 1)) (h : S.AdjHyp (q + 1))
    (hend : ¬ IsZero (𝟙 (S.obj (q + 1 + 1))) → finrank k (S.E (q + 1) ⟶ S.E (q + 1)) = 1)
    (hyp : ∀ r', q + 1 + 1 < r' → S.AdjHyp r') (hnum : ∀ r', q + 1 < r' → S.NumAdj r') :
    ∃ adj : S.grR (q + 1) ⊣ S.grE (q + 1),
      IsHomogeneous adj.unit (-(2 * S.wt (q + 1) + 2)) ∧
      IsHomogeneous adj.counit (2 * S.wt (q + 1) + 2) ∧ S.cwBubble adj.unit = 𝟙 _ := by
  by_cases h2 : IsZero (𝟙 (S.obj (q + 1 + 1)))
  · have hz : IsZero (𝟙 (of (S.obj (q + 1 + 1)))) := (incl _).map_isZero h2
    exact ⟨S.leftAdj h, S.isHomogeneous_leftAdj_unit h, S.isHomogeneous_leftAdj_counit h,
      hz.eq_of_src _ _⟩
  have hw : S.wt (q + 1 + 1) = S.wt (q + 1) + 2 := S.wt_add_one _
  have hN : ((S.wt (q + 1 + 1)).toNat : ℤ) = S.wt (q + 1 + 1) := Int.toNat_of_nonneg (by omega)
  obtain ⟨e'⟩ := S.exists_EFDecomp (r := q + 1) (by omega)
  have hb := S.topBubble_ne_zero hn hyp hnum h2 e'
  let tb : ℤ := 1 * (((S.wt (q + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))
  let osb : of₁ (S.oneShift (q + 1) 0) ≅ 𝟙 (of (S.obj (q + 1 + 1))) :=
    shiftIso₁ (𝟙 (S.obj (q + 1 + 1))) tb
  let u₀ : 𝟙 (of (S.obj (q + 1 + 1))) ⟶ S.grR (q + 1) ≫ S.grE (q + 1) :=
    osb.inv ≫ incl₂ (ι e' 0) ≫ (S.rhoSourceIso (q + 1)).inv
  have hu₀ : IsHomogeneous u₀ (-(2 * S.wt (q + 1) + 2)) :=
    (((shiftIso₁_inv_isHomogeneous (𝟙 _) tb : IsHomogeneous osb.inv (-tb))).comp
      ((isHomogeneous_incl₂ _).comp (S.isHomogeneous_rhoSourceIso_inv (q + 1)) rfl) rfl).of_eq
        (by simp only [tb, wt] at hN hw ⊢; push_cast; omega)
  obtain ⟨c, hc⟩ := S.exists_eq_smul_leftAdj_unit h (hend h2) hu₀
  have hdotN : IsHomogeneous (S.grDotN (q + 1)) 2 := (isHomogeneous_of₂ _ _).smul _
  have hbubH : IsHomogeneous (S.cwBubble (S.leftAdj h).unit) 0 :=
    ((S.isHomogeneous_leftAdj_unit h).comp ((isHomogeneous_whiskerLeft _
      (GradedHomBicat.isHomogeneous_powComp hdotN _)).comp (isHomogeneous_incl₂ _) rfl)
        rfl).of_eq (by
          have : (((S.wt (q + 1 + 1)).toNat - 1 : ℕ) : ℤ) = S.wt (q + 1 + 1) - 1 := by omega
          rw [this]; omega)
  obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hbubH
  have hid0 : (𝟙 (𝟙 (S.obj (q + 1 + 1))) : _) ≠ 0 := fun h0 =>
    h2 ((IsZero.iff_id_eq_zero _).2 h0)
  obtain ⟨β, hβ⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).1 (S.hom_zero _ h2) g
  have hβg : S.cwBubble (S.leftAdj h).unit = β • 𝟙 _ := by
    rw [hg, ← hβ]
    change (incl _).map (β • 𝟙 _) = _
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hb
    change u₀ ≫ _ = 0
    rw [hc, Linear.smul_comp]
    change c • S.cwBubble (S.leftAdj h).unit = 0
    rw [hβg, zero_smul, smul_zero]
  refine ⟨scaleAdj (S.leftAdj h) (inv_ne_zero hβ0),
    (S.isHomogeneous_leftAdj_unit h).smul _, (S.isHomogeneous_leftAdj_counit h).smul _, ?_⟩
  change (β⁻¹ • (S.leftAdj h).unit) ≫ _ = _
  rw [Linear.smul_comp]
  change β⁻¹ • S.cwBubble (S.leftAdj h).unit = _
  rw [hβg, smul_smul, inv_mul_cancel₀ hβ0, one_smul]

/-- **CL (4.1) for `n ≥ 1` under (BB_w)**: for every `E 1_m` with `m ≥ -1` there is a left
adjunction `R_m ⊣ E 1_m` whose clockwise degree-zero bubble at the weight `m + 2` is the
identity. -/
theorem BBw.exists_normalized_leftAdj [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    {S : StrongSl2 k B} (hS : S.BBw) {q : ℤ} (hn : 1 ≤ S.wt (q + 1 + 1)) :
    ∃ adj : S.grR (q + 1) ⊣ S.grE (q + 1),
      IsHomogeneous adj.unit (-(2 * S.wt (q + 1) + 2)) ∧
      IsHomogeneous adj.counit (2 * S.wt (q + 1) + 2) ∧ S.cwBubble adj.unit = 𝟙 _ := by
  have hyp : ∀ r', S.AdjHyp r' := hS.adjHyp
  refine S.exists_normalized_leftAdj hn (hyp _) ?_ (fun r' _ => hyp r')
    (fun r' _ => hS.numAdj r')
  intro h2
  have hw : S.wt (q + 1 + 1) = S.wt (q + 1) + 2 := S.wt_add_one _
  rcases le_or_gt 0 (S.wt (q + 1)) with h0 | h0
  · exact S.lem1_zero (r₀ := q + 1) h0 (fun r' _ => hyp r') le_rfl h2
  · have hobj : ¬ IsZero (𝟙 (S.obj (q + 1))) := fun hz => by
      obtain ⟨e'⟩ := S.exists_EFDecomp (r := q + 1) (by omega)
      apply S.topBubble_ne_zero hn (fun r' _ => hyp r') (fun r' _ => hS.numAdj r') h2 e'
      have hZ : IsZero (S.grR (q + 1) ≫ S.grE (q + 1)) :=
        (incl _).map_isZero (isZero_comp_left (isZero_of_isZero_id_tgt hz _) _)
      rw [hZ.eq_of_src (S.grCounit (q + 1)) 0, comp_zero, comp_zero]
    exact S.lem1Neg_zero (r₁ := q + 1) (by omega) (fun r' _ => hyp r') le_rfl (by omega) hobj

end StrongSl2

end Categorification.TwoRep
