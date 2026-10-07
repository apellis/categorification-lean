/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FixedAdjunction
import Categorification.TwoRep.DotNondegNeg

/-!
# Fixing the left adjunctions at the weights `n ≤ -2` (CL §4.1)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §4.1 ("Fixing adjunction maps"), the normalization (4.1) for `n < -1`.

For `n = wt r ≤ -2`, CL fix the scalar in the left adjunction `R_n ⊣ E 1_n`
(`StrongSl2.leftAdj`) so that the counter-clockwise degree-zero bubble at the weight `n` (the unit
of `E 1_n ⊣ R_n`, then `-n-1` dots on `E 1_n`, then the left cap, i.e. the counit of
`R_n ⊣ E 1_n`; `StrongSl2.ccwBubble`) is the identity of `1_n`. This is possible because that
bubble is nonzero, which is CL Corollary 3.7 for `n < 0` (`StrongSl2.BBw.isIso_bubbleN`)
transported to the graded-Hom bicategory (`StrongSl2.BBw.botBubble_ne_zero`), and because the left
cap is unique up to a scalar (`exists_eq_smul_leftAdj_counit`, CL Corollary 3.10). The left
adjunctions of `E 1_m` for `m ≥ -1` are normalized by the clockwise bubbles instead
(`FixedAdjunction.lean`); together the two normalizations fix every left adjunction, as in CL's
table in §4.1.

## Main declarations

* `StrongSl2.ccwBubble`: the counter-clockwise degree-zero bubble of a left cap;
* `StrongSl2.BBw.botBubble_ne_zero`: under (BB_w), the bubble built from the cap of a
  decomposition datum of `F E 1_n` is nonzero;
* `StrongSl2.BBw.exists_normalized_leftAdj_neg`: **CL (4.1) for `n < -1` under (BB_w)**.
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

/-- **The counter-clockwise degree-zero bubble** at the weight `n = wt r` of a left cap
`c : E_n R_n ⟶ 𝟙`: the unit of `E 1_n ⊣ R_n`, then `-n-1` (normalized) dots on `E 1_n`, then
`c`. -/
def ccwBubble {r : ℤ} (c : S.grE r ≫ S.grR r ⟶ 𝟙 (of (S.obj r))) :
    𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r)) :=
  S.grUnit r ≫ powComp (S.grDotN r) ((-S.wt r).toNat - 1) ▷ S.grR r ≫ c

theorem ccwBubble_smul {r : ℤ} (t : k) (c : S.grE r ≫ S.grR r ⟶ 𝟙 (of (S.obj r))) :
    S.ccwBubble (t • c) = t • S.ccwBubble c := by
  simp only [ccwBubble, Linear.comp_smul]

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- The cap of a decomposition datum of `F E 1_n` (`n = wt (q + 1) ≤ 0`): the projection onto the
top summand `1_n⟨n+1⟩`, as a 2-morphism `E_n R_n ⟶ 𝟙` of the graded-Hom bicategory. -/
def capN {q : ℤ} (e : S.FEDecomp q) : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ 𝟙 (of (S.obj (q + 1))) :=
  (S.rhoTargetIso q).hom ≫ incl₂ (πN e ((-S.wt (q + 1)).toNat - 1)) ≫
    (shiftIso₁ (𝟙 (S.obj (q + 1)))
      (1 * ((((-S.wt (q + 1)).toNat : ℕ) : ℤ) - 1 - 2 *
        (((-S.wt (q + 1)).toNat - 1 : ℕ) : ℤ)))).hom

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem isHomogeneous_capN {q : ℤ} (hn : S.wt (q + 1) ≤ -1) (e : S.FEDecomp q) :
    IsHomogeneous (S.capN e) (2 * S.wt (q + 1) + 2) :=
  ((S.isHomogeneous_rhoTargetIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (shiftIso₁_hom_isHomogeneous _ _) rfl) rfl).of_eq (by
      have : ((((-S.wt (q + 1)).toNat - 1 : ℕ) : ℤ)) = -S.wt (q + 1) - 1 := by omega
      rw [this]; simp only [wt] at hn ⊢; omega)

/-- **The counter-clockwise degree-zero bubble of CL Corollary 3.7 is nonzero** under (BB_w): at
the object `q + 1` of weight `n ≤ -2`, the unit of `E 1_n ⊣ R_n`, followed by `-n-1` dots on
`E 1_n` and the cap of a decomposition datum of `F E 1_n`, is a nonzero endomorphism of `1_n`. -/
theorem BBw.botBubble_ne_zero [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) {q : ℤ}
    (hn : S.wt (q + 1) ≤ -2) (h2 : ¬ IsZero (𝟙 (S.obj (q + 1)))) (e : S.FEDecomp q) :
    S.ccwBubble (S.capN e) ≠ 0 := by
  have hN : ((-S.wt (q + 1)).toNat : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  have hw : S.wt (q + 1) = S.wt q + 2 := S.wt_add_one q
  set N := (-S.wt (q + 1)).toNat with hNdef
  let ρT := S.rhoTargetIso q
  let tN : ℤ := 1 * (((N : ℕ) : ℤ) - 1 - 2 * ((N - 1 : ℕ) : ℤ))
  let osN : of₁ (S.oneShiftNeg q (N - 1)) ≅ 𝟙 (of (S.obj (q + 1))) :=
    shiftIso₁ (𝟙 (S.obj (q + 1))) tN
  let a : 𝟙 (of (S.obj (q + 1))) ⟶ of₁ (S.oneShiftNeg q 0) :=
    S.grUnit (q + 1) ≫ ρT.hom ≫ incl₂ (πN e 0)
  -- `E 1_n` is nonzero, so the unit of `E 1_n ⊣ R_n` is nonzero
  have hE : ¬ IsZero (S.E (q + 1)) := by
    intro hz
    have hFE : IsZero (S.E (q + 1) ≫ S.F (q + 1)) := isZero_comp_left hz _
    have h1 : IsZero (S.oneShiftNeg q 0) := by
      rw [IsZero.iff_id_eq_zero, ← ιN_πN_self e (j := 0) (by omega),
        hFE.eq_of_tgt (ιN e 0) 0, zero_comp]
    apply h2
    exact ((shiftFunctor _ (-(1 * (((N : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))))).map_isZero
      h1).of_iso ((shiftFunctorCompIsoId _ _ _ (add_neg_cancel _)).app _).symm
  have hη0 := S.grUnit_ne_zero hE
  -- the decomposition of the identity of `F E 1_n`
  have htot' : ∑ j ∈ Finset.range N, incl₂ (πN e j) ≫ incl₂ (ιN e j) +
      incl₂ (πEF e) ≫ incl₂ (ιEF e) = 𝟙 (of₁ (S.E (q + 1) ≫ S.F (q + 1))) := by
    rw [← incl₂_id, ← totalN e, GradedHomBicat.incl₂_add', GradedHomBicat.incl₂_sum']
    simp only [incl₂_comp]
    rfl
  have hρ : IsHomogeneous ρT.hom (S.n₀ + 2 * (q + 1) + 1) := S.isHomogeneous_rhoTargetIso_hom q
  have hηρ : IsHomogeneous (S.grUnit (q + 1) ≫ ρT.hom) (S.n₀ + 2 * (q + 1) + 1) :=
    ((isHomogeneous_incl₂ _).comp hρ rfl).of_eq (by ring)
  have hM : ∀ j : ℕ, j < N → j ≠ 0 → (S.grUnit (q + 1) ≫ ρT.hom) ≫ incl₂ (πN e j) = 0 := by
    intro j hj hj0
    refine GradedHomBicat.eq_zero_of_isHomogeneous (k := k) (d := S.n₀ + 2 * (q + 1) + 1)
      (hηρ.comp (isHomogeneous_incl₂ _) (by ring)) ?_
    rw [oneShiftNeg, finrank_hom_shift_right k _ _ (b := -(S.n₀ + 2 * (q + 1) + 1)) (by ring),
      finrank_hom_shift_shift k _ _
        (c := 1 * ((((-S.wt (q + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) +
          (S.n₀ + 2 * (q + 1) + 1)) (by ring)]
    exact S.hom_neg _ _ (by simp only [wt] at hN hn ⊢; omega)
  have hMEF : (S.grUnit (q + 1) ≫ ρT.hom) ≫ incl₂ (πEF e) = 0 := by
    refine GradedHomBicat.eq_zero_of_isHomogeneous (k := k) (d := S.n₀ + 2 * (q + 1) + 1)
      (hηρ.comp (isHomogeneous_incl₂ _) (by ring)) ?_
    have hyp : ∀ r', r' < q + 1 → S.AdjHyp r' := fun r' _ => hS.adjHyp r'
    rw [finrank_hom_shift_right k _ _ (b := -(S.n₀ + 2 * (q + 1) + 1)) (by ring),
      ← ((hyp q (by omega)).dimAdj S).left,
      finrank_hom_congr_left k (idShiftCompShiftIso (S.F q)
        (s := -(S.wt q + 1) + -(S.n₀ + 2 * (q + 1) + 1)) rfl),
      finrank_hom_shift_left k _ _ (b := -(-(S.wt q + 1) + -(S.n₀ + 2 * (q + 1) + 1))) (by ring),
      S.finrank_F_F_eq]
    refine S.lem1Neg_neg (r₁ := q + 1) (by omega) hyp q (by omega) _ ?_
    simp only [wt] at hw hn ⊢
    omega
  have hsplit : ∀ {W : of (S.obj (q + 1)) ⟶ of (S.obj (q + 1))}
      (Y : of₁ (S.E (q + 1) ≫ S.F (q + 1)) ⟶ W),
      (S.grUnit (q + 1) ≫ ρT.hom) ≫ Y = a ≫ incl₂ (ιN e 0) ≫ Y := by
    intro W Y
    calc (S.grUnit (q + 1) ≫ ρT.hom) ≫ Y = (S.grUnit (q + 1) ≫ ρT.hom) ≫ 𝟙 _ ≫ Y := by
          rw [Category.id_comp]
      _ = (S.grUnit (q + 1) ≫ ρT.hom) ≫ (∑ j ∈ Finset.range N,
            incl₂ (πN e j) ≫ incl₂ (ιN e j) + incl₂ (πEF e) ≫ incl₂ (ιEF e)) ≫ Y := by
          rw [htot']
      _ = ∑ j ∈ Finset.range N, ((S.grUnit (q + 1) ≫ ρT.hom) ≫ incl₂ (πN e j)) ≫
            incl₂ (ιN e j) ≫ Y +
          ((S.grUnit (q + 1) ≫ ρT.hom) ≫ incl₂ (πEF e)) ≫ incl₂ (ιEF e) ≫ Y := by
          simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
            Preadditive.comp_sum, Category.assoc]
      _ = _ := by
          rw [hMEF, zero_comp, add_zero, Finset.sum_eq_single 0]
          · simp only [a, Category.assoc]
          · intro j hj hne
            rw [hM j (Finset.mem_range.1 hj) hne, zero_comp]
          · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have ha0 : a ≠ 0 := by
    intro h
    apply hη0
    have := hsplit ρT.inv
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, h, zero_comp] at this
    exact this
  -- the dots commute with the unshifting of `R_n`
  have hx' : powComp (S.grDotN (q + 1)) (N - 1) ▷ S.grR (q + 1) ≫ ρT.hom =
      ρT.hom ≫ powComp (S.grDotN (q + 1)) (N - 1) ▷ of₁ (S.F (q + 1)) := by
    simp only [ρT, rhoTargetIso, whiskerLeftIso_hom]
    exact (whisker_exchange _ _).symm
  have hpow : powComp (S.grDotN (q + 1)) (N - 1) ▷ of₁ (S.F (q + 1)) =
      (((S.rQ⁻¹ : kˣ) : k) ^ (N - 1)) •
        of₂ (((N - 1 : ℕ) : ℤ) * 2) (shPow (S.dotFE q) (N - 1)) := by
    rw [powComp_whiskerRight, show S.grDotN (q + 1) ▷ of₁ (S.F (q + 1)) =
        ((S.rQ⁻¹ : kˣ) : k) • of₂ 2 (S.dotFE q) from ?_, powComp_smul,
      ← GradedHomBicat.of₂_shPow]
    rw [show S.grDotN (q + 1) = ((S.rQ⁻¹ : kˣ) : k) • S.grDot (q + 1) from rfl,
      GradedHomBicat.smul_whiskerRight, of₂_whiskerRight]
    rfl
  have hbub : incl₂ (ιN e 0) ≫ of₂ (((N - 1 : ℕ) : ℤ) * 2) (shPow (S.dotFE q) (N - 1)) ≫
      incl₂ (πN e (N - 1)) = of₂ (((N - 1 : ℕ) : ℤ) * 2) (bubbleN e) := by
    rw [incl₂_eq_of₂, incl₂_eq_of₂, of₂_comp_of₂ (shPow (S.dotFE q) (N - 1))
      (ShiftedHom.mk₀ (0 : ℤ) rfl (πN e (N - 1))) (zero_add _),
      of₂_comp_of₂ _ _ (add_zero _), ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
    simp only [bubbleN, cupDotsN, Category.assoc]
    rfl
  have hbI : IsIso (bubbleN e) := hS.isIso_bubbleN e (by omega)
  have hbI' : IsIso (of₂ (((N - 1 : ℕ) : ℤ) * 2) (bubbleN e)) := isIso_of₂ _ _
  have hc0 : (((S.rQ⁻¹ : kˣ) : k) ^ (N - 1)) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have key : S.ccwBubble (S.capN e) = (((S.rQ⁻¹ : kˣ) : k) ^ (N - 1)) •
      (a ≫ of₂ (((N - 1 : ℕ) : ℤ) * 2) (bubbleN e) ≫ osN.hom) := by
    show S.grUnit (q + 1) ≫ powComp (S.grDotN (q + 1)) (N - 1) ▷ S.grR (q + 1) ≫ ρT.hom ≫
      incl₂ (πN e (N - 1)) ≫ osN.hom = _
    rw [← Category.assoc (powComp _ _ ▷ _), hx']
    simp only [Category.assoc]
    rw [← Category.assoc (S.grUnit (q + 1)), hsplit, hpow]
    simp only [Linear.smul_comp, Linear.comp_smul, reassoc_of% hbub]
  intro h0
  have h1 := (smul_eq_zero.1 (key.symm.trans h0)).resolve_left hc0
  exact ha0 ((cancel_mono _).1 (h1.trans zero_comp.symm))

/-- **CL (4.1) for `n < -1` under (BB_w)**: for every `E 1_n` with `n ≤ -2` there is a left
adjunction `R_n ⊣ E 1_n` (homogeneous unit and counit of degrees `-2n-2`, `2n+2`) whose
counter-clockwise degree-zero bubble at the weight `n` is the identity. -/
theorem BBw.exists_normalized_leftAdj_neg [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    (hS : S.BBw) {r : ℤ} (hn : S.wt r ≤ -2) :
    ∃ adj : S.grR r ⊣ S.grE r,
      IsHomogeneous adj.unit (-(2 * S.wt r + 2)) ∧
      IsHomogeneous adj.counit (2 * S.wt r + 2) ∧ S.ccwBubble adj.counit = 𝟙 _ := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by ring⟩
  have h : S.AdjHyp (q + 1) := hS.adjHyp _
  by_cases h2 : IsZero (𝟙 (S.obj (q + 1)))
  · have hz : IsZero (𝟙 (of (S.obj (q + 1)))) := (incl _).map_isZero h2
    exact ⟨S.leftAdj h, S.isHomogeneous_leftAdj_unit h, S.isHomogeneous_leftAdj_counit h,
      hz.eq_of_src _ _⟩
  obtain ⟨e⟩ := S.exists_FEDecomp (r := q) (by omega)
  have hb := BBw.botBubble_ne_zero S hS hn h2 e
  have hend : finrank k (S.E (q + 1) ⟶ S.E (q + 1)) = 1 :=
    S.lem1Neg_zero (r₁ := q + 1) (by omega) (fun r' _ => hS.adjHyp r') le_rfl (by omega) h2
  obtain ⟨t, ht⟩ := S.exists_eq_smul_leftAdj_counit h hend (S.isHomogeneous_capN (by omega) e)
  have hdotN : IsHomogeneous (S.grDotN (q + 1)) 2 := (isHomogeneous_of₂ _ _).smul _
  have hbubH : IsHomogeneous (S.ccwBubble (S.leftAdj h).counit) 0 :=
    ((isHomogeneous_incl₂ _).comp ((isHomogeneous_whiskerRight
      (GradedHomBicat.isHomogeneous_powComp hdotN _) _).comp
        (S.isHomogeneous_leftAdj_counit h) rfl) rfl).of_eq (by
          have : (((-S.wt (q + 1)).toNat - 1 : ℕ) : ℤ) = -S.wt (q + 1) - 1 := by omega
          rw [this]; omega)
  obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hbubH
  have hid0 : (𝟙 (𝟙 (S.obj (q + 1))) : _) ≠ 0 := fun h0 =>
    h2 ((IsZero.iff_id_eq_zero _).2 h0)
  obtain ⟨β, hβ⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).1 (S.hom_zero _ h2) g
  have hβg : S.ccwBubble (S.leftAdj h).counit = β • 𝟙 _ := by
    rw [hg, ← hβ]
    change (incl _).map (β • 𝟙 _) = _
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hb
    rw [ht, ccwBubble_smul, hβg, zero_smul, smul_zero]
  refine ⟨scaleAdj (S.leftAdj h) hβ0,
    (S.isHomogeneous_leftAdj_unit h).smul _, (S.isHomogeneous_leftAdj_counit h).smul _, ?_⟩
  change S.ccwBubble (β⁻¹ • (S.leftAdj h).counit) = _
  rw [ccwBubble_smul, hβg, smul_smul, inv_mul_cancel₀ hβ0, one_smul]

end StrongSl2

end Categorification.TwoRep
