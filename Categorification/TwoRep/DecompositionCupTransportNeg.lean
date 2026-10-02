/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DotMateBridge
import Categorification.TwoRep.DownwardNilHeckeRepresentation

/-!
# Transport of the lowest negative decomposition cup

Only the cup summand `ιN e 0` is considered. Its Hom space is computed using
the supplied adjunction and `lem1Neg_zero`, hence only strictly lower `AdjHyp`.
No dot nondegeneracy, rank comparison, or automatic biadjointness is assumed.
-/

noncomputable section
namespace Categorification.TwoRep.StrongSl2
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)
open GradedHomBicat ShiftRemoval
universe w v u
variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B)

/-- The actual degree of the negative cup has a one-dimensional Hom space.
The adjunction used here is supplied, not the desired adjunction at this weight. -/
theorem finrank_cupNeg_eq_one {r : ℤ} (hn : S.wt (r + 1) < 0)
    (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    finrank k (𝟙 (S.obj (r + 1)) ⟶
      (S.E (r + 1) ≫ S.F (r + 1))⟦S.wt (r + 1) + 1⟧) = 1 := by
  rw [finrank_hom_congr_right k _ (whiskerLeftShiftIso _ _ _).symm,
    ← (S.dimAdj (r + 1)).left,
    finrank_hom_congr_left k (λ_ _)]
  exact S.lem1Neg_zero hn.le hyp le_rfl (by omega) hI

/-- The source of the actual decomposition inclusion gives that same line. -/
theorem finrank_oneShiftNeg_cup_eq_one {r : ℤ} (hn : S.wt (r + 1) < 0)
    (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    finrank k (S.oneShiftNeg r 0 ⟶ S.E (r + 1) ≫ S.F (r + 1)) = 1 := by
  have hN : ((-S.wt (r + 1)).toNat : ℤ) = -S.wt (r + 1) :=
    Int.toNat_of_nonneg (by omega)
  rw [oneShiftNeg, finrank_hom_shift_left k _ _
    (b := S.wt (r + 1) + 1) (by rw [hN]; simp)]
  exact S.finrank_cupNeg_eq_one hn hyp hI

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The inclusion is nonzero because it is split and the weight identity is nonzero. -/
theorem iotaN_zero_ne_zero {r : ℤ} (e : S.FEDecomp r)
    (hn : S.wt (r + 1) < 0) (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    ιN e 0 ≠ 0 := by
  intro hz
  have h := ιN_πN_self e (j := 0) (by omega)
  rw [hz, zero_comp] at h
  have hs : IsZero (S.oneShiftNeg r 0) := (IsZero.iff_id_eq_zero _).2 h.symm
  apply hI
  apply (IsZero.iff_id_eq_zero _).2
  apply (shiftFunctor _ (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (0 : ℤ)))).map_injective
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hs

variable [GradedBicategory.ShiftCoherence B]

/-- The supplied cup, as an ordinary homogeneous morphism. -/
def suppliedCupNegHom (r : ℤ) :
    𝟙 (S.obj (r + 1)) ⟶
      (S.E (r + 1) ≫ S.F (r + 1))⟦S.wt (r + 1) + 1⟧ :=
  (S.adj (r + 1)).unit ≫ (whiskerLeftShiftIso _ _ _).hom

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- Its graded inclusion is exactly the shift-corrected supplied cup. -/
theorem of_suppliedCupNegHom (r : ℤ) :
    of₂ (S.wt (r + 1) + 1) (S.suppliedCupNegHom r) =
      incl₂ (S.adj (r + 1)).unit ≫ of₁ (S.E (r + 1)) ◁
        (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv := by
  change _ = incl₂ (S.adj (r + 1)).unit ≫
    of₁ (S.E (r + 1)) ◁ of₂ (S.wt (r + 1) + 1) (down _ _)
  rw [incl₂_eq_of₂, whiskerLeft_of₂, of₂_comp_of₂ _ _ (add_zero _)]
  congr 1
  simp [suppliedCupNegHom, down, shWhiskerLeft, ShiftedHom.map,
    ShiftedHom.mk₀_comp, whiskerLeftShiftIso, wt]
  erw [Category.id_comp]


omit [GradedBicategory.ShiftCoherence B] in
/-- The supplied cup is nonzero at a nonzero negative weight. -/
theorem suppliedCupNegHom_ne_zero {r : ℤ} (hn : S.wt (r + 1) < 0)
    (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) : S.suppliedCupNegHom r ≠ 0 := by
  intro hz
  have hu : (S.adj (r + 1)).unit = 0 := by
    apply (cancel_mono (whiskerLeftShiftIso (S.E (r + 1)) (S.F (r + 1))
      (S.wt (r + 1) + 1)).hom).1
    rw [zero_comp]
    exact hz
  have ht := (S.adj (r + 1)).left_triangle
  have hi := congrArg (fun t => (λ_ (S.E (r + 1))).inv ≫ t ≫
    (ρ_ (S.E (r + 1))).hom) ht
  have hid : 𝟙 (S.E (r + 1)) = 0 := by
    simpa [leftZigzag, bicategoricalComp, hu] using hi.symm
  have hzE : IsZero (S.E (r + 1)) := (IsZero.iff_id_eq_zero _).2 hid
  have h0 := finrank_hom_of_isZero_left k hzE (S.E (r + 1))
  have h1 := S.lem1Neg_zero hn.le hyp le_rfl (by omega) hI
  omega


/-- The actual decomposition cup, after removing its source shift, is a nonzero
scalar multiple of the supplied shift-corrected adjunction cup. This holds for
every decomposition datum; compatibility is a conclusion, not an assumption. -/
theorem iotaN_zero_eq_nonzero_smul_suppliedCup {r : ℤ} (e : S.FEDecomp r)
    (hn : S.wt (r + 1) < 0) (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    ∃ c : k, c ≠ 0 ∧
      (shiftIso (𝟙 (S.obj (r + 1)))
        (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (0 : ℤ)))).hom ≫
          incl₂ (ιN e 0) =
        c • (incl₂ (S.adj (r + 1)).unit ≫ of₁ (S.E (r + 1)) ◁
          (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv) := by
  let q : ℤ := 1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (0 : ℤ))
  have hN : ((-S.wt (r + 1)).toNat : ℤ) = -S.wt (r + 1) :=
    Int.toNat_of_nonneg (by omega)
  have hdeg : 0 + -q = S.wt (r + 1) + 1 := by dsimp [q]; rw [hN]; ring
  let t : ShiftedHom (𝟙 (S.obj (r + 1)))
      (S.E (r + 1) ≫ S.F (r + 1)) (S.wt (r + 1) + 1) :=
    (up (𝟙 (S.obj (r + 1))) q).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (ιN e 0)) hdeg
  have ht : of₂ (S.wt (r + 1) + 1) t =
      (shiftIso (𝟙 (S.obj (r + 1))) q).hom ≫ incl₂ (ιN e 0) :=
    (of₂_comp_of₂ _ _ hdeg).symm
  have htne : t ≠ 0 := by
    intro hz
    have hh : (shiftIso (𝟙 (S.obj (r + 1))) q).hom ≫ incl₂ (ιN e 0) = 0 := by
      rw [← ht, hz]
      exact GradedHomCat.homOf_zero _
    have hi : incl₂ (ιN e 0) = 0 := by
      apply (cancel_epi (shiftIso (𝟙 (S.obj (r + 1))) q).hom).1
      simpa only [comp_zero] using hh
    apply S.iotaN_zero_ne_zero e hn hI
    apply (GradedHomCat.incl _).map_injective
    change incl₂ (ιN e 0) = incl₂ 0
    simpa only [incl₂_eq_of₂, ShiftedHom.mk₀_zero, of₂, GradedHomCat.homOf_zero] using hi
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _
    (S.suppliedCupNegHom_ne_zero hn hyp hI)).mp (S.finrank_cupNeg_eq_one hn hyp hI) t
  refine ⟨c, ?_, ?_⟩
  · intro hz
    apply htne
    rw [← hc, hz, zero_smul]
  · rw [← ht, ← S.of_suppliedCupNegHom]
    change GradedHomCat.homOf _ t = c • GradedHomCat.homOf _ _
    rw [← GradedHomCat.homOf_smul, hc]


/-- The original upward dot slides to the actual downward mate at the actual
lowest inclusion of any negative decomposition. No higher inclusion is asserted. -/
theorem iotaN_zero_dotFE {r : ℤ} (e : S.FEDecomp r)
    (hn : S.wt (r + 1) < 0) (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    incl₂ (ιN e 0) ≫ of₂ 2 (S.dotFE r) =
      incl₂ (ιN e 0) ≫ of₁ (S.E (r + 1)) ◁ of₂ 2 (S.fDot (r + 1)) := by
  obtain ⟨c, _, hc⟩ := S.iotaN_zero_eq_nonzero_smul_suppliedCup e hn hyp hI
  apply (cancel_epi (shiftIso (𝟙 (S.obj (r + 1)))
    (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (0 : ℤ)))).hom).1
  rw [← Category.assoc, ← Category.assoc, hc, Linear.smul_comp, Linear.smul_comp,
    S.suppliedCup_dotFE]


/-- The cup slide in the original Hom category, not just its faithful graded inclusion. -/
theorem iotaN_zero_dotFE_hom {r : ℤ} (e : S.FEDecomp r)
    (hn : S.wt (r + 1) < 0) (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    ιN e 0 ≫ S.dotFE r = ιN e 0 ≫ shWhiskerLeft (S.E (r + 1)) (S.fDot (r + 1)) := by
  have h := S.iotaN_zero_dotFE e hn hyp hI
  rw [whiskerLeft_of₂, incl₂_eq_of₂, of₂_comp_of₂ _ _ (add_zero _),
    of₂_comp_of₂ _ _ (add_zero _), ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp] at h
  exact of₂_injective 2 h

/-- Right whiskering the actual decomposition cup slide gives exactly the
first-factor downward dot on `FF`, the dot used by `nhF.xL`. -/
theorem iotaN_zero_dotFE_whisker_F {r : ℤ} (e : S.FEDecomp r)
    (hn : S.wt (r + 1) < 0) (hyp : ∀ s, s < r + 1 → S.AdjHyp s)
    (hI : ¬ IsZero (𝟙 (S.obj (r + 1)))) :
    incl₂ (ιN e 0) ▷ of₁ (S.F r) ≫
      of₂ 2 (shWhiskerRight (S.dotFE r) (S.F r)) ≫
      (α_ (of₁ (S.E (r + 1))) (of₁ (S.F (r + 1))) (of₁ (S.F r))).hom =
    incl₂ (ιN e 0) ▷ of₁ (S.F r) ≫
      (α_ (of₁ (S.E (r + 1))) (of₁ (S.F (r + 1))) (of₁ (S.F r))).hom ≫
      of₁ (S.E (r + 1)) ◁ of₂ 2 (shWhiskerRight (S.fDot (r + 1)) (S.F r)) := by
  rw [← of₂_whiskerRight, ← of₂_whiskerRight,
    ← comp_whiskerRight_assoc, S.iotaN_zero_dotFE e hn hyp hI,
    comp_whiskerRight_assoc, associator_naturality_middle]

end Categorification.TwoRep.StrongSl2
