/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DownwardDividedPower
import Categorification.TwoRep.DotEntriesNeg
import Categorification.TwoRep.StepLemmas

/-!
# A negative-weight induction-step vanishing lemma

At `n = wt r ≤ -2`, assuming `AdjHyp` only strictly below `r`, a
negative-degree endomorphism of `F (r + 1)` is killed by right whiskering
with `F r`. This is an actual downward version of the nilHecke argument
in `StepLemmas.lemA`; it does not assert that the endomorphism itself is zero.
The nilHecke operators are the published `fDot` and `ffCross`, obtained
from the supplied adjunctions `S.adj` and grading coherence.

The retract consequence rules out repeated shifts of a summand visible
under that whiskering. This is a prerequisite for a negative rank argument,
not a proof of `DotNondegNeg`: in particular the upward `dotFE` has not
been identified with the downward dot on `FF`. No biadjointness or
per-summand lower-Hom bound is asserted.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B)

omit [GradedBicategory.ShiftCoherence B] in
/-- At the negative induction step, the actual `FF` endomorphisms below
 degree `-2` vanish. Only `AdjHyp` strictly below `r` is used. -/
theorem hom_FF_neg_step_eq_zero {r : ℤ} (hn : S.wt (r + 1) ≤ 0)
    (hyp : ∀ r', r' < r → S.AdjHyp r') {m : ℤ} (hm : m < -2)
    (f : ShiftedHom (S.F (r + 1) ≫ S.F r) (S.F (r + 1) ≫ S.F r) m) : f = 0 := by
  have hw := S.wt_add_one r
  apply eq_zero_of_finrank_eq_zero (k := k) (f := f)
  rw [S.finrank_FF_FF_eq]
  exact S.cor0Neg_neg (r₁ := r) (by omega) hyp r le_rfl hn m hm

/-- Negative-step Lemma A on the actual downward factors. The endomorphism
of `F (r + 1)` is not assumed to vanish, and no induction hypothesis at `r`
or `r + 1` is used. -/
theorem lemANeg {r : ℤ} (hn : S.wt (r + 1) ≤ 0)
    (hyp : ∀ r', r' < r → S.AdjHyp r') {m : ℤ} (hm : m < 0)
    (f : ShiftedHom (S.F (r + 1)) (S.F (r + 1)) m) :
    shWhiskerRight f (S.F r) = 0 := by
  set N := S.nhF r
  set φ : ShiftedHom (S.F (r + 1) ≫ S.F r) (S.F (r + 1) ≫ S.F r) m :=
    shWhiskerRight f (S.F r)
  have hτφ : N.τ.comp φ (by ring : m + -2 = m - 2) = 0 :=
    S.hom_FF_neg_step_eq_zero hn hyp (by omega) _
  have hcomm : N.xR.comp φ (by ring : m + 2 = m + 2) =
      φ.comp N.xR (by ring : 2 + m = m + 2) :=
    (shWhisker_exchange f (S.fDot r) (by ring) (by ring)).symm
  have key : ((S.rQ : k) • NH2.one (W := S.F (r + 1) ≫ S.F r)).comp φ
      (add_zero m) = 0 := by
    rw [NH2.one, ← ShiftedHom.mk₀_smul]
    change (ShiftedHom.mk₀ (0 : ℤ) rfl ((N.r : k) • 𝟙 _)).comp φ (add_zero m) = 0
    rw [N.slide₁, ShiftedHom.sub_comp',
      ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0)
        (by ring : m + -2 = m - 2) (by ring), hτφ, ShiftedHom.comp_zero,
      ShiftedHom.comp_assoc _ _ _ (by norm_num : (2 : ℤ) + -2 = 0)
        (by ring : m + 2 = m + 2) (by ring), hcomm,
      ← ShiftedHom.comp_assoc _ _ _ (by ring : m + -2 = m - 2)
        (by ring : (2 : ℤ) + m = m + 2) (by ring),
      hτφ, ShiftedHom.zero_comp, sub_self]
  rw [ShiftedHom.smul_comp', NH2.one, ShiftedHom.mk₀_id_comp] at key
  have := congrArg (fun ψ => ((S.rQ⁻¹ : kˣ) : k) • ψ) key
  simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using this

/-- Unshifted form of negative-step Lemma A. -/
theorem lemANeg' {r : ℤ} (hn : S.wt (r + 1) ≤ 0)
    (hyp : ∀ r', r' < r → S.AdjHyp r') {m : ℤ} (hm : m < 0)
    (f : S.F (r + 1) ⟶ (S.F (r + 1))⟦m⟧) : f ▷ S.F r = 0 :=
  (shWhiskerRight_eq_zero_iff (f : ShiftedHom _ _ m) _).1 (S.lemANeg hn hyp hm f)

/-- Summands of `F (r + 1)` related by a strictly negative shift become
zero after composition with `F r`. This is not lower-Hom vanishing for
each summand before whiskering. -/
theorem isZero_comp_F_of_retract_shift_neg_step {r : ℤ} (hn : S.wt (r + 1) ≤ 0)
    (hyp : ∀ r', r' < r → S.AdjHyp r')
    {Z₁ Z₂ : S.obj (r + 1 + 1) ⟶ S.obj (r + 1)}
    (i₁ : Z₁ ⟶ S.F (r + 1)) (p₁ : S.F (r + 1) ⟶ Z₁) (h₁ : i₁ ≫ p₁ = 𝟙 Z₁)
    (i₂ : Z₂ ⟶ S.F (r + 1)) (p₂ : S.F (r + 1) ⟶ Z₂) (h₂ : i₂ ≫ p₂ = 𝟙 Z₂)
    {j : ℤ} (hj : j < 0) (e : Z₁ ≅ Z₂⟦j⟧) : IsZero (Z₁ ≫ S.F r) := by
  have hf := S.lemANeg' hn hyp hj (p₁ ≫ e.hom ≫ i₂⟦j⟧')
  have hid : (i₁ ≫ (p₁ ≫ e.hom ≫ i₂⟦j⟧') ≫ p₂⟦j⟧' ≫ e.inv) = 𝟙 Z₁ := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, h₂, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id, h₁]
  rw [IsZero.iff_id_eq_zero, ← Bicategory.id_whiskerRight, ← hid, comp_whiskerRight,
    comp_whiskerRight, hf, zero_comp, comp_zero]

end Categorification.TwoRep.StrongSl2
