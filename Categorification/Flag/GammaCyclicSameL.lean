/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaCyclicSame

/-!
# Cyclicity of the crossing of equal colours: the left rotation

KL III, arXiv:0807.3250v1, Definition 3.1 (`eq_cyclic_cross-gen` for `i = j`; relation
`Categorification.KL3.Diagram.Rel.cycCrossL`) and Proposition 6.3.

The left rotation of the upward crossing of two strands of colour `i` (`rotCrossLW`) is `Γ_N` of
the downward crossing (`rotCrossLW_same_eq`). The proof mirrors the right rotation
(`Categorification.Flag.rotCrossRW_same_eq`): dot slides of the rotation of an arbitrary map
(`rotGenL_fwdL`, `rotGenL_fwdR`, `rotGenL_bwdL`, `rotGenL_bwdR`), the rotation of the identity
(`rotTauL_eq`), and the vanishing of the rotated crossing at `1` (`rotCrossLW_same_one`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

/-! ### Left rotations of an arbitrary two-strand map -/

section RotGenL

variable (i j : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, j) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, j) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

variable (K) in
/-- The left rotation of an arbitrary map `φ : E_j E_i → E_i E_j` (the five layers of
`rotCrossLW`, with `φ` in the middle). -/
def rotGenL (φ : BHom ((stepB K (true, j) w r₂ hFj').tensor (stepB K (true, i) t w hFi')) ((stepB K (true, i) r₁ r₂ hFi).tensor (stepB K (true, j) t r₁ hFj))) : BHom ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y)) :=
  (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y))).comp ((BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))).comp ((BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (locTwo φ ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))).comp ((BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))).comp (cupFEW K i (hFi' : StepR (true, i) t w) hFi' ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))))

theorem rotCrossLW_eq_rotGenL : rotCrossLW K i j hFj hFi hFi' hFj' Y =
    rotGenL K i j hFj hFi hFi' hFj' Y (crossU K j i (hFj' : StepR (true, j) w r₂)
      (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, j) t r₁)) := rfl

variable (φ : BHom ((stepB K (true, j) w r₂ hFj').tensor (stepB K (true, i) t w hFi')) ((stepB K (true, i) r₁ r₂ hFi).tensor (stepB K (true, j) t r₁ hFj)))

/-- A dot on the left input strand of `φ` (from the inner cup) becomes the dot of `F_j`. -/
theorem rotGenL_fwdL (x) :
    BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y)) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (locTwo φ ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, j) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K j w hFj'.2) 1)) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) x))) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1 (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y)) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (locTwo φ ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) x))) := by
  rw [whiskerLeft_mul_image _ _ _ (BRing.tmul (stepB K (false, j) r₂ w hFj') _ (eXi K j w hFj'.2) 1) (fun y =>
      (cupFEW_slide j (hFj' : StepR (true, j) w r₂) hFj' _ y).symm)]
  rw [whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _)]

/-- A dot on the right input strand of `φ` (from the outer cup) becomes the dot of `F_i`. -/
theorem rotGenL_fwdR (z) :
    BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y)) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (locTwo φ ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2) 1) * cupFEW K i (hFi' : StepR (true, i) t w) hFi' ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) z)))) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) (eXi K i t hFi'.2) 1 * rotGenL K i j hFj hFi hFi' hFj' Y φ z := by
  rw [← cupFEW_slide i (hFi' : StepR (true, i) t w) hFi']
  simp only [rotGenL, BHom.comp_apply]
  rw [whiskerLeft_mul_left, whiskerLeft_mul_left, whiskerLeft_mul_left, whiskerLeft_mul_left]

/-- A dot on the left source strand `F_j` slides across the inner cap to the right output strand
of `φ`. -/
theorem rotGenL_bwdL (z) :
    rotGenL K i j hFj hFi hFi' hFj' Y φ (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K j t hFj.2) 1 * z) =
      BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y)) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, j) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) _ 1 (BRing.tmul (stepB K (true, j) t r₁ hFj) ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K j t hFj.2) 1))) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (locTwo φ ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (cupFEW K i (hFi' : StepR (true, i) t w) hFi' ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) z)))) := by
  simp only [rotGenL, BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (cupFEW_mul j _ _ _ _),
    whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _)),
    whiskerLeft_mul_congr _ _ _ _ (whiskerLeft_mul_congr _ _ _ _ (whiskerLeft_mul_congr _ _ _ _
      (capEFW_slide j (hFj : StepR (true, j) t r₁) hFj _ _)))]

/-- A dot on the right source strand `F_i` slides across the outer cap to the left output strand
of `φ`. -/
theorem rotGenL_bwdR (z) :
    rotGenL K i j hFj hFi hFi' hFj' Y φ (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1
        (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y)) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, j) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i r₁ hFi.2) 1)) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (locTwo φ ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (cupFEW K i (hFi' : StepR (true, i) t w) hFi' ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) z)))) := by
  simp only [rotGenL, BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (cupFEW_mul j _ _ _ _),
    whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _)),
    whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _
      (capEFW_mul j _ _ _ _))),
    whiskerLeft_mul_congr _ _ _ _ (whiskerLeft_mul_congr _ _ _ _
      (capEFW_slide i (hFi : StepR (true, i) r₁ r₂) hFi _ _)),
    ← whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _
      (fun z => whiskerLeft_mul_left _ _ z _))]

end RotGenL

/-! ### Equal colours -/

section LSame

variable (i : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, i) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, i) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

theorem lPsi_L (v) :
    BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i w hFj'.2) 1)) * v) = BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (v) + BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) _ 1 (BRing.tmul (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFj.2) 1))) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (v) := by
  refine whiskerLeft_mul_add _ _ _ _ _ (fun u => whiskerLeft_mul_add _ _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locL
      ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) u'
  rw [BHom.comp_apply, BHom.add_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem lPsi_R (v) :
    BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') _ 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2) 1))) * v) = -BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (v) + BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i r₁ hFi.2) 1)) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (v) := by
  have hneg : ∀ u, BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (-(tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) u =
      -BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (u) := by
    intro u; rw [locTwo_neg, BHom.whiskerLeft_neg, BHom.whiskerLeft_neg]; rfl
  rw [← hneg]
  refine whiskerLeft_mul_add _ _ _ _ _ (fun u => whiskerLeft_mul_add _ _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locR
      ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) u'
  rw [BHom.comp_apply, BHom.sub_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  rw [this, locTwo_neg, BHom.neg_apply, sub_eq_add_neg]
  exact add_comm _ _

theorem lTau_L (v) : BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i w hFj'.2) 1)) * v) = BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i r₁ hFi.2) 1)) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (v) := by
  refine whiskerLeft_mul_right _ _ _ _ (fun u => whiskerLeft_mul_right _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locτL
      ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) u'
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem lTau_R (v) : BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') _ 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2) 1))) * v) = BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) _ 1 (BRing.tmul (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFj.2) 1))) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, i) r₂ w hFj') (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (v) := by
  refine whiskerLeft_mul_right _ _ _ _ (fun u => whiskerLeft_mul_right _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locτR
      ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) u'
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem lL2_mul (x) : BRing.tmul (stepB K (false, i) w t hFi') _ 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') _ 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2) 1))) * BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K i (hFj' : StepR (true, i) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) x = BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K i (hFj' : StepR (true, i) w r₂) hFj' ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) (BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2) 1) * x) :=
  (whiskerLeft_mul_right _ _ _ _ (cupFEW_mul i _ _ _ _) x).symm

theorem rotTauL_dotL (z) :
    rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K i t hFj.2) 1 * z) = BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) (eXi K i t hFi'.2) 1 * rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGenL_bwdL, ← lTau_R, lL2_mul, rotGenL_fwdR]

theorem rotTauL_dotR (z) :
    rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') Y (eXi K i w hFj'.2) 1) * rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGenL_bwdR, ← lTau_L, rotGenL_fwdL]
  rfl

theorem rotPsiL_dotL (z) :
    rotGenL K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K i t hFj.2) 1 * z) = BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ w hFj') Y (eXi K i w hFj'.2) 1) * rotGenL K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z - rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGenL_bwdL, eq_sub_of_add_eq' (lPsi_L i hFj hFi hFi' hFj' Y _).symm, BHom.map_sub,
    BHom.map_sub, rotGenL_fwdL]
  rfl

theorem rotPsiL_dotR (z) :
    rotGenL K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) (eXi K i t hFi'.2) 1 * rotGenL K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z + rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGenL_bwdR, eq_sub_of_add_eq' (lPsi_R i hFj hFi hFi' hFj' Y _).symm, sub_neg_eq_add,
    BHom.map_add, BHom.map_add, lL2_mul, rotGenL_fwdR]
  rfl

end LSame

section LValues

variable (i : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, i) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, i) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

theorem capEFP_left_mul {s s' : Comp m} (hE : StepR (true, i) s s') (a : H K s')
    (mm : (stepB K (true, i) s s' hE).T) :
    capEFP K i hE (hE : StepR (false, i) s' s) (BRing.tmul (stepB K (true, i) s s' hE)
      (stepB K (false, i) s' s hE) ((stepB K (true, i) s s' hE).left a * mm) 1) =
      a * capEFP K i hE (hE : StepR (false, i) s' s) (BRing.tmul _ _ mm 1) := by
  rw [← capEFP_left, BRing.tensor_left, BRing.tmul_mul_tmul, mul_one]

/-- Below the top degree, the cap `E F → 1` kills `x̄_k ξ^e ⊗ 1` (with `x̄` acting on the
right of `E`). -/
theorem capEFP_right_xbar_vanish {s s' : Comp m} (hE : StepR (true, i) s s') (k e : ℕ)
    (h : e + k < s i.castSucc) :
    capEFP K i hE (hE : StepR (false, i) s' s) (BRing.tmul (stepB K (true, i) s s' hE)
      (stepB K (false, i) s' s hE) ((stepB K (true, i) s s' hE).right (xbar K s i.castSucc k) *
        xiStep K (true, i) s s' hE ^ e) 1) = 0 := by
  have hxi : xiStep K (true, i) s s' hE = eXi K i s hE.2 := rfl
  rcases k with _ | k
  · rw [xbar_zero', map_one, one_mul, hxi, capEFP_xi_pow_one, if_neg (by omega)]
  · rw [Eright_xbar_succ, add_mul, BRing.add_tmul, capEFP_add, mul_comm (xiStep K (true, i) s s' hE),
      mul_assoc, capEFP_left_mul, capEFP_left_mul, ← pow_succ', hxi, capEFP_xi_pow_one, capEFP_xi_pow_one,
      if_neg (by omega), if_neg (by omega), mul_zero, mul_zero, add_zero]

/-- **The two caps of the left rotation vanish below the top degree.** -/
theorem lCap_vanish (e₁ e₂ : ℕ) (he : e₁ + e₂ < t i.castSucc + r₁ i.castSucc) (y : Y.T) :
    capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K i (hFj : StepR (true, i) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i r₁ hFi.2 ^ e₁) (BRing.tmul (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFj.2 ^ e₂) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y 1 y))))) = 0 := by
  rw [BHom.whiskerLeft_tmul, capEFW_tmul, capEFP_xi_pow_one, ← BRing.tmul_balance]
  split_ifs with h1
  · have hsign : ∀ k : ℕ, (stepB K (true, i) r₁ r₂ hFi).right ((-1) ^ k) =
        (stepB K (true, i) r₁ r₂ hFi).left ((-1) ^ k) := fun k => by
      rw [map_pow, map_neg, map_one, map_pow, map_neg, map_one]
    have hxi : xiStep K (true, i) r₁ r₂ hFi = eXi K i r₁ hFi.2 := rfl
    rw [capEFW_tmul, map_mul, mul_assoc, hsign, capEFP_left_mul, ← hxi,
      capEFP_right_xbar_vanish i hFi _ _ (by omega), mul_zero, map_zero, zero_mul]
  · rw [map_zero, zero_mul, BRing.zero_tmul, BHom.map_zero]

/-- The two caps on `ξ^{e₁} ⊗ ξ^{e₂}` up to the top degree: `1` exactly in the top degree. -/
theorem lCap_top (e₁ e₂ : ℕ) (h₁ : e₁ ≤ r₁ i.castSucc) (h₂ : e₂ ≤ t i.castSucc) (y : Y.T) :
    capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K i (hFj : StepR (true, i) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i r₁ hFi.2 ^ e₁) (BRing.tmul (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFj.2 ^ e₂) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y 1 y))))) = if e₁ = r₁ i.castSucc ∧ e₂ = t i.castSucc then y else 0 := by
  rw [BHom.whiskerLeft_tmul, capEFW_tmul, capEFP_xi_pow_one, ← BRing.tmul_balance]
  by_cases he₂ : e₂ = t i.castSucc
  · rw [if_pos (by omega), show e₂ + 1 - (t i.castSucc + 1) = 0 by omega, pow_zero, xbar_zero',
      mul_one, map_one, one_mul, capEFW_tmul, capEFP_xi_pow_one]
    by_cases he₁ : e₁ = r₁ i.castSucc
    · rw [if_pos (by omega), show e₁ + 1 - (r₁ i.castSucc + 1) = 0 by omega, pow_zero, xbar_zero',
        mul_one, map_one, one_mul, if_pos ⟨he₁, he₂⟩]
    · rw [if_neg (by omega), if_neg (fun h => he₁ h.1), map_zero, zero_mul]
  · rw [if_neg (by omega), if_neg (fun h => he₂ h.2), map_zero, zero_mul, BRing.zero_tmul,
      BHom.map_zero]

variable (K) in
/-- The two caps after the crossing, as an additive map of the crossing's output. -/
def rotQL (W : ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)).T) :
    BRing.TT (stepB K (true, i) r₁ r₂ hFi) (stepB K (true, i) t r₁ hFj) →+ Y.T :=
  AddMonoidHom.mk' (fun u => capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K i (hFj : StepR (true, i) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) ((BRing.assoc (stepB K (true, i) r₁ r₂ hFi) (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))).hom (BRing.tmul _ _ u W))))
    (fun u v => by
      simp only
      rw [BRing.add_tmul, BHom.map_add, BHom.map_add, BHom.map_add])

theorem rotQL_apply (W : ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)).T) (u) :
    capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K i (hFj : StepR (true, i) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) ((BRing.assoc (stepB K (true, i) r₁ r₂ hFi) (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))).hom (BRing.tmul _ _ u W))) =
      rotQL K i hFj hFi Y W u := rfl

/-- The two caps after the crossing vanish on `ξ^h ⊗ ξ^g` below the top degree. -/
theorem rotPsiL_vanish (g h : ℕ) (hgh : g + h < t i.castSucc + r₁ i.castSucc + 1) (y : Y.T) :
    capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K i (hFj : StepR (true, i) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i w hFj'.2 ^ h) (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2 ^ g) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y 1 y)))))) = 0 := by
  rw [locTwo_tmul, rotQL_apply, crossU_same_tmul_pow, map_sub, map_sum, map_sum,
    Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
  all_goals
    intro f hf
    have := Finset.mem_range.1 hf
    rw [← rotQL_apply, BRing.assoc_hom_tmul]
    exact lCap_vanish i hFj hFi Y (h + g - 1 - f) f (by omega) y

/-- The identity followed by the two caps, on `ξ^h ⊗ ξ^g` up to the top degree. -/
theorem rotTauL_top (g h : ℕ) (hg : g ≤ t i.castSucc) (hh : h ≤ r₁ i.castSucc) (y : Y.T) :
    capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi) (capEFW K i (hFj : StepR (true, i) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))) (eXi K i w hFj'.2 ^ h) (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2 ^ g) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y 1 y)))))) =
      if h = r₁ i.castSucc ∧ g = t i.castSucc then y else 0 := by
  rw [locTwo_tmul, tauU_same_tmul_pow, BRing.assoc_hom_tmul, lCap_top i hFj hFi Y h g hh hg]

/-- **The left rotation of the crossing of equal colours vanishes at `1`.** -/
theorem rotCrossLW_same_one (y : Y.T) :
    rotCrossLW K i i hFj hFi hFi' hFj' Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) = 0 := by
  have hw : w i.castSucc = r₁ i.castSucc := by rw [← hFi'.1, ← hFj.1]
  have hd1 := dFE_eq i (hFi' : StepR (true, i) t w)
  have hd2 := dFE_eq i (hFj' : StepR (true, i) w r₂)
  simp only [rotCrossLW, BHom.comp_apply]
  rw [cupFEW_apply']
  repeat rw [BHom.map_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [BHom.whiskerLeft_tmul, cupFEW_apply', BRing.tmul_sum]
  repeat rw [BHom.map_sum]
  refine Finset.sum_eq_zero fun h hh => ?_
  have hh' := Finset.mem_range.1 hh
  simp only [BHom.whiskerLeft_tmul]
  rw [rotPsiL_vanish i hFj hFi hFi' hFj' Y g h (by omega) y, BRing.tmul_zero, BRing.tmul_zero]

/-- **The rotation of the identity is the identity at `1`.** -/
theorem rotTauL_one (y : Y.T) :
    rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) =
      BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  have hw : w i.castSucc = r₁ i.castSucc := by rw [← hFi'.1, ← hFj.1]
  have hd1 := dFE_eq i (hFi' : StepR (true, i) t w)
  have hd2 := dFE_eq i (hFj' : StepR (true, i) w r₂)
  simp only [rotGenL, BHom.comp_apply]
  rw [cupFEW_apply']
  repeat rw [BHom.map_sum]
  rw [Finset.sum_eq_single (dFE i (hFi' : StepR (true, i) t w))]
  · rw [BHom.whiskerLeft_tmul, cupFEW_apply', BRing.tmul_sum]
    repeat rw [BHom.map_sum]
    rw [Finset.sum_eq_single (dFE i (hFj' : StepR (true, i) w r₂))]
    · simp only [BHom.whiskerLeft_tmul]
      rw [rotTauL_top i hFj hFi hFi' hFj' Y _ _ (by omega) (by omega), if_pos ⟨by omega, by omega⟩]
      simp only [Nat.sub_self, pow_zero, one_mul, xsFE_eq, x_zero, map_one]
    · intro h hh hhd
      have hh' := Finset.mem_range.1 hh
      simp only [BHom.whiskerLeft_tmul]
      rw [rotTauL_top i hFj hFi hFi' hFj' Y _ _ (by omega) (by omega), if_neg (by omega),
        BRing.tmul_zero, BRing.tmul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h
  · intro g hg hgd
    have hg' := Finset.mem_range.1 hg
    rw [BHom.whiskerLeft_tmul, cupFEW_apply', BRing.tmul_sum]
    repeat rw [BHom.map_sum]
    refine Finset.sum_eq_zero fun h hh => ?_
    have hh' := Finset.mem_range.1 hh
    simp only [BHom.whiskerLeft_tmul]
    rw [rotTauL_top i hFj hFi hFi' hFj' Y _ _ (by omega) (by omega), if_neg (by omega),
      BRing.tmul_zero, BRing.tmul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

/-- **The left rotation of the identity** is `Γ_N` of the identity of `F_i F_i`. -/
theorem rotTauL_eq : rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) = locTwo (tauDn K i i hFj hFi hFi' hFj') Y := by
  refine BHom.ext fun z => ?_
  refine ext_two (Y := Y) (eXi K i t hFj.2) (eXi K i r₁ hFi.2) (stepF_spanned i hFj)
    (stepF_spanned i hFi) (rotGenL K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))).toAddHom (locTwo (tauDn K i i hFj hFi hFi' hFj') Y).toAddHom
    (BRing.tmul _ _ (eXi K i t hFi'.2) 1) (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K i w hFj'.2) 1))
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun y => ?_) z
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotTauL_dotL]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, locTauDn_dotL]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotTauL_dotR]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, locTauDn_dotR]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotTauL_one, locTwo_tmul, ← BRing.one_eq,
      tauDn_one, if_pos rfl, BRing.one_eq (M := stepB K (false, i) w t hFi')
        (N := stepB K (false, i) r₂ w hFj'), BRing.assoc_hom_tmul]

/-- **Cyclicity of the crossing of equal colours, left rotation** (KL III `eq_cyclic_cross-gen`
for `i = j`, relation `cycCrossL`; Proposition 6.3): the left rotation of the upward crossing
`E_i E_i → E_i E_i` is `Γ_N` of the downward crossing (6.9) on `F_i F_i Y`. -/
theorem rotCrossLW_same_eq : rotCrossLW K i i hFj hFi hFi' hFj' Y = locTwo (crossDn K i i hFj hFi hFi' hFj') Y := by
  refine BHom.ext fun z => sub_eq_zero.1 ?_
  have key := ext_two (Y := Y) (eXi K i t hFj.2) (eXi K i r₁ hFi.2) (stepF_spanned i hFj)
    (stepF_spanned i hFi) ((rotCrossLW K i i hFj hFi hFi' hFj' Y).toAddHom - (locTwo (crossDn K i i hFj hFi hFi' hFj') Y).toAddHom) 0
    (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K i w hFj'.2) 1)) (BRing.tmul _ _ (eXi K i t hFi'.2) 1)
    (fun z => ?_) (fun z => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, mul_zero])
    (fun z => ?_) (fun z => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, mul_zero])
    (fun y => ?_) z
  · rw [AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply] at key
    rw [key, AddMonoidHom.zero_apply]
  · rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply,
      BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossLW_eq_rotGenL, rotPsiL_dotL,
      locCrossDn_dotL, rotTauL_eq, mul_sub]
    abel
  · rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply,
      BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossLW_eq_rotGenL, rotPsiL_dotR,
      locCrossDn_dotR, rotTauL_eq, mul_sub]
    abel
  · rw [AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply, AddMonoidHom.zero_apply,
      rotCrossLW_same_one, locTwo_tmul, ← BRing.one_eq, crossDn_one, if_pos rfl, BRing.zero_tmul,
      BHom.map_zero, sub_zero]

end LValues

end Categorification.Flag

end
