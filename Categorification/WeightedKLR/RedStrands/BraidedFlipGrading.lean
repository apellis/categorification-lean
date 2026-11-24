/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedBimoduleFlip
import Categorification.WeightedKLR.RedStrands.BraidedStandardGrading
import Categorification.KLR.GradingFlip

/-!
# Horizontal reflection preserves the auxiliary diagram grading

For Webster, arXiv:1309.3796v2, Lemma 6.11, use the degree-preserving
horizontal reflection to compare the two standard inputs of the coend.
The affine grading comparison descends through both diagram quotients.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR MulOpposite

variable {I k : Type} [DecidableEq I] [Field k] {l : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin l → I →₀ ℕ} {ν : Multiset I}
  (G : GradingDatum (stendhalQ Q Λ))
  (hG : ∀ i j, G.degΨ i j = G.degΨ j i)

include hG in
/-- Horizontal reflection preserves the auxiliary grading of the violated braid algebra. -/
theorem violFlip_mem_violAuxiliaryGrade {n : ℤ} {a : ViolQuotient k Q Λ ν}
    (ha : a ∈ violAuxiliaryGrade G n) : violFlip a ∈ violAuxiliaryGrade G n := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  change violFlip (violMk k Q Λ ν (ofKLR k Q Λ ν x)) ∈ violAuxiliaryGrade G n
  rw [violFlip_violMk, flip_ofKLR]
  exact Submodule.mem_map.mpr ⟨ofKLR k Q Λ ν (KLRAlgebra.hflip x),
    Submodule.mem_map.mpr ⟨KLRAlgebra.hflip x, G.hflip_mem_grade hG hx, rfl⟩, rfl⟩

include hG in
theorem cornerFlipEquiv_mem_violAuxiliaryGrade_iff (κ : List (Fin l)) (n : ℤ)
    (a : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ) :
    (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ a).val ∈ violAuxiliaryGrade G n ↔
      a.unop.val ∈ violAuxiliaryGrade G n := by
  change violFlip a.unop.val ∈ violAuxiliaryGrade G n ↔ _
  constructor
  · intro h
    have hh := violFlip_mem_violAuxiliaryGrade G hG h
    rw [violFlip_violFlip] at hh
    exact hh
  · exact violFlip_mem_violAuxiliaryGrade G hG

end Categorification.Stendhal.BraidedStendhalAlgebra
