/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongBaseChange

/-!
# Base change of induction along a surjection is surjective

The comparison `z ⊗ n ↦ πB(z) ⊗ n` of `InductionAlong.baseChange` is surjective, hence an
epimorphism of modules, when `πB` is surjective (`baseChange_app_surjective`,
`baseChange_app_epi`).
-/

namespace Categorification

open CategoryTheory MulOpposite

namespace InductionAlong

universe u w

variable {A A' B B' : Type u} [Ring A] [Ring A'] [Ring B] [Ring B']
  (πA : A →+* A') (πB : B →+* B')
  {φ : A →ₙ+* B} {φ' : A' →ₙ+* B'} (hφ : ∀ x, πB (φ x) = φ' (πA x))

include hφ in
/-- **Base change along a surjection is surjective.** -/
theorem baseChange_app_surjective (hπB : Function.Surjective πB) (N : ModuleCat.{max u w} A') :
    Function.Surjective ((baseChange.{u, w} πA πB hφ).app N) := by
  intro y
  change ∃ x, baseMap πA πB hφ N x = y
  induction y using Ind.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul z' n =>
    obtain ⟨c, hc⟩ := hπB z'.1
    refine ⟨Ind.tmul ⟨c * φ 1, mul_mem_corner φ c 1⟩ n, ?_⟩
    rw [baseMap_tmul]
    congr 1
    refine Subtype.ext ?_
    change πB (c * φ 1) = z'.1
    rw [map_mul, hφ, map_one, hc]
    exact z'.2
  | add s t hs ht =>
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨x', rfl⟩ := ht
    exact ⟨x + x', map_add _ _ _⟩

include hφ in
/-- **Base change along a surjection is an epimorphism.** -/
theorem baseChange_app_epi (hπB : Function.Surjective πB) (N : ModuleCat.{max u w} A') :
    Epi ((baseChange.{u, w} πA πB hφ).app N) :=
  (ModuleCat.epi_iff_surjective _).2 (baseChange_app_surjective πA πB hφ hπB N)

end InductionAlong

end Categorification
