/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongSigma

/-!
# The mate of a left multiplication on restriction

Let `φ : A → B` be a nonunital ring map and `c ∈ B` commute with the image of `φ`. Left
multiplication by `c` on `Res_φ` (`resAct`) is a natural endomorphism of restriction; its mate
through `Ind_φ ⊣ Res_φ` is right multiplication `z ⊗ n ↦ z c ⊗ n` on induction
(`InductionAlong.conjugateEquiv_symm_resAct_app`, with the map `natMap`). This describes the dot on
Webster's induction functors on modules over `T^λ` (arXiv:1309.3796v3, §4.6), the mate of the
dot on restriction, as in Rouquier's definition (Brundan, arXiv:1501.00350v1, Definition 1.1).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite

universe u

variable {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B} {c : B}
  (hc : ∀ a, c * φ a = φ a * c)

include hc in
/-- An element commuting with the image of `φ` intertwines `φ` with itself. -/
theorem intertwines_of_commute : Intertwines φ φ c := fun a => (hc a).symm

variable (τ : resFunctor.{u, u} φ ⟶ resFunctor φ)
  (hτ : ∀ M, τ.app M = ModuleCat.ofHom (resAct c hc M))

include hτ in
/-- **The mate of left multiplication by `c` on restriction is right multiplication by `c` on
induction**: `z ⊗ n ↦ z c ⊗ n`. -/
theorem conjugateEquiv_symm_resAct_app (N : ModuleCat.{u} A) :
    ((conjugateEquiv (adjunction.{u, u} φ) (adjunction φ)).symm τ).app N =
      ModuleCat.ofHom (natMap (N := N) (intertwines_of_commute hc)) := by
  set τ' := (conjugateEquiv (adjunction.{u, u} φ) (adjunction φ)).symm τ
  ext x
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul z n =>
    have key := fun n : N => congrArg (fun f => (f.hom n).val)
      (unit_conjugateEquiv_symm (adjunction.{u, u} φ) (adjunction φ) τ N)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hτ] at key
    change ∀ n : N, Ind.tmul (φ := φ) (c • unitGen φ) n = τ'.app N (Ind.tmul (unitGen φ) n) at key
    have hz : Ind.tmul (φ := φ) z n = z.1 • Ind.tmul (unitGen φ) n := by
      rw [Ind.smul_tmul]
      exact congrArg (Ind.tmul · n) (Subtype.ext z.2.symm)
    rw [hz, (τ'.app N).hom.map_smul, ← key, Ind.smul_tmul]
    erw [natMap_tmul]
    congr 1
    apply Subtype.ext
    change z.1 * (c * φ 1) = z.1 * φ 1 * c
    rw [hc 1, ← mul_assoc]

end Categorification.InductionAlong
