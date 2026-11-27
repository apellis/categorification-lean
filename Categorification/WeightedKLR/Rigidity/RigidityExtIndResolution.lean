/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongExact
import Categorification.WeightedKLR.RedStrands.ExactMulRightTransport
import Categorification.WeightedKLR.Induction.K0
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Induction along a map with projective corner maps projective resolutions

Let `φ : A →ₙ+* B` be a nonunital ring map whose corner `B φ(1)` is projective as a right
`A`-module. Induction `Ind − φ` of left modules is additive (`Ind.map_add`), exact and sends projective
modules to projective modules, so it sends a projective resolution of `N` to a projective
resolution of `Ind N φ`.

This is the step of Webster's proof of Proposition 7.6 (arXiv:1309.3796v3, §7.1) that applies
the functor `𝔉_i` of adding a black strand at the right (whose corner is projective by
Theorem 4.31) to a resolution of a standard module.

## Main results

* `InductionAlong.functor_preservesProjectiveObjects`.
* `InductionAlong.functor_preservesHomology`: under a projective corner.
* `InductionAlong.indResolution`: the induced projective resolution.
-/

namespace Categorification

open CategoryTheory

noncomputable section

namespace InductionAlong

universe u

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B)

instance functor_additive : (functor.{u, u} φ).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (Ind.map_add f.hom g.hom)

/-- Induction sends projective modules to projective modules. -/
instance functor_preservesProjectiveObjects : (functor.{u, u} φ).PreservesProjectiveObjects where
  projective_obj {N} hN := by
    have : Module.Projective A N := (IsProjective.iff_projective N).2 hN
    have := Ind.projective φ N
    exact (IsProjective.iff_projective (Ind N φ)).1 this

/-- Induction along a map with projective corner preserves homology. -/
theorem functor_preservesHomology [Module.Projective Aᵐᵒᵖ (Corner φ)] :
    (functor.{u, u} φ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS => by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Ind.map_exact hS

/-- **Induced projective resolution.** Induction along a map with projective corner sends a
projective resolution of `N` to a projective resolution of `Ind N φ`. -/
def indResolution [Module.Projective Aᵐᵒᵖ (Corner φ)] {N : ModuleCat.{u} A}
    (P : ProjectiveResolution N) : ProjectiveResolution ((functor.{u, u} φ).obj N) :=
  have := functor_preservesHomology φ
  (functor.{u, u} φ).mapProjectiveResolution P

@[simp] theorem indResolution_X [Module.Projective Aᵐᵒᵖ (Corner φ)] {N : ModuleCat.{u} A}
    (P : ProjectiveResolution N) (n : ℕ) :
    (indResolution φ P).complex.X n = (functor.{u, u} φ).obj (P.complex.X n) := rfl

/-- `indResolution`, with its target written as the module `Ind N φ`. -/
def indResolutionOf [Module.Projective Aᵐᵒᵖ (Corner φ)] {N : ModuleCat.{u} A}
    (P : ProjectiveResolution N) : ProjectiveResolution (ModuleCat.of B (Ind N φ)) :=
  indResolution φ P

theorem indResolutionOf_X [Module.Projective Aᵐᵒᵖ (Corner φ)] {N : ModuleCat.{u} A}
    (P : ProjectiveResolution N) (n : ℕ) :
    (indResolutionOf φ P).complex.X n = ModuleCat.of B (Ind (P.complex.X n) φ) := rfl

/-- Induction commutes with finite products: `Ind (∏ P a) ≅ ∏ Ind (P a)`. -/
def indPiIso {ι : Type} [Fintype ι] (P : ι → ModuleCat.{u} A) :
    (functor.{u, u} φ).obj (ModuleCat.of A (∀ a, P a)) ≅
      ModuleCat.of B (∀ a, (functor.{u, u} φ).obj (P a)) :=
  (functor.{u, u} φ).mapIso (ModuleCat.biproductIsoPi P).symm ≪≫
    (functor.{u, u} φ).mapBiproduct P ≪≫ ModuleCat.biproductIsoPi _

end InductionAlong

end

end Categorification
