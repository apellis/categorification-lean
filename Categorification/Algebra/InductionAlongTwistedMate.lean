/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongSigma

/-!
# The mate of an action between two towers of restrictions

Let `φ₁ : A₀ → A₁`, `φ₂ : A₁ → A₂` and `ψ₁ : A₀ → B₁`, `ψ₂ : B₁ → A₂` be two towers of nonunital
ring maps with the same ends. A natural transformation `τ : Res_{ψ₁} Res_{ψ₂} ⟶ Res_{φ₁} Res_{φ₂}`
that acts by left multiplication by an element `c ∈ A₂` has as mate through the composite
adjunctions `Ind ⊣ Res` the transformation `Ind_{φ₂} Ind_{φ₁} ⟶ Ind_{ψ₂} Ind_{ψ₁}` sending
`1 ⊗ (1 ⊗ n)` to `c · (1 ⊗ (1 ⊗ n))` (`InductionAlong.conjugateEquiv_symm_twisted_unitGen`).
This is the shape of the crossing of two strands of different colours on Webster's induction
functors (arXiv:1309.3796v3, §4.6), whose restriction counterpart runs between the two orders
of appending the strands; it is used for the compatibility of the cap functor with that crossing
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite

universe u

variable {A₀ A₁ B₁ A₂ : Type u} [Ring A₀] [Ring A₁] [Ring B₁] [Ring A₂]
  (φ₁ : A₀ →ₙ+* A₁) (φ₂ : A₁ →ₙ+* A₂) (ψ₁ : A₀ →ₙ+* B₁) (ψ₂ : B₁ →ₙ+* A₂) (c : A₂)
  (τ : resFunctor.{u, u} ψ₂ ⋙ resFunctor.{u, u} ψ₁ ⟶ resFunctor φ₂ ⋙ resFunctor φ₁)
  (hτ : ∀ (M : ModuleCat.{u} A₂) (r : Res ψ₁ (Res ψ₂ M)),
    ((τ.app M).hom r).val.val = c • r.val.val)

include hτ in
/-- The mate of an action by `c` between two towers of restrictions, on the generator
`1 ⊗ (1 ⊗ n)`: it multiplies by `c`. -/
theorem conjugateEquiv_symm_twisted_unitGen (N : ModuleCat.{u} A₀) (n : N) :
    (((conjugateEquiv ((adjunction.{u, u} ψ₁).comp (adjunction.{u, u} ψ₂))
        ((adjunction φ₁).comp (adjunction φ₂))).symm τ).app N).hom
        (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n)) =
      c • Ind.tmul (unitGen ψ₂) (Ind.tmul (unitGen ψ₁) n) := by
  have key := congrArg (fun f => (f.hom n).val.val)
    (unit_conjugateEquiv_symm ((adjunction.{u, u} ψ₁).comp (adjunction.{u, u} ψ₂))
      ((adjunction φ₁).comp (adjunction φ₂)) τ N)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key.symm.trans (hτ _ _)

end Categorification.InductionAlong
