/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.BalancedInduction
import Categorification.Algebra.BalancedTensorRightExact

/-!
# Induction along a graded bimodule on short exact sequences

Tensoring with a finite-dimensional graded bimodule `M` is right exact, so it carries a short
exact sequence `0 → K → P → N → 0` to a short exact sequence exactly when `M ⊗_A K → M ⊗_A P` is
injective (`GFin.ShortExact.induce`). This is how the braiding functors of B. Webster, *Knot
invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, Definition 6.6, act on
short exact sequences with vanishing `Tor` (proof of Corollary 6.10).
-/

noncomputable section

namespace Categorification.Graded

open DirectSum MulOpposite BalancedTensor

universe u

variable {k : Type*} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {ℬ : ℤ → Submodule k B}
  {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule k M} [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
  [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ] [Module.Finite k M]

/-- **Induction on a short exact sequence**: if `M ⊗_A K → M ⊗_A P` is injective, tensoring with
`M` carries the short exact sequence `K → P → N` to a short exact sequence. -/
def GFin.ShortExact.induce {K P N : GFin 𝒜} (S : GFin.ShortExact K P N)
    (h : Function.Injective (mapRight (k := k) (B := B) (M := M) S.f)) :
    GFin.ShortExact (GFin.induce 𝒜 ℬ ℳ K) (GFin.induce 𝒜 ℬ ℳ P) (GFin.induce 𝒜 ℬ ℳ N) where
  f := mapRight S.f
  g := mapRight S.g
  preservesGrading_f := fun _ _ hy => mapRight_mem_balancedGrading (ℳ := ℳ) S.preservesGrading_f hy
  preservesGrading_g := fun _ _ hy => mapRight_mem_balancedGrading (ℳ := ℳ) S.preservesGrading_g hy
  injective := h
  surjective := mapRight_surjective S.surjective
  exact := mapRight_exact S.f S.g S.exact S.surjective

end Categorification.Graded
