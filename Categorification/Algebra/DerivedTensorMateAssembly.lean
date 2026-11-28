/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorDualAdjunction
import Categorification.Algebra.DerivedTensorCompComparison
import Categorification.Algebra.DerivedTensorDegreeZero

/-!
# Exchanging a right adjoint with derived tensor products by mates

Let `𝕂 = K ⊗ᴸ_{R₁} - : D(R₁) ⥤ D(R₂)` and `𝕂_b = K_b ⊗ᴸ_{R₀} - : D(R₀) ⥤ D(R₃)` be derived
tensor products with right adjoints `𝕋`, `𝕋_b`, and let `𝕊 = S ⊗ᴸ_{R₀} -`,
`𝕊₊ = S₊ ⊗ᴸ_{R₃} -` be derived tensor products with bimodules that are finitely generated
projective on the right. Then `𝕊` and `𝕊₊` are right adjoints of the derived tensor products with
the duals `S^∨`, `S₊^∨`, and

`𝕋 ∘ 𝕊₊ ≅ 𝕊 ∘ 𝕋_b`

follows from an isomorphism of the left adjoints. These are `S₊^∨ ⊗ᴸ_{R₂} (K ⊗ᴸ -)` and
`K_b ⊗ᴸ_{R₀} (S^∨ ⊗ᴸ -)`. The second is `(K_b ⊗_{R₀} S^∨) ⊗ᴸ -` because `S^∨` is projective.
The first is `(S₊^∨ ⊗_{R₂} K) ⊗ᴸ -` when `Tor^{R₂}_{>0}(S₊^∨, K) = 0`.
So the inputs are this Tor vanishing and a bimodule isomorphism
`S₊^∨ ⊗_{R₂} K ≅ K_b ⊗_{R₀} S^∨` (`rightAdjointExchangeIso`).

This is the assembly of the trace half of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, Lemma 7.19, `𝕋 𝕊₊(Z ⊠ N) ≅ 𝕊(Z ⊗ 𝕋_∅ N)`, with `𝕂` the coevaluation
functor, `𝕊`, `𝕊₊` the (partial) standardizations and `𝕂_b = - ⊠ L` on the blocks.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits DG MulOpposite
open scoped DG.DegreeZero DG.TensorProductOver.RightAction

universe u

variable (R₀ R₁ R₂ R₃ : Type u) [Ring R₀] [Ring R₁] [Ring R₂] [Ring R₃]
  [HasDerivedCategory.{u, u} R₀] [HasDerivedCategory.{u, u} R₁]
  [HasDerivedCategory.{u, u} R₂] [HasDerivedCategory.{u, u} R₃]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj R₁)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj R₀)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj R₂)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj R₃)]
  (K : Type u) [AddCommGroup K] [Module R₂ K] [Module R₁ᵐᵒᵖ K] [SMulCommClass R₂ R₁ᵐᵒᵖ K]
  (Kb : Type u) [AddCommGroup Kb] [Module R₃ Kb] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb]
  (S : Type u) [AddCommGroup S] [Module R₁ S] [Module R₀ᵐᵒᵖ S] [SMulCommClass R₁ R₀ᵐᵒᵖ S]
  [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  (Sp : Type u) [AddCommGroup Sp] [Module R₂ Sp] [Module R₃ᵐᵒᵖ Sp] [SMulCommClass R₂ R₃ᵐᵒᵖ Sp]
  [Module.Projective R₃ᵐᵒᵖ Sp] [Module.Finite R₃ᵐᵒᵖ Sp]

/-- The isomorphism of the two left adjoints,
`S₊^∨ ⊗ᴸ_{R₂} (K ⊗ᴸ_{R₁} -) ≅ K_b ⊗ᴸ_{R₀} (S^∨ ⊗ᴸ_{R₀} -)`, from `Tor^{R₂}_{>0}(S₊^∨, K) = 0`
and a bimodule isomorphism `S₊^∨ ⊗_{R₂} K ≅ K_b ⊗_{R₀} S^∨`. -/
def leftAdjointExchangeIso
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((DG.DerivedCategory.homologyFunctor (A := R₃) ℤ n).obj
      ((derivedTensor.{u} R₃ R₂ (RightDualModule R₃ Sp)).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of R₂ (InDegreeZero K))))))
    (Φ : TensorProductOver R₂ (InDegreeZero (RightDualModule R₃ Sp)) (InDegreeZero K) ≃ₗ[R₃]
      TensorProductOver R₀ (InDegreeZero Kb) (InDegreeZero (RightDualModule R₀ S)))
    (hΦ : ∀ (b : R₁) (x : TensorProductOver R₂ (InDegreeZero (RightDualModule R₃ Sp))
      (InDegreeZero K)), Φ (op b • x) = op b • Φ x) :
    derivedTensor.{u} R₂ R₁ K ⋙ derivedTensor.{u} R₃ R₂ (RightDualModule R₃ Sp) ≅
      derivedTensor.{u} R₀ R₁ (RightDualModule R₀ S) ⋙ derivedTensor.{u} R₃ R₀ Kb :=
  derivedTensorCompIsoOfTorVanishing R₃ R₂ R₁ (RightDualModule R₃ Sp) K hv ≪≫
    dgDerivedTensorIsoOfEquiv
      (DGModuleEquiv.ofDegreeZero Φ
        (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
        TensorProductOver.d_inDegreeZero TensorProductOver.mem_grading_zero_inDegreeZero
        TensorProductOver.d_inDegreeZero) hΦ ≪≫
    (dgDerivedTensorCompIso (A := R₃) (B := R₀) (C := R₁) (InDegreeZero Kb)
      (N := InDegreeZero (RightDualModule R₀ S)) InDegreeZero.isKProjective).symm

/-- **Exchanging the right adjoints**: `𝕋 ∘ 𝕊₊ ≅ 𝕊 ∘ 𝕋_b` for any right adjoints `𝕋` of
`K ⊗ᴸ_{R₁} -` and `𝕋_b` of `K_b ⊗ᴸ_{R₀} -`, given `Tor^{R₂}_{>0}(S₊^∨, K) = 0` and a bimodule
isomorphism `S₊^∨ ⊗_{R₂} K ≅ K_b ⊗_{R₀} S^∨`. -/
def rightAdjointExchangeIso
    {T : DerivedCategory.{u, u} R₂ ⥤ DerivedCategory.{u, u} R₁}
    (adj : derivedTensor.{u} R₂ R₁ K ⊣ T)
    {Tb : DerivedCategory.{u, u} R₃ ⥤ DerivedCategory.{u, u} R₀}
    (adjb : derivedTensor.{u} R₃ R₀ Kb ⊣ Tb)
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((DG.DerivedCategory.homologyFunctor (A := R₃) ℤ n).obj
      ((derivedTensor.{u} R₃ R₂ (RightDualModule R₃ Sp)).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of R₂ (InDegreeZero K))))))
    (Φ : TensorProductOver R₂ (InDegreeZero (RightDualModule R₃ Sp)) (InDegreeZero K) ≃ₗ[R₃]
      TensorProductOver R₀ (InDegreeZero Kb) (InDegreeZero (RightDualModule R₀ S)))
    (hΦ : ∀ (b : R₁) (x : TensorProductOver R₂ (InDegreeZero (RightDualModule R₃ Sp))
      (InDegreeZero K)), Φ (op b • x) = op b • Φ x) :
    derivedTensor.{u} R₂ R₃ Sp ⋙ T ≅ Tb ⋙ derivedTensor.{u} R₁ R₀ S :=
  Adjunction.rightAdjointUniq
    (adj.comp (derivedTensorDualAdjunction.{u} R₂ R₃ Sp))
    ((((derivedTensorDualAdjunction.{u} R₁ R₀ S).comp adjb).ofNatIsoLeft
      (leftAdjointExchangeIso R₀ R₁ R₂ R₃ K Kb S Sp hv Φ hΦ).symm))

end Categorification
