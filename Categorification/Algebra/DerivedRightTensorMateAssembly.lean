/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorMateAssembly
import Categorification.Algebra.DerivedRightTensorDualAdjunction

/-!
# Exchanging a right adjoint with derived tensor products on right modules

The form of `rightAdjointExchangeIso` for derived tensor products on right modules
(`derivedRightTensor`), which is how the coevaluation functor and the standardization functors
of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
act. For bimodules `K` (`T`–`T⁺`), `K_b` (`B`–`E`), `S` (`B`–`T`) and `S₊` (`E`–`T⁺`), with `S`
and `S₊` finitely generated projective as left modules, and right adjoints `𝕋` of `- ⊗ᴸ_T K`
and `𝕋_b` of `- ⊗ᴸ_B K_b`:

`(- ⊗ᴸ_E S₊) ⋙ 𝕋 ≅ 𝕋_b ⋙ (- ⊗ᴸ_B S)`

given `Tor^{T⁺}_{>0}(K, S₊^∨) = 0` and a bimodule isomorphism `K ⊗_{T⁺} S₊^∨ ≅ S^∨ ⊗_B K_b`
(`rightAdjointExchangeIsoRight`). Both inputs are written through `OpBimodule`, as the
definition of `derivedRightTensor` is.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits DG MulOpposite
open scoped DG.DegreeZero DG.TensorProductOver.RightAction

universe u

section Tor

variable (A A' : Type u) [Ring A] [Ring A'] [HasDerivedCategory.{u, u} A]
  [HasDerivedCategory.{u, u} A'] (M N : Type u) [AddCommGroup M] [Module A M]
  [Module A'ᵐᵒᵖ M] [SMulCommClass A A'ᵐᵒᵖ M] [AddCommGroup N] [Module A' N]

/-- `Tor^{A'}_{n}(M, N) = 0` for every `n ≠ 0`, as the vanishing of the homology of
`M ⊗ᴸ_{A'} N` off degree `0`. -/
def TorVanishesOffZero : Prop :=
  ∀ n : ℤ, n ≠ 0 → IsZero ((DG.DerivedCategory.homologyFunctor (A := A) ℤ n).obj
    ((derivedTensor.{u} A A' M).obj
      (DG.DerivedCategory.Q.obj (DGModuleCat.of A' (InDegreeZero N)))))

end Tor

variable (B T Tp E : Type u) [Ring B] [Ring T] [Ring Tp] [Ring E]
  [HasDerivedCategory.{u, u} Bᵐᵒᵖ] [HasDerivedCategory.{u, u} Tᵐᵒᵖ]
  [HasDerivedCategory.{u, u} Tpᵐᵒᵖ] [HasDerivedCategory.{u, u} Eᵐᵒᵖ]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj Bᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj Tᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj Tpᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj Eᵐᵒᵖ)]
  (K : Type u) [AddCommGroup K] [Module T K] [Module Tpᵐᵒᵖ K] [SMulCommClass T Tpᵐᵒᵖ K]
  (Kb : Type u) [AddCommGroup Kb] [Module B Kb] [Module Eᵐᵒᵖ Kb] [SMulCommClass B Eᵐᵒᵖ Kb]
  (S : Type u) [AddCommGroup S] [Module B S] [Module Tᵐᵒᵖ S] [SMulCommClass B Tᵐᵒᵖ S]
  [Module.Projective B S] [Module.Finite B S]
  (Sp : Type u) [AddCommGroup Sp] [Module E Sp] [Module Tpᵐᵒᵖ Sp] [SMulCommClass E Tpᵐᵒᵖ Sp]
  [Module.Projective E Sp] [Module.Finite E Sp]

/-- **Exchanging the right adjoints, on right modules**: `(- ⊗ᴸ_E S₊) ⋙ 𝕋 ≅ 𝕋_b ⋙ (- ⊗ᴸ_B S)`
for any right adjoints `𝕋` of `- ⊗ᴸ_T K` and `𝕋_b` of `- ⊗ᴸ_B K_b`, given
`Tor^{T⁺}_{>0}(K, S₊^∨) = 0` (`hv`) and a bimodule isomorphism `K ⊗_{T⁺} S₊^∨ ≅ S^∨ ⊗_B K_b`
(`Φ`, linear for `E` on the right and `T` on the left). -/
def rightAdjointExchangeIsoRight
    {𝕋 : DerivedCategory.{u, u} Tpᵐᵒᵖ ⥤ DerivedCategory.{u, u} Tᵐᵒᵖ}
    (adj : derivedRightTensor.{u} T Tp K ⊣ 𝕋)
    {𝕋b : DerivedCategory.{u, u} Eᵐᵒᵖ ⥤ DerivedCategory.{u, u} Bᵐᵒᵖ}
    (adjb : derivedRightTensor.{u} B E Kb ⊣ 𝕋b)
    (hv : TorVanishesOffZero Eᵐᵒᵖ Tpᵐᵒᵖ (RightDualModule Eᵐᵒᵖ (OpBimodule E Sp))
      (OpBimodule T K))
    (Φ : TensorProductOver Tpᵐᵒᵖ (InDegreeZero (RightDualModule Eᵐᵒᵖ (OpBimodule E Sp)))
        (InDegreeZero (OpBimodule T K)) ≃ₗ[Eᵐᵒᵖ]
      TensorProductOver Bᵐᵒᵖ (InDegreeZero (OpBimodule B Kb))
        (InDegreeZero (RightDualModule Bᵐᵒᵖ (OpBimodule B S))))
    (hΦ : ∀ (b : Tᵐᵒᵖ) (x : TensorProductOver Tpᵐᵒᵖ
      (InDegreeZero (RightDualModule Eᵐᵒᵖ (OpBimodule E Sp))) (InDegreeZero (OpBimodule T K))),
        Φ (op b • x) = op b • Φ x) :
    derivedRightTensor.{u} E Tp Sp ⋙ 𝕋 ≅ 𝕋b ⋙ derivedRightTensor.{u} B T S :=
  haveI := OpBimodule.moduleProjective_opOp (C := B) (N := S)
  haveI := OpBimodule.moduleFinite_opOp (C := B) (N := S)
  haveI := OpBimodule.moduleProjective_opOp (C := E) (N := Sp)
  haveI := OpBimodule.moduleFinite_opOp (C := E) (N := Sp)
  rightAdjointExchangeIso Bᵐᵒᵖ Tᵐᵒᵖ Tpᵐᵒᵖ Eᵐᵒᵖ (OpBimodule T K) (OpBimodule B Kb)
    (OpBimodule B S) (OpBimodule E Sp) adj adjb hv Φ hΦ

end Categorification
