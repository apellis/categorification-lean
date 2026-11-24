/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstWeightBlockKernel
import Categorification.WeightedKLR.RedStrands.OneBlackKernelProjective
import Categorification.WeightedKLR.RedStrands.ProjectiveKernelDerived

/-!
# Derived braid vanishing at one black strand

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The higher kernel is projective and the ordinary balanced inclusion is injective
for all red spectators. The short exact sequence gives derived concentration.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory DG DG.DerivedCategory KLR QuantumGroup KL3.Diagram
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {D : CartanDatum I} {i : I}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)
local notation "ν₁" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν₁

variable (Λ : Fin ℓ → I →₀ ℕ) (t : Seq μ) (a b : Fin ℓ) (L M : List (Fin ℓ))
local notation "κ" => L ++ b :: a :: M
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k QL Λ ν₁ (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k QL Λ ν₁ κ)

variable [HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [HasDerivedCategory.{w, 0} Uᵐᵒᵖ]

/-- The derived braid of an actual one-black partial standard is concentrated
in degree zero for the standard Khovanov–Lauda parameters. -/
theorem oneBlack_partialStandard_braid_homology_vanish_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL)
    (ht : redWord t = L ++ a :: b :: M)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k QL Λ ν₁ (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
          (blockLoadingShortComplex QL Λ t a b).X₃)))) := by
  have hP : Module.Projective Tᵐᵒᵖ (blockLoadingKernel QL Λ t a b) :=
    oneBlack_kernel_projective_standard hR hQ i Λ a b t ht
  have hbal : Function.Injective (blockKernelTensorInclusion QL Λ t a b κ) :=
    firstWeight_blockKernelTensorInclusion_injective i QL Λ a b t κ hQ
  exact blockPartialStandard_braid_homology_vanish_of_projective_kernel QL Λ t a b κ hP hbal n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
