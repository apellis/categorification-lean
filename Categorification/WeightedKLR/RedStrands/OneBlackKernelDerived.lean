/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstWeightBlockKernel
import Categorification.WeightedKLR.RedStrands.ProjectiveKernelDerived

/-!
# Derived braid vanishing at one black strand

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The higher kernel is projective and the ordinary balanced inclusion is injective
for all red spectators. The short exact sequence gives derived concentration.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory KLR
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w v

variable {I : Type} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} (i : I)
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "ν₁" => (Singleton.singleton i : Multiset I)

set_option backward.isDefEq.respectTransparency false in
/-- The derived braid of the actual one-black partial standard is concentrated
in degree zero for symmetric parameters over any commutative ring. -/
theorem firstWeight_blockPartialStandard_braid_homology_vanish
    (t : KLR.Seq (stendhalWeight ℓ ν₁)) (a b : Fin ℓ) (κ : List (Fin ℓ))
    [sourceDerived : HasDerivedCategory.{w, v}
      (isIdempotentElem_violMk_redProj k Q Λ ν₁ (redWord t)).Cornerᵐᵒᵖ]
    [targetDerived : HasDerivedCategory.{w, v}
      (isIdempotentElem_violMk_redProj k Q Λ ν₁ κ).Cornerᵐᵒᵖ]
    (hQ : KLRSymm Q) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
      (A := (isIdempotentElem_violMk_redProj k Q Λ ν₁ κ).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₁ (redWord t) κ).obj (DG.DerivedCategory.Q.obj
        ((degreeZeroModuleFunctor (isIdempotentElem_violMk_redProj k Q Λ ν₁ (redWord t)).Cornerᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t a b).X₃)))) := by
  have hP : Module.Projective (isIdempotentElem_violMk_redProj k Q Λ ν₁ (redWord t)).Cornerᵐᵒᵖ
      (blockLoadingKernel Q Λ t a b) :=
    firstWeight_blockLoadingKernel_projective i Q Λ a b t hQ
  have hbal : Function.Injective (blockKernelTensorInclusion Q Λ t a b κ) :=
    firstWeight_blockKernelTensorInclusion_injective i Q Λ a b t κ hQ
  exact blockPartialStandard_braid_homology_vanish_of_projective_kernel Q Λ t a b κ hP hbal n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
