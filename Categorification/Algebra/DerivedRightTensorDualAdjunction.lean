/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorDualAdjunction

/-!
# The left adjoint of `- ⊗ᴸ_C N` for a finitely generated projective left module `N`

For rings `C`, `C'` and a `(C, C')`-bimodule `N` which is finitely generated and projective as a
left `C`-module, the derived tensor product on right modules
`- ⊗ᴸ_C N = derivedRightTensor C C' N : D(Cᵐᵒᵖ) ⥤ D(C'ᵐᵒᵖ)` has the left adjoint
`- ⊗ᴸ_{C'} N^∨`, `N^∨ = Hom_C(N, C)` (`Categorification.derivedRightTensorDualAdjunction`). This is
`Categorification.derivedTensorDualAdjunction` for the coefficient `OpBimodule C N`, after moving
projectivity and finite generation along `C ≃ Cᵐᵒᵖᵐᵒᵖ`.

It is the form used for the standardization functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Lemma 7.19, which act on right modules.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe w u

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace OpBimodule

variable {C : Type*} [Ring C] {N : Type*} [AddCommGroup N] [Module C N]

/-- The identity of `N`, semilinear along `C ≃ Cᵐᵒᵖᵐᵒᵖ`, onto `OpBimodule C N`. -/
def opOpSemilinearEquiv :
    N ≃ₛₗ[((RingEquiv.opOp C : C ≃+* Cᵐᵒᵖᵐᵒᵖ) : C →+* Cᵐᵒᵖᵐᵒᵖ)] OpBimodule C N where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- A projective left `C`-module is projective as a right `Cᵐᵒᵖ`-module. -/
theorem moduleProjective_opOp [Module.Projective C N] :
    Module.Projective Cᵐᵒᵖᵐᵒᵖ (OpBimodule C N) :=
  Module.Projective.of_equiv (σ := ((RingEquiv.opOp C : C ≃+* Cᵐᵒᵖᵐᵒᵖ) : C →+* Cᵐᵒᵖᵐᵒᵖ))
    (σ' := ((RingEquiv.opOp C).symm : Cᵐᵒᵖᵐᵒᵖ →+* C)) opOpSemilinearEquiv

/-- A finitely generated left `C`-module is finitely generated as a right `Cᵐᵒᵖ`-module. -/
theorem moduleFinite_opOp [Module.Finite C N] : Module.Finite Cᵐᵒᵖᵐᵒᵖ (OpBimodule C N) :=
  Module.Finite.of_surjective (opOpSemilinearEquiv (C := C) (N := N)).toLinearMap
    opOpSemilinearEquiv.surjective

end OpBimodule

variable (C C' : Type u) [Ring C] [Ring C'] (N : Type u) [AddCommGroup N] [Module C N]
  [Module C'ᵐᵒᵖ N] [SMulCommClass C C'ᵐᵒᵖ N] [Module.Projective C N] [Module.Finite C N]
  [CatModule.HasDerivedCategory.{w, u} (SingleObj Cᵐᵒᵖ)]
  [CatModule.HasDerivedCategory.{w, u} (SingleObj C'ᵐᵒᵖ)]
  [DG.HasDerivedCategory.{w, u} Cᵐᵒᵖ] [DG.HasDerivedCategory.{w, u} C'ᵐᵒᵖ]

/-- **The left adjoint of `- ⊗ᴸ_C N`**: for a `(C, C')`-bimodule `N` which is finitely generated
and projective as a left `C`-module, `- ⊗ᴸ_{C'} N^∨ ⊣ - ⊗ᴸ_C N` on derived categories of right
modules, with `N^∨ = Hom_C(N, C)` written as `RightDualModule Cᵐᵒᵖ (OpBimodule C N)`. -/
def derivedRightTensorDualAdjunction :
    derivedTensor.{w} Cᵐᵒᵖ C'ᵐᵒᵖ (RightDualModule Cᵐᵒᵖ (OpBimodule C N)) ⊣
      derivedRightTensor.{w} C C' N :=
  haveI := OpBimodule.moduleProjective_opOp (C := C) (N := N)
  haveI := OpBimodule.moduleFinite_opOp (C := C) (N := N)
  derivedTensorDualAdjunction.{w} C'ᵐᵒᵖ Cᵐᵒᵖ (OpBimodule C N)

end Categorification
