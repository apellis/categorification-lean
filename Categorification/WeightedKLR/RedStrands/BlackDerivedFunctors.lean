/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongDerived
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

set_option backward.isDefEq.respectTransparency false

/-!
# `Eᵢ` and `Fᵢ` on derived categories of right `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6, the
functors `Fᵢ M = M ⊗_{T^λ_ν} e' T^λ_{ν+i}` and `Eᵢ N = N e' = N ⊗_{T^λ_{ν+i}} T^λ_{ν+i} e'` on
right modules (`blackF`, `blackE`), and their derived functors, which Webster uses on the derived
categories `D(T^λ_ν)` in §§6–7.

Right modules are left modules over the opposite algebras, and `e' = appendBlackOp 1`. The
derived functors are derived tensor products of dg modules, in the form of
`coevaluationFunctor` (functors between the derived categories of left modules over the
opposite algebras, that is, of right modules):

* `derivedBlackE`: `- ⊗ᴸ e' T^λ_{ν+i}ᵐᵒᵖ`, with the right ideal `RCorner` of `appendBlackOp`;
* `derivedBlackF`: `- ⊗ᴸ T^λ_{ν+i}ᵐᵒᵖ e'`, with the corner `Corner` of `appendBlackOp`.

**Projectivity.** A derived tensor product is computed degreewise, without resolutions, when the
bimodule is projective over the ring one tensors over (`derivedTensorComparisonIso`).

* For `Eᵢ`, the bimodule `e' T^λ_{ν+i}` (in the opposite ring) is a direct summand of the
  regular module over the ring one tensors over (`InductionAlong.RCorner.projective`), with no
  hypothesis.
* For `Fᵢ`, the bimodule `e' T^λ_{ν+i}` must be projective as a left `T^λ_ν`-module: this is
  Webster's Theorem 4.31 (`projective_blackCorner`), over a field with Rouquier polynomials `Q`.
  As a right `T^λ_{ν+i}`-module it is a summand of the regular module, so it is projective with
  no hypothesis on that side.

Under the comparison of derived categories of dg modules with Mathlib's derived categories of
modules (`DG.DegreeZero.derivedComparison`), the two derived functors are the derived functors
of the exact functors `blackE` and `blackF` (`derivedBlackEComparisonIso`,
`derivedBlackFComparisonIso`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory DG DG.DegreeZero MulOpposite InductionAlong KLR

universe w w' u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "T'" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)

/-! ### Exactness on modules -/

private theorem blackE_additive' : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{u, u} (appendBlackOp Q Λ i ν)).Additive

private theorem blackF_additive' : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{u, u} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackE_additive' blackF_additive'

instance blackE_preservesFiniteLimits : Limits.PreservesFiniteLimits (blackE Q Λ i ν) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (resFunctor.{u, u} (appendBlackOp Q Λ i ν)))

instance blackE_preservesFiniteColimits : Limits.PreservesFiniteColimits (blackE Q Λ i ν) :=
  inferInstanceAs (Limits.PreservesFiniteColimits (resFunctor.{u, u} (appendBlackOp Q Λ i ν)))

/-- `Fᵢ` is left exact (Webster, Theorem 4.31). -/
theorem blackF_preservesFiniteLimits (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    Limits.PreservesFiniteLimits (blackF Q Λ i ν) :=
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  functor_preservesFiniteLimits (appendBlackOp Q Λ i ν)

/-- `Fᵢ` is right exact. -/
theorem blackF_preservesFiniteColimits (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    Limits.PreservesFiniteColimits (blackF Q Λ i ν) :=
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  functor_preservesFiniteColimits (appendBlackOp Q Λ i ν)

/-! ### The derived functors -/

variable [HasDerivedCategory.{w} Tᵐᵒᵖ] [HasDerivedCategory.{w} T'ᵐᵒᵖ]

/-- **Webster's `Eᵢ` on derived categories** of right modules, `N ↦ N ⊗ᴸ_{T^λ_{ν+i}} T^λ_{ν+i} e'`,
the derived tensor product with the right ideal `e' T^λ_{ν+i}ᵐᵒᵖ` of the opposite ring. -/
def derivedBlackE : DG.DerivedCategory.{w} T'ᵐᵒᵖ ⥤ DG.DerivedCategory.{w} Tᵐᵒᵖ :=
  derivedTensor.{w} Tᵐᵒᵖ T'ᵐᵒᵖ (RCorner (appendBlackOp Q Λ i ν))

/-- **Webster's `Fᵢ` on derived categories** of right modules, `M ↦ M ⊗ᴸ_{T^λ_ν} e' T^λ_{ν+i}`,
the derived tensor product with the corner `T^λ_{ν+i}ᵐᵒᵖ e'` of the opposite ring. -/
def derivedBlackF : DG.DerivedCategory.{w} Tᵐᵒᵖ ⥤ DG.DerivedCategory.{w} T'ᵐᵒᵖ :=
  derivedTensor.{w} T'ᵐᵒᵖ Tᵐᵒᵖ (Corner (appendBlackOp Q Λ i ν))

variable [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} Tᵐᵒᵖ)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} T'ᵐᵒᵖ)]

/-- **The derived `Eᵢ` is the derived functor of the exact functor `Eᵢ`**, with no hypothesis:
the bimodule is a summand of the regular module. -/
def derivedBlackEComparisonIso :
    derivedBlackE.{w} Q Λ i ν ⋙ derivedComparison.{w, w'} Tᵐᵒᵖ ≅
      derivedComparison.{w, w'} T'ᵐᵒᵖ ⋙ (blackE Q Λ i ν).mapDerivedCategory :=
  derivedTensorComparisonIso.{w, w'} Tᵐᵒᵖ T'ᵐᵒᵖ (RCorner (appendBlackOp Q Λ i ν)) ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryIsoOfIso (resOrdIso (appendBlackOp Q Λ i ν)))

/-- **The derived `Fᵢ` is the derived functor of the exact functor `Fᵢ`**, for Rouquier
polynomials over a field (Webster, Theorem 4.31: `e' T^λ_{ν+i}` is a projective left
`T^λ_ν`-module). -/
def derivedBlackFComparisonIso (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
    letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
    derivedBlackF.{w} Q Λ i ν ⋙ derivedComparison.{w, w'} T'ᵐᵒᵖ ≅
      derivedComparison.{w, w'} Tᵐᵒᵖ ⋙ (blackF Q Λ i ν).mapDerivedCategory :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
  letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  letI := functor_preservesFiniteLimits (appendBlackOp Q Λ i ν)
  letI := functor_preservesFiniteColimits (appendBlackOp Q Λ i ν)
  derivedTensorComparisonIso.{w, w'} T'ᵐᵒᵖ Tᵐᵒᵖ (Corner (appendBlackOp Q Λ i ν)) ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryIsoOfIso (indOrdIso (appendBlackOp Q Λ i ν)))

end Categorification.Stendhal
