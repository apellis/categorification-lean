/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTrace

/-!
# Commutation of the quantum trace from commutation of the coevaluation

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21. Webster reduces the equivariance of the quantum trace `𝕋^{λ⁺}_λ` to
that of the coevaluation `𝕂^{λ⁺}_λ` "by taking adjoint". This file gives that step for one
1-morphism and its adjoint: if `𝕂` intertwines functors `E` on the two sides,
`𝕂 ⋙ E ≅ E ⋙ 𝕂`, and `E ⊣ F` on both sides, then the right adjoints satisfy
`F ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ F` (the conjugate, or mate, of the inverse isomorphism). With the
homological shift of Definition 7.18 the same holds for `𝕋^{λ⁺}_λ` when `F` commutes with shifts.
Applied to `E = 𝔈_i` (with `𝔈_i ⊣ 𝔉_i`) this gives `𝔉_i 𝕋 ≅ 𝕋 𝔉_i`, and applied to `E = 𝔉_i`
(with `𝔉_i ⊣ 𝔈_i`) it gives `𝔈_i 𝕋 ≅ 𝕋 𝔈_i`.

The compatibility of these isomorphisms with the 2-morphisms of `𝒰` (Definition 3.23) is not
treated here.

## Main definitions

* `CupCap.rightAdjointCommIso`: the generic conjugate isomorphism.
* `CupCap.coevaluationRightAdjointCommIso`: its instance for `RHom(K^{λ⁺}_λ, -)`.
* `CupCap.quantumTraceCommIso`: the instance for `𝕋^{λ⁺}_λ`, with its shift.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory

section Generic

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
  [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
  {K₁ : A₁ ⥤ B₁} {T₁ : B₁ ⥤ A₁} {K₂ : A₂ ⥤ B₂} {T₂ : B₂ ⥤ A₂}
  {EA : A₁ ⥤ A₂} {FA : A₂ ⥤ A₁} {EB : B₁ ⥤ B₂} {FB : B₂ ⥤ B₁}

/-- If `K₁ ⋙ E_B ≅ E_A ⋙ K₂`, with adjunctions `K_r ⊣ T_r`, `E_A ⊣ F_A` and `E_B ⊣ F_B`, then
`F_B ⋙ T₁ ≅ T₂ ⋙ F_A`: the conjugate of the inverse isomorphism along the composite adjunctions
`K₁ ⋙ E_B ⊣ F_B ⋙ T₁` and `E_A ⋙ K₂ ⊣ T₂ ⋙ F_A`. -/
def rightAdjointCommIso (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂) (adjA : EA ⊣ FA) (adjB : EB ⊣ FB)
    (c : K₁ ⋙ EB ≅ EA ⋙ K₂) : FB ⋙ T₁ ≅ T₂ ⋙ FA :=
  conjugateIsoEquiv (adj₁.comp adjB) (adjA.comp adj₂) c.symm

/-- The conjugate isomorphism followed by a shift: if moreover `F_A` commutes with the shift by
`n`, then `F_B ⋙ (T₁ ⋙ [n]) ≅ (T₂ ⋙ [n]) ⋙ F_A`. -/
def rightAdjointShiftCommIso [HasShift A₁ ℤ] [HasShift A₂ ℤ] [FA.CommShift ℤ]
    (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂) (adjA : EA ⊣ FA) (adjB : EB ⊣ FB)
    (c : K₁ ⋙ EB ≅ EA ⋙ K₂) (n : ℤ) :
    FB ⋙ (T₁ ⋙ shiftFunctor A₁ n) ≅ (T₂ ⋙ shiftFunctor A₂ n) ⋙ FA :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightAdjointCommIso adj₁ adj₂ adjA adjB c) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T₂ (FA.commShiftIso n).symm ≪≫
    (Functor.associator _ _ _).symm

end Generic

section Trace

open DG DG.DegreeZero

universe u

variable {I : Type u} [DecidableEq I] (k : Type u) [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν' ν₀ : Multiset I)
  (L : Type u) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [HasDerivedCategory.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [HasDerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ]
  [HasDerivedCategory.{u} (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ]
  [HasDerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν' + ν₀))ᵐᵒᵖ]

variable {k Q Λ Λc j hj ν ν' ν₀ L}

/-- Proof of Proposition 7.21 (arXiv:1309.3796v3), the reduction from the trace to the
coevaluation, for `RHom(K^{λ⁺}_λ, -)`: from `𝕂 ⋙ E_B ≅ E_A ⋙ 𝕂` (black weights `ν → ν'`) and
`E_A ⊣ F_A`, `E_B ⊣ F_B`, the right adjoints satisfy `F_B ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ F_A`. -/
def coevaluationRightAdjointCommIso
    {EA : DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ}
    {FA : DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}
    {EB : DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν' + ν₀))ᵐᵒᵖ}
    {FB : DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν' + ν₀))ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ}
    (adjA : EA ⊣ FA) (adjB : EB ⊣ FB)
    (c : coevaluationFunctor.{u} k Q Λ Λc j hj ν ν₀ L ⋙ EB ≅
      EA ⋙ coevaluationFunctor.{u} k Q Λ Λc j hj ν' ν₀ L) :
    FB ⋙ coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj ν' ν₀ L ⋙ FA :=
  rightAdjointCommIso (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
    (coevaluationAdjunction k Q Λ Λc j hj ν' ν₀ L) adjA adjB c

/-- Proof of Proposition 7.21 (arXiv:1309.3796v3), the reduction from the trace to the
coevaluation, for the quantum trace `𝕋^{λ⁺}_λ` of Definition 7.18 with homological shift
`shift`: when `F_A` commutes with shifts, `F_B ⋙ 𝕋 ≅ 𝕋 ⋙ F_A`. -/
def quantumTraceCommIso
    {EA : DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ}
    {FA : DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν')ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}
    {EB : DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν' + ν₀))ᵐᵒᵖ}
    {FB : DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν' + ν₀))ᵐᵒᵖ ⥤
      DG.DerivedCategory.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ}
    [FA.CommShift ℤ]
    (adjA : EA ⊣ FA) (adjB : EB ⊣ FB)
    (c : coevaluationFunctor.{u} k Q Λ Λc j hj ν ν₀ L ⋙ EB ≅
      EA ⋙ coevaluationFunctor.{u} k Q Λ Λc j hj ν' ν₀ L) (shift : ℤ) :
    FB ⋙ quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ν' ν₀ L shift ⋙ FA :=
  rightAdjointShiftCommIso (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
    (coevaluationAdjunction k Q Λ Λc j hj ν' ν₀ L) adjA adjB c shift

end Trace

end Categorification.Stendhal.CupCap
