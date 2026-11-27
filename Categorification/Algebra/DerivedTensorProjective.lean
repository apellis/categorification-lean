/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.ProjectiveKProjective
import Categorification.Algebra.CornerBimodule

set_option backward.isDefEq.respectTransparency false

/-!
# Derived tensor products with projective modules

A projective module `P`, placed in degree `0`, is K-projective, so `M ⊗ᴸ_B P` is the ordinary
tensor product `M ⊗_B P` in degree `0`, and has no cohomology outside degree `0`
(`isZero_derivedTensor_homology_of_projective`). The corner bimodule `e A e` is free of rank one
as a right module over the corner (`cornerBimoduleSelfEquiv`), hence projective.

This is used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 6.12, at the identity permutation.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

variable {A B : Type} [Ring A] [Ring B] [HasDerivedCategory.{w, 0} A] [HasDerivedCategory.{w, 0} B]
  (M : Type) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

/-- **Derived tensor products with a projective module are concentrated in degree `0`.** -/
theorem isZero_derivedTensor_homology_of_projective (P : Type) [AddCommGroup P] [Module B P]
    [Module.Projective B P] (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := A) ℤ n).obj ((derivedTensor.{w} A B M).obj
      (DG.DerivedCategory.Q.obj (DGModuleCat.of B (InDegreeZero P))))) := by
  let e := derivedTensorObjIso (A := A) (B := B) (M := M)
    («P» := DGModuleCat.of B (InDegreeZero P))
    (show IsKProjective B (InDegreeZero P) from InDegreeZero.isKProjective)
  let Z := DGModuleCat.of A (TensorProductOver B (InDegreeZero M) (InDegreeZero P))
  have hZ : IsZero ((homologyFunctor (A := A) ℤ n).obj (DG.DerivedCategory.Q.obj Z)) := by
    let : Subsingleton (cocycles Z n) := ⟨fun x y => by
      apply Subtype.ext
      have hx := TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn (mem_cocycles.mp x.2).1
      have hy := TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn (mem_cocycles.mp y.2).1
      exact hx.trans hy.symm⟩
    let : Subsingleton (cohomology Z n) := (cohomology.mk_surjective Z n).subsingleton
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((cohomologyAddEquiv ℤ Z n).surjective.subsingleton)
  exact hZ.of_iso ((homologyFunctor ℤ n).mapIso e)

section Corner

open MulOpposite CornerEndomorphism

variable {R : Type*} [Ring R] {e : R} (he : IsIdempotentElem e)

/-- The corner bimodule `e R e` is the corner `e R e` as a right module over itself. -/
def cornerBimoduleSelfEquiv : cornerBimodule e e ≃ₗ[he.Cornerᵐᵒᵖ] he.Cornerᵐᵒᵖ where
  toFun x := op ⟨x.1, x.1, show e * x.1 * e = x.1 by rw [x.2.1, x.2.2]⟩
  invFun c := ⟨c.unop.1, corner_mul_left he c.unop, corner_mul_right he c.unop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance projective_cornerBimodule_self : Module.Projective he.Cornerᵐᵒᵖ (cornerBimodule e e) :=
  Module.Projective.of_equiv (cornerBimoduleSelfEquiv he).symm

end Corner

end Categorification
