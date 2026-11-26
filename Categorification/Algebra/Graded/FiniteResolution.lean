/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.EulerCharacteristic
import Categorification.Algebra.Graded.Simple
import Categorification.Algebra.Graded.Tensor
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Graded resolutions of modules of finite projective dimension

Let `A` be a finite-dimensional graded algebra over a field `k`. Every finite-dimensional graded
`A`-module `N` is a degree-preserving quotient of the graded projective module `A ⊗_k N`
(`GFin.cover`, `GFin.coverMap`), with a finite-dimensional graded kernel (`GFin.coverKernel`).
Iterating, a module of finite projective dimension has a finite resolution by finitely generated
graded projective modules (`GFin.exists_resolution_of_hasProjectiveDimensionLT`). This is the
graded form of the finite projective resolutions of standard modules used in B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v2, Corollary 5.22 and the
proof of Corollary 6.10.

## Main definitions and results

* `GFin.cover N` : the graded projective module `A ⊗_k N`.
* `GFin.coverShortExact N` : the short exact sequence `0 → K → A ⊗_k N → N → 0`.
* `GFin.exists_resolution_of_hasProjectiveDimensionLT`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum CategoryTheory TensorProduct

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [Module.Finite k A]

namespace GFin

variable (N : GFin 𝒜)

/-- The graded projective cover `A ⊗_k N` of a finite-dimensional graded module. -/
def cover : GProj 𝒜 where
  carrier := A ⊗[k] N.carrier
  grading := tensorGrading 𝒜 N.grading
  finite := Module.Finite.of_restrictScalars_finite k A _
  projective := inferInstance

/-- The action map `A ⊗_k N → N`. -/
def coverMap : (A ⊗[k] N.carrier) →ₗ[A] N.carrier :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun n => a • n
          map_add' := smul_add a
          map_smul' := fun c n => smul_comm a c n }
      map_add' := fun a b => by ext n; exact add_smul a b n
      map_smul' := fun a b => by ext n; exact mul_smul a b n }

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
@[simp] theorem coverMap_tmul (a : A) (n : N.carrier) : coverMap N (a ⊗ₜ n) = a • n := rfl

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem coverMap_preservesGrading :
    PreservesGrading (tensorGrading 𝒜 N.grading) N.grading (coverMap N) := fun _ _ hx =>
  tensorGrading_map_mem 𝒜 N.grading N.grading ((coverMap N).restrictScalars k)
    (fun _ _ _ _ ha hn => SetLike.GradedSMul.smul_mem ha hn) hx

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem coverMap_surjective : Function.Surjective (coverMap N) := fun n =>
  ⟨1 ⊗ₜ n, by rw [coverMap_tmul, one_smul]⟩

/-- The kernel of `A ⊗_k N → N`, a finite-dimensional graded module. -/
def coverKernel : GFin 𝒜 :=
  letI := submoduleDecomposition (tensorGrading 𝒜 N.grading)
    (isHomogeneous_ker (coverMap_preservesGrading N))
  { carrier := LinearMap.ker (coverMap N)
    grading := submodule (tensorGrading 𝒜 N.grading) (LinearMap.ker (coverMap N))
    finiteDimensional := Module.Finite.of_injective
      ((LinearMap.ker (coverMap N)).subtype.restrictScalars k) Subtype.val_injective }

/-- The short exact sequence `0 → K → A ⊗_k N → N → 0`. -/
def coverShortExact : GFin.ShortExact (coverKernel N) (cover N).toGFin N where
  f := (LinearMap.ker (coverMap N)).subtype
  g := coverMap N
  preservesGrading_f := fun _ _ hx => hx
  preservesGrading_g := coverMap_preservesGrading N
  injective := Subtype.val_injective
  surjective := coverMap_surjective N
  exact := LinearMap.exact_subtype_ker_map _

/-- A finite-dimensional graded module that is projective, as a graded projective module. -/
def toGProj [Module.Projective A N.carrier] : GProj 𝒜 :=
  { N.toGMod with finite := Module.Finite.of_restrictScalars_finite k A _ }

/-- **Finite graded projective resolutions.** A finite-dimensional graded module of projective
dimension `≤ n` has a resolution by finitely generated graded projective modules. -/
theorem exists_resolution_of_hasProjectiveDimensionLT (n : ℕ) :
    ∀ (N : GFin 𝒜), HasProjectiveDimensionLT (ModuleCat.of A N.carrier) (n + 1) →
      ∃ Ps : List (GProj 𝒜), Nonempty (GFin.Resolution N (Ps.map GProj.toGFin)) := by
  induction n with
  | zero =>
    intro N hN
    have : Module.Projective A N.carrier := (IsProjective.iff_projective _).mpr inferInstance
    exact ⟨[N.toGProj], ⟨.single (GradedEquiv.ofEq rfl)⟩⟩
  | succ n ih =>
    intro N hN
    let S := coverShortExact N
    let T : ShortComplex (ModuleCat.{u} A) :=
      { X₁ := ModuleCat.of A (coverKernel N).carrier
        X₂ := ModuleCat.of A (cover N).carrier
        X₃ := ModuleCat.of A N.carrier
        f := ModuleCat.ofHom S.f
        g := ModuleCat.ofHom S.g
        zero := by ext x; exact S.exact.apply_apply_eq_zero x }
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T S.exact S.injective S.surjective
    have : Projective T.X₂ := (IsProjective.iff_projective _).mp (cover N).projective
    have hK : HasProjectiveDimensionLT T.X₁ (n + 1) := hT.hasProjectiveDimensionLT_X₁ (n + 1)
      inferInstance hN
    obtain ⟨Ps, ⟨r⟩⟩ := ih (coverKernel N) hK
    exact ⟨cover N :: Ps, ⟨.cons S r⟩⟩

end GFin

end Categorification.Graded
