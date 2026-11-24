/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoOutgoingRows
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The label-two outgoing augmentation

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The outgoing crossing
has its actual cokernel as the terminal augmentation. The map to this
quotient is surjective and exact at the complementary exterior
projective.
-/

namespace Categorification.Stendhal

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "T" => TensorProductAlgebra k param wt ν
local notation "P" => lIdeal (labelTwoLeftExteriorProjector param)
local notation "d" => labelTwoMiddleExteriorDifferential param
local notation "I" => LinearMap.range (d)

/-- The actual cokernel of the outgoing label-two crossing. -/
abbrev labelTwoExteriorCokernel := P ⧸ I

/-- The canonical augmentation of the complementary exterior divided projective. -/
def labelTwoExteriorAugmentation : P →ₗ[T] labelTwoExteriorCokernel param := (I).mkQ

theorem labelTwoExteriorAugmentation_surjective :
    Function.Surjective (labelTwoExteriorAugmentation param) :=
  (I).mkQ_surjective

theorem labelTwoExteriorAugmentation_exact :
    Function.Exact (d) (labelTwoExteriorAugmentation param) :=
  LinearMap.exact_iff.mpr (Submodule.ker_mkQ (I))

theorem labelTwoExteriorAugmentation_comp_zero :
    (labelTwoExteriorAugmentation param).comp (d) = 0 := by
  apply LinearMap.ext
  intro z
  exact (Submodule.Quotient.mk_eq_zero (I)).mpr ⟨z,rfl⟩

/-- The outgoing crossing followed by its actual cokernel augmentation. -/
def labelTwoExteriorEndComplex : CategoryTheory.ShortComplex (ModuleCat T) :=
  CategoryTheory.ShortComplex.mk (ModuleCat.ofHom d)
    (ModuleCat.ofHom (labelTwoExteriorAugmentation param))
    (ModuleCat.hom_ext (labelTwoExteriorAugmentation_comp_zero param))

theorem labelTwoExteriorEndComplex_exact : (labelTwoExteriorEndComplex param).Exact :=
  (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (labelTwoExteriorAugmentation_exact param)

theorem labelTwoExteriorEndComplex_epi : CategoryTheory.Epi (labelTwoExteriorEndComplex param).g :=
  (ModuleCat.epi_iff_surjective _).mpr (labelTwoExteriorAugmentation_surjective param)

end
end Categorification.Stendhal
