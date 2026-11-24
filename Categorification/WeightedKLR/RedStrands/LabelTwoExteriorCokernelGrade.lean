/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorDegrees
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorCokernelSimple

/-!
# Graded simple augmentation of the label-two exterior sequence

The homogeneous outgoing image induces a grading on its actual simple
cokernel. The normalized augmentation has degree zero and completes the
exact sequence of the three explicitly graded diagrammatic terms.
-/

namespace Categorification.Stendhal.LabelTwo

open Categorification.Graded DirectSum
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "𝒜" => middleTensorGrade k (labelTwoGradingDatum k)
local notation "T" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "Q" => lIdeal (labelTwoLeftExteriorProjector (parameter k))
private abbrev projector : A := labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal (projector k)
local notation "out" => labelTwoMiddleExteriorDifferential (parameter k)
private abbrev rawImage : Submodule T Q := LinearMap.range out
private abbrev image : Submodule A P := rawImage k
private abbrev Augmentation := P ⧸ image k
local notation "L" => Augmentation k
private abbrev aug : P →ₗ[A] L := (image k).mkQ
local notation "𝓠" => labelTwoMiddleQuotientGrade k
local notation "𝓟" => labelTwoLeftExteriorGrade k

/-- The grading on the simple augmentation is the quotient grading of the exterior projective. -/
def labelTwoExteriorCokernelGrade : ℤ → Submodule k L :=
  Graded.map 𝓟 ((aug k).restrictScalars k)

private theorem outgoing_range_eq :
    LinearMap.range (normalizedOutgoing k) = image k := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(exteriorMiddleQuotientEquiv k).symm v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨exteriorMiddleQuotientEquiv k v,
      congrArg out ((exteriorMiddleQuotientEquiv k).symm_apply_apply v)⟩

local instance : Decomposition 𝓟 := labelTwoLeftExteriorDecomposition k
local instance : Decomposition 𝓠 := labelTwoMiddleQuotientDecomposition k

private theorem image_isHomogeneous :
    (image k).IsHomogeneous 𝓟 := by
  rw [← outgoing_range_eq k]
  apply Graded.isHomogeneous_range (ℳ := Graded.shift 𝓠 2)
  intro i x hx
  change x ∈ 𝓠 (i - 2) at hx
  simpa only [sub_add_cancel] using (mem_homGrade.mp (labelTwoOutgoing_degree_two k) hx)

/-- The exterior augmentation has a genuine grading because the outgoing image is homogeneous. -/
@[instance_reducible] def labelTwoExteriorCokernelDecomposition :
    Decomposition (labelTwoExteriorCokernelGrade k) := by
  apply Graded.mapDecomposition (π := (aug k).restrictScalars k)
    (image k).mkQ_surjective
  intro x hx i
  change aug k x = 0 at hx
  change aug k _ = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (image_isHomogeneous k i ((Submodule.Quotient.mk_eq_zero _).mp hx))

instance labelTwoExteriorCokernel_gradedSMul :
    SetLike.GradedSMul 𝒜 (labelTwoExteriorCokernelGrade k) := by
  let : SetLike.GradedSMul 𝒜 𝓟 :=
    inferInstanceAs (SetLike.GradedSMul 𝒜 (Graded.submodule 𝒜 P))
  exact Graded.gradedSMul_map 𝒜 (fun a x => (aug k).map_smul a x)

/-- The exterior augmentation preserves the inherited degree on each quotient vector. -/
theorem labelTwoExteriorAugmentation_preservesGrading :
    PreservesGrading 𝓟 (labelTwoExteriorCokernelGrade k) (aug k) :=
  fun _ _ hx => Submodule.mem_map_of_mem hx

/-- The normalized outgoing map is exact at the complementary exterior projective. -/
theorem labelTwoNormalizedAugmentation_exact :
    Function.Exact (normalizedOutgoing k) (aug k) := by
  apply LinearMap.exact_iff.mpr
  exact (Submodule.ker_mkQ _).trans (outgoing_range_eq k).symm

/-- The augmentation preserves degree on the normalized exterior and simple gradings. -/
theorem labelTwoShiftedAugmentation_preservesGrading :
    PreservesGrading (Graded.shift 𝓟 (-1))
      (Graded.shift (labelTwoExteriorCokernelGrade k) (-1)) (aug k) :=
  fun _ _ hx => labelTwoExteriorAugmentation_preservesGrading k hx

/-- The shifted augmentation map remains surjective. -/
theorem labelTwoNormalizedAugmentation_surjective : Function.Surjective (aug k) :=
  (image k).mkQ_surjective

/-- The actual graded augmentation has simple underlying module. -/
theorem labelTwoGradedAugmentation_simple :
    CategoryTheory.Simple (ModuleCat.of A L) :=
  labelTwoExteriorCokernel_simple (parameter k)

end
end Categorification.Stendhal.LabelTwo
