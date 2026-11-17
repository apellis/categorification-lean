/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Categorification.WeightedKLR.RedStrands.StendhalGrading

/-!
# Homogeneous lifts of tensor product diagrams

Webster, arXiv:1309.3796v2, Definitions 4.4–4.7. The augmented KLR
projection onto the ordered violating quotient preserves degrees and
surjects onto each homogeneous component.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {m : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (wts : Fin m → I →₀ ℕ)
    (G₀ : GradingDatum (stendhalQ Q wts)) (ν₀ : Multiset I)

/-- The augmented KLR projection onto the ordered violating quotient. -/
abbrev stendhalTensorProjection :=
  (TensorProductAlgebra.mk Q wts ν₀).comp ((orderProjection Q wts ν₀).comp (StendhalAlgebraAllOrders.ofKLR k Q wts ν₀))

/-- At an ordered loading, affine projection gives its tensor-algebra idempotent. -/
theorem stendhalTensorProjection_e (s : Seq (stendhalWeight m ν₀)) (ho : IsRedOrdered s) :
    stendhalTensorProjection (Q := Q) wts ν₀ (e s) =
      TensorProductAlgebra.mk Q wts ν₀ (StendhalAlgebra.e s ho) :=
  congrArg (TensorProductAlgebra.mk Q wts ν₀) (Subtype.ext
    ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left ho)))

/-- Every homogeneous tensor-algebra element has a homogeneous affine lift. -/
theorem stendhalTensorProjection_grade_lift {d : ℤ} {z} (hz : z ∈ tensorProductGrade G₀ ν₀ d) :
    ∃ a ∈ G₀.grade (stendhalWeight m ν₀) d, stendhalTensorProjection (Q := Q) wts ν₀ a=z := by
  obtain ⟨t,ht,rfl⟩ := Submodule.mem_map.mp hz
  obtain ⟨a,ha,h⟩ := Submodule.mem_map.mp (show t.1 ∈ allOrdersGrade G₀ ν₀ d from ht)
  refine ⟨a,ha,congrArg (TensorProductAlgebra.mk Q wts ν₀) (Subtype.ext ?_)⟩
  change StendhalAlgebraAllOrders.ofKLR k Q wts ν₀ a * StendhalAlgebraAllOrders.redOrderedIdem k Q wts ν₀ = t.1
  rw [show StendhalAlgebraAllOrders.ofKLR k Q wts ν₀ a = t.1 from h]
  exact ((Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp t.2).2

/-- Projection of a homogeneous affine diagram has its original degree. -/
theorem stendhalTensorProjection_mem_grade {d : ℤ} {x}
    (hx : x ∈ G₀.grade (stendhalWeight m ν₀) d) :
    stendhalTensorProjection (Q := Q) wts ν₀ x ∈ tensorProductGrade G₀ ν₀ d := by
  apply Graded.mem_map_of_mem
  change StendhalAlgebraAllOrders.ofKLR k Q wts ν₀ x * StendhalAlgebraAllOrders.redOrderedIdem k Q wts ν₀ ∈ allOrdersGrade G₀ ν₀ d
  have ha := Graded.mem_map_of_mem _ (StendhalAlgebraAllOrders.ofKLR k Q wts ν₀).toLinearMap hx
  have hE : StendhalAlgebraAllOrders.redOrderedIdem k Q wts ν₀ ∈ allOrdersGrade G₀ ν₀ 0 :=
    Submodule.sum_mem _ fun i _ => Graded.mem_map_of_mem _ _ (G₀.e_mem_grade i)
  simpa using SetLike.mul_mem_graded (A := allOrdersGrade G₀ ν₀) ha hE

end Categorification.Stendhal
