/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.WeightedKLR.GradedK0.Grading
import Categorification.Algebra.Graded.QuotientAlgebra
import Categorification.KLR.Grading

/-!
# The grading of the tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Definitions 4.4–4.7. Extend the KLR grading on black strands by giving a crossing with
the red strand of weight `λ_r` degree `d_i λ_r^i` in both directions. The relations
killing red dots and red/red crossings are homogeneous. The corner at red-ordered
sequences and the quotient by violated idempotents therefore inherit the diagram grading.

Webster fixes a field in §4.1. The descent works over any commutative coefficient ring.
-/

namespace Categorification.Stendhal

open KLR MvPolynomial
open StendhalAlgebraAllOrders

variable {I k : Type*} [CommRing k] {ℓ : ℕ} {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ)

/-- Webster's degrees of Definition 4.4 on the augmented colours. For the ambient KLR algebra the red dots have auxiliary
degree two and red/red crossings degree minus two. Both vanish in the diagram algebra. -/
def stendhalGradingDatum (G : KLR.GradingDatum Q) (d : I → ℤ)
    (hd : ∀ i, G.degX i = 2 * d i) : KLR.GradingDatum (stendhalQ Q Λ) where
  degX := Sum.elim G.degX (fun _ => 2)
  degΨ
    | .inl i, .inl j => G.degΨ i j
    | .inl i, .inr r | .inr r, .inl i => d i * Λ r i
    | .inr _, .inr _ => -2
  degΨ_self := by rintro (i | r); exact G.degΨ_self i; simp
  isWeightedHomogeneous := by
    rintro (i | r) (j | s) h
    · exact G.isWeightedHomogeneous i j (fun hij => h (congrArg Sum.inl hij))
    · change (X 0 ^ Λ s i : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![G.degX i, 2]
        (d i * Λ s i + d i * Λ s i)
      have hdeg : d i * Λ s i + d i * Λ s i = Λ s i • G.degX i := by
        rw [hd, nsmul_eq_mul]; ring
      rw [hdeg]
      exact (isWeightedHomogeneous_X k ![G.degX i, (2 : ℤ)] (0 : Fin 2)).pow (Λ s i)
    · change (X 1 ^ Λ r j : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![2, G.degX j]
        (d j * Λ r j + d j * Λ r j)
      have hdeg : d j * Λ r j + d j * Λ r j = Λ r j • G.degX j := by
        rw [hd, nsmul_eq_mul]; ring
      rw [hdeg]
      exact (isWeightedHomogeneous_X k ![(2 : ℤ), G.degX j] (1 : Fin 2)).pow (Λ r j)
    · exact isWeightedHomogeneous_zero k _ _

variable [DecidableEq I] {Λ} (G : KLR.GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "π" => ofKLR k Q Λ ν

/-- The grading of all red orders by images of homogeneous KLR diagrams. -/
noncomputable def allOrdersGrade : ℤ → Submodule k (StendhalAlgebraAllOrders k Q Λ ν) :=
  Graded.map (G.grade μ) (π).toLinearMap

private noncomputable def allOrdersCoaction :
    StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] AddMonoidAlgebra (StendhalAlgebraAllOrders k Q Λ ν) ℤ :=
  let f := (AddMonoidAlgebra.mapAlgHom ℤ π).comp G.coaction
  RingQuot.liftAlgHom k ⟨f.comp (KLRAlgebra.mk k _ μ), by
    intro a b hab
    cases hab with
    | klr h => exact congrArg f (RingQuot.mkAlgHom_rel k h)
    | red_dot a i h =>
      change AddMonoidAlgebra.mapAlgHom ℤ π (G.coaction (KLRAlgebra.mk k _ μ _)) = _
      rw [map_mul]
      change AddMonoidAlgebra.mapAlgHom ℤ π (G.coaction (KLRAlgebra.x a * KLRAlgebra.e i)) = _
      rw [G.mem_grade.mp (G.x_mul_e_mem_grade a i), AddMonoidAlgebra.mapAlgHom_single, map_mul]
      change AddMonoidAlgebra.single _ (x a * e i) = _
      rw [x_mul_e_of_red a i h, AddMonoidAlgebra.single_zero, map_zero]
    | red_cross j h i h₁ h₂ =>
      change AddMonoidAlgebra.mapAlgHom ℤ π (G.coaction (KLRAlgebra.mk k _ μ _)) = _
      rw [map_mul]
      change AddMonoidAlgebra.mapAlgHom ℤ π (G.coaction (KLRAlgebra.ψ j * KLRAlgebra.e i)) = _
      rw [G.mem_grade.mp (G.ψ_mul_e_mem_grade' j i), AddMonoidAlgebra.mapAlgHom_single, map_mul]
      change AddMonoidAlgebra.single _ (ψ j * e i) = _
      rw [ψ_mul_e_of_red j h i h₁ h₂, AddMonoidAlgebra.single_zero, map_zero]⟩

private theorem allOrdersCoaction_ofKLR (x : KLRAlgebra k (stendhalQ Q Λ) μ) :
    allOrdersCoaction G ν (π x) = AddMonoidAlgebra.mapAlgHom ℤ π (G.coaction x) := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective x
  rw [ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

noncomputable instance : GradedAlgebra (allOrdersGrade G ν) :=
  Graded.mapGradedAlgebra (G.grade μ) π ofKLR_surjective fun x hx n => by
    have h := congrArg (fun a => (allOrdersCoaction G ν a).coeff n) hx
    rw [G.decompose_apply]
    simpa only [allOrdersCoaction_ofKLR, AddMonoidAlgebra.coeff_mapAlgHom, map_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h

/-- The grading of the algebra of red-ordered Stendhal diagrams (Definitions 4.4–4.5, 4.7). -/
noncomputable def stendhalGrade : ℤ → Submodule k (StendhalAlgebra k Q Λ ν) :=
  Graded.cornerGrading (allOrdersGrade G ν) isIdempotentElem_redOrderedIdem

noncomputable instance : GradedAlgebra (stendhalGrade G ν) :=
  Graded.cornerGradedAlgebra _ _ <| Submodule.sum_mem _ fun i _ =>
    Graded.mem_map_of_mem _ (π).toLinearMap (G.e_mem_grade i)

/-- Every red-ordered idempotent has degree zero. -/
theorem e_mem_stendhalGrade (i : Seq μ) (hi : IsRedOrdered i) :
    StendhalAlgebra.e i hi ∈ stendhalGrade G ν 0 :=
  Graded.mem_map_of_mem _ (π).toLinearMap (G.e_mem_grade i)

/-- The quotient grading on the tensor product algebra (Definitions 4.4, 4.6–4.7). -/
noncomputable def tensorProductGrade : ℤ → Submodule k (TensorProductAlgebra k Q Λ ν) :=
  Graded.map (stendhalGrade G ν) (TensorProductAlgebra.mk Q Λ ν).toLinearMap

private theorem tensorProduct_mk_eq_zero (x : StendhalAlgebra k Q Λ ν) :
    TensorProductAlgebra.mk Q Λ ν x = 0 ↔ x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν := by
  change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' x = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

/-- The violated ideal is homogeneous, so `T^λ` is a graded algebra with the diagram degrees. -/
noncomputable instance tensorProductGradedAlgebra : GradedAlgebra (tensorProductGrade G ν) :=
  Graded.mapGradedAlgebra _ _ (RingCon.mkₐ_surjective _) fun x hx n =>
    (tensorProduct_mk_eq_zero ν _).2 <| by
      have h := (tensorProduct_mk_eq_zero ν x).1 hx
      unfold StendhalAlgebra.violatedIdeal at h ⊢
      apply Graded.decompose_mem_twoSidedSpan (stendhalGrade G ν) _ h n
      rintro _ ⟨i, hi, _, rfl⟩
      exact ⟨0, e_mem_stendhalGrade G ν i hi⟩

/-- The projected idempotent belongs to degree zero in the violating quotient. -/
theorem mk_e_mem_tensorProductGrade (i : Seq μ) (hi : IsRedOrdered i) :
    TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e i hi) ∈ tensorProductGrade G ν 0 :=
  Graded.mem_map_of_mem _ _ (e_mem_stendhalGrade G ν i hi)

end Categorification.Stendhal
