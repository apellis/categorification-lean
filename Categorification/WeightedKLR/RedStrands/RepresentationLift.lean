/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderProjection

/-!
# Descent of representations to the tensor product algebra

Webster, arXiv:1309.3796v2, Definitions 4.5–4.7. An affine representation
satisfying the two red relations, supported on the prescribed order, and
annihilating violating boundaries factors through the tensor product algebra.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {B : Type*} [Ring B] [Algebra k B]
local notation "μ" => stendhalWeight ℓ ν
local notation "S" => stendhalQ Q Λ
local notation "A" => KLRAlgebra k S μ
local notation "All" => StendhalAlgebraAllOrders k Q Λ ν
local notation "Ord" => StendhalAlgebra k Q Λ ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν
local notation "E" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
local notation "pr" => orderProjection Q Λ ν
local notation "τ" => TensorProductAlgebra.mk Q Λ ν

/-- The affine generators that must vanish in a representation of Webster's
tensor product algebra, Definitions 4.5–4.7. -/
structure TensorRepresentationRelations (ρ : A →ₐ[k] B) : Prop where
  red_dot : ∀ (a : Fin (Multiset.card μ)) (s : Seq μ), (s.lbl a).isRight →
    ρ (KLRAlgebra.x a * KLRAlgebra.e s) = 0
  red_cross : ∀ (j : ℕ) (hj : j+1 < Multiset.card μ) (s : Seq μ),
    (s.lbl ⟨j,by omega⟩).isRight → (s.lbl ⟨j+1,hj⟩).isRight →
    ρ (KLRAlgebra.ψ j * KLRAlgebra.e s) = 0
  unordered : ∀ s : Seq μ, ¬ IsRedOrdered s → ρ (KLRAlgebra.e s) = 0
  violated : ∀ s : Seq μ, IsRedOrdered s → IsViolated s → ρ (KLRAlgebra.e s) = 0

/-- The canonical tensor product quotient satisfies the presentation. -/
theorem tensorRepresentationRelations_projection :
    TensorRepresentationRelations ((τ).comp ((pr).comp (π))) where
  red_dot a s ha := by
    change (τ) ((pr) ((π) (_ * _))) = 0
    rw [map_mul (π)]
    exact (congrArg (fun z => (τ) ((pr) z)) (StendhalAlgebraAllOrders.x_mul_e_of_red a s ha)).trans
      (by rw [map_zero,map_zero])
  red_cross j hj s ha hb := by
    change (τ) ((pr) ((π) (_ * _))) = 0
    rw [map_mul (π)]
    exact (congrArg (fun z => (τ) ((pr) z)) (StendhalAlgebraAllOrders.ψ_mul_e_of_red j hj s ha hb)).trans
      (by rw [map_zero,map_zero])
  unordered s hs := by
    have he : (pr) (StendhalAlgebraAllOrders.e s) = 0 := Subtype.ext
      ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
    exact (congrArg (τ) he).trans (map_zero _)
  violated s ho hv := by
    let J := StendhalAlgebra.violatedIdeal k Q Λ ν
    change J.ringCon.mk' ((pr) (StendhalAlgebraAllOrders.e s)) = 0
    rw [← TwoSidedIdeal.mem_ker,TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨s,ho,hv,Subtype.ext
      ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left ho))⟩

variable (ρ : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₐ[k] B) (h : TensorRepresentationRelations ρ)

private def relationLiftAll : All →ₐ[k] B :=
  RingQuot.liftAlgHom k ⟨ρ.comp (KLRAlgebra.mk k S μ), fun _ _ hr => by
    cases hr with
    | klr hr => exact congrArg ρ (RingQuot.mkAlgHom_rel k hr)
    | red_dot a s ha =>
      simpa only [AlgHom.comp_apply,map_mul,map_zero] using
        (show ρ (KLRAlgebra.mk k S μ (fx k μ a) * KLRAlgebra.mk k S μ (fe k μ s)) = 0 from
          h.red_dot a s ha)
    | red_cross j hj s ha hb =>
      simpa only [AlgHom.comp_apply,map_mul,map_zero] using
        (show ρ (KLRAlgebra.mk k S μ (fψ k μ j) * KLRAlgebra.mk k S μ (fe k μ s)) = 0 from
          h.red_cross j hj s ha hb)⟩

private theorem relationLiftAll_apply (z : A) : relationLiftAll ρ h (π z) = ρ z := by
  obtain ⟨a,rfl⟩ := KLRAlgebra.mk_surjective z
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

private theorem relationLiftAll_order : relationLiftAll ρ h E = 1 := by
  classical
  have total := congrArg ρ (KLRAlgebra.sum_e (k := k) (Q := S) (ν := μ))
  rw [map_sum,map_one] at total
  rw [StendhalAlgebraAllOrders.redOrderedIdem,map_sum,← total]
  simp only [StendhalAlgebraAllOrders.e,relationLiftAll_apply]
  exact Finset.sum_subset (Finset.filter_subset _ _) (fun s _ hs => h.unordered s (by simpa using hs))

private def relationLiftOrdered : Ord →ₐ[k] B where
  toFun z := relationLiftAll ρ h z.val
  map_zero' := map_zero _
  map_one' := relationLiftAll_order ρ h
  map_add' _ _ := map_add _ _ _
  map_mul' _ _ := map_mul _ _ _
  commutes' c := by
    change relationLiftAll ρ h (c • E) = _
    rw [map_smul,relationLiftAll_order,Algebra.smul_def,mul_one]

/-- The homomorphism descending an affine representation through the ordered
Stendhal quotient and the violating ideal (Webster, Definitions 4.5–4.7). -/
def tensorRepresentationLift : T →ₐ[k] B :=
  (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.liftₐ (relationLiftOrdered ρ h) (by
    apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker (relationLiftOrdered ρ h).toRingHom)).mp
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨s,ho,hv,rfl⟩
    apply (TwoSidedIdeal.mem_ker _).mpr
    change relationLiftAll ρ h (π (KLRAlgebra.e s)) = 0
    exact (relationLiftAll_apply ρ h _).trans (h.violated s ho hv))

/-- Pulling the descended representation back to the affine algebra recovers
the given action on every element. -/
theorem tensorRepresentationLift_comp :
    (tensorRepresentationLift ρ h).comp ((τ).comp ((pr).comp (π))) = ρ := by
  apply AlgHom.ext
  intro z
  change relationLiftAll ρ h ((π) z * E) = ρ z
  rw [map_mul,relationLiftAll_order,mul_one,relationLiftAll_apply]

end Categorification.Stendhal
