/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineCoverGrading
import Categorification.WeightedKLR.RedStrands.RepresentationLift
import Categorification.WeightedKLR.RedStrands.TensorProjection

/-!
# The affine presentation for the all-down comparison

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.2, Definitions 4.5–4.7. We express this presentation of `T^λ` using the
affine KLR cover used to formalize Lemma 4.37. For the all-down comparison of
Lemma 4.28, this gives a test for descending a map from the affine generators
to the corner of the double Stendhal algebra.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLR.KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {B : Type*} [Ring B] [Algebra k B]

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "P" => affineCoverQ Q Λ
local notation "S" => stendhalQ Q Λ
local notation "Aff" => KLRAlgebra k P μ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => affineTensorProjection (Q := Q) Λ ν

/-- The ideal of red dots, unordered boundaries and violating boundaries in the
affine cover of Webster's `T^λ` (arXiv:1309.3796v2, §4.2, Definitions 4.5–4.7). -/
def affineTensorIdeal (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (ν : Multiset I) : TwoSidedIdeal (KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν)) :=
  let weight := stendhalWeight ℓ ν
  TwoSidedIdeal.span {z | (∃ (s : Seq weight) (a : Fin weight.card),
      (s.lbl a).isRight ∧ z = x a * e s) ∨
    ∃ s : Seq weight, (¬ IsRedOrdered s ∨ IsViolated s) ∧ z = e s}

private theorem affineRedCross (ρ : Aff →ₐ[k] B)
    (hOrder : ∀ s : Seq μ, ¬ IsRedOrdered s → ρ (e s) = 0)
    (j : ℕ) (hj : j + 1 < m) (s : Seq μ)
    (ha : (s.lbl ⟨j, by omega⟩).isRight) (hb : (s.lbl ⟨j + 1, hj⟩).isRight) :
    ρ (ψ j * e s) = 0 := by
  by_cases ho : IsRedOrdered s
  · let t := TypeA.sadj m j • s
    have ht : ¬ IsRedOrdered t := by
      rcases h₀ : s.lbl ⟨j, by omega⟩ with i | r
      · simp [h₀] at ha
      rcases h₁ : s.lbl ⟨j + 1, hj⟩ with i | r'
      · simp [h₁] at hb
      intro ht
      have hlt : (⟨j, by omega⟩ : Fin m) < ⟨j + 1, hj⟩ := Fin.mk_lt_mk.2 (by omega)
      have hr : r < r' := ho _ _ _ _ hlt h₀ h₁
      exact hr.not_gt (ht _ _ _ _ hlt ((lbl_sadj_left hj s).trans h₁)
        ((lbl_sadj_right hj s).trans h₀))
    rw [ψ_mul_e, map_mul, hOrder t ht, zero_mul]
  · rw [map_mul, hOrder s ho, mul_zero]

private def fromStendhalKLR (ρ : Aff →ₐ[k] B)
    (hOrder : ∀ s : Seq μ, ¬ IsRedOrdered s → ρ (e s) = 0) :
    KLRAlgebra k S μ →ₐ[k] B := by
  let f := ρ.comp (mk k P μ)
  refine RingQuot.liftAlgHom k ⟨f, ?_⟩
  intro a b h
  have hf : ∀ {u v}, KLR.Rel k P μ u v → f u = f v := fun hr => congrArg ρ (rel hr)
  cases h with
  | idem_mul s t => exact hf (.idem_mul s t)
  | idem_sum => exact hf .idem_sum
  | dot_idem a s => exact hf (.dot_idem a s)
  | cross_idem j s => exact hf (.cross_idem j s)
  | cross_zero j hj => exact hf (.cross_zero j hj)
  | dot_dot a b => exact hf (.dot_dot a b)
  | cross_cross j t h => exact hf (.cross_cross j t h)
  | dot_cross a j ha hb => exact hf (.dot_cross a j ha hb)
  | dot_cross_left j hj s => exact hf (.dot_cross_left j hj s)
  | dot_cross_right j hj s => exact hf (.dot_cross_right j hj s)
  | cross_sq j hj s =>
    by_cases he : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, hj⟩
    · exact (hf (.cross_sq j hj s)).trans (by rw [ite_eq_left he, ite_eq_left he])
    simp only [ite_eq_right he]
    have hs := hf (.cross_sq j hj s)
    rw [ite_eq_right he] at hs
    cases ha : s.lbl ⟨j, by omega⟩ with
    | inl i =>
      cases hb : s.lbl ⟨j + 1, hj⟩ <;> simpa only [ha, hb, affineCoverQ] using hs
    | inr r =>
      cases hb : s.lbl ⟨j + 1, hj⟩ with
      | inl i => simpa only [ha, hb, affineCoverQ] using hs
      | inr t =>
        have hcross : f (fψ k μ j * fe k μ s) = 0 := by
          change ρ (mk k P μ (_ * _)) = 0
          rw [map_mul]
          exact affineRedCross ρ hOrder j hj s (by simp [ha]) (by simp [hb])
        rw [mul_assoc, map_mul, hcross, mul_zero]
        simp [stendhalQ, ncEval]
  | braid j hj s =>
    refine (hf (.braid j hj s)).trans ?_
    split_ifs with he
    · by_cases ho : IsRedOrdered s
      · cases ha : s.lbl ⟨j, by omega⟩ with
        | inl i => rfl
        | inr r =>
          exact (lt_irrefl r (ho _ _ r r (Fin.mk_lt_mk.2 (by omega)) ha
            (he.1.symm.trans ha))).elim
      · have hz : f (fe k μ s) = 0 := hOrder s ho
        simp only [map_mul, hz, mul_zero]
    · rfl

private theorem fromStendhalKLR_mk (ρ : Aff →ₐ[k] B)
    (hOrder : ∀ s : Seq μ, ¬ IsRedOrdered s → ρ (e s) = 0) (a : FreeAlgebra k (Gen μ)) :
    fromStendhalKLR ρ hOrder (mk k S μ a) = ρ (mk k P μ a) :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

private theorem fromStendhalKLR_relations (ρ : Aff →ₐ[k] B)
    (h : affineTensorIdeal Q Λ ν ≤ TwoSidedIdeal.ker ρ.toRingHom)
    (hOrder : ∀ s : Seq μ, ¬ IsRedOrdered s → ρ (e s) = 0) :
    TensorRepresentationRelations (fromStendhalKLR ρ hOrder) where
  red_dot a s ha := by
    rw [x, e, ← map_mul, fromStendhalKLR_mk, map_mul]
    exact (TwoSidedIdeal.mem_ker ρ.toRingHom).mp
      (h (TwoSidedIdeal.subset_span (Or.inl ⟨s, a, ha, rfl⟩)))
  red_cross j hj s ha hb := by
    rw [ψ, e, ← map_mul, fromStendhalKLR_mk, map_mul]
    exact affineRedCross ρ hOrder j hj s ha hb
  unordered s hs := by
    rw [e, fromStendhalKLR_mk]
    exact hOrder s hs
  violated s _ hs := by
    rw [e, fromStendhalKLR_mk]
    exact (TwoSidedIdeal.mem_ker ρ.toRingHom).mp
      (h (TwoSidedIdeal.subset_span (Or.inr ⟨s, Or.inr hs, rfl⟩)))

private theorem order_of_ideal (ρ : Aff →ₐ[k] B)
    (h : affineTensorIdeal Q Λ ν ≤ TwoSidedIdeal.ker ρ.toRingHom)
    (s : Seq μ) (hs : ¬ IsRedOrdered s) : ρ (e s) = 0 :=
  (TwoSidedIdeal.mem_ker ρ.toRingHom).mp
    (h (TwoSidedIdeal.subset_span (Or.inr ⟨s, Or.inl hs, rfl⟩)))

/-- Descend a map from the ordinary affine KLR generators to Webster's
`T^λ` (arXiv:1309.3796v2, §4.2, Definitions 4.5–4.7). -/
def affineTensorLift (ρ : Aff →ₐ[k] B)
    (h : affineTensorIdeal Q Λ ν ≤ TwoSidedIdeal.ker ρ.toRingHom) : T →ₐ[k] B :=
  tensorRepresentationLift _ (fromStendhalKLR_relations ρ h (order_of_ideal ρ h))

/-- Precomposing the descended map with the affine projection recovers the
given map. -/
theorem affineTensorLift_comp (ρ : Aff →ₐ[k] B)
    (h : affineTensorIdeal Q Λ ν ≤ TwoSidedIdeal.ker ρ.toRingHom) :
    (affineTensorLift ρ h).comp π = ρ := by
  ext z
  obtain ⟨a, rfl⟩ := mk_surjective z
  have he : affineCover Q Λ ν (mk k P μ a) =
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν (mk k S μ a) := by
    rw [StendhalAlgebraAllOrders.ofKLR_mk]
    exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
  simp only [AlgHom.comp_apply, affineTensorProjection, he]
  exact (DFunLike.congr_fun (tensorRepresentationLift_comp _
    (fromStendhalKLR_relations ρ h (order_of_ideal ρ h))) _).trans
      (fromStendhalKLR_mk ρ _ _)

/-- The kernel of the affine cover of `T^λ` is generated by red dots and the
idempotents of unordered or violating boundaries (Webster, arXiv:1309.3796v2,
§4.2, Definitions 4.5–4.7). -/
theorem ker_affineTensorProjection : TwoSidedIdeal.ker (π).toRingHom = affineTensorIdeal Q Λ ν := by
  apply le_antisymm
  · let J := affineTensorIdeal Q Λ ν
    let q := J.ringCon.mkₐ k
    have hq : J ≤ TwoSidedIdeal.ker q.toRingHom := by
      change J ≤ TwoSidedIdeal.ker J.ringCon.mk'
      rw [TwoSidedIdeal.ker_ringCon_mk']
    intro z hz
    have hz' : π z = 0 := (TwoSidedIdeal.mem_ker (π).toRingHom).mp hz
    have he := DFunLike.congr_fun (affineTensorLift_comp q hq) z
    rw [AlgHom.comp_apply, hz', map_zero] at he
    have hqz : z ∈ TwoSidedIdeal.ker J.ringCon.mk' :=
      (TwoSidedIdeal.mem_ker J.ringCon.mk').mpr he.symm
    rwa [TwoSidedIdeal.ker_ringCon_mk'] at hqz
  · apply TwoSidedIdeal.span_le.mpr
    have hRel := tensorRepresentationRelations_projection (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    rintro z (⟨s, a, ha, rfl⟩ | ⟨s, hs, rfl⟩)
    · apply (TwoSidedIdeal.mem_ker (π).toRingHom).mpr
      change TensorProductAlgebra.mk Q Λ ν
        (orderProjection Q Λ ν (affineCover Q Λ ν (x a * e s))) = 0
      simpa only [AlgHom.comp_apply, map_mul, affineCover_x, affineCover_e,
        StendhalAlgebraAllOrders.x, StendhalAlgebraAllOrders.e] using hRel.red_dot a s ha
    · apply (TwoSidedIdeal.mem_ker (π).toRingHom).mpr
      change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν (e s))) = 0
      rw [affineCover_e]
      by_cases ho : IsRedOrdered s
      · exact hRel.violated s ho (hs.resolve_left (not_not_intro ho))
      · exact hRel.unordered s ho

end Categorification.Stendhal
