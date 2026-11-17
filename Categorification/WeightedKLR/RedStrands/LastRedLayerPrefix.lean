/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedLayerCyclotomic

/-!
# The tensor algebra on the left of a last-red cut

Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.37. Adjoining a
straight black block to the right respects the relations for the prefix,
including the violated-boundary relation.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)
  {ν θ β : Multiset I}
local notation "ι" => (Sum.inl : I → I ⊕ Fin (ℓ+1))
local notation "M" => stendhalWeight (ℓ+1) ν
local notation "PWeight" => stendhalWeight (ℓ+1) θ
local notation "B" => β.map ι
local notation "S" => stendhalQ Q Λ
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν
local notation "π₀" => StendhalAlgebraAllOrders.ofKLR k Q Λ θ
variable (p : Fin (stendhalWeight (ℓ+1) ν).card)
  (h : stendhalWeight (ℓ+1) θ + β.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) = stendhalWeight (ℓ+1) ν)
local notation "F" => suffixConcat Q Λ p h
local notation "C" => RingCon.Quotient (TwoSidedIdeal.ringCon (smallerSuffixIdeal Q Λ p))
local notation "pr" => lastRedLayerProjection Q Λ p

private def prefixRaw : KLRAlgebra k S PWeight →ₙₐ[k] C where
  toFun x := F (x ⊗ₜ 1)
  map_zero' := by rw [TensorProduct.zero_tmul, map_zero]
  map_add' := fun x y => by rw [TensorProduct.add_tmul, map_add]
  map_mul' := fun x y => by
    rw [← suffixConcat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_smul' := fun c x => by rw [← TensorProduct.smul_tmul', map_smul]; rfl

local notation "G" => prefixRaw Q Λ p h

private theorem prefixRaw_eq_sum (z : KLRAlgebra k S PWeight) :
    G z = ∑ b : Seq B, F (z ⊗ₜ e b) := by
  change F (z ⊗ₜ 1) = _
  rw [← sum_e (Q := S) (ν := B), TensorProduct.tmul_sum, map_sum]

omit [DecidableEq I] in
private theorem castAppend_lbl_left (a : Seq PWeight) (b : Seq B) (j : Fin (Multiset.card PWeight)) :
    (Seq.cast h (a.append b)).lbl (Fin.cast (congrArg Multiset.card h) (Seq.posL B j)) = a.lbl j := by
  change (Seq.cast h _).1 _ = _
  simp

private theorem concat_x_e_left {J : Type*} [DecidableEq J]
    (P : J → J → MvPolynomial (Fin 2) k) {μ η : Multiset J}
    (a : Seq μ) (b : Seq η) (z : Fin μ.card) :
    concat P μ η ((x z * e a) ⊗ₜ e b) = x (Seq.posL η z) * e (a.append b) := by
  simpa [ψw,TypeA.shiftWord,pol_X] using concat_pol_ψw_e (Q := P) (MvPolynomial.X z)
    (1 : MvPolynomial _ k) (α := []) (α' := []) (by simp) (by simp) a b

private theorem concat_cross_e_left {J : Type*} [DecidableEq J]
    (P : J → J → MvPolynomial (Fin 2) k) {μ η : Multiset J}
    (a : Seq μ) (b : Seq η) {j : ℕ} (hj : j+1 < μ.card) :
    concat P μ η ((ψ j * e a) ⊗ₜ e b) = ψ j * e (a.append b) := by
  simpa [ψw,TypeA.shiftWord] using concat_pol_ψw_e (Q := P) (1 : MvPolynomial _ k)
    (1 : MvPolynomial _ k) (α := [j]) (α' := []) (by simp [hj]) (by simp) a b

private theorem prefixRaw_dot (a : Seq PWeight) (j : Fin (Multiset.card PWeight)) (hr : (a.lbl j).isRight) :
    G (x j * e a) = 0 := by
  rw [prefixRaw_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  change pr (π (castKLR S h (concat S PWeight B _))) = 0
  rw [concat_x_e_left, map_mul, castKLR_x, castKLR_e, map_mul]
  exact (congrArg pr (StendhalAlgebraAllOrders.x_mul_e_of_red _ _
    (by rwa [castAppend_lbl_left h a b j]))).trans (map_zero pr)

private theorem prefixRaw_cross (a : Seq PWeight) {j : ℕ} (hj : j+1 < (Multiset.card PWeight))
    (hr : (a.lbl ⟨j,by omega⟩).isRight) (hr' : (a.lbl ⟨j+1,hj⟩).isRight) :
    G (ψ j * e a) = 0 := by
  rw [prefixRaw_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  change pr (π (castKLR S h (concat S PWeight B _))) = 0
  rw [concat_cross_e_left S a b hj, map_mul, castKLR_ψ, castKLR_e, map_mul]
  let z (i : Fin (Multiset.card PWeight)) := Fin.cast (congrArg Multiset.card h) (Seq.posL B i)
  have hj' := (z ⟨j+1,hj⟩).isLt
  change j+1 < (Multiset.card M) at hj'
  exact (congrArg pr (StendhalAlgebraAllOrders.ψ_mul_e_of_red j hj' _
    (by change ((Seq.cast h (a.append b)).lbl (z ⟨j,by omega⟩)).isRight
        rwa [castAppend_lbl_left])
    (by change ((Seq.cast h (a.append b)).lbl (z ⟨j+1,hj⟩)).isRight
        rwa [castAppend_lbl_left]))).trans (map_zero pr)

private theorem prefixRaw_one_idem : IsIdempotentElem (G 1) := by rw [IsIdempotentElem, ← map_mul, one_mul]

private def prefixRawCorner : KLRAlgebra k S PWeight →ₐ[k] (prefixRaw_one_idem Q Λ p h).Corner where
  toFun a := KLR.Corner.mk (G a) (by rw [← map_mul, ← map_mul, one_mul, mul_one])
  map_zero' := Subtype.ext (map_zero G)
  map_add' a b := Subtype.ext (map_add G a b)
  map_mul' a b := Subtype.ext (map_mul G a b)
  map_one' := rfl
  commutes' c := Subtype.ext (by
    change G (algebraMap k _ c) = c • G 1
    rw [← map_smul, Algebra.smul_def, mul_one])

private def prefixAllOrders : StendhalAlgebraAllOrders k Q Λ θ →ₐ[k] (prefixRaw_one_idem Q Λ p h).Corner :=
  RingQuot.liftAlgHom k ⟨(prefixRawCorner Q Λ p h).comp (KLRAlgebra.mk k S PWeight), fun _ _ hr => by
    cases hr with
    | klr hr => exact congrArg (prefixRawCorner Q Λ p h) (RingQuot.mkAlgHom_rel k hr)
    | red_dot j a hr =>
      apply Subtype.ext
      change G (KLRAlgebra.mk k S PWeight _) = G (KLRAlgebra.mk k S PWeight 0)
      rw [map_zero, map_zero, map_mul]
      exact prefixRaw_dot Q Λ p h a j hr
    | red_cross j hj a hr hr' =>
      apply Subtype.ext
      change G (KLRAlgebra.mk k S PWeight _) = G (KLRAlgebra.mk k S PWeight 0)
      rw [map_zero, map_zero, map_mul]
      exact prefixRaw_cross Q Λ p h a hj hr hr'⟩

private theorem prefixAllOrders_ofKLR (a : KLRAlgebra k S PWeight) :
    (prefixAllOrders Q Λ p h (π₀ a)).val = G a := by
  obtain ⟨z,rfl⟩ := KLRAlgebra.mk_surjective a
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  exact congrArg (fun t : (prefixRaw_one_idem Q Λ p h).Corner => t.val)
    (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _)

private def prefixOrdered : StendhalAlgebra k Q Λ θ →ₙₐ[k] C where
  toFun x := (prefixAllOrders Q Λ p h x.val).val
  map_zero' := by change (prefixAllOrders Q Λ p h 0).val = 0; rw [map_zero]; rfl
  map_add' x y := by change (prefixAllOrders Q Λ p h (x.val+y.val)).val = _; rw [map_add]; rfl
  map_mul' x y := by change (prefixAllOrders Q Λ p h (x.val*y.val)).val = _; rw [map_mul]; rfl
  map_smul' c x := by
    obtain ⟨a,ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective x.val
    let f := fun z : StendhalAlgebraAllOrders k Q Λ θ => (prefixAllOrders Q Λ p h z).val
    have hraw (z : KLRAlgebra k S PWeight) : f (π₀ z) = G z := prefixAllOrders_ofKLR Q Λ p h z
    have hv : (c • x).val = c • x.val := rfl
    have hs : (c • x).val = π₀ (c • a) := hv.trans
      ((congrArg (c • ·) ha.symm).trans ((π₀).toLinearMap.map_smul c a).symm)
    change f (c • x).val = c • f x.val
    rw [hs, ← ha, hraw, hraw, map_smul]

private theorem prefixOrdered_e_violated (a : Seq PWeight) (ho : IsRedOrdered a) (hv : IsViolated a) :
    prefixOrdered Q Λ p h (StendhalAlgebra.e a ho) = 0 := by
  change (prefixAllOrders Q Λ p h (π₀ (e a))).val = 0
  rw [prefixAllOrders_ofKLR, prefixRaw_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  let s := Seq.cast h (a.append b)
  obtain ⟨h0,hv⟩ := hv
  let j := Fin.cast (congrArg Multiset.card h) (Seq.posL B (⟨0,h0⟩ : Fin (Multiset.card PWeight)))
  have hv' : IsViolated s := ⟨j.isLt, (castAppend_lbl_left h a b ⟨0,h0⟩) ▸ hv⟩
  change pr (π (castKLR S h (concat S PWeight B _))) = 0
  rw [concat_e_tmul_e, castKLR_e]
  by_cases hs : IsRedOrdered s
  · have he : orderProjection Q Λ ν (π (e s)) = StendhalAlgebra.e s hs :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))
    have hz : TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) = 0 := by
      change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' _ = 0
      rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
      exact TwoSidedIdeal.subset_span ⟨s,hs,hv',rfl⟩
    change (smallerSuffixIdeal Q Λ p).ringCon.mk' ((TensorProductAlgebra.mk Q Λ ν)
      (orderProjection Q Λ ν (π (e s)))) = 0
    rw [he,hz,map_zero]
  · have he : orderProjection Q Λ ν (π (e s)) = 0 :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
    change (smallerSuffixIdeal Q Λ p).ringCon.mk' ((TensorProductAlgebra.mk Q Λ ν)
      (orderProjection Q Λ ν (π (e s)))) = 0
    rw [he,map_zero,map_zero]

/-- Adjoin a straight black block to a prefix in Webster's tensor product algebra. -/
def prefixTensor : TensorProductAlgebra k Q Λ θ →ₙₐ[k] C := by
  let f := prefixOrdered Q Λ p h
  have hk : StendhalAlgebra.violatedIdeal k Q Λ θ ≤ TwoSidedIdeal.ker f := by
    apply TwoSidedIdeal.span_le.2
    rintro _ ⟨s,hs,hv,rfl⟩
    exact (TwoSidedIdeal.mem_ker _).2 (prefixOrdered_e_violated Q Λ p h s hs hv)
  exact {
    toFun := Quotient.lift f (fun _ _ hxy => (TwoSidedIdeal.ringCon_le_iff.mp hk) hxy)
    map_zero' := map_zero f
    map_add' := by rintro ⟨x⟩ ⟨y⟩; exact map_add f x y
    map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact map_mul f x y
    map_smul' := by rintro c ⟨x⟩; exact map_smul f c x }


private theorem prefixRaw_e_unordered (a : Seq PWeight) (ha : ¬ IsRedOrdered a) : G (e a) = 0 := by
  rw [prefixRaw_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  let s := Seq.cast h (a.append b)
  let j (i : Fin (Multiset.card PWeight)) := Fin.cast (congrArg Multiset.card h) (Seq.posL B i)
  have hs : ¬ IsRedOrdered s := by
    intro ho
    apply ha
    intro u v r r' huv hu hv
    exact ho (j u) (j v) r r' huv ((castAppend_lbl_left h a b u).trans hu)
      ((castAppend_lbl_left h a b v).trans hv)
  have he : orderProjection Q Λ ν (π (e s)) = 0 :=
    Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
  change pr (π (castKLR S h (concat S PWeight B _))) = 0
  rw [concat_e_tmul_e, castKLR_e]
  change (smallerSuffixIdeal Q Λ p).ringCon.mk' ((TensorProductAlgebra.mk Q Λ ν)
    (orderProjection Q Λ ν (π (e s)))) = 0
  rw [he,map_zero,map_zero]

private theorem prefixAllOrders_orderedIdem :
    prefixAllOrders Q Λ p h (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ) = 1 := by
  classical
  let U := Finset.univ.filter (IsRedOrdered (μ := PWeight))
  have hs : π₀ (eSum S U) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ := by
    rw [eSum,map_sum]
    rfl
  apply Subtype.ext
  change (prefixAllOrders Q Λ p h (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ)).val = G 1
  rw [← hs, prefixAllOrders_ofKLR, eSum, map_sum, ← sum_e (Q := S) (ν := PWeight), map_sum]
  change (∑ a ∈ Finset.univ.filter IsRedOrdered, G (e a)) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ho
  · rfl
  · exact (prefixRaw_e_unordered Q Λ p h a ho).symm

/-- The prefix action after both red quotients is the original juxtaposition. -/
theorem prefixTensor_projection (x : KLRAlgebra k S PWeight) :
    prefixTensor Q Λ p h (TensorProductAlgebra.mk Q Λ θ (orderProjection Q Λ θ (π₀ x))) =
      F (x ⊗ₜ 1) := by
  change KLR.Corner.val (prefixAllOrders Q Λ p h (π₀ x * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ)) = _
  have H : prefixAllOrders Q Λ p h (π₀ x * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ) =
      prefixAllOrders Q Λ p h (π₀ x) := by
    rw [map_mul, prefixAllOrders_orderedIdem]
    exact mul_one (prefixAllOrders Q Λ p h (π₀ x))
  exact (congrArg (fun t : (prefixRaw_one_idem Q Λ p h).Corner => t.val) H).trans
    (prefixAllOrders_ofKLR Q Λ p h x)

end Categorification.Stendhal
