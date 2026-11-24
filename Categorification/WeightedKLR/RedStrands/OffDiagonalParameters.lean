/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedRelabel

noncomputable section
namespace Categorification.KLR

variable {I k : Type*} [CommRing k] [DecidableEq I]
  {Q Q' : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

/-- The defining KLR relations depend only on the off-diagonal parameters. -/
theorem rel_of_offDiagonal (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    {a b : FreeAlgebra k (Gen ν)} (h : Rel k Q ν a b) : Rel k Q' ν a b := by
  cases h with
  | cross_sq j hj i =>
    have h' := Rel.cross_sq (k := k) (Q := Q') (ν := ν) j hj i
    split_ifs with h
    · simpa only [ite_eq_left h] using h'
    · simpa only [ite_eq_right h, ← hQ _ _ h] using h'
  | braid j hj i =>
    have h' := Rel.braid (k := k) (Q := Q') (ν := ν) j hj i
    split_ifs with h
    · simpa only [ite_eq_left h, ← hQ _ _ h.2] using h'
    · simpa only [ite_eq_right h] using h'
  | _ => constructor <;> assumption

theorem rel_eq_of_offDiagonal (hQ : ∀ i j, i ≠ j → Q i j = Q' i j) :
    Rel k Q ν = Rel k Q' ν := by
  funext a b
  exact propext ⟨rel_of_offDiagonal hQ, rel_of_offDiagonal fun i j hij => (hQ i j hij).symm⟩

end Categorification.KLR

namespace Categorification.Stendhal

variable {I k : Type*} [CommRing k] [DecidableEq I] {ℓ : ℕ}
  {Q Q' : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

omit [DecidableEq I] in
theorem stendhalQ_eq_offDiagonal (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    (x y : I ⊕ Fin ℓ) (hxy : x ≠ y) : stendhalQ Q Λ x y = stendhalQ Q' Λ x y := by
  cases x with
  | inl i =>
    cases y with
    | inl j => exact hQ i j (fun h => hxy (congrArg Sum.inl h))
    | inr => rfl
  | inr =>
    cases y <;> rfl

theorem rel_of_offDiagonal (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    {a b : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν))} (h : Rel k Q Λ ν a b) :
    Rel k Q' Λ ν a b := by
  cases h with
  | klr h => exact .klr (KLR.rel_of_offDiagonal (stendhalQ_eq_offDiagonal hQ) h)
  | red_dot a i h => exact Rel.red_dot a i h
  | red_cross j hj i h₁ h₂ => exact Rel.red_cross j hj i h₁ h₂

theorem rel_eq_of_offDiagonal (hQ : ∀ i j, i ≠ j → Q i j = Q' i j) :
    Rel k Q Λ ν = Rel k Q' Λ ν := by
  funext a b
  exact propext ⟨rel_of_offDiagonal hQ, rel_of_offDiagonal fun i j hij => (hQ i j hij).symm⟩


private def ringQuotAlgEquivOfRelEq {R : Type*} [Ring R] [Algebra k R]
    {r s : R → R → Prop} (h : r = s) : RingQuot r ≃ₐ[k] RingQuot s := by
  subst s
  exact AlgEquiv.refl

private theorem ringQuotAlgEquivOfRelEq_mk {R : Type*} [Ring R] [Algebra k R]
    {r s : R → R → Prop} (h : r = s) (x : R) :
    ringQuotAlgEquivOfRelEq (k := k) h (RingQuot.mkAlgHom k r x) =
      RingQuot.mkAlgHom k s x := by
  subst s
  rfl

/-- Changing only the diagonal polynomials fixes all Stendhal generators. -/
def stendhalAllOrdersOffDiagonalEquiv (hQ : ∀ i j, i ≠ j → Q i j = Q' i j) :
    StendhalAlgebraAllOrders k Q Λ ν ≃ₐ[k] StendhalAlgebraAllOrders k Q' Λ ν :=
  ringQuotAlgEquivOfRelEq (rel_eq_of_offDiagonal hQ)

theorem stendhalAllOrdersOffDiagonalEquiv_mk (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    (x : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν))) :
    stendhalAllOrdersOffDiagonalEquiv (Λ := Λ) hQ
      (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLR.KLRAlgebra.mk k _ _ x)) =
        StendhalAlgebraAllOrders.ofKLR k Q' Λ ν (KLR.KLRAlgebra.mk k _ _ x) := by
  rw [StendhalAlgebraAllOrders.ofKLR_mk, StendhalAlgebraAllOrders.ofKLR_mk]
  exact ringQuotAlgEquivOfRelEq_mk _ _

theorem stendhalAllOrdersOffDiagonalEquiv_e (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    (i : KLR.Seq (stendhalWeight ℓ ν)) :
    stendhalAllOrdersOffDiagonalEquiv (Λ := Λ) hQ
      (StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ) i) =
        StendhalAlgebraAllOrders.e (k := k) (Q := Q') (Λ := Λ) i :=
  stendhalAllOrdersOffDiagonalEquiv_mk hQ (KLR.fe k _ i)

theorem stendhalAllOrdersOffDiagonalEquiv_redOrderedIdem (hQ : ∀ i j, i ≠ j → Q i j = Q' i j) :
    stendhalAllOrdersOffDiagonalEquiv (Λ := Λ) hQ
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) =
        StendhalAlgebraAllOrders.redOrderedIdem k Q' Λ ν := by
  classical
  simp only [StendhalAlgebraAllOrders.redOrderedIdem, map_sum,
    stendhalAllOrdersOffDiagonalEquiv_e]

/-- The isomorphism restricts to the corner with red strands in order. -/
def stendhalOffDiagonalEquiv (hQ : ∀ i j, i ≠ j → Q i j = Q' i j) :
    StendhalAlgebra k Q Λ ν ≃ₐ[k] StendhalAlgebra k Q' Λ ν where
  toRingEquiv := IsIdempotentElem.cornerRingEquiv _ _
    (stendhalAllOrdersOffDiagonalEquiv hQ).toRingEquiv
    (stendhalAllOrdersOffDiagonalEquiv_redOrderedIdem hQ)
  commutes' r := by
    apply Subtype.ext
    change stendhalAllOrdersOffDiagonalEquiv (Λ := Λ) hQ
        (algebraMap k (StendhalAlgebraAllOrders k Q Λ ν) r *
          StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) =
      algebraMap k (StendhalAlgebraAllOrders k Q' Λ ν) r *
        StendhalAlgebraAllOrders.redOrderedIdem k Q' Λ ν
    rw [map_mul, AlgEquiv.commutes, stendhalAllOrdersOffDiagonalEquiv_redOrderedIdem]

theorem stendhalOffDiagonalEquiv_e (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    (i : KLR.Seq (stendhalWeight ℓ ν)) (hi : IsRedOrdered i) :
    stendhalOffDiagonalEquiv (Λ := Λ) hQ (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) i hi) =
      StendhalAlgebra.e (k := k) (Q := Q') (Λ := Λ) i hi :=
  Subtype.ext (stendhalAllOrdersOffDiagonalEquiv_e hQ i)


private theorem violatedIdeal_le_comap (f : StendhalAlgebra k Q Λ ν ≃ₐ[k]
    StendhalAlgebra k Q' Λ ν)
    (hf : ∀ (i : KLR.Seq (stendhalWeight ℓ ν)) (hi : IsRedOrdered i),
      f (StendhalAlgebra.e i hi) = StendhalAlgebra.e i hi) :
    StendhalAlgebra.violatedIdeal k Q Λ ν ≤ TwoSidedIdeal.comap f.toRingEquiv.toRingHom
      (StendhalAlgebra.violatedIdeal k Q' Λ ν) := by
  rw [StendhalAlgebra.violatedIdeal, TwoSidedIdeal.span_le]
  rintro _ ⟨i, hi, hv, rfl⟩
  rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
  change f (StendhalAlgebra.e i hi) ∈ _
  rw [hf]
  exact TwoSidedIdeal.subset_span ⟨i, hi, hv, rfl⟩

theorem stendhalOffDiagonalEquiv_mem_violatedIdeal_iff (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    (x : StendhalAlgebra k Q Λ ν) :
    stendhalOffDiagonalEquiv hQ x ∈ StendhalAlgebra.violatedIdeal k Q' Λ ν ↔
      x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν := by
  let f := stendhalOffDiagonalEquiv (Λ := Λ) (ν := ν) hQ
  have hf := stendhalOffDiagonalEquiv_e (Λ := Λ) (ν := ν) hQ
  constructor
  · intro hx
    have h := violatedIdeal_le_comap f.symm (fun i hi => (f.symm_apply_eq).mpr (hf i hi).symm) hx
    rw [TwoSidedIdeal.mem_comap] at h
    change f.symm (f x) ∈ _ at h
    rwa [AlgEquiv.symm_apply_apply] at h
  · intro hx
    have h := violatedIdeal_le_comap f hf hx
    rwa [TwoSidedIdeal.mem_comap] at h

/-- The tensor product algebra is unchanged by altering only diagonal parameters. -/
def tensorProductOffDiagonalEquiv (hQ : ∀ i j, i ≠ j → Q i j = Q' i j) :
    TensorProductAlgebra k Q Λ ν ≃ₐ[k] TensorProductAlgebra k Q' Λ ν :=
  RingCon.congrₐ k (stendhalOffDiagonalEquiv hQ) (by
    ext x y
    rw [RingCon.comap_rel, TwoSidedIdeal.rel_iff, TwoSidedIdeal.rel_iff]
    change _ ↔ stendhalOffDiagonalEquiv hQ x - stendhalOffDiagonalEquiv hQ y ∈ _
    rw [← map_sub, stendhalOffDiagonalEquiv_mem_violatedIdeal_iff])

theorem tensorProductOffDiagonalEquiv_e (hQ : ∀ i j, i ≠ j → Q i j = Q' i j)
    (i : KLR.Seq (stendhalWeight ℓ ν)) (hi : IsRedOrdered i) :
    tensorProductOffDiagonalEquiv hQ
      (TensorProductAlgebra.mk (k := k) (Q := Q) (Λ := Λ) ν (StendhalAlgebra.e i hi)) =
      TensorProductAlgebra.mk (k := k) (Q := Q') (Λ := Λ) ν (StendhalAlgebra.e i hi) := by
  change TensorProductAlgebra.mk (k := k) (Q := Q') (Λ := Λ) ν
      (stendhalOffDiagonalEquiv hQ (StendhalAlgebra.e i hi)) = _
  rw [stendhalOffDiagonalEquiv_e]

/-- For a single black colour, the comparison applies to arbitrary parameters. -/
def tensorProductUnitParameterEquiv {P P' : Unit → Unit → MvPolynomial (Fin 2) k}
    (Λ : Fin ℓ → Unit →₀ ℕ) (ν : Multiset Unit) :
    TensorProductAlgebra k P Λ ν ≃ₐ[k] TensorProductAlgebra k P' Λ ν :=
  tensorProductOffDiagonalEquiv (fun i j h => (h (Subsingleton.elim i j)).elim)

end Categorification.Stendhal
