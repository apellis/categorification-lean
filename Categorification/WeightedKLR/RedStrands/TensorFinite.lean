/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorProjection
import Categorification.WeightedKLR.RedStrands.AffineCoverGrading
import Categorification.KLR.CyclotomicIntegrable

/-!
# Finiteness of Webster's tensor product algebra

Webster, arXiv:1309.3796v2, Definitions 4.6–4.7 and §4.7, Theorem 4.38.
In the violating quotient the leftmost dot vanishes. Red dots vanish at
every position; induction on the black dot positions and the polynomial
spanning theorem then give a finite module over the coefficient ring.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra MvPolynomial
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "Aff" => KLRAlgebra k (affineCoverQ Q Λ) μ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => affineTensorProjection (Q := Q) Λ ν
local notation "q" => affineCoverQ Q Λ

private theorem projection_red_dot (s : Seq μ) (a : Fin m) (h : (s.lbl a).isRight) :
    π (x a * e s) = 0 := by
  have hred : affineCover Q Λ ν (x a * e s) = 0 := by
    rw [map_mul, affineCover_e, affineCover_x]
    exact StendhalAlgebraAllOrders.x_mul_e_of_red a s h
  change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν (x a * e s))) = 0
  rw [hred, map_zero, map_zero]

private theorem projection_violated (s : Seq μ) (hs : IsViolated s) : π (e s) = 0 := by
  let J := StendhalAlgebra.violatedIdeal k Q Λ ν
  change J.ringCon.mk' (orderProjection Q Λ ν (affineCover Q Λ ν (e s))) = 0
  rw [affineCover_e, ← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  by_cases ho : IsRedOrdered s
  · apply TwoSidedIdeal.subset_span
    refine ⟨s, ho, hs, Subtype.ext ?_⟩
    change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν = StendhalAlgebraAllOrders.e s
    simp [StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ho]
  · have hz : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s) = 0 := by
      apply Subtype.ext
      change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν = 0
      simp [StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ho]
    rw [hz]
    exact J.zero_mem

local instance : Module Aff T := Module.compHom _ (π).toRingHom

private theorem first_dot (h : 0 < m) (v : T) :
    (pol (X ⟨0,h⟩ ^ 1) : Aff) • v = 0 := by
  apply smul_eq_zero_of_mul_e _ _ v
  intro s w
  change π (pol _ * e s) * w = 0
  rw [pow_one, pol_X]
  cases hc : s.lbl ⟨0,h⟩ with
  | inl i => rw [map_mul, projection_violated Λ ν s ⟨h, by simp [hc]⟩, mul_zero, zero_mul]
  | inr r => rw [projection_red_dot Λ ν s _ (by simp [hc]), zero_mul]

variable {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q)

include hQ in
private theorem next_dot (b N : ℕ) (hb : b+1 < m)
    (hN : ∀ v : T, (pol (X ⟨b, by omega⟩ ^ N) : Aff) • v = 0) :
    ∃ N' : ℕ, ∀ v : T, (pol (X ⟨b+1,hb⟩ ^ N') : Aff) • v = 0 := by
  classical
  let S := Finset.univ (α := Seq μ)
  have hs (s : Seq μ) : ∃ n : ℕ, (X ⟨b+1,hb⟩ : MvPolynomial (Fin m) k) ^ n ∈ annE (Q := q) T s := by
    by_cases he : s.lbl ⟨b, by omega⟩ = s.lbl ⟨b+1,hb⟩
    · exact ⟨N, next_pow_mem_annE_of_eq b hb N hN s he⟩
    cases hj : s.lbl ⟨b+1,hb⟩ with
    | inr r =>
      refine ⟨1, fun v => ?_⟩
      change π (pol _ * e s) * v = 0
      rw [pow_one, pol_X, projection_red_dot Λ ν s _ (by simp [hj]), zero_mul]
    | inl j =>
      have hc : ∃ (c : k) (d : ℕ), IsUnit c ∧
          aeval (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k)
            (q (s.lbl ⟨b, by omega⟩) (s.lbl ⟨b+1,hb⟩)) = MvPolynomial.C c * X 1 ^ d := by
        cases hi : s.lbl ⟨b, by omega⟩ with
        | inl i =>
          rw [hj]
          exact hQ.aeval_zero_first i j (by intro h; apply he; simp [hi,hj,h])
        | inr r =>
          refine ⟨1,Λ r j,isUnit_one,?_⟩
          simp [hj, affineCoverQ, stendhalQ]
      obtain ⟨c,d,hc,hcd⟩ := hc
      exact ⟨_, next_pow_mem_annE_of_ne b hb N hN s he c d hc hcd⟩
  choose n hn using hs
  refine ⟨S.sup n, fun v => smul_eq_zero_of_mul_e _ (fun s => ?_) v⟩
  have hle : n s ≤ S.sup n := Finset.le_sup (Finset.mem_univ s)
  have hm : (X ⟨b+1,hb⟩ : MvPolynomial (Fin m) k) ^ S.sup n ∈ annE (Q := q) T s := by
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Ideal.mul_mem_left _ _ (hn s)
  exact hm

include hQ in
/-- Each dot of the affine cover becomes nilpotent in Webster's tensor product
algebra (Definitions 4.6–4.7). -/
theorem tensorProjection_dot_nilpotent (a : Fin m) : IsNilpotent (π (x a)) := by
  have hb (b : ℕ) (hb : b < m) : ∃ N : ℕ, ∀ v : T, (pol (X ⟨b,hb⟩ ^ N) : Aff) • v = 0 := by
    induction b with
    | zero => exact ⟨1, first_dot Λ ν hb⟩
    | succ b ih =>
      obtain ⟨N,hN⟩ := ih (by omega)
      exact next_dot Λ ν hQ b N hb hN
  obtain ⟨N,hN⟩ := hb a.val a.isLt
  refine ⟨N,?_⟩
  have hz := hN 1
  change π _ * 1 = 0 at hz
  simpa only [mul_one, map_pow, pol_X] using hz

include hQ in
/-- Webster's tensor product algebra in fixed black content is a finite
module over the coefficient ring. Over a field its projective Euler form
therefore takes Laurent polynomial values (Webster, arXiv:1309.3796v2,
§4.7, Theorem 4.38). -/
theorem tensorProductAlgebra_finite : Module.Finite k T := by
  classical
  choose N hN using tensorProjection_dot_nilpotent Λ ν hQ
  let ρ (w : Equiv.Perm (Fin m)) := (TypeA.exists_reduced m w).choose
  let Dots := (a : Fin m) → Fin (N a)
  let b (z : Equiv.Perm (Fin m) × Dots × Seq μ) : T :=
    π (ψw (ρ z.1) * pol (monomial (Finsupp.equivFunOnFinite.symm (fun a => (z.2.1 a).val)) 1) *
      e z.2.2)
  let W := Submodule.span k (Set.range b)
  have hspan := span_eq_top' (k := k) (Q := q) (ν := μ) ρ (fun w => (TypeA.exists_reduced m w).choose_spec)
  have hw : W = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro t
    obtain ⟨r,rfl⟩ := affineTensorProjection_surjective (Q := Q) Λ ν t
    have hr : r ∈ Submodule.span k _ := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun r _ => π r ∈ W) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨w,u,s,rfl⟩
      by_cases h : ∀ a, u a < N a
      · apply Submodule.subset_span
        refine ⟨(w,fun a => ⟨u a,h a⟩,s),?_⟩
        have he : Finsupp.equivFunOnFinite.symm (fun a => u a) = u :=
          Finsupp.equivFunOnFinite.symm_apply_apply u
        simp only [b, he]
      · push Not at h
        obtain ⟨a, ha⟩ := h
        have hle : Finsupp.single a (N a) ≤ u := Finsupp.single_le_iff.mpr ha
        have hm : monomial u (1 : k) = monomial (u - Finsupp.single a (N a)) 1 * X a ^ N a := by
          rw [← monomial_add_single, tsub_add_cancel_of_le hle]
        simp only [hm, map_mul, map_pow, pol_X, hN, mul_zero, zero_mul]
        exact W.zero_mem
    · simpa only [map_zero] using W.zero_mem
    · intro a b _ _ ha hb
      rw [map_add]
      exact W.add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact W.smul_mem c ha
  exact ⟨hw ▸ Submodule.fg_span (Set.finite_range b)⟩

end Categorification.Stendhal
