/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.KLR.Prop213

/-!
# The cyclotomic relation at a single red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.4, proof of Theorem 4.20. In the violating quotient with a single red strand
the leftmost crossing and the leftmost dot vanish. Relation (4.2) then kills
the cyclotomic dot power on the first black strand, for every black weight.
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR TypeA StendhalAlgebraAllOrders

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight 1 ν
local notation "m" => Multiset.card μ
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν

omit [DecidableEq I] in
private theorem eq_of_single_red {s : Seq μ} {a b : Fin m} {r : Fin 1}
    (ha : s.lbl a = .inr r) (hb : s.lbl b = .inr r) : a = b := by
  classical
  let F := Finset.univ.filter (fun c => Sum.inr r = s.lbl c)
  have hc : F.card = 1 := by
    change (Finset.univ.val.filter (fun c => Sum.inr r = s.lbl c)).card = 1
    rw [← Multiset.count_map, show Finset.univ.val.map s.lbl = μ from s.2]
    have hr : r = 0 := Subsingleton.elim _ _
    simp [stendhalWeight, hr]
  exact Finset.card_le_one_iff.mp hc.le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.symm⟩)

omit [DecidableEq I] in
/-- A single red strand always occurs in the prescribed red order. -/
theorem ordered (s : Seq μ) : IsRedOrdered s := by
  intro a b r r' hab ha hb
  obtain rfl : r' = r := Subsingleton.elim _ _
  exact (hab.ne (eq_of_single_red ν ha hb)).elim

theorem redOrderedIdem_eq_one : redOrderedIdem k Q Λ ν = 1 := by
  classical
  simp [redOrderedIdem, ordered, e, ← map_sum, KLRAlgebra.sum_e]

/-- For one red label Webster's red-order corner is the entire diagram algebra. -/
def orderedEquiv : A ≃ₐ[k] StendhalAlgebra k Q Λ ν where
  toFun z := ⟨z, by
    rw [Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem, redOrderedIdem_eq_one]
    simp⟩
  invFun z := z.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    apply Subtype.ext
    change algebraMap k A c = c • redOrderedIdem k Q Λ ν
    rw [redOrderedIdem_eq_one, Algebra.algebraMap_eq_smul_one]

/-- Projection of every one-red diagram to the violating quotient. -/
def mk : A →ₐ[k] TensorProductAlgebra k Q Λ ν :=
  (TensorProductAlgebra.mk Q Λ ν).comp (orderedEquiv Q Λ ν).toAlgHom

theorem mk_surjective : Function.Surjective (mk Q Λ ν) :=
  (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective.comp
    (orderedEquiv Q Λ ν).surjective

variable {ν}

theorem mk_e_of_violated (s : Seq μ) (hs : IsViolated s) : mk Q Λ ν (e s) = 0 := by
  let J := StendhalAlgebra.violatedIdeal k Q Λ ν
  change J.ringCon.mk' (StendhalAlgebra.e s (ordered ν s)) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span ⟨s, ordered ν s, hs, rfl⟩

private theorem ext_e (z : A) (hz : ∀ s : Seq μ, mk Q Λ ν (z * e s) = 0) :
    mk Q Λ ν z = 0 := by
  have hs : (∑ s : Seq μ, e s : A) = 1 := by
    simp only [e, ← map_sum, KLRAlgebra.sum_e, map_one]
  rw [← mul_one z, ← hs, Finset.mul_sum, map_sum]
  exact Finset.sum_eq_zero fun s _ => hz s

/-- The unique red strand is leftmost on every surviving idempotent, so no crossing
at position zero survives (Webster, Definition 4.6 and Theorem 4.20). -/
theorem mk_first_cross : mk Q Λ ν (ψ 0) = 0 := by
  by_cases h : 0 + 1 < m
  · apply ext_e
    intro s
    by_cases hs : IsViolated s
    · rw [map_mul, mk_e_of_violated Q Λ s hs, mul_zero]
    have ht : IsViolated (sadj m 0 • s) := by
      refine ⟨by omega, ?_⟩
      rw [KLRAlgebra.lbl_sadj_left h]
      cases hb : s.lbl ⟨1, h⟩ with
      | inl i => rfl
      | inr r =>
        cases hr : s.lbl ⟨0, by omega⟩ with
        | inl i => exact (hs ⟨by omega, by simp [hr]⟩).elim
        | inr r' =>
          obtain rfl : r' = r := Subsingleton.elim _ _
          have he := eq_of_single_red ν hr hb
          exact False.elim (by have := congrArg Fin.val he; simp at this)
    have hp := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.ψ_mul_e 0 s)
    simp only [map_mul] at hp
    change mk Q Λ ν (ofKLR k Q Λ ν _ * ofKLR k Q Λ ν _) = 0
    rw [hp, map_mul, ← e, mk_e_of_violated Q Λ _ ht, zero_mul]
  · simp [ψ, KLRAlgebra.ψ_eq_zero 0 (Nat.le_of_not_gt h)]

/-- The leftmost dot vanishes in the one-red violating quotient. -/
theorem mk_first_dot (h : 0 < m) : mk Q Λ ν (x ⟨0, h⟩) = 0 := by
  apply ext_e
  intro s
  cases hs : s.lbl ⟨0, h⟩ with
  | inl i =>
    rw [map_mul, mk_e_of_violated Q Λ s ⟨h, by simp [hs]⟩, mul_zero]
  | inr r =>
    rw [x_mul_e_of_red _ s (by simp [hs]), map_zero]

/-- The cyclotomic generator vanishes in every black weight (Webster,
arXiv:1309.3796v2, Theorem 4.20, first kernel inclusion). -/
theorem first_black_dot_pow (h : 1 < m) (s : Seq μ) (i : I)
    (hr : s.lbl ⟨0, by omega⟩ = .inr 0) (hi : s.lbl ⟨1, h⟩ = .inl i) :
    mk Q Λ ν (x ⟨1, h⟩) ^ Λ 0 i * mk Q Λ ν (e s) = 0 := by
  have he := congrArg (mk Q Λ ν) (ψ_sq_red_black 0 h s i 0 hr hi)
  simpa only [map_mul, map_pow, mk_first_cross, zero_mul] using he.symm

end Categorification.Stendhal.SingleRed
