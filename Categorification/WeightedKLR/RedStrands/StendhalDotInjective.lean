/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalBasis

/-!
# Dots on black strands act injectively on `T̃^λ e(i)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 4.16. Multiplying a Stendhal term `ψ_{ρ w} x^u e(i)` on the right by `x_a^d`, for a
black strand at position `a` of `i`, gives the Stendhal term `ψ_{ρ w} x^{u + d·a} e(i)`. Since
the Stendhal terms are linearly independent, right multiplication by `e(i) x_a^d` is injective
on `T̃^λ e(i)`.

## Main results

* `KLRAlgebra.stdElt_mul_e_mul_x_pow`: `ψ_{ρ w} x^u e(i) · e(i) x_a^d = ψ_{ρ w} x^{u + d·a} e(i)`.
* `Stendhal.eq_zero_of_mul_e_mul_x_pow`: if `y e(i) x_a^d = 0` for `y ∈ T̃^λ` and a black strand
  at position `a` of `i`, then `y e(i) = 0`.
-/

noncomputable section

namespace Categorification

open KLR Equiv MvPolynomial

namespace KLR.KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- A dot of order `d` at the bottom of a standard element adds `d` to its dot exponent. -/
theorem stdElt_mul_e_mul_x_pow (ρ : Perm (Fin m) → List ℕ)
    (b : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) (a : Fin m) (d : ℕ) :
    (stdElt ρ b : KLRAlgebra k Q ν) * e b.1 * x a ^ d =
      stdElt ρ (b.1, b.2.1, b.2.2 + Finsupp.single a d) := by
  have hc1 : Commute (x a : KLRAlgebra k Q ν) (e b.1) := x_mul_e a b.1
  have hc : Commute (x a ^ d : KLRAlgebra k Q ν) (e b.1) := hc1.pow_left d
  simp only [stdElt]
  rw [mul_assoc (_ * _) (e b.1) (e b.1), e_mul_e, ite_eq_left_of_eq_true _ _ (eq_self _),
    mul_assoc (_ * _) (e b.1),
    ← hc.eq, ← mul_assoc, mul_assoc (ψw _), ← pol_X, ← map_pow, ← map_mul, X_pow_eq_monomial,
    monomial_mul_monomial, one_mul]

end KLR.KLRAlgebra

namespace Stendhal

open KLRAlgebra TypeA

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}

/-- Adding `d` dots on the black strand at position `a` of the bottom `t` of a Stendhal term. -/
def dotShift (t : KLR.Seq μ) (a : Fin m) (ha : (t.1 a).isLeft) (d : ℕ)
    (b : {b : {b // IsStendhalTerm ρ b} // b.1.1 = t}) : {b // IsStendhalTerm ρ b} :=
  ⟨(b.1.1.1, b.1.1.2.1, b.1.1.2.2 + Finsupp.single a d), b.1.2.1, b.1.2.2.1,
    fun a' ha' => by
      rcases Finset.mem_union.1 (Finsupp.support_add ha') with h | h
      · exact b.1.2.2.2.1 a' h
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h), b.2]
        exact ha,
    b.1.2.2.2.2⟩

omit [DecidableEq I] in
theorem dotShift_injective (t : KLR.Seq μ) (a : Fin m) (ha : (t.1 a).isLeft) (d : ℕ) :
    Function.Injective (dotShift (ρ := ρ) t a ha d) := by
  intro b b' h
  have h' := congrArg Subtype.val h
  simp only [dotShift, Prod.mk.injEq, add_left_inj] at h'
  exact Subtype.ext (Subtype.ext (Prod.ext h'.1 (Prod.ext h'.2.1 h'.2.2)))

theorem stendhalTerm_val_mul_x_pow (hρ : ∀ w, wordProd m (ρ w) = w) (t : KLR.Seq μ) (a : Fin m)
    (ha : (t.1 a).isLeft) (d : ℕ) (b : {b : {b // IsStendhalTerm ρ b} // b.1.1 = t}) :
    (stendhalTerm Q Λ hρ b.1).1 * StendhalAlgebraAllOrders.x a ^ d =
      (stendhalTerm Q Λ hρ (dotShift t a ha d b)).1 := by
  have h := stdElt_mul_e_mul_x_pow (k := k) (Q := stendhalQ Q Λ) ρ b.1.1 a d
  rw [stdElt_mul_e] at h
  rw [stendhalTerm_val, stendhalTerm_val, StendhalAlgebraAllOrders.x, ← map_pow, ← map_mul, h]
  rfl

/-- **Dots on a black strand act injectively** on `T̃^λ e(t)` (from the independence of the
Stendhal terms, arXiv:1309.3796v3, Proposition 4.16). -/
theorem eq_zero_of_mul_e_mul_x_pow (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hB : LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)))
    (t : KLR.Seq μ) (ht : IsRedOrdered t) (a : Fin m) (ha : (t.1 a).isLeft) (d : ℕ)
    (y : StendhalAlgebra k Q Λ ν)
    (hy : y.1 * StendhalAlgebraAllOrders.e t * StendhalAlgebraAllOrders.x a ^ d = 0) :
    y.1 * StendhalAlgebraAllOrders.e t = 0 := by
  classical
  have hρ' : ∀ w, wordProd m (ρ w) = w := fun w => (hρ w).2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (span_stendhalTerm (Q := Q) (Λ := Λ) hρ (Submodule.mem_top (x := y)))
  let p : {b // IsStendhalTerm ρ b} → Prop := fun b => b.1.1 = t
  have hz : y * StendhalAlgebra.e t ht =
      ∑ b ∈ c.support.subtype p, c b.1 • stendhalTerm Q Λ hρ' b.1 := by
    rw [Finset.sum_subtype_eq_sum_filter (fun b => c b • stendhalTerm Q Λ hρ' b),
      ← hc, Finsupp.sum, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc, stendhalTerm_mul_e]
    by_cases hb : b.1.1 = t
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false hb),
        smul_zero]
  have hzv : y.1 * StendhalAlgebraAllOrders.e t = (y * StendhalAlgebra.e t ht).1 := rfl
  have hsum : ∑ b ∈ c.support.subtype p,
      c b.1 • stendhalTerm Q Λ hρ' (dotShift t a ha d b) = 0 := by
    apply stendhalValₗ_injective
    rw [map_sum, map_zero, ← hy, hzv, hz]
    change _ = stendhalValₗ (∑ b ∈ c.support.subtype p, c b.1 • stendhalTerm Q Λ hρ' b.1) *
      StendhalAlgebraAllOrders.x a ^ d
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, map_smul, smul_mul_assoc]
    exact congrArg (c b.1 • ·) (stendhalTerm_val_mul_x_pow hρ' t a ha d b).symm
  have h0 := linearIndependent_iff'.1 (hB.comp _ (dotShift_injective t a ha d))
    (c.support.subtype p) (fun b => c b.1) hsum
  rw [hzv, hz, Finset.sum_eq_zero fun b hb => by
    rw [h0 b hb]; exact zero_smul k (stendhalTerm Q Λ hρ' b.1)]
  rfl

end Stendhal

end Categorification
