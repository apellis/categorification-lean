/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumJets
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Clockwise bubbles on a lowest weight object

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: on the generating object `𝕍` the bubbles of the colour `i`
act by the coefficients of `∏_{π j = i} (1 - z_j t)^{-Λ_j}`.

This file is the categorical part of that computation, stated in a linear category. Let `V` be
lowest weight for `i` (`F_i V = 0`), of weight `h = -N`. Let the labels `a` over `i` occur with
multiplicities `hₐ`, `N = ∑ₐ hₐ`. Rouquier's isomorphism then says that the cups
`c t : V → F_i E_i V`, `t < N`, are a basis, with dual basis the caps `capN`. The clockwise
bubble with `n` dots is `c n ≫ capN (N - 1)`. Its value comes from the decomposition
`F_i E_i V = ⊕ₐ Wₐ` over the labels. On the summand `a`:

* the cup with `n` dots is the label cup `νₐ : V → Wₐ` followed by the `n`-th power of the dot,
  `zₐ + yₐ`;
* the shifted dot `yₐ` kills the cup in degrees `≥ hₐ` (the cyclotomic relation).

Then `c n ≫ d = ∑_{(a, m), m < hₐ} C(n, m) zₐ^{n-m} ψ_{a,m}`, with
`ψ_{a,m} = νₐ ≫ yₐ^m ≫ ιₐ ≫ d` (`comp_eq_sum_jetCoeff`). Read through an `L`-algebra map `ev` of
`End V` to a commutative ring, the dual-basis property `ev (c t ≫ d) = δ_{t, N-1}` (`t < N`)
determines all the values (`ev_comp_eq_coeff`, from `jetSum_eq_coeff`):

  `ev (c n ≫ d) = [t^{n+1-N}] ∏ₐ (1 - zₐ t)^{-hₐ}`.

## Main results

* `comp_eq_sum_jetCoeff`: the expansion of `c n ≫ d` over the summands.
* `ev_comp_eq_coeff`: the values.
-/

open CategoryTheory CategoryTheory.Limits PowerSeries

namespace Categorification.KLR.Unfurling

variable {L : Type*} [Field L] {C : Type*} [Category C] [Preadditive C] [Linear L C]
  {A : Type*} [Fintype A] {V W : C} {Wa : A → C}
  (π : ∀ a, W ⟶ Wa a) (ι : ∀ a, Wa a ⟶ W) (ν : ∀ a, V ⟶ Wa a) (y : ∀ a, End (Wa a))
  (z : A → L) (hp : A → ℕ) (c : ℕ → (V ⟶ W)) (d : W ⟶ V)

/-- The coefficients `ψ_{a,m} = νₐ ≫ yₐ^m ≫ ιₐ ≫ d`. -/
def vacCoeff (x : Σ a, Fin (hp a)) : End V := ν x.1 ≫ (y x.1 ^ (x.2 : ℕ) : End (Wa x.1)) ≫ ι x.1 ≫ d

omit [Fintype A] in
theorem comp_pow_shift (a : A) (n : ℕ) (hν : ∀ m, hp a ≤ m → ν a ≫ (y a ^ m : End (Wa a)) = 0) :
    ν a ≫ ((algebraMap L (End (Wa a)) (z a) + y a) ^ n : End (Wa a)) =
      ∑ m : Fin (hp a), jetCoeff (z a) m n • (ν a ≫ (y a ^ (m : ℕ) : End (Wa a))) := by
  have hcomm : Commute (y a) (algebraMap L (End (Wa a)) (z a)) := (Algebra.commutes _ _).symm
  rw [add_comm, hcomm.add_pow, Preadditive.comp_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1), ν a ≫ (y a ^ m * algebraMap L (End (Wa a)) (z a) ^
      (n - m) * (n.choose m : End (Wa a)) : End (Wa a)) =
        jetCoeff (z a) m n • (ν a ≫ (y a ^ m : End (Wa a))) := by
    intro m _
    rw [← map_pow, ← map_natCast (algebraMap L (End (Wa a))), mul_assoc, ← map_mul,
      ← Algebra.commutes, ← Algebra.smul_def, Linear.comp_smul, jetCoeff, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_subset (s₂ := Finset.range (n + 1 + hp a))
      (fun m hm => by simp only [Finset.mem_range] at hm ⊢; omega)
      (fun m _ hm => by
        simp only [Finset.mem_range, not_lt] at hm
        rw [jetCoeff, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_smul]),
    Fin.sum_univ_eq_sum_range (fun m => jetCoeff (z a) m n • (ν a ≫ (y a ^ m : End (Wa a))))]
  exact (Finset.sum_subset (fun m hm => by simp only [Finset.mem_range] at hm ⊢; omega)
    (fun m _ hm => by
      simp only [Finset.mem_range, not_lt] at hm
      rw [hν m hm, smul_zero])).symm

/-- **The expansion of a bubble on a lowest weight object** over the summands of
`F E V = ⊕ₐ Wₐ`. -/
theorem comp_eq_sum_jetCoeff (hπι : ∑ a, π a ≫ ι a = 𝟙 W)
    (hc : ∀ n a, c n ≫ π a = ν a ≫ ((algebraMap L (End (Wa a)) (z a) + y a) ^ n : End (Wa a)))
    (hν : ∀ a m, hp a ≤ m → ν a ≫ (y a ^ m : End (Wa a)) = 0) (n : ℕ) :
    (c n ≫ d : End V) = ∑ x : Σ a, Fin (hp a), jetCoeff (z x.1) x.2 n • vacCoeff ι ν y hp d x := by
  conv_lhs => rw [← Category.id_comp d, ← hπι, Preadditive.sum_comp, Preadditive.comp_sum]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Category.assoc, ← Category.assoc (c n), hc n a, comp_pow_shift ν y z hp a n (hν a),
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [vacCoeff, Linear.smul_comp, Category.assoc]

/-- **The clockwise bubbles on a lowest weight object** (Webster, arXiv:1603.06311v3, proof of
the theorem with label `nondegenerate`). Suppose `F E V = ⊕ₐ Wₐ`, the cups `c n` with `n` dots
are `νₐ ≫ (zₐ + yₐ)ⁿ` on the summand `a`, and `νₐ ≫ yₐ^m = 0` for `m ≥ hₐ`. If an `L`-algebra map
`ev` from `End V` to a commutative ring sends `c t ≫ d` to `δ_{t, N-1}` for `t < N = ∑ₐ hₐ > 0`,
then for every `n`

  `ev (c n ≫ d) = [t^{n+1-N}] ∏ₐ (1 - zₐ t)^{-hₐ}`   (`0` if `n + 1 < N`). -/
theorem ev_comp_eq_coeff {R : Type*} [CommRing R] [Algebra L R] (ev : End V →ₐ[L] R)
    (hπι : ∑ a, π a ≫ ι a = 𝟙 W)
    (hc : ∀ n a, c n ≫ π a = ν a ≫ ((algebraMap L (End (Wa a)) (z a) + y a) ^ n : End (Wa a)))
    (hν : ∀ a m, hp a ≤ m → ν a ≫ (y a ^ m : End (Wa a)) = 0) (hN : 0 < ∑ a, hp a)
    (hd : ∀ t < ∑ a, hp a, ev (c t ≫ d) = if t + 1 = ∑ a, hp a then 1 else 0) (n : ℕ) :
    ev (c n ≫ d) = if ∑ a, hp a ≤ n + 1 then
      algebraMap L R (coeff (n + 1 - ∑ a, hp a)
        ((∏ a, oneSubUnit (z a) ^ (-(hp a : ℤ)) : (PowerSeries L)ˣ) : PowerSeries L))
      else 0 := by
  have hjet : ∀ t, ev (c t ≫ d) =
      jetSum (fun a => algebraMap L R (z a)) hp (fun x => ev (vacCoeff ι ν y hp d x)) t := by
    intro t
    rw [comp_eq_sum_jetCoeff π ι ν y z hp c d hπι hc hν t, map_sum, jetSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm, jetCoeff, jetCoeff, map_mul, map_pow, map_natCast]
  rw [hjet, jetSum_eq_coeff _ hp _ hN (fun t ht => by rw [← hjet]; exact hd t ht)]
  split_ifs
  · rw [← coeff_map]
    congr 1
    have h := congrArg Units.val
      (map_prod (Units.map (map (algebraMap L R) : PowerSeries L →* PowerSeries R))
        (fun a => oneSubUnit (z a) ^ (-(hp a : ℤ))) Finset.univ)
    simp only [map_zpow, map_oneSubUnit, Units.coe_map, MonoidHom.coe_coe] at h
    exact h.symm
  · rfl

end Categorification.KLR.Unfurling
