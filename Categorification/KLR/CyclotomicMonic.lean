/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicEF

/-!
# Monic cancellation on the cyclotomic module K₀

Right multiplication by a monic polynomial in the last dot is injective on
`K₀ e(β,i)`. This supplies the torsion-free cancellation used in the proof of
Kang–Kashiwara, arXiv:1102.4677v4, Lemma 4.19. It is proved in last-strand free
coordinates and does not assert the reversed `PQ` identity by itself.
-/

namespace Categorification.KLR.KLRAlgebra
open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rb" => KLRAlgebra k Q β
local notation "Ri" => KLRAlgebra k Q Si
local notation "T0" => Rb ⊗[k] Ri

/-- Right multiplication acts on each last-strand free coordinate. -/
theorem lastFree_mul_cLL (t : Fin (Multiset.card β + 1) → T0) (u : T0) :
    lastFree i β t * cLL Q i β u = lastFree i β (fun b => t b * u) := by
  simp only [lastFree, Finset.sum_mul, mul_assoc, cLL_mul]

variable (a : I → Polynomial k)

/-- Scalar polynomials in the last strand become scalar-coefficient polynomials. -/
theorem thetaL0_one_tmul_sec (g : Polynomial k) :
    thetaL0 Q i β a (1 ⊗ₜ sec Q i g) = g.map (algebraMap k (CycKLR k Q a β)) := by
  ext d
  rw [thetaL0_apply, Algebra.TensorProduct.comm_tmul, thetaL, AlgHom.comp_apply,
    Polynomial.coe_mapAlgHom, Polynomial.coeff_map, coeff_theta_tmul,
    singlePoly_sec, mul_one, Polynomial.coeff_map]
  exact (CycKLR.mk k Q a β).commutes _

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (hβ : 0 < Multiset.card β)

include hPQ hP hβ in
/-- Monic cancellation, retaining the explicit right colour projection. -/
theorem mul_monic_mem_cycL0_iff (r : R) (g : Polynomial k) (hg : g.Monic) :
    (r * Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) g) * cL Q i β 1 ∈
        cycL0 a (zero_lt_card_single_add i β) ↔
      r * cL Q i β 1 ∈ cycL0 a (zero_lt_card_single_add i β) := by
  obtain ⟨t, ht⟩ := lastFree_span i β hPQ hP r
  have hm : lastFree i β (fun b => t b * (1 ⊗ₜ sec Q i g)) =
      (r * Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) g) * cL Q i β 1 := by
    rw [← lastFree_mul_cLL, ← ht, mul_assoc, cL_one_mul_cLL,
      cLL_one_tmul, singlePoly_sec, mul_assoc]
  rw [← hm, ht, lastFree_mem_cycL0_iff i β a hPQ hP hβ,
    lastFree_mem_cycL0_iff i β a hPQ hP hβ]
  apply forall_congr'
  intro b
  rw [← thetaL0_eq_zero_iff, ← thetaL0_eq_zero_iff, map_mul, thetaL0_one_tmul_sec]
  exact (hg.map (algebraMap k (CycKLR k Q a β))).mul_left_eq_zero_iff

include hPQ hP hβ in
/-- On the `e(β,i)` corner, no additional projection is needed for monic cancellation. -/
theorem mul_monic_mem_cycL0_iff_of_cut (r : R) (hr : r * cL Q i β 1 = r)
    (g : Polynomial k) (hg : g.Monic) :
    r * Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) g ∈
        cycL0 a (zero_lt_card_single_add i β) ↔
      r ∈ cycL0 a (zero_lt_card_single_add i β) := by
  have hc := (commute_aeval_of_commute (commute_x_last_cL (Q := Q) i β 1) g).eq
  have h := mul_monic_mem_cycL0_iff i β a hPQ hP hβ r g hg
  rwa [mul_assoc, hc, ← mul_assoc, hr] at h

end Categorification.KLR.KLRAlgebra
