/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedMaximalLoading
import Categorification.KLR.CyclotomicStringParametrization

/-!
# Stringy loadings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Definition 5.16 and Proposition 5.17. The black blocks of a loading are compared with the string
parametrizations of simple modules over the cyclotomic quotients of the KLR algebra.

## Main results

* `cycKLR_x_isNilpotent`: the dots act nilpotently in the cyclotomic quotient
  `R^{λ}(β)` for monomial cyclotomic polynomials `X^{λ_i}`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra
variable {I k : Type*} [DecidableEq I] [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} {C : QuantumGroup.CartanDatum I}
    (hQ : IsRouquierQ C Q) (μ : I →₀ ℕ) (β : Multiset I)

include hQ in
/-- The dots are nilpotent in the cyclotomic quotient with monomial cyclotomic polynomials,
through the identification with the tensor product algebra of one red strand. -/
theorem cycKLR_x_isNilpotent (a : Fin (Multiset.card β)) :
    IsNilpotent (CycKLR.mk k Q (fun i => (Polynomial.X : Polynomial k) ^ μ i) β (x a)) := by
  obtain ⟨N, hN⟩ := tensorProjection_dot_nilpotent (fun _ : Fin 1 => μ) β hQ
    (SingleRed.blackPos β a)
  refine ⟨N, (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => μ) β).injective ?_⟩
  rw [map_pow, map_zero, ← hN]
  congr 1
  change SingleRed.cyclotomicProjection Q (fun _ : Fin 1 => μ) β (CycKLR.mk _ _ _ _ (x a)) = _
  rw [SingleRed.cyclotomicProjection, CycKLR.lift_mk, SingleRed.insertRed_x]
  change TensorProductAlgebra.mk Q _ β _ = TensorProductAlgebra.mk Q _ β
    (orderProjection Q _ β (affineCover Q _ β (x _)))
  rw [affineCover_x]
  congr 1
  apply Subtype.ext
  change _ = _ * StendhalAlgebraAllOrders.redOrderedIdem k Q _ β
  have h1 := SingleRed.redOrderedIdem_eq_one Q (fun _ : Fin 1 => μ) β
  have h2 : StendhalAlgebraAllOrders.x (SingleRed.blackPos β a) *
      StendhalAlgebraAllOrders.redOrderedIdem k Q (fun _ : Fin 1 => μ) β =
      StendhalAlgebraAllOrders.x (SingleRed.blackPos β a) := by
    rw [h1, mul_one]
  rw [h2]
  rfl
end Categorification.Stendhal
