/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.IndDecomp

/-!
# Induction of KLR modules is exact

Khovanov–Lauda I, arXiv:0803.4121v2, Proposition 2.16: `R(ν + ν') 1_{ν,ν'}` is a free right
`R(ν) ⊗ R(ν')`-module, so `Ind_{ν,ν'}` is exact. In terms of the shuffle decomposition
`indDecomp : Ind N ≅ ⊕_u N`, the induced map `1 ⊗ f` acts as `f` on every summand
(`indDecomp_mapRight`). Hence `1 ⊗ f` is injective when `f` is (`mapRight_injective_ind`) and
`Ind` preserves exactness in the middle (`exists_mapRight_eq_of_mapRight_eq_zero`).

This is used in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5.
-/

noncomputable section

namespace Categorification.KLR

open MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' : Multiset I} (hsym : KLRSymm Q)
  {N : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N]
  [IsScalarTower k (TensorKLR Q ν ν') N]
  {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (TensorKLR Q ν ν') N']
  [IsScalarTower k (TensorKLR Q ν ν') N']

/-- **`1 ⊗ f` acts as `f` on every shuffle summand.** -/
theorem indDecomp_mapRight (f : N →ₗ[TensorKLR Q ν ν'] N') (y : Ind Q ν ν' N)
    (u : TypeA.Shuffle (Seq.card_add' ν ν')) :
    indDecomp hsym N' (BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν')) f y) u =
      f (indDecomp hsym N y u) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp
  | tmul r n =>
    rw [BalancedTensor.mapRight_tmul, indDecomp_tmul, indDecomp_tmul, map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

include hsym in
/-- **Induction preserves injectivity.** -/
theorem mapRight_injective_ind {f : N →ₗ[TensorKLR Q ν ν'] N'} (hf : Function.Injective f) :
    Function.Injective
      (BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν'))
        (M := IndBimod Q ν ν') f) := by
  intro x y hxy
  apply (indDecomp hsym N).injective
  funext u
  apply hf
  rw [← indDecomp_mapRight hsym f x u, ← indDecomp_mapRight hsym f y u, hxy]

variable {N'' : Type*} [AddCommGroup N''] [Module k N''] [Module (TensorKLR Q ν ν') N'']
  [IsScalarTower k (TensorKLR Q ν ν') N'']

include hsym in
/-- **Induction preserves exactness in the middle.** -/
theorem exists_mapRight_eq_of_mapRight_eq_zero {f : N →ₗ[TensorKLR Q ν ν'] N'}
    {g : N' →ₗ[TensorKLR Q ν ν'] N''} (hfg : ∀ n', g n' = 0 → ∃ n, f n = n')
    {x : Ind Q ν ν' N'}
    (hx : BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν')) g x = 0) :
    ∃ y, BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν')) f y = x := by
  have hu : ∀ u, ∃ n, f n = indDecomp hsym N' x u := fun u => hfg _ (by
    rw [← indDecomp_mapRight hsym g x u, hx, map_zero, Pi.zero_apply])
  choose n hn using hu
  refine ⟨(indDecomp hsym N).symm n, ?_⟩
  apply (indDecomp hsym N').injective
  funext u
  rw [indDecomp_mapRight, LinearEquiv.apply_symm_apply, hn]

end KLRAlgebra

end Categorification.KLR
