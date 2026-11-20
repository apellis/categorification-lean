/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ConcatAssoc
import Categorification.Algebra.BalancedTensorTransport

/-!
# Transport of induced modules along equalities of weights

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6: the induction functor `Ind_{ν,ν'}` depends on the
weights `ν`, `ν'` only up to the canonical isomorphisms `castKLR`. Equal but not definitionally
equal weights arise when the weights of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, §5 (the parabolic loadings of the proof of Proposition 5.5) are
compared with weights of the form `ν₀ + i`.

## Main results

* `KLRAlgebra.castTensor` : the isomorphism `R(ν₁) ⊗ R(ν₁') ≃ R(ν₂) ⊗ R(ν₂')`, and
  `castKLR_concat` : it intertwines `ι_{ν,ν'}` with `castKLR`.
* `KLRAlgebra.castBimod` : the isomorphism `R(ν₁ + ν₁') 1_{ν₁,ν₁'} ≃ R(ν₂ + ν₂') 1_{ν₂,ν₂'}`.
* `KLRAlgebra.indCast` : a `k`-linear isomorphism `N₁ ≃ N₂`, semilinear along `castTensor`,
  induces `Ind_{ν₁,ν₁'} N₁ ≃ Ind_{ν₂,ν₂'} N₂`, semilinear along `castKLR`
  (`indCast_smul`).
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open MulOpposite

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν₁ ν₁' ν₂ ν₂' : Multiset I}

variable (Q) in
/-- The isomorphism `R(ν₁) ⊗ R(ν₁') ≃ R(ν₂) ⊗ R(ν₂')` for `ν₁ = ν₂`, `ν₁' = ν₂'`. -/
def castTensor (h : ν₁ = ν₂) (h' : ν₁' = ν₂') :
    TensorKLR Q ν₁ ν₁' ≃ₐ[k] TensorKLR Q ν₂ ν₂' := by
  subst h h'; exact AlgEquiv.refl

theorem castTensor_tmul (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (a : KLRAlgebra k Q ν₁)
    (b : KLRAlgebra k Q ν₁') : castTensor Q h h' (a ⊗ₜ b) = castKLR Q h a ⊗ₜ castKLR Q h' b := by
  subst h h'; rfl

@[simp] theorem castTensor_rfl (t : TensorKLR Q ν₁ ν₁') : castTensor Q rfl rfl t = t := rfl

theorem castTensor_symm_apply (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (t : TensorKLR Q ν₂ ν₂') :
    (castTensor Q h h').symm t = castTensor Q h.symm h'.symm t := by
  subst h h'; rfl

omit [DecidableEq I] in
theorem add_eq_add_of_eq (h : ν₁ = ν₂) (h' : ν₁' = ν₂') : ν₁ + ν₁' = ν₂ + ν₂' := by rw [h, h']

/-- `castKLR` intertwines the inclusions `ι_{ν,ν'}`. -/
theorem castKLR_concat (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (t : TensorKLR Q ν₁ ν₁') :
    castKLR Q (add_eq_add_of_eq h h') (concat Q ν₁ ν₁' t) =
      concat Q ν₂ ν₂' (castTensor Q h h' t) := by
  subst h h'; rfl

theorem castKLR_oneConcat (h : ν₁ = ν₂) (h' : ν₁' = ν₂') :
    castKLR Q (add_eq_add_of_eq h h') (oneConcat Q ν₁ ν₁') = oneConcat Q ν₂ ν₂' := by
  subst h h'; rfl

variable (Q) in
/-- The isomorphism `R(ν₁ + ν₁') 1_{ν₁,ν₁'} ≃ R(ν₂ + ν₂') 1_{ν₂,ν₂'}` induced by `castKLR`. -/
def castBimod (h : ν₁ = ν₂) (h' : ν₁' = ν₂') : IndBimod Q ν₁ ν₁' ≃ₗ[k] IndBimod Q ν₂ ν₂' := by
  subst h h'; exact LinearEquiv.refl k _

theorem coe_castBimod (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (m : IndBimod Q ν₁ ν₁') :
    ((castBimod Q h h' m : IndBimod Q ν₂ ν₂') : KLRAlgebra k Q (ν₂ + ν₂')) =
      castKLR Q (add_eq_add_of_eq h h') m := by
  subst h h'; rfl

theorem castBimod_op_smul (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (t : TensorKLR Q ν₁ ν₁')
    (m : IndBimod Q ν₁ ν₁') :
    castBimod Q h h' (op t • m) = op (castTensor Q h h' t) • castBimod Q h h' m := by
  subst h h'; rfl

theorem castBimod_smul (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (a : KLRAlgebra k Q (ν₁ + ν₁'))
    (m : IndBimod Q ν₁ ν₁') :
    castBimod Q h h' (a • m) = castKLR Q (add_eq_add_of_eq h h') a • castBimod Q h h' m := by
  subst h h'; rfl

section IndCast

variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (TensorKLR Q ν₁ ν₁') N₁]
  [AddCommGroup N₂] [Module k N₂] [Module (TensorKLR Q ν₂ ν₂') N₂]
  (h : ν₁ = ν₂) (h' : ν₁' = ν₂') (g : N₁ ≃ₗ[k] N₂)
  (hg : ∀ (t : TensorKLR Q ν₁ ν₁') (n : N₁), g (t • n) = castTensor Q h h' t • g n)

/-- **Transport of induced modules**: `Ind_{ν₁,ν₁'} N₁ ≃ Ind_{ν₂,ν₂'} N₂` for `ν₁ = ν₂`,
`ν₁' = ν₂'` and a `k`-linear isomorphism `N₁ ≃ N₂` intertwining the actions along
`castTensor`. -/
def indCast : Ind Q ν₁ ν₁' N₁ ≃ₗ[k] Ind Q ν₂ ν₂' N₂ :=
  BalancedTensor.changeRingEquiv (castTensor Q h h').toRingEquiv (castBimod Q h h') g
    (castBimod_op_smul h h') hg

@[simp] theorem indCast_tmul (m : IndBimod Q ν₁ ν₁') (n : N₁) :
    indCast h h' g hg (BalancedTensor.tmul m n) = BalancedTensor.tmul (castBimod Q h h' m) (g n) :=
  rfl

theorem indCast_symm_tmul (m : IndBimod Q ν₂ ν₂') (n : N₂) :
    (indCast h h' g hg).symm (BalancedTensor.tmul m n) =
      BalancedTensor.tmul ((castBimod Q h h').symm m) (g.symm n) := rfl

/-- `indCast` is semilinear along `castKLR`. -/
theorem indCast_smul (a : KLRAlgebra k Q (ν₁ + ν₁')) (y : Ind Q ν₁ ν₁' N₁) :
    indCast h h' g hg (a • y) = castKLR Q (add_eq_add_of_eq h h') a • indCast h h' g hg y :=
  BalancedTensor.changeRingEquiv_smul _ _ _ _ _ (castKLR Q (add_eq_add_of_eq h h')).toRingEquiv
    (castBimod_smul h h') a y

end IndCast

end KLRAlgebra

end Categorification.KLR
