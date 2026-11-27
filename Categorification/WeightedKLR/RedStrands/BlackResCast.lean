/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FactorAlgebraCast
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackNatural
import Categorification.WeightedKLR.RedStrands.BlockAlgebraCast
import Categorification.Algebra.BalancedTensorEndAction

/-!
# `Eᵢ` and the standardizations along equal weights

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. The functor `Eᵢ` (restriction along a terminal black strand of colour `i`) is
functorial (`blackResMap`, `blackResEnd`) and commutes with the transport of modules over the
tensor product algebras `T^λ(ν)` along equal weights (`blackResCast`). The standardization
`M ⊗_B S^L_α` of Definition 5.4 is unchanged, up to this transport, by the choice of the proof
that the blocks have weight `ν` (`leftStandardizationFamilyCast`), and the standardization
`S N` viewed over `T(i + (θ₀ + β))` is the transport of `S N` over `T(θ + β)`
(`lastStandardTEquiv`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra StendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}

section BlackRes

variable {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} (i : I)

variable {ν ν' : Multiset I}
  {M : Type} [AddCommGroup M] [Module k M]
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M]
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M]
  {M' : Type} [AddCommGroup M'] [Module k M']
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M']
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M']

local notation "Tfam" => TensorProductAlgebra k Q Λ
local notation "Ei" => BlackRes (Q := Q) (Λ := Λ) i

/-- **`Eᵢ` on maps.** -/
def blackResMap (g : M →ₗ[Tfam (({i} : Multiset I) + ν)] M') :
    Ei ν M →ₗ[Tfam ν] Ei ν M' where
  toFun m := ⟨g m.1, by rw [mem_fixSub, ← map_smul, (mem_fixSub).1 m.2]⟩
  map_add' m m' := Subtype.ext (map_add g m.1 m'.1)
  map_smul' t m := Subtype.ext (map_smul g _ m.1)

@[simp] theorem blackResMap_val (g : M →ₗ[Tfam (({i} : Multiset I) + ν)] M')
    (m : Ei ν M) : (blackResMap i g m).1 = g m.1 := rfl

variable (M) in
/-- **`Eᵢ` on endomorphisms**, as a map of algebras. -/
def blackResEnd : Module.End (Tfam (({i} : Multiset I) + ν)) M →ₐ[k]
    Module.End (Tfam ν) (Ei ν M) where
  toFun := blackResMap i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := LinearMap.ext fun m => Subtype.ext (by
    change (algebraMap k (Module.End (Tfam (({i} : Multiset I) + ν)) M) c) m.1 =
      ((algebraMap k (Module.End (Tfam ν) (Ei ν M)) c) m).1
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    rfl)

theorem familyRingCast_symm_appendBlack (h : ν = ν') (h' : ({i} : Multiset I) + ν = {i} + ν')
    (t : Tfam ν') :
    (familyRingCast (Tfam) h').symm (appendBlack Q Λ i ν' t) =
      appendBlack Q Λ i ν ((familyRingCast (Tfam) h).symm t) := by
  subst h
  rfl

variable (M) in
/-- **`Eᵢ` commutes with the transport along equal weights.** -/
def blackResCast (h : ν = ν') (h' : ({i} : Multiset I) + ν = {i} + ν') :
    Ei ν' (FamilyCast (Tfam) h' M) ≃ₗ[Tfam ν']
      FamilyCast (Tfam) h (Ei ν M) where
  toFun m := (⟨m.1, by
    have hm : (familyRingCast (Tfam) h').symm (appendBlack Q Λ i ν' 1) •
        (show M from m.1) = m.1 := (mem_fixSub).1 m.2
    rw [familyRingCast_symm_appendBlack i h h', map_one] at hm
    exact (mem_fixSub).2 hm⟩ : Ei ν M)
  invFun m := ⟨(m : Ei ν M).1, by
    refine (mem_fixSub).2 ?_
    change (familyRingCast (Tfam) h').symm (appendBlack Q Λ i ν' 1) •
        ((m : Ei ν M).1 : M) = (m : Ei ν M).1
    rw [familyRingCast_symm_appendBlack i h h', map_one]
    exact (mem_fixSub).1 (m : Ei ν M).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t m := Subtype.ext (by
    change (familyRingCast (Tfam) h').symm (appendBlack Q Λ i ν' t) •
        (show M from m.1) = appendBlack Q Λ i ν ((familyRingCast (Tfam) h).symm t) •
        (show M from m.1)
    rw [familyRingCast_symm_appendBlack i h h'])

end BlackRes

section LeftStandardization

variable {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  {c : Fin (ℓ + 1) → Multiset I} {ν ν' : Multiset I}
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ c)ᵐᵒᵖ M]

/-- **The standardization along equal weights**: changing the proof that the blocks have
weight `ν` transports `M ⊗_B S^L_α` along `ν = ν'`. -/
def leftStandardizationFamilyCast (h : ν = ν') (hb : blockPrefix c (ℓ + 1) = ν)
    (hb' : blockPrefix c (ℓ + 1) = ν') (hα : RootNonViolated (ν := ν) (blockRoot c))
    (hα' : RootNonViolated (ν := ν') (blockRoot c)) :
    LeftStandardization Q Λ c hb' hα' M ≃ₗ[TensorProductAlgebra k Q Λ ν']
      FamilyCast (TensorProductAlgebra k Q Λ) h (LeftStandardization Q Λ c hb hα M) := by
  subst h
  exact FamilyCast.rflEquiv _ _

end LeftStandardization

section LastStandard

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  (θ₀ β₀ : Multiset I) (hQ : KLRSymm Q)

theorem familyRingCast_symm_eq_castTensorProductAlgebra {ν ν' : Multiset I} (h : ν = ν')
    (t : TensorProductAlgebra k Q Λ ν') :
    (familyRingCast (TensorProductAlgebra k Q Λ) h).symm t =
      castTensorProductAlgebra Q Λ h.symm t := by
  subst h
  rfl

variable (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N]

/-- **`S N` over `T(i + (θ₀ + β))` is the transport of `S N` over `T(θ + β)`.** -/
def lastStandardTEquiv :
    LastStandardT Q Λ i θ₀ β₀ N hQ ≃ₗ[TensorProductAlgebra k Q Λ
        (({i} : Multiset I) + (θ₀ + ({i} + β₀)))]
      FamilyCast (TensorProductAlgebra k Q Λ) (lastBlack_weight i θ₀ β₀).symm
        (ParabolicStandardT Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀) N hQ) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t m := by
    change lastStandardTAction Q Λ i θ₀ β₀ N hQ t m =
      parabolicStandardAction Q Λ _ _ N hQ ((familyRingCast (TensorProductAlgebra k Q Λ)
        (lastBlack_weight i θ₀ β₀).symm).symm t) m
    rw [familyRingCast_symm_eq_castTensorProductAlgebra]
    rfl

end LastStandard

end Categorification.Stendhal
