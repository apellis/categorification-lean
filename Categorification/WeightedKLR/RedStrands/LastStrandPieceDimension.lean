/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentDimension
import Categorification.WeightedKLR.RedStrands.LastStrandDecomposition
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# Black-last pieces as restrictions

Webster, arXiv:1309.3796v3, proof of Proposition 5.5. The piece of a `T(ν)`-module `Y` where
the last strand is black of colour `j` (`lastStrandIdem (some j)`) is the restriction
`E_j Y = BlackRes j ν₀ Y` of `Y`, for `ν = j + ν₀`. This file records it in dimension form.

* `finrank_fixSub_lastStrandIdem_eq_of_equiv`: the transport statement, for `ν` with
  `j + ν₀ = ν` and a `k`-linear isomorphism `Y' ≃ Y` intertwining the action of `T(j + ν₀)` on
  `Y'` with that of `T(ν)` on `Y` through `castTensorProductAlgebra`.
* `finrank_fixSub_lastStrandIdem_some`: the case `ν = j + ν₀` itself.
* `finrank_blackRes_eq_finrank_res`: `BlackRes j ν₀ Y` and the restriction
  `Res (appendBlackNU j ν₀) Y` have the same dimension.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}

/-- **Black-last pieces, transported along a content equality** (Webster, arXiv:1309.3796v3,
proof of Proposition 5.5). Let `j + ν₀ = ν`, `Y` a `T(ν)`-module and `Y'` a `T(j + ν₀)`-module
with a `k`-linear isomorphism `e : Y' ≃ Y` such that `e (t • y) = cast t • e y`. Then the piece
of `Y` where the last strand is black of colour `j` has the dimension of `E_j Y'`. -/
theorem finrank_fixSub_lastStrandIdem_eq_of_equiv (j : I) {ν₀ ν : Multiset I}
    (h : (Singleton.singleton j : Multiset I) + ν₀ = ν)
    (Y' : Type*) [AddCommGroup Y'] [Module k Y']
    [Module (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀)) Y']
    [IsScalarTower k (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀)) Y']
    (Y : Type*) [AddCommGroup Y] [Module k Y] [Module (TensorProductAlgebra k Q Λ ν) Y]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ν) Y] (e : Y' ≃ₗ[k] Y)
    (he : ∀ (t : TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀))
      (y : Y'), e (t • y) = castTensorProductAlgebra Q Λ h t • e y) :
    Module.finrank k (fixSub k Y (lastStrandIdem Q Λ ν (some j))) =
      Module.finrank k (BlackRes (Q := Q) (Λ := Λ) j ν₀ Y') := by
  rw [lastStrandIdem_some Q Λ ν j ν₀ h]
  have hmap : (fixSub k Y' (appendBlack Q Λ j ν₀ 1)).map (e : Y' →ₗ[k] Y) =
      fixSub k Y (castTensorProductAlgebra Q Λ h (appendBlack Q Λ j ν₀ 1)) := by
    ext z
    rw [Submodule.mem_map_equiv, mem_fixSub, mem_fixSub]
    constructor
    · intro hz
      have := congrArg e hz
      rw [he, LinearEquiv.apply_symm_apply] at this
      exact this
    · intro hz
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply]
      exact hz
  exact (e.ofSubmodules _ _ hmap).finrank_eq.symm

/-- **Black-last pieces** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5): for a
`T(j + ν₀)`-module `Y`, the piece where the last strand is black of colour `j` has the
dimension of `E_j Y = BlackRes j ν₀ Y`. -/
theorem finrank_fixSub_lastStrandIdem_some (j : I) (ν₀ : Multiset I)
    (Y : Type*) [AddCommGroup Y] [Module k Y]
    [Module (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀)) Y]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀)) Y] :
    Module.finrank k (fixSub k Y
        (lastStrandIdem Q Λ ((Singleton.singleton j : Multiset I) + ν₀) (some j))) =
      Module.finrank k (BlackRes (Q := Q) (Λ := Λ) j ν₀ Y) :=
  finrank_fixSub_lastStrandIdem_eq_of_equiv j rfl Y Y (LinearEquiv.refl k Y)
    (fun _ _ => rfl)

/-- For an idempotent `a`, the piece `a X` of `IdempotentDimension` is the fixed subspace. -/
theorem idemPiece_eq_fixSub {A : Type*} [Ring A] [Algebra k A] (X : Type*) [AddCommGroup X]
    [Module A X] [Module k X] [IsScalarTower k A X] {a : A} (ha : IsIdempotentElem a) :
    idemPiece k X a = fixSub k X a := by
  ext x
  rw [mem_idemPiece_iff_of_idem k X ha, mem_fixSub]

section Res

universe u

variable {I k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}

/-- **`E_j Y` as a restriction** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5): the
fixed part `BlackRes j ν₀ Y` of `appendBlack 1` and the restriction of `Y` along
`appendBlackNU j ν₀`, with scalars through `T(ν₀)`, have the same dimension. -/
theorem finrank_blackRes_eq_finrank_res (j : I) (ν₀ : Multiset I)
    (Y : Type*) [AddCommGroup Y] [Module k Y]
    [Module (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀)) Y]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + ν₀)) Y] :
    letI := Res.moduleK k (appendBlackNU (Q := Q) (Λ := Λ) j ν₀) Y
    Module.finrank k (BlackRes (Q := Q) (Λ := Λ) j ν₀ Y) =
      Module.finrank k (Res (appendBlackNU (Q := Q) (Λ := Λ) j ν₀) Y) := by
  let := Res.moduleK k (appendBlackNU (Q := Q) (Λ := Λ) j ν₀) Y
  let := Res.isScalarTowerK k (appendBlackNU (Q := Q) (Λ := Λ) j ν₀) Y
  have hidem : IsIdempotentElem (appendBlack Q Λ j ν₀ 1) := by
    rw [IsIdempotentElem, ← map_mul, one_mul]
  have hφ : ∀ c : k, appendBlackNU (Q := Q) (Λ := Λ) j ν₀ (algebraMap k _ c) =
      algebraMap k _ c * appendBlackNU (Q := Q) (Λ := Λ) j ν₀ 1 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def]
    exact (appendBlack Q Λ j ν₀).map_smul c 1
  rw [finrank_eq_pieceDim_one (A := TensorProductAlgebra k Q Λ ν₀) k
      (Res (appendBlackNU (Q := Q) (Λ := Λ) j ν₀) Y), pieceDim_res k _ hφ Y,
    pieceDim]
  exact congrArg (fun p : Submodule k Y => Module.finrank k p)
    (idemPiece_eq_fixSub Y hidem).symm

end Res

end Categorification.Stendhal
