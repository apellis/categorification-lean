/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastStrandPieceDimension
import Categorification.WeightedKLR.RedStrands.Prop55CountRedEmpty
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossLeft

/-!
# Transport of dimensions along equalities of black weights

Webster, arXiv:1309.3796v2, proof of Proposition 5.5. The dimension count (5.13)–(5.14) compares
pieces of modules over tensor product algebras `T(ν)` and `T(ν')` for black weights `ν = ν'`
that are equal but not syntactically equal. This file records the transport statements used
there.

* `finrank_restrictScalars_of_tower`: for a `T`-module `X` with a compatible `k`-structure,
  `RestrictScalars k T X` and `X` have the same dimension.
* `blackResEquivRes`: `BlackRes j μ M` is the restriction `Res (appendBlackNU j μ) M`.
* `finrank_fixSub_lastStrandIdem_transport`, `finrank_indK_transport`,
  `finrank_fixSub_indK_transport`: last-strand pieces, inductions `Fᵢ` and their pieces are
  transported along a `k`-linear isomorphism intertwining the actions through
  `castTensorProductAlgebra`.
* `finrank_fixSub_lastStrandIdem_eq_res`: the piece where the last strand is black of colour
  `j` is the restriction along `appendBlackNUOfEq j h`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Scalars

variable {k T X : Type*} [Field k] [Ring T] [Algebra k T] [AddCommGroup X] [Module T X]
  [Module k X] [IsScalarTower k T X]

variable (k T X) in
/-- `RestrictScalars k T X` is `X` as a `k`-module when the `k`-structure of `X` is compatible
with `T`. -/
def restrictScalarsEquivOfTower : RestrictScalars k T X ≃ₗ[k] X :=
  (RestrictScalars.addEquiv k T X).toLinearEquiv fun c x => by
    rw [RestrictScalars.smul_def, AddEquiv.apply_symm_apply, algebraMap_smul]

/-- `RestrictScalars k T X` and `X` have the same dimension over `k`. -/
theorem finrank_restrictScalars_of_tower :
    Module.finrank k (RestrictScalars k T X) = Module.finrank k X :=
  (restrictScalarsEquivOfTower k T X).finrank_eq

end Scalars

section Tensor

universe u

variable {I k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}

variable (Q Λ) in
/-- `BlackRes j μ M` is the restriction of `M` along `appendBlackNU j μ`. -/
def blackResEquivRes (j : I) (μ : Multiset I) (M : Type*) [AddCommGroup M] [Module k M]
    [Module (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + μ)) M]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + μ)) M] :
    BlackRes (Q := Q) (Λ := Λ) j μ M ≃ₗ[TensorProductAlgebra k Q Λ μ]
      Res (appendBlackNU (Q := Q) (Λ := Λ) j μ) M where
  toFun z := Res.mk z.1 (mem_fixSub.1 z.2)
  invFun r := ⟨r.val, mem_fixSub.2 r.prop⟩
  map_add' _ _ := Res.ext rfl
  map_smul' _ _ := Res.ext rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `k`-linear isomorphism intertwining the actions of `T(ν)` and `T(ν')` through
`castTensorProductAlgebra h`, for `h : ν = ν'`, as a `T(ν)`-linear isomorphism. -/
def castLinearEquiv {ν : Multiset I} (X X' : Type*) [AddCommGroup X] [Module k X]
    [Module (TensorProductAlgebra k Q Λ ν) X] [AddCommGroup X'] [Module k X']
    [Module (TensorProductAlgebra k Q Λ ν) X'] (e : X ≃ₗ[k] X')
    (he : ∀ (t : TensorProductAlgebra k Q Λ ν) (x : X),
      e (t • x) = castTensorProductAlgebra Q Λ (rfl : ν = ν) t • e x) :
    X ≃ₗ[TensorProductAlgebra k Q Λ ν] X' :=
  { e with map_smul' := fun t x => he t x }

/-- **Pieces along an equality of black weights**: a `k`-linear isomorphism `e : X ≃ X'`
intertwining `T(ν)` and `T(ν')` through `castTensorProductAlgebra h` identifies the pieces of
`X` and `X'` cut out by the last-strand idempotents. -/
theorem finrank_fixSub_lastStrandIdem_transport {ν ν' : Multiset I} (h : ν = ν')
    (X X' : Type*) [AddCommGroup X] [Module k X] [Module (TensorProductAlgebra k Q Λ ν) X]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ν) X] [AddCommGroup X'] [Module k X']
    [Module (TensorProductAlgebra k Q Λ ν') X'] [IsScalarTower k (TensorProductAlgebra k Q Λ ν') X']
    (e : X ≃ₗ[k] X')
    (he : ∀ (t : TensorProductAlgebra k Q Λ ν) (x : X),
      e (t • x) = castTensorProductAlgebra Q Λ h t • e x) (b : Option I) :
    Module.finrank k (fixSub k X' (lastStrandIdem Q Λ ν' b)) =
      Module.finrank k (fixSub k X (lastStrandIdem Q Λ ν b)) := by
  subst h
  exact (fixSubLinearCongr (castLinearEquiv X X' e he) _).finrank_eq.symm

/-- **`Fᵢ` along an equality of black weights**: the inductions of `X` and `X'` have the same
dimension. -/
theorem finrank_indK_transport (i : I) {ν ν' : Multiset I} (h : ν = ν')
    (X X' : Type u) [AddCommGroup X] [Module k X] [Module (TensorProductAlgebra k Q Λ ν) X]
    [AddCommGroup X'] [Module k X'] [Module (TensorProductAlgebra k Q Λ ν') X']
    (e : X ≃ₗ[k] X')
    (he : ∀ (t : TensorProductAlgebra k Q Λ ν) (x : X),
      e (t • x) = castTensorProductAlgebra Q Λ h t • e x) :
    Module.finrank k (IndK k X' (appendBlackNU (Q := Q) (Λ := Λ) i ν')) =
      Module.finrank k (IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν)) := by
  subst h
  let E : IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Singleton.singleton i : Multiset I) + ν)] IndK k X' (appendBlackNU (Q := Q) (Λ := Λ) i ν) :=
    Ind.mapEquiv (castLinearEquiv X X' e he)
  exact (E.restrictScalars k).finrank_eq.symm

/-- **Pieces of `Fᵢ` along an equality of black weights.** -/
theorem finrank_fixSub_indK_transport (i : I) {ν ν' : Multiset I} (h : ν = ν')
    (X X' : Type u) [AddCommGroup X] [Module k X] [Module (TensorProductAlgebra k Q Λ ν) X]
    [AddCommGroup X'] [Module k X'] [Module (TensorProductAlgebra k Q Λ ν') X']
    (e : X ≃ₗ[k] X')
    (he : ∀ (t : TensorProductAlgebra k Q Λ ν) (x : X),
      e (t • x) = castTensorProductAlgebra Q Λ h t • e x) (b : Option I) :
    Module.finrank k (fixSub k (IndK k X' (appendBlackNU (Q := Q) (Λ := Λ) i ν'))
        (lastStrandIdem Q Λ ((Singleton.singleton i : Multiset I) + ν') b)) =
      Module.finrank k (fixSub k (IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν))
        (lastStrandIdem Q Λ ((Singleton.singleton i : Multiset I) + ν) b)) := by
  subst h
  let E : IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Singleton.singleton i : Multiset I) + ν)] IndK k X' (appendBlackNU (Q := Q) (Λ := Λ) i ν) :=
    Ind.mapEquiv (castLinearEquiv X X' e he)
  exact (fixSubLinearCongr E _).finrank_eq.symm

/-- **The black-last piece as a restriction**, for a black weight given by an equality
`h : j + μ = ν` (Webster, arXiv:1309.3796v2, proof of Proposition 5.5). -/
theorem finrank_fixSub_lastStrandIdem_eq_res (j : I) {μ ν : Multiset I}
    (h : (Singleton.singleton j : Multiset I) + μ = ν) (Y : Type*) [AddCommGroup Y] [Module k Y]
    [Module (TensorProductAlgebra k Q Λ ν) Y] [IsScalarTower k (TensorProductAlgebra k Q Λ ν) Y] :
    Module.finrank k (fixSub k Y (lastStrandIdem Q Λ ν (some j))) =
      Module.finrank k (RestrictScalars k (TensorProductAlgebra k Q Λ μ)
        (Res (appendBlackNUOfEq Q Λ j h) Y)) := by
  subst h
  refine (finrank_fixSub_lastStrandIdem_some j μ Y).trans
    ((finrank_blackRes_eq_finrank_res j μ Y).trans ?_)
  let := Res.moduleK k (appendBlackNU (Q := Q) (Λ := Λ) j μ) Y
  have := Res.isScalarTowerK k (appendBlackNU (Q := Q) (Λ := Λ) j μ) Y
  exact finrank_restrictScalars_of_tower.symm

end Tensor

end Categorification.Stendhal
