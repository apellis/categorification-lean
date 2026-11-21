/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.IdempotentDimension
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Boundary idempotent pieces of modules over tensor product algebras

The boundary idempotents `e(s)` of Webster's tensor product algebra `T^λ`, indexed by the
loadings `s` whose red strands are in the order `λ_1, …, λ_ℓ`, form a complete family of
orthogonal idempotents. Hence the dimension of a finite-dimensional `T^λ`-module is the sum of
the dimensions of its pieces `e(s) M`. For a loading ending in a black strand, the piece of a
`T^{λ}`-module is a piece of its restriction along the map adjoining that black strand.

This is bookkeeping for the dimension count in Webster's proof of arXiv:1309.3796v3,
Proposition 5.5 (tracking issue #405).

## Main results

* `TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem`
* `TensorProductAlgebra.finrank_eq_sum_pieceDim_boundaryIdem`
* `TensorProductAlgebra.pieceDim_appendBlack_boundaryIdem`
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} {ℓ : ℕ} [DecidableEq I] {k : Type*} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

namespace TensorProductAlgebra

variable (Q Λ) (ν : Multiset I)

/-- The red-ordered loadings of black weight `ν`. -/
abbrev OrderedLoading : Type _ := {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}

noncomputable instance : Fintype (OrderedLoading (ℓ := ℓ) ν) := Fintype.ofFinite _

/-- The boundary idempotent `e(s)` of `T^λ`. -/
noncomputable def boundaryIdem (s : OrderedLoading (ℓ := ℓ) ν) :
    TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s.1 s.2)

theorem stendhal_e_mul_e (s t : OrderedLoading (ℓ := ℓ) ν) :
    (StendhalAlgebra.e s.1 s.2 * StendhalAlgebra.e t.1 t.2 : StendhalAlgebra k Q Λ ν) =
      if s = t then StendhalAlgebra.e s.1 s.2 else 0 := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e s.1 * StendhalAlgebraAllOrders.e t.1 = _
  rw [StendhalAlgebraAllOrders.e_mul_e]
  by_cases h : s = t
  · subst h; simp; rfl
  · have h' : s.1 ≠ t.1 := fun h'' => h (Subtype.ext h'')
    simp [h, h']

theorem stendhal_one :
    (1 : StendhalAlgebra k Q Λ ν) =
      ∑ s : OrderedLoading (ℓ := ℓ) ν, StendhalAlgebra.e s.1 s.2 := by
  classical
  apply Subtype.ext
  rw [KLR.Corner.val_one, KLR.Corner.val_sum]
  exact Finset.sum_subtype _ (fun s => by simp) _

/-- **The boundary idempotents of `T^λ` are a complete family of orthogonal idempotents.** -/
theorem completeOrthogonalIdempotents_boundaryIdem :
    CompleteOrthogonalIdempotents (boundaryIdem (k := k) Q Λ ν) where
  idem s := by
    change _ * _ = _
    rw [boundaryIdem, ← map_mul, stendhal_e_mul_e]
    simp
  ortho s t hst := by
    change _ * _ = _
    rw [boundaryIdem, boundaryIdem, ← map_mul, stendhal_e_mul_e]
    simp [hst]
  complete := by
    rw [← map_one (TensorProductAlgebra.mk Q Λ ν), stendhal_one, map_sum]
    rfl

variable {Q Λ ν}

/-- The dimension of a finite-dimensional `T^λ`-module is the sum of the dimensions of its
boundary pieces `e(s) M`. -/
theorem finrank_eq_sum_pieceDim_boundaryIdem (M : Type*) [AddCommGroup M]
    [Module (TensorProductAlgebra k Q Λ ν) M] [Module k M]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ν) M] [FiniteDimensional k M] :
    Module.finrank k M = ∑ s : OrderedLoading (ℓ := ℓ) ν, pieceDim k M (boundaryIdem Q Λ ν s) :=
  by
  classical
  exact finrank_eq_sum_pieceDim k (completeOrthogonalIdempotents_boundaryIdem Q Λ ν)

variable (i : I)

/-- The black-terminal boundary idempotent of `T^{λ}` with black weight `{i} + ν`. -/
noncomputable def blackTerminalIdem (s : OrderedLoading (ℓ := ℓ) ν) :
    OrderedLoading (ℓ := ℓ) ((Singleton.singleton i : Multiset I) + ν) :=
  ⟨appendBlackLoading i ν s.1, appendBlackLoading_ordered i ν s.1 s.2⟩

theorem appendBlack_boundaryIdem (s : OrderedLoading (ℓ := ℓ) ν) :
    appendBlack Q Λ i ν (boundaryIdem Q Λ ν s) =
      boundaryIdem Q Λ _ (blackTerminalIdem i s) :=
  appendBlack_mk_e Q Λ i ν s.1 s.2

/-- `appendBlack` as a nonunital ring map. -/
noncomputable abbrev appendBlackRingHom :
    TensorProductAlgebra k Q Λ ν →ₙ+*
      TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (appendBlack Q Λ i ν)

theorem appendBlackRingHom_algebraMap (c : k) :
    appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i (algebraMap k _ c) =
      algebraMap k _ c * appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i 1 := by
  rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def]
  exact (appendBlack Q Λ i ν).map_smul c 1

/-- **Black-terminal pieces.** For a loading ending in a black strand `i`, the piece `e(s i) M`
of a `T^λ`-module is the piece `e(s) Res M` of its restriction along the map adjoining the
black strand. -/
theorem pieceDim_appendBlack_boundaryIdem (M : Type*) [AddCommGroup M]
    [Module (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)) M]
    [Module k M]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)) M]
    (s : OrderedLoading (ℓ := ℓ) ν) :
    letI := Res.moduleK k (appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i) M
    letI := Res.isScalarTowerK k (appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i) M
    pieceDim k M (boundaryIdem Q Λ _ (blackTerminalIdem i s)) =
      pieceDim k (Res (appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i) M) (boundaryIdem Q Λ ν s) := by
  let := Res.moduleK k (appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i) M
  let := Res.isScalarTowerK k (appendBlackRingHom (Q := Q) (Λ := Λ) (ν := ν) i) M
  rw [pieceDim_res k _ (appendBlackRingHom_algebraMap i) M]
  exact congrArg (pieceDim k M) (appendBlack_boundaryIdem i s).symm

end TensorProductAlgebra

end Categorification.Stendhal
