/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtDualStandard
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Maps into a star dual as functionals on a tensor product

Let `A` be an algebra over a field `k` with an anti-automorphism `σ : A ≃+* Aᵐᵒᵖ`, `a ↦ ā`,
fixing the scalars, and let `ε : Aᵐᵒᵖ →+* A` satisfy `ε (op a) = ā`. For left `A`-modules `M`
and `Y`, let `M^ε` be `M` made a right module along `ε` (restriction of scalars). Currying
identifies `Hom_A(Y, M^⋆)` with the `k`-dual of `M^ε ⊗_A Y` (`starDualHomCurryEquiv`), so
`dim (M^ε ⊗_A Y) = dim Hom_A(Y, M^⋆)` (`finrank_tensorProductOver_restrictScalars`).

This is the bridge from `Hom` into the duals of Proposition 7.8 to `Tor₀` in B. Webster, *Knot
invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22.

## Main results

* `starDualHomCurryEquiv`: `Hom_A(Y, M^⋆) ≃ₗ[k] (M^ε ⊗_A Y)^*`.
* `finrank_tensorProductOver_restrictScalars`.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite StarDual

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {k A : Type} [Field k] [Ring A] [Algebra k A] (σ : A ≃+* Aᵐᵒᵖ)
  (ε : Aᵐᵒᵖ →+* A) (hε : ∀ a : A, ε (op a) = bar σ a)
  (hc : ∀ c : k, bar σ (algebraMap k A c) = algebraMap k A c)

set_option quotPrecheck false in
/-- `M` as a right module along `ε`. -/
local notation "⟪" M "⟫" => ((ModuleCat.restrictScalars ε).obj M : Type)

include hε hc in
/-- The scalar action on `M^ε` is that of `M`. -/
theorem reflectAlong_algebraMap_smul (M : ModuleCat.{0} A) (c : k) (m : M) :
    ε (op (algebraMap k A c)) • m = algebraMap k A c • m := by
  rw [hε, hc]

include hε in
/-- The balanced pairing `M^ε × Y → k` of a map `Y → M^⋆`. -/
def starDualPairing {M Y : ModuleCat.{0} A} (f : Y ⟶ starDualObj k σ M) :
    TensorProductOver A ⟪M⟫ Y →+ k :=
  TensorProductOver.lift
    { toFun := fun m => { toFun := fun y => toDual (k := k) (σ := σ) (f.hom y) m
                          map_zero' := by rw [map_zero]; rfl
                          map_add' := fun y y' => by rw [map_add]; rfl }
      map_zero' := AddMonoidHom.ext fun y => map_zero (toDual (k := k) (σ := σ) (f.hom y))
      map_add' := fun m m' => AddMonoidHom.ext fun y =>
        map_add (toDual (k := k) (σ := σ) (f.hom y)) m m' }
    (fun a m y => by
      change toDual (f.hom y) (ε (op a) • m) = toDual (f.hom (a • y)) m
      rw [LinearMap.map_smul, hε]
      rfl)

theorem starDualPairing_tmul {M Y : ModuleCat.{0} A} (f : Y ⟶ starDualObj k σ M)
    (m : M) (y : Y) :
    starDualPairing σ ε hε f (TensorProductOver.tmul A (@id ⟪M⟫ m) y) =
      toDual (k := k) (σ := σ) (f.hom y) m := rfl

include hε hc in
/-- The `k`-dual of `M^ε ⊗_A Y` back to maps `Y → M^⋆`. -/
def starDualUncurry {M Y : ModuleCat.{0} A}
    (g : Module.Dual k (TensorProductOver A ⟪M⟫ Y)) : Y ⟶ starDualObj k σ M :=
  ModuleCat.ofHom
    { toFun := fun y => ofDual
        { toFun := fun m => g (TensorProductOver.tmul A (@id ⟪M⟫ m) y)
          map_add' := fun m m' => by
            rw [show (@id ⟪M⟫ (m + m')) = (@id ⟪M⟫ m) + (@id ⟪M⟫ m') from rfl,
              TensorProductOver.add_tmul, map_add]
          map_smul' := fun c m => by
            rw [RingHom.id_apply, ← LinearMap.map_smul, TensorProductOver.smul_tmul]
            congr 2
            exact (reflectAlong_algebraMap_smul σ ε hε hc M c m).symm }
      map_add' := fun y y' => LinearMap.ext fun m => by
        change g _ = g _ + g _
        rw [TensorProductOver.tmul_add, map_add]
      map_smul' := fun a y => LinearMap.ext fun m => by
        change g (TensorProductOver.tmul A (@id ⟪M⟫ m) (a • y)) =
          g (TensorProductOver.tmul A (@id ⟪M⟫ (bar σ a • m)) y)
        rw [← TensorProductOver.op_smul_tmul]
        congr 2
        change ε (op a) • m = _
        rw [hε]
        rfl }

theorem starDualUncurry_apply {M Y : ModuleCat.{0} A}
    (g : Module.Dual k (TensorProductOver A ⟪M⟫ Y)) (y : Y) (m : M) :
    toDual (k := k) (σ := σ) ((starDualUncurry σ ε hε hc g).hom y) m =
      g (TensorProductOver.tmul A (@id ⟪M⟫ m) y) := rfl

include hε hc in
/-- **Currying** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the passage from
`Hom` into the dual to `Tor₀`): `Hom_A(Y, M^⋆) ≃ₗ[k] (M^ε ⊗_A Y)^*`, where `M^ε` is `M` as a
right module along `ε` with `ε (op a) = ā`. -/
def starDualHomCurryEquiv (M Y : ModuleCat.{0} A) :
    (Y ⟶ starDualObj k σ M) ≃ₗ[k] Module.Dual k (TensorProductOver A ⟪M⟫ Y) where
  toFun f :=
    { toFun := starDualPairing σ ε hε f
      map_add' := map_add _
      map_smul' := fun c z => by
        induction z using TensorProductOver.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul m y =>
          rw [TensorProductOver.smul_tmul, RingHom.id_apply]
          change toDual (k := k) (σ := σ) (f.hom y) (ε (op (algebraMap k A c)) • m) =
            c • toDual (k := k) (σ := σ) (f.hom y) m
          refine (congrArg (fun z => toDual (k := k) (σ := σ) (f.hom y) z)
            (reflectAlong_algebraMap_smul σ ε hε hc M c m)).trans ?_
          exact (toDual (k := k) (σ := σ) (f.hom y)).map_smul c m
        | add x z hx hz => rw [smul_add, map_add, map_add, hx, hz, smul_add] }
  invFun := starDualUncurry σ ε hε hc
  left_inv f := by
    ext y
    rfl
  right_inv g := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m y => rfl
    | add x z hx hz => rw [map_add, map_add, hx, hz]
  map_add' f f' := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m y => rfl
    | add x z hx hz => rw [map_add, map_add, hx, hz]
  map_smul' c f := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m y =>
      change toDual (k := k) (σ := σ) ((c • f).hom y) m =
        c • toDual (k := k) (σ := σ) (f.hom y) m
      change toDual (k := k) (σ := σ) (f.hom y) (bar σ (algebraMap k A c) • @id (M : Type) m) =
        c • toDual (k := k) (σ := σ) (f.hom y) m
      rw [hc]
      exact (toDual (k := k) (σ := σ) (f.hom y)).map_smul c m
    | add x z hx hz => rw [map_add, map_add, hx, hz]

include hε hc in
/-- **`dim (M^ε ⊗_A Y) = dim Hom_A(Y, M^⋆)`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22). -/
theorem finrank_tensorProductOver_restrictScalars (M Y : ModuleCat.{0} A) :
    Module.finrank k (TensorProductOver A ⟪M⟫ Y) =
      Module.finrank k (Y ⟶ starDualObj k σ M) :=
  (Subspace.dual_finrank_eq (K := k)).symm.trans
    (starDualHomCurryEquiv σ ε hε hc M Y).finrank_eq.symm

end Categorification
