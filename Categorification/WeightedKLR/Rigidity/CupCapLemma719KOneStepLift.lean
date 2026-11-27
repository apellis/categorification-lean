/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutOneStep

/-!
# The universal property of the one-step partial standardization with three blocks

Webster, arXiv:1309.3796v3, §5.1 (partial standardization with several blocks, after
Definition 5.4), in the form used in the proof of Lemma 7.19 (K). For a module `N` over the
affine KLR algebras of three blocks and a representation `σ` of the affine KLR algebra of all
strands on `X` in which the ordered loadings `F` sum to `1`, a map `f : N → X` intertwining the
triple concatenation `ι₃` induces a map `Ind₃ N / (part supported off F) → X`
(`ind3QuotLift`), `m ⊗ n ↦ σ(m) f(n)`, linear over the affine algebra
(`ind3QuotLift_smul`). The partial standardization `BlocksStandard` is this quotient
(`blocksStandardOneStepEquiv`), so this is how maps out of `S_+` are built.

## Main definitions

* `KLR.KLRAlgebra.IsInd3InputHom`: the intertwining condition.
* `KLR.KLRAlgebra.ind3Lift`, `KLR.KLRAlgebra.ind3QuotLift`: the induced maps.

## Main results

* `KLR.KLRAlgebra.ind3Lift_tmul`, `ind3Lift_smul`, `ind3QuotLift_mk`, `ind3QuotLift_smul`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open scoped TensorProduct
open MulOpposite Categorification.Stendhal

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' ν'' : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR3 Q ν ν' ν'') N]
  {X : Type*} [AddCommGroup X] [Module k X]
  (σ : KLRAlgebra k Q (ν + (ν' + ν'')) →ₐ[k] Module.End k X)

/-- **The intertwining condition** for the one-step induction: the three blocks act on `N`
and, through the triple concatenation, on `X`. -/
def IsInd3InputHom (f : N →ₗ[k] X) : Prop :=
  ∀ (t : TensorKLR3 Q ν ν' ν'') (n : N), f (t • n) = σ (concat3 Q ν ν' ν'' t) (f n)

/-- The bilinear map `m ⊗ n ↦ σ(m) f(n)`. -/
def ind3LiftBil (f : N →ₗ[k] X) : IndBimod3 Q ν ν' ν'' →ₗ[k] N →ₗ[k] X :=
  LinearMap.mk₂ k (fun m n => σ (m : KLRAlgebra k Q (ν + (ν' + ν''))) (f n))
    (fun m m' n => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c m n => by simp only [Submodule.coe_smul_of_tower, map_smul, LinearMap.smul_apply])
    (fun m n n' => by simp only [map_add])
    (fun c m n => by simp only [map_smul])

variable {σ}

/-- **The map of the one-step induced module** induced by an intertwining map. -/
def ind3Lift (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) : Ind3 Q ν ν' ν'' N →ₗ[k] X :=
  BalancedTensor.lift (ind3LiftBil σ f) fun m t n => by
    change σ ((m : KLRAlgebra k Q (ν + (ν' + ν''))) * concat3 Q ν ν' ν'' t) (f n) =
      σ (m : KLRAlgebra k Q (ν + (ν' + ν''))) (f (t • n))
    rw [map_mul, Module.End.mul_apply, hf]

theorem ind3Lift_tmul (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) (m : IndBimod3 Q ν ν' ν'')
    (n : N) :
    ind3Lift f hf (BalancedTensor.tmul m n : Ind3 Q ν ν' ν'' N) =
      σ (m : KLRAlgebra k Q (ν + (ν' + ν''))) (f n) := rfl

/-- The map of the one-step induced module is linear over the affine algebra of all strands. -/
theorem ind3Lift_smul (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f)
    (z : KLRAlgebra k Q (ν + (ν' + ν''))) (y : Ind3 Q ν ν' ν'' N) :
    ind3Lift f hf (z • y) = σ z (ind3Lift f hf y) := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul m n =>
    rw [BalancedTensor.smul_tmul', ind3Lift_tmul, ind3Lift_tmul, Submodule.coe_smul,
      smul_eq_mul, map_mul, Module.End.mul_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]

variable (F : Finset (Seq (ν + (ν' + ν''))))

/-- The map of the one-step induced module vanishes on the part supported off `F`, when the
loadings of `F` sum to `1` on `X`. -/
theorem ind3Lift_excluded (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) (hF : σ (eSum Q F) = 1) :
    excludedSpace (Algebra.lsmul k k (Ind3 Q ν ν' ν'' N) :
        KLRAlgebra k Q (ν + (ν' + ν'')) →ₐ[k] Module.End k (Ind3 Q ν ν' ν'' N)) F ≤
      LinearMap.ker (ind3Lift f hf) := by
  intro y hy
  have hy' : (eSum Q F : KLRAlgebra k Q (ν + (ν' + ν''))) • y = 0 := hy
  have h1 : ind3Lift f hf y = σ (eSum Q F) (ind3Lift f hf y) := by
    rw [hF, Module.End.one_apply]
  rw [LinearMap.mem_ker, h1, ← ind3Lift_smul, hy', map_zero]

/-- **The map of the one-step partial standardization** induced by an intertwining map. -/
def ind3QuotLift (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) (hF : σ (eSum Q F) = 1) :
    (Ind3 Q ν ν' ν'' N ⧸ excludedSpace (Algebra.lsmul k k (Ind3 Q ν ν' ν'' N) :
        KLRAlgebra k Q (ν + (ν' + ν'')) →ₐ[k] Module.End k (Ind3 Q ν ν' ν'' N)) F) →ₗ[k] X :=
  (excludedSpace _ F).liftQ (ind3Lift f hf) (ind3Lift_excluded F f hf hF)

theorem ind3QuotLift_mk (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) (hF : σ (eSum Q F) = 1)
    (y : Ind3 Q ν ν' ν'' N) :
    ind3QuotLift F f hf hF (Submodule.Quotient.mk y) = ind3Lift f hf y := rfl

/-- The map of the one-step partial standardization is linear over the affine algebra. -/
theorem ind3QuotLift_smul (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) (hF : σ (eSum Q F) = 1)
    (z : KLRAlgebra k Q (ν + (ν' + ν''))) (y : Ind3 Q ν ν' ν'' N) :
    ind3QuotLift F f hf hF (Submodule.Quotient.mk (z • y)) =
      σ z (ind3QuotLift F f hf hF (Submodule.Quotient.mk y)) :=
  ind3Lift_smul f hf z y

/-- The unit `n ↦ 1_{ν,ν',ν''} ⊗ n` of the one-step induction. -/
def ind3Unit (n : N) : Ind3 Q ν ν' ν'' N :=
  BalancedTensor.tmul (⟨oneConcat3 Q ν ν' ν'', by
    rw [Graded.mem_leftIdeal]; exact oneConcat3_idem⟩ : IndBimod3 Q ν ν' ν'') n

/-- **The induced map restricts to `f` on the unit.** -/
theorem ind3Lift_unit (f : N →ₗ[k] X) (hf : IsInd3InputHom σ f) (n : N) :
    ind3Lift f hf (ind3Unit n) = f n := by
  change σ (concat3 Q ν ν' ν'' 1) (f n) = f n
  rw [← hf, one_smul]

/-- An element `m ⊗ n` of the one-step induction is `m` times the unit. -/
theorem tmul_eq_smul_ind3Unit (m : IndBimod3 Q ν ν' ν'') (n : N) :
    (BalancedTensor.tmul m n : Ind3 Q ν ν' ν'' N) =
      (m : KLRAlgebra k Q (ν + (ν' + ν''))) • ind3Unit n := by
  rw [ind3Unit, BalancedTensor.smul_tmul']
  congr 1
  exact Subtype.ext (m.2).symm

/-- **A map out of the one-step induction that is linear over the affine algebra is determined
by its values on the unit.** -/
theorem ind3_ext {g g' : Ind3 Q ν ν' ν'' N →ₗ[k] X} (hg : ∀ z y, g (z • y) = σ z (g y))
    (hg' : ∀ z y, g' (z • y) = σ z (g' y)) (he : ∀ n, g (ind3Unit n) = g' (ind3Unit n)) :
    g = g' := by
  refine LinearMap.ext fun y => ?_
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m n => rw [tmul_eq_smul_ind3Unit, hg, hg', he]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The unit of the one-step induction, as a linear map. -/
def ind3UnitLin : N →ₗ[k] Ind3 Q ν ν' ν'' N where
  toFun := ind3Unit
  map_add' n n' := BalancedTensor.tmul_add _ n n'
  map_smul' c n := BalancedTensor.tmul_smul c _ n

/-- The unit is intertwining: `ι₃(t) (1 ⊗ n) = 1 ⊗ t n`. -/
theorem concat3_smul_ind3Unit (t : TensorKLR3 Q ν ν' ν'') (n : N) :
    concat3 Q ν ν' ν'' t • (ind3Unit n : Ind3 Q ν ν' ν'' N) = ind3Unit (t • n) := by
  rw [ind3Unit, ind3Unit, ← BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul']
  congr 1
  refine Subtype.ext ?_
  rw [coe_op_smul3, Submodule.coe_smul, smul_eq_mul, unop_op]
  exact (oneConcat3_mul_concat3 t).trans (concat3_mul_oneConcat3 t).symm |>.symm

/-- The restriction to the unit of a map linear over the affine algebra is intertwining. -/
theorem isInd3InputHom_comp_unit {g : Ind3 Q ν ν' ν'' N →ₗ[k] X}
    (hg : ∀ z y, g (z • y) = σ z (g y)) : IsInd3InputHom σ (g.comp ind3UnitLin) := by
  intro t n
  change g (ind3Unit (t • n)) = σ (concat3 Q ν ν' ν'' t) (g (ind3Unit n))
  rw [← hg, concat3_smul_ind3Unit]

end Categorification.KLR.KLRAlgebra
