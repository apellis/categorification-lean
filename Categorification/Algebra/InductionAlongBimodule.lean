/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.BalancedTensorAssoc
import Categorification.Algebra.HomTensorComp

/-!
# Restriction of induction and induction of restriction as tensor products with bimodules

Let `φ : A →ₙ+* B` be a nonunital ring map with idempotent `e = φ 1`. The composite
`Res_φ ∘ Ind_φ`, `N ↦ e (B e ⊗_A N)`, is tensoring with the `(A, A)`-bimodule `e B e`, realized
here as `Res φ (Ind A φ)` (`resIndTensor`). Dually, for `ψ : A' →ₙ+* A` with idempotent `e'`,
the composite `Ind_ψ ∘ Res_ψ`, `N ↦ A e' ⊗_{A'} e' N`, is tensoring with the `(A, A)`-bimodule
`A e' ⊗_{A'} e' A`, realized as `Ind (Res ψ A) ψ` (`indResTensor`). Both identifications are
natural in `N`, and the right `A`-actions on the bimodules are the ones induced from the right
regular action of `A`.

Hence an isomorphism of `(A, A)`-bimodules between such bimodules gives an isomorphism of the
composite functors on every module. This is how the commutation relations of the quantum group
on projective modules over the tensor product algebras give the commutation relations on all
modules, used in the proof of Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Proposition 5.5.

## Main definitions

* `Res.rightModule`: a right action commuting with `B` passes to `Res φ M`.
* `Ind.rightModule`: a right action on `N` commuting with `A` passes to `Ind N φ`.
* `resIndTensor`: `Res_φ (Ind_φ N) ≅ Res_φ (Ind_φ A) ⊗_A N`.
* `indResTensor`: `Ind_ψ (Res_ψ N) ≅ Ind_ψ (Res_ψ A) ⊗_A N`.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u v w

/-! ### Right actions on restricted and induced modules -/

section RightRes

variable {A : Type u} [Ring A] {B : Type v} [Ring B] (φ : A →ₙ+* B) {C : Type*} [Ring C]
  (M : Type w) [AddCommGroup M] [Module B M] [Module Cᵐᵒᵖ M] [SMulCommClass B Cᵐᵒᵖ M]

namespace Res

/-- A right action on `M` commuting with `B` restricts to `φ(1) M`. -/
instance rightModule : Module Cᵐᵒᵖ (Res φ M) where
  smul c m := mk (c • m.val) (by rw [smul_comm (φ 1) c, m.prop])
  one_smul m := ext (one_smul _ m.val)
  mul_smul c d m := ext (mul_smul c d m.val)
  smul_zero c := ext (smul_zero c)
  smul_add c m m' := ext (smul_add c m.val m'.val)
  add_smul c d m := ext (add_smul c d m.val)
  zero_smul m := ext (zero_smul _ m.val)

variable {φ M} in
@[simp] theorem val_op_smul (c : Cᵐᵒᵖ) (m : Res φ M) : (c • m).val = c • m.val := rfl

instance : SMulCommClass A Cᵐᵒᵖ (Res φ M) where
  smul_comm a c m := ext (smul_comm (φ a) c m.val)

end Res

end RightRes

section RightInd

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B) {C : Type u} [Ring C]
  (N : Type w) [AddCommGroup N] [Module A N] [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N]

namespace Ind

/-- A right action on `N` commuting with `A` passes to `B e ⊗_A N`. -/
instance rightModule : Module Cᵐᵒᵖ (Ind N φ) :=
  inferInstanceAs (Module Cᵐᵒᵖ (BalancedTensor ℤ B A (Corner φ) N))

instance : SMulCommClass B Cᵐᵒᵖ (Ind N φ) :=
  inferInstanceAs (SMulCommClass B Cᵐᵒᵖ (BalancedTensor ℤ B A (Corner φ) N))

variable {φ N} in
theorem op_smul_tmul_right (c : Cᵐᵒᵖ) (z : Corner φ) (n : N) :
    c • tmul z n = tmul z (c • n) :=
  rfl

end Ind

end RightInd

/-! ### `Res ∘ Ind` -/

section ResInd

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B)
  (N : Type u) [AddCommGroup N] [Module A N]

/-- The idempotent part `e x` of an element of the induction of the regular module. -/
def resIndProj (x : Ind A φ) : Res φ (Ind A φ) :=
  Res.mk (φ 1 • x) (by rw [smul_smul, unit_mul_unit])

/-- The `A`-linear map `a ↦ a n`. -/
def actOn (n : N) : A →ₗ[A] N where
  toFun a := a • n
  map_add' a a' := add_smul a a' n
  map_smul' a a' := mul_smul a a' n

variable {φ N}

@[simp] theorem actOn_apply (n : N) (a : A) : actOn N n a = a • n := rfl

theorem resIndProj_add (x y : Ind A φ) :
    resIndProj φ (x + y) = resIndProj φ x + resIndProj φ y :=
  Res.ext (smul_add _ x y)

theorem resIndProj_zero : resIndProj φ 0 = 0 := Res.ext (smul_zero _)

theorem resIndProj_op_smul (a : A) (x : Ind A φ) :
    resIndProj φ (op a • x) = op a • resIndProj φ x :=
  Res.ext (smul_comm (φ 1) (op a) x)

theorem actOn_add (n n' : N) :
    actOn (A := A) N (n + n') = actOn N n + actOn N n' :=
  LinearMap.ext fun (a : A) => smul_add a n n'

theorem actOn_zsmul (c : ℤ) (n : N) : actOn (A := A) N (c • n) = c • actOn N n :=
  LinearMap.ext fun (a : A) => smul_comm a c n

theorem map_actOn_add (n n' : N) (x : Ind A φ) :
    Ind.map (actOn N (n + n')) x = Ind.map (actOn N n) x + Ind.map (actOn N n') x := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul z a => simp only [Ind.map_tmul, actOn_apply, smul_add, Ind.tmul_add]
  | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]; abel

theorem map_actOn_zsmul (c : ℤ) (n : N) (x : Ind A φ) :
    Ind.map (actOn N (c • n)) x = c • Ind.map (actOn N n) x := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul z a =>
    rw [Ind.map_tmul, Ind.map_tmul, actOn_apply, actOn_apply, smul_comm a c n]
    exact map_zsmul (AddMonoidHom.mk' (Ind.tmul (N := N) z) (Ind.tmul_add z)) c (a • n)
  | add s t hs ht => rw [map_add, hs, ht, map_add, smul_add]

theorem map_actOn_op_smul (a : A) (n : N) (x : Ind A φ) :
    Ind.map (actOn N n) (op a • x) = Ind.map (actOn N (a • n)) x := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul z b =>
    change Ind.map (actOn N n) (Ind.tmul z (op a • b)) = _
    rw [Ind.map_tmul, Ind.map_tmul, actOn_apply, actOn_apply, op_smul_eq_mul, mul_smul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht]

variable (φ N)

/-- The forward map `Ind_φ N → Res_φ (Ind_φ A) ⊗_A N`, `z ⊗ n ↦ e (z ⊗ 1) ⊗ n`. -/
def resIndFwd : Ind N φ →+ BalancedTensor ℤ A A (Res φ (Ind A φ)) N :=
  Ind.liftAdd (fun (z : Corner φ) (n : N) => BalancedTensor.tmul (resIndProj φ (Ind.tmul z 1)) n)
    (fun z z' n => by
      rw [Ind.add_tmul, resIndProj_add, BalancedTensor.add_tmul])
    (fun z n n' => BalancedTensor.tmul_add _ n n')
    (fun z a n => by
      rw [← BalancedTensor.op_smul_tmul, ← resIndProj_op_smul, Ind.op_smul_tmul]
      congr 2
      change Ind.tmul z (a • (1 : A)) = Ind.tmul z (op a • (1 : A))
      rw [smul_eq_mul, op_smul_eq_mul, mul_one, one_mul])

theorem resIndFwd_tmul (z : Corner φ) (n : N) :
    resIndFwd φ N (Ind.tmul z n) = BalancedTensor.tmul (resIndProj φ (Ind.tmul z 1)) n :=
  rfl

/-- The underlying element, as an additive map. -/
def resValHom (M : Type u) [AddCommGroup M] [Module B M] : Res φ M →+ M where
  toFun m := m.val
  map_zero' := rfl
  map_add' _ _ := rfl

theorem res_val_zsmul {M : Type u} [AddCommGroup M] [Module B M] (c : ℤ) (m : Res φ M) :
    (c • m).val = c • m.val :=
  map_zsmul (resValHom φ M) c m

/-- The action `x n` of `x ∈ Res_φ (Ind_φ A)` on `n ∈ N`. -/
def resIndAct (x : Res φ (Ind A φ)) (n : N) : Res φ (Ind N φ) :=
  Res.mk (Ind.map (actOn N n) x.val) (by rw [← map_smul, x.prop])

@[simp] theorem resIndAct_val (x : Res φ (Ind A φ)) (n : N) :
    (resIndAct φ N x n).val = Ind.map (actOn N n) x.val := rfl

/-- The `ℤ`-bilinear map `(x, n) ↦ x n` underlying the backward map. -/
def resIndBil : Res φ (Ind A φ) →ₗ[ℤ] N →ₗ[ℤ] Res φ (Ind N φ) :=
  LinearMap.mk₂ ℤ (resIndAct φ N)
    (fun x x' n => Res.ext (by
      rw [Res.val_add, resIndAct_val, resIndAct_val, resIndAct_val, Res.val_add, map_add]))
    (fun c x n => Res.ext (by
      rw [res_val_zsmul, resIndAct_val, resIndAct_val, res_val_zsmul, map_zsmul]))
    (fun x n n' => Res.ext (by
      rw [Res.val_add, resIndAct_val, resIndAct_val, resIndAct_val]
      exact map_actOn_add n n' x.val))
    (fun c x n => Res.ext (by
      rw [res_val_zsmul, resIndAct_val, resIndAct_val]
      exact map_actOn_zsmul c n x.val))

theorem resIndBil_apply (x : Res φ (Ind A φ)) (n : N) :
    resIndBil φ N x n = resIndAct φ N x n :=
  rfl

theorem resIndAct_op_smul (x : Res φ (Ind A φ)) (a : A) (n : N) :
    resIndAct φ N (op a • x) n = resIndAct φ N x (a • n) :=
  Res.ext (map_actOn_op_smul a n x.val)

theorem resIndAct_smul (a : A) (x : Res φ (Ind A φ)) (n : N) :
    resIndAct φ N (a • x) n = a • resIndAct φ N x n := by
  apply Res.ext
  rw [Res.val_smul, resIndAct_val, resIndAct_val, Res.val_smul, map_smul]

/-- The backward map `Res_φ (Ind_φ A) ⊗_A N → Res_φ (Ind_φ N)`, `x ⊗ n ↦ x n`. -/
def resIndBwd : BalancedTensor ℤ A A (Res φ (Ind A φ)) N →ₗ[A] Res φ (Ind N φ) :=
  BalancedTensor.liftB (resIndBil φ N)
    (fun x a n => resIndAct_op_smul φ N x a n)
    (fun a x n => resIndAct_smul φ N a x n)

theorem resIndBwd_tmul (x : Res φ (Ind A φ)) (n : N) :
    (resIndBwd φ N (BalancedTensor.tmul x n)).val = Ind.map (actOn N n) x.val :=
  rfl

theorem resIndFwd_map (n : N) (x : Ind A φ) :
    resIndFwd φ N (Ind.map (actOn N n) x) = BalancedTensor.tmul (resIndProj φ x) n := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, resIndProj_zero, BalancedTensor.zero_tmul]
  | tmul z a =>
    rw [Ind.map_tmul, actOn_apply, resIndFwd_tmul, ← BalancedTensor.op_smul_tmul,
      ← resIndProj_op_smul]
    congr 2
    change Ind.tmul z (op a • (1 : A)) = Ind.tmul z a
    rw [op_smul_eq_mul, one_mul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, resIndProj_add, BalancedTensor.add_tmul]

theorem resIndBwd_fwd (t : Ind N φ) :
    (resIndBwd φ N (resIndFwd φ N t)).val = φ 1 • t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]; rfl
  | tmul z n =>
    rw [resIndFwd_tmul, resIndBwd_tmul]
    change Ind.map (actOn N n) (φ 1 • Ind.tmul z 1) = _
    rw [map_smul, Ind.map_tmul, actOn_apply, one_smul]
  | add s t hs ht => rw [map_add, map_add, Res.val_add, hs, ht, smul_add]

/-- **`Res ∘ Ind` is tensoring with `e B e`**: `Res_φ (Ind_φ N) ≅ Res_φ (Ind_φ A) ⊗_A N`. -/
def resIndTensor : Res φ (Ind N φ) ≃ₗ[A] BalancedTensor ℤ A A (Res φ (Ind A φ)) N :=
  LinearEquiv.symm
    { resIndBwd φ N with
      invFun := fun t => resIndFwd φ N t.val
      left_inv := fun t => by
        induction t using BalancedTensor.induction_on with
        | zero => exact (congrArg (resIndFwd φ N) (Res.val_zero)).trans (map_zero _)
        | tmul x n =>
          change resIndFwd φ N (Ind.map (actOn N n) x.val) = _
          rw [resIndFwd_map]
          congr 1
          exact Res.ext x.prop
        | add s t hs ht =>
          change resIndFwd φ N (resIndBwd φ N (s + t)).val = s + t
          rw [map_add, Res.val_add, map_add]
          exact congrArg₂ (· + ·) hs ht
      right_inv := fun t => by
        apply Res.ext
        change (resIndBwd φ N (resIndFwd φ N t.val)).val = t.val
        rw [resIndBwd_fwd, t.prop] }

theorem resIndTensor_symm_tmul (x : Res φ (Ind A φ)) (n : N) :
    ((resIndTensor φ N).symm (BalancedTensor.tmul x n)).val = Ind.map (actOn N n) x.val :=
  rfl

end ResInd

/-! ### `Ind ∘ Res` -/

section IndRes

variable {A' : Type u} [Ring A'] {A : Type u} [Ring A] (ψ : A' →ₙ+* A)
  (N : Type u) [AddCommGroup N] [Module A N]

/-- The idempotent `e' = ψ 1` as an element of `Res_ψ A = e' A`. -/
def resUnit : Res ψ A := Res.mk (ψ 1) (unit_mul_unit ψ)

/-- The `A'`-linear map `e' A → e' N`, `r ↦ r n`. -/
def resActOn (n : N) : Res ψ A →ₗ[A'] Res ψ N where
  toFun r := Res.mk (r.val • n) (by rw [smul_smul]; exact congrArg (· • n) r.prop)
  map_add' r r' := Res.ext (add_smul r.val r'.val n)
  map_smul' a r := Res.ext (mul_smul (ψ a) r.val n)

variable {ψ N}

@[simp] theorem resActOn_val (n : N) (r : Res ψ A) : (resActOn ψ N n r).val = r.val • n := rfl

theorem resUnit_smul (a : A') : a • resUnit ψ = op (ψ a) • resUnit ψ := by
  apply Res.ext
  change ψ a * ψ 1 = ψ 1 * ψ a
  rw [← map_mul, ← map_mul, mul_one, one_mul]

theorem op_smul_resUnit (r : Res ψ A) : op r.val • resUnit ψ = r := by
  apply Res.ext
  change ψ 1 * r.val = r.val
  exact r.prop

theorem map_resActOn_add (n n' : N) (x : Ind (Res ψ A) ψ) :
    Ind.map (resActOn ψ N (n + n')) x =
      Ind.map (resActOn ψ N n) x + Ind.map (resActOn ψ N n') x := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul z r =>
    rw [Ind.map_tmul, Ind.map_tmul, Ind.map_tmul, ← Ind.tmul_add]
    congr 1
    exact Res.ext (smul_add r.val n n')
  | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]; abel

theorem map_resActOn_zsmul (c : ℤ) (n : N) (x : Ind (Res ψ A) ψ) :
    Ind.map (resActOn ψ N (c • n)) x = c • Ind.map (resActOn ψ N n) x := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul z r =>
    rw [Ind.map_tmul, Ind.map_tmul]
    have : resActOn ψ N (c • n) r = c • resActOn ψ N n r := by
      apply Res.ext
      rw [res_val_zsmul, resActOn_val, resActOn_val]
      exact smul_comm r.val c n
    rw [this]
    exact map_zsmul (AddMonoidHom.mk' (Ind.tmul (N := Res ψ N) z) (Ind.tmul_add z)) c _
  | add s t hs ht => rw [map_add, hs, ht, map_add, smul_add]

theorem map_resActOn_op_smul (a : A) (n : N) (x : Ind (Res ψ A) ψ) :
    Ind.map (resActOn ψ N n) (op a • x) = Ind.map (resActOn ψ N (a • n)) x := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul z r =>
    rw [Ind.op_smul_tmul_right, Ind.map_tmul, Ind.map_tmul]
    congr 1
    apply Res.ext
    change (r.val * a) • n = r.val • a • n
    rw [mul_smul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht]

variable (ψ N)

/-- The forward map `Ind_ψ (Res_ψ N) → Ind_ψ (Res_ψ A) ⊗_A N`, `z ⊗ m ↦ (z ⊗ e') ⊗ m`. -/
def indResFwd : Ind (Res ψ N) ψ →+ BalancedTensor ℤ A A (Ind (Res ψ A) ψ) N :=
  Ind.liftAdd
    (fun (z : Corner ψ) (m : Res ψ N) => BalancedTensor.tmul (Ind.tmul z (resUnit ψ)) m.val)
    (fun z z' m => by rw [Ind.add_tmul, BalancedTensor.add_tmul])
    (fun z m m' => by rw [Res.val_add, BalancedTensor.tmul_add])
    (fun z a m => by
      rw [Ind.op_smul_tmul, resUnit_smul, ← Ind.op_smul_tmul_right, BalancedTensor.op_smul_tmul,
        Res.val_smul])

theorem indResFwd_tmul (z : Corner ψ) (m : Res ψ N) :
    indResFwd ψ N (Ind.tmul z m) = BalancedTensor.tmul (Ind.tmul z (resUnit ψ)) m.val :=
  rfl

/-- The `ℤ`-bilinear map `(x, n) ↦ x n` underlying the backward map. -/
def indResBil : Ind (Res ψ A) ψ →ₗ[ℤ] N →ₗ[ℤ] Ind (Res ψ N) ψ :=
  LinearMap.mk₂ ℤ (fun x n => Ind.map (resActOn ψ N n) x)
    (fun x x' _ => map_add _ x x')
    (fun c x _ => map_zsmul _ c x)
    (fun x n n' => map_resActOn_add n n' x)
    (fun c x n => map_resActOn_zsmul c n x)

theorem indResBil_apply (x : Ind (Res ψ A) ψ) (n : N) :
    indResBil ψ N x n = Ind.map (resActOn ψ N n) x :=
  rfl

/-- The backward map `Ind_ψ (Res_ψ A) ⊗_A N → Ind_ψ (Res_ψ N)`, `x ⊗ n ↦ x n`. -/
def indResBwd : BalancedTensor ℤ A A (Ind (Res ψ A) ψ) N →ₗ[A] Ind (Res ψ N) ψ :=
  BalancedTensor.liftB (indResBil ψ N)
    (fun x a n => map_resActOn_op_smul a n x)
    (fun a x n => map_smul (Ind.map (resActOn ψ N n)) a x)

theorem indResBwd_tmul (x : Ind (Res ψ A) ψ) (n : N) :
    indResBwd ψ N (BalancedTensor.tmul x n) = Ind.map (resActOn ψ N n) x :=
  rfl

theorem indResFwd_map (n : N) (x : Ind (Res ψ A) ψ) :
    indResFwd ψ N (Ind.map (resActOn ψ N n) x) = BalancedTensor.tmul x n := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, BalancedTensor.zero_tmul]
  | tmul z r =>
    rw [Ind.map_tmul, indResFwd_tmul, resActOn_val, ← BalancedTensor.op_smul_tmul,
      Ind.op_smul_tmul_right, op_smul_resUnit]
  | add s t hs ht => rw [map_add, map_add, hs, ht, BalancedTensor.add_tmul]

theorem indResBwd_fwd (t : Ind (Res ψ N) ψ) : indResBwd ψ N (indResFwd ψ N t) = t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z m =>
    rw [indResFwd_tmul, indResBwd_tmul, Ind.map_tmul]
    congr 1
    exact Res.ext m.prop
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- **`Ind ∘ Res` is tensoring with `A e' ⊗_{A'} e' A`**:
`Ind_ψ (Res_ψ N) ≅ Ind_ψ (Res_ψ A) ⊗_A N`. -/
def indResTensor : Ind (Res ψ N) ψ ≃ₗ[A] BalancedTensor ℤ A A (Ind (Res ψ A) ψ) N :=
  LinearEquiv.symm
    { indResBwd ψ N with
      invFun := indResFwd ψ N
      left_inv := fun t => by
        induction t using BalancedTensor.induction_on with
        | zero => exact (congrArg (indResFwd ψ N) (map_zero (indResBwd ψ N))).trans (map_zero _)
        | tmul x n => exact indResFwd_map ψ N n x
        | add s t hs ht =>
          change indResFwd ψ N (indResBwd ψ N (s + t)) = s + t
          rw [map_add, map_add]
          exact congrArg₂ (· + ·) hs ht
      right_inv := indResBwd_fwd ψ N }

theorem indResTensor_symm_tmul (x : Ind (Res ψ A) ψ) (n : N) :
    (indResTensor ψ N).symm (BalancedTensor.tmul x n) = Ind.map (resActOn ψ N n) x :=
  rfl

end IndRes

end InductionAlong

end

end Categorification
