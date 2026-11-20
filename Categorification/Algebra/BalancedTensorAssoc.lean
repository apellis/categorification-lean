/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.BalancedTensor

/-!
# Associativity of balanced tensor products

Let `X` be a `(B, A)`-bimodule, `Y` an `(A, C)`-bimodule and `P` a left `C`-module. The right
`C`-action of `Y` makes `X ⊗_A Y` a `(B, C)`-bimodule (`BalancedTensor.rightModule`), and

`(X ⊗_A Y) ⊗_C P ≅ X ⊗_A (Y ⊗_C P)`,   `(x ⊗ y) ⊗ p ↦ x ⊗ (y ⊗ p)`,

as left `B`-modules (`BalancedTensor.assoc`). Right modules are left modules over the opposite
ring, as elsewhere in the library. Together with `BalancedTensor.mapLeftBimodule`, this turns
isomorphisms of bimodules `X ⊗_A Y ≅ Z` into natural isomorphisms of the functors `P ↦ X ⊗_A
(Y ⊗_C P)` and `P ↦ Z ⊗_C P`. This is how the relations of a categorical action on projectives
(B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 4.31) become relations between functors on module categories, as used in §5 there.

## Main definitions

* `BalancedTensor.rightModule`: the right `C`-action on `X ⊗_A Y`.
* `BalancedTensor.assoc`: the associativity isomorphism, built from `assocHom` and `assocInv`.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]
  {A : Type*} [Ring A] [Algebra k A] {C : Type*} [Ring C] [Algebra k C]
  {X : Type*} [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
  [Module Aᵐᵒᵖ X] [SMulCommClass B Aᵐᵒᵖ X]
  {Y : Type*} [AddCommGroup Y] [Module k Y] [Module A Y] [IsScalarTower k A Y]
  [Module Cᵐᵒᵖ Y] [SMulCommClass A Cᵐᵒᵖ Y]

variable (A Y) in
/-- Right multiplication by `c` on the `(A, C)`-bimodule `Y`, an `A`-linear map. -/
def rmul (c : Cᵐᵒᵖ) : Y →ₗ[A] Y where
  toFun y := c • y
  map_add' := smul_add c
  map_smul' a y := (smul_comm a c y).symm

variable (k B X) in
/-- The right `C`-action on `X ⊗_A Y` through the right factor. -/
instance rightModule : Module Cᵐᵒᵖ (BalancedTensor k B A X Y) where
  smul c t := mapRight (rmul A Y c) t
  one_smul t := by
    change mapRight (rmul A Y 1) t = t
    induction t using induction_on with
    | zero => rw [map_zero]
    | tmul x y => exact congrArg (tmul x) (one_smul _ y)
    | add s t hs ht => rw [map_add, hs, ht]
  mul_smul c d t := by
    change mapRight (rmul A Y (c * d)) t = mapRight (rmul A Y c) (mapRight (rmul A Y d) t)
    induction t using induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => exact congrArg (tmul x) (mul_smul c d y)
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  smul_zero c := map_zero _
  smul_add c := map_add _
  add_smul c d t := by
    change mapRight (rmul A Y (c + d)) t = mapRight (rmul A Y c) t + mapRight (rmul A Y d) t
    induction t using induction_on with
    | zero => rw [map_zero, map_zero, map_zero, add_zero]
    | tmul x y =>
      change tmul x ((c + d) • y) = tmul x (c • y) + tmul x (d • y)
      rw [add_smul, tmul_add]
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, add_add_add_comm]
  zero_smul t := by
    change mapRight (rmul A Y 0) t = 0
    induction t using induction_on with
    | zero => rw [map_zero]
    | tmul x y =>
      change tmul x ((0 : Cᵐᵒᵖ) • y) = 0
      rw [zero_smul, tmul_zero]
    | add s t hs ht => rw [map_add, hs, ht, add_zero]

omit [Algebra k C] in
theorem smul_tmul_right (c : Cᵐᵒᵖ) (x : X) (y : Y) :
    c • (tmul x y : BalancedTensor k B A X Y) = tmul x (c • y) :=
  rfl

instance : SMulCommClass B Cᵐᵒᵖ (BalancedTensor k B A X Y) where
  smul_comm b c t := ((mapRight (rmul A Y c)).map_smul b t).symm

variable {P : Type*} [AddCommGroup P] [Module k P] [Module C P] [IsScalarTower k C P]

variable (A C Y P) in
/-- The `A`-linear map `y ↦ y ⊗ p`. -/
def tmulRight (p : P) : Y →ₗ[A] BalancedTensor k A C Y P where
  toFun y := tmul y p
  map_add' y y' := add_tmul y y' p
  map_smul' a y := (smul_tmul' a y p).symm

/-- The bilinear map `(x ⊗ y, p) ↦ x ⊗ (y ⊗ p)`. -/
def assocBil :
    BalancedTensor k B A X Y →ₗ[k] P →ₗ[k] BalancedTensor k B A X (BalancedTensor k A C Y P) :=
  LinearMap.mk₂ k (fun t p => mapRight (tmulRight A C Y P p) t)
    (fun t t' p => map_add _ t t')
    (fun c t p => (mapRight (tmulRight A C Y P p)).map_smul_of_tower c t)
    (fun t p p' => by
      induction t using induction_on with
      | zero => rw [map_zero, map_zero, map_zero, add_zero]
      | tmul x y =>
        change tmul x (tmul y (p + p')) = tmul x (tmul y p) + tmul x (tmul y p')
        rw [tmul_add, tmul_add]
      | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, add_add_add_comm])
    (fun c t p => by
      induction t using induction_on with
      | zero => rw [map_zero, map_zero, smul_zero]
      | tmul x y =>
        change tmul x (tmul y (c • p)) = c • tmul x (tmul y p)
        rw [tmul_smul, tmul_smul]
      | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add])

/-- The bilinear map `(x, y ⊗ p) ↦ (x ⊗ y) ⊗ p`, for fixed `x`. -/
def assocInvRight (x : X) :
    BalancedTensor k A C Y P →ₗ[k] BalancedTensor k B C (BalancedTensor k B A X Y) P :=
  lift ((mkBil k B C (BalancedTensor k B A X Y) P).comp
      ((mkBil k B A X Y x).restrictScalars k))
    (fun y c p => op_smul_tmul (tmul x y) c p)

/-- The bilinear map `(x, y ⊗ p) ↦ (x ⊗ y) ⊗ p`. -/
def assocInvBil :
    X →ₗ[k] BalancedTensor k A C Y P →ₗ[k] BalancedTensor k B C (BalancedTensor k B A X Y) P :=
  LinearMap.mk₂ k (fun x s => assocInvRight (B := B) x s)
    (fun x x' s => by
      induction s using induction_on with
      | zero => rw [map_zero, map_zero, map_zero, add_zero]
      | tmul y p =>
        change tmul (tmul (x + x') y) p = tmul (tmul x y) p + tmul (tmul x' y) p
        rw [add_tmul, add_tmul]
      | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, add_add_add_comm])
    (fun c x s => by
      induction s using induction_on with
      | zero => rw [map_zero, map_zero, smul_zero]
      | tmul y p =>
        change tmul (tmul (c • x) y) p = c • tmul (tmul x y) p
        rw [smul_tmul, smul_tmul]
      | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add])
    (fun x s s' => map_add _ s s')
    (fun c x s => (assocInvRight (B := B) x).map_smul c s)

omit [Algebra k C] [SMulCommClass A Cᵐᵒᵖ Y] [IsScalarTower k C P] in
theorem assocBil_tmul (x : X) (y : Y) (p : P) :
    assocBil (C := C) (tmul x y : BalancedTensor k B A X Y) p = tmul x (tmul y p) :=
  rfl

omit [Algebra k C] [IsScalarTower k C P] in
theorem assocInvBil_tmul (x : X) (y : Y) (p : P) :
    assocInvBil (B := B) x (tmul y p : BalancedTensor k A C Y P) = tmul (tmul x y) p :=
  rfl

variable (k B A C X Y P) in
/-- The map `(x ⊗ y) ⊗ p ↦ x ⊗ (y ⊗ p)`. -/
def assocHom : BalancedTensor k B C (BalancedTensor k B A X Y) P →ₗ[B]
    BalancedTensor k B A X (BalancedTensor k A C Y P) :=
  liftB assocBil
    (fun t c p => by
      induction t using induction_on with
      | zero => simp only [smul_zero, map_zero, LinearMap.zero_apply]
      | tmul x y =>
        rw [smul_tmul_right, assocBil_tmul, assocBil_tmul, op_smul_tmul]
      | add s t hs ht => simp only [smul_add, map_add, LinearMap.add_apply, hs, ht])
    (fun b t p => (mapRight (tmulRight A C Y P p)).map_smul b t)

variable (k B A C X Y P) in
/-- The map `x ⊗ (y ⊗ p) ↦ (x ⊗ y) ⊗ p`. -/
def assocInv : BalancedTensor k B A X (BalancedTensor k A C Y P) →ₗ[B]
    BalancedTensor k B C (BalancedTensor k B A X Y) P :=
  liftB assocInvBil
    (fun x a s => by
      induction s using induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul y p =>
        rw [smul_tmul', assocInvBil_tmul, assocInvBil_tmul, op_smul_tmul]
      | add s t hs ht => simp only [map_add, smul_add, hs, ht])
    (fun b x s => by
      induction s using induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul y p => rw [assocInvBil_tmul, assocInvBil_tmul, smul_tmul', smul_tmul']
      | add s t hs ht => simp only [map_add, smul_add, hs, ht])

omit [Algebra k C] [IsScalarTower k C P] in
@[simp] theorem assocHom_tmul (x : X) (y : Y) (p : P) :
    assocHom k B A C X Y P (tmul (tmul x y) p) = tmul x (tmul y p) :=
  rfl

omit [Algebra k C] [IsScalarTower k C P] in
@[simp] theorem assocInv_tmul (x : X) (y : Y) (p : P) :
    assocInv k B A C X Y P (tmul x (tmul y p)) = tmul (tmul x y) p :=
  rfl

variable (k B A C X Y P) in
/-- **Associativity**: `(X ⊗_A Y) ⊗_C P ≅ X ⊗_A (Y ⊗_C P)` as left `B`-modules. -/
def assoc : BalancedTensor k B C (BalancedTensor k B A X Y) P ≃ₗ[B]
    BalancedTensor k B A X (BalancedTensor k A C Y P) :=
  LinearEquiv.ofLinearMap (assocHom k B A C X Y P) (assocInv k B A C X Y P)
    (extB fun x s => by
      induction s using induction_on with
      | zero => rw [tmul_zero, map_zero, map_zero]
      | tmul y p => rw [LinearMap.comp_apply, assocInv_tmul, assocHom_tmul]; rfl
      | add s t hs ht => rw [tmul_add, map_add, map_add, hs, ht])
    (extB fun t p => by
      induction t using induction_on with
      | zero => rw [zero_tmul, map_zero, map_zero]
      | tmul x y => rw [LinearMap.comp_apply, assocHom_tmul, assocInv_tmul]; rfl
      | add s t hs ht => rw [add_tmul, map_add, map_add, hs, ht])

omit [Algebra k C] [IsScalarTower k C P] in
@[simp] theorem assoc_tmul (x : X) (y : Y) (p : P) :
    assoc k B A C X Y P (tmul (tmul x y) p) = tmul x (tmul y p) :=
  rfl

omit [Algebra k C] [IsScalarTower k C P] in
@[simp] theorem assoc_symm_tmul (x : X) (y : Y) (p : P) :
    (assoc k B A C X Y P).symm (tmul x (tmul y p)) = tmul (tmul x y) p :=
  rfl

end BalancedTensor

end

end Categorification
