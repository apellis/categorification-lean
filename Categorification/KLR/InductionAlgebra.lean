/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ConcatAssoc

/-!
# Associativity and unitality of induction; the algebra `K₀(R)`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1, **Proposition 3.1** (`K₀` part): `[Ind]` makes
`K₀(R) = ⨁_ν K₀(R(ν))` an associative unital `ℤ[q, q⁻¹]`-algebra with unit `[R(0)]`.

## Main definitions and results

* `KLRAlgebra.assocEquiv` : for modules `N₁`, `N₂`, `N₃` over `R(ν)`, `R(ν')`, `R(ν'')`, the
  isomorphism
  `Ind_{ν+ν',ν''} (Ind_{ν,ν'} (N₁ ⊠ N₂) ⊠ N₃) ≅ Ind_{ν,ν'+ν''} (N₁ ⊠ Ind_{ν',ν''} (N₂ ⊠ N₃))`,
  semilinear along the canonical isomorphism `castKLR : R((ν + ν') + ν'') ≃ R(ν + (ν' + ν''))`
  (`assocEquiv_smul`), built from the associativity of concatenation
  (`KLRAlgebra.concat_assoc`).
* `KLRAlgebra.unitLEquiv`, `KLRAlgebra.unitREquiv` :
  `Ind_{0,ν} (R(0) ⊠ N) ≅ N` and `Ind_{ν,0} (N ⊠ R(0)) ≅ N`, semilinear along
  `R(0 + ν) ≃ R(ν)`, `R(ν + 0) ≃ R(ν)` (`unitLEquiv_smul`, `unitREquiv_smul`).

The maps are built from nested universal properties (`BalancedTensor.lift`, `ExtTensor.lift`);
the associativity isomorphism is `r ⊗ ((r' ⊗ (n₁ ⊗ n₂)) ⊗ n₃) ↦
castKLR (r ι(r' ⊗ 1)) ⊗ (n₁ ⊗ (1_{ν',ν''} ⊗ (n₂ ⊗ n₃)))`, with inverse
`r ⊗ (n₁ ⊗ (r'' ⊗ (n₂ ⊗ n₃))) ↦ castKLR⁻¹ (r ι(1 ⊗ r'')) ⊗ ((1_{ν,ν'} ⊗ (n₁ ⊗ n₂)) ⊗ n₃)`.
Gradings are handled in `Categorification.KLR.K0Algebra`.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open KLRAlgebra MulOpposite Graded

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

/-! ### The element `1_{ν,ν'}` of `R(ν + ν') 1_{ν,ν'}` -/

section OneBimod

variable (Q) (ν ν' : Multiset I)

/-- `1_{ν,ν'} ∈ R(ν + ν') 1_{ν,ν'}`. -/
def oneBimod : IndBimod Q ν ν' := ⟨oneConcat Q ν ν', oneConcat_idem.eq⟩

@[simp] theorem coe_oneBimod :
    ((oneBimod Q ν ν' : IndBimod Q ν ν') : KLRAlgebra k Q (ν + ν')) = oneConcat Q ν ν' := rfl

variable {Q ν ν'}

theorem concat_smul_oneBimod (t : TensorKLR Q ν ν') :
    concat Q ν ν' t • oneBimod Q ν ν' = op t • oneBimod Q ν ν' :=
  Subtype.ext (by
    show concat Q ν ν' t * oneConcat Q ν ν' = oneConcat Q ν ν' * concat Q ν ν' t
    rw [concat_mul_oneConcat, oneConcat_mul_concat])

/-- `ι(t) (1_{ν,ν'} ⊗ m) = 1_{ν,ν'} ⊗ t m` in an induced module. -/
theorem concat_smul_tmul_oneBimod {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorKLR Q ν ν') N] [IsScalarTower k (TensorKLR Q ν ν') N] (t : TensorKLR Q ν ν')
    (m : N) :
    concat Q ν ν' t • (BalancedTensor.tmul (oneBimod Q ν ν') m : Ind Q ν ν' N) =
      BalancedTensor.tmul (oneBimod Q ν ν') (t • m) := by
  rw [BalancedTensor.smul_tmul', concat_smul_oneBimod, BalancedTensor.op_smul_tmul]

end OneBimod

/-! ### Associativity of induction -/

section Assoc

variable {ν ν' ν'' : Multiset I}
  (N₁ : Type*) [AddCommGroup N₁] [Module k N₁] [Module (KLRAlgebra k Q ν) N₁]
    [IsScalarTower k (KLRAlgebra k Q ν) N₁]
  (N₂ : Type*) [AddCommGroup N₂] [Module k N₂] [Module (KLRAlgebra k Q ν') N₂]
    [IsScalarTower k (KLRAlgebra k Q ν') N₂]
  (N₃ : Type*) [AddCommGroup N₃] [Module k N₃] [Module (KLRAlgebra k Q ν'') N₃]
    [IsScalarTower k (KLRAlgebra k Q ν'') N₃]

variable (Q ν ν' ν'') in
/-- `Ind_{ν+ν',ν''} (Ind_{ν,ν'} (N₁ ⊠ N₂) ⊠ N₃)`. -/
abbrev AssocL : Type _ :=
  Ind Q (ν + ν') ν'' (ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃)

variable (Q ν ν' ν'') in
/-- `Ind_{ν,ν'+ν''} (N₁ ⊠ Ind_{ν',ν''} (N₂ ⊠ N₃))`. -/
abbrev AssocR : Type _ :=
  Ind Q ν (ν' + ν'') (ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃)))

omit [IsScalarTower k (KLRAlgebra k Q ν) N₁] [IsScalarTower k (KLRAlgebra k Q ν') N₂] in
/-- Maps out of `Ind_{ν,ν'} N ⊠ N₃` are determined by their values on the `(r' ⊗ n) ⊗ n₃`. -/
theorem extTensorInd_ext {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorKLR Q ν ν') N] {M : Type*} [AddCommGroup M] [Module k M]
    {f g : ExtTensor k (Ind Q ν ν' N) N₃ →ₗ[k] M}
    (h : ∀ r' n n₃, f (ExtTensor.tmul (BalancedTensor.tmul r' n) n₃) =
      g (ExtTensor.tmul (BalancedTensor.tmul r' n) n₃)) : f = g := by
  ext z
  induction z using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y n₃ =>
    induction y using BalancedTensor.induction_on with
    | zero => rw [ExtTensor.zero_tmul, map_zero, map_zero]
    | tmul r' n => exact h r' n n₃
    | add y y' hy hy' => rw [ExtTensor.add_tmul, map_add, map_add, hy, hy']
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem assocBimod_mem (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν') :
    castKLR Q (add_assoc ν ν' ν'')
        ((r : KLRAlgebra k Q (ν + ν' + ν'')) * concat Q (ν + ν') ν'' ((r' : KLRAlgebra k Q
          (ν + ν')) ⊗ₜ 1)) ∈ Graded.leftIdeal (oneConcat Q ν (ν' + ν'')) := by
  rw [Graded.mem_leftIdeal]
  have h : concat Q (ν + ν') ν'' ((r' : KLRAlgebra k Q (ν + ν')) ⊗ₜ (1 : KLRAlgebra k Q ν'')) =
      concat Q (ν + ν') ν'' ((r' : KLRAlgebra k Q (ν + ν')) ⊗ₜ 1) * concatL ν ν' ν'' 1 1 1 := by
    rw [concatL_one_eq, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Graded.mem_leftIdeal.1 r'.2]
  rw [h, ← mul_assoc, map_mul, castKLR_concatL_one, mul_assoc, concatR, concat_mul_oneConcat]

variable (Q ν ν' ν'') in
/-- `(r, r') ↦ castKLR (r ι(r' ⊗ 1))`, from `R(μ) 1_{ν+ν',ν''} × R(ν + ν') 1_{ν,ν'}` to
`R(μ') 1_{ν,ν'+ν''}`. -/
def assocBimod :
    IndBimod Q (ν + ν') ν'' →ₗ[k] IndBimod Q ν ν' →ₗ[k] IndBimod Q ν (ν' + ν'') :=
  LinearMap.mk₂ k (fun r r' => ⟨_, assocBimod_mem r r'⟩)
    (fun r₁ r₂ r' => Subtype.ext (by
      show castKLR Q _ (((r₁ : KLRAlgebra k Q (ν + ν' + ν'')) + (r₂ : KLRAlgebra k Q (ν + ν' + ν''))) * _) = castKLR Q _ (_ * _) +
        castKLR Q _ (_ * _)
      rw [add_mul, map_add]))
    (fun c r r' => Subtype.ext (by
      show castKLR Q _ ((c • (r : KLRAlgebra k Q (ν + ν' + ν''))) * _) = c • castKLR Q _ (_ * _)
      rw [smul_mul_assoc, map_smul]))
    (fun r r₁ r₂ => Subtype.ext (by
      show castKLR Q _ (_ * concat Q (ν + ν') ν'' ((((r₁ : KLRAlgebra k Q (ν + ν'))) + (r₂ : KLRAlgebra k Q (ν + ν'))) ⊗ₜ 1))
        = castKLR Q _ (_ * _) + castKLR Q _ (_ * _)
      rw [TensorProduct.add_tmul, map_add, mul_add, map_add]))
    (fun c r r' => Subtype.ext (by
      show castKLR Q _ (_ * concat Q (ν + ν') ν'' ((c • (r' : KLRAlgebra k Q (ν + ν'))) ⊗ₜ 1))
        = c • castKLR Q _ (_ * _)
      rw [← TensorProduct.smul_tmul', map_smul, mul_smul_comm, map_smul]))

@[simp] theorem coe_assocBimod (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν') :
    (assocBimod Q ν ν' ν'' r r' : KLRAlgebra k Q (ν + (ν' + ν''))) =
      castKLR Q (add_assoc ν ν' ν'') ((r : KLRAlgebra k Q (ν + ν' + ν'')) *
        concat Q (ν + ν') ν'' ((r' : KLRAlgebra k Q (ν + ν')) ⊗ₜ 1)) := rfl

theorem assocBimod_op_smul (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν')
    (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    assocBimod Q ν ν' ν'' r (op (a ⊗ₜ[k] b) • r') =
      op (a ⊗ₜ[k] concat Q ν' ν'' (b ⊗ₜ 1)) • assocBimod Q ν ν' ν'' r r' := by
  apply Subtype.ext
  rw [coe_op_smul, coe_assocBimod, coe_assocBimod, coe_op_smul, unop_op, unop_op,
    ← concat_assoc, ← map_mul, mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]

theorem assocBimod_op_smul_outer (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν')
    (a' : KLRAlgebra k Q (ν + ν')) (d : KLRAlgebra k Q ν'') :
    assocBimod Q ν ν' ν'' (op (a' ⊗ₜ[k] d) • r) r' =
      op ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] concat Q ν' ν'' (1 ⊗ₜ d)) • assocBimod Q ν ν' ν'' r (a' • r') := by
  apply Subtype.ext
  rw [coe_op_smul, coe_assocBimod, coe_assocBimod, coe_op_smul, unop_op, unop_op,
    Submodule.coe_smul, smul_eq_mul]
  have h1 : concat Q (ν + ν') ν'' (a' ⊗ₜ d) *
      concat Q (ν + ν') ν'' ((r' : KLRAlgebra k Q (ν + ν')) ⊗ₜ 1) =
      concat Q (ν + ν') ν'' ((a' * r') ⊗ₜ 1) *
        concat Q (ν + ν') ν'' (oneConcat Q ν ν' ⊗ₜ d) := by
    rw [← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc,
      Graded.mem_leftIdeal.1 r'.2]
  have h2 : castKLR Q (add_assoc ν ν' ν'') (concat Q (ν + ν') ν'' (oneConcat Q ν ν' ⊗ₜ d)) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ d)) := by
    rw [← concat_one_tmul_one, concat_assoc]
  rw [mul_assoc, h1, ← mul_assoc, map_mul, h2]

variable (Q ν' ν'') in
/-- `n ↦ 1_{ν',ν''} ⊗ n`. -/
def assocW : ExtTensor k N₂ N₃ →ₗ[k] Ind Q ν' ν'' (ExtTensor k N₂ N₃) :=
  BalancedTensor.mkBil k (KLRAlgebra k Q (ν' + ν'')) (TensorKLR Q ν' ν'') (IndBimod Q ν' ν'')
    (ExtTensor k N₂ N₃) (oneBimod Q ν' ν'')

variable (Q ν' ν'') in
/-- `(n₁ ⊗ n₂) ⊗ n₃ ↦ n₁ ⊗ (1_{ν',ν''} ⊗ (n₂ ⊗ n₃))`. -/
def assocJ : ExtTensor k (ExtTensor k N₁ N₂) N₃ →ₗ[k]
    ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃)) :=
  (TensorProduct.map LinearMap.id (assocW Q ν' ν'' N₂ N₃)).comp
    (TensorProduct.assoc k N₁ N₂ N₃).toLinearMap

theorem assocJ_tmul (n₁ : N₁) (n₂ : N₂) (n₃ : N₃) :
    assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul (ExtTensor.tmul n₁ n₂) n₃) =
      ExtTensor.tmul n₁ (BalancedTensor.tmul (oneBimod Q ν' ν'') (ExtTensor.tmul n₂ n₃)) :=
  rfl

theorem smul_assocJ_left (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν')
    (n : ExtTensor k N₁ N₂) (n₃ : N₃) :
    (a ⊗ₜ[k] concat Q ν' ν'' (b ⊗ₜ 1)) • assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃) =
      assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul ((a ⊗ₜ[k] b) • n) n₃) := by
  induction n using ExtTensor.induction_on with
  | zero => simp
  | tmul n₁ n₂ =>
    rw [assocJ_tmul, ExtTensor.smul_tmul, concat_smul_tmul_oneBimod, ExtTensor.smul_tmul,
      ExtTensor.smul_tmul, one_smul, assocJ_tmul]
  | add n n' hn hn' => rw [ExtTensor.add_tmul, map_add, smul_add, hn, hn', smul_add,
      ExtTensor.add_tmul, map_add]

theorem smul_assocJ_right (d : KLRAlgebra k Q ν'') (n : ExtTensor k N₁ N₂) (n₃ : N₃) :
    ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] concat Q ν' ν'' (1 ⊗ₜ d)) •
        assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃) =
      assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n (d • n₃)) := by
  induction n using ExtTensor.induction_on with
  | zero => simp
  | tmul n₁ n₂ =>
    rw [assocJ_tmul, ExtTensor.smul_tmul, concat_smul_tmul_oneBimod, ExtTensor.smul_tmul,
      one_smul, one_smul, assocJ_tmul]
  | add n n' hn hn' => rw [ExtTensor.add_tmul, map_add, smul_add, hn, hn',
      ExtTensor.add_tmul, map_add]

/-! #### The forward map -/

variable (Q ν ν' ν'') in
/-- For fixed `r` and `n₃`: `(r', n) ↦ castKLR (r ι(r' ⊗ 1)) ⊗ J (n ⊗ n₃)`. -/
def assocMidBil (r : IndBimod Q (ν + ν') ν'') (n₃ : N₃) :
    IndBimod Q ν ν' →ₗ[k] ExtTensor k N₁ N₂ →ₗ[k] AssocR Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearMap.mk₂ k (fun r' n => BalancedTensor.tmul (assocBimod Q ν ν' ν'' r r')
      (assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃)))
    (fun r'₁ r'₂ n => by
      beta_reduce; simp only [map_add, LinearMap.add_apply, BalancedTensor.add_tmul])
    (fun c r' n => by
      beta_reduce; simp only [map_smul, LinearMap.smul_apply, BalancedTensor.smul_tmul])
    (fun r' n n' => by beta_reduce; rw [ExtTensor.add_tmul, map_add, BalancedTensor.tmul_add])
    (fun c r' n => by beta_reduce; rw [← ExtTensor.smul_tmul', map_smul, BalancedTensor.tmul_smul])

theorem assocMidBil_balanced (r : IndBimod Q (ν + ν') ν'') (n₃ : N₃) (r' : IndBimod Q ν ν')
    (t : TensorKLR Q ν ν') (n : ExtTensor k N₁ N₂) :
    assocMidBil Q ν ν' ν'' N₁ N₂ N₃ r n₃ (op t • r') n =
      assocMidBil Q ν ν' ν'' N₁ N₂ N₃ r n₃ r' (t • n) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [op_zero, zero_smul, zero_smul, map_zero, LinearMap.zero_apply, map_zero]
  | tmul a b =>
    show BalancedTensor.tmul (assocBimod Q ν ν' ν'' r (op (a ⊗ₜ[k] b) • r'))
        (assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃)) =
      BalancedTensor.tmul (assocBimod Q ν ν' ν'' r r')
        (assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul ((a ⊗ₜ[k] b) • n) n₃))
    rw [assocBimod_op_smul, BalancedTensor.op_smul_tmul, smul_assocJ_left]
  | add t t' ht ht' =>
    rw [op_add, add_smul, map_add, LinearMap.add_apply, ht, ht', add_smul, map_add]

variable (Q ν ν' ν'') in
/-- For fixed `r` and `n₃`: `y ↦ Φ (r ⊗ (y ⊗ n₃))` on `Ind_{ν,ν'} (N₁ ⊠ N₂)`. -/
def assocMid (r : IndBimod Q (ν + ν') ν'') (n₃ : N₃) :
    Ind Q ν ν' (ExtTensor k N₁ N₂) →ₗ[k] AssocR Q ν ν' ν'' N₁ N₂ N₃ :=
  BalancedTensor.lift (assocMidBil Q ν ν' ν'' N₁ N₂ N₃ r n₃)
    (fun r' t n => assocMidBil_balanced N₁ N₂ N₃ r n₃ r' t n)

theorem assocMid_tmul (r : IndBimod Q (ν + ν') ν'') (n₃ : N₃) (r' : IndBimod Q ν ν')
    (n : ExtTensor k N₁ N₂) :
    assocMid Q ν ν' ν'' N₁ N₂ N₃ r n₃ (BalancedTensor.tmul r' n) =
      BalancedTensor.tmul (assocBimod Q ν ν' ν'' r r')
        (assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃)) := rfl

variable (Q ν ν' ν'') in
/-- For fixed `r`: the bilinear map `(y, n₃) ↦ Φ (r ⊗ (y ⊗ n₃))`. -/
def assocOuterInner (r : IndBimod Q (ν + ν') ν'') :
    Ind Q ν ν' (ExtTensor k N₁ N₂) →ₗ[k] N₃ →ₗ[k] AssocR Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearMap.mk₂ k (fun y n₃ => assocMid Q ν ν' ν'' N₁ N₂ N₃ r n₃ y)
    (fun y y' n₃ => map_add _ y y')
    (fun c y n₃ => map_smul _ c y)
    (fun y n₃ n₃' => by
      beta_reduce
      induction y using BalancedTensor.induction_on with
      | zero => simp only [map_zero, add_zero]
      | tmul r' n => rw [assocMid_tmul, assocMid_tmul, assocMid_tmul, ExtTensor.tmul_add,
          map_add, BalancedTensor.tmul_add]
      | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy']; abel)
    (fun c y n₃ => by
      beta_reduce
      induction y using BalancedTensor.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul r' n => rw [assocMid_tmul, assocMid_tmul, ExtTensor.tmul_smul, map_smul,
          BalancedTensor.tmul_smul]
      | add y y' hy hy' => rw [map_add, map_add, hy, hy', smul_add])

theorem assocOuterInner_apply (r : IndBimod Q (ν + ν') ν'') (y : Ind Q ν ν' (ExtTensor k N₁ N₂))
    (n₃ : N₃) :
    assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ r y n₃ = assocMid Q ν ν' ν'' N₁ N₂ N₃ r n₃ y := rfl

theorem assocMid_add_left (r₁ r₂ : IndBimod Q (ν + ν') ν'') (n₃ : N₃)
    (y : Ind Q ν ν' (ExtTensor k N₁ N₂)) :
    assocMid Q ν ν' ν'' N₁ N₂ N₃ (r₁ + r₂) n₃ y =
      assocMid Q ν ν' ν'' N₁ N₂ N₃ r₁ n₃ y + assocMid Q ν ν' ν'' N₁ N₂ N₃ r₂ n₃ y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul r' n =>
    rw [assocMid_tmul, assocMid_tmul, assocMid_tmul, ← BalancedTensor.add_tmul]
    congr 1
    exact LinearMap.map_add₂ _ _ _ _
  | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy']; abel

theorem assocMid_smul_left (c : k) (r : IndBimod Q (ν + ν') ν'') (n₃ : N₃)
    (y : Ind Q ν ν' (ExtTensor k N₁ N₂)) :
    assocMid Q ν ν' ν'' N₁ N₂ N₃ (c • r) n₃ y = c • assocMid Q ν ν' ν'' N₁ N₂ N₃ r n₃ y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul r' n =>
    rw [assocMid_tmul, assocMid_tmul, ← BalancedTensor.smul_tmul]
    congr 1
    exact LinearMap.map_smul₂ _ _ _ _
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', smul_add]

theorem assocOuter_add_left (r₁ r₂ : IndBimod Q (ν + ν') ν'')
    (z : ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃) :
    ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ (r₁ + r₂)) z =
      ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ r₁) z +
        ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ r₂) z := by
  induction z using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul y n₃ =>
    rw [ExtTensor.lift_tmul, ExtTensor.lift_tmul, ExtTensor.lift_tmul, assocOuterInner_apply,
      assocOuterInner_apply, assocOuterInner_apply, assocMid_add_left]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']; abel

theorem assocOuter_smul_left (c : k) (r : IndBimod Q (ν + ν') ν'')
    (z : ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃) :
    ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ (c • r)) z =
      c • ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ r) z := by
  induction z using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul y n₃ =>
    rw [ExtTensor.lift_tmul, ExtTensor.lift_tmul, assocOuterInner_apply,
      assocOuterInner_apply, assocMid_smul_left]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', smul_add]

variable (Q ν ν' ν'') in
/-- The bilinear map inducing the associativity isomorphism. -/
def assocOuterBil : IndBimod Q (ν + ν') ν'' →ₗ[k]
    ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃ →ₗ[k] AssocR Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearMap.mk₂ k (fun r z => ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ r) z)
    (fun r₁ r₂ z => assocOuter_add_left N₁ N₂ N₃ r₁ r₂ z)
    (fun c r z => assocOuter_smul_left N₁ N₂ N₃ c r z)
    (fun _ z z' => map_add _ z z')
    (fun c _ z => map_smul _ c z)

theorem assocOuterBil_apply (r : IndBimod Q (ν + ν') ν'')
    (z : ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃) :
    assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ r z =
      ExtTensor.lift (assocOuterInner Q ν ν' ν'' N₁ N₂ N₃ r) z := rfl

theorem assocOuterBil_tmul (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν')
    (n : ExtTensor k N₁ N₂) (n₃ : N₃) :
    assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ r (ExtTensor.tmul (BalancedTensor.tmul r' n) n₃) =
      BalancedTensor.tmul (assocBimod Q ν ν' ν'' r r')
        (assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃)) := by
  rw [assocOuterBil_apply, ExtTensor.lift_tmul, assocOuterInner_apply, assocMid_tmul]

theorem assocOuterBil_balanced_tmul (r : IndBimod Q (ν + ν') ν'')
    (a' : KLRAlgebra k Q (ν + ν')) (d : KLRAlgebra k Q ν'') :
    assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ (op (a' ⊗ₜ[k] d) • r) =
      (assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ r).comp
        (DistribMulAction.toLinearMap k _ (a' ⊗ₜ[k] d)) := by
  refine extTensorInd_ext N₃ fun r' n n₃ => ?_
  rw [LinearMap.comp_apply, DistribMulAction.toLinearMap_apply, ExtTensor.smul_tmul,
    BalancedTensor.smul_tmul', assocOuterBil_tmul, assocOuterBil_tmul,
    assocBimod_op_smul_outer, BalancedTensor.op_smul_tmul, smul_assocJ_right]

theorem assocOuterBil_balanced (r : IndBimod Q (ν + ν') ν'')
    (t : TensorKLR Q (ν + ν') ν'') (z : ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃) :
    assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ (op t • r) z =
      assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ r (t • z) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [op_zero, zero_smul, zero_smul, map_zero, LinearMap.zero_apply, map_zero]
  | tmul a' d =>
    rw [assocOuterBil_balanced_tmul]; rfl
  | add t t' ht ht' =>
    rw [op_add, add_smul, map_add, LinearMap.add_apply, ht, ht', add_smul, map_add]

variable (Q ν ν' ν'') in
/-- **The associativity map**
`Ind_{ν+ν',ν''} (Ind_{ν,ν'} (N₁ ⊠ N₂) ⊠ N₃) → Ind_{ν,ν'+ν''} (N₁ ⊠ Ind_{ν',ν''} (N₂ ⊠ N₃))`. -/
def assocFwd : AssocL Q ν ν' ν'' N₁ N₂ N₃ →ₗ[k] AssocR Q ν ν' ν'' N₁ N₂ N₃ :=
  BalancedTensor.lift (assocOuterBil Q ν ν' ν'' N₁ N₂ N₃)
    (fun r t z => assocOuterBil_balanced N₁ N₂ N₃ r t z)

theorem assocFwd_tmul (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν')
    (n : ExtTensor k N₁ N₂) (n₃ : N₃) :
    assocFwd Q ν ν' ν'' N₁ N₂ N₃
        (BalancedTensor.tmul r (ExtTensor.tmul (BalancedTensor.tmul r' n) n₃)) =
      BalancedTensor.tmul (assocBimod Q ν ν' ν'' r r')
        (assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃)) := by
  rw [assocFwd, BalancedTensor.lift_tmul, assocOuterBil_tmul]

theorem assocBimod_smul (b : KLRAlgebra k Q (ν + ν' + ν'')) (r : IndBimod Q (ν + ν') ν'')
    (r' : IndBimod Q ν ν') :
    assocBimod Q ν ν' ν'' (b • r) r' = castKLR Q (add_assoc ν ν' ν'') b • assocBimod Q ν ν' ν'' r r' :=
  Subtype.ext (by
    rw [coe_assocBimod, Submodule.coe_smul, Submodule.coe_smul, coe_assocBimod, smul_eq_mul,
      smul_eq_mul, mul_assoc, map_mul])

theorem assocOuterBil_smul_tmul (b : KLRAlgebra k Q (ν + ν' + ν'')) (r : IndBimod Q (ν + ν') ν'')
    (r' : IndBimod Q ν ν') (n : ExtTensor k N₁ N₂) (n₃ : N₃) :
    assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ (b • r) (ExtTensor.tmul (BalancedTensor.tmul r' n) n₃) =
      castKLR Q (add_assoc ν ν' ν'') b •
        assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ r (ExtTensor.tmul (BalancedTensor.tmul r' n) n₃) := by
  rw [assocOuterBil_tmul, assocOuterBil_tmul, assocBimod_smul, BalancedTensor.smul_tmul']

theorem assocOuterBil_smul (b : KLRAlgebra k Q (ν + ν' + ν'')) (r : IndBimod Q (ν + ν') ν'')
    (z : ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃) :
    assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ (b • r) z =
      castKLR Q (add_assoc ν ν' ν'') b • assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ r z := by
  induction z using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul y n₃ =>
    induction y using BalancedTensor.induction_on with
    | zero => rw [ExtTensor.zero_tmul, map_zero, map_zero, smul_zero]
    | tmul r' n => exact assocOuterBil_smul_tmul N₁ N₂ N₃ b r r' n n₃
    | add y y' hy hy' => simp only [ExtTensor.add_tmul, map_add, hy, hy', smul_add]
  | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]

/-- The associativity map is semilinear along `castKLR : R((ν + ν') + ν'') ≃ R(ν + (ν' + ν''))`. -/
theorem assocFwd_smul (b : KLRAlgebra k Q (ν + ν' + ν'')) (x : AssocL Q ν ν' ν'' N₁ N₂ N₃) :
    assocFwd Q ν ν' ν'' N₁ N₂ N₃ (b • x) =
      castKLR Q (add_assoc ν ν' ν'') b • assocFwd Q ν ν' ν'' N₁ N₂ N₃ x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul r z =>
    rw [BalancedTensor.smul_tmul', assocFwd, BalancedTensor.lift_tmul, BalancedTensor.lift_tmul,
      assocOuterBil_smul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-! #### The backward map -/

theorem castKLR_symm_concatR (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν')
    (d : KLRAlgebra k Q ν'') :
    castKLR Q (add_assoc ν ν' ν'').symm (concat Q ν (ν' + ν'') (a ⊗ₜ concat Q ν' ν'' (b ⊗ₜ d))) =
      concat Q (ν + ν') ν'' (concat Q ν ν' (a ⊗ₜ b) ⊗ₜ d) := by
  rw [← concat_assoc, castKLR_symm_castAlg]

theorem assocBimod'_mem (r : IndBimod Q ν (ν' + ν'')) (r'' : IndBimod Q ν' ν'') :
    castKLR Q (add_assoc ν ν' ν'').symm
        ((r : KLRAlgebra k Q (ν + (ν' + ν''))) * concat Q ν (ν' + ν'') (1 ⊗ₜ (r'' :
          KLRAlgebra k Q (ν' + ν'')))) ∈ Graded.leftIdeal (oneConcat Q (ν + ν') ν'') := by
  rw [Graded.mem_leftIdeal]
  have h : concat Q ν (ν' + ν'') ((1 : KLRAlgebra k Q ν) ⊗ₜ (r'' : KLRAlgebra k Q (ν' + ν''))) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ (r'' : KLRAlgebra k Q (ν' + ν''))) *
        concat Q ν (ν' + ν'') (1 ⊗ₜ concat Q ν' ν'' (1 ⊗ₜ 1)) := by
    rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, concat_one_tmul_one,
      Graded.mem_leftIdeal.1 r''.2]
  rw [h, ← mul_assoc, map_mul, castKLR_symm_concatR, mul_assoc, concat_mul_oneConcat]

variable (Q ν ν' ν'') in
/-- `(r, r'') ↦ castKLR⁻¹ (r ι(1 ⊗ r''))`. -/
def assocBimod' :
    IndBimod Q ν (ν' + ν'') →ₗ[k] IndBimod Q ν' ν'' →ₗ[k] IndBimod Q (ν + ν') ν'' :=
  LinearMap.mk₂ k (fun r r'' => ⟨_, assocBimod'_mem r r''⟩)
    (fun r₁ r₂ r'' => Subtype.ext (by
      show castKLR Q _ (((r₁ : KLRAlgebra k Q (ν + (ν' + ν''))) +
        (r₂ : KLRAlgebra k Q (ν + (ν' + ν'')))) * _) = castKLR Q _ (_ * _) + castKLR Q _ (_ * _)
      rw [add_mul, map_add]))
    (fun c r r'' => Subtype.ext (by
      show castKLR Q _ ((c • (r : KLRAlgebra k Q (ν + (ν' + ν'')))) * _) =
        c • castKLR Q _ (_ * _)
      rw [smul_mul_assoc, map_smul]))
    (fun r r₁ r₂ => Subtype.ext (by
      show castKLR Q _ (_ * concat Q ν (ν' + ν'') (1 ⊗ₜ ((r₁ : KLRAlgebra k Q (ν' + ν'')) +
        (r₂ : KLRAlgebra k Q (ν' + ν''))))) = castKLR Q _ (_ * _) + castKLR Q _ (_ * _)
      rw [TensorProduct.tmul_add, map_add, mul_add, map_add]))
    (fun c r r'' => Subtype.ext (by
      show castKLR Q _ (_ * concat Q ν (ν' + ν'') (1 ⊗ₜ (c • (r'' : KLRAlgebra k Q (ν' + ν'')))))
        = c • castKLR Q _ (_ * _)
      rw [TensorProduct.tmul_smul, map_smul, mul_smul_comm, map_smul]))

@[simp] theorem coe_assocBimod' (r : IndBimod Q ν (ν' + ν'')) (r'' : IndBimod Q ν' ν'') :
    (assocBimod' Q ν ν' ν'' r r'' : KLRAlgebra k Q (ν + ν' + ν'')) =
      castKLR Q (add_assoc ν ν' ν'').symm ((r : KLRAlgebra k Q (ν + (ν' + ν''))) *
        concat Q ν (ν' + ν'') (1 ⊗ₜ (r'' : KLRAlgebra k Q (ν' + ν'')))) := rfl

theorem assocBimod'_op_smul (r : IndBimod Q ν (ν' + ν'')) (r'' : IndBimod Q ν' ν'')
    (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'') :
    assocBimod' Q ν ν' ν'' r (op (b ⊗ₜ[k] d) • r'') =
      op (concat Q ν ν' (1 ⊗ₜ b) ⊗ₜ[k] d) • assocBimod' Q ν ν' ν'' r r'' := by
  apply Subtype.ext
  rw [coe_op_smul, coe_assocBimod', coe_assocBimod', coe_op_smul, unop_op, unop_op,
    ← castKLR_symm_concatR, ← map_mul, mul_assoc, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem assocBimod'_op_smul_outer (r : IndBimod Q ν (ν' + ν'')) (r'' : IndBimod Q ν' ν'')
    (a : KLRAlgebra k Q ν) (Y : KLRAlgebra k Q (ν' + ν'')) :
    assocBimod' Q ν ν' ν'' (op (a ⊗ₜ[k] Y) • r) r'' =
      op (concat Q ν ν' (a ⊗ₜ 1) ⊗ₜ[k] (1 : KLRAlgebra k Q ν'')) •
        assocBimod' Q ν ν' ν'' r (Y • r'') := by
  apply Subtype.ext
  rw [coe_op_smul, coe_assocBimod', coe_assocBimod', coe_op_smul, unop_op, unop_op,
    Submodule.coe_smul, smul_eq_mul]
  have h1 : concat Q ν (ν' + ν'') (a ⊗ₜ Y) *
      concat Q ν (ν' + ν'') (1 ⊗ₜ (r'' : KLRAlgebra k Q (ν' + ν''))) =
      concat Q ν (ν' + ν'') (1 ⊗ₜ (Y * r'')) *
        concat Q ν (ν' + ν'') (a ⊗ₜ oneConcat Q ν' ν'') := by
    rw [← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc,
      Graded.mem_leftIdeal.1 r''.2]
  have h2 : castKLR Q (add_assoc ν ν' ν'').symm
      (concat Q ν (ν' + ν'') (a ⊗ₜ oneConcat Q ν' ν'')) =
      concat Q (ν + ν') ν'' (concat Q ν ν' (a ⊗ₜ 1) ⊗ₜ 1) := by
    rw [← concat_one_tmul_one, castKLR_symm_concatR]
  rw [mul_assoc, h1, ← mul_assoc, map_mul, h2]

variable (Q ν ν') in
/-- `n ↦ 1_{ν,ν'} ⊗ n`. -/
def assocW' : ExtTensor k N₁ N₂ →ₗ[k] Ind Q ν ν' (ExtTensor k N₁ N₂) :=
  BalancedTensor.mkBil k (KLRAlgebra k Q (ν + ν')) (TensorKLR Q ν ν') (IndBimod Q ν ν')
    (ExtTensor k N₁ N₂) (oneBimod Q ν ν')

variable (Q ν ν') in
/-- `n₁ ⊗ (n₂ ⊗ n₃) ↦ (1_{ν,ν'} ⊗ (n₁ ⊗ n₂)) ⊗ n₃`. -/
def assocJ' : ExtTensor k N₁ (ExtTensor k N₂ N₃) →ₗ[k]
    ExtTensor k (Ind Q ν ν' (ExtTensor k N₁ N₂)) N₃ :=
  (TensorProduct.map (assocW' Q ν ν' N₁ N₂) LinearMap.id).comp
    (TensorProduct.assoc k N₁ N₂ N₃).symm.toLinearMap

theorem assocJ'_tmul (n₁ : N₁) (n₂ : N₂) (n₃ : N₃) :
    assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ (ExtTensor.tmul n₂ n₃)) =
      ExtTensor.tmul (BalancedTensor.tmul (oneBimod Q ν ν') (ExtTensor.tmul n₁ n₂)) n₃ :=
  rfl

theorem smul_assocJ'_right (b : KLRAlgebra k Q ν') (d : KLRAlgebra k Q ν'')
    (n₁ : N₁) (m : ExtTensor k N₂ N₃) :
    (concat Q ν ν' (1 ⊗ₜ b) ⊗ₜ[k] d) • assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m) =
      assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ ((b ⊗ₜ[k] d) • m)) := by
  induction m using ExtTensor.induction_on with
  | zero => simp
  | tmul n₂ n₃ =>
    rw [assocJ'_tmul, ExtTensor.smul_tmul, concat_smul_tmul_oneBimod, ExtTensor.smul_tmul,
      ExtTensor.smul_tmul, one_smul, assocJ'_tmul]
  | add m m' hm hm' => rw [ExtTensor.tmul_add, map_add, smul_add, hm, hm', smul_add,
      ExtTensor.tmul_add, map_add]

theorem smul_assocJ'_left (a : KLRAlgebra k Q ν) (n₁ : N₁) (m : ExtTensor k N₂ N₃) :
    (concat Q ν ν' (a ⊗ₜ 1) ⊗ₜ[k] (1 : KLRAlgebra k Q ν'')) •
        assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m) =
      assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul (a • n₁) m) := by
  induction m using ExtTensor.induction_on with
  | zero => simp
  | tmul n₂ n₃ =>
    rw [assocJ'_tmul, ExtTensor.smul_tmul, concat_smul_tmul_oneBimod, ExtTensor.smul_tmul,
      one_smul, one_smul, assocJ'_tmul]
  | add m m' hm hm' => rw [ExtTensor.tmul_add, map_add, smul_add, hm, hm',
      ExtTensor.tmul_add, map_add]

variable (Q ν ν' ν'') in
/-- For fixed `r` and `n₁`: `(r'', m) ↦ castKLR⁻¹ (r ι(1 ⊗ r'')) ⊗ J' (n₁ ⊗ m)`. -/
def assocMidBil' (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) :
    IndBimod Q ν' ν'' →ₗ[k] ExtTensor k N₂ N₃ →ₗ[k] AssocL Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearMap.mk₂ k (fun r'' m => BalancedTensor.tmul (assocBimod' Q ν ν' ν'' r r'')
      (assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m)))
    (fun r''₁ r''₂ m => by
      beta_reduce; simp only [map_add, LinearMap.add_apply, BalancedTensor.add_tmul])
    (fun c r'' m => by
      beta_reduce; simp only [map_smul, LinearMap.smul_apply, BalancedTensor.smul_tmul])
    (fun r'' m m' => by
      beta_reduce; simp only [ExtTensor.tmul_add, map_add, BalancedTensor.tmul_add])
    (fun c r'' m => by
      beta_reduce; simp only [ExtTensor.tmul_smul, map_smul, BalancedTensor.tmul_smul])

theorem assocMidBil'_apply (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'')
    (m : ExtTensor k N₂ N₃) :
    assocMidBil' Q ν ν' ν'' N₁ N₂ N₃ r n₁ r'' m = BalancedTensor.tmul
      (assocBimod' Q ν ν' ν'' r r'') (assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m)) := rfl

theorem assocMidBil'_balanced (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'')
    (t : TensorKLR Q ν' ν'') (m : ExtTensor k N₂ N₃) :
    assocMidBil' Q ν ν' ν'' N₁ N₂ N₃ r n₁ (op t • r'') m =
      assocMidBil' Q ν ν' ν'' N₁ N₂ N₃ r n₁ r'' (t • m) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [op_zero, zero_smul, map_zero, LinearMap.zero_apply]
  | tmul b d =>
    rw [assocMidBil'_apply, assocMidBil'_apply, assocBimod'_op_smul,
      BalancedTensor.op_smul_tmul, smul_assocJ'_right]
  | add t t' ht ht' =>
    simp only [op_add, add_smul, map_add, LinearMap.add_apply, ht, ht']

variable (Q ν ν' ν'') in
/-- For fixed `r` and `n₁`: `y ↦ Ψ (r ⊗ (n₁ ⊗ y))` on `Ind_{ν',ν''} (N₂ ⊠ N₃)`. -/
def assocMid' (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) :
    Ind Q ν' ν'' (ExtTensor k N₂ N₃) →ₗ[k] AssocL Q ν ν' ν'' N₁ N₂ N₃ :=
  BalancedTensor.lift (assocMidBil' Q ν ν' ν'' N₁ N₂ N₃ r n₁)
    (fun r'' t m => assocMidBil'_balanced N₁ N₂ N₃ r n₁ r'' t m)

theorem assocMid'_tmul (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'')
    (m : ExtTensor k N₂ N₃) :
    assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁ (BalancedTensor.tmul r'' m) = BalancedTensor.tmul
      (assocBimod' Q ν ν' ν'' r r'') (assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m)) := by
  rw [assocMid', BalancedTensor.lift_tmul, assocMidBil'_apply]

theorem assocMid'_add_left (r₁ r₂ : IndBimod Q ν (ν' + ν'')) (n₁ : N₁)
    (y : Ind Q ν' ν'' (ExtTensor k N₂ N₃)) :
    assocMid' Q ν ν' ν'' N₁ N₂ N₃ (r₁ + r₂) n₁ y =
      assocMid' Q ν ν' ν'' N₁ N₂ N₃ r₁ n₁ y + assocMid' Q ν ν' ν'' N₁ N₂ N₃ r₂ n₁ y := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul r'' m =>
    rw [assocMid'_tmul, assocMid'_tmul, assocMid'_tmul, ← BalancedTensor.add_tmul]
    congr 1
    exact LinearMap.map_add₂ _ _ _ _
  | add y y' hy hy' => simp only [map_add, hy, hy']; abel

theorem assocMid'_smul_left (c : k) (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁)
    (y : Ind Q ν' ν'' (ExtTensor k N₂ N₃)) :
    assocMid' Q ν ν' ν'' N₁ N₂ N₃ (c • r) n₁ y = c • assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁ y := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul r'' m =>
    rw [assocMid'_tmul, assocMid'_tmul, ← BalancedTensor.smul_tmul]
    congr 1
    exact LinearMap.map_smul₂ _ _ _ _
  | add y y' hy hy' => simp only [map_add, hy, hy', smul_add]

theorem assocMid'_add_n (r : IndBimod Q ν (ν' + ν'')) (n₁ n₁' : N₁)
    (y : Ind Q ν' ν'' (ExtTensor k N₂ N₃)) :
    assocMid' Q ν ν' ν'' N₁ N₂ N₃ r (n₁ + n₁') y =
      assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁ y + assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁' y := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul r'' m =>
    rw [assocMid'_tmul, assocMid'_tmul, assocMid'_tmul, ExtTensor.add_tmul, map_add,
      BalancedTensor.tmul_add]
  | add y y' hy hy' => simp only [map_add, hy, hy']; abel

theorem assocMid'_smul_n (c : k) (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁)
    (y : Ind Q ν' ν'' (ExtTensor k N₂ N₃)) :
    assocMid' Q ν ν' ν'' N₁ N₂ N₃ r (c • n₁) y = c • assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁ y := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul r'' m =>
    rw [assocMid'_tmul, assocMid'_tmul, ← ExtTensor.smul_tmul', map_smul,
      BalancedTensor.tmul_smul]
  | add y y' hy hy' => simp only [map_add, hy, hy', smul_add]

variable (Q ν ν' ν'') in
/-- For fixed `r`: the bilinear map `(n₁, y) ↦ Ψ (r ⊗ (n₁ ⊗ y))`. -/
def assocOuterInner' (r : IndBimod Q ν (ν' + ν'')) :
    N₁ →ₗ[k] Ind Q ν' ν'' (ExtTensor k N₂ N₃) →ₗ[k] AssocL Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearMap.mk₂ k (fun n₁ y => assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁ y)
    (fun n₁ n₁' y => assocMid'_add_n N₁ N₂ N₃ r n₁ n₁' y)
    (fun c n₁ y => assocMid'_smul_n N₁ N₂ N₃ c r n₁ y)
    (fun _ y y' => map_add _ y y')
    (fun c _ y => map_smul _ c y)

theorem assocOuterInner'_apply (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁)
    (y : Ind Q ν' ν'' (ExtTensor k N₂ N₃)) :
    assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ r n₁ y = assocMid' Q ν ν' ν'' N₁ N₂ N₃ r n₁ y := rfl

theorem assocOuter'_add_left (r₁ r₂ : IndBimod Q ν (ν' + ν''))
    (z : ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃))) :
    ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ (r₁ + r₂)) z =
      ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ r₁) z +
        ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ r₂) z := by
  induction z using ExtTensor.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul n₁ y =>
    rw [ExtTensor.lift_tmul, ExtTensor.lift_tmul, ExtTensor.lift_tmul, assocOuterInner'_apply,
      assocOuterInner'_apply, assocOuterInner'_apply, assocMid'_add_left]
  | add z z' hz hz' => simp only [map_add, hz, hz']; abel

theorem assocOuter'_smul_left (c : k) (r : IndBimod Q ν (ν' + ν''))
    (z : ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃))) :
    ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ (c • r)) z =
      c • ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ r) z := by
  induction z using ExtTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul n₁ y =>
    rw [ExtTensor.lift_tmul, ExtTensor.lift_tmul, assocOuterInner'_apply,
      assocOuterInner'_apply, assocMid'_smul_left]
  | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]

variable (Q ν ν' ν'') in
/-- The bilinear map inducing the inverse associativity isomorphism. -/
def assocOuterBil' : IndBimod Q ν (ν' + ν'') →ₗ[k]
    ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃)) →ₗ[k] AssocL Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearMap.mk₂ k (fun r z => ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ r) z)
    (fun r₁ r₂ z => assocOuter'_add_left N₁ N₂ N₃ r₁ r₂ z)
    (fun c r z => assocOuter'_smul_left N₁ N₂ N₃ c r z)
    (fun _ z z' => map_add _ z z')
    (fun c _ z => map_smul _ c z)

theorem assocOuterBil'_apply (r : IndBimod Q ν (ν' + ν''))
    (z : ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃))) :
    assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃ r z =
      ExtTensor.lift (assocOuterInner' Q ν ν' ν'' N₁ N₂ N₃ r) z := rfl

theorem assocOuterBil'_tmul (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'')
    (m : ExtTensor k N₂ N₃) :
    assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃ r (ExtTensor.tmul n₁ (BalancedTensor.tmul r'' m)) =
      BalancedTensor.tmul (assocBimod' Q ν ν' ν'' r r'')
        (assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m)) := by
  rw [assocOuterBil'_apply, ExtTensor.lift_tmul, assocOuterInner'_apply, assocMid'_tmul]

theorem assocOuterBil'_balanced_tmul (r : IndBimod Q ν (ν' + ν'')) (a : KLRAlgebra k Q ν)
    (Y : KLRAlgebra k Q (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'')
    (m : ExtTensor k N₂ N₃) :
    assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃ (op (a ⊗ₜ[k] Y) • r)
        (ExtTensor.tmul n₁ (BalancedTensor.tmul r'' m)) =
      assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃ r
        ((a ⊗ₜ[k] Y) • ExtTensor.tmul n₁ (BalancedTensor.tmul r'' m)) := by
  rw [ExtTensor.smul_tmul, BalancedTensor.smul_tmul', assocOuterBil'_tmul, assocOuterBil'_tmul,
    assocBimod'_op_smul_outer, BalancedTensor.op_smul_tmul, smul_assocJ'_left]

theorem assocOuterBil'_balanced (r : IndBimod Q ν (ν' + ν''))
    (t : TensorKLR Q ν (ν' + ν'')) (z : ExtTensor k N₁ (Ind Q ν' ν'' (ExtTensor k N₂ N₃))) :
    assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃ (op t • r) z =
      assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃ r (t • z) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [op_zero, zero_smul, map_zero, LinearMap.zero_apply]
  | tmul a Y =>
    induction z using ExtTensor.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul n₁ y =>
      induction y using BalancedTensor.induction_on with
      | zero => simp only [ExtTensor.tmul_zero, map_zero, smul_zero]
      | tmul r'' m => exact assocOuterBil'_balanced_tmul N₁ N₂ N₃ r a Y n₁ r'' m
      | add y y' hy hy' => simp only [ExtTensor.tmul_add, map_add, smul_add, hy, hy']
    | add z z' hz hz' => simp only [map_add, smul_add, hz, hz']
  | add t t' ht ht' =>
    simp only [op_add, add_smul, map_add, LinearMap.add_apply, ht, ht']

variable (Q ν ν' ν'') in
/-- **The inverse associativity map**. -/
def assocBwd : AssocR Q ν ν' ν'' N₁ N₂ N₃ →ₗ[k] AssocL Q ν ν' ν'' N₁ N₂ N₃ :=
  BalancedTensor.lift (assocOuterBil' Q ν ν' ν'' N₁ N₂ N₃)
    (fun r t z => assocOuterBil'_balanced N₁ N₂ N₃ r t z)

theorem assocBwd_tmul (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'')
    (m : ExtTensor k N₂ N₃) :
    assocBwd Q ν ν' ν'' N₁ N₂ N₃
        (BalancedTensor.tmul r (ExtTensor.tmul n₁ (BalancedTensor.tmul r'' m))) =
      BalancedTensor.tmul (assocBimod' Q ν ν' ν'' r r'')
        (assocJ' Q ν ν' N₁ N₂ N₃ (ExtTensor.tmul n₁ m)) := by
  rw [assocBwd, BalancedTensor.lift_tmul, assocOuterBil'_tmul]

/-! #### The two maps are mutually inverse -/

theorem assocL_induction {P : AssocL Q ν ν' ν'' N₁ N₂ N₃ → Prop} (x : AssocL Q ν ν' ν'' N₁ N₂ N₃)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν') (n₁ : N₁) (n₂ : N₂) (n₃ : N₃),
      P (BalancedTensor.tmul r (ExtTensor.tmul (BalancedTensor.tmul r'
        (ExtTensor.tmul n₁ n₂)) n₃))) : P x := by
  induction x using BalancedTensor.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | tmul r z =>
    induction z using ExtTensor.induction_on with
    | zero => rw [BalancedTensor.tmul_zero]; exact h0
    | add z z' hz hz' => rw [BalancedTensor.tmul_add]; exact hadd _ _ hz hz'
    | tmul y n₃ =>
      induction y using BalancedTensor.induction_on with
      | zero => rw [ExtTensor.zero_tmul, BalancedTensor.tmul_zero]; exact h0
      | add y y' hy hy' =>
        rw [ExtTensor.add_tmul, BalancedTensor.tmul_add]; exact hadd _ _ hy hy'
      | tmul r' n =>
        induction n using ExtTensor.induction_on with
        | zero => rw [BalancedTensor.tmul_zero, ExtTensor.zero_tmul, BalancedTensor.tmul_zero];
                  exact h0
        | add n n' hn hn' =>
          rw [BalancedTensor.tmul_add, ExtTensor.add_tmul, BalancedTensor.tmul_add]
          exact hadd _ _ hn hn'
        | tmul n₁ n₂ => exact hgen r r' n₁ n₂ n₃

theorem assocR_induction {P : AssocR Q ν ν' ν'' N₁ N₂ N₃ → Prop} (x : AssocR Q ν ν' ν'' N₁ N₂ N₃)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (r : IndBimod Q ν (ν' + ν'')) (n₁ : N₁) (r'' : IndBimod Q ν' ν'') (n₂ : N₂)
      (n₃ : N₃), P (BalancedTensor.tmul r (ExtTensor.tmul n₁ (BalancedTensor.tmul r''
        (ExtTensor.tmul n₂ n₃))))) : P x := by
  induction x using BalancedTensor.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | tmul r z =>
    induction z using ExtTensor.induction_on with
    | zero => rw [BalancedTensor.tmul_zero]; exact h0
    | add z z' hz hz' => rw [BalancedTensor.tmul_add]; exact hadd _ _ hz hz'
    | tmul n₁ y =>
      induction y using BalancedTensor.induction_on with
      | zero => rw [ExtTensor.tmul_zero, BalancedTensor.tmul_zero]; exact h0
      | add y y' hy hy' =>
        rw [ExtTensor.tmul_add, BalancedTensor.tmul_add]; exact hadd _ _ hy hy'
      | tmul r'' m =>
        induction m using ExtTensor.induction_on with
        | zero => rw [BalancedTensor.tmul_zero, ExtTensor.tmul_zero, BalancedTensor.tmul_zero];
                  exact h0
        | add m m' hm hm' =>
          rw [BalancedTensor.tmul_add, ExtTensor.tmul_add, BalancedTensor.tmul_add]
          exact hadd _ _ hm hm'
        | tmul n₂ n₃ => exact hgen r n₁ r'' n₂ n₃

theorem smul_oneBimod {μ μ' : Multiset I} (r : IndBimod Q μ μ') :
    (r : KLRAlgebra k Q (μ + μ')) • oneBimod Q μ μ' = r :=
  Subtype.ext (Graded.mem_leftIdeal.1 r.2)

theorem assocBimod_assocBimod' (r : IndBimod Q ν (ν' + ν'')) (r'' : IndBimod Q ν' ν'') :
    assocBimod Q ν ν' ν'' (assocBimod' Q ν ν' ν'' r r'') (oneBimod Q ν ν') =
      op ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] (r'' : KLRAlgebra k Q (ν' + ν''))) • r := by
  apply Subtype.ext
  rw [coe_assocBimod, coe_assocBimod', coe_oneBimod, coe_op_smul, unop_op, map_mul,
    castKLR_castAlg_symm, ← concatL_one_eq, castKLR_concatL_one, concatR_one_eq, mul_assoc,
    ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Graded.mem_leftIdeal.1 r''.2]

theorem assocBimod'_assocBimod (r : IndBimod Q (ν + ν') ν'') (r' : IndBimod Q ν ν') :
    assocBimod' Q ν ν' ν'' (assocBimod Q ν ν' ν'' r r') (oneBimod Q ν' ν'') =
      op ((r' : KLRAlgebra k Q (ν + ν')) ⊗ₜ[k] (1 : KLRAlgebra k Q ν'')) • r := by
  apply Subtype.ext
  have hsymm : castKLR Q (add_assoc ν ν' ν'').symm (concatR ν ν' ν'' 1 1 1) =
      concatL ν ν' ν'' 1 1 1 := by
    rw [← castKLR_concatL_one, castKLR_symm_castAlg]
  rw [coe_assocBimod', coe_assocBimod, coe_oneBimod, coe_op_smul, unop_op, map_mul,
    castKLR_symm_castAlg, ← concatR_one_eq, hsymm, concatL_one_eq, mul_assoc,
    ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Graded.mem_leftIdeal.1 r'.2]

theorem assocFwd_assocBwd (x : AssocR Q ν ν' ν'' N₁ N₂ N₃) :
    assocFwd Q ν ν' ν'' N₁ N₂ N₃ (assocBwd Q ν ν' ν'' N₁ N₂ N₃ x) = x := by
  induction x using assocR_induction with
  | h0 => simp only [map_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hgen r n₁ r'' n₂ n₃ =>
    rw [assocBwd_tmul, assocJ'_tmul, assocFwd_tmul, assocJ_tmul, assocBimod_assocBimod',
      BalancedTensor.op_smul_tmul, ExtTensor.smul_tmul, one_smul, BalancedTensor.smul_tmul',
      smul_oneBimod]

theorem assocBwd_assocFwd (x : AssocL Q ν ν' ν'' N₁ N₂ N₃) :
    assocBwd Q ν ν' ν'' N₁ N₂ N₃ (assocFwd Q ν ν' ν'' N₁ N₂ N₃ x) = x := by
  induction x using assocL_induction with
  | h0 => simp only [map_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hgen r r' n₁ n₂ n₃ =>
    rw [assocFwd_tmul, assocJ_tmul, assocBwd_tmul, assocJ'_tmul, assocBimod'_assocBimod,
      BalancedTensor.op_smul_tmul, ExtTensor.smul_tmul, one_smul, BalancedTensor.smul_tmul',
      smul_oneBimod]

variable (Q ν ν' ν'') in
/-- **Associativity of induction**:
`Ind_{ν+ν',ν''} (Ind_{ν,ν'} (N₁ ⊠ N₂) ⊠ N₃) ≅ Ind_{ν,ν'+ν''} (N₁ ⊠ Ind_{ν',ν''} (N₂ ⊠ N₃))`,
a `k`-linear isomorphism which is semilinear along `castKLR` (`assocEquiv_smul`). -/
def assocEquiv : AssocL Q ν ν' ν'' N₁ N₂ N₃ ≃ₗ[k] AssocR Q ν ν' ν'' N₁ N₂ N₃ :=
  LinearEquiv.ofLinear (assocFwd Q ν ν' ν'' N₁ N₂ N₃) (assocBwd Q ν ν' ν'' N₁ N₂ N₃)
    (LinearMap.ext fun x => assocFwd_assocBwd N₁ N₂ N₃ x)
    (LinearMap.ext fun x => assocBwd_assocFwd N₁ N₂ N₃ x)

theorem assocEquiv_apply (x : AssocL Q ν ν' ν'' N₁ N₂ N₃) :
    assocEquiv Q ν ν' ν'' N₁ N₂ N₃ x = assocFwd Q ν ν' ν'' N₁ N₂ N₃ x := rfl

theorem assocEquiv_smul (b : KLRAlgebra k Q (ν + ν' + ν'')) (x : AssocL Q ν ν' ν'' N₁ N₂ N₃) :
    assocEquiv Q ν ν' ν'' N₁ N₂ N₃ (b • x) =
      castKLR Q (add_assoc ν ν' ν'') b • assocEquiv Q ν ν' ν'' N₁ N₂ N₃ x :=
  assocFwd_smul N₁ N₂ N₃ b x

end Assoc

/-! ### Unitality of induction -/

section Unit

variable {ν : Multiset I}
  (N : Type*) [AddCommGroup N] [Module k N] [Module (KLRAlgebra k Q ν) N]
    [IsScalarTower k (KLRAlgebra k Q ν) N]

variable (Q ν) in
/-- `Ind_{0,ν} (R(0) ⊠ N)`. -/
abbrev UnitL : Type _ := Ind Q 0 ν (ExtTensor k (KLRAlgebra k Q 0) N)

variable (Q ν) in
/-- `Ind_{ν,0} (N ⊠ R(0))`. -/
abbrev UnitR : Type _ := Ind Q ν 0 (ExtTensor k N (KLRAlgebra k Q 0))

theorem concat_one_tmul_eq_castAlg_symm (b : KLRAlgebra k Q ν) :
    concat Q 0 ν (1 ⊗ₜ b) = castKLR Q (zero_add ν).symm b := by
  apply (castKLR Q (zero_add ν)).injective
  rw [castKLR_castAlg_symm, concat_one_left]

theorem concat_tmul_one_eq_castAlg_symm (b : KLRAlgebra k Q ν) :
    concat Q ν 0 (b ⊗ₜ 1) = castKLR Q (add_zero ν).symm b := by
  apply (castKLR Q (add_zero ν)).injective
  rw [castKLR_castAlg_symm, concat_one_right]

variable (Q ν) in
/-- `(r, a ⊗ n) ↦ castKLR (r ι(a ⊗ 1)) n`. -/
def unitLBil : IndBimod Q 0 ν →ₗ[k] ExtTensor k (KLRAlgebra k Q 0) N →ₗ[k] N :=
  LinearMap.mk₂ k (fun r z => ExtTensor.lift
      (LinearMap.mk₂ k (fun a n => castKLR Q (zero_add ν)
          ((r : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a ⊗ₜ 1)) • n)
        (fun a a' n => by beta_reduce; rw [TensorProduct.add_tmul, map_add, mul_add, map_add,
          add_smul])
        (fun c a n => by beta_reduce; rw [← TensorProduct.smul_tmul', map_smul, mul_smul_comm,
          map_smul, smul_assoc])
        (fun a n n' => by beta_reduce; rw [smul_add])
        (fun c a n => by beta_reduce; rw [smul_comm])) z)
    (fun r r' z => by
      beta_reduce
      induction z using ExtTensor.induction_on with
      | zero => simp only [map_zero, add_zero]
      | tmul a n =>
        simp only [ExtTensor.lift_tmul, LinearMap.mk₂_apply, Submodule.coe_add, add_mul,
          map_add, add_smul]
      | add z z' hz hz' => simp only [map_add, hz, hz']; abel)
    (fun c r z => by
      beta_reduce
      induction z using ExtTensor.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul a n =>
        simp only [ExtTensor.lift_tmul, LinearMap.mk₂_apply, Submodule.coe_smul_of_tower,
          smul_mul_assoc, map_smul, smul_assoc]
      | add z z' hz hz' => simp only [map_add, hz, hz', smul_add])
    (fun _ z z' => map_add _ z z')
    (fun c _ z => map_smul _ c z)

theorem unitLBil_tmul (r : IndBimod Q 0 ν) (a : KLRAlgebra k Q 0) (n : N) :
    unitLBil Q ν N r (ExtTensor.tmul a n) =
      castKLR Q (zero_add ν) ((r : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a ⊗ₜ 1)) • n := rfl

theorem unitLBil_balanced (r : IndBimod Q 0 ν) (t : TensorKLR Q 0 ν)
    (z : ExtTensor k (KLRAlgebra k Q 0) N) :
    unitLBil Q ν N (op t • r) z = unitLBil Q ν N r (t • z) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [op_zero, zero_smul, map_zero, LinearMap.zero_apply]
  | tmul a' b =>
    induction z using ExtTensor.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul a n =>
      rw [ExtTensor.smul_tmul, unitLBil_tmul, unitLBil_tmul, coe_op_smul, unop_op, smul_eq_mul]
      have : concat Q 0 ν (a' ⊗ₜ b) * concat Q 0 ν (a ⊗ₜ 1) =
          concat Q 0 ν ((a' * a) ⊗ₜ 1) * concat Q 0 ν (1 ⊗ₜ b) := by
        rw [← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one]
      rw [mul_assoc, this, ← mul_assoc, map_mul, concat_one_tmul_eq_castAlg_symm,
        castKLR_castAlg_symm, mul_smul]
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
  | add t t' ht ht' => simp only [op_add, add_smul, map_add, LinearMap.add_apply, ht, ht']

variable (Q ν) in
/-- The map `Ind_{0,ν} (R(0) ⊠ N) → N`. -/
def unitLFwd : UnitL Q ν N →ₗ[k] N :=
  BalancedTensor.lift (unitLBil Q ν N) (fun r t z => unitLBil_balanced N r t z)

theorem unitLFwd_tmul (r : IndBimod Q 0 ν) (a : KLRAlgebra k Q 0) (n : N) :
    unitLFwd Q ν N (BalancedTensor.tmul r (ExtTensor.tmul a n)) =
      castKLR Q (zero_add ν) ((r : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a ⊗ₜ 1)) • n := by
  rw [unitLFwd, BalancedTensor.lift_tmul, unitLBil_tmul]

variable (Q ν) in
/-- The map `N → Ind_{0,ν} (R(0) ⊠ N)`, `n ↦ 1_{0,ν} ⊗ (1 ⊗ n)`. -/
def unitLBwd : N →ₗ[k] UnitL Q ν N where
  toFun n := BalancedTensor.tmul (oneBimod Q 0 ν) (ExtTensor.tmul 1 n)
  map_add' n n' := by simp only [ExtTensor.tmul_add, BalancedTensor.tmul_add]
  map_smul' c n := by simp only [ExtTensor.tmul_smul, BalancedTensor.tmul_smul,
    RingHom.id_apply]

theorem unitLBwd_smul (b : KLRAlgebra k Q ν) (n : N) :
    unitLBwd Q ν N (b • n) = castKLR Q (zero_add ν).symm b • unitLBwd Q ν N n := by
  show BalancedTensor.tmul (oneBimod Q 0 ν) (ExtTensor.tmul 1 (b • n)) =
    castKLR Q (zero_add ν).symm b • BalancedTensor.tmul (oneBimod Q 0 ν) (ExtTensor.tmul 1 n)
  rw [← concat_one_tmul_eq_castAlg_symm, concat_smul_tmul_oneBimod, ExtTensor.smul_tmul,
    one_smul]

theorem unitLFwd_smul (b : KLRAlgebra k Q (0 + ν)) (x : UnitL Q ν N) :
    unitLFwd Q ν N (b • x) = castKLR Q (zero_add ν) b • unitLFwd Q ν N x := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul r z =>
    rw [BalancedTensor.smul_tmul']
    induction z using ExtTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero, smul_zero]
    | tmul a n =>
      rw [unitLFwd_tmul, unitLFwd_tmul, Submodule.coe_smul, smul_eq_mul, mul_assoc, map_mul,
        mul_smul]
    | add z z' hz hz' => simp only [BalancedTensor.tmul_add, map_add, hz, hz', smul_add]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem unitLFwd_unitLBwd (n : N) : unitLFwd Q ν N (unitLBwd Q ν N n) = n := by
  show unitLFwd Q ν N (BalancedTensor.tmul (oneBimod Q 0 ν) (ExtTensor.tmul 1 n)) = n
  rw [unitLFwd_tmul, coe_oneBimod, concat_one_tmul_one, (oneConcat_idem (ν := 0) (ν' := ν)).eq,
    castKLR_oneConcat_zero_left, one_smul]

theorem unitLBwd_unitLFwd (x : UnitL Q ν N) : unitLBwd Q ν N (unitLFwd Q ν N x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r z =>
    induction z using ExtTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | tmul a n =>
      rw [unitLFwd_tmul, unitLBwd_smul, castKLR_symm_castAlg]
      show BalancedTensor.tmul (((r : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a ⊗ₜ 1)) •
        oneBimod Q 0 ν) (ExtTensor.tmul 1 n) = _
      rw [show ((r : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a ⊗ₜ 1)) • oneBimod Q 0 ν =
          op (a ⊗ₜ[k] (1 : KLRAlgebra k Q ν)) • r from Subtype.ext (by
            show (r : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a ⊗ₜ 1) * oneConcat Q 0 ν = _
            rw [mul_assoc, concat_mul_oneConcat]; rfl),
        BalancedTensor.op_smul_tmul, ExtTensor.smul_tmul, smul_eq_mul, mul_one, one_smul]
    | add z z' hz hz' => simp only [BalancedTensor.tmul_add, map_add, hz, hz']
  | add x y hx hy => simp only [map_add, hx, hy]

variable (Q ν) in
/-- **Left unitality of induction**: `Ind_{0,ν} (R(0) ⊠ N) ≅ N`, semilinear along
`castKLR : R(0 + ν) ≃ R(ν)` (`unitLEquiv_smul`). -/
def unitLEquiv : UnitL Q ν N ≃ₗ[k] N :=
  LinearEquiv.ofLinear (unitLFwd Q ν N) (unitLBwd Q ν N)
    (LinearMap.ext fun n => unitLFwd_unitLBwd N n)
    (LinearMap.ext fun x => unitLBwd_unitLFwd N x)

theorem unitLEquiv_smul (b : KLRAlgebra k Q (0 + ν)) (x : UnitL Q ν N) :
    unitLEquiv Q ν N (b • x) = castKLR Q (zero_add ν) b • unitLEquiv Q ν N x :=
  unitLFwd_smul N b x

variable (Q ν) in
/-- `(r, n ⊗ a) ↦ castKLR (r ι(1 ⊗ a)) n`. -/
def unitRBil : IndBimod Q ν 0 →ₗ[k] ExtTensor k N (KLRAlgebra k Q 0) →ₗ[k] N :=
  LinearMap.mk₂ k (fun r z => ExtTensor.lift
      (LinearMap.mk₂ k (fun n a => castKLR Q (add_zero ν)
          ((r : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a)) • n)
        (fun n n' a => by beta_reduce; rw [smul_add])
        (fun c n a => by beta_reduce; rw [smul_comm])
        (fun n a a' => by beta_reduce; rw [TensorProduct.tmul_add, map_add, mul_add, map_add,
          add_smul])
        (fun c n a => by beta_reduce; rw [TensorProduct.tmul_smul, map_smul, mul_smul_comm,
          map_smul, smul_assoc])) z)
    (fun r r' z => by
      beta_reduce
      induction z using ExtTensor.induction_on with
      | zero => simp only [map_zero, add_zero]
      | tmul n a =>
        simp only [ExtTensor.lift_tmul, LinearMap.mk₂_apply, Submodule.coe_add, add_mul,
          map_add, add_smul]
      | add z z' hz hz' => simp only [map_add, hz, hz']; abel)
    (fun c r z => by
      beta_reduce
      induction z using ExtTensor.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul n a =>
        simp only [ExtTensor.lift_tmul, LinearMap.mk₂_apply, Submodule.coe_smul_of_tower,
          smul_mul_assoc, map_smul, smul_assoc]
      | add z z' hz hz' => simp only [map_add, hz, hz', smul_add])
    (fun _ z z' => map_add _ z z')
    (fun c _ z => map_smul _ c z)

theorem unitRBil_tmul (r : IndBimod Q ν 0) (n : N) (a : KLRAlgebra k Q 0) :
    unitRBil Q ν N r (ExtTensor.tmul n a) =
      castKLR Q (add_zero ν) ((r : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a)) • n := rfl

theorem unitRBil_balanced (r : IndBimod Q ν 0) (t : TensorKLR Q ν 0)
    (z : ExtTensor k N (KLRAlgebra k Q 0)) :
    unitRBil Q ν N (op t • r) z = unitRBil Q ν N r (t • z) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [op_zero, zero_smul, map_zero, LinearMap.zero_apply]
  | tmul b a' =>
    induction z using ExtTensor.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul n a =>
      rw [ExtTensor.smul_tmul, unitRBil_tmul, unitRBil_tmul, coe_op_smul, unop_op, smul_eq_mul]
      have : concat Q ν 0 (b ⊗ₜ a') * concat Q ν 0 (1 ⊗ₜ a) =
          concat Q ν 0 (1 ⊗ₜ (a' * a)) * concat Q ν 0 (b ⊗ₜ 1) := by
        rw [← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one]
      rw [mul_assoc, this, ← mul_assoc, map_mul, concat_tmul_one_eq_castAlg_symm,
        castKLR_castAlg_symm, mul_smul]
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
  | add t t' ht ht' => simp only [op_add, add_smul, map_add, LinearMap.add_apply, ht, ht']

variable (Q ν) in
/-- The map `Ind_{ν,0} (N ⊠ R(0)) → N`. -/
def unitRFwd : UnitR Q ν N →ₗ[k] N :=
  BalancedTensor.lift (unitRBil Q ν N) (fun r t z => unitRBil_balanced N r t z)

theorem unitRFwd_tmul (r : IndBimod Q ν 0) (n : N) (a : KLRAlgebra k Q 0) :
    unitRFwd Q ν N (BalancedTensor.tmul r (ExtTensor.tmul n a)) =
      castKLR Q (add_zero ν) ((r : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a)) • n := by
  rw [unitRFwd, BalancedTensor.lift_tmul, unitRBil_tmul]

variable (Q ν) in
/-- The map `N → Ind_{ν,0} (N ⊠ R(0))`, `n ↦ 1_{ν,0} ⊗ (n ⊗ 1)`. -/
def unitRBwd : N →ₗ[k] UnitR Q ν N where
  toFun n := BalancedTensor.tmul (oneBimod Q ν 0) (ExtTensor.tmul n 1)
  map_add' n n' := by simp only [ExtTensor.add_tmul, BalancedTensor.tmul_add]
  map_smul' c n := by simp only [← ExtTensor.smul_tmul', BalancedTensor.tmul_smul,
    RingHom.id_apply]

theorem unitRBwd_smul (b : KLRAlgebra k Q ν) (n : N) :
    unitRBwd Q ν N (b • n) = castKLR Q (add_zero ν).symm b • unitRBwd Q ν N n := by
  show BalancedTensor.tmul (oneBimod Q ν 0) (ExtTensor.tmul (b • n) 1) =
    castKLR Q (add_zero ν).symm b • BalancedTensor.tmul (oneBimod Q ν 0) (ExtTensor.tmul n 1)
  rw [← concat_tmul_one_eq_castAlg_symm, concat_smul_tmul_oneBimod, ExtTensor.smul_tmul,
    one_smul]

theorem unitRFwd_smul (b : KLRAlgebra k Q (ν + 0)) (x : UnitR Q ν N) :
    unitRFwd Q ν N (b • x) = castKLR Q (add_zero ν) b • unitRFwd Q ν N x := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul r z =>
    rw [BalancedTensor.smul_tmul']
    induction z using ExtTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero, smul_zero]
    | tmul n a =>
      rw [unitRFwd_tmul, unitRFwd_tmul, Submodule.coe_smul, smul_eq_mul, mul_assoc, map_mul,
        mul_smul]
    | add z z' hz hz' => simp only [BalancedTensor.tmul_add, map_add, hz, hz', smul_add]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem unitRFwd_unitRBwd (n : N) : unitRFwd Q ν N (unitRBwd Q ν N n) = n := by
  show unitRFwd Q ν N (BalancedTensor.tmul (oneBimod Q ν 0) (ExtTensor.tmul n 1)) = n
  rw [unitRFwd_tmul, coe_oneBimod, concat_one_tmul_one, (oneConcat_idem (ν := ν) (ν' := 0)).eq,
    castKLR_oneConcat_zero_right, one_smul]

theorem unitRBwd_unitRFwd (x : UnitR Q ν N) : unitRBwd Q ν N (unitRFwd Q ν N x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r z =>
    induction z using ExtTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | tmul n a =>
      rw [unitRFwd_tmul, unitRBwd_smul, castKLR_symm_castAlg]
      show BalancedTensor.tmul (((r : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a)) •
        oneBimod Q ν 0) (ExtTensor.tmul n 1) = _
      rw [show ((r : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a)) • oneBimod Q ν 0 =
          op ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] a) • r from Subtype.ext (by
            show (r : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a) * oneConcat Q ν 0 = _
            rw [mul_assoc, concat_mul_oneConcat]; rfl),
        BalancedTensor.op_smul_tmul, ExtTensor.smul_tmul, smul_eq_mul, mul_one, one_smul]
    | add z z' hz hz' => simp only [BalancedTensor.tmul_add, map_add, hz, hz']
  | add x y hx hy => simp only [map_add, hx, hy]

variable (Q ν) in
/-- **Right unitality of induction**: `Ind_{ν,0} (N ⊠ R(0)) ≅ N`, semilinear along
`castKLR : R(ν + 0) ≃ R(ν)` (`unitREquiv_smul`). -/
def unitREquiv : UnitR Q ν N ≃ₗ[k] N :=
  LinearEquiv.ofLinear (unitRFwd Q ν N) (unitRBwd Q ν N)
    (LinearMap.ext fun n => unitRFwd_unitRBwd N n)
    (LinearMap.ext fun x => unitRBwd_unitRFwd N x)

theorem unitREquiv_smul (b : KLRAlgebra k Q (ν + 0)) (x : UnitR Q ν N) :
    unitREquiv Q ν N (b • x) = castKLR Q (add_zero ν) b • unitREquiv Q ν N x :=
  unitRFwd_smul N b x

end Unit

end KLRAlgebra

end Categorification.KLR

end
