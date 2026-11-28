/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockRightProjective

/-!
# Induction is coinduction, on modules

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the module form of the identity (IC), at
`ℓ = 0`. Let `A = T̃^{λ⁺}`, `D = T̃^λ ⊗ T̃^{(μ,μ*)}`, `D_R = T̃^{(μ,μ*)} ⊗ T̃^λ` and `c : A → D`
the trace (`blockTrace`). The corner `e_L A` (`endCorner`) is a left `D`-module through `ι`
(`endLeftAct`), and `A e_R` (`frontRightCorner`) a right `D_R`-module through `ι_R`. For a right
`D`-module `X`, regarded as a right `D_R`-module through the exchange of the factors, write

* `Ind X = X ⊗_D e_L A` (`BalancedTensor`), and
* `CoInd X = Hom_{D_R}(A e_R, X)` (`coInd`: the `k`-linear `f` with `f(y ι_R(d')) =
  f(y) swap(d')`).

Then `x ⊗ z ↦ (y ↦ x c(z y))` is a `k`-linear isomorphism `Ind X ≅ CoInd X`
(`indCoindEquiv`, with the formula `indCoindEquiv_tmul_apply`). The formula shows that it
commutes with the right `A`-actions (`(x ⊗ z a)` and `y ↦ f(a y)`) and is natural in `X`.

Proof. The map is well defined since `c(ι(d) z y) = d c(z y)` and lands in `CoInd X` since
`c(z y ι_R(d')) = c(z y) swap(d')`. By (IC) (`exists_blockTrace_mul_eq`) there are `z_{c'} ∈ e_L A`,
one for each front generator `c'`, with `c(z_{c'} y) = swap(κ(y)_{c'})` for `y ∈ A e_R`, where `κ`
are the (B3-R) coordinates (`frontRightCoord`). The inverse is
`f ↦ ∑_{c'} f(flip(γ_{c'})) ⊗ z_{c'}`: one composite is the identity because
`y = ∑_{c'} flip(γ_{c'}) ι_R(κ(y)_{c'})`, the other because
`∑_{c'} ι(c(z flip(γ_{c'}))) z_{c'} = z`, which follows from the injectivity half of (IC)
(`eq_zero_of_blockTrace_mul_flip_genEltF`).

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, `ℓ = 0`.

## Main definitions

* `CupCap.endLeftAct` (and the module instance), `CupCap.coInd`, `CupCap.indCoind`,
  `CupCap.dualElt`.

## Main results

* `CupCap.indCoindEquiv`: `X ⊗_D e_L A ≃ Hom_{D_R}(A e_R, X)`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 0 → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 le_rfl) (ν + ν₀)

omit [DecidableEq I] in
/-- The exchange of the factors is multiplicative. -/
private theorem comm_mul' {B C : Type*} [Ring B] [Algebra k B] [Ring C] [Algebra k C]
    (x y : B ⊗[k] C) :
    TensorProduct.comm k B C (x * y) = TensorProduct.comm k B C x * TensorProduct.comm k B C y :=
  map_mul (Algebra.TensorProduct.comm k B C) x y

/-! ### The left `D`-module `e_L A` -/

variable (Q Λ Λc ν ν₀) in
/-- The left action of `D` on `e_L A`, `d · z = ι(d) z`. -/
def endLeftAct : (T ⊗[k] Tc) →+* Module.End k (endCorner Q Λ Λc ν ν₀) where
  toFun d :=
    { toFun := fun z => ⟨blockTensor Q Λ Λc ν ν₀ d * z.1, by
        change endStendhal Q Λ Λc ν ν₀ 1 * _ = _
        rw [← mul_assoc, endStendhal_one_mul_blockTensor]⟩
      map_add' := fun z z' => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r z => Subtype.ext (mul_smul_comm _ _ _) }
  map_one' := LinearMap.ext fun z => Subtype.ext (by
    change blockTensor Q Λ Λc ν ν₀ 1 * z.1 = z.1
    rw [blockTensor_one]
    exact z.2)
  map_mul' a b := LinearMap.ext fun z => Subtype.ext (by
    change blockTensor Q Λ Λc ν ν₀ (a * b) * z.1 =
      blockTensor Q Λ Λc ν ν₀ a * (blockTensor Q Λ Λc ν ν₀ b * z.1)
    rw [blockTensor_mul, mul_assoc])
  map_zero' := LinearMap.ext fun z => Subtype.ext (by
    change blockTensor Q Λ Λc ν ν₀ 0 * z.1 = 0
    rw [map_zero, zero_mul])
  map_add' a b := LinearMap.ext fun z => Subtype.ext (by
    change blockTensor Q Λ Λc ν ν₀ (a + b) * z.1 =
      blockTensor Q Λ Λc ν ν₀ a * z.1 + blockTensor Q Λ Λc ν ν₀ b * z.1
    rw [map_add, add_mul])

/-- `e_L A` as a left `D`-module. -/
instance : Module (T ⊗[k] Tc) (endCorner Q Λ Λc ν ν₀) :=
  Module.compHom _ (endLeftAct Q Λ Λc ν ν₀)

theorem smul_endCorner_coe (d : T ⊗[k] Tc) (z : endCorner Q Λ Λc ν ν₀) :
    ((d • z : endCorner Q Λ Λc ν ν₀) : Tp) = blockTensor Q Λ Λc ν ν₀ d * z.1 :=
  rfl

/-! ### The coinduced module -/

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (StendhalAlgebra k Q Λ ν ⊗[k] StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ X]
  [IsScalarTower k (StendhalAlgebra k Q Λ ν ⊗[k] StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ X]
  [SMulCommClass k (StendhalAlgebra k Q Λ ν ⊗[k] StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ X]

variable (Q Λ Λc ν ν₀) in
/-- `CoInd X = Hom_{D_R}(A e_R, X)`: the `k`-linear `f : A e_R → X` with
`f(y ι_R(d')) = f(y) swap(d')`. -/
def coInd : Submodule k (frontRightCorner Q Λ Λc ν ν₀ →ₗ[k] X) where
  carrier := {f | ∀ (d' : Tc ⊗[k] T) y, f (op d' • y) = op (TensorProduct.comm k Tc T d') • f y}
  add_mem' {f g} hf hg d' y := by
    rw [LinearMap.add_apply, LinearMap.add_apply, hf, hg, smul_add]
  zero_mem' d' y := by rw [LinearMap.zero_apply, LinearMap.zero_apply, smul_zero]
  smul_mem' r f hf d' y := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hf, smul_comm]

variable {X}

omit [IsScalarTower k (StendhalAlgebra k Q Λ ν ⊗[k] StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ X] in
theorem mem_coInd {f : frontRightCorner Q Λ Λc ν ν₀ →ₗ[k] X} :
    f ∈ coInd Q Λ Λc ν ν₀ X ↔
      ∀ (d' : Tc ⊗[k] T) y, f (op d' • y) = op (TensorProduct.comm k Tc T d') • f y :=
  Iff.rfl

variable (Q Λ Λc ν ν₀) in
/-- The projection `y ↦ y e_R` onto `A e_R`. -/
def frontRightProj : Tp →ₗ[k] frontRightCorner Q Λ Λc ν ν₀ where
  toFun y := ⟨y * blockTensorR Q Λ Λc ν ν₀ 1, mul_blockTensorR_mem_frontRightCorner _ _⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

theorem frontRightProj_coe (y : frontRightCorner Q Λ Λc ν ν₀) :
    frontRightProj Q Λ Λc ν ν₀ y.1 = y :=
  Subtype.ext (by
    change y.1 * blockTensorR Q Λ Λc ν ν₀ 1 = y.1
    rw [blockTensorR_one]
    exact y.2)

theorem frontRightProj_mul_blockTensorR (y : Tp) (d' : Tc ⊗[k] T) :
    frontRightProj Q Λ Λc ν ν₀ (y * blockTensorR Q Λ Λc ν ν₀ d') =
      op d' • frontRightProj Q Λ Λc ν ν₀ y :=
  Subtype.ext (by
    change y * blockTensorR Q Λ Λc ν ν₀ d' * blockTensorR Q Λ Λc ν ν₀ 1 =
      y * blockTensorR Q Λ Λc ν ν₀ 1 * blockTensorR Q Λ Λc ν ν₀ d'
    rw [mul_assoc, mul_assoc, ← blockTensorR_mul, ← blockTensorR_mul, mul_one, one_mul])

/-! ### The map `Ind X → CoInd X` -/

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight 0 ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}
  [DecidableEq (EndGen ν₀ ρ₁)]
  (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)

local notation "𝐜" => blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃

variable (Q Λ Λc ρ₁ ρ₃) in
/-- `y ↦ x c(z y)` on `A e_R`. -/
def traceAct (z : Tp) (x : X) : frontRightCorner Q Λ Λc ν ν₀ →ₗ[k] X where
  toFun y := op (𝐜 (z * y.1)) • x
  map_add' y y' := by rw [Submodule.coe_add, mul_add, map_add, op_add, add_smul]
  map_smul' r y := by
    rw [Submodule.coe_smul, mul_smul_comm, map_smul, op_smul, smul_assoc, RingHom.id_apply]

omit [SMulCommClass k (StendhalAlgebra k Q Λ ν ⊗[k] StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ X] in
theorem traceAct_apply (z : Tp) (x : X) (y : frontRightCorner Q Λ Λc ν ν₀) :
    traceAct Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z x y = op (𝐜 (z * y.1)) • x :=
  rfl

variable (Q Λ Λc ρ₁ ρ₃) in
/-- The bilinear map `(x, z) ↦ (y ↦ x c(z y))`. -/
def indCoindBil :
    X →ₗ[k] endCorner Q Λ Λc ν ν₀ →ₗ[k] (frontRightCorner Q Λ Λc ν ν₀ →ₗ[k] X) :=
  LinearMap.mk₂ k (fun x z => traceAct Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z.1 x)
    (fun x x' z => LinearMap.ext fun y => smul_add _ _ _)
    (fun r x z => LinearMap.ext fun y => smul_comm _ _ _)
    (fun x z z' => LinearMap.ext fun y => by
      change op (𝐜 ((z.1 + z'.1) * y.1)) • x = op (𝐜 (z.1 * y.1)) • x + op (𝐜 (z'.1 * y.1)) • x
      rw [add_mul, map_add, op_add, add_smul])
    (fun r x z => LinearMap.ext fun y => by
      change op (𝐜 ((r • z.1) * y.1)) • x = r • (op (𝐜 (z.1 * y.1)) • x)
      rw [smul_mul_assoc, map_smul, op_smul, smul_assoc])

omit [SMulCommClass k (StendhalAlgebra k Q Λ ν ⊗[k] StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ X] in
theorem indCoindBil_balanced (x : X) (d : T ⊗[k] Tc) (z : endCorner Q Λ Λc ν ν₀) :
    indCoindBil Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (op d • x) z =
      indCoindBil Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ x (d • z) :=
  LinearMap.ext fun y => by
    change op (𝐜 (z.1 * y.1)) • (op d • x) =
      op (𝐜 ((blockTensor Q Λ Λc ν ν₀ d * z.1) * y.1)) • x
    rw [mul_assoc, blockTrace_blockTensor_mul, op_mul, mul_smul]

variable (Q Λ Λc ρ₁ ρ₃) in
/-- The map `X ⊗_D e_L A → Hom_k(A e_R, X)`, `x ⊗ z ↦ (y ↦ x c(z y))`. -/
def indCoindMap :
    BalancedTensor k k (T ⊗[k] Tc) X (endCorner Q Λ Λc ν ν₀) →ₗ[k]
      (frontRightCorner Q Λ Λc ν ν₀ →ₗ[k] X) :=
  BalancedTensor.lift (indCoindBil Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃)
    (indCoindBil_balanced hQ hρ₁ hρ₂ hρ₃)

theorem indCoindMap_tmul_apply (x : X) (z : endCorner Q Λ Λc ν ν₀)
    (y : frontRightCorner Q Λ Λc ν ν₀) :
    indCoindMap Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (BalancedTensor.tmul x z) y =
      op (𝐜 (z.1 * y.1)) • x :=
  rfl

theorem indCoindMap_mem
    (t : BalancedTensor k k (T ⊗[k] Tc) X (endCorner Q Λ Λc ν ν₀)) :
    indCoindMap Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ t ∈ coInd Q Λ Λc ν ν₀ X := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul x z =>
    intro d' y
    rw [indCoindMap_tmul_apply, indCoindMap_tmul_apply, op_smul_frontRightCorner, ← mul_assoc,
      blockTrace_mul_blockTensorR, op_mul, mul_smul]
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

variable (Q Λ Λc ρ₁ ρ₃ X) in
/-- **The map `Ind X → CoInd X`**, `x ⊗ z ↦ (y ↦ x c(z y))`. -/
def indCoind :
    BalancedTensor k k (T ⊗[k] Tc) X (endCorner Q Λ Λc ν ν₀) →ₗ[k] coInd Q Λ Λc ν ν₀ X :=
  (indCoindMap Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).codRestrict _ (indCoindMap_mem hQ hρ₁ hρ₂ hρ₃)

/-! ### The dual elements and the inverse -/

variable [DecidableEq (FrontGen 0 ν ν₀)]

variable (Q Λ Λc ρ₃) in
/-- The functional `y ↦ swap(κ(y e_R)_{c'})` on `A`. -/
def frontCoordFun (c' : FrontGen 0 ν ν₀) : Tp →ₗ[k] T ⊗[k] Tc :=
  (TensorProduct.comm k Tc T).toLinearMap ∘ₗ (blockRightF Q Λ Λc c').subtype ∘ₗ
    DFinsupp.lapply c' ∘ₗ frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ ∘ₗ
      frontRightProj Q Λ Λc ν ν₀

omit [DecidableEq (EndGen ν₀ ρ₁)] in
theorem frontCoordFun_apply (c' : FrontGen 0 ν ν₀) (y : Tp) :
    frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c' y = TensorProduct.comm k Tc T
      (frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ (frontRightProj Q Λ Λc ν ν₀ y) c' :
        Tc ⊗[k] T) :=
  rfl

omit [DecidableEq (EndGen ν₀ ρ₁)] in
theorem frontCoordFun_mul_blockTensorR (c' : FrontGen 0 ν ν₀) (y : Tp) (d' : Tc ⊗[k] T) :
    frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c' (y * blockTensorR Q Λ Λc ν ν₀ d') =
      frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c' y * TensorProduct.comm k Tc T d' := by
  rw [frontCoordFun_apply, frontCoordFun_apply, frontRightProj_mul_blockTensorR,
    frontRightCoord_op_smul, ← comm_mul']
  rfl

variable (Q Λ Λc ρ₁ ρ₃) in
/-- **The dual element** `z_{c'} ∈ e_L A`, with `c(z_{c'} y) = swap(κ(y e_R)_{c'})` (by (IC)). -/
def dualElt (c' : FrontGen 0 ν ν₀) : endCorner Q Λ Λc ν ν₀ :=
  ⟨(exists_blockTrace_mul_eq hQ hρ₁ hρ₂ hρ₃ (frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c')
      (frontCoordFun_mul_blockTensorR hQ hρ₁ hρ₂ hρ₃ c')).choose,
    (exists_blockTrace_mul_eq hQ hρ₁ hρ₂ hρ₃ (frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c')
      (frontCoordFun_mul_blockTensorR hQ hρ₁ hρ₂ hρ₃ c')).choose_spec.1⟩

theorem blockTrace_dualElt_mul (c' : FrontGen 0 ν ν₀) (y : Tp) :
    𝐜 ((dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c').1 * y) =
      frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c' y :=
  (exists_blockTrace_mul_eq hQ hρ₁ hρ₂ hρ₃ (frontCoordFun Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ c')
    (frontCoordFun_mul_blockTensorR hQ hρ₁ hρ₂ hρ₃ c')).choose_spec.2 y

/-- `c(z_{c'} flip(γ_{c''}))` is `swap(1_{c'})` if `c' = c''` and `0` otherwise. -/
theorem blockTrace_dualElt_mul_gen (c' c'' : FrontGen 0 ν ν₀) :
    𝐜 ((dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c').1 * (frontRightGen Q Λ Λc ρ₃ c'').1) =
      if c'' = c' then TensorProduct.comm k Tc T (blockIdemF Q Λ Λc c') else 0 := by
  rw [blockTrace_dualElt_mul, frontCoordFun_apply, frontRightProj_coe, frontRightCoord_gen]
  by_cases h : c'' = c'
  · subst h
    rw [ite_eq_left rfl, DFinsupp.single_eq_same]
  · rw [ite_eq_right h, DFinsupp.single_eq_of_ne (Ne.symm h), Submodule.coe_zero, map_zero]

variable [Fintype (FrontGen 0 ν ν₀)]

omit [DecidableEq I] in
private theorem equivFunOnFinite_symm_apply'' {α M : Type*} [Zero M] [Finite α] (g : α → M)
    (a : α) : Finsupp.equivFunOnFinite.symm g a = g a :=
  congrFun (Finsupp.equivFunOnFinite.apply_symm_apply g) a

omit [DecidableEq (EndGen ν₀ ρ₁)] in
/-- `y = ∑_{c'} flip(γ_{c'}) ι_R(κ(y)_{c'})` in `A e_R`. -/
theorem sum_op_smul_frontRightGen (y : frontRightCorner Q Λ Λc ν ν₀) :
    ∑ c', op (frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y c' : Tc ⊗[k] T) •
      frontRightGen Q Λ Λc ρ₃ c' = y := by
  have h := LinearMap.congr_fun (frontRightComb_comp_coordFree hQ hρ₁ hρ₂ hρ₃) y
  rw [LinearMap.comp_apply, frontRightComb, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun _ => by simp), LinearMap.id_apply] at h
  conv_rhs => rw [← h]
  refine Finset.sum_congr rfl fun c' _ => ?_
  change _ = (Finsupp.equivFunOnFinite.symm fun c' =>
    op ((frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y c' : Tc ⊗[k] T))) c' • _
  rw [equivFunOnFinite_symm_apply'']

variable (Q Λ Λc ρ₁ ρ₃ X) in
/-- The inverse `CoInd X → Ind X`, `f ↦ ∑_{c'} f(flip(γ_{c'})) ⊗ z_{c'}`. -/
def coIndInd :
    coInd Q Λ Λc ν ν₀ X →ₗ[k] BalancedTensor k k (T ⊗[k] Tc) X (endCorner Q Λ Λc ν ν₀) where
  toFun f := ∑ c', BalancedTensor.tmul (f.1 (frontRightGen Q Λ Λc ρ₃ c'))
    (dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c')
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Submodule.coe_add, LinearMap.add_apply, BalancedTensor.add_tmul]
  map_smul' r f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Submodule.coe_smul, LinearMap.smul_apply, BalancedTensor.smul_tmul]

/-- `∑_{c'} ι(c(z flip(γ_{c'}))) z_{c'} = z` for `z ∈ e_L A`. -/
theorem sum_smul_dualElt (z : endCorner Q Λ Λc ν ν₀) :
    ∑ c', 𝐜 (z.1 * (frontRightGen Q Λ Λc ρ₃ c').1) • dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c' =
      z := by
  rw [← sub_eq_zero]
  apply Subtype.ext
  rw [Submodule.coe_sub, Submodule.coe_zero]
  have hmem := (∑ c', 𝐜 (z.1 * (frontRightGen Q Λ Λc ρ₃ c').1) •
    dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c' - z).2
  refine eq_zero_of_blockTrace_mul_flip_genEltF hQ hρ₁ hρ₂ hρ₃ ?_ fun c'' => ?_
  · rw [← Submodule.coe_sub]
    exact hmem
  · have hsum : (∑ c', 𝐜 (z.1 * (frontRightGen Q Λ Λc ρ₃ c').1) •
        dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c' : endCorner Q Λ Λc ν ν₀).1 =
        ∑ c', blockTensor Q Λ Λc ν ν₀ (𝐜 (z.1 * (frontRightGen Q Λ Λc ρ₃ c').1)) *
          (dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c').1 := by
      rw [Submodule.coe_sum]
      rfl
    have hg : StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c'') =
        (frontRightGen Q Λ Λc ρ₃ c'').1 := rfl
    have hsm : ∀ x y w : Tp, (x - y) * w = x * w - y * w := fun x y w => sub_mul x y w
    rw [hsum, hg, hsm, map_sub, Finset.sum_mul, map_sum]
    simp only [mul_assoc, blockTrace_blockTensor_mul, blockTrace_dualElt_mul_gen, mul_ite,
      mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ c''),
      ← blockTrace_mul_blockTensorR hQ hρ₁ hρ₂ hρ₃, mul_assoc, ← hg,
      flip_genEltF_mul_blockTensorR_blockIdemF, sub_self]

theorem indCoind_coIndInd (f : coInd Q Λ Λc ν ν₀ X) :
    indCoind Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (coIndInd Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ f) = f := by
  apply Subtype.ext
  refine LinearMap.ext fun y => ?_
  change indCoindMap Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (∑ c', BalancedTensor.tmul
    (f.1 (frontRightGen Q Λ Λc ρ₃ c')) (dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c')) y = f.1 y
  rw [map_sum, LinearMap.sum_apply]
  conv_rhs => rw [← sum_op_smul_frontRightGen hQ hρ₁ hρ₂ hρ₃ y, map_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [indCoindMap_tmul_apply, blockTrace_dualElt_mul, frontCoordFun_apply, frontRightProj_coe,
    f.2]

theorem coIndInd_comp_indCoind :
    (coIndInd Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).comp (indCoind Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃) =
      LinearMap.id :=
  BalancedTensor.ext fun x z => by
    change ∑ c', BalancedTensor.tmul
        (op (𝐜 (z.1 * (frontRightGen Q Λ Λc ρ₃ c').1)) • x)
        (dualElt Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ c') = BalancedTensor.tmul x z
    rw [Finset.sum_congr rfl fun c' _ => BalancedTensor.op_smul_tmul _ _ _,
      ← BalancedTensor.tmul_sum, sum_smul_dualElt]

variable (Q Λ Λc ρ₁ ρ₃ X) in
/-- **Induction is coinduction** (module form of (IC)): `x ⊗ z ↦ (y ↦ x c(z y))` is an
isomorphism `X ⊗_D e_L A ≃ Hom_{D_R}(A e_R, X)`. -/
def indCoindEquiv :
    BalancedTensor k k (T ⊗[k] Tc) X (endCorner Q Λ Λc ν ν₀) ≃ₗ[k] coInd Q Λ Λc ν ν₀ X :=
  LinearEquiv.ofLinearMap (indCoind Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃)
    (coIndInd Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃)
    (LinearMap.ext (indCoind_coIndInd hQ hρ₁ hρ₂ hρ₃)) (coIndInd_comp_indCoind hQ hρ₁ hρ₂ hρ₃)

theorem indCoindEquiv_tmul_apply (x : X) (z : endCorner Q Λ Λc ν ν₀)
    (y : frontRightCorner Q Λ Λc ν ν₀) :
    (indCoindEquiv Q Λ Λc X ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (BalancedTensor.tmul x z)).1 y =
      op (𝐜 (z.1 * y.1)) • x :=
  rfl

end Categorification.Stendhal.CupCap
