/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingProduct
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.Induction.Restriction
import Categorification.Algebra.BalancedTensorExact

/-!
# The map out of the partial standard kernel

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, (6.21) and the paragraph following it.
In the source order `κ` put `T = eκ V eκ`, where `V` is the quotient by globally
violated diagrams. The projective is `P = e(t) T`. Its submodule `K` consists of the
products through strictly higher loadings of order `κ` for the *retained* block cuts.
The inclusion induces `K ⊗_T B → P ⊗_T B`, without any flatness hypothesis on `B`.
Multiplication detects zero on the projective tensor, not a priori on the kernel tensor.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "p" => fun s : KLR.Seq μ => mk (ofKLR k Q Λ ν (KLRAlgebra.e s))
local notation "E" => fun κ => mk (redProj k Q Λ ν κ)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν

variable (t : KLR.Seq (stendhalWeight ℓ ν))

/-- The loading idempotent inside the unital ordered algebra. -/
def orderedLoadingIdem : (ord (redWord t)).Corner :=
  ⟨p t, (Subsemigroup.mem_corner_iff (ord (redWord t))).2 ⟨by rw [← map_mul, redProj_mul_e, ite_eq_left rfl],
    by rw [← map_mul, e_mul_redProj, ite_eq_left rfl]⟩⟩

local notation "eₜ" => orderedLoadingIdem Q Λ t
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "P" => rIdeal eₜ

theorem orderedLoadingIdem_idem : IsIdempotentElem eₜ :=
  Subtype.ext (((show IsIdempotentElem (KLRAlgebra.e t : KLRAlgebra k (stendhalQ Q Λ) μ) from
    KLRAlgebra.e_mul_self _).map (ofKLR k Q Λ ν)).map mk).eq

/-- The middle term `Q` in (6.21) is a projective over the full ordered algebra. -/
theorem blockLoading_projective : Module.Projective Tᵐᵒᵖ P :=
  rIdeal_projective (orderedLoadingIdem_idem Q Λ t)

variable (a b : Fin ℓ)
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)

/-- `e(t) T` intersected with the ideal of strictly higher retained boundaries of this
red order. Membership is tested before any braiding tensor is taken. -/
def blockLoadingKernel : Submodule Tᵐᵒᵖ P where
  carrier := {x | x.1.1 ∈ J}
  zero_mem' := (J).zero_mem
  add_mem' {x y} hx hy := (J).add_mem (x := x.1.1) (y := y.1.1) hx hy
  smul_mem' r x hx := by
    change x.1.1 * r.unop.1 ∈ J
    exact TwoSidedIdeal.mul_mem_right _ _ _ hx

local notation "K" => blockLoadingKernel Q Λ t a b

instance blockKernelAddGroup : AddCommGroup K :=
  @Submodule.addCommGroup Tᵐᵒᵖ P _ (Submodule.addCommGroup (rIdeal eₜ)) (Submodule.module (rIdeal eₜ)) (K)
instance blockKernelSmulComm : SMulCommClass k Tᵐᵒᵖ K where
  smul_comm c r x := Subtype.ext (Subtype.ext (Subtype.ext (smul_mul_assoc c x.1.1.1 r.unop.1).symm))

/-- Cut both ends in the source order, projecting onto the loading on top. -/
def blockLoadingRep (x : V) : P :=
  rIdealProj (orderedLoadingIdem_idem Q Λ t) ⟨E (redWord t) * x * E (redWord t), x, rfl⟩

theorem blockLoadingRep_val (x : V) : (blockLoadingRep Q Λ t x).1.1 = p t * x * E (redWord t) := by
  change p t * (E (redWord t) * x * E (redWord t)) = _
  rw [← mul_assoc, ← mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left rfl]

theorem blockLoadingRep_self (x : P) : blockLoadingRep Q Λ t x.1.1 = x := by
  apply Subtype.ext; apply Subtype.ext
  rw [blockLoadingRep_val, show p t * x.1.1 = x.1.1 from congrArg Subtype.val x.2]
  exact CornerEndomorphism.corner_mul_right _ x.1

variable (κ' : List (Fin ℓ))
local notation "B" => RedBlock.crossingSpace (k := k) (E (redWord t)) (E κ')

/-- Use the left action of Definition 6.6 on the crossing space with its ground scalars. -/
instance blockBraidingLeftModule {R : Type*} [Ring R] [Algebra k R] {u v : R} (hu : IsIdempotentElem u) :
    Module hu.Corner (RedBlock.crossingSpace (k := k) u v) := cornerBimodule.instModuleLeft hu

/-- The two ordinary balanced tensors in the degree-one homology test of (6.21) (degree
`−1` for cochains), and the map between them: functoriality on the actual inclusion. -/
def blockKernelTensorInclusion : BalancedTensor k k T K B →ₗ[k] BalancedTensor k k T P B :=
  BalancedTensor.mapLeftBimodule k B ((K).subtype.restrictScalars k) (fun _ _ => rfl)

local notation "inc" => blockKernelTensorInclusion Q Λ t a b κ'

@[simp] theorem blockKernelTensorInclusion_tmul (x : K) (y : B) :
    inc (BalancedTensor.tmul x y) = BalancedTensor.tmul x.1 y := rfl

/-- Evaluate the projective tensor by multiplication of diagrams, without imposing any
higher-boundary relation on the output. -/
def blockLoadingTensorStack : BalancedTensor k k T P B →ₗ[k] V :=
  BalancedTensor.lift ((LinearMap.compl₂ (LinearMap.mul k V) (B).subtype).comp
    ((IsIdempotentElem.cornerVal (R := k) (ord (redWord t))).comp ((P).subtype.restrictScalars k)))
    (fun x r y => mul_assoc x.1.1 r.1 y.1)

local notation "stack" => blockLoadingTensorStack Q Λ t κ'

@[simp] theorem blockLoadingTensorStack_tmul (x : P) (y : B) :
    stack (BalancedTensor.tmul x y) = x.1.1 * y.1 := rfl

/-- Only the *projective* tensor has the evident inverse cut `z ↦ e(t) ⊗ z` on its image. -/
theorem blockLoadingTensorStack_injective : Function.Injective stack := by
  let gen : P := ⟨eₜ, (orderedLoadingIdem_idem Q Λ t).eq⟩
  let cut : V →ₗ[k] B := ((LinearMap.mulRight k (E κ')).comp (LinearMap.mulLeft k (E (redWord t)))).codRestrict B
    fun z => ⟨by change E (redWord t) * (E (redWord t)*z*E κ') = _
                 rw [← mul_assoc, ← mul_assoc, (ord (redWord t)).eq]; rfl,
              by change E (redWord t)*z*E κ'*E κ' = _; rw [mul_assoc _ (E κ'), (ord κ').eq]; rfl⟩
  let read := ((BalancedTensor.mkBil k k T P B) gen).comp cut
  have inv : read.comp stack = LinearMap.id := by
    apply BalancedTensor.ext; intro x y
    change BalancedTensor.tmul gen (cut (x.1.1 * y.1)) = BalancedTensor.tmul x y
    have hc : cut (x.1.1 * y.1) = x.1 • y := Subtype.ext (by
      change E (redWord t) * (x.1.1 * y.1) * E κ' = x.1.1 * y.1
      rw [← mul_assoc, CornerEndomorphism.corner_mul_left _ x.1, mul_assoc, y.2.2])
    rw [hc, ← BalancedTensor.op_smul_tmul]
    exact congrArg (fun m : P => BalancedTensor.tmul m y) (Subtype.ext x.2)
  exact fun _ _ h => by simpa only [← LinearMap.comp_apply, inv, LinearMap.id_apply] using congrArg read h

/-- Testing a class from `K ⊗_T B` in the projective tensor is exactly testing its
unquotiented-by-higher stack in `V`. This is not yet injectivity on the kernel tensor. -/
theorem blockKernelTensorInclusion_eq_zero_iff (z) : inc z = 0 ↔ stack (inc z) = 0 :=
  ⟨fun h => h ▸ map_zero _, fun h => blockLoadingTensorStack_injective Q Λ t κ' (h.trans (map_zero _).symm)⟩

private theorem kernel_zero_of_violated (h : IsViolated t) (x : K) : x=0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hx := congrArg (fun y : T => y.1) x.1.2
  change p t * x.1.1.1 = x.1.1.1 at hx
  exact hx.symm.trans ((congrArg (fun y : V => y*x.1.1.1) (violMk_e h)).trans (zero_mul _))

private theorem tensor_zero_of_zero_kernel (h : ∀ x : K, x = 0)
    (z : BalancedTensor k k T K B) : z=0 := by
  induction z using BalancedTensor.induction_on with
  | zero => rfl
  | tmul x y =>
    have hx := h x
    exact (congrArg (fun x : K => (BalancedTensor.tmul x y : BalancedTensor k k T K B)) hx).trans
      (BalancedTensor.zero_tmul y)
  | add x y hx hy =>
    exact (congrArg₂ (fun x y : BalancedTensor k k T K B => x+y) hx hy).trans (zero_add 0)

/-- A violated top loading has zero source kernel tensor. -/
theorem blockKernelTensorInclusion_injective_of_violated_top (h : IsViolated t) :
    Function.Injective inc := by
  intro x y _
  exact (tensor_zero_of_zero_kernel Q Λ t a b κ' (kernel_zero_of_violated Q Λ t a b h) x).trans (tensor_zero_of_zero_kernel Q Λ t a b κ' (kernel_zero_of_violated Q Λ t a b h) y).symm



/-- An actual bottom higher kernel gives zero source tensor for every target order. -/
theorem blockKernelTensorInclusion_injective_of_bot (h : K = ⊥) :
    Function.Injective inc := by
  have zero (x : K) : x = 0 := by
    apply Subtype.ext
    have hx : x.1 ∈ (⊥ : Submodule Tᵐᵒᵖ P) := (le_of_eq h) x.2
    simpa only [Submodule.mem_bot, Submodule.coe_zero] using hx
  intro x y _
  exact (tensor_zero_of_zero_kernel Q Λ t a b κ' zero x).trans
    (tensor_zero_of_zero_kernel Q Λ t a b κ' zero y).symm

end Categorification.Stendhal.BraidedStendhalAlgebra
