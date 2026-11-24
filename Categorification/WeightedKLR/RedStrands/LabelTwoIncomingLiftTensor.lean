/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingLiftCut
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixed
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection

/-!
# The balanced tensor readout on the label-two incoming preimage

The left-dot coefficient descends to the tensor of the reflected incoming
preimage with the actual middle dot-sum quotient.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
noncomputable section

section QuotientTensor

variable {𝕜 R M X : Type*} [CommRing 𝕜] [Ring R] [Algebra 𝕜 R]
  [AddCommGroup M] [Module 𝕜 M]
  [AddCommGroup X] [Module 𝕜 X] [Module R X] [IsScalarTower 𝕜 R X]

private def descendRightQuotient (W : Submodule R X) (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜)
    (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f) : M →ₗ[𝕜] (X ⧸ W) →ₗ[𝕜] 𝕜 :=
  (((W.restrictScalars 𝕜).liftQ f hf).comp
    (Submodule.Quotient.restrictScalarsEquiv 𝕜 W).symm.toLinearMap).flip

private theorem descendRightQuotient_mk (W : Submodule R X) (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜)
    (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f) (m : M) (x : X) :
    descendRightQuotient W f hf m (W.mkQ x) = f x m := rfl

variable [Module Rᵐᵒᵖ M] [SMulCommClass 𝕜 Rᵐᵒᵖ M]

private def descendBalancedRightQuotient (W : Submodule R X) (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜)
    (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f)
    (hb : ∀ (m : M) (a : R) (x : X), f x (MulOpposite.op a • m) = f (a • x) m) :
    BalancedTensor 𝕜 𝕜 R M (X ⧸ W) →ₗ[𝕜] 𝕜 :=
  BalancedTensor.lift (descendRightQuotient W f hf) (fun m a b => by
    obtain ⟨x,rfl⟩ := W.mkQ_surjective b
    rw [← W.mkQ.map_smul, descendRightQuotient_mk, descendRightQuotient_mk]
    exact hb m a x)

private theorem descendBalancedRightQuotient_tmul (W : Submodule R X)
    (f : X →ₗ[𝕜] M →ₗ[𝕜] 𝕜) (hf : W.restrictScalars 𝕜 ≤ LinearMap.ker f)
    (hb : ∀ (m : M) (a : R) (x : X), f x (MulOpposite.op a • m) = f (a • x) m)
    (m : M) (x : X) :
    descendBalancedRightQuotient W f hf hb (BalancedTensor.tmul m (W.mkQ x)) = f x m :=
  (BalancedTensor.lift_tmul (descendRightQuotient W f hf) _ m (W.mkQ x)).trans
    (descendRightQuotient_mk W f hf m x)

end QuotientTensor

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 ν
local notation "T" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "B" => StandardDotSumQuotient k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "q" => Submodule.mkQ (LinearMap.range (diagramPlus k))
local notation "E" => seqIdem (parameter k) weights loading loading_ordered

local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "fElt" => leftMiddleDot k + rightMiddleDot k

open MulOpposite Categorification

local notation "J" => incomingLiftSubmodule k

private abbrev reflection : T →ₐ[k] Tᵐᵒᵖ := tensorReflect

private def reflectedAction : Tᵐᵒᵖ →+* T :=
  (RingEquiv.opOp T).symm.toRingHom.comp (reflection k).toRingHom.op

/-- The incoming preimage viewed as a right module by horizontal reflection. -/
def IncomingLiftCoefficient : Type := J

local notation "N" => IncomingLiftCoefficient k

instance : AddCommGroup N := inferInstanceAs (AddCommGroup J)
instance : Module k N := inferInstanceAs (Module k J)
instance : Module Tᵐᵒᵖ N := Module.compHom J (reflectedAction k)

/-- The right action on the incoming preimage is the reflected left action. -/
theorem incomingLiftCoefficient_op_smul (a : T) (z : N) :
    (op a • z : N) = ((reflection k a).unop • (show J from z) : J) := rfl

instance : IsScalarTower k Tᵐᵒᵖ N where
  smul_assoc c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    change (op (c • b) • z : N) = c • (op b • z)
    rw [incomingLiftCoefficient_op_smul, incomingLiftCoefficient_op_smul]
    change (reflection k (c • b)).unop • (show J from z) =
      c • ((reflection k b).unop • (show J from z))
    rw [map_smul, unop_smul, smul_assoc]

instance : SMulCommClass k Tᵐᵒᵖ N where
  smul_comm c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    rw [incomingLiftCoefficient_op_smul, incomingLiftCoefficient_op_smul]
    exact smul_comm c (reflection k b).unop (show J from z)

private theorem coefficient_kills_higher (s : Seq μ) (hs : IsRedOrdered s)
    (hlt : StendhalLT loading s) (z : N) : op (seqIdem (parameter k) weights s hs) • z = 0 := by
  rw [incomingLiftCoefficient_op_smul, unop_tensorReflect_e]
  apply Subtype.ext
  exact seqIdem_smul_leftStandard_eq_zero (parameter k) weights loading_ordered hs hlt
    (show J from z).val

local notation "𝓦" => fixSub k N (op E)
local notation "BT" => BalancedTensor k k T N S

private def tensorFixed : BT ≃ₗ[k] 𝓦 :=
  leftStandardTensorEquivFixed (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k)

private def liftTensorPreReadout : BT →ₗ[k] k :=
  ((middleY₁Readout k).comp (((J).subtype).restrictScalars k)).comp
    ((𝓦).subtype.comp (tensorFixed k).toLinearMap)

private theorem liftTensorPreReadout_generator (z : N) :
    liftTensorPreReadout k (BalancedTensor.tmul z g) =
      middleY₁Readout k (show J from z).val := by
  have h := leftStandardTensorEquivFixed_tmul_generator (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k) z
  have h0 : (tensorFixed k (BalancedTensor.tmul z g)).val = op E • z := h
  rw [incomingLiftCoefficient_op_smul, unop_tensorReflect_e] at h0
  exact (congrArg (fun x : J => middleY₁Readout k x.val) h0).trans
    (middleY₁Readout_project_eq k (show J from z).val)

private theorem dotSum_reflection_fixed : (reflection k fElt).unop = fElt := by
  let π := stendhalTensorProjection (Q := parameter k) weights ν
  let H := KLRAlgebra k (stendhalQ (parameter k) weights) μ
  let z : H := x ⟨1, by decide⟩ + x ⟨3, by decide⟩
  have h : π z = fElt := π.map_add _ _
  have h' := congrArg unop
    (tensorReflect_projection (Q := parameter k) (Λ := weights) («ν» := ν) z)
  change (reflection k (π z)).unop = π (hflip z) at h'
  have hfix : hflip z = z := by
    unfold z
    rw [hflip_add, hflip_x, hflip_x]
  rw [hfix, h] at h'
  exact h'

private theorem liftTensorPreReadout_kills_plus (z : N) (s : S) :
    liftTensorPreReadout k (BalancedTensor.tmul z (diagramPlus k s)) = 0 := by
  obtain ⟨a,rfl⟩ := leftStandard_exists_smul_unit
    (Q := parameter k) (Λ := weights) loading loading_ordered s
  have hg : diagramPlus k g = fElt • g := by
    change dotEnd k 0 g + dotEnd k 1 g = fElt • g
    rw [dotEnd_zero_gen, dotEnd_one_gen, add_smul]
  rw [map_smul, ← BalancedTensor.op_smul_tmul, hg, ← BalancedTensor.op_smul_tmul,
    liftTensorPreReadout_generator]
  change middleY₁Readout k ((show J from op fElt • (op a • z)).val) = 0
  have he := incomingLiftCoefficient_op_smul k fElt (op a • z)
  rw [dotSum_reflection_fixed k] at he
  exact (congrArg (fun x : J => middleY₁Readout k x.val) he).trans
    (middleY₁Readout_middleDotElt_incomingLift_zero k (show J from op a • z))

private def liftTensorPreBil : S →ₗ[k] N →ₗ[k] k :=
  ((BalancedTensor.mkBil k k T N S).compr₂ (liftTensorPreReadout k)).flip

private theorem liftTensorPreBil_kills :
    (U).restrictScalars k ≤ LinearMap.ker (liftTensorPreBil k) := by
  rintro _ ⟨s,rfl⟩
  apply LinearMap.mem_ker.mpr
  ext m
  exact liftTensorPreReadout_kills_plus k m s

private theorem liftTensorPreBil_balanced (m : N) (a : T) (s : S) :
    liftTensorPreBil k s (op a • m) = liftTensorPreBil k (a • s) m :=
  congrArg (liftTensorPreReadout k) (BalancedTensor.op_smul_tmul m a s)

/-- The middle left-dot coefficient defines a balanced tensor readout
after imposing the dot-sum relation on the middle standard. -/
def incomingLiftTensorReadout : BalancedTensor k k T N B →ₗ[k] k :=
  descendBalancedRightQuotient U (liftTensorPreBil k) (liftTensorPreBil_kills k)
    (liftTensorPreBil_balanced k)

private theorem incomingLiftTensorReadout_mk (m : N) (s : S) :
    incomingLiftTensorReadout k (BalancedTensor.tmul m (q s)) =
      liftTensorPreReadout k (BalancedTensor.tmul m s) :=
  descendBalancedRightQuotient_tmul U _ _ _ m s

/-- The dot sum of the middle generator, viewed in the incoming preimage. -/
def incomingLiftDotSumGenerator : J :=
  ⟨diagramPlus k g, by
    change q (diagramPlus k g) ∈ LinearMap.range (normalizedIncoming k)
    have h : q (diagramPlus k g) = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr ⟨g,rfl⟩
    rw [h]
    exact Submodule.zero_mem _⟩

/-- The tensor of the incoming lift's dot-sum generator and the middle
quotient generator is detected by the left-dot coefficient. -/
theorem incomingLiftTensorReadout_dotSum_generator :
    incomingLiftTensorReadout k (BalancedTensor.tmul (show N from incomingLiftDotSumGenerator k) (q g)) = 1 := by
  rw [incomingLiftTensorReadout_mk, liftTensorPreReadout_generator]
  exact middleY₁Readout_diagramPlus_generator k

open Categorification.Webster.LabelTwo

private theorem plus_eq_smul_plus_and_square (z : Middle k) [NeZero (2 : k)] :
    ∃ a b : k, plus z = a • plus 1 + b • plus (plus 1) := by
  rcases z with ⟨⟨a,b⟩,⟨c,d⟩⟩
  have h₁ : plus (1 : Middle k) = ⟨⟨0,1⟩,⟨1,0⟩⟩ := by
    change plus (⟨⟨1,0⟩,⟨0,0⟩⟩ : Middle k) = _
    rw [plus_coordinates, zero_add]
  refine ⟨a,(c+b)/2,?_⟩
  rw [h₁, plus_coordinates, plus_coordinates]
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · change (0 : k) = a * 0 + (c+b)/2 * 0
    simp
  · change a = a * 1 + (c+b)/2 * 0
    simp
  · change a = a * 1 + (c+b)/2 * 0
    simp
  · change c+b = a * 0 + (c+b)/2 * (1+1)
    rw [mul_zero, zero_add, one_add_one_eq_two, div_mul_cancel₀ _ (NeZero.ne (2 : k))]

private theorem diagramPlus_generator_eq_smul :
    diagramPlus k g = fElt • g := by
  change dotEnd k 0 g + dotEnd k 1 g = _
  rw [dotEnd_zero_gen, dotEnd_one_gen, add_smul]

private theorem middleToFixed_plus_val (a : Middle k) :
    (middleToFixed k (plus a)).val = diagramPlus k (middleToFixed k a).val :=
  (congrArg Subtype.val (fixedPlus_transport k a)).symm

private theorem middle_fixed_dotSum_spans [NeZero (2 : k)] (z : fixSub k S E) :
    ∃ a b : k, diagramPlus k z.val = a • diagramPlus k g + b • (fElt • diagramPlus k g) := by
  let u := (middleToFixed k).symm z
  obtain ⟨a,b,h⟩ := plus_eq_smul_plus_and_square k u
  refine ⟨a,b,?_⟩
  have h₁ : (middleToFixed k (plus (1 : Middle k))).val = diagramPlus k g :=
    (middleToFixed_plus_val k 1).trans (congrArg (diagramPlus k) (middleToFixed_one_val k))
  have h₂ : (middleToFixed k (plus (plus (1 : Middle k)))).val = fElt • diagramPlus k g := calc
    _ = diagramPlus k (middleToFixed k (plus (1 : Middle k))).val := middleToFixed_plus_val k _
    _ = diagramPlus k (diagramPlus k g) := congrArg (diagramPlus k) h₁
    _ = diagramPlus k (fElt • g) := congrArg (diagramPlus k) (diagramPlus_generator_eq_smul k)
    _ = fElt • diagramPlus k g := (diagramPlus k).map_smul fElt g
  let f : Middle k →ₗ[k] S := (fixSub k S E).subtype.comp (middleToFixed k).toLinearMap
  have hu : (middleToFixed k u).val = z.val :=
    congrArg Subtype.val ((middleToFixed k).apply_symm_apply z)
  have h₀ : f (plus u) = diagramPlus k z.val :=
    (middleToFixed_plus_val k u).trans (congrArg (diagramPlus k) hu)
  calc
    _ = f (plus u) := h₀.symm
    _ = a • f (plus 1) + b • f (plus (plus 1)) := by rw [h, map_add, map_smul, map_smul]
    _ = _ := congrArg₂ (· + ·) (congrArg (a • ·) h₁) (congrArg (b • ·) h₂)

private theorem incoming_fixed_dotSum_spans [NeZero (2 : k)] (w : 𝓦) :
    ∃ a b : k, w.val = a • (show N from incomingLiftDotSumGenerator k) +
      b • (op fElt • (show N from incomingLiftDotSumGenerator k)) := by
  let u : J := w.val
  have hW : op E • w.val = w.val := w.property
  rw [incomingLiftCoefficient_op_smul, unop_tensorReflect_e] at hW
  have hu : E • u.val = u.val := congrArg Subtype.val hW
  obtain ⟨v,hv,h⟩ := (incomingLift_middle_fixed_iff k u.val hu).1 u.property
  obtain ⟨a,b,hab⟩ := middle_fixed_dotSum_spans k ⟨v,hv⟩
  refine ⟨a,b,?_⟩
  rw [incomingLiftCoefficient_op_smul, dotSum_reflection_fixed]
  exact Subtype.ext (h.symm.trans hab)

local notation "BTQ" => BalancedTensor k k T N B

private def dotSumTensor : BTQ :=
  BalancedTensor.tmul (show N from incomingLiftDotSumGenerator k) (q g)

private def tensorQuotientMap : BT →ₗ[k] BTQ := BalancedTensor.mapRight q

private theorem tensorQuotientMap_surjective : Function.Surjective (tensorQuotientMap k) :=
  BalancedTensor.mapRight_surjective (k := k) («B» := k) (M := N) (U).mkQ_surjective

private theorem opDotSum_tmul_quotGen :
    (BalancedTensor.tmul (op fElt • (show N from incomingLiftDotSumGenerator k)) (q g) : BTQ) = 0 := by
  let m : N := incomingLiftDotSumGenerator k
  have hq : q (diagramPlus k g) = 0 := (Submodule.Quotient.mk_eq_zero U).2 ⟨g,rfl⟩
  have h : fElt • q g = 0 :=
    ((q).map_smul fElt g).symm.trans ((congrArg q (diagramPlus_generator_eq_smul k).symm).trans hq)
  exact (BalancedTensor.op_smul_tmul m fElt (q g)).trans
    ((congrArg (fun v : B => (BalancedTensor.tmul m v : BTQ)) h).trans (BalancedTensor.tmul_zero m))

private theorem tensorQuotientMap_pure_fixed (v : BT) :
    tensorQuotientMap k v = BalancedTensor.tmul (tensorFixed k v).val (q g) := by
  have eqv := ((tensorFixed k).symm_apply_apply v).symm
  have hs := leftStandardTensorEquivFixed_symm_apply (parameter k) weights loading loading_ordered N
    (coefficient_kills_higher k) (tensorFixed k v)
  exact (congrArg (tensorQuotientMap k) (eqv.trans hs)).trans
    (BalancedTensor.mapRight_tmul q _ g)

private theorem image_spanning_of_surjection {K V W : Type*} [CommRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (z : W)
    (h : ∀ v, ∃ a : K, f v = a • z) (w : W) : ∃ a : K, w = a • z := by
  obtain ⟨v,rfl⟩ := hf w
  exact h v

private theorem readout_span_quotient {K V W : Type*} [CommRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (eval : V →ₗ[K] W) (x u v : V) (huv : ∃ a b : K, x = a • u + b • v)
    (hv : eval v = 0) : ∃ a : K, eval x = a • eval u := by
  obtain ⟨a,b,h⟩ := huv
  exact ⟨a, by rw [h, map_add, map_smul, map_smul, hv, smul_zero, add_zero]⟩

private theorem quotientTensor_dotSum_span [NeZero (2 : k)] (v : BT) :
    ∃ a : k, tensorQuotientMap k v = a • dotSumTensor k := by
  let eval : N →ₗ[k] BTQ := (BalancedTensor.mkBil k k T N B).flip (q g)
  let d : N := incomingLiftDotSumGenerator k
  have h := readout_span_quotient eval (tensorFixed k v).val d (op fElt • d)
    (incoming_fixed_dotSum_spans k (tensorFixed k v)) (opDotSum_tmul_quotGen k)
  exact h.imp fun a ha => (tensorQuotientMap_pure_fixed k v).trans ha

private theorem tensor_dotSum_spans [NeZero (2 : k)] (x : BTQ) :
    ∃ a : k, x = a • dotSumTensor k :=
  image_spanning_of_surjection (tensorQuotientMap k) (tensorQuotientMap_surjective k)
    (dotSumTensor k) (quotientTensor_dotSum_span k) x

private theorem bijective_of_line_readout {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] K) (z : V) (h : ∀ v, ∃ a : K, v = a • z) (hOne : f z = 1) :
    Function.Bijective f := by
  have hf (a : K) : f (a • z) = a := by rw [map_smul,hOne,smul_eq_mul,mul_one]
  constructor
  · apply (injective_iff_map_eq_zero (f := f)).2
    intro x hx
    obtain ⟨a,rfl⟩ := h x
    rw [hf] at hx
    rw [hx,zero_smul]
  · intro a
    exact ⟨a • z,hf a⟩

/-- With two invertible, the reflected incoming preimage tensored with the
middle quotient is the one-dimensional dot-sum line. -/
def incomingLiftTensorEquiv [NeZero (2 : k)] : BTQ ≃ₗ[k] k :=
  LinearEquiv.ofBijective (incomingLiftTensorReadout k)
    (bijective_of_line_readout (incomingLiftTensorReadout k) (dotSumTensor k)
      (tensor_dotSum_spans k) (incomingLiftTensorReadout_dotSum_generator k))

end
end Categorification.Stendhal.LabelTwo
