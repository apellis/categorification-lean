/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Module.TensorProductOver
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleLayerResolution
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleTensorDifferentials
import Categorification.Algebra.DerivedTensorHomology
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Relative derived tensor at the label-two middle cut

The actual periodic projective resolution over the middle layer tensors
with the reflected actual coefficient to the separated factor complex.
In each degree the ordinary tensor is the dual-number space and the
differentials alternate zero and multiplication by twice the variable.
-/

noncomputable section

namespace DG.TensorProductOver

open MulOpposite

variable {k A B M N : Type*} [CommRing k] [Ring A] [Ring B]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [Module Bᵐᵒᵖ M]
  [SMulCommClass k Aᵐᵒᵖ M] [SMulCommClass k Bᵐᵒᵖ M]
  [AddCommGroup N] [Module A N] [Module B N]
  (σ : A →+* B) (hσ : Function.Surjective σ)
  (hM : ∀ a m, op (σ a) • (m : M) = op a • m)
  (hN : ∀ a n, σ a • (n : N) = a • n)

private def quotientToAdd : TensorProductOver A M N →+ TensorProductOver B M N :=
  lift (tmulAddHom B M N) (fun a m n => by
    change tmul B (op a • m) n = tmul B m (a • n)
    rw [← hM a m, ← hN a n, op_smul_tmul])

private def quotientFromAdd : TensorProductOver B M N →+ TensorProductOver A M N :=
  lift (tmulAddHom A M N) (fun b m n => by
    obtain ⟨a, rfl⟩ := hσ b
    change tmul A (op (σ a) • m) n = tmul A m (σ a • n)
    rw [hM, hN, op_smul_tmul])

/-- Balanced tensor is unchanged when both actions descend along a surjective
ring homomorphism. The equivalence preserves each pure tensor. -/
def quotientScalarsEquiv :
    TensorProductOver A M N ≃ₗ[k] TensorProductOver B M N where
  __ := quotientToAdd σ hM hN
  invFun := quotientFromAdd σ hσ hM hN
  left_inv t := by
    change quotientFromAdd σ hσ hM hN (quotientToAdd σ hM hN t) = t
    induction t using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv t := by
    change quotientToAdd σ hM hN (quotientFromAdd σ hσ hM hN t) = t
    induction t using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_smul' c t := by
    change quotientToAdd σ hM hN (c • t) = c • quotientToAdd σ hM hN t
    induction t using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, ← smul_add, map_add]

/-- The quotient comparison preserves a pure tensor. -/
theorem quotientScalarsEquiv_tmul (m : M) (n : N) :
    quotientScalarsEquiv (k := k) σ hσ hM hN (tmul A m n) = tmul B m n := rfl

/-- The inverse quotient comparison preserves a pure tensor. -/
theorem quotientScalarsEquiv_symm_tmul (m : M) (n : N) :
    (quotientScalarsEquiv (k := k) σ hσ hM hN).symm (tmul B m n) = tmul A m n := rfl

end DG.TensorProductOver

noncomputable section


namespace Categorification.Stendhal.LabelTwo

open CategoryTheory KLR MulOpposite DG

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k
local notation "Qmod" => StandardDotSumQuotient k
local notation "Coeff" => MiddleTensorCoefficient k
local notation "Higher" => leftStandardHigherLoadingIdeal (parameter k) weights loading
local notation "Layer" => LeftStandardLayerAlgebra (parameter k) weights loading
local notation "p" => RingCon.mkₐ k (TwoSidedIdeal.ringCon Higher)

private abbrev reflect := tensorReflect (Q := parameter k) (Λ := weights) (ν := blackWeight)

/-- Diagram reflection preserves the upper ideal and descends to the middle layer. -/
def middleLayerReflect : Layer →+* Layerᵐᵒᵖ := by
  let f : Ambient →+* Layerᵐᵒᵖ := ((p).toRingHom.op).comp (reflect k).toRingHom
  apply (Higher).ringCon.lift f
  apply (TwoSidedIdeal.ringCon_le_iff (I := Higher) (J := TwoSidedIdeal.ker f)).mp
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨s, hs, hlt, rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  change op (p ((reflect k (seqIdem (parameter k) weights s hs)).unop)) = 0
  rw [unop_tensorReflect_e, leftStandardLayer_quotient_higher (parameter k) weights loading
    s hs hlt, op_zero]

private def middleLayerRightAction : Layerᵐᵒᵖ →+* Layer :=
  (RingEquiv.opOp Layer).symm.toRingHom.comp (middleLayerReflect k).op

instance : Module Layerᵐᵒᵖ Coeff :=
  Module.compHom Qmod (middleLayerRightAction k)

/-- The descended action recovers the ordinary reflected action. -/
theorem middleLayerCoefficient_smul_mk (a : Ambient) (z : Coeff) :
    (op (p a) • z : Coeff) = op a • z := rfl

private theorem p_surj : Function.Surjective (p : Ambient → Layer) :=
  (Higher).ringCon.mk'_surjective

instance : SMulCommClass k Layerᵐᵒᵖ Coeff where
  smul_comm c b z := by
    obtain ⟨b, rfl⟩ := op_surjective b
    obtain ⟨a, rfl⟩ := p_surj k b
    rw [middleLayerCoefficient_smul_mk, middleLayerCoefficient_smul_mk]
    exact smul_comm c (op a) z

instance : IsScalarTower k Layerᵐᵒᵖ Coeff where
  smul_assoc c b z := by
    obtain ⟨b, rfl⟩ := op_surjective b
    obtain ⟨a, rfl⟩ := p_surj k b
    change (op (c • p a) • z : Coeff) = c • (op (p a) • z)
    rw [← map_smul (p), middleLayerCoefficient_smul_mk, middleLayerCoefficient_smul_mk]
    exact smul_assoc c (op a) z

private def layerTensorMap {X Y : ModuleCat Layer} (f : X →ₗ[Layer] Y) :
    TensorProductOver Layer Coeff X →ₗ[k] TensorProductOver Layer Coeff Y where
  toFun := TensorProductOver.map LinearMap.id f
  map_add' := (TensorProductOver.map LinearMap.id f).map_add
  map_smul' c t := by
    let g := TensorProductOver.map (LinearMap.id : Coeff →ₗ[Layerᵐᵒᵖ] Coeff) f
    change g (c • t) = c • g t
    induction t using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul x y => rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The ordinary tensor functor with the actual reflected coefficient, over
the middle layer algebra. -/
def tensorOverMiddleLayer : ModuleCat Layer ⥤ ModuleCat k where
  obj X := ModuleCat.of k (TensorProductOver Layer Coeff X)
  map f := ModuleCat.ofHom (layerTensorMap k f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change TensorProductOver.map (LinearMap.id : Coeff →ₗ[Layerᵐᵒᵖ] Coeff)
      (LinearMap.id : X →ₗ[Layer] X) t = t
    exact DFunLike.congr_fun TensorProductOver.map_id t
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change TensorProductOver.map (LinearMap.id : Coeff →ₗ[Layerᵐᵒᵖ] Coeff) (g.hom.comp f.hom) t =
      TensorProductOver.map LinearMap.id g.hom (TensorProductOver.map LinearMap.id f.hom t)
    exact DFunLike.congr_fun
      (TensorProductOver.map_comp (LinearMap.id : Coeff →ₗ[Layerᵐᵒᵖ] Coeff) LinearMap.id f.hom g.hom) t

instance : (tensorOverMiddleLayer k).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    let I : Coeff →ₗ[Layerᵐᵒᵖ] Coeff := LinearMap.id
    change TensorProductOver.map I (f.hom + g.hom) t =
      TensorProductOver.map I f.hom t + TensorProductOver.map I g.hom t
    induction t using TensorProductOver.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul x y => exact TensorProductOver.tmul_add x (f y) (g y)
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_add_add_comm]

open Categorification.Webster.LabelTwo
open scoped DualNumber

local notation "Tens" => TensorProductOver Layer Coeff S
local notation "Ord" => BalancedTensor k k Ambient Coeff S
local notation "Post" => postTensorComplex (k := k)
local notation "F" => tensorOverMiddleLayer k
local notation "P" => relativeMiddleProjectiveResolution k
local notation "C" => relativeMiddleComplex k
local notation "shape" => ComplexShape.down ℕ

private def ambientTensorLinearEquiv : TensorProductOver Ambient Coeff S ≃ₗ[k] Ord where
  __ := ordinaryBalancedTensorAddEquiv (A := k) (middleTensorCoefficient_algebraMap_smul k)
  map_smul' c z := by
    let e := ordinaryBalancedTensorAddEquiv (A := k) (N := S)
      (middleTensorCoefficient_algebraMap_smul k)
    change e (c • z) = c • e z
    induction z using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul m z => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private def ambientLayerTensorEquiv : TensorProductOver Ambient Coeff S ≃ₗ[k] Tens :=
  TensorProductOver.quotientScalarsEquiv (p).toRingHom (p_surj k)
    (middleLayerCoefficient_smul_mk k)
    (leftStandardLayer_smul_mk (parameter k) weights loading loading_ordered)

/-- Compare the tensor of the middle standard over the layer with its ordinary
diagram tensor. Both actions descend from the original diagram algebra. -/
def layerTensorAtStandard : Tens ≃ₗ[k] Ord :=
  (ambientLayerTensorEquiv k).symm.trans (ambientTensorLinearEquiv k)

/-- The ordinary and layer tensors identify the same diagram generators. -/
theorem layerTensorAtStandard_tmul (m : Coeff) (z : S) :
    layerTensorAtStandard k (TensorProductOver.tmul Layer m z) = BalancedTensor.tmul m z := rfl

private theorem relative_d_succ_apply (n : ℕ) (z : S) :
    (((C).d (n + 1) n).hom) z =
      (if Even n then diagramPlus k else diagramMinus k) z := by
  change ((ChainComplex.of.d (fun _ => ModuleCat.of Layer S) _ (n + 1) n).hom) z = _
  rw [ChainComplex.of_d]
  rfl

private theorem post_d_succ (n : ℕ) :
    ((Post).d (n + 1) n).hom = if Even n then 0 else twiceEps := by
  change (ChainComplex.of.d (fun _ => ModuleCat.of k (DualNumber k)) _ (n + 1) n).hom = _
  rw [ChainComplex.of_d]
  change (if Even n then 0 else ModuleCat.ofHom (twiceEps (k := k))).hom = _
  by_cases h : Even n <;> simp [h]

private theorem layerTensorMap_apply (f : Module.End Layer S) (g : Module.End Ambient S)
    (h : ∀ z, f z = g z) (t : Tens) :
    layerTensorAtStandard k (TensorProductOver.map LinearMap.id f t) =
      BalancedTensor.mapRight g (layerTensorAtStandard k t) := by
  induction t using TensorProductOver.induction_on with
  | zero => simp only [map_zero]
  | tmul m z =>
    simp only [TensorProductOver.map_tmul, LinearMap.id_coe, id_eq,
      layerTensorAtStandard_tmul, BalancedTensor.mapRight_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

private def layerTermEquiv : Tens ≃ₗ[k] DualNumber k :=
  (layerTensorAtStandard k).trans (middleStandardTensorEquiv k)

private abbrev layerTensorComplex :=
  ((tensorOverMiddleLayer k).mapHomologicalComplex (ComplexShape.down ℕ)).obj (C)

private theorem post_d_succ_apply (j : ℕ) (v : DualNumber k) :
    ((Post).d (j + 1) j).hom v = if Even j then 0 else (ε + ε) * v := by
  rw [post_d_succ]
  by_cases hj : Even j
  · rw [ite_eq_left hj, ite_eq_left hj, LinearMap.zero_apply]
  · rw [ite_eq_right hj, ite_eq_right hj, twiceEps_apply]

private theorem layerTensorTerm_compat (j : ℕ) (t : Tens) :
    ((Post).d (j + 1) j).hom (layerTermEquiv k t) =
      layerTermEquiv k
        (TensorProductOver.map LinearMap.id (((C).d (j + 1) j).hom) t) := by
  let d : Module.End Layer S := ((C).d (j + 1) j).hom
  let u : Ord := layerTensorAtStandard k t
  let E := middleStandardTensorEquiv k
  have post : ((Post).d (j + 1) j).hom (layerTermEquiv k t) =
      if Even j then 0 else (ε + ε) * E u :=
    post_d_succ_apply k j (layerTermEquiv k t)
  change _ = E (layerTensorAtStandard k (TensorProductOver.map LinearMap.id d t))
  by_cases hj : Even j
  · have hd (z : S) : d z = diagramPlus k z :=
      (relative_d_succ_apply k j z).trans (ite_eq_left hj ▸ rfl)
    have hmap := congrArg E (layerTensorMap_apply k d (diagramPlus k) hd t)
    exact (post.trans (ite_eq_left hj)).trans ((middleStandardTensorEquiv_plus k u).symm.trans hmap.symm)
  · have hd (z : S) : d z = diagramMinus k z :=
      (relative_d_succ_apply k j z).trans (ite_eq_right hj ▸ rfl)
    have hmap := congrArg E (layerTensorMap_apply k d (diagramMinus k) hd t)
    exact (post.trans (ite_eq_right hj)).trans ((middleStandardTensorEquiv_minus k u).symm.trans hmap.symm)

/-- Tensoring the actual projective resolution over the middle layer yields the
specialized periodic factor complex, including its alternating maps. -/
def layerTensorResolutionIso : layerTensorComplex k ≅ Post := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => (layerTermEquiv k).toModuleIso) ?_
  intro i j h
  obtain rfl : i = j + 1 := h.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (t : Tens)
  exact layerTensorTerm_compat k j t

/-- The relative Tor of the actual reflected and left diagrammatic dot-sum
quotients. -/
abbrev relativeMiddleTor (n : ℕ) : ModuleCat k :=
  ((tensorOverMiddleLayer k).leftDerived n).obj (ModuleCat.of Layer Qmod)

/-- The relative diagrammatic Tor is the homology of the specialized factor
complex from Webster's calculation. -/
def relativeMiddleTorHomologyIso (n : ℕ) : relativeMiddleTor k n ≅ (Post).homology n :=
  ((P).isoLeftDerivedObj (F) n).trans
    ((HomologicalComplex.homologyFunctor _ shape n).mapIso (layerTensorResolutionIso k))

/-- The degree-zero relative Tor has the two dual-number classes. -/
def relativeMiddleTorZero :
    relativeMiddleTor k 0 ≅ ModuleCat.of k (DualNumber k) :=
  relativeMiddleTorHomologyIso k 0 ≪≫ postTensorHomologyZero

/-- Every positive relative Tor is one-dimensional if the characteristic
of the ground field is different from two. -/
def relativeMiddleTorPositive (n : ℕ) (h₂ : (2 : k) ≠ 0) :
    relativeMiddleTor k (n + 1) ≅ ModuleCat.of k k :=
  relativeMiddleTorHomologyIso k (n + 1) ≪≫
    if h : Even n then postTensorHomologyOdd n h h₂ else postTensorHomologyPositiveEven n h h₂

end Categorification.Stendhal.LabelTwo