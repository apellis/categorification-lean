/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleInjective
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixed
import Categorification.WeightedKLR.RedStrands.OppositeStandardTor
import Categorification.Algebra.DerivedHomologyShift
import Categorification.Algebra.DerivedTensorOrdinaryLinear
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDots
import Categorification.Algebra.DerivedTensorFiltration

/-!
# Ambient tensor homology of the incoming label-two exterior term

The horizontal reflection of the divided exterior standard is killed
by loading idempotents strictly above the exterior loading. An ordered
resolution proves acyclicity for the full standard, and the idempotent
splitting passes it to the divided standard. In degree zero the fixed-cut
comparison reduces the diagonal tensor to the reflected projector line.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable (k : Type) [Field k]
local notation "ν" => Multiset.replicate 2 ()
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "T" => TensorProductAlgebra k (parameter k) wt ν
local notation "A" => labelTwoExteriorRightLoading
local notation "μ" => stendhalWeight 2 ν
private theorem ordered : IsRedOrdered A := by unfold IsRedOrdered; decide +kernel
local notation "S" => leftStandard (parameter k) wt A ordered
private abbrev divided : Submodule T S := labelTwoRightExteriorDividedStandard (parameter k)
local notation "P" => divided k

private abbrev reflection : T →ₐ[k] Tᵐᵒᵖ := tensorReflect

private def reflectedAction : Tᵐᵒᵖ →+* T :=
  (RingEquiv.opOp T).symm.toRingHom.comp (reflection k).toRingHom.op

/-- The reflected incoming divided exterior term as a right diagram coefficient. -/
def IncomingExteriorCoefficient : Type := P

local notation "N" => IncomingExteriorCoefficient k

instance : AddCommGroup N := inferInstanceAs (AddCommGroup P)
instance : Module k N := inferInstanceAs (Module k P)
instance : Module Tᵐᵒᵖ N := Module.compHom P (reflectedAction k)

private theorem coefficient_op_smul (a : T) (z : N) :
    (op a • z : N) = ((reflection k a).unop • (show P from z) : P) := rfl

instance : SMulCommClass k Tᵐᵒᵖ N where
  smul_comm c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    rw [coefficient_op_smul, coefficient_op_smul]
    exact smul_comm c (reflection k b).unop (show P from z)

private theorem coefficient_kills_other (s : Seq μ) (hs : IsRedOrdered s) (hne : s ≠ A)
    (z : N) : op (seqIdem (parameter k) wt s hs) • z = 0 := by
  rw [coefficient_op_smul, unop_tensorReflect_e]
  have h : seqIdem (parameter k) wt s hs =
      tensorOfKLR (parameter k) wt ν (KLRAlgebra.e s) :=
    (stendhalTensorProjection_e wt ν s hs).symm
  apply Subtype.ext
  change seqIdem (parameter k) wt s hs • (show P from z).val = 0
  rw [h]
  exact labelTwo_rightStandard_loading_annihilation (parameter k) s hne (show P from z).val

private abbrev projection : Module.End T S := labelTwoRightExteriorProjection (parameter k)

private theorem splitting :
    (projection k).rangeRestrict.comp (P).subtype = LinearMap.id := by
  ext z
  obtain ⟨y,hy⟩ := z.property
  change projection k y = z.val at hy
  change projection k z.val = z.val
  rw [← hy]
  exact congrArg (fun f : Module.End T S => f y)
    (isIdempotentElem_labelTwoRightExteriorProjection (parameter k)).eq

private theorem coefficient_algebraMap_smul (c : k) (z : N) :
    (op (algebraMap k T c) • z : N) = c • z := by
  rw [coefficient_op_smul, AlgHom.commutes]
  exact algebraMap_smul T c (show P from z)

instance : IsScalarTower k Tᵐᵒᵖ N where
  smul_assoc c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    change (op (c • b) • z : N) = c • (op b • z)
    rw [coefficient_op_smul, coefficient_op_smul]
    change (reflection k (c • b)).unop • (show P from z) =
      c • ((reflection k b).unop • (show P from z))
    rw [map_smul, unop_smul, smul_assoc]

local notation "g" => leftStandardUnit (parameter k) wt A ordered
local notation "E" => seqIdem (parameter k) wt A ordered
local notation "𝓕" => fixSub k N (op E)
local notation "BTS" => BalancedTensor k k T N S
local notation "BTP" => BalancedTensor k k T N P
local notation "Aff" => KLRAlgebra k (stendhalQ (parameter k) wt) μ

private def projectorWord : Aff :=
  KLRAlgebra.x (⟨2, by decide⟩ : Fin (Multiset.card μ)) * KLRAlgebra.ψ 2 * KLRAlgebra.e A
private abbrev project : T := tensorOfKLR (parameter k) wt ν (projectorWord k)

private theorem coefficient_e_fixed (z : N) : (op E • z : N) = z := by
  rw [coefficient_op_smul, unop_tensorReflect_e]
  let z' : P := z
  have h : tensorOfKLR (parameter k) wt ν (KLRAlgebra.e A) = E :=
    stendhalTensorProjection_e wt ν A ordered
  apply Subtype.ext
  change E • z'.val = z'.val
  exact (congrArg (· • z'.val) h).symm.trans
    (labelTwo_rightStandard_loading_fixed (parameter k) z'.val)

private def stdTensorCoords : BTS ≃ₗ[k] 𝓕 :=
  leftStandardTensorEquivFixed (parameter k) wt A ordered N
    (fun s hs hlt z => coefficient_kills_other k s hs
      (fun he => hlt.2 (he ▸ fun _ _ => le_rfl)) z)

private def projectedTensorForward : BTP →ₗ[k] 𝓕 :=
  (stdTensorCoords k).toLinearMap.comp (BalancedTensor.mapRight (P).subtype)

private abbrev projectRestrict : S →ₗ[T] P := (projection k).rangeRestrict

private def projectedTensorBack : 𝓕 →ₗ[k] BTP :=
  (BalancedTensor.mapRight (projectRestrict k)).comp
    (stdTensorCoords k).symm.toLinearMap

set_option maxHeartbeats 650000 in
private theorem projectedTensor_split (v : BTP) :
    projectedTensorBack k (projectedTensorForward k v) = v := by
  change BalancedTensor.mapRight (projectRestrict k)
    ((stdTensorCoords k).symm
      ((stdTensorCoords k) (BalancedTensor.mapRight (P).subtype v))) = v
  rw [LinearEquiv.symm_apply_apply]
  change ((BalancedTensor.mapRight (projectRestrict k)).comp
    (BalancedTensor.mapRight (P).subtype)) v = v
  have hc := BalancedTensor.mapRight_comp (k := k) (B := k) (M := N)
    (P).subtype (projectRestrict k)
  have hr := congrArg
    (fun f : P →ₗ[T] P => BalancedTensor.mapRight (k := k) (B := k) (M := N) f)
    (splitting k)
  have hid := BalancedTensor.mapRight_id (k := k) (B := k) («A» := T) (M := N) («N» := P)
  exact DFunLike.congr_fun (hc.symm.trans (hr.trans hid)) v


private theorem projectedTensor_project (w : 𝓕) :
    (projectedTensorForward k (projectedTensorBack k w)).val = op (project k) • w.val := by
  change (stdTensorCoords k
    ((BalancedTensor.mapRight (P).subtype).comp
      (BalancedTensor.mapRight (projectRestrict k)) ((stdTensorCoords k).symm w))).val = _
  rw [← BalancedTensor.mapRight_comp]
  have hi : (P).subtype.comp (projectRestrict k) = projection k := rfl
  rw [hi]
  have h := leftStandardTensorEquivFixed_mapRight (parameter k) wt A ordered N
    (fun s hs hlt z => coefficient_kills_other k s hs
      (fun he => hlt.2 (he ▸ fun _ _ => le_rfl)) z)
    (projection k) (project k) (labelTwoRightExteriorProjection_generator (parameter k)) w
  exact h.trans (coefficient_e_fixed k (op (project k) • w.val))

set_option maxHeartbeats 850000 in
/-- Ordinary incoming exterior tensor is the right-coefficient subspace
fixed by the divided projector. -/
def incomingExteriorStandardTensorEquiv :
    BTP ≃ₗ[k] fixSub k N (op (project k)) := by
  let f := ((𝓕).subtype.comp (projectedTensorForward k)).codRestrict
    (fixSub k N (op (project k))) fun v => by
      change op (project k) • (projectedTensorForward k v).val = _
      rw [← projectedTensor_project, projectedTensor_split]
      rfl
  let r : fixSub k N (op (project k)) →ₗ[k] 𝓕 :=
    { toFun := fun w => ⟨w.val, coefficient_e_fixed k w.val⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let inverse := (projectedTensorBack k).comp r
  refine LinearEquiv.ofLinearMap f inverse ?_ ?_
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact (projectedTensor_project k (r w)).trans w.property
  · apply LinearMap.ext
    intro v
    change projectedTensorBack k (r (f v)) = v
    have hf : r (f v) = projectedTensorForward k v := Subtype.ext rfl
    rw [hf, projectedTensor_split]


private abbrev affineProjection : Aff →ₐ[k] T := stendhalTensorProjection (Q := parameter k) wt ν

private def crossingTranslate : P :=
  affineProjection k (KLRAlgebra.ψ 2) • projectRestrict k g

private theorem crossingTranslate_val :
    (crossingTranslate k).val =
      affineProjection k (KLRAlgebra.ψ 2) • (project k • g) := by
  exact congrArg (affineProjection k (KLRAlgebra.ψ 2) • ·)
    (labelTwoRightExteriorProjection_generator (parameter k))

set_option maxHeartbeats 850000 in
private theorem crossingTranslate_ne_zero : (crossingTranslate k).val ≠ 0 := by
  let coord := terminalQuotientCoordinates k
  let e := exteriorMiddleQuotientEquiv k
  let F := labelTwoExteriorToMiddle (parameter k)
  have hTranslate := congrArg (fun x : S => coord (e (F x))) (crossingTranslate_val k)
  have hProjected := congrArg coord (exteriorMiddleQuotientEquiv_projected_translate k)
  have h : coord (e (F (crossingTranslate k).val)) = (0, 1) :=
    hTranslate.trans (hProjected.trans (terminalQuotientCoordinates_incoming_translate k))
  intro hzero
  have h₀ := congrArg (fun x : S => coord (e (F x))) hzero
  have hF := congrArg (fun y => coord (e y)) F.map_zero
  have hE := congrArg coord e.map_zero
  have hz : coord (e (F (crossingTranslate k).val)) = 0 :=
    h₀.trans (hF.trans (hE.trans coord.map_zero))
  exact zero_ne_one (congrArg Prod.snd (hz.symm.trans h))

private def incomingFixedGenerator : fixSub k N (op (project k)) := by
  refine ⟨crossingTranslate k, ?_⟩
  change (op (project k) • (show N from crossingTranslate k) : N) = crossingTranslate k
  rw [coefficient_op_smul]
  apply Subtype.ext
  change (reflection k (project k)).unop • (crossingTranslate k).val = _
  rw [crossingTranslate_val]
  exact labelTwoRightExterior_reflectedProjector_fixes_translate (parameter k)

private theorem incomingFixed_spans (z : fixSub k N (op (project k))) :
    ∃ c : k, c • incomingFixedGenerator k = z := by
  let z' : P := z.val
  obtain ⟨c, hc⟩ := labelTwoRightExterior_reflectedProjector_image (parameter k) z'
  refine ⟨c, Subtype.ext (Subtype.ext ?_)⟩
  change c • (crossingTranslate k).val = z'.val
  rw [crossingTranslate_val]
  have hz : (op (project k) • z.val : N) = z.val := z.property
  rw [coefficient_op_smul] at hz
  have h : (reflection k (project k)).unop • z'.val = z'.val :=
    congrArg (fun x : P => x.val) hz
  exact hc.symm.trans h

/-- The reflected divided projector fixes precisely the one-dimensional line
generated by the black-crossing translate. -/
def incomingExteriorFixedLineEquiv : k ≃ₗ[k] fixSub k N (op (project k)) := by
  let f := LinearMap.toSpanSingleton k ↥(fixSub k N (op (project k))) (incomingFixedGenerator k)
  refine LinearEquiv.ofBijective f ⟨?_, incomingFixed_spans k⟩
  apply (injective_iff_map_eq_zero (f := f)).mpr
  intro c h
  have hz : c • (crossingTranslate k).val = 0 :=
    congrArg (fun z : fixSub k N (op (project k)) => (show P from z.val).val) h
  exact (smul_eq_zero.mp hz).resolve_right (crossingTranslate_ne_zero k)


variable [HasDerivedCategory.{w,0}
  (TensorProductAlgebra k (parameter k) (fun (_ : Fin 2) => Finsupp.single () 2)
    (Multiset.replicate 2 ()))]
  [HasDerivedCategory.{w,0} k]

private abbrev H (n : ℤ) : ModuleCat T ⥤ ModuleCat k :=
  degreeZeroModuleFunctor T ⋙ Q ⋙ derivedTensor k T N ⋙ homologyFunctor k n

/-- Ambient derived tensor homology of the divided incoming exterior term
and its horizontal reflection. -/
abbrev incomingExteriorAmbientHomology (n : ℤ) : ModuleCat k :=
  (H k n).obj (ModuleCat.of T P)

/-- An ordered loading resolution gives ambient acyclicity for the incoming
divided exterior diagonal. -/
theorem incomingExteriorAmbientHomology_isZero_of_support
    (R : ProjectiveResolution (ModuleCat.of T S))
    (hR : ∀ n : ℕ, ∃ (J : Type) (label : J → {s : Seq μ // IsRedOrdered s})
      (inc : ∀ j, lIdeal (seqIdem (parameter k) wt (label j).1 (label j).2) →ₗ[T]
        R.complex.X (n+1)),
      (∀ j, StendhalLT A (label j).1) ∧ ∀ x : R.complex.X (n+1),
        x ∈ Submodule.span T {y | ∃ j z, inc j z = y})
    (n : ℤ) (hn : n ≠ 0) : IsZero (incomingExteriorAmbientHomology k n) := by
  have hZ : IsZero ((H k n).obj (ModuleCat.of T S)) := by
    apply isZero_homology_of_isZero_intHomology k
    apply isZero_derivedTensorHomology_of_projectiveResolution_loading_support
      (M := N) R (fun s : {s : Seq μ // IsRedOrdered s} =>
        seqIdem (parameter k) wt s.1 s.2) (fun s => StendhalLT A s.1)
      (fun s => seqIdem_mul_self (parameter k) wt s.1 s.2) hR _ n hn
    intro s hs z
    have hne : s.1 ≠ A := by
      intro h
      exact hs.2 (h ▸ fun _ _ => le_rfl)
    exact coefficient_kills_other k s.1 s.2 hne z
  let F := H k n
  let i := ModuleCat.ofHom (P).subtype
  let r : ModuleCat.of T S ⟶ ModuleCat.of T P :=
    ModuleCat.ofHom (projection k).rangeRestrict
  have hsplit : i ≫ r = 𝟙 (ModuleCat.of T P) := ModuleCat.hom_ext (splitting k)
  have hmap : F.map i ≫ F.map r = 𝟙 (F.obj (ModuleCat.of T P)) := by
    exact (F.map_comp i r).symm.trans
      ((congrArg (fun u => F.map u) hsplit).trans (F.map_id _))
  apply (IsZero.iff_id_eq_zero _).2
  rw [← hmap, hZ.eq_of_tgt (F.map i) 0, zero_comp]


private def incomingOrdinaryBalanced :
    TensorProductOver T N P ≃ₗ[k] BTP where
  __ := ordinaryBalancedTensorAddEquiv («A» := k) (coefficient_algebraMap_smul k)
  map_smul' c z := by
    let e := ordinaryBalancedTensorAddEquiv («A» := k) («N» := P) (coefficient_algebraMap_smul k)
    change e (c • z) = c • e z
    induction z using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul m z => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The actual degree-zero ambient derived tensor of the incoming exterior
pair is its reflected divided-projector fixed subspace. -/
def incomingExteriorAmbientHomology_zero_equiv_fixed :
    incomingExteriorAmbientHomology k 0 ≃ₗ[k] fixSub k N (op (project k)) :=
  (ambientDerivedTensorH0Equiv (k := k) («A» := T) («N» := N) P).trans
    ((incomingOrdinaryBalanced k).trans (incomingExteriorStandardTensorEquiv k))

/-- The degree-zero ambient derived tensor of the incoming exterior pair is a scalar line. -/
def incomingExteriorAmbientHomology_zero : incomingExteriorAmbientHomology k 0 ≃ₗ[k] k :=
  (incomingExteriorAmbientHomology_zero_equiv_fixed k).trans (incomingExteriorFixedLineEquiv k).symm

end
end Categorification.Stendhal.LabelTwo
