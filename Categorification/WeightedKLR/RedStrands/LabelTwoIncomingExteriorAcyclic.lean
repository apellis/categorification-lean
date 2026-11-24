/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorStandardSupport
import Categorification.WeightedKLR.RedStrands.OppositeStandardTor
import Categorification.Algebra.DerivedHomologyShift
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDots
import Categorification.Algebra.DerivedTensorFiltration

/-!
# Ambient acyclicity of the incoming label-two exterior term

The horizontal reflection of the divided exterior standard is killed
by loading idempotents strictly above the exterior loading. An ordered
resolution proves acyclicity for the full standard, and the idempotent
splitting passes it to the divided standard.
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


end
end Categorification.Stendhal.LabelTwo
