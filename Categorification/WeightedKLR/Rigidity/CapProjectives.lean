/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.DerivedCupCap
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.ProjectiveKProjective
import Categorification.WeightedKLR.Induction.Restriction

/-!
# Evaluation on a loading projective

Webster, arXiv:1309.3796v2, §7.1, proof of Proposition 7.5. Evaluating a
principal right projective against the left coefficient gives the image
of the corresponding idempotent in degree zero.
-/

noncomputable section
namespace Categorification.Stendhal.Coevaluation
open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero
universe u v
variable (k A L : Type u) [Field k] [Ring A] [Algebra k A] [AddCommGroup L]
  [Module k L] [Module A L] [IsScalarTower k A L]

private instance : SMulCommClass A k L where
  smul_comm a c x := smul_algebra_smul_comm c a x

local notation "CM" => OpBimodule A L
local notation "RP" f:arg => InDegreeZero (rIdeal f)
local notation "BT" f:arg => TensorProductOver Aᵐᵒᵖ (InDegreeZero CM) (RP f)

section OrdinaryTensor

variable {f : A} (hf : IsIdempotentElem f)

private def coefficientTensorMul : InDegreeZero CM →+ RP f →+ fixSub k L f where
  toFun b :=
    { toFun := fun p => ⟨p.val • (show L from b), by
        change f • (p.val • (show L from b)) = _
        rw [← mul_smul, p.property]⟩
      map_zero' := Subtype.ext (by
        change (0 : A) • (show L from b) = 0
        exact zero_smul _ _)
      map_add' p q := Subtype.ext (add_smul p.val q.val (show L from b)) }
  map_zero' := AddMonoidHom.ext fun p => Subtype.ext (by
    change p.val • (0 : L) = 0
    exact smul_zero _)
  map_add' b b' := AddMonoidHom.ext fun p => Subtype.ext (smul_add p.val b b')

private def coefficientTensorTo : BT f →+ fixSub k L f :=
  TensorProductOver.lift (coefficientTensorMul k A L (f := f)) fun a b p =>
    Subtype.ext (mul_smul p.val a.unop (show L from b)).symm

/-- Balancing the cap coefficient with a loading projective gives the
image of that loading idempotent in the left coefficient. -/
def coefficientLoadingTensorEquiv : BT f ≃ₗ[k] fixSub k L f := by
  let g : RP f := ⟨f, hf.eq⟩
  let inv : fixSub k L f →+ BT f :=
    ((TensorProductOver.tmulAddHom Aᵐᵒᵖ (InDegreeZero CM) (RP f)).flip g).comp
      (fixSub k L f).subtype.toAddMonoidHom
  have hleft : inv.comp (coefficientTensorTo k A L) = AddMonoidHom.id (BT f) := by
    apply TensorProductOver.addHom_ext
    intro b p
    change TensorProductOver.tmul Aᵐᵒᵖ (op (op p.val) • b) g =
      TensorProductOver.tmul Aᵐᵒᵖ b p
    rw [TensorProductOver.op_smul_tmul]
    congr 1
    exact Subtype.ext p.property
  refine { coefficientTensorTo k A L with
    invFun := inv
    left_inv := DFunLike.congr_fun hleft
    right_inv := fun x => Subtype.ext x.property
    map_smul' := ?_ }
  intro c x
  have h : (coefficientTensorTo k A L).comp (DistribSMul.toAddMonoidHom (BT f) c) =
      (DistribSMul.toAddMonoidHom (fixSub k L f) c).comp (coefficientTensorTo k A L) := by
    apply TensorProductOver.addHom_ext
    intro b p
    change coefficientTensorTo k A L (c • TensorProductOver.tmul Aᵐᵒᵖ b p) =
      c • coefficientTensorTo k A L (TensorProductOver.tmul Aᵐᵒᵖ b p)
    rw [TensorProductOver.smul_tmul]
    apply Subtype.ext
    change p.val • (c • (show L from b)) = c • (p.val • (show L from b))
    exact smul_algebra_smul_comm c p.val _
  exact DFunLike.congr_fun h x

end OrdinaryTensor


variable [HasDerivedCategory.{v,u} k] [HasDerivedCategory.{v,u} Aᵐᵒᵖ]
local notation "zeroObj" R:arg N:arg => DG.DerivedCategory.Q.obj (DGModuleCat.of R (InDegreeZero N))

/-- The cap on a loading projective is its idempotent image in degree zero. -/
def capFunctor_projectiveIso {f : A} (hf : IsIdempotentElem f) :
    (capFunctor k A L).obj (zeroObj Aᵐᵒᵖ (rIdeal f)) ≅ zeroObj k (fixSub k L f) := by
  let : Module.Projective Aᵐᵒᵖ (rIdeal f) := rIdeal_projective hf
  let U := DGModuleCat.of Aᵐᵒᵖ (RP f)
  let W := DGModuleCat.of k (InDegreeZero (fixSub k L f))
  let G := DGModuleCat.tensorFunctor (B := Aᵐᵒᵖ) k (InDegreeZero CM)
  let e : BT f ≃ᵈᵍ[k] InDegreeZero (fixSub k L f) :=
    DGModuleEquiv.ofDegreeZero (coefficientLoadingTensorEquiv k A L hf)
      (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
      TensorProductOver.d_inDegreeZero
      (fun y => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))
      (InDegreeZero.d_apply _)
  exact derivedTensorObjIso (A := k) (B := Aᵐᵒᵖ) (M := CM) (P := U)
    (show IsKProjective Aᵐᵒᵖ (RP f) from InDegreeZero.isKProjective) ≪≫
    DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv (M := G.obj U) (N := W) e)

end Categorification.Stendhal.Coevaluation
