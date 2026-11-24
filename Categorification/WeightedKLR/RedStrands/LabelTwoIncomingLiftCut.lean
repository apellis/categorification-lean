/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingDegrees
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleFixedComplex
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCoordinates

/-!
# The middle loading of the incoming exterior preimage

The incoming preimage in the unquotiented middle standard has exactly
the dot-sum image at the middle loading. The middle left-dot coefficient
vanishes on the second dot-sum image and reads the first dot sum as one.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
noncomputable section

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

private def rightCut : Seq μ := labelTwoExteriorRightLoading

private theorem right_ordered : IsRedOrdered rightCut := by
  unfold IsRedOrdered
  decide +kernel

private abbrev incomingDivided :
    Submodule T (leftStandard («ν» := ν) (parameter k) weights rightCut right_ordered) :=
  labelTwoRightExteriorDividedStandard (parameter k)

/-- The preimage of the incoming exterior image in the unquotiented
middle standard. -/
def incomingLiftSubmodule : Submodule T S :=
  (LinearMap.range (normalizedIncoming k)).comap q

private theorem middle_idem_kills_incoming (u : incomingDivided k) :
    E • normalizedIncoming k u = 0 := by
  have hne : loading ≠ labelTwoExteriorRightLoading := by
    intro he
    have hx := congrArg (fun s : Seq μ => s.lbl ⟨1, by decide⟩) he
    change (Sum.inl () : Unit ⊕ Fin 2) = Sum.inr 1 at hx
    exact Sum.inl_ne_inr hx
  have h := labelTwo_rightStandard_loading_annihilation (parameter k) loading hne u.val
  have hE : E = tensorOfKLR (parameter k) weights ν (e loading) :=
    (stendhalTensorProjection_e weights ν loading loading_ordered).symm
  have hsub : E • u = 0 := by
    apply Subtype.ext
    change E • u.val = 0
    exact (congrArg (· • u.val) hE).trans h
  exact ((normalizedIncoming k).map_smul E u).symm.trans
    ((congrArg (normalizedIncoming k) hsub).trans (normalizedIncoming k).map_zero)

/-- At the middle loading, the incoming preimage is exactly the dot-sum
image of the middle fixed space. -/
theorem incomingLift_middle_fixed_iff (z : S) (hz : E • z = z) :
    z ∈ incomingLiftSubmodule k ↔ ∃ y : S, E • y = y ∧ diagramPlus k y = z := by
  constructor
  · rintro ⟨u,hu⟩
    have hq : q z = 0 := calc
      q z = q (E • z) := congrArg q hz.symm
      _ = E • q z := (q).map_smul E z
      _ = 0 := (congrArg (E • ·) hu.symm).trans (middle_idem_kills_incoming k u)
    change (Submodule.Quotient.mk z : B) = 0 at hq
    obtain ⟨y,hy⟩ := (Submodule.Quotient.mk_eq_zero U).mp hq
    refine ⟨E • y,?_,?_⟩
    · rw [← mul_smul, seqIdem_mul_self]
    · rw [map_smul, hy, hz]
  · rintro ⟨y,_,rfl⟩
    change q (diagramPlus k y) ∈ LinearMap.range (normalizedIncoming k)
    have hq : q (diagramPlus k y) = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr ⟨y,rfl⟩
    rw [hq]
    exact Submodule.zero_mem _

open Categorification.Webster.LabelTwo

local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "F" => fixSub k S E

private def fixedProjection : S →ₗ[k] F where
  toFun x := ⟨E • x, by
    change E • (E • x) = E • x
    rw [← mul_smul, seqIdem_mul_self]⟩
  map_add' x y := Subtype.ext (smul_add E x y)
  map_smul' c x := Subtype.ext ((smul_comm c E x).symm)

private def middleY₁Coefficient : Middle k →ₗ[k] k where
  toFun z := z.fst.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extract the left-dot coefficient at the middle fixed loading. -/
def middleY₁Readout : S →ₗ[k] k :=
  (middleY₁Coefficient k).comp
    ((middleToFixed k).symm.toLinearMap.comp (fixedProjection k))

private theorem readout_of_fixed (u : F) :
    middleY₁Readout k u.val = ((middleToFixed k).symm u).fst.snd := by
  have h : fixedProjection k u.val = u := Subtype.ext u.property
  exact congrArg (fun z => ((middleToFixed k).symm z).fst.snd) h

private theorem fixedPlus_val_eq (u : F) :
    (fixedPlus k u).val = diagramPlus k u.val := rfl

private theorem plus_sq_firstDotCoeff (b : Middle k) :
    (plus (plus b)).fst.snd = 0 := by
  rcases b with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rw [plus_coordinates, plus_coordinates]
  rfl

private theorem readout_middleFixed_plus_sq_zero (u : F) :
    middleY₁Readout k (diagramPlus k (diagramPlus k u.val)) = 0 := by
  obtain ⟨a,rfl⟩ := (middleToFixed k).surjective u
  have h₀ : diagramPlus k ((middleToFixed k) a).val =
      ((middleToFixed k) (plus a)).val :=
    congrArg Subtype.val (fixedPlus_transport k a)
  have h₁ : diagramPlus k ((middleToFixed k) (plus a)).val =
      ((middleToFixed k) (plus (plus a))).val :=
    congrArg Subtype.val (fixedPlus_transport k (plus a))
  have h := (congrArg (diagramPlus k) h₀).trans h₁
  rw [h, readout_of_fixed, LinearEquiv.symm_apply_apply]
  exact plus_sq_firstDotCoeff k a

/-- On the incoming preimage, applying the dot-sum endomorphism kills
the left-dot coefficient at the middle cut. -/
theorem middleY₁Readout_diagramPlus_incomingLift_zero (z : incomingLiftSubmodule k) :
    middleY₁Readout k (diagramPlus k z.val) = 0 := by
  have hmem : E • z.val ∈ incomingLiftSubmodule k :=
    Submodule.smul_mem _ _ z.property
  have hfixed : E • (E • z.val) = E • z.val := by
    rw [← mul_smul, seqIdem_mul_self]
  obtain ⟨y,hy,hr⟩ := (incomingLift_middle_fixed_iff k _ hfixed).mp hmem
  let u : F := ⟨y,hy⟩
  have h : fixedProjection k (diagramPlus k z.val) =
      fixedProjection k (diagramPlus k (diagramPlus k u.val)) := by
    apply Subtype.ext
    change E • diagramPlus k z.val = E • diagramPlus k (diagramPlus k y)
    rw [← (diagramPlus k).map_smul E, ← hr]
    have h₁ : E • diagramPlus k (diagramPlus k y) = diagramPlus k (diagramPlus k y) := by
      rw [← (diagramPlus k).map_smul E, ← (diagramPlus k).map_smul E, hy]
    exact h₁.symm
  exact (congrArg (fun w => ((middleToFixed k).symm w).fst.snd) h).trans
    (readout_middleFixed_plus_sq_zero k u)

/-- The unquotiented dot-sum generator has left-dot coefficient one at
the middle cut. -/
theorem middleY₁Readout_diagramPlus_generator :
    middleY₁Readout k (diagramPlus k g) = 1 := by
  rw [← middleToFixed_one_val k, ← fixedPlus_val_eq, fixedPlus_transport,
    readout_of_fixed, LinearEquiv.symm_apply_apply]
  have h : (plus (1 : Middle k)).fst.snd = 1 := by
    change (plus (⟨⟨1,0⟩,⟨0,0⟩⟩ : Middle k)).fst.snd = _
    rw [plus_coordinates]
    rfl
  exact h

local notation "fElt" => leftMiddleDot k + rightMiddleDot k

private theorem middleDots_commute_loading : Commute E fElt := by
  let π := stendhalTensorProjection (Q := parameter k) weights ν
  let S₀ := KLRAlgebra k (stendhalQ (parameter k) weights) μ
  let Z : S₀ := x ⟨1, by decide⟩ + x ⟨3, by decide⟩
  have h : Commute (e loading : S₀) Z := by
    change (e loading : S₀) * (x ⟨1, by decide⟩ + x ⟨3, by decide⟩) =
      (x ⟨1, by decide⟩ + x ⟨3, by decide⟩) * e loading
    rw [mul_add, add_mul, e_mul_x, e_mul_x]
  have he : π (e loading) = E := stendhalTensorProjection_e weights ν loading loading_ordered
  have hf : π Z = fElt := by
    change π (x ⟨1, by decide⟩ + x ⟨3, by decide⟩) = _
    exact π.map_add _ _
  exact (he ▸ hf ▸ h.map π.toRingHom)

private theorem middleDotElt_smul_fixed (u : F) :
    fElt • u.val = diagramPlus k u.val := by
  rw [add_smul, leftMiddleDot_smul_middle_fixed, rightMiddleDot_smul_middle_fixed]
  rfl

/-- On any lift in the incoming preimage, the ambient dot-sum action has
zero left-dot coefficient at the middle cut. -/
theorem middleY₁Readout_middleDotElt_incomingLift_zero (z : incomingLiftSubmodule k) :
    middleY₁Readout k (fElt • z.val) = 0 := by
  have h : fixedProjection k (fElt • z.val) = fixedProjection k (diagramPlus k z.val) := by
    apply Subtype.ext
    change E • (fElt • z.val) = E • diagramPlus k z.val
    rw [← mul_smul, (middleDots_commute_loading k).eq, mul_smul]
    exact (middleDotElt_smul_fixed k (fixedProjection k z.val)).trans
      ((diagramPlus k).map_smul E z.val)
  exact (congrArg (fun w => ((middleToFixed k).symm w).fst.snd) h).trans
    (middleY₁Readout_diagramPlus_incomingLift_zero k z)

/-- Projecting to the middle loading leaves the middle coefficient readout unchanged. -/
theorem middleY₁Readout_project_eq (z : S) : middleY₁Readout k (E • z) = middleY₁Readout k z := by
  have h : fixedProjection k (E • z) = fixedProjection k z := by
    apply Subtype.ext
    change E • (E • z) = E • z
    rw [← mul_smul, seqIdem_mul_self]
  exact congrArg (fun w => ((middleToFixed k).symm w).fst.snd) h


end
end Categorification.Stendhal.LabelTwo
