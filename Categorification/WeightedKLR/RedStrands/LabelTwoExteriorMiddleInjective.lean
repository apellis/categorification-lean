/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCoordinates
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleReadout
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorStandardSupport

/-!
# The incoming label-two crossing is injective

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The two diagrammatic
descriptions of the middle quotient agree. The projected exterior generator
and its black-crossing translate then have independent terminal coordinates.
-/

namespace Categorification.Stendhal.LabelTwo
open KLR

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

theorem exterior_middle_loading_alignment : labelTwoMiddleLoading = loading := by
  apply Subtype.ext
  funext j
  fin_cases j <;> rfl

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "g" => leftStandardUnit («ν» := ν) (parameter k) weights loading loading_ordered

private theorem oldOrdered : IsRedOrdered labelTwoMiddleLoading := by
  unfold IsRedOrdered
  decide +kernel

private def transportLoading {s t : KLR.Seq (stendhalWeight 2 ν)} (hs : IsRedOrdered s)
    (ht : IsRedOrdered t) (h : s = t) :
    leftStandard («ν» := ν) (parameter k) weights s hs ≃ₗ[A] leftStandard («ν» := ν) (parameter k) weights t ht := by
  subst t
  exact LinearEquiv.refl _ _

private theorem transportLoading_unit {s t : KLR.Seq (stendhalWeight 2 ν)}
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) (h : s = t) :
    transportLoading k hs ht h (leftStandardUnit («ν» := ν) (parameter k) weights s hs) =
      leftStandardUnit («ν» := ν) (parameter k) weights t ht := by
  subst t
  rfl

local notation "rawν" => Multiset.replicate 2 ()
local notation "rawW" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "old" => leftStandard («ν» := rawν) (parameter k) rawW labelTwoMiddleLoading oldOrdered
local notation "oldGen" => leftStandardUnit («ν» := rawν) (parameter k) rawW labelTwoMiddleLoading oldOrdered
local notation "bridge" => transportLoading k oldOrdered loading_ordered exterior_middle_loading_alignment

private abbrev oldDotSum : Module.End (TensorProductAlgebra k (parameter k) rawW rawν) old :=
  labelTwoMiddleDotSumEnd (parameter k)

private theorem oldDotSum_generator :
    oldDotSum k oldGen =
      tensorOfKLR (parameter k) rawW rawν
        (KLRAlgebra.x ⟨1, by decide⟩ + KLRAlgebra.x ⟨3, by decide⟩) • oldGen :=
  labelTwoMiddleDotSumEnd_generator (parameter k)

local notation "oldAligned" => leftStandard («ν» := ν) (parameter k) weights labelTwoMiddleLoading oldOrdered

private def oldDotSumAligned : Module.End A oldAligned :=
  oldDotSum k

private theorem transportLoading_conj_by_gen
    {s t : KLR.Seq (stendhalWeight 2 ν)}
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) (h : s = t)
    (d : A)
    (f : Module.End A (leftStandard («ν» := ν) (parameter k) weights s hs))
    (r : Module.End A (leftStandard («ν» := ν) (parameter k) weights t ht))
    (hf : f (leftStandardUnit («ν» := ν) (parameter k) weights s hs) =
      d • leftStandardUnit («ν» := ν) (parameter k) weights s hs)
    (hr : r (leftStandardUnit («ν» := ν) (parameter k) weights t ht) =
      d • leftStandardUnit («ν» := ν) (parameter k) weights t ht) :
    (transportLoading k hs ht h).toLinearMap.comp
      (f.comp (transportLoading k hs ht h).symm.toLinearMap) = r := by
  subst t
  apply leftStandard_hom_ext s hs
  change f (leftStandardUnit («ν» := ν) (parameter k) weights s hs) =
    r (leftStandardUnit («ν» := ν) (parameter k) weights s ht)
  exact hf.trans hr.symm

def alignedDotSum : Module.End A (Standard k) :=
  (bridge).toLinearMap.comp ((oldDotSumAligned k).comp (bridge).symm.toLinearMap)

private theorem diagramPlus_generator :
    diagramPlus k g =
      tensorOfKLR (parameter k) weights ν
        (KLRAlgebra.x ⟨1, by decide⟩ + KLRAlgebra.x ⟨3, by decide⟩) • g := by
  change dotEnd k 0 g + dotEnd k 1 g = _
  rw [dotEnd_zero_gen, dotEnd_one_gen]
  simp only [leftMiddleDot, rightMiddleDot, tensorOfKLR, map_add, add_smul]

theorem exterior_middle_dotSum_alignment : alignedDotSum k = diagramPlus k :=
  transportLoading_conj_by_gen k oldOrdered loading_ordered exterior_middle_loading_alignment _
    (oldDotSumAligned k) (diagramPlus k) (oldDotSum_generator k) (diagramPlus_generator k)

private theorem alignedDotSum_range :
    (LinearMap.range (oldDotSumAligned k)).map (bridge).toLinearMap =
      LinearMap.range (diagramPlus k) := by
  rw [← exterior_middle_dotSum_alignment]
  apply le_antisymm
  · rintro _ ⟨u, ⟨v, rfl⟩, rfl⟩
    refine ⟨(bridge) v, ?_⟩
    change (bridge) (oldDotSumAligned k ((bridge).symm ((bridge) v))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · rintro _ ⟨y, rfl⟩
    refine ⟨oldDotSumAligned k ((bridge).symm y), ⟨(bridge).symm y, rfl⟩, ?_⟩
    rfl

/-- The middle quotient of the two exterior crossing maps is the quotient
used by the separated terminal coordinate calculation. -/
def exteriorMiddleQuotientEquiv :
    (oldAligned ⧸ LinearMap.range (oldDotSumAligned k)) ≃ₗ[A] StandardDotSumQuotient k :=
  Submodule.Quotient.equiv _ _ (bridge) (alignedDotSum_range k)

private def alignedOldBar : oldAligned ⧸ LinearMap.range (oldDotSumAligned k) :=
  Submodule.Quotient.mk oldGen

/-- The middle quotient comparison transports the generating diagram. -/
theorem exteriorMiddleQuotientEquiv_mk_unit :
    exteriorMiddleQuotientEquiv k (Submodule.Quotient.mk oldGen) =
      (LinearMap.range (diagramPlus k)).mkQ g := by
  change (LinearMap.range (diagramPlus k)).mkQ ((bridge) oldGen) = _
  exact congrArg (LinearMap.range (diagramPlus k)).mkQ
    (transportLoading_unit k oldOrdered loading_ordered exterior_middle_loading_alignment)

end
end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo
open KLR KLRAlgebra Categorification.Webster.LabelTwo

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "Et" => seqIdem (parameter k) weights terminalLoading terminalLoading_ordered
local notation "S" => Standard k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "V" => fixSub k (StandardDotSumQuotient k) Et
local notation "T" => fixSub k S Et
local notation "J" => LinearEquiv.symm (terminalToTwoMiddle k)
local notation "u" => J (middleToFixed k (1 : Middle k), middleToFixed k (y₂ : Middle k))
local notation "v" => J (0, middleToFixed k (1 : Middle k))

/-- Reading the terminal loading cut on the full middle dot-sum quotient. -/
def terminalQuotientProjection : StandardDotSumQuotient k →ₗ[k] V where
  toFun z := ⟨Et • z, by
    change Et • (Et • z) = Et • z
    rw [← mul_smul, seqIdem_mul_self]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext (((Algebra.lsmul k k _ : A →ₐ[k] Module.End k _) Et).map_smul c x)

theorem terminalQuotientProjection_mk (z : T) :
    terminalQuotientProjection k ((U).mkQ z.val) = terminalQuotientMap k z := by
  apply Subtype.ext
  change Et • (U).mkQ z.val = (U).mkQ z.val
  rw [← map_smul, show Et • z.val = z.val from z.property]

/-- Terminal loading coordinates extended to the full middle quotient. -/
def terminalQuotientCoordinates : StandardDotSumQuotient k →ₗ[k]
    DualNumber k × DualNumber k :=
  (terminalCutDotSumEquiv k).toLinearMap.comp (terminalQuotientProjection k)

theorem terminalQuotientCoordinates_incoming :
    terminalQuotientCoordinates k ((U).mkQ (u).val) =
      ((1, -DualNumber.eps) : DualNumber k × DualNumber k) := by
  change terminalCutDotSumEquiv k (terminalQuotientProjection k ((U).mkQ (u).val)) = _
  exact (congrArg (terminalCutDotSumEquiv k) (terminalQuotientProjection_mk k u)).trans
    (incomingDiagram_coordinates k)

theorem terminalQuotientCoordinates_incoming_translate :
    terminalQuotientCoordinates k ((U).mkQ (v).val) =
      ((0, 1) : DualNumber k × DualNumber k) := by
  change terminalCutDotSumEquiv k (terminalQuotientProjection k ((U).mkQ (v).val)) = _
  exact (congrArg (terminalCutDotSumEquiv k) (terminalQuotientProjection_mk k v)).trans
    (incomingDiagram_translate_coordinates k)

end
end Categorification.Stendhal.LabelTwo

noncomputable section

namespace Categorification.Stendhal.LabelTwo

variable {k : Type*} [CommRing k]

/-- The two incoming coordinate vectors are linearly independent over the ground ring. -/
theorem incoming_coordinates_coefficients_eq_zero {a b : k}
    (h : a • ((1, -DualNumber.eps) : DualNumber k × DualNumber k) +
      b • ((0, 1) : DualNumber k × DualNumber k) = 0) :
    a = 0 ∧ b = 0 := by
  have ha := congrArg (fun v : DualNumber k × DualNumber k => v.1.fst) h
  have hb := congrArg (fun v : DualNumber k × DualNumber k => v.2.fst) h
  exact ⟨by simpa using ha, by simpa using hb⟩

/-- The two scalar equations of the outgoing terminal rows cut out exactly
the span of the two incoming vectors. -/
theorem exists_incoming_coordinates_of_outgoing_zero
    (u v : DualNumber k) (h₀ : u.fst + v.snd = 0) (h₁ : u.snd = 0) :
    ∃ a b : k, (u,v) = a • ((1, -DualNumber.eps) : DualNumber k × DualNumber k) +
      b • ((0, 1) : DualNumber k × DualNumber k) := by
  refine ⟨u.fst, v.fst, Prod.ext ?_ ?_⟩
  · apply TrivSqZeroExt.ext <;> simp [h₁]
  · have hv : v.snd = -u.fst := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h₀)
    apply TrivSqZeroExt.ext <;> simp [hv]

end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra Categorification.Webster.LabelTwo

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "rawν" => Multiset.replicate 2 ()
local notation "rawW" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "oldLoading" => labelTwoMiddleLoading
local notation "B" => labelTwoExteriorRightLoading
local notation "H" => KLRAlgebra k (stendhalQ (parameter k) weights) (stendhalWeight 2 ν)
local notation "rawH" => KLRAlgebra k (stendhalQ (parameter k) rawW) (stendhalWeight 2 rawν)
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "rawπ" => tensorOfKLR (parameter k) rawW rawν
local notation "X₂" => (x (⟨2, by decide⟩ : Fin (Multiset.card (stendhalWeight 2 rawν))) : rawH)
local notation "X₃" => (x (⟨3, by decide⟩ : Fin (Multiset.card (stendhalWeight 2 ν))) : H)
local notation "U" => LinearMap.range (diagramPlus k)
local notation "E" => exteriorMiddleQuotientEquiv k
local notation "g" => leftStandardUnit («ν» := ν) (parameter k) weights loading loading_ordered
local notation "coord" => terminalQuotientCoordinates k
local notation "J" => LinearEquiv.symm (terminalToTwoMiddle k)
local notation "u" => J (middleToFixed k (1 : Middle k), middleToFixed k (y₂ : Middle k))
local notation "v" => J (0, middleToFixed k (1 : Middle k))

private theorem terminal_ordered : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
local notation "start" => leftStandard («ν» := rawν) (parameter k) rawW B terminal_ordered
local notation "gB" => leftStandardUnit («ν» := rawν) (parameter k) rawW B terminal_ordered
local notation "v₀" => (rawπ (X₂ * ψ 2 * e B : rawH) • gB : start)
local notation "v₁" => (rawπ (ψ 2 : rawH) • v₀ : start)
local notation "F" => labelTwoExteriorToMiddle (parameter k)
local notation "E₁" => labelTwoExteriorMiddleDifferential (parameter k)

private def oldMiddleCut : KLR.Seq (stendhalWeight 2 ν) := labelTwoMiddleLoading

private theorem oldMiddleCut_eq_loading : oldMiddleCut = loading :=
  exterior_middle_loading_alignment

local notation "oldBar" => alignedOldBar k

private theorem middleGen_fixed :
    π (e loading) • g = g := by
  have he : π (e loading) = seqIdem (parameter k) weights loading loading_ordered := by
    apply congrArg (TensorProductAlgebra.mk (parameter k) weights ν)
    apply Subtype.ext
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem loading).trans (ite_eq_left loading_ordered)
  rw [he, leftStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (seqIdem_mul_self (parameter k) weights loading loading_ordered)

private theorem raw_map_mul (a b : H) : π (a * b) = π a * π b := by
  simp only [tensorOfKLR, map_mul]

private theorem compare_oldBar_smul (a : A) :
    E (a • oldBar) = (U).mkQ (a • g) := by
  have hbar : E oldBar = (U).mkQ g := exteriorMiddleQuotientEquiv_mk_unit k
  exact ((E).map_smul a oldBar).trans
    ((congrArg (a • ·) hbar).trans ((U).mkQ.map_smul a g).symm)

private theorem compare_oldBar_smul_add (a b : A) :
    E (a • oldBar + b • oldBar) = (U).mkQ (a • g + b • g) :=
  ((E).map_add _ _).trans <|
    (congrArg₂ (· + ·) (compare_oldBar_smul k a) (compare_oldBar_smul k b)).trans
      ((U).mkQ.map_add _ _).symm

private def incomingRowA : A := π ((ψ 1 : H) * e oldMiddleCut)
private def incomingRowB : A := π ((ψ 2 : H) * ((ψ 1 : H) * (X₃ * e oldMiddleCut)))
private def incomingRowC : A := π ((ψ 2 : H) * ((ψ 1 : H) * e oldMiddleCut))

private theorem actual_incoming_diagram :
    incomingRowA k • g + incomingRowB k • g = (u).val := by
  unfold incomingRowA incomingRowB
  rw [incomingDiagram_val k, oldMiddleCut_eq_loading]
  simp only [raw_map_mul, mul_smul, middleGen_fixed, ψw_cons, ψw_nil, mul_one, rightMiddleDot]

private theorem actual_incoming_translate_diagram : incomingRowC k • g = (v).val := by
  unfold incomingRowC
  rw [incomingDiagram_translate_val k, oldMiddleCut_eq_loading]
  simp only [raw_map_mul, mul_smul, middleGen_fixed, ψw_cons, ψw_nil, mul_one]

/-- The projected exterior generator gives the dotted incoming shuffle diagram in the common quotient. -/
theorem exteriorMiddleQuotientEquiv_projected_generator :
    E (F v₀) = (U).mkQ (u).val := by
  refine (congrArg (fun w => E w) (labelTwoExteriorMiddle_map_projectedGen (parameter k))).trans ?_
  exact (compare_oldBar_smul_add k (incomingRowA k) (incomingRowB k)).trans (congrArg ((U).mkQ) (actual_incoming_diagram k))

/-- The black-crossing translate gives the undotted second shuffle in the common quotient. -/
theorem exteriorMiddleQuotientEquiv_projected_translate :
    E (F v₁) = (U).mkQ (v).val := by
  refine (congrArg (fun w => E w) (labelTwoExteriorMiddle_map_projectedTranslate (parameter k))).trans ?_
  exact (compare_oldBar_smul k (incomingRowC k)).trans (congrArg ((U).mkQ) (actual_incoming_translate_diagram k))

private def exteriorReadout : start →ₗ[k] DualNumber k × DualNumber k :=
  (coord).comp (((E).toLinearMap.restrictScalars k).comp ((F).restrictScalars k))

private theorem exteriorReadout_v₀ : exteriorReadout k v₀ = (1,-DualNumber.eps) := by
  change coord (E (F v₀)) = _
  rw [exteriorMiddleQuotientEquiv_projected_generator, terminalQuotientCoordinates_incoming]

private theorem exteriorReadout_v₁ : exteriorReadout k v₁ = (0,1) := by
  change coord (E (F v₁)) = _
  rw [exteriorMiddleQuotientEquiv_projected_translate, terminalQuotientCoordinates_incoming_translate]

/-- The actual incoming label-two crossing embeds the exterior divided standard. -/
theorem labelTwoExteriorMiddleDifferential_injective : Function.Injective (E₁) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨a,b,hab⟩ := labelTwo_rightExteriorDividedStandard_span (parameter k) z
  have hspan : (z.val : start) = a • v₀ + b • v₁ := hab
  have hf : F z.val = 0 := hz
  have hzero : exteriorReadout k z.val = 0 := by
    change coord (E (F z.val)) = _
    rw [hf]
    exact (congrArg (coord) (E).map_zero).trans (coord).map_zero
  have huv : a • ((1,-DualNumber.eps) : DualNumber k × DualNumber k) +
      b • ((0,1) : DualNumber k × DualNumber k) = 0 := by
    let f := exteriorReadout k
    calc
      _ = a • f v₀ + b • f v₁ :=
        congrArg₂ (fun x y => a • x + b • y) (exteriorReadout_v₀ k).symm (exteriorReadout_v₁ k).symm
      _ = f (a • v₀ + b • v₁) :=
        (congrArg₂ (· + ·) (f.map_smul a v₀).symm (f.map_smul b v₁).symm).trans (f.map_add _ _).symm
      _ = f z.val := congrArg f hspan.symm
      _ = 0 := hzero
  obtain ⟨ha,hb⟩ := incoming_coordinates_coefficients_eq_zero huv
  apply Subtype.ext
  simpa only [ha, hb, zero_smul, add_zero, Submodule.coe_zero] using hspan

/-- The first map of the native label-two short complex is a monomorphism. -/
theorem labelTwoExteriorStandardComplex_mono_first :
    CategoryTheory.Mono (labelTwoExteriorStandardComplex (parameter k)).f :=
  (ModuleCat.mono_iff_injective _).mpr (labelTwoExteriorMiddleDifferential_injective k)

end
end Categorification.Stendhal.LabelTwo
