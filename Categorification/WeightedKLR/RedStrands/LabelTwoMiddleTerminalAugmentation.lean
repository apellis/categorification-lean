/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleExact

/-!
# Terminal coordinates of the label-two middle augmentation

Webster, arXiv:1309.3796v2, §8.2. At the terminal loading, the actual
dot-sum quotient has two independent copies of the middle specialization.
The two shuffle diagrams identify the corresponding components of the
quotient map with the two dual-number specializations.
-/


noncomputable section

set_option maxHeartbeats 2400000

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "S" => Standard k
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "Et" => seqIdem (parameter k) weights terminalLoading terminalLoading_ordered
local notation "W" => fixSub k S E
local notation "T" => fixSub k S Et
local notation "U" => LinearMap.range (diagramPlus k)
local notation "V" => fixSub k (StandardDotSumQuotient k) Et
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "J" => LinearEquiv.symm (terminalToTwoMiddle k)

/-- The inverse coordinates are the two terminal shuffles on the middle fixed vectors. -/
theorem terminalToTwoMiddle_symm_apply (z : W × W) :
    (J z).val = π (ψw [1]) • z.1.val + π (ψw [2, 1]) • z.2.val := rfl

private theorem terminalToTwoMiddle_plus (z : W × W) :
    diagramPlus k (J z).val = (J (fixedPlus k z.1, fixedPlus k z.2)).val := by
  let a : S := π (ψw [1]) • z.1.val
  let b : S := π (ψw [2, 1]) • z.2.val
  calc
    diagramPlus k (J z).val = diagramPlus k (a + b) :=
      congrArg (diagramPlus k) (terminalToTwoMiddle_symm_apply k z)
    _ = diagramPlus k a + diagramPlus k b := (diagramPlus k).map_add a b
    _ = π (ψw [1]) • (fixedPlus k z.1).val + π (ψw [2, 1]) • (fixedPlus k z.2).val :=
      congrArg₂ (· + ·) ((diagramPlus k).map_smul _ _) ((diagramPlus k).map_smul _ _)
    _ = (J (fixedPlus k z.1, fixedPlus k z.2)).val :=
      (terminalToTwoMiddle_symm_apply k (fixedPlus k z.1, fixedPlus k z.2)).symm

/-- The two augmentation coordinates at the terminal loading. -/
def terminalAugmentation : T →ₗ[k] DualNumber k × DualNumber k :=
  ((fixedAugmentation k).prodMap (fixedAugmentation k)).comp (terminalToTwoMiddle k).toLinearMap

private theorem terminalAugmentation_apply (z : W × W) :
    terminalAugmentation k (J z) = (fixedAugmentation k z.1, fixedAugmentation k z.2) := by
  change (fixedAugmentation k).prodMap (fixedAugmentation k) (terminalToTwoMiddle k (J z)) = _
  exact congrArg ((fixedAugmentation k).prodMap (fixedAugmentation k))
    ((terminalToTwoMiddle k).apply_symm_apply z)

private theorem terminalAugmentation_surjective :
    Function.Surjective (terminalAugmentation k) := by
  rintro ⟨x,y⟩
  obtain ⟨a,ha⟩ := fixedAugmentation_surjective k x
  obtain ⟨b,hb⟩ := fixedAugmentation_surjective k y
  refine ⟨J (a,b), (terminalAugmentation_apply k (a,b)).trans ?_⟩
  exact Prod.ext ha hb

/-- The map on the terminal fixed parts induced by the diagrammatic augmentation. -/
def terminalQuotientMap : T →ₗ[k] V where
  toFun z := ⟨(U).mkQ z.val, by
    change Et • (U).mkQ z.val = _
    rw [← map_smul, show Et • z.val = z.val from z.property]⟩
  map_add' x y := Subtype.ext ((U).mkQ.map_add x.val y.val)
  map_smul' c x := Subtype.ext (((U).mkQ.restrictScalars k).map_smul c x.val)

private theorem terminalQuotientMap_surjective :
    Function.Surjective (terminalQuotientMap k) := by
  intro z
  have hz : ∃ a : S, (U).mkQ a = z.val := (U).mkQ_surjective z.val
  obtain ⟨a, ha⟩ := hz
  let h : IsIdempotentElem Et := seqIdem_mul_self (parameter k) weights terminalLoading terminalLoading_ordered
  refine ⟨⟨Et • a, smul_mem_fixSub h a⟩, Subtype.ext ?_⟩
  change (U).mkQ (Et • a) = z.val
  rw [map_smul, ha]
  exact z.property

private theorem fixedAugmentation_zero_iff (z : W) :
    fixedAugmentation k z = 0 ↔ ∃ a, fixedPlus k a = z := by
  change z ∈ LinearMap.ker (fixedAugmentation k) ↔ z ∈ LinearMap.range (fixedPlus k)
  rw [fixedAugmentation_ker]

private theorem terminalQuotientMap_zero_iff (z : T) :
    terminalQuotientMap k z = 0 ↔ ∃ x : T, diagramPlus k x.val = z.val := by
  constructor
  · intro hz
    have h := congrArg Subtype.val hz
    change (U).mkQ z.val = 0 at h
    have hx' : ∃ x : S, diagramPlus k x = z.val := (Submodule.Quotient.mk_eq_zero U).mp h
    obtain ⟨x,hx⟩ := hx'
    let ht : IsIdempotentElem Et := seqIdem_mul_self (parameter k) weights terminalLoading terminalLoading_ordered
    refine ⟨⟨Et • x, smul_mem_fixSub ht x⟩, ?_⟩
    exact ((diagramPlus k).map_smul Et x).trans
      ((congrArg (fun s : S => Et • s) hx).trans z.property)
  · rintro ⟨x,hx⟩
    apply Subtype.ext
    change (U).mkQ z.val = 0
    exact (Submodule.Quotient.mk_eq_zero U).mpr ⟨x.val,hx⟩

private theorem terminalQuotient_coordinates_zero (a b : W) :
    terminalQuotientMap k (J (a,b)) = 0 ↔
      (fixedAugmentation k a, fixedAugmentation k b) = 0 := by
  rw [terminalQuotientMap_zero_iff]
  constructor
  · rintro ⟨x,hx⟩
    have hp : ∃ z : W × W, J z = x := (J).surjective x
    obtain ⟨⟨u,v⟩, huv⟩ := hp
    have h₁ : (J (fixedPlus k u, fixedPlus k v)).val = (J (a,b)).val :=
      (terminalToTwoMiddle_plus k (u,v)).symm.trans
        ((congrArg (fun y : T => diagramPlus k y.val) huv).trans hx)
    have h₂ : (fixedPlus k u, fixedPlus k v) = (a,b) :=
      (J).injective (Subtype.ext h₁)
    have ha : fixedAugmentation k a = 0 :=
      (fixedAugmentation_zero_iff k a).mpr ⟨u, congrArg Prod.fst h₂⟩
    have hb : fixedAugmentation k b = 0 :=
      (fixedAugmentation_zero_iff k b).mpr ⟨v, congrArg Prod.snd h₂⟩
    exact congrArg₂ Prod.mk ha hb
  · intro hz
    have ha : fixedAugmentation k a = 0 := congrArg Prod.fst hz
    have hb : fixedAugmentation k b = 0 := congrArg Prod.snd hz
    obtain ⟨u,hu⟩ := (fixedAugmentation_zero_iff k a).mp ha
    obtain ⟨v,hv⟩ := (fixedAugmentation_zero_iff k b).mp hb
    have hpair : (fixedPlus k u, fixedPlus k v) = (a,b) := congrArg₂ Prod.mk hu hv
    refine ⟨J (u,v), ?_⟩
    exact (terminalToTwoMiddle_plus k (u,v)).trans (congrArg (fun t : W × W => (J t).val) hpair)

private theorem terminalQuotientMap_ker :
    LinearMap.ker (terminalQuotientMap k) = LinearMap.ker (terminalAugmentation k) := by
  apply Submodule.ext
  intro z
  have hz : ∃ v : W × W, J v = z := (J).surjective z
  obtain ⟨⟨a,b⟩,rfl⟩ := hz
  change terminalQuotientMap k (J (a,b)) = 0 ↔ terminalAugmentation k (J (a,b)) = 0
  exact (terminalQuotient_coordinates_zero k a b).trans
    ((congrArg (fun v : DualNumber k × DualNumber k => v = 0)
      (terminalAugmentation_apply k (a,b))).symm.to_iff)

/-- At the terminal loading the actual dot-sum quotient specializes the two middle
shuffle coordinates to two copies of the dual-number algebra. -/
def terminalCutDotSumEquiv : V ≃ₗ[k] DualNumber k × DualNumber k :=
  (LinearMap.quotKerEquivOfSurjective (terminalQuotientMap k) (terminalQuotientMap_surjective k)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (terminalQuotientMap_ker k)).trans
      (LinearMap.quotKerEquivOfSurjective (terminalAugmentation k) (terminalAugmentation_surjective k)))


/-- The terminal quotient map specializes each of the two shuffle coordinates. -/
theorem terminalCutDotSumEquiv_apply (z : W × W) :
    terminalCutDotSumEquiv k (terminalQuotientMap k (J z)) =
      (fixedAugmentation k z.1, fixedAugmentation k z.2) := by
  simpa only [terminalCutDotSumEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk] using terminalAugmentation_apply k z

end Categorification.Stendhal.LabelTwo
