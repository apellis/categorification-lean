/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorDegrees
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleInjective
import Categorification.Algebra.Graded.Idempotent

/-!
# Grading of the label-two incoming exterior crossing

The grading on the divided right exterior standard is induced by its projected
cyclic generator. The actual incoming crossing raises degree by two, and
the relative shifts make both maps in the exact crossing sequence degree zero.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA Categorification.Graded DirectSum
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 ν
local notation "G" => labelTwoGradingDatum k
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "𝒜" => middleTensorGrade k (G)
local notation "πT" => stendhalTensorProjection (Q := parameter k) weights ν

theorem labelTwoLoadingIdempotent_mem_grade (s : Seq μ) (hs : IsRedOrdered s) :
    seqIdem (parameter k) weights s hs ∈ 𝒜 0 := by
  have h : πT (e s) = seqIdem (parameter k) weights s hs :=
    stendhalTensorProjection_e weights ν s hs
  exact h ▸ stendhalTensorProjection_mem_grade weights (G) ν ((G).e_mem_grade s)

theorem labelTwoLeftUpper_isHomogeneous (s : Seq μ) (hs : IsRedOrdered s) :
    (leftUpper (parameter k) weights s hs).IsHomogeneous 𝒜 := by
  intro i a ha
  suffices h : ∀ j, (decompose 𝒜 a j).val ∈ leftUpper (parameter k) weights s hs from h i
  clear i
  induction ha using Submodule.span_induction with
  | mem a ha =>
    intro i
    obtain ⟨t, ht, z, hst, rfl⟩ := ha
    have hₛ := labelTwoLoadingIdempotent_mem_grade k s hs
    have hₜ := labelTwoLoadingIdempotent_mem_grade k t ht
    refine Submodule.subset_span ⟨t, ht, (decompose 𝒜 z i).val, hst, ?_⟩
    have hr := coe_decompose_mul_add_of_right_mem 𝒜 (a := seqIdem (parameter k) weights t ht * z)
      (i := i) hₛ
    rw [add_zero] at hr
    have hl := decompose_smul_of_mem_zero (ℳ := 𝒜) hₜ z i
    exact hr.trans (congrArg (fun u : A => u * seqIdem (parameter k) weights s hs) hl)
  | zero =>
    intro i
    rw [decompose_zero, DirectSum.zero_apply]
    exact Submodule.zero_mem _
  | add a b ha hb hda hdb =>
    intro i
    rw [decompose_add, DirectSum.add_apply]
    exact Submodule.add_mem _ (hda i) (hdb i)
  | smul b a ha hda =>
    intro i
    induction b using Decomposition.inductionOn 𝒜 with
    | zero => rw [zero_smul, decompose_zero, DirectSum.zero_apply]; exact Submodule.zero_mem _
    | add c d hc hd =>
      rw [add_smul, decompose_add, DirectSum.add_apply]
      exact Submodule.add_mem _ hc hd
    | @homogeneous j b =>
      have h := coe_decompose_mul_add_of_left_mem 𝒜 (b := a) (j := i - j) b.2
      rw [show j + (i - j) = i by omega] at h
      exact h.symm ▸ Submodule.smul_mem _ b.1 (hda (i - j))

local notation "H" => KLRAlgebra k (stendhalQ (parameter k) weights) μ
private def terminal : Seq μ := labelTwoExteriorRightLoading
private theorem terminal_ordered : IsRedOrdered terminal := by
  unfold IsRedOrdered
  decide +kernel

local notation "S" => leftStandard (parameter k) weights terminal terminal_ordered
local notation "g" => leftStandardUnit (parameter k) weights terminal terminal_ordered
private abbrev divided : Submodule A S := labelTwoRightExteriorDividedStandard (parameter k)
local notation "P" => divided k
private def pword : H := (x (⟨2, by decide⟩ : Fin (Multiset.card μ)) : H) * ψ 2 * e terminal
private def p : A := πT (pword k)
private abbrev projection : Module.End A S := labelTwoRightExteriorProjection (parameter k)
private def u : P := (projection k).rangeRestrict g

private theorem u_val : (u k).val = p k • g :=
  labelTwoRightExteriorProjection_generator (parameter k)

private abbrev action : A →ₗ[A] P := LinearMap.toSpanSingleton A P (u k)

private theorem action_surjective : Function.Surjective (action k) := by
  intro v
  obtain ⟨z, hz⟩ := v.property
  obtain ⟨a, rfl⟩ := leftStandard_exists_smul_unit (Q := parameter k) (Λ := weights)
    terminal terminal_ordered z
  refine ⟨a, Subtype.ext ?_⟩
  change a • (u k).val = v.val
  exact ((projection k).map_smul a _).symm.trans hz

private theorem pr_grade : p k ∈ 𝒜 0 := by
  have hc : IsConstOn terminal 2 2 := by unfold IsConstOn; decide +kernel
  have h := blockIdem_mem_grade (G) (by decide : 2 + 2 ≤ Multiset.card μ) hc
  rw [blockIdem, blockElt_two (by decide : 2 + 1 < Multiset.card μ)] at h
  exact stendhalTensorProjection_mem_grade weights (G) ν h

private theorem action_eq_zero_iff (a : A) : action k a = 0 ↔
    (a * p k) * seqIdem (parameter k) weights terminal terminal_ordered ∈
      leftUpper (parameter k) weights terminal terminal_ordered := by
  rw [Subtype.ext_iff]
  change a • (u k).val = 0 ↔ _
  rw [u_val, ← mul_smul, leftStandardUnit, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  rfl

/-- The natural grading of the right divided exterior standard, with its projected generator
in degree zero. -/
def labelTwoRightExteriorGrade : ℤ → Submodule k P :=
  Graded.map 𝒜 ((action k).restrictScalars k)

@[instance_reducible] def labelTwoRightExteriorDecomposition :
    Decomposition (labelTwoRightExteriorGrade k) := by
  apply Graded.mapDecomposition (π := (action k).restrictScalars k) (action_surjective k)
  intro a ha i
  change action k a = 0 at ha
  change action k _ = 0
  rw [action_eq_zero_iff] at ha ⊢
  have h := labelTwoLeftUpper_isHomogeneous k terminal terminal_ordered i ha
  have he := coe_decompose_mul_add_of_right_mem 𝒜 (i := i) (a := a * p k)
    (labelTwoLoadingIdempotent_mem_grade k terminal terminal_ordered)
  have hp := coe_decompose_mul_add_of_right_mem 𝒜 (i := i) (a := a) (pr_grade k)
  rw [Int.add_zero] at he hp
  rwa [he, hp] at h

instance labelTwoRightExterior_gradedSMul :
    SetLike.GradedSMul 𝒜 (labelTwoRightExteriorGrade k) :=
  Graded.gradedSMul_map 𝒜 (fun a b => (action k).map_smul a b)

local notation "V" => StandardDotSumQuotient k
local notation "T" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "F" => labelTwoExteriorMiddleDifferential (parameter k)
local notation "E" => exteriorMiddleQuotientEquiv k

set_option maxHeartbeats 850000 in
/-- The incoming crossing written in the common middle quotient. -/
def normalizedIncoming : P →ₗ[A] V where
  toFun z := E (F z)
  map_add' x y := (congrArg (fun v => E v) ((F).map_add x y)).trans ((E).map_add _ _)
  map_smul' a x := (congrArg (fun v => E v) ((F).map_smul (a : T) x)).trans ((E).map_smul a _)

set_option maxHeartbeats 850000 in
private theorem incoming_generator_mem_grade :
    normalizedIncoming k (u k) ∈ labelTwoMiddleQuotientGrade k 2 := by
  have h₀ := congrArg (fun v => E (labelTwoExteriorToMiddle (parameter k) v)) (u_val k)
  have h := h₀.trans (exteriorMiddleQuotientEquiv_projected_generator k)
  refine Submodule.mem_map.mpr ⟨_, ?_, h.symm⟩
  rw [incomingDiagram_val]
  exact incomingExteriorDiagram_mem_grade k

/-- The incoming crossing between the actual divided standard and the actual middle quotient
has internal degree two. -/
theorem labelTwoIncoming_degree_two :
    normalizedIncoming k ∈ homGrade A (labelTwoRightExteriorGrade k)
      (labelTwoMiddleQuotientGrade k) 2 := by
  intro i z hz
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  change normalizedIncoming k (a • u k) ∈ _
  rw [map_smul]
  exact (labelTwoMiddleQuotient_gradedSMul k).smul_mem ha (incoming_generator_mem_grade k)

local notation "𝓡" => labelTwoRightExteriorGrade k
local notation "𝓠" => labelTwoMiddleQuotientGrade k
local notation "𝓟" => labelTwoLeftExteriorGrade k

/-- The normalized first map is injective. -/
theorem labelTwoNormalizedIncoming_injective :
    Function.Injective (normalizedIncoming k) :=
  (exteriorMiddleQuotientEquiv k).injective.comp
    (labelTwoExteriorMiddleDifferential_injective k)

/-- Middle exactness is preserved by the common quotient comparison. -/
theorem labelTwoNormalizedCrossings_exact :
    Function.Exact (normalizedIncoming k) (normalizedOutgoing k) := by
  intro z
  constructor
  · intro hz
    obtain ⟨u,hu⟩ := (labelTwoExteriorMiddle_exact k ((E).symm z)).mp hz
    exact ⟨u, (congrArg (fun y => E y) hu).trans ((E).apply_symm_apply z)⟩
  · rintro ⟨u,rfl⟩
    change labelTwoMiddleExteriorDifferential (parameter k) ((E).symm (E (F u))) = 0
    exact (congrArg (labelTwoMiddleExteriorDifferential (parameter k))
      ((E).symm_apply_apply (F u))).trans
      ((labelTwoExteriorMiddle_exact k (F u)).mpr ⟨u,rfl⟩)

/-- With the normalized exterior and middle shifts, the incoming crossing preserves degree. -/
theorem labelTwoShiftedIncoming_preservesGrading :
    PreservesGrading (Graded.shift 𝓡 3) (Graded.shift 𝓠 1) (normalizedIncoming k) := by
  intro i z hz
  change z ∈ 𝓡 (i - 3) at hz
  change normalizedIncoming k z ∈ 𝓠 (i - 1)
  rw [show i - 1 = (i - 3) + 2 by omega]
  exact mem_homGrade.mp (labelTwoIncoming_degree_two k) hz

/-- With the normalized middle and exterior shifts, the outgoing crossing preserves degree. -/
theorem labelTwoShiftedOutgoing_preservesGrading :
    PreservesGrading (Graded.shift 𝓠 1) (Graded.shift 𝓟 (-1)) (normalizedOutgoing k) := by
  intro i z hz
  change z ∈ 𝓠 (i - 1) at hz
  change normalizedOutgoing k z ∈ 𝓟 (i - (-1))
  rw [show i - (-1) = (i - 1) + 2 by omega]
  exact mem_homGrade.mp (labelTwoOutgoing_degree_two k) hz

end
end Categorification.Stendhal.LabelTwo
