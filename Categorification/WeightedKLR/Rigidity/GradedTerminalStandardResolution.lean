/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedMiddleComplex
import Categorification.WeightedKLR.Rigidity.WeightModuleExactTriangle
import Categorification.WeightedKLR.RedStrands.StandardModule
import DG.Category.Resolution.KProjective

/-!
# Graded higher-loading resolution in the fundamental terminal cut

Webster, arXiv:1309.3796v2, Lemma 6.11 (p. 65).
For two fundamental reds and one black in type A₁, the terminal loading
standard has a homogeneous two-term projective resolution. Its only
positive chain degree uses the strictly higher middle loading.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG CatModule MulOpposite StendhalAlgebraAllOrders
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "𝒜" => tensorProductGrade grading ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading (Graded.oppositeGrade 𝒜)
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing (Graded.oppositeGrade 𝒜)
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

open KLR DirectSum

local notation "Fχ" => WeightCategory.mapFunctor gradedTerminalCharacter gradedTerminalCharacter_mem_weight

/-- The unshifted terminal standard in the fundamental weight block, presented by its
coefficient character. -/
def gradedTerminalStandard : CatModule.{0} (WeightCategory Tᵐᵒᵖ) :=
  (CatModule.precomp Fχ).obj (CatModule.representable (⟨0⟩ : WeightCategory ℚ))

private theorem middleOrdered : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
local notation "P₀" => shiftedLoadingModule terminal terminal_ordered 0
local notation "P₁" => shiftedLoadingModule middle middleOrdered 1

/-- The positive term is the middle loading projective at internal generating
weight one, and the differential preserves internal weight. -/
def gradedTerminalStandardD₁ : P₁ ⟶ P₀ :=
  loadingMap fundamentalResolutionMap (fun n x hx => by
    have h := (middleResolution_maps_degree (n+1)).1 x
    simpa only [show n + 1 - 2 = n - 1 by omega, add_sub_cancel_right, sub_zero] using h (by simpa only [show n + 1 - 2 = n - 1 by omega] using hx))

private theorem scalar_mem_grading {n : ℤ} {k : WeightCategory Tᵐᵒᵖ} (x : gradedTerminalStandard.obj k) :
    x ∈ DG.grading n ↔ n = 0 ∨ x = 0 := by
  change x.val ∈ DG.grading n ↔ _
  rw [InDegreeZero.ring_mem_grading_iff]
  exact ⟨Or.imp_right (fun h => Subtype.ext h), Or.imp_right (fun h => h ▸ rfl)⟩

private theorem scalar_d {k : WeightCategory Tᵐᵒᵖ} (x : gradedTerminalStandard.obj k) :
    d x = 0 := Subtype.ext (InDegreeZero.ring_d_apply x.val)

/-- The homogeneous augmentation by the character at the terminal cut. -/
def gradedTerminalStandardAugmentation : P₀ ⟶ gradedTerminalStandard where
  app k := {
    toFun := fun x => ⟨terminalCharacter (loadingValue x).val, by
      have h := gradedTerminalCharacter_mem_weight x.val.property
      change terminalCharacter x.val.val.unop ∈ DG.wgrading (M := ℚ) (k.as - 0)
      exact h⟩
    map_zero' := Subtype.ext (map_zero terminalCharacter)
    map_add' := fun x y => Subtype.ext (map_add terminalCharacter (loadingValue x).val (loadingValue y).val) }
  map_mem' {k n x} hx := by
    apply (scalar_mem_grading _).mpr
    rcases (loading_mem_grading x).mp hx with h | rfl
    · exact Or.inl h
    · exact Or.inr (Subtype.ext (map_zero terminalCharacter))
  map_d' x := by rw [loading_d x, scalar_d]; exact Subtype.ext (map_zero terminalCharacter)
  map_smul' g x := Subtype.ext ((map_mul terminalCharacter (loadingValue x).val g.val.unop).trans (mul_comm _ _))


/-- The mixed crossing followed by the terminal quotient is short exact at
each internal weight. -/
theorem gradedTerminalStandard_exact (k : WeightCategory Tᵐᵒᵖ) :
    Function.Injective (gradedTerminalStandardD₁.app k) ∧
    Function.Exact (gradedTerminalStandardD₁.app k) (gradedTerminalStandardAugmentation.app k) ∧
    Function.Surjective (gradedTerminalStandardAugmentation.app k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    apply loadingExt
    apply congrArg Subtype.val
    apply fundamentalResolutionMap_injective
    exact Subtype.ext (congrArg (fun z => (loadingValue z).val) h)
  · intro x
    have hxdeg : (loadingValue x).val ∈ 𝒜 k.as := by simpa only [sub_zero] using loadingValue_degree x
    have ex : terminalCharacter (loadingValue x).val = 0 ↔
        loadingValue x ∈ LinearMap.range fundamentalResolutionMap := by
      rw [fundamentalResolutionMap_range, mem_fundamentalCutTrace_iff]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := ex.mp (congrArg Subtype.val hx)
      obtain ⟨hq, _, hc, _⟩ := fundamental_loading_crossing_degrees
      obtain ⟨z, hz, hzx⟩ := homogeneous_crossing_preimage hq hc hxdeg
        (show 1 + (k.as - 1) = k.as by omega) y (congrArg Subtype.val hy)
      exact ⟨loadingElement z hz, loadingExt hzx⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (ex.mpr ⟨loadingValue y, rfl⟩)
  · intro z
    have hz : k.as = 0 ∨ z.val = 0 := by
      have h : z.val ∈ DG.grading (k.as - 0) := z.property
      simpa only [sub_zero, InDegreeZero.ring_mem_grading_iff] using h
    rcases hz with h | h
    · obtain ⟨_, hp, _, _⟩ := fundamental_loading_crossing_degrees
      have hpidem : IsIdempotentElem terminalIdem :=
        IsIdempotentElem.map (by simp [IsIdempotentElem, e_mul_e]) project
      let y : rIdeal terminalIdem := ⟨z.val • terminalIdem, by
        change terminalIdem * (z.val • terminalIdem) = _
        rw [mul_smul_comm, hpidem.eq]⟩
      have hy : y.val ∈ 𝒜 (k.as - 0) := by rw [h, sub_zero]; exact Submodule.smul_mem _ _ hp
      refine ⟨loadingElement y hy, Subtype.ext ?_⟩
      change terminalCharacter (z.val • terminalIdem) = z.val
      rw [map_smul, terminalCharacter_terminalIdem, smul_eq_mul, mul_one]
    · refine ⟨0, ?_⟩
      rw [map_zero]
      apply Subtype.ext
      change (0 : ℚ) = z.val
      exact h.symm

/-- In Webster's loading order the only positive term of the terminal
standard resolution uses a strictly higher loading. -/
theorem terminal_lt_middle : StendhalLT terminal middle := by
  constructor
  · intro r i
    fin_cases r <;> cases i <;> decide +kernel
  · intro h
    exact (by decide +kernel : ¬blackCount middle 1 () ≤ blackCount terminal 1 ()) (h 1 ())

/-- The terminal mixed-crossing kernel is the standard-stratification trace
of all strictly higher loadings. The other ordered loading with higher
black counts is globally violated. -/
theorem fundamentalTerminal_higherTrace :
    coevaluationTrace (e := terminalIdem)
      (fun t : {t : Seq μ // IsRedOrdered t ∧ StendhalLT terminal t} => project (e t.val)) =
      fundamentalCutTrace := by
  have classify : ∀ t : Seq μ, IsRedOrdered t → ¬ IsViolated t → t = terminal ∨ t = middle := by
    intro t ht hv
    obtain ⟨r, hr⟩ := (FirstWeight.boundaryEquiv () 2).surjective ⟨t, ht, hv⟩
    have hr' : (FirstWeight.boundaryAt () 2 r).val = t := congrArg Subtype.val hr
    fin_cases r
    · exact Or.inr (hr'.symm.trans (by apply Subtype.ext; funext j; fin_cases j <;> rfl))
    · exact Or.inl (hr'.symm.trans (by apply Subtype.ext; funext j; fin_cases j <;> rfl))
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨s, hs, hlt⟩, hx⟩
    change x.val * project (e s) = x.val at hx
    by_cases hv : IsViolated s
    · have hz : project (e s) = 0 := by
        change (StendhalAlgebra.violatedIdeal ℚ Q wt ({()} : Multiset Unit)).ringCon.mk'
          (orderProjection Q wt ({()} : Multiset Unit) (e s)) = 0
        rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
        refine TwoSidedIdeal.subset_span ⟨s, hs, hv, Subtype.ext ?_⟩
        exact (e_mul_redOrderedIdem s).trans (ite_eq_left hs)
      rw [hz, mul_zero] at hx
      rw [show x = 0 from Subtype.ext hx.symm]
      exact Submodule.zero_mem _
    · rcases classify s hs hv with rfl | rfl
      · exact (hlt.2 (fun _ _ => le_rfl)).elim
      · exact Submodule.subset_span ⟨(), hx⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨_, hx⟩
    exact Submodule.subset_span ⟨⟨middle, middleOrdered, terminal_lt_middle⟩, hx⟩

private theorem gradedTerminalStandard_comp :
    gradedTerminalStandardD₁ ≫ gradedTerminalStandardAugmentation = 0 :=
  CatModule.hom_ext fun k x => ((gradedTerminalStandard_exact k).2.1 _).mpr ⟨x, rfl⟩

/-- A literal K-projective two-term complex for the terminal standard, with
the middle projective as its only term in cohomological degree -1. -/
abbrev gradedTerminalStandardResolution := cone gradedTerminalStandardD₁

/-- Each negative cohomological component is literally the shifted higher
loading, with all degrees below minus one zero. -/
theorem gradedTerminalStandardResolution_negative_component
    (X : WeightCategory Tᵐᵒᵖ) {n : ℤ} (hn : n < 0)
    (x : gradedTerminalStandardResolution.obj X) (hx : x ∈ DG.grading n) :
    ∃ y : (P₁).obj X,
      x = (show gradedTerminalStandardResolution.obj X from (shift.mk 1 y, 0)) ∧
      (n = -1 ∨ y = 0) := by
  change x.1 ∈ DG.grading n ∧ x.2 ∈ DG.grading n at hx
  have h₀ := ((loading_mem_grading x.2).mp hx.2).resolve_left (by omega)
  have h₁ := (loading_mem_grading (shift.unmk 1 x.1)).mp (shift.unmk_mem_grading hx.1)
  refine ⟨shift.unmk 1 x.1, Prod.ext ?_ h₀, h₁.imp_left (fun h => by omega)⟩
  simp

def gradedTerminalStandardResolutionAugmentation :
    gradedTerminalStandardResolution ⟶ gradedTerminalStandard :=
  coneDescent gradedTerminalStandardD₁ gradedTerminalStandardAugmentation gradedTerminalStandard_comp

theorem gradedTerminalStandardResolution_isKProjective :
    IsKProjective gradedTerminalStandardResolution :=
  IsKProjective.cone (isKProjective_corner (gradedLoadingIdempotentAt middle middleOrdered 1))
    (isKProjective_corner (gradedLoadingIdempotentAt terminal terminal_ordered 0))

theorem gradedTerminalStandardResolution_quasiIso :
    IsQuasiIso gradedTerminalStandardResolutionAugmentation :=
  coneDescent_quasiIso _ _ gradedTerminalStandard_comp
    (fun k => (gradedTerminalStandard_exact k).1)
    (fun k => (gradedTerminalStandard_exact k).2.1)
    (fun k => (gradedTerminalStandard_exact k).2.2)

end Categorification.Stendhal.FundamentalCorner
