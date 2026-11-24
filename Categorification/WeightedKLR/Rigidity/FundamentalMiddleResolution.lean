/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleHead

/-!
# The mixed-crossing projective resolution at the middle cut

Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3 and Proposition 7.8,
in the fundamental two-red type A₁ block over the rationals. The two mixed
crossings give a length-two projective resolution of the simple at cut
(0,1). Its first syzygy is the simple at the cut (0,0).
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory MulOpposite StendhalAlgebraAllOrders
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "q" => middleIdem
local notation "p" => terminalIdem
local notation "C" => project (ψ 1)
local notation "u" => C * q
local notation "v" => C * p

private theorem p_idem : IsIdempotentElem p :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, e_mul_e]) project
private theorem q_idem : IsIdempotentElem q :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, e_mul_e]) project

/-- Left multiplication by the mixed crossing from the terminal projective to the middle projective. -/
def terminalToMiddle : rIdeal p →ₗ[Tᵐᵒᵖ] rIdeal q where
  toFun x := ⟨v * x.val, by
    change q * (v * x.val) = v * x.val
    rw [← mul_assoc, terminalCrossing_eq_middle_mul, ← mul_assoc q q, q_idem.eq]⟩
  map_add' x y := Subtype.ext (mul_add v x.val y.val)
  map_smul' a x := Subtype.ext (mul_assoc v x.val a.unop).symm

private theorem reverse_bigon : v * u = 0 := by
  let x := terminalToMiddle (fundamentalResolutionMap (⟨q, q_idem.eq⟩ : rIdeal q))
  have h : x.val = v * u := by
    change v * (u * q) = v * u
    rw [mul_assoc C q q, q_idem.eq]
  have hx := middle_mul_middle x
  rw [h, mul_assoc v u q, mul_assoc C q q, q_idem.eq] at hx
  rw [hx, map_mul, map_mul, middleCharacter_terminalIdem, mul_zero, zero_mul, zero_smul]

/-- The two crossings compose to zero on the middle projective. -/
theorem terminalToMiddle_comp : terminalToMiddle.comp fundamentalResolutionMap = 0 := by
  ext x
  change v * (u * x.val) = 0
  rw [← mul_assoc, reverse_bigon, zero_mul]

theorem terminalToMiddle_range : LinearMap.range terminalToMiddle = middleCutTrace := by
  ext x
  rw [mem_middleCutTrace_iff]
  constructor
  · rintro ⟨y, rfl⟩
    change middleCharacter (v * y.val) = 0
    rw [map_mul, map_mul, middleCharacter_terminalIdem, mul_zero, zero_mul]
  · intro hx
    obtain ⟨c, hc⟩ := (fundamental_middle_corner_coordinates x.val).2.2
    change q * x.val * p = c • v at hc
    rw [x.property] at hc
    have hq : x.val * q = 0 := by rw [middle_mul_middle, hx, zero_smul]
    refine ⟨c • (⟨p, p_idem.eq⟩ : rIdeal p), Subtype.ext ?_⟩
    change v * (c • p) = x.val
    rw [mul_smul_comm, mul_assoc C p p, p_idem.eq, ← hc]
    calc
      x.val * p = x.val * p + x.val * q := by rw [hq, add_zero]
      _ = x.val := by rw [← mul_add, terminalIdem_add_middleIdem, mul_one]

theorem terminalToMiddle_ker : LinearMap.ker terminalToMiddle = fundamentalCutTrace := by
  apply le_antisymm
  · intro x hx
    apply (mem_fundamentalCutTrace_iff _).mpr
    by_contra h
    obtain ⟨b, hb⟩ := exists_mul_eq_terminalIdem x h
    have hx' : v * x.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hv : v = 0 := by
      have hprod : v * p = 0 := by
        calc
          v * p = v * (x.val * b) := congrArg (v * ·) hb.symm
          _ = 0 := by rw [← mul_assoc, hx', zero_mul]
      rwa [mul_assoc C p p, p_idem.eq] at hprod
    exact dot_ne_zero (by rw [← mixedBigon_terminal, hv, mul_zero])
  · rw [← fundamentalResolutionMap_range]
    exact LinearMap.range_le_ker_iff.mpr terminalToMiddle_comp

/-- The first syzygy at the middle cut is the one-dimensional terminal character. -/
def terminalSimpleEquivMiddleTrace :
    (rIdeal p ⧸ fundamentalCutTrace) ≃ₗ[Tᵐᵒᵖ] middleCutTrace :=
  (Submodule.quotEquivOfEq _ _ terminalToMiddle_ker.symm).trans
    (terminalToMiddle.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ terminalToMiddle_range))

/-- The short exact sequence which splices with the terminal resolution. -/
def middleTraceSequence : ShortComplex (ModuleCat.{0} Tᵐᵒᵖ) :=
  ShortComplex.mk (ModuleCat.ofHom (middleCutTrace.subtype.comp terminalSimpleEquivMiddleTrace.toLinearMap))
    (ModuleCat.ofHom middleCutTrace.mkQ) (by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).mpr (terminalSimpleEquivMiddleTrace x).property)

theorem middleTraceSequence_shortExact : middleTraceSequence.ShortExact := by
  let : Mono middleTraceSequence.f := (ModuleCat.mono_iff_injective _).2
    (Subtype.val_injective.comp terminalSimpleEquivMiddleTrace.injective)
  let : Epi middleTraceSequence.g := (ModuleCat.epi_iff_surjective _).2 middleCutTrace.mkQ_surjective
  have ex : Function.Exact (middleCutTrace.subtype.comp terminalSimpleEquivMiddleTrace.toLinearMap)
      middleCutTrace.mkQ := by
    intro x
    change (Submodule.Quotient.mk x : rIdeal q ⧸ middleCutTrace) = 0 ↔
      ∃ z, (terminalSimpleEquivMiddleTrace z).val = x
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hx => ⟨terminalSimpleEquivMiddleTrace.symm ⟨x,hx⟩,
      congrArg Subtype.val (terminalSimpleEquivMiddleTrace.apply_symm_apply ⟨x,hx⟩)⟩,
      fun ⟨z,hz⟩ => hz ▸ (terminalSimpleEquivMiddleTrace z).property⟩
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 ex⟩

/-- The projective resolution in homological degrees 2, 1 and 0 is the middle,
terminal and middle loading projectives, with the two mixed crossings as differentials. -/
theorem middleProjectiveResolution :
    Module.Projective Tᵐᵒᵖ (rIdeal q) ∧ Module.Projective Tᵐᵒᵖ (rIdeal p) ∧
      Function.Injective fundamentalResolutionMap ∧ Function.Exact fundamentalResolutionMap terminalToMiddle ∧
      Function.Exact terminalToMiddle middleCutTrace.mkQ ∧ Function.Surjective middleCutTrace.mkQ := by
  refine ⟨rIdeal_projective q_idem, rIdeal_projective p_idem, fundamentalResolutionMap_injective,
    LinearMap.exact_iff.mpr ?_, LinearMap.exact_iff.mpr ?_, middleCutTrace.mkQ_surjective⟩
  · rw [fundamentalResolutionMap_range, terminalToMiddle_ker]
  · rw [terminalToMiddle_range, Submodule.ker_mkQ]

end Categorification.Stendhal.FundamentalCorner
