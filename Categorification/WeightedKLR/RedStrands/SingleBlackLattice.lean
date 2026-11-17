/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlack
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightIntegral

/-!
# The first lowering block of Webster's integral tensor product

B. Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38. For one red factor, the
regular projective in the first lowering block corresponds to `Fᵢ v_λ`
in the weight component of the integral highest-weight lattice.

Webster uses `[P(a)] = q^a[P]` for `P(a)ₙ = Pₙ₊ₐ` (§1.2). With the repository
shift `P{a}ₙ = Pₙ₋ₐ`, the comparison is semilinear for Laurent inversion.
-/

noncomputable section

namespace Categorification.Stendhal.SingleBlack

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open LieLean.QuantumGroup.Sl2.RankOne LusztigF Categorification.Graded

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "LP" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} (highest : Dom R) (i : I)

local notation "V" => IrreducibleModule R 𝕍 (Subtype.val highest)
local notation "vλ" => IrreducibleModule.hwv R 𝕍 (Subtype.val highest)
local notation "fλ" => F R 𝕍 i • vλ
local notation "μ" => Subtype.val highest - R.root i

/-- The `λ − αᵢ` component of the divided-power integral lattice `V^ℤ_λ`. -/
def firstLoweringLattice : Submodule LP V where
  carrier := {m | m ∈ hwIntegral highest ∧ m ∈ weightSpace R 𝕍 V μ}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  smul_mem' a _ hm := ⟨Submodule.smul_mem _ a hm.1, by
    rw [hw_laurent_smul_eq]
    exact Submodule.smul_mem _ _ hm.2⟩

omit [Finite I] in
private theorem qDivPow_one (q : RatFunc ℚ) (x : QuantumGroup R 𝕍) :
    qDivPow q 1 x = x := by simp [qDivPow, qFactorial, qInt]

/-- The first lowering of the highest vector lies in its integral weight component. -/
theorem lower_mem_lattice : fλ ∈ firstLoweringLattice highest i := by
  refine ⟨?_, F_smul_mem_weightSpace IrreducibleModule.hwv_mem_weightSpace i⟩
  simpa only [qDivPow_one] using
    dF_smul_mem_hwIntegral highest i 1 (hwv_mem_hwIntegral highest)

private theorem evq_divPow_mul (j : I) (n : ℕ) (y : LusztigF.Quotient D 𝕍) :
    evq hvt highest ((negativeQuotientEquiv D).symm (quotientIntegralGenerator D j n * y)) =
      qDivPow (𝕍 ^ D.d j) n (F R 𝕍 j) • evq hvt highest ((negativeQuotientEquiv D).symm y) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕍 y
  rw [← toQuotient_qDivPow, ← map_mul, symm_toQuotient, symm_toQuotient, evq_mk, evq_mk,
    ev_qDivPow_mul]

private theorem eval_product_at_single {y : LusztigF.Quotient D 𝕍}
    (hy : y ∈ Submonoid.closure {u | ∃ j n, u = quotientIntegralGenerator D j n}) :
    ∃ ν : I →₀ ℕ,
      let m : V := evq hvt highest ((negativeQuotientEquiv D).symm y)
      m ∈ wsp highest ν ∧ (ν = 0 → m = vλ) ∧ (ν = Finsupp.single i 1 → m = fλ) := by
  induction hy using Submonoid.closure_induction_left with
  | one =>
    refine ⟨0, ?_⟩
    dsimp only
    rw [← map_one (toQuotient D 𝕍), symm_toQuotient, evq_mk, ev_one]
    refine ⟨hwv_mem_wsp highest, fun _ => rfl, fun h => ?_⟩
    have h' := congrArg (fun ν : I →₀ ℕ => ν i) h
    simp at h'
  | mul_left x hx y _ ih =>
    obtain ⟨j, n, rfl⟩ := hx
    obtain ⟨ν, hν, h₀, h₁⟩ := ih
    refine ⟨Finsupp.single j n + ν, ?_⟩
    dsimp only
    rw [evq_divPow_mul]
    refine ⟨?_, ?_, ?_⟩
    · change _ ∈ weightSpace R 𝕍 V (highest.1 - R.rootSum (Finsupp.single j n + ν))
      rw [R.rootSum_add, R.rootSum_single, add_comm (n • R.root j), ← sub_sub]
      rw [qDivPow, smul_assoc]
      refine Submodule.smul_mem _ _ ?_
      induction n with
      | zero => simpa using hν
      | succ n ih =>
        rw [pow_succ', mul_smul, succ_nsmul, sub_add_eq_sub_sub]
        exact F_smul_mem_weightSpace ih j
    · intro h
      have h' := congrArg (fun ν : I →₀ ℕ => ν j) h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at h'
      have hn : n = 0 := by omega
      subst n
      simp only [Finsupp.single_zero, zero_add] at h
      rw [qDivPow_zero', one_smul]
      exact h₀ h
    · intro h
      cases n with
      | zero =>
        simp only [Finsupp.single_zero, zero_add] at h
        rw [qDivPow_zero', one_smul]
        exact h₁ h
      | succ n =>
        have h' := congrArg (fun ν : I →₀ ℕ => ν j) h
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h'
        have hji : j = i := by
          by_contra hne
          rw [Finsupp.single_eq_of_ne hne] at h'
          omega
        subst j
        rw [Finsupp.single_eq_same] at h'
        have hn : n = 0 := by omega
        subst n
        have hv : ν = 0 := add_left_cancel (h.trans (add_zero _).symm)
        rw [qDivPow_one, h₀ hv]

private theorem map_hwIntegral_mem_of_generators (P : Module.End (RatFunc ℚ) V) (W : Submodule LP V)
    (hgen : ∀ y ∈ Submonoid.closure {u | ∃ j n, u = quotientIntegralGenerator D j n},
      P (evq hvt highest ((negativeQuotientEquiv D).symm y)) ∈ W)
    {m : V} (hm : m ∈ hwIntegral highest) : P m ∈ W := by
  obtain ⟨x, hx, rfl⟩ := hm
  replace hx : negativeQuotientEquiv D x ∈ Subalgebra.toSubmodule (quotientIntegralForm D) :=
    (mem_negIntegral D x).1 hx
  rw [quotientIntegralForm, Algebra.adjoin_eq_span] at hx
  rw [← (negativeQuotientEquiv D).symm_apply_apply x]
  generalize negativeQuotientEquiv D x = y at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add _ _ _ _ hx hy =>
    rw [map_add, map_add, map_add]
    exact add_mem hx hy
  | smul a y _ hy =>
    change P (evq hvt highest ((negativeQuotientEquiv D).symm (integralLaurentEval a • y))) ∈ _
    rw [map_smul, map_smul, map_smul, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ a hy

private theorem hwIntegral_weight_mem_span (hR : R.IsXRegular) (ν₀ : I →₀ ℕ) (b : V)
    (hgen : ∀ y ∈ Submonoid.closure {u | ∃ j n, u = quotientIntegralGenerator D j n},
      ∃ ν : I →₀ ℕ, let m : V := evq hvt highest ((negativeQuotientEquiv D).symm y)
        m ∈ wsp highest ν ∧ (ν = ν₀ → m = b))
    {m : V} (hm : m ∈ hwIntegral highest) (hw : m ∈ wsp highest ν₀) :
    m ∈ Submodule.span LP {b} := by
  classical
  let P : Module.End (RatFunc ℚ) V :=
    weightSetProj hvn_ratFunc (isInt hvt hR highest) {highest.1 - R.rootSum ν₀}
  have hPm : P m = m := by
    change weightSetProj hvn_ratFunc (isInt hvt hR highest) _ m = m
    rw [weightSetProj_of_mem hvn_ratFunc (isInt hvt hR highest) _ hw]
    simp
  rw [← hPm]
  refine map_hwIntegral_mem_of_generators highest P _ (fun y hy => ?_) hm
  obtain ⟨ν, hν, hs⟩ := hgen y hy
  have hν' : highest.1 - R.rootSum ν = highest.1 - R.rootSum ν₀ ↔ ν = ν₀ :=
    ⟨fun h => LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h),
      fun h => congrArg (fun a => highest.1 - R.rootSum a) h⟩
  change weightSetProj hvn_ratFunc (isInt hvt hR highest) _
    (evq hvt highest ((negativeQuotientEquiv D).symm y)) ∈ _
  rw [weightSetProj_of_mem hvn_ratFunc (isInt hvt hR highest) _ hν, Set.mem_singleton_iff, hν']
  by_cases h : ν = ν₀
  · rw [ite_eq_left h, hs h]
    exact Submodule.mem_span_singleton_self _
  · rw [ite_eq_right h]
    exact zero_mem _

/-- In depth one the integral lattice is spanned by the Chevalley lowering of the
highest vector, as used in the one-factor case of Webster's Theorem 4.38. -/
theorem lattice_le_span (hR : R.IsXRegular) :
    firstLoweringLattice highest i ≤ Submodule.span LP {fλ} := by
  rintro m ⟨hm, hw⟩
  refine hwIntegral_weight_mem_span highest hR (Finsupp.single i 1) fλ (fun y hy => ?_) hm
    (by simpa only [wsp, R.rootSum_single, one_smul] using hw)
  obtain ⟨ν, hν, _, h₁⟩ := eval_product_at_single highest i hy
  exact ⟨ν, hν, h₁⟩

/-- The highest weight component of the integral lattice is generated by the
highest vector, the generator used in the recursion preceding Webster's Lemma 4.36. -/
theorem hwIntegral_weight_zero_mem_span (hR : R.IsXRegular) {m : V}
    (hm : m ∈ hwIntegral highest) (hw : m ∈ wsp highest 0) :
    m ∈ Submodule.span LP {vλ} := by
  by_cases hI : Nonempty I
  · refine hwIntegral_weight_mem_span highest hR 0 vλ (fun y hy => ?_) hm hw
    obtain ⟨ν, hν, h₀, _⟩ := eval_product_at_single highest (Classical.choice hI) hy
    exact ⟨ν, hν, h₀⟩
  · let := not_nonempty_iff.mp hI
    refine hwIntegral_weight_mem_span highest hR 0 vλ (fun y hy => ?_) hm hw
    have hy₁ : y = 1 := by
      have hempty : {u : LusztigF.Quotient D 𝕍 | ∃ j n, u = quotientIntegralGenerator D j n} =
          ∅ := by ext u; simp
      rwa [hempty, Submonoid.closure_empty, Submonoid.mem_bot] at hy
    subst y
    refine ⟨0, ?_⟩
    dsimp only
    rw [← map_one (toQuotient D 𝕍), symm_toQuotient, evq_mk, ev_one]
    exact ⟨hwv_mem_wsp highest, fun _ => rfl⟩

/-- The homogeneous vectors of the divided-power integral lattice span it. -/
theorem hwIntegral_le_span_homogeneous (hR : R.IsXRegular) :
    hwIntegral highest ≤ Submodule.span LP {m : V | ∃ ν : I →₀ ℕ,
      m ∈ wsp highest ν ∧ m ∈ hwIntegral highest} := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := hm
  have h := negIntegral_le_span D hx
  clear hx
  induction h using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨ν, y, hy, rfl, hz⟩ := hz
    apply Submodule.subset_span
    refine ⟨ν, ?_, ⟨_, hz, rfl⟩⟩
    rw [evq_mk]
    exact ev_mem_weightSpace hvn_ratFunc hR highest.1 hy
  | zero => simp
  | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a z _ hz =>
    rw [laurent_smul_eq, map_smul, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ a hz

omit [Finite I] in
/-- Positive coroot multiplicity makes the first lowering vector nonzero. -/
theorem lower_ne_zero (hR : R.IsXRegular) (hi : 0 < highest.1 (R.coroot i)) : fλ ≠ 0 := by
  intro h
  have hE := (nodeSl2 R 𝕍 V hvn_ratFunc (isInt hvt hR highest) i).E_F_sub
    (mem_nodeWt_of_mem (i := i) (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := 𝕍)
      (Λ := highest.1)))
  change E R 𝕍 i • fλ - F R 𝕍 i • (E R 𝕍 i • vλ) =
    qIntZ (𝕍 ^ D.d i) (highest.1 (R.coroot i)) • vλ at hE
  rw [h, smul_zero, IrreducibleModule.E_smul_hwv, smul_zero, sub_zero] at hE
  exact (smul_ne_zero (qIntZ_vd_ne_zero hvn_ratFunc i hi.ne')
    (hwv_ne_zero hR hvn_ratFunc highest.1)) hE.symm

private def latticeEquiv (hR : R.IsXRegular) (hi : 0 < highest.1 (R.coroot i)) :
    LP ≃ₗ[LP] firstLoweringLattice highest i := by
  let f := LinearMap.toSpanSingleton LP V fλ
  have hf : Function.Injective f := by
    intro a b h
    exact integralLaurentEval_injective (smul_left_injective _ (lower_ne_zero highest i hR hi) h)
  have hspan : Submodule.span LP {fλ} = firstLoweringLattice highest i :=
    le_antisymm (Submodule.span_le.2 (Set.singleton_subset_iff.2 (lower_mem_lattice highest i)))
      (lattice_le_span highest i hR)
  exact (LinearEquiv.ofInjective f hf).trans
    (LinearEquiv.ofEq _ _ ((LinearMap.range_toSpanSingleton fλ).trans hspan))

variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {Λ : Fin 1 → I →₀ ℕ} (G : KLR.GradingDatum (stendhalQ Q Λ))

private abbrev laurentInvert : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv

local instance : RingHomInvPair laurentInvert.toRingHom laurentInvert.toRingHom :=
  RingHomInvPair.of_ringEquiv laurentInvert

/-- The generator assignment in Webster, arXiv:1309.3796v2, §4.7,
Theorem 4.38, for the one-factor, first lowering block with positive multiplicity.
Scalar inversion implements Webster's convention for grading shifts. -/
def oneBlackLatticeEquiv (hR : R.IsXRegular) (hwt : highest.1 (R.coroot i) = Λ 0 i)
    (hi : 0 < Λ 0 i) :
    K0 (tensorProductGrade G {i}) ≃ₛₗ[laurentInvert.toRingHom]
      firstLoweringLattice highest i :=
  let e : LP ≃ₛₗ[laurentInvert.toRingHom] LP :=
    LinearEquiv.ofBijective laurentInvert.toRingHom.toSemilinearMap laurentInvert.bijective
  ((oneBlackK0Equiv i G hi).trans e)
    |>.trans (latticeEquiv highest i hR (by rw [hwt]; exact_mod_cast hi))

@[simp] theorem oneBlackLatticeEquiv_regular (hR : R.IsXRegular)
    (hwt : highest.1 (R.coroot i) = Λ 0 i) (hi : 0 < Λ 0 i) :
    (oneBlackLatticeEquiv highest i G hR hwt hi (K0.of (GProj.regular (tensorProductGrade G {i}))) : V)
      = fλ := by
  rw [oneBlackLatticeEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    oneBlackK0Equiv_regular]
  change LaurentPolynomial.invert (1 : LP) • fλ = fλ
  rw [map_one, one_smul]

/-- The repository shift by `a` corresponds to Webster's multiplication by `q⁻ᵃ`. -/
theorem oneBlackLatticeEquiv_regular_shift (hR : R.IsXRegular)
    (hwt : highest.1 (R.coroot i) = Λ 0 i) (hi : 0 < Λ 0 i) (a : ℤ) :
    (oneBlackLatticeEquiv highest i G hR hwt hi
      (K0.of ((GProj.regular (tensorProductGrade G {i})).shift a)) : V) = 𝕍 ^ (-a) • fλ := by
  rw [← K0.T_smul_of, LinearEquiv.map_smulₛₗ]
  change integralLaurentEval (LaurentPolynomial.invert (LaurentPolynomial.T a)) •
    (oneBlackLatticeEquiv highest i G hR hwt hi
      (K0.of (GProj.regular (tensorProductGrade G {i}))) : V) = _
  rw [LaurentPolynomial.invert_T, integralLaurentEval_T, oneBlackLatticeEquiv_regular]

end Categorification.Stendhal.SingleBlack
