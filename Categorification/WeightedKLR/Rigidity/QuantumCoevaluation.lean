/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumIrreducibleFinite
import Mathlib.LinearAlgebra.Contraction
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.DirectSumUniqueness

/-!
# Quantum evaluation and coevaluation for `V_μ` and `V_{μ*}`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1
(the pairing of `V_μ` with `V_{μ*}`, `μ* = -w₀μ`, normalized by its value on `v_h ⊗ v_l`; the
evaluation `E^{λ*,λ}_∅` and the coevaluation sending `1` to the canonical element of the pairing)
and Proposition 7.20 (the maps `coev_μ`, `qtr_μ` it categorifies). Finite type enters through
`[Finite (P.weylGroup _)]`.

* `dualIntegralWeight`, `lowestContent_dualIntegralWeight`: the datum `-w₀λ` of `μ*` has the same
  content `β` as `λ` (`w₀² = 1`), so `v_l^{μ*}` has weight `-μ`.
* `twistLowestLinear_dualLowestVector`: `Θ(v_l^{μ*}) = a v_h^μ` with `a ≠ 0`.
* `evaluationPairing`: `ev_μ(y, x) = a (y, Θ⁻¹ x)` on `V_{μ*} × V_μ`, with `ev(u y, x) =
  ev(y, S(u) x)`, `ev_μ(v_l^{μ*}, v_h^μ) = 1` and `ev_μ(v_h^{μ*}, v_l^μ) = a`;
  `evaluation_smul`: `ev_μ` is invariant.
* `contraction_bijective`: `x ⊗ y' ↦ ev_μ(-, x) y'` is a linear isomorphism
  `V_μ ⊗ V_{μ*} ≃ End(V_{μ*})` (finite dimension, `QuantumIrreducibleFinite`).
* `coevaluationElement`, `coevaluation`: the canonical element of `ev_μ`, the preimage of `id`;
  both zigzag identities (`contraction_coevaluationElement`,
  `contractionRight_coevaluationElement`); invariance (`coevaluationElement_smul`,
  `coevaluation_smul`); the invariant line (`eq_smul_coevaluationElement_of_invariant`).
* `tensorForm_coevaluationElement`: `(B_μ ⊗ B_{μ*})(t, coev_μ(1)) = a⁻¹ qtr_μ(t)`.

Webster's normalization of `ev_μ` (value `1` on `v_l ⊗ v_h`) is the one stated in §7.1. The
canonical element of `a⁻¹ ev_μ` is `a coev_μ(1)`, with component `v_l ⊗ v_h` in
`(V_μ)_low ⊗ (V_{μ*})_high` and `a v_h ⊗ v_l` in `(V_μ)_high ⊗ (V_{μ*})_low`; in the proof of
Proposition 7.5 the corresponding factor for `[L_λ]` is `(-1)^{2ρ^∨(λ)} q^{-2⟨λ,ρ⟩}`. The
value of `a` is not computed here. The construction of the
canonical element through the contraction is ours.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module
open scoped TensorProduct

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩
local notation "𝕌" => QuantumGroup R vQ
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan
local notation "cs" => P.coxeterSystem hCartan

/-- The integral weight `-w₀λ` of the dual module, for the Weyl element `w₀` of `w.reverse`. -/
def dualIntegralWeight (weight : P.integralWeights) (w : List I) : P.integralWeights :=
  -(w.foldl (fun x j => (Dc).reflection j x) weight)

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

omit [FiniteDimensional K H] in
include hdom hlong in
theorem isDominantIntegral_dualIntegralWeight :
    P.IsDominantIntegral (dualIntegralWeight P weight w : Dual K H) :=
  isDominantIntegral_neg_foldl P hCartan weight w hdom hlong

omit [FiniteDimensional K H] in
include hdom hm hw in
theorem dualIntegralWeight_coroot (j : I) :
    (dualIntegralWeight P weight w : Dual K H) (P.coroot j) =
      ((dualWeight P μ weight hdom hm w hw hlong).1 (R.coroot j) : K) := by
  rw [dualWeight_val, lowestContent_sub_coroot P μ weight hdom hm w hw j, dualIntegralWeight,
    AddSubgroup.coe_neg, LinearMap.neg_apply, ← P.coroot_cartanDatum_cast hCartan]
  push_cast
  rfl

omit [FiniteDimensional K H] in
include hdom hw hlong in
/-- **The content of `w₀` is the same for `λ` and `λ* = -w₀λ`** (finite type: `w₀² = 1`). -/
theorem lowestContent_dualIntegralWeight [Finite (P.weylGroup hCartan)] :
    lowestContent P (dualIntegralWeight P weight w) w = lowestContent P weight w := by
  have hπ : (cs).wordProd w.reverse = (cs).longestElement := by
    have h : ((cs).wordProd w.reverse)⁻¹ = (cs).longestElement :=
      (cs).eq_longestElement_iff_forall_isRightDescent.2 fun j =>
        (cs).isRightDescent_inv_iff.2 (hlong j)
    rw [← (cs).inv_longestElement, ← h, inv_inv]
  have hsq : ∀ x, ((cs).wordProd w.reverse).1 (((cs).wordProd w.reverse).1 x) = x := by
    intro x
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hπ, (cs).longestElement_mul_self]
    rfl
  have h1 := rootSum_coevaluationWord_of_reduced P hCartan weight hdom w hw
  have h2 := rootSum_coevaluationWord_of_reduced P hCartan _
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong) w hw
  rw [P.coe_rootSum_cartanDatum hCartan] at h1 h2
  have hd : (dualIntegralWeight P weight w : Dual K H) = -((cs).wordProd w.reverse).1 weight := by
    rw [dualIntegralWeight, AddSubgroup.coe_neg, coe_foldl_reflection_cartanDatum P hCartan]
  rw [hd, map_neg, hsq] at h2
  have h3 := P.rootOf_injective (h2.trans (by rw [h1]; abel))
  ext i
  exact_mod_cast congrFun h3 i


/-! ### Invariant functionals from adjoint pairings -/

section Adjoint

variable {M N : Type*} [AddCommGroup M] [Module (RatFunc ℚ) M]
  [Module (QuantumGroup R (RatFunc.X : RatFunc ℚ)) M]
  [IsScalarTower (RatFunc ℚ) (QuantumGroup R (RatFunc.X : RatFunc ℚ)) M]
  [AddCommGroup N] [Module (RatFunc ℚ) N] [Module (QuantumGroup R (RatFunc.X : RatFunc ℚ)) N]
  [IsScalarTower (RatFunc ℚ) (QuantumGroup R (RatFunc.X : RatFunc ℚ)) N]

omit [Fintype I] in
/-- A pairing with `p(a m, n) = p(m, S(a) n)` induces a `U`-invariant functional on `M ⊗ N`. -/
theorem lift_smul_of_adjoint (p : M →ₗ[𝕂] N →ₗ[𝕂] 𝕂)
    (hp : ∀ (a : 𝕌) (m : M) (n : N), p (a • m) n = p m (antipode R vQ a • n))
    (u : 𝕌) (t : TensorModule 𝕂 M N) :
    (TensorProduct.lift p) ((TensorModule.mk M N).symm (u • t)) =
      counit R vQ u * (TensorProduct.lift p) ((TensorModule.mk M N).symm t) := by
  let q := (TensorProduct.lift p) ∘ₗ (TensorModule.mk M N).symm.toLinearMap
  change q (u • t) = counit R vQ u * q t
  have hq : ∀ (x : M) (y : N), q (TensorModule.mk M N (x ⊗ₜ y)) = p x y := fun _ _ => rfl
  have key : ∀ a : 𝕌, (∀ (x : M) (y : N), q (a • TensorModule.mk M N (x ⊗ₜ y)) =
      counit R vQ a * q (TensorModule.mk M N (x ⊗ₜ y))) →
      ∀ t, q (a • t) = counit R vQ a * q t := by
    intro a h t
    obtain ⟨t, rfl⟩ := (TensorModule.mk M N).surjective t
    induction t using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add c d hc hd => rw [map_add, smul_add, map_add, hc, hd, map_add, mul_add]
  refine key u ?_ t
  intro x y
  induction u using QuantumGroup.induction_on generalizing x y with
  | algebraMap c =>
    rw [algebraMap_smul, map_smul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      smul_eq_mul]
  | E i =>
    rw [TensorModule.E_smul_tmul, map_add, map_add, hq, hq, counit_E, zero_mul, hp, hp,
      antipode_E, antipode_K, ← mul_smul, neg_smul, map_neg, neg_add_cancel]
  | F i =>
    rw [TensorModule.F_smul_tmul, map_add, map_add, hq, hq, counit_F, zero_mul, hp,
      antipode_F, neg_smul, ← mul_smul, mul_assoc, Kt, K_add, add_neg_cancel, K_zero, mul_one,
      map_neg, neg_add_cancel]
  | K μ' =>
    rw [TensorModule.K_smul_tmul, hq, hq, counit_K, one_mul, hp,
      antipode_K, ← mul_smul, K_add, neg_add_cancel, K_zero, one_smul]
  | add a b ha hb => rw [add_smul, map_add, ha, hb, map_add, add_mul]
  | mul a b ha hb =>
    rw [mul_smul, map_mul, key a ha, hb, mul_assoc]

omit [Fintype I] in
theorem K_neg_smul_K_smul {M : Type*} [AddCommGroup M] [Module 𝕌 M] (ν : Y) (z : M) :
    QuantumGroup.K R vQ (-ν) • QuantumGroup.K R vQ ν • z = z := by
  rw [← mul_smul, K_add, neg_add_cancel, K_zero, one_smul]

omit [Fintype I] in
theorem K_smul_K_neg_smul {M : Type*} [AddCommGroup M] [Module 𝕌 M] (ν : Y) (z : M) :
    QuantumGroup.K R vQ ν • QuantumGroup.K R vQ (-ν) • z = z := by
  rw [← mul_smul, K_add, add_neg_cancel, K_zero, one_smul]

omit [Fintype I] in
/-- `L_q(Λ)` is generated by `v_Λ`. -/
theorem exists_eq_smul_irreducible_hwv {Λ : Y →+ ℤ} (y : IrreducibleModule R vQ Λ) :
    ∃ u : 𝕌, y = u • IrreducibleModule.hwv R vQ Λ := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨u, by rw [VermaModule.mk_eq_smul_hwv, Submodule.Quotient.mk_smul]⟩

end Adjoint

/-! ### The lowest weight vector of `V_{μ*}` -/

section Lowest

variable [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)]

include hR hdom hm hw hlong

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "Θ" => twistLowestLinear P hR μ weight hdom hm w hw hlong
local notation "B" => IrreducibleModule.form (Subtype.val μ) hR hvn_ratFunc
local notation "vls" => lowestVector P (dualWeight P μ weight hdom hm w hw hlong)
  (dualIntegralWeight P weight w) w

omit [FiniteDimensional K H] hR in
/-- The lowest weight vector `v_l` of `V_{μ*}` has weight `-μ`. -/
theorem dualLowestVector_mem_weightSpace : vls ∈ weightSpace R vQ Vμs (-μ.1) := by
  have h := lowestVector_mem_weightSpace P μs (dualIntegralWeight P weight w) w
  have he : μs.1 - R.rootSum (lowestContent P (dualIntegralWeight P weight w) w) = -μ.1 := by
    rw [lowestContent_dualIntegralWeight P weight hdom w hw hlong, dualWeight_val,
      sub_sub_cancel_left]
  rwa [he] at h

/-- The scalar `a` with `Θ(v_l^{μ*}) = a v_h^μ`. -/
def dualLowestScalar : 𝕂 := B (Θ vls) (IrreducibleModule.hwv R vQ μ.1)

/-- **`Θ` sends the lowest weight vector of `V_{μ*}` to a multiple of the highest weight vector
of `V_μ`.** -/
theorem twistLowestLinear_dualLowestVector :
    Θ vls = dualLowestScalar P hR μ weight hdom hm w hw hlong • IrreducibleModule.hwv R vQ μ.1 := by
  have hx := twistLowestLinear_mem_weightSpace P hR μ weight hdom hm w hw hlong
    (dualLowestVector_mem_weightSpace P μ weight hdom hm w hw hlong)
  rw [neg_neg] at hx
  obtain ⟨c, hc⟩ := exists_eq_smul_hwv_of_mem_weightSpace
    (hvt := LusztigF.transcendental_ratFunc_X) (hR := hR) μ hx
  rw [dualLowestScalar, hc, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
    IrreducibleModule.form_hwv, smul_eq_mul, mul_one]

theorem dualLowestScalar_ne_zero : dualLowestScalar P hR μ weight hdom hm w hw hlong ≠ 0 := by
  intro h0
  have h := twistLowestLinear_dualLowestVector P hR μ weight hdom hm w hw hlong
  rw [h0, zero_smul] at h
  refine lowestVector_ne_zero P hR μs (dualIntegralWeight P weight w)
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
    (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw ?_
  exact twistLowestLinear_injective P hR μ weight hdom hm w hw hlong (h.trans (map_zero _).symm)

/-! ### Webster's evaluation `ev_μ : V_{μ*} ⊗ V_μ → ℚ(q)` -/

local notation "Bs" =>
  IrreducibleModule.form (Subtype.val (dualWeight P μ weight hdom hm w hw hlong)) hR hvn_ratFunc
local notation "Θe" => twistLowestEquiv P hR μ weight hdom hm w hw hlong
local notation "aμ" => dualLowestScalar P hR μ weight hdom hm w hw hlong
local notation "vl" => lowestVector P μ weight w

/-- **Webster's evaluation pairing** `ev_μ : V_{μ*} × V_μ → ℚ(q)`,
`(y, x) ↦ a (y, Θ⁻¹ x)`, normalized by `ev_μ(v_l^{μ*}, v_h^μ) = 1`
(`evaluationPairing_lowest_hwv`; Webster §7.1, the map `E^{λ*,λ}_∅`). -/
def evaluationPairing : Vμs →ₗ[𝕂] Vμ →ₗ[𝕂] 𝕂 :=
  aμ • (Bs).compl₂ (Θe).symm.toLinearMap

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem evaluationPairing_apply (y : Vμs) (x : Vμ) :
    evaluationPairing P hR μ weight hdom hm w hw hlong y x = aμ * Bs y ((Θe).symm x) := rfl

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- **`V_μ` is the dual of `V_{μ*}` through the antipode**: `ev(a y, x) = ev(y, S(a) x)`. -/
theorem evaluationPairing_smul_left (u : 𝕌) (y : Vμs) (x : Vμ) :
    evaluationPairing P hR μ weight hdom hm w hw hlong (u • y) x =
      evaluationPairing P hR μ weight hdom hm w hw hlong y (antipode R vQ u • x) := by
  have h : antipode R vQ u = dualTwist R vQ (rho R vQ u) := by
    rw [← dualTwist_antipode, dualTwist_dualTwist]
  rw [evaluationPairing_apply, evaluationPairing_apply, IrreducibleModule.isContravariant_form,
    h, twistLowestEquiv_symm_smul]

theorem twistLowestEquiv_symm_hwv :
    (Θe).symm (IrreducibleModule.hwv R vQ μ.1) = (aμ)⁻¹ • vls := by
  rw [LinearEquiv.symm_apply_eq, map_smul]
  change _ = (aμ)⁻¹ • Θ vls
  rw [twistLowestLinear_dualLowestVector, smul_smul,
    inv_mul_cancel₀ (dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong), one_smul]

/-- **Normalization** (Webster §7.1): `ev_μ(v_l^{μ*}, v_h^μ) = 1`. -/
theorem evaluationPairing_lowest_hwv :
    evaluationPairing P hR μ weight hdom hm w hw hlong vls
      (IrreducibleModule.hwv R vQ μ.1) = 1 := by
  rw [evaluationPairing_apply, twistLowestEquiv_symm_hwv, map_smul,
    form_lowestVector P hR μs (dualIntegralWeight P weight w)
      (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
      (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw, smul_eq_mul, mul_one,
    mul_inv_cancel₀ (dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong)]

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- The other extremal value: `ev_μ(v_h^{μ*}, v_l^μ) = a`. -/
theorem evaluationPairing_hwv_lowest :
    evaluationPairing P hR μ weight hdom hm w hw hlong (IrreducibleModule.hwv R vQ μs.1) vl =
      aμ := by
  have h : (Θe).symm vl = IrreducibleModule.hwv R vQ μs.1 := by
    rw [LinearEquiv.symm_apply_eq]
    exact (twistLowestLinear_hwv P hR μ weight hdom hm w hw hlong).symm
  rw [evaluationPairing_apply, h, IrreducibleModule.form_hwv, mul_one]

/-- **Webster's evaluation** `ev_μ : V_{μ*} ⊗ V_μ → ℚ(q)` (§7.1). -/
def evaluation : TensorModule 𝕂 Vμs Vμ →ₗ[𝕂] 𝕂 :=
  TensorProduct.lift (evaluationPairing P hR μ weight hdom hm w hw hlong) ∘ₗ
    (TensorModule.mk Vμs Vμ).symm.toLinearMap

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem evaluation_tmul (y : Vμs) (x : Vμ) :
    evaluation P hR μ weight hdom hm w hw hlong (TensorModule.mk Vμs Vμ (y ⊗ₜ x)) =
      evaluationPairing P hR μ weight hdom hm w hw hlong y x := rfl

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- **`ev_μ` is `U`-invariant**: `ev_μ(u t) = ε(u) ev_μ(t)`. -/
theorem evaluation_smul (u : 𝕌) (t : TensorModule 𝕂 Vμs Vμ) :
    evaluation P hR μ weight hdom hm w hw hlong (u • t) =
      counit R vQ u * evaluation P hR μ weight hdom hm w hw hlong t :=
  lift_smul_of_adjoint _ (evaluationPairing_smul_left P hR μ weight hdom hm w hw hlong) u t

/-! ### The contraction `V_μ ⊗ V_{μ*} ≃ End(V_{μ*})` -/

/-- `x ⊗ y' ↦ (y ↦ ev_μ(y, x) y')`. -/
def contraction : TensorModule 𝕂 Vμ Vμs →ₗ[𝕂] Module.End 𝕂 Vμs :=
  dualTensorHom 𝕂 Vμs Vμs ∘ₗ
    TensorProduct.map (evaluationPairing P hR μ weight hdom hm w hw hlong).flip LinearMap.id ∘ₗ
    (TensorModule.mk Vμ Vμs).symm.toLinearMap

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem contraction_tmul (x : Vμ) (y' y : Vμs) :
    contraction P hR μ weight hdom hm w hw hlong (TensorModule.mk Vμ Vμs (x ⊗ₜ y')) y =
      evaluationPairing P hR μ weight hdom hm w hw hlong y x • y' := rfl

theorem evaluationPairing_flip_injective :
    Function.Injective (evaluationPairing P hR μ weight hdom hm w hw hlong).flip := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h : ∀ y, Bs ((Θe).symm x) y = 0 := by
    intro y
    have := LinearMap.congr_fun hx y
    rw [LinearMap.flip_apply, evaluationPairing_apply, LinearMap.zero_apply, mul_eq_zero] at this
    rw [IrreducibleModule.form_comm]
    exact this.resolve_left (dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong)
  have h0 := IrreducibleModule.eq_zero_of_form_eq_zero hR hvn_ratFunc h
  rwa [LinearEquiv.map_eq_zero_iff] at h0

theorem contraction_bijective :
    Function.Bijective (contraction P hR μ weight hdom hm w hw hlong) := by
  have := finiteDimensional_dualIrreducible P hR μ weight hdom hm w hw hlong
  have := finiteDimensional_irreducible P hR μ weight hdom hm w hw hlong
  set ι := (evaluationPairing P hR μ weight hdom hm w hw hlong).flip
  have hdim : finrank 𝕂 Vμ = finrank 𝕂 (Module.Dual 𝕂 Vμs) := by
    rw [Subspace.dual_finrank_eq, (Θe).finrank_eq]
  have hι : Function.Bijective ι :=
    ⟨evaluationPairing_flip_injective P hR μ weight hdom hm w hw hlong,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        (evaluationPairing_flip_injective P hR μ weight hdom hm w hw hlong)⟩
  let e := LinearEquiv.ofBijective ι hι
  have hmap : TensorProduct.map ι LinearMap.id =
      (TensorProduct.congr e (LinearEquiv.refl 𝕂 Vμs)).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  refine (dualTensorHom_bijective (R := 𝕂) (M := Vμs) (N := Vμs)).comp ?_
  rw [hmap]
  exact (TensorProduct.congr e (LinearEquiv.refl 𝕂 Vμs)).bijective.comp
    (TensorModule.mk Vμ Vμs).symm.bijective

/-- **The quantum coevaluation** `coev_μ(1) ∈ V_μ ⊗ V_{μ*}` (Webster §7.1): the canonical
element of the pairing `ev_μ`, i.e. the preimage of `id` under the contraction. -/
def coevaluationElement : TensorModule 𝕂 Vμ Vμs :=
  (LinearEquiv.ofBijective _ (contraction_bijective P hR μ weight hdom hm w hw hlong)).symm
    LinearMap.id

/-- **The quantum coevaluation** `coev_μ : ℚ(q) → V_μ ⊗ V_{μ*}`. -/
def coevaluation : 𝕂 →ₗ[𝕂] TensorModule 𝕂 Vμ Vμs :=
  LinearMap.toSpanSingleton 𝕂 _ (coevaluationElement P hR μ weight hdom hm w hw hlong)

theorem coevaluation_apply (c : 𝕂) :
    coevaluation P hR μ weight hdom hm w hw hlong c =
      c • coevaluationElement P hR μ weight hdom hm w hw hlong := rfl

/-- **First zigzag identity**: `(ev_μ ⊗ id) ∘ (id ⊗ coev_μ) = id` on `V_{μ*}`. -/
theorem contraction_coevaluationElement :
    contraction P hR μ weight hdom hm w hw hlong
      (coevaluationElement P hR μ weight hdom hm w hw hlong) = LinearMap.id :=
  (LinearEquiv.ofBijective _
    (contraction_bijective P hR μ weight hdom hm w hw hlong)).apply_symm_apply LinearMap.id

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
private theorem ev_K_smul (ν : Y) (y : Vμs) (x : Vμ) :
    evaluationPairing P hR μ weight hdom hm w hw hlong (QuantumGroup.K R vQ ν • y) x =
      evaluationPairing P hR μ weight hdom hm w hw hlong y (QuantumGroup.K R vQ (-ν) • x) := by
  rw [evaluationPairing_smul_left, antipode_K]

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
private theorem ev_E_smul (i : I) (y : Vμs) (x : Vμ) :
    evaluationPairing P hR μ weight hdom hm w hw hlong (E R vQ i • y) x =
      -evaluationPairing P hR μ weight hdom hm w hw hlong y
        (QuantumGroup.K R vQ (-ktilde R i) • E R vQ i • x) := by
  rw [evaluationPairing_smul_left, antipode_E, neg_smul, map_neg, mul_smul]

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
private theorem ev_F_smul (i : I) (y : Vμs) (x : Vμ) :
    evaluationPairing P hR μ weight hdom hm w hw hlong (F R vQ i • y) x =
      -evaluationPairing P hR μ weight hdom hm w hw hlong y (F R vQ i • Kt R vQ i • x) := by
  rw [evaluationPairing_smul_left, antipode_F, neg_smul, map_neg, mul_smul]

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- Action of `K_ν` through the contraction: `Φ(K_ν t) = K_ν ∘ Φ(t) ∘ K_{-ν}`. -/
theorem contraction_K_smul (ν : Y) (t : TensorModule 𝕂 Vμ Vμs) (y : Vμs) :
    contraction P hR μ weight hdom hm w hw hlong (QuantumGroup.K R vQ ν • t) y =
      QuantumGroup.K R vQ ν •
        contraction P hR μ weight hdom hm w hw hlong t (QuantumGroup.K R vQ (-ν) • y) := by
  obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y' =>
    rw [TensorModule.K_smul_tmul, contraction_tmul, contraction_tmul, ev_K_smul, neg_neg]
    exact (smul_comm _ _ _).symm
  | add a b ha hb => simp only [map_add, smul_add, LinearMap.add_apply, ha, hb]

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- Action of `Eᵢ` through the contraction: `Φ(Eᵢ t) = Eᵢ ∘ Φ(t) ∘ K̃ᵢ⁻¹ - Φ(t) ∘ Eᵢ K̃ᵢ⁻¹`. -/
theorem contraction_E_smul (i : I) (t : TensorModule 𝕂 Vμ Vμs) (y : Vμs) :
    contraction P hR μ weight hdom hm w hw hlong (E R vQ i • t) y =
      E R vQ i • contraction P hR μ weight hdom hm w hw hlong t
          (QuantumGroup.K R vQ (-ktilde R i) • y) -
        contraction P hR μ weight hdom hm w hw hlong t
          (E R vQ i • QuantumGroup.K R vQ (-ktilde R i) • y) := by
  obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y' =>
    rw [TensorModule.E_smul_tmul, map_add, LinearMap.map_add, LinearMap.add_apply,
      contraction_tmul, contraction_tmul, contraction_tmul, contraction_tmul, ev_E_smul,
      ev_K_smul, ev_K_smul, neg_neg, K_smul_K_neg_smul, smul_comm (E R vQ i), neg_smul,
      sub_neg_eq_add, add_comm]
  | add a b ha hb =>
    simp only [map_add, smul_add, LinearMap.add_apply, ha, hb]
    abel

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- Action of `Fᵢ` through the contraction: `Φ(Fᵢ t) = Fᵢ ∘ Φ(t) - K̃ᵢ⁻¹ ∘ Φ(t) ∘ K̃ᵢ Fᵢ`. -/
theorem contraction_F_smul (i : I) (t : TensorModule 𝕂 Vμ Vμs) (y : Vμs) :
    contraction P hR μ weight hdom hm w hw hlong (F R vQ i • t) y =
      F R vQ i • contraction P hR μ weight hdom hm w hw hlong t y -
        QuantumGroup.K R vQ (-ktilde R i) •
          contraction P hR μ weight hdom hm w hw hlong t (Kt R vQ i • F R vQ i • y) := by
  obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y' =>
    rw [TensorModule.F_smul_tmul, map_add, LinearMap.map_add, LinearMap.add_apply,
      contraction_tmul, contraction_tmul, contraction_tmul, contraction_tmul, Kt, ev_K_smul,
      ev_F_smul, Kt, K_smul_K_neg_smul, smul_comm (F R vQ i), smul_comm (QuantumGroup.K R vQ _),
      neg_smul, sub_neg_eq_add, add_comm]
  | add a b ha hb =>
    simp only [map_add, smul_add, LinearMap.add_apply, ha, hb]
    abel

/-- **`coev_μ` is `U`-invariant**: `u · coev_μ(1) = ε(u) coev_μ(1)`. -/
theorem coevaluationElement_smul (u : 𝕌) :
    u • coevaluationElement P hR μ weight hdom hm w hw hlong =
      counit R vQ u • coevaluationElement P hR μ weight hdom hm w hw hlong := by
  have hinj := (contraction_bijective P hR μ weight hdom hm w hw hlong).1
  suffices key : ∀ c, contraction P hR μ weight hdom hm w hw hlong c = LinearMap.id →
      ∀ u : 𝕌, u • c = counit R vQ u • c from
    key _ (contraction_coevaluationElement P hR μ weight hdom hm w hw hlong) u
  intro c hΦ u
  have hΦ' : ∀ y, contraction P hR μ weight hdom hm w hw hlong c y = y := fun y => by
    rw [hΦ, LinearMap.id_apply]
  have hext : ∀ t t' : TensorModule 𝕂 Vμ Vμs,
      (∀ y, contraction P hR μ weight hdom hm w hw hlong t y =
        contraction P hR μ weight hdom hm w hw hlong t' y) → t = t' :=
    fun t t' h => hinj (LinearMap.ext h)
  induction u using QuantumGroup.induction_on with
  | algebraMap c' => rw [algebraMap_smul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply]
  | E i =>
    rw [counit_E, zero_smul]
    refine hext _ _ fun y => ?_
    rw [contraction_E_smul, hΦ', hΦ', sub_self, map_zero, LinearMap.zero_apply]
  | F i =>
    rw [counit_F, zero_smul]
    refine hext _ _ fun y => ?_
    rw [contraction_F_smul, hΦ', hΦ', Kt, K_neg_smul_K_smul, sub_self, map_zero,
      LinearMap.zero_apply]
  | K ν =>
    rw [counit_K, one_smul]
    refine hext _ _ fun y => ?_
    rw [contraction_K_smul, hΦ', hΦ', K_smul_K_neg_smul]
  | add a b ha hb => rw [add_smul, ha, hb, map_add, add_smul]
  | mul a b ha hb => rw [mul_smul, hb, smul_comm, ha, smul_smul, map_mul, mul_comm]

/-- **`coev_μ` is a `U`-module map** `ℚ(q) → V_μ ⊗ V_{μ*}` (trivial module `ℚ(q)` via `ε`). -/
theorem coevaluation_smul (u : 𝕌) (c : 𝕂) :
    u • coevaluation P hR μ weight hdom hm w hw hlong c =
      coevaluation P hR μ weight hdom hm w hw hlong (counit R vQ u * c) := by
  rw [coevaluation_apply, coevaluation_apply, smul_comm, coevaluationElement_smul, smul_smul,
    mul_comm]

/-! ### The second zigzag identity -/

/-- `x ⊗ y' ↦ (x' ↦ ev_μ(y', x') x)`. -/
def contractionRight : TensorModule 𝕂 Vμ Vμs →ₗ[𝕂] Module.End 𝕂 Vμ :=
  dualTensorHom 𝕂 Vμ Vμ ∘ₗ
    TensorProduct.map (evaluationPairing P hR μ weight hdom hm w hw hlong) LinearMap.id ∘ₗ
    (TensorProduct.comm 𝕂 Vμ Vμs).toLinearMap ∘ₗ (TensorModule.mk Vμ Vμs).symm.toLinearMap

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem contractionRight_tmul (x : Vμ) (y' : Vμs) (x' : Vμ) :
    contractionRight P hR μ weight hdom hm w hw hlong (TensorModule.mk Vμ Vμs (x ⊗ₜ y')) x' =
      evaluationPairing P hR μ weight hdom hm w hw hlong y' x' • x := rfl

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem evaluationPairing_contractionRight (t : TensorModule 𝕂 Vμ Vμs) (y : Vμs) (x' : Vμ) :
    evaluationPairing P hR μ weight hdom hm w hw hlong y
        (contractionRight P hR μ weight hdom hm w hw hlong t x') =
      evaluationPairing P hR μ weight hdom hm w hw hlong
        (contraction P hR μ weight hdom hm w hw hlong t y) x' := by
  obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y' =>
    rw [contractionRight_tmul, contraction_tmul, map_smul, map_smul, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, mul_comm]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- **Second zigzag identity**: `(id ⊗ ev_μ) ∘ (coev_μ ⊗ id) = id` on `V_μ`. -/
theorem contractionRight_coevaluationElement :
    contractionRight P hR μ weight hdom hm w hw hlong
      (coevaluationElement P hR μ weight hdom hm w hw hlong) = LinearMap.id := by
  suffices key : ∀ c, contraction P hR μ weight hdom hm w hw hlong c = LinearMap.id →
      contractionRight P hR μ weight hdom hm w hw hlong c = LinearMap.id from
    key _ (contraction_coevaluationElement P hR μ weight hdom hm w hw hlong)
  intro c hΦ
  refine LinearMap.ext fun x' => evaluationPairing_flip_injective P hR μ weight hdom hm w hw hlong
    (LinearMap.ext fun y => ?_)
  rw [LinearMap.flip_apply, LinearMap.flip_apply, evaluationPairing_contractionRight, hΦ,
    LinearMap.id_apply, LinearMap.id_apply]


/-! ### The invariant line in `V_μ ⊗ V_{μ*}` -/

omit [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- The contraction of an invariant tensor is a `U`-module endomorphism of `V_{μ*}`. -/
theorem contraction_smul_of_invariant (t : TensorModule 𝕂 Vμ Vμs)
    (ht : ∀ u : 𝕌, u • t = counit R vQ u • t) (u : 𝕌) (y : Vμs) :
    contraction P hR μ weight hdom hm w hw hlong t (u • y) =
      u • contraction P hR μ weight hdom hm w hw hlong t y := by
  set f := contraction P hR μ weight hdom hm w hw hlong t
  have hK : ∀ (ν : Y) (y : Vμs), f (QuantumGroup.K R vQ ν • y) = QuantumGroup.K R vQ ν • f y := by
    intro ν y
    have h := contraction_K_smul P hR μ weight hdom hm w hw hlong ν t (QuantumGroup.K R vQ ν • y)
    rwa [ht, counit_K, one_smul, K_neg_smul_K_smul] at h
  have hE : ∀ (i : I) (y : Vμs), f (E R vQ i • y) = E R vQ i • f y := by
    intro i y
    have h := contraction_E_smul P hR μ weight hdom hm w hw hlong i t
      (QuantumGroup.K R vQ (ktilde R i) • y)
    rw [ht, counit_E, zero_smul, map_zero, LinearMap.zero_apply, K_neg_smul_K_smul] at h
    exact (sub_eq_zero.mp h.symm).symm
  have hF : ∀ (i : I) (y : Vμs), f (F R vQ i • y) = F R vQ i • f y := by
    intro i y
    have h := contraction_F_smul P hR μ weight hdom hm w hw hlong i t y
    rw [ht, counit_F, zero_smul, map_zero, LinearMap.zero_apply, Kt, hK,
      K_neg_smul_K_smul] at h
    exact (sub_eq_zero.mp h.symm).symm
  induction u using QuantumGroup.induction_on generalizing y with
  | algebraMap c => rw [algebraMap_smul, algebraMap_smul, map_smul]
  | E i => exact hE i y
  | F i => exact hF i y
  | K ν => exact hK ν y
  | add a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]
  | mul a b ha hb => rw [mul_smul, ha, hb, mul_smul]

/-- **The invariant line** (Webster §7.1): every `U`-invariant tensor in `V_μ ⊗ V_{μ*}` is a
multiple of `coev_μ(1)`. -/
theorem eq_smul_coevaluationElement_of_invariant (t : TensorModule 𝕂 Vμ Vμs)
    (ht : ∀ u : 𝕌, u • t = counit R vQ u • t) :
    t = Bs (contraction P hR μ weight hdom hm w hw hlong t (IrreducibleModule.hwv R vQ μs.1))
        (IrreducibleModule.hwv R vQ μs.1) •
      coevaluationElement P hR μ weight hdom hm w hw hlong := by
  set f := contraction P hR μ weight hdom hm w hw hlong t
  have hf := contraction_smul_of_invariant P hR μ weight hdom hm w hw hlong t ht
  have hmem : f (IrreducibleModule.hwv R vQ μs.1) ∈ weightSpace R vQ Vμs μs.1 := by
    intro ν
    rw [← hf, IrreducibleModule.hwv_mem_weightSpace ν, map_smul]
  obtain ⟨c, hc⟩ := exists_eq_smul_hwv_of_mem_weightSpace
    (hvt := LusztigF.transcendental_ratFunc_X) (hR := hR) μs hmem
  have hc' : Bs (f (IrreducibleModule.hwv R vQ μs.1)) (IrreducibleModule.hwv R vQ μs.1) = c := by
    rw [hc, map_smul, LinearMap.smul_apply, IrreducibleModule.form_hwv, smul_eq_mul, mul_one]
  rw [hc']
  apply (contraction_bijective P hR μ weight hdom hm w hw hlong).1
  refine LinearMap.ext fun y => ?_
  obtain ⟨u, rfl⟩ := exists_eq_smul_irreducible_hwv y
  rw [LinearMap.map_smul (contraction P hR μ weight hdom hm w hw hlong) c,
    contraction_coevaluationElement, LinearMap.smul_apply, LinearMap.id_apply, hf, hc, smul_comm]


/-! ### Convention point: `qtr_μ` against `coev_μ` -/

theorem evaluationPairing_injective :
    Function.Injective (evaluationPairing P hR μ weight hdom hm w hw hlong) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  refine IrreducibleModule.eq_zero_of_form_eq_zero hR hvn_ratFunc fun y => ?_
  have := LinearMap.congr_fun hz ((Θe) y)
  rw [evaluationPairing_apply, LinearEquiv.symm_apply_apply, LinearMap.zero_apply,
    mul_eq_zero] at this
  exact this.resolve_left (dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong)

/-- **The transpose identity** (convention point (a) of Webster, Proposition 7.20): for the
symmetric contravariant forms `B_μ ⊗ B_{μ*}` on `V_μ ⊗ V_{μ*}`,
`(B_μ ⊗ B_{μ*})(x ⊗ y, coev_μ(1)) = a⁻¹ qtr_μ(x ⊗ y)`, where `Θ(v_l^{μ*}) = a v_h^μ`. -/
theorem tensorForm_coevaluationElement (x : Vμ) (y : Vμs) :
    TensorProduct.lift ((LinearMap.mul 𝕂 𝕂).compl₁₂ (B x) (Bs y))
        ((TensorModule.mk Vμ Vμs).symm (coevaluationElement P hR μ weight hdom hm w hw hlong)) =
      (aμ)⁻¹ * quantumTrace P hR μ weight hdom hm w hw hlong (TensorModule.mk Vμ Vμs (x ⊗ₜ y)) := by
  have := finiteDimensional_dualIrreducible P hR μ weight hdom hm w hw hlong
  have := finiteDimensional_irreducible P hR μ weight hdom hm w hw hlong
  have ha := dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong
  have hdim : finrank 𝕂 Vμs = finrank 𝕂 (Module.Dual 𝕂 Vμ) := by
    rw [Subspace.dual_finrank_eq, (Θe).finrank_eq]
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (evaluationPairing_injective P hR μ weight hdom hm w hw hlong) (B x)
  have key : ∀ t, TensorProduct.lift ((LinearMap.mul 𝕂 𝕂).compl₁₂ (B x) (Bs y))
      ((TensorModule.mk Vμ Vμs).symm t) =
      Bs y (contraction P hR μ weight hdom hm w hw hlong t z) := by
    intro t
    obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
    induction t using TensorProduct.inductionOn with
    | tmul x₁ y₁ =>
      rw [LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
        LinearMap.mul_apply', contraction_tmul, map_smul, smul_eq_mul, hz]
    | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd]
  rw [key, contraction_coevaluationElement, LinearMap.id_apply, quantumTrace_tmul,
    quantumTracePairing_apply, ← hz, evaluationPairing_apply]
  change _ = (aμ)⁻¹ * (aμ * Bs z ((Θe).symm ((Θe) y)))
  rw [LinearEquiv.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ ha, one_mul,
    IrreducibleModule.form_comm]

end Lowest

end Categorification.Stendhal.QuantumDual
