/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeTensorEquiv

/-!
# The lattice `U_q^{-,ℤ} ⊗ V^ℤ_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 4.39. The `ℤ[q, q⁻¹]`-span of the vectors `p̃_w` in `U⁻ ⊗ V^λ` is the tensor
product of Lusztig's integral form `U_q^{-,ℤ}` with the integral tensor product `V^ℤ_λ`.

* The `p̃_w` lie in `U_q^{-,ℤ} ⊗ V^ℤ_λ`: the divided powers `F̃_i^{(a)}` expand by the
  divided quantum binomial formula into `F_i^{(s)} u ⊗ F_i^{(r)} K^{-s ĩ} x`, and both factors
  are integral.
* Conversely, for a homogeneous `u ∈ U_q^{-,ℤ}` and a tensor vector `p_w`, the map `𝔮_N` sends
  `u ⊗ p_w` into a single integral weight space of `V^ℤ_{Nλ₀} ⊗ V^ℤ_λ`, which Theorem 4.38
  spans by tensor vectors. Each of these is zero or `𝔮_N` of some `p̃_{w'}`, and `𝔮_N` is
  injective on the relevant weights for `N` large.

## Main definitions

* `negIntegralTensor` : the `ℤ[q, q⁻¹]`-span of the `u ⊗ x`, `u ∈ U_q^{-,ℤ}`, `x ∈ V^ℤ_λ`.

## Main results

* `negTensorDivF_tmul` : the divided powers `F̃_i^{(a)}` on `u ⊗ x`.
* `negTensorLattice_eq_negIntegralTensor` : the span of the `p̃_w` is `U_q^{-,ℤ} ⊗ V^ℤ_λ`.
* `exists_negIntegralTensorEquiv` : **Webster, Proposition 4.39**,
  `K₀(T̃^λ) ≅ U_q^{-,ℤ} ⊗ V^ℤ_λ` with `[P̃_w] ↦ p̃_w`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra Categorification.Graded GProj QuantumGroup LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "ρ" => tensorRepresentation
local notation "hvt" => transcendental_ratFuncX
private abbrev invLP' := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance instRingHomInvPairInvLPLattice : RingHomInvPair invLP'.toRingHom invLP'.toRingHom :=
  RingHomInvPair.of_ringEquiv invLP'
local instance instNeZeroXNegativeTensorLattice : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

section Generic

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "divF" => fun (i : I) (n : ℕ) => qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)

/-! ### Divided powers on `U⁻` -/

omit [DecidableEq I] in
theorem negF_pow_mk (i : I) (n : ℕ) (y : LusztigF 𝕂 I) :
    (negF D i ^ n) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (FreeAlgebra.ι 𝕂 i ^ n * y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, negF_mk, pow_succ', mul_assoc]

omit [DecidableEq I] in
theorem qDivPow_negF_mk (i : I) (n : ℕ) (y : LusztigF 𝕂 I) :
    qDivPow (𝕍 ^ D.d i) n (negF D i) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (qDivPow (𝕍 ^ D.d i) n (θ 𝕂 i) * y) := by
  rw [qDivPow, qDivPow, LinearMap.smul_apply, negF_pow_mk, smul_mul_assoc,
    Submodule.Quotient.mk_smul]

/-- `U_q^{-,ℤ}` is stable under left multiplication by the divided powers `F_i^{(n)}`. -/
theorem qDivPow_negF_mem_negIntegral [Finite I] (i : I) (n : ℕ) {u : Um D 𝕍} (hu : u ∈ negIntegral D) :
    qDivPow (𝕍 ^ D.d i) n (negF D i) u ∈ negIntegral D := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [qDivPow_negF_mk]
  rw [mem_negIntegral] at hu ⊢
  change toQuotient D 𝕍 (_ * y) ∈ _
  change toQuotient D 𝕍 y ∈ _ at hu
  rw [map_mul, toQuotient_qDivPow]
  exact mul_mem (quotientIntegralGenerator_mem D i n) hu

theorem one_mem_negIntegral [Finite I] : (Submodule.Quotient.mk 1 : Um D 𝕍) ∈ negIntegral D := by
  rw [mem_negIntegral]
  change toQuotient D 𝕍 1 ∈ _
  rw [map_one]
  exact one_mem _

/-! ### Divided powers on `U⁻ ⊗ V^λ` -/

variable {ℓ : ℕ}

/-- **`F̃_i^{(n)}` on `U⁻ ⊗ V^λ`**:
`F̃_i^{(n)} = Σ_{r+s=n} q_i^{rs} (1 ⊗ F_i^{(r)}) (F_i^{(s)} ⊗ K_{-ĩ}^s)`. -/
theorem negTensorDivF_eq (wt : Fin ℓ → Dom R) (i : I) (n : ℕ) :
    negTensorDivF D wt i n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((𝕍 ^ D.d i) ^ (p.1 * p.2)) •
      (TensorProduct.map LinearMap.id (ρ wt (divF i p.1)) *
        TensorProduct.map (qDivPow (𝕍 ^ D.d i) p.2 (negF D i))
          (ρ wt (K R 𝕍 (-ktilde R i)) ^ p.2)) := by
  let t : 𝕂ˣ := vQ ^ D.d i
  let a : Module.End 𝕂 (NegTensor D wt) := TensorProduct.map LinearMap.id (ρ wt (F R 𝕍 i))
  let b : Module.End 𝕂 (NegTensor D wt) :=
    TensorProduct.map (negF D i) (ρ wt (K R 𝕍 (-ktilde R i)))
  have ht : (t : 𝕂) = 𝕍 ^ D.d i := by simp [t]
  have hz (m : ℕ) (hm : 0 < m) : (𝕍 ^ D.d i) ^ m ≠ 1 := by
    rw [← pow_mul]
    change (vQ : 𝕂) ^ (D.d i * m) ≠ 1
    rw [← Units.val_pow_eq_pow_val, ne_eq, Units.val_eq_one]
    exact vQ_pow_ne_one (mul_pos (D.d_pos i) hm)
  have hf : qFactorial (t : 𝕂) n ≠ 0 := by
    rw [ht]
    exact qFactorial_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero) (fun m hm _ => hz _ (by omega))
  have hcomm : b * a = ((t ^ (2 : ℤ) : 𝕂ˣ) : 𝕂) • (a * b) := by
    have hKF : ρ wt (K R 𝕍 (-ktilde R i)) * ρ wt (F R 𝕍 i) =
        ((t ^ (2 : ℤ) : 𝕂ˣ) : 𝕂) • (ρ wt (F R 𝕍 i) * ρ wt (K R 𝕍 (-ktilde R i))) := by
      rw [← map_mul, ← map_mul, K_mul_F, map_smul, map_neg, neg_neg, root_ktilde,
        D.cartanMatrix_self, Units.val_zpow_eq_zpow_val, ht, ← zpow_natCast, ← zpow_mul]
    simp only [a, b, Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id]
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hKF, TensorProduct.map_smul_right]
  have he : negTensorDivF D wt i n = qDivPow (t : 𝕂) n (a + b) := by
    rw [ht, negTensorDivF, negTensorF, add_comm]
  rw [he, qDivPow_add_of_qcomm t a b hcomm n hf]
  apply Finset.sum_congr rfl
  rintro ⟨r, s⟩ _
  rw [ht]
  congr 1
  simp only [a, b, qDivPow, TensorProduct.map_pow, ← Module.End.one_eq_id, one_pow, map_smul, map_pow,
      TensorProduct.map_smul_right, TensorProduct.map_smul_left]

/-- `F̃_i^{(n)}` on a pure tensor. -/
theorem negTensorDivF_tmul (wt : Fin ℓ → Dom R) (i : I) (n : ℕ) (u : Um D 𝕍)
    (x : TensorSpace wt) :
    negTensorDivF D wt i n (u ⊗ₜ[𝕂] x) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((𝕍 ^ D.d i) ^ (p.1 * p.2)) • (qDivPow (𝕍 ^ D.d i) p.2 (negF D i) u ⊗ₜ[𝕂]
        ρ wt (divF i p.1) ((ρ wt (K R 𝕍 (-ktilde R i)) ^ p.2) x)) := by
  rw [negTensorDivF_eq, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [LinearMap.smul_apply, Module.End.mul_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
    LinearMap.id_apply]

end Generic

/-! ### The lattice `U_q^{-,ℤ} ⊗ V^ℤ_λ` -/

section Lattice

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} [Finite I]

local notation "D" => C.toLusztig
local notation "moduleGrading" Λ' =>
  stendhalGradingDatum Λ' hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

variable (wt : Fin ℓ → Dom R)

/-- `U_q^{-,ℤ} ⊗ V^ℤ_λ`: the `ℤ[q, q⁻¹]`-span of the `u ⊗ x` with `u` in Lusztig's integral
form of `U⁻` and `x` in the integral tensor product of the highest weight lattices. -/
def negIntegralTensor : Submodule LP (NegTensor D wt) :=
  Submodule.span LP {z | ∃ u ∈ negIntegral D, ∃ x ∈ integralTensor wt, z = u ⊗ₜ[𝕂] x}

variable {C wt}

theorem tmul_mem_negIntegralTensor {u : Um D 𝕍} (hu : u ∈ negIntegral D) {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) : u ⊗ₜ[𝕂] x ∈ negIntegralTensor C wt :=
  Submodule.subset_span ⟨u, hu, x, hx, rfl⟩

omit [Finite I] in
/-- A Laurent scalar keeps a `ℤ[q, q⁻¹]`-submodule of `U⁻ ⊗ V^λ`. -/
theorem laurent_smul_mem {S : Submodule LP (NegTensor D wt)} {c : 𝕂}
    (hc : c ∈ (integralLaurentEval : LP →+* 𝕂).range) {z : NegTensor D wt} (hz : z ∈ S) :
    c • z ∈ S := by
  obtain ⟨a, rfl⟩ := hc
  rw [← negTensor_laurent_smul]
  exact S.smul_mem a hz

omit [Finite I] in
theorem zpow_mem_range (e : ℤ) : 𝕍 ^ e ∈ (integralLaurentEval : LP →+* 𝕂).range :=
  ⟨LaurentPolynomial.T e, integralLaurentEval_T e⟩

omit [Finite I] in
private theorem pow_apply_of_eq_smul {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (f : Module.End 𝕂 M) {x : M} {c : 𝕂} (h : f x = c • x) (s : ℕ) : (f ^ s) x = c ^ s • x := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ, Module.End.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

/-- `U_q^{-,ℤ} ⊗ V^ℤ_λ` is stable under the divided powers `F̃_i^{(n)}`. -/
theorem negTensorDivF_mem_negIntegralTensor (i : I) (n : ℕ) {z : NegTensor D wt}
    (hz : z ∈ negIntegralTensor C wt) : negTensorDivF D wt i n z ∈ negIntegralTensor C wt := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, x, hx, rfl⟩ := hz
    rw [← span_tensorWordVector] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      rw [negTensorDivF_tmul]
      refine Submodule.sum_mem _ fun p _ => ?_
      rw [pow_apply_of_eq_smul _ (tensorWordVector_torus w wt (-ktilde R i)), map_smul,
        TensorProduct.tmul_smul, smul_smul]
      have h𝕍 : 𝕍 ∈ (integralLaurentEval : LP →+* 𝕂).range := by
        simpa using zpow_mem_range 1
      refine laurent_smul_mem (mul_mem (pow_mem (pow_mem h𝕍 _) _) (pow_mem (zpow_mem_range _) _))
        (tmul_mem_negIntegralTensor (qDivPow_negF_mem_negIntegral i p.2 hu) ?_)
      rw [← span_tensorWordVector]
      exact Submodule.subset_span ⟨w.black i p.1, rfl⟩
    | zero => rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [tensor_laurent_smul, TensorProduct.tmul_smul, map_smul, ← negTensor_laurent_smul]
      exact Submodule.smul_mem _ c hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [negTensor_laurent_smul, map_smul, ← negTensor_laurent_smul]
    exact Submodule.smul_mem _ c hx

theorem lTensor_mem_negIntegralTensor {ℓ' : ℕ} {wt' : Fin ℓ' → Dom R}
    (f : TensorSpace wt →ₗ[𝕂] TensorSpace wt')
    (hf : ∀ x ∈ integralTensor wt, f x ∈ integralTensor wt') {z : NegTensor D wt}
    (hz : z ∈ negIntegralTensor C wt) :
    TensorProduct.map LinearMap.id f z ∈ negIntegralTensor C wt' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, x, hx, rfl⟩ := hz
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    exact tmul_mem_negIntegralTensor hu (hf x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [negTensor_laurent_smul, map_smul, ← negTensor_laurent_smul]
    exact Submodule.smul_mem _ c hx

/-- The vectors `p̃_w` lie in `U_q^{-,ℤ} ⊗ V^ℤ_λ`. -/
theorem negWordVector_mem_negIntegralTensor : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin n → Dom R),
    negWordVector D w wt ∈ negIntegralTensor C wt
  | _, .empty, wt => tmul_mem_negIntegralTensor one_mem_negIntegral
      (Submodule.subset_span ⟨_, fun j => hwv_mem_hwIntegral (wt j), rfl⟩)
  | _, .red w, wt => lTensor_mem_negIntegralTensor (appendHighest wt)
      (fun _ hx => append_mem_integralTensor wt hx (hwv_mem_hwIntegral _))
      (negWordVector_mem_negIntegralTensor w _)
  | _, .black w i a, wt => negTensorDivF_mem_negIntegralTensor i a
      (negWordVector_mem_negIntegralTensor w wt)

theorem negTensorLattice_le_negIntegralTensor :
    negTensorLattice (C := C) wt ≤ negIntegralTensor C wt :=
  Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact negWordVector_mem_negIntegralTensor w wt)

/-! ### The reverse inclusion -/

omit [Finite I] in
theorem prependTensor_smul_left {n : ℕ} (wt' : Fin (n + 1) → Dom R)
    (c : 𝕂) (v : IrreducibleModule R 𝕍 (wt' 0).1) (x : TensorSpace (fun j : Fin n => wt' j.succ)) :
    prependTensor wt' (c • v) x = c • prependTensor wt' v x := by
  rw [prependTensor, prependTensor, ← TensorProduct.smul_tmul', map_smul]

/-- Putting a vector of `V^ℤ_{λ₀}` in front of a vector of `V^ℤ_λ`. -/
theorem prepend_mem_integralTensor {n : ℕ} (wt' : Fin (n + 1) → Dom R)
    {v : IrreducibleModule R 𝕍 (wt' 0).1} (hv : v ∈ hwIntegral (wt' 0))
    {x : TensorSpace (fun j : Fin n => wt' j.succ)}
    (hx : x ∈ integralTensor (fun j : Fin n => wt' j.succ)) :
    prependTensor wt' v x ∈ integralTensor wt' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    have h := prependTensor_tprod wt'
      (Fin.cons (α := fun j => IrreducibleModule R 𝕍 (wt' j).1) v f)
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    rw [h]
    refine Submodule.subset_span ⟨_, fun j => ?_, rfl⟩
    induction j using Fin.cases with
    | zero => simpa using hv
    | succ j => simpa using hf j
  | zero =>
    rw [prependTensor, TensorProduct.tmul_zero, map_zero]
    exact zero_mem _
  | add a b _ _ ha hb => rw [prependTensor_add_right]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [tensor_laurent_smul, prependTensor_smul_right, ← tensor_laurent_smul]
    exact Submodule.smul_mem _ c ha

omit [DecidableEq I] [Finite I] in
private theorem cons_sum (ω₀ : Dom R) :
    ∑ j, ((Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) j).1 = ω₀.1 + ∑ j, (wt j).1 := by
  rw [Fin.sum_univ_succ]
  rfl

omit [Finite I] in
theorem negTensorMapCons_tmul (ω₀ : Dom R) (u : Um D 𝕍) (x : TensorSpace wt) :
    negTensorMapCons C ω₀ wt (u ⊗ₜ[𝕂] x) =
      prependTensor (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) (evq hvt ω₀ u) x := rfl

include hR in
/-- `𝔮_N (u ⊗ p_w)`, for `u` homogeneous of degree `ν` in `U_q^{-,ℤ}`, lies in the integral
weight space of `V^ℤ_{λ₀} ⊗ V^ℤ_λ` of black content `ν + c(w)`. -/
theorem negTensorMapCons_mem_integralTensorWeight (ω₀ : Dom R) {ν : I →₀ ℕ} {y : LusztigF 𝕂 I}
    (hy : y ∈ LusztigF.weightSpace 𝕂 ν)
    (hyi : (Submodule.Quotient.mk y : Um D 𝕍) ∈ negIntegral D) (w : TensorWord I ℓ) :
    negTensorMapCons C ω₀ wt (Submodule.Quotient.mk y ⊗ₜ[𝕂] tensorWordVector w wt) ∈
      integralTensorWeight (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR (ν + w.content) := by
  refine ⟨prepend_mem_integralTensor (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) ⟨_, hyi, rfl⟩
    (by rw [← span_tensorWordVector]; exact Submodule.subset_span ⟨w, rfl⟩), ?_⟩
  change tensorWeightProj _ hR ((∑ j, ((Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) j).1) -
    R.rootSum (ν + w.content)) _ = _
  rw [tensorWeightProj_eq_self_iff]
  intro a
  rw [← tensorRepresentation_K]
  have hev := ev_mem_weightSpace (pow_ne_one_of_transcendental' hvt) hR ω₀.1 hy a
  have hK := tensorRepresentation_K_prepend (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) a
    (evq hvt ω₀ (Submodule.Quotient.mk y)) (tensorWordVector w wt)
  rw [negTensorMapCons_tmul, hK]
  erw [tensorWordVector_torus w wt a]
  rw [evq_mk] at hK ⊢
  erw [hev, prependTensor_smul_left, prependTensor_smul_right]
  rw [smul_smul, ← zpow_add₀ RatFunc.X_ne_zero, cons_sum, R.rootSum_add]
  congr 2
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply]
  abel

private def largeWeight' (ω : Dom R) (N : ℕ) : Dom R :=
  ⟨N • ω.1, fun i => by rw [AddMonoidHom.nsmul_apply]; exact nsmul_nonneg (ω.2 i) N⟩

omit [DecidableEq I] [Finite I] in
private theorem largeWeight'_coroot {ω : Dom R} (h₁ : ∀ i, 1 ≤ ω.1 (R.coroot i)) (N : ℕ)
    (i : I) : (N : ℤ) ≤ (largeWeight' ω N).1 (R.coroot i) := by
  change (N : ℤ) ≤ (N • ω.1) (R.coroot i)
  rw [AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  nlinarith [h₁ i]

include hR in
/-- Every vector of the integral weight space of content `β` of `V^ℤ_{λ₀} ⊗ V^ℤ_λ` is `𝔮_N` of
a combination of vectors `p̃_w` of content `β`. -/
theorem exists_negTensorLattice_of_mem_integralTensorWeight (ω₀ : Dom R) (β : I →₀ ℕ)
    {X : TensorSpace (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R)}
    (hX : X ∈ integralTensorWeight (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β) :
    ∃ z ∈ negTensorLattice (C := C) wt, z ∈ negTensorBelow D wt β ∧
      negTensorMapCons C ω₀ wt z = X := by
  rw [← span_tensorWordVector_content] at hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨w', hw', rfl⟩ := hX
    rcases tensorWordVector_eq_zero_or w' (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) with h | ⟨h, hc⟩
    · exact ⟨0, zero_mem _, zero_mem _, by rw [map_zero, h]⟩
    · refine ⟨negWordVector D w'.eraseFirstRed wt, Submodule.subset_span ⟨_, rfl⟩, ?_, ?_⟩
      · have := negWordVector_mem_negTensorBelow w'.eraseFirstRed wt
        rwa [hc, hw'] at this
      · rw [negTensorMapCons_negWordVector, h]
  | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero _⟩
  | add X X' _ _ hX hX' =>
    obtain ⟨z, hz, hzb, rfl⟩ := hX
    obtain ⟨z', hz', hzb', rfl⟩ := hX'
    exact ⟨z + z', add_mem hz hz', add_mem hzb hzb', map_add _ _ _⟩
  | smul c X _ hX =>
    obtain ⟨z, hz, hzb, rfl⟩ := hX
    refine ⟨c • z, Submodule.smul_mem _ c hz, ?_, negTensorMapCons_laurent_smul C ω₀ wt c z⟩
    rw [negTensor_laurent_smul]
    exact Submodule.smul_mem _ _ hzb

include hR in
/-- For homogeneous `u ∈ U_q^{-,ℤ}`, the vectors `u ⊗ p_w` lie in the span of the `p̃_w`. -/
theorem tmul_tensorWordVector_mem_negTensorLattice (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    {ν : I →₀ ℕ} {y : LusztigF 𝕂 I} (hy : y ∈ LusztigF.weightSpace 𝕂 ν)
    (hyi : (Submodule.Quotient.mk y : Um D 𝕍) ∈ negIntegral D) (w : TensorWord I ℓ) :
    (Submodule.Quotient.mk y : Um D 𝕍) ⊗ₜ[𝕂] tensorWordVector w wt ∈
      negTensorLattice (C := C) wt := by
  obtain ⟨ω, h₁⟩ := hρ
  set β := ν + w.content
  let ω₀ := largeWeight' ω β.degree
  obtain ⟨z, hz, hzb, hzX⟩ := exists_negTensorLattice_of_mem_integralTensorWeight hR ω₀ β
    (negTensorMapCons_mem_integralTensorWeight hR ω₀ hy hyi w)
  have hgb : (Submodule.Quotient.mk y : Um D 𝕍) ⊗ₜ[𝕂] tensorWordVector w wt ∈
      negTensorBelow D wt β :=
    tmul_mem_negTensorBelow wt (Uw_le_negBelow le_self_add ⟨y, hy, rfl⟩) _
  have he := negTensorMap_injective_below hR (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R)
    (fun i => largeWeight'_coroot h₁ β.degree i) hgb hzb hzX.symm
  rw [he]
  exact hz

include hR in
/-- The vectors of `U_q^{-,ℤ} ⊗ V^ℤ_λ` lie in the span of the `p̃_w`. -/
theorem negIntegralTensor_le_negTensorLattice (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i)) :
    negIntegralTensor C wt ≤ negTensorLattice (C := C) wt := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, hu, x, hx, rfl⟩
  rw [← span_tensorWordVector] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have h : negativeQuotientEquiv D u ∈ Subalgebra.toSubmodule (quotientIntegralForm D) :=
      (mem_negIntegral D u).1 hu
    rw [quotientIntegralForm, Algebra.adjoin_eq_span] at h
    rw [← (negativeQuotientEquiv D).symm_apply_apply u]
    generalize negativeQuotientEquiv D u = q at h
    induction h using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨ν, y, hy, rfl, hyi⟩ := exists_homogeneous_of_mem_closure D hq
      rw [negativeQuotientEquiv_symm_toQuotient]
      exact tmul_tensorWordVector_mem_negTensorLattice hR hρ hy
        ((mem_negIntegral D _).2 (by rwa [← negativeQuotientEquiv_symm_toQuotient,
          LinearEquiv.apply_symm_apply])) w
    | zero => rw [map_zero, TensorProduct.zero_tmul]; exact zero_mem _
    | add q q' _ _ hq hq' => rw [map_add, TensorProduct.add_tmul]; exact add_mem hq hq'
    | smul c q _ hq =>
      have : (negativeQuotientEquiv D).symm (c • q) =
          integralLaurentEval c • (negativeQuotientEquiv D).symm q :=
        map_smul (negativeQuotientEquiv D).symm (integralLaurentEval c) q
      rw [this, ← TensorProduct.smul_tmul', ← negTensor_laurent_smul]
      exact Submodule.smul_mem _ c hq
  | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [tensor_laurent_smul, TensorProduct.tmul_smul, ← negTensor_laurent_smul]
    exact Submodule.smul_mem _ c hx

include hR in
/-- **The span of the `p̃_w` is `U_q^{-,ℤ} ⊗ V^ℤ_λ`** (Webster, arXiv:1309.3796v3,
Proposition 4.39). -/
theorem negTensorLattice_eq_negIntegralTensor (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i)) :
    negTensorLattice (C := C) wt = negIntegralTensor C wt :=
  le_antisymm negTensorLattice_le_negIntegralTensor (negIntegralTensor_le_negTensorLattice hR hρ)

include hQ hR in
/-- **Webster, arXiv:1309.3796v3, Proposition 4.39**: `K₀(T̃^λ) ≅ U_q^{-,ℤ} ⊗ V^ℤ_λ`.
For dominant labels `λ`, the sum over black contents of the split Grothendieck groups of
graded projective `T̃^λ`-modules is isomorphic, semilinearly for `q ↦ q⁻¹`, to the tensor
product of Lusztig's integral form `U_q^{-,ℤ}` with the integral tensor product `V^ℤ_λ`, by
an isomorphism sending `[P̃_w]` to `p̃_w`.

Route hypothesis (see the roadmap): a dominant weight `λ₁` with `⟨α_i^∨, λ₁⟩ ≥ 1` for all
`i`; Webster's proof fixes such a weight. -/
theorem exists_negIntegralTensorEquiv (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (Λ : Fin ℓ → I →₀ ℕ) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    ∃ e : DirectSum (Multiset I) (fun β => K0 (stendhalGrade (moduleGrading Λ) β))
        ≃ₛₗ[invLP'.toRingHom] negIntegralTensor C wt,
      ∀ w : TensorWord I ℓ, (e (DirectSum.lof LP _ _ w.content.toMultiset (tildeClass C hQ Λ w)) :
        NegTensor D wt) = negWordVector D w wt := by
  obtain ⟨e, he⟩ := exists_tildeTensorEquiv C hQ hR wt hρ Λ hwt
  refine ⟨e.trans (LinearEquiv.ofEq (negTensorLattice (C := C) wt) (negIntegralTensor C wt)
    (negTensorLattice_eq_negIntegralTensor hR hρ)), fun w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, he]

end Lattice

end Categorification.Stendhal.FirstWeight
