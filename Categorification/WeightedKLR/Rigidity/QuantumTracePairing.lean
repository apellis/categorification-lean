/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumDualTwist
import Categorification.WeightedKLR.Rigidity.QuantumLowestVector
import LieLean.Algebra.QuantumGroup.HighestWeightMaps
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# The quantum trace `qtr_μ : V_μ ⊗ V_{μ*} → ℚ(q)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1 and
Proposition 7.13: for `g` of finite type and `μ* = -w₀μ`, the quantum trace for the ST ribbon
structure is categorified by `T^{μ,μ*}_∅ = - ⊗ L̇_μ`, which is the evaluation functor of
Definition 7.4 for the pair `(μ*, μ)` read with the labels exchanged. On classes it is the
invariant map `V_μ ⊗ V_{μ*} → ℚ(q)` taking the value `1` on `v_l ⊗ v_h`, where `v_h` is the
highest weight vector of `V_{μ*}` and `v_l = [P⁰_{i^μ}]` Webster's lowest weight vector of `V_μ`
(proof of Proposition 7.5: `P^{(0,2ρ^∨(μ))}_{i_μ} ⊗ L_μ ≅ k`).

Construction. The vector `v_l` is primitive of weight `μ*` for the twisted action `u ↦ ψ(u)`
(`QuantumDual.dualTwist`), so the universal property of `V_{μ*}` gives a `ψ`-equivariant map
`Θ : V_{μ*} → V_μ`, `v_h ↦ v_l` (`twistLowest`). It is bijective (`twistLowest_bijective`):
`V_{μ*}` is simple, and the range is stable under `ψ(U) = U`. With Lusztig's contravariant form
`(-, -)` on `V_μ` we set

`qtr_μ(x ⊗ y) = (x, Θ y)`  (`quantumTrace`).

Since `ψ ∘ S = ρ`, `qtr_μ(a x ⊗ y) = qtr_μ(x ⊗ S(a) y)` (`quantumTracePairing_smul_left`), which
identifies `V_{μ*}` with the dual of `V_μ` through the antipode; equivalently `qtr_μ` is
`U`-invariant (`quantumTrace_smul`). Its normalization is `qtr_μ(v_l ⊗ v_h) = (v_l, v_l) = 1`
(`quantumTrace_lowest_hwv`), and every invariant functional on `V_μ ⊗ V_{μ*}` is a multiple of it
(`eq_smul_quantumTrace_of_invariant`): the invariant functionals form the line spanned by
`qtr_μ`.

The identification of this normalized invariant map with the ST quantum trace (ribbon element
acting on `V_λ` by `(-1)^{2ρ^∨(λ)} q^{⟨λ,λ⟩+2⟨λ,ρ⟩}`) is Webster's Proposition 7.13; here the map
is fixed by the normalization of the categorified functor, as in Webster's proof.
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

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "vl" => lowestVector P μ weight w
local notation "B" => IrreducibleModule.form (Subtype.val μ) hR hvn_ratFunc

/-! ### The twisted map `Θ : V_{μ*} → V_μ` -/

include hR hdom hm hw hlong in
private theorem twist_E_lowest (i : I) :
    E R vQ i • DualTwist.of (R := R) (v := vQ) vl = 0 := by
  rw [DualTwist.smul_of, dualTwist_E, smul_assoc,
    F_smul_lowestVector P hR μ weight hdom hm w hw hlong i, smul_zero]
  rfl

omit [FiniteDimensional K H] in
include hdom hm hw hlong in
private theorem twist_lowest_mem :
    DualTwist.of (R := R) (v := vQ) vl ∈ weightSpace R vQ (DualTwist R vQ Vμ) μs.1 :=
  (DualTwist.mem_weightSpace_iff _ _).mpr
    (lowestVector_mem_weightSpace_neg P μ weight hdom hm w hw hlong)

/-- **The map `Θ : V_{μ*} → V_μ`**, `v_h ↦ v_l`, equivariant for `ψ`:
`Θ(u y) = ψ(u) Θ(y)` (as a `U`-linear map into the twist `DualTwist V_μ`). -/
def twistLowest : Vμs →ₗ[𝕌] DualTwist R vQ Vμ :=
  IrreducibleModule.lift LusztigF.transcendental_ratFunc_X hR hvn_ratFunc μs.2
    (DualTwist.isIntegrable (IrreducibleModule.isIntegrable hR hvn_ratFunc μ.2))
    (DualTwist.of (R := R) (v := vQ) vl) (twist_lowest_mem P μ weight hdom hm w hw hlong)
    (twist_E_lowest P hR μ weight hdom hm w hw hlong)

@[simp] theorem twistLowest_hwv :
    twistLowest P hR μ weight hdom hm w hw hlong (IrreducibleModule.hwv R vQ μs.1) =
      DualTwist.of vl :=
  IrreducibleModule.lift_hwv _ _ _ _ _ _ _ _

/-- `Θ` as a linear map `V_{μ*} → V_μ`. -/
def twistLowestLinear : Vμs →ₗ[𝕂] Vμ :=
  DualTwist.of.symm.toLinearMap ∘ₗ (twistLowest P hR μ weight hdom hm w hw hlong).restrictScalars 𝕂

theorem twistLowestLinear_smul (u : 𝕌) (y : Vμs) :
    twistLowestLinear P hR μ weight hdom hm w hw hlong (u • y) =
      dualTwist R vQ u • twistLowestLinear P hR μ weight hdom hm w hw hlong y := by
  change DualTwist.of.symm (twistLowest P hR μ weight hdom hm w hw hlong (u • y)) = _
  rw [LinearMap.map_smul, DualTwist.of_symm_smul]
  rfl

theorem twistLowestLinear_hwv :
    twistLowestLinear P hR μ weight hdom hm w hw hlong (IrreducibleModule.hwv R vQ μs.1) = vl := by
  change DualTwist.of.symm (twistLowest P hR μ weight hdom hm w hw hlong _) = _
  rw [twistLowest_hwv]
  rfl

theorem twistLowestLinear_injective :
    Function.Injective (twistLowestLinear P hR μ weight hdom hm w hw hlong) := by
  have := IrreducibleModule.isSimpleModule hR hvn_ratFunc (v := vQ) μs.1
  rcases LinearMap.injective_or_eq_zero (twistLowest P hR μ weight hdom hm w hw hlong) with h | h
  · exact DualTwist.of.symm.injective.comp h
  · exfalso
    apply lowestVector_ne_zero P hR μ weight hdom hm w hw
    have := congrArg (fun f => DualTwist.of.symm (f (IrreducibleModule.hwv R vQ μs.1))) h
    simpa [twistLowest_hwv] using this

/-- The range of `Θ` is a `U`-submodule of `V_μ`, since `ψ` is surjective. -/
private def twistRange : Submodule 𝕌 Vμ where
  carrier := Set.range (twistLowestLinear P hR μ weight hdom hm w hw hlong)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro u _ ⟨a, rfl⟩
    refine ⟨dualTwist R vQ u • a, ?_⟩
    rw [twistLowestLinear_smul, dualTwist_dualTwist]

theorem twistLowestLinear_surjective :
    Function.Surjective (twistLowestLinear P hR μ weight hdom hm w hw hlong) := by
  have := IrreducibleModule.isSimpleModule hR hvn_ratFunc (v := vQ) μ.1
  rcases IsSimpleOrder.eq_bot_or_eq_top (twistRange P hR μ weight hdom hm w hw hlong) with h | h
  · exfalso
    apply lowestVector_ne_zero P hR μ weight hdom hm w hw
    have hm' : vl ∈ twistRange P hR μ weight hdom hm w hw hlong :=
      ⟨_, twistLowestLinear_hwv P hR μ weight hdom hm w hw hlong⟩
    rw [h] at hm'
    exact (Submodule.mem_bot _).mp hm'
  · intro x
    have hx : x ∈ twistRange P hR μ weight hdom hm w hw hlong := by rw [h]; trivial
    exact hx

theorem twistLowestLinear_bijective :
    Function.Bijective (twistLowestLinear P hR μ weight hdom hm w hw hlong) :=
  ⟨twistLowestLinear_injective P hR μ weight hdom hm w hw hlong,
    twistLowestLinear_surjective P hR μ weight hdom hm w hw hlong⟩

/-- `Θ` as a linear equivalence `V_{μ*} ≃ V_μ`. -/
def twistLowestEquiv : Vμs ≃ₗ[𝕂] Vμ :=
  LinearEquiv.ofBijective _ (twistLowestLinear_bijective P hR μ weight hdom hm w hw hlong)

theorem twistLowestEquiv_symm_smul (u : 𝕌) (x : Vμ) :
    (twistLowestEquiv P hR μ weight hdom hm w hw hlong).symm (dualTwist R vQ u • x) =
      u • (twistLowestEquiv P hR μ weight hdom hm w hw hlong).symm x := by
  rw [LinearEquiv.symm_apply_eq]
  change _ = twistLowestLinear P hR μ weight hdom hm w hw hlong _
  rw [twistLowestLinear_smul]
  congr 1
  exact ((twistLowestEquiv P hR μ weight hdom hm w hw hlong).apply_symm_apply x).symm

/-! ### The pairing and the quantum trace -/

/-- The pairing `V_μ × V_{μ*} → ℚ(q)`, `(x, y) ↦ (x, Θ y)`. -/
def quantumTracePairing : Vμ →ₗ[𝕂] Vμs →ₗ[𝕂] 𝕂 :=
  (B).compl₂ (twistLowestLinear P hR μ weight hdom hm w hw hlong)

theorem quantumTracePairing_apply (x : Vμ) (y : Vμs) :
    quantumTracePairing P hR μ weight hdom hm w hw hlong x y =
      B x (twistLowestLinear P hR μ weight hdom hm w hw hlong y) := rfl

/-- **`V_{μ*}` is the dual of `V_μ` through the antipode**: `⟨a x, y⟩ = ⟨x, S(a) y⟩`. -/
theorem quantumTracePairing_smul_left (a : 𝕌) (x : Vμ) (y : Vμs) :
    quantumTracePairing P hR μ weight hdom hm w hw hlong (a • x) y =
      quantumTracePairing P hR μ weight hdom hm w hw hlong x (antipode R vQ a • y) := by
  rw [quantumTracePairing_apply, quantumTracePairing_apply, IrreducibleModule.isContravariant_form,
    twistLowestLinear_smul, dualTwist_antipode]

/-- **Normalization**: `qtr_μ(v_l ⊗ v_h) = 1`. -/
theorem quantumTracePairing_lowest_hwv :
    quantumTracePairing P hR μ weight hdom hm w hw hlong vl
      (IrreducibleModule.hwv R vQ μs.1) = 1 := by
  rw [quantumTracePairing_apply, twistLowestLinear_hwv,
    form_lowestVector P hR μ weight hdom hm w hw]

/-- **The quantum trace** `qtr_μ : V_μ ⊗ V_{μ*} → ℚ(q)` (Webster, Proposition 7.13 and
Proposition 7.20), on the `U`-module `V_μ ⊗ V_{μ*}` (coproduct `QuantumGroup.comul`). -/
def quantumTrace : TensorModule 𝕂 Vμ Vμs →ₗ[𝕂] 𝕂 :=
  TensorProduct.lift (quantumTracePairing P hR μ weight hdom hm w hw hlong) ∘ₗ
    (TensorModule.mk Vμ Vμs).symm.toLinearMap

theorem quantumTrace_tmul (x : Vμ) (y : Vμs) :
    quantumTrace P hR μ weight hdom hm w hw hlong (TensorModule.mk Vμ Vμs (x ⊗ₜ y)) =
      quantumTracePairing P hR μ weight hdom hm w hw hlong x y := rfl

theorem quantumTrace_lowest_hwv :
    quantumTrace P hR μ weight hdom hm w hw hlong
      (TensorModule.mk Vμ Vμs (vl ⊗ₜ IrreducibleModule.hwv R vQ μs.1)) = 1 :=
  quantumTracePairing_lowest_hwv P hR μ weight hdom hm w hw hlong

/-- **`qtr_μ` is `U`-invariant**: `qtr_μ(u t) = ε(u) qtr_μ(t)`. -/
theorem quantumTrace_smul (u : 𝕌) (t : TensorModule 𝕂 Vμ Vμs) :
    quantumTrace P hR μ weight hdom hm w hw hlong (u • t) =
      counit R vQ u * quantumTrace P hR μ weight hdom hm w hw hlong t := by
  let q := quantumTrace P hR μ weight hdom hm w hw hlong
  have hq : ∀ (x : Vμ) (y : Vμs), q (TensorModule.mk Vμ Vμs (x ⊗ₜ y)) =
      quantumTracePairing P hR μ weight hdom hm w hw hlong x y := fun _ _ => rfl
  have hp := quantumTracePairing_smul_left P hR μ weight hdom hm w hw hlong
  -- it suffices to treat pure tensors
  suffices h : ∀ (x : Vμ) (y : Vμs), q (u • TensorModule.mk Vμ Vμs (x ⊗ₜ y)) =
      counit R vQ u * q (TensorModule.mk Vμ Vμs (x ⊗ₜ y)) by
    obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
    induction t using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add a b ha hb => rw [map_add, smul_add, map_add, ha, hb, map_add, mul_add]
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
    rw [mul_smul, map_mul]
    obtain ⟨s, hs⟩ := (TensorModule.mk Vμ Vμs).surjective
      (b • TensorModule.mk Vμ Vμs (x ⊗ₜ[𝕂] y))
    rw [← hs]
    have key : ∀ s : Vμ ⊗[𝕂] Vμs, q (a • TensorModule.mk Vμ Vμs s) =
        counit R vQ a * q (TensorModule.mk Vμ Vμs s) := by
      intro s
      induction s using TensorProduct.inductionOn with
      | tmul x' y' => exact ha x' y'
      | add c d hc hd => rw [map_add, smul_add, map_add, hc, hd, map_add, mul_add]
    rw [key, hs, hb, mul_assoc]

/-! ### Uniqueness: the invariant line -/

omit [FiniteDimensional K H] in
/-- An invariant pairing satisfies `β(a x, y) = β(x, S(a) y)`. -/
private theorem pairing_smul_left_of_invariant (β : Vμ →ₗ[𝕂] Vμs →ₗ[𝕂] 𝕂)
    (hβ : ∀ (u : 𝕌) (x : Vμ) (y : Vμs), TensorProduct.lift β
      ((TensorModule.mk Vμ Vμs).symm (u • TensorModule.mk Vμ Vμs (x ⊗ₜ y))) =
        counit R vQ u * β x y)
    (a : 𝕌) (x : Vμ) (y : Vμs) : β (a • x) y = β x (antipode R vQ a • y) := by
  have hK : ∀ (ν : Y) (x : Vμ) (y : Vμs),
      β (QuantumGroup.K R vQ ν • x) y = β x (QuantumGroup.K R vQ (-ν) • y) := by
    intro ν x y
    have h := hβ (QuantumGroup.K R vQ ν) x (QuantumGroup.K R vQ (-ν) • y)
    rw [TensorModule.K_smul_tmul, counit_K, one_mul, ← mul_smul, K_add, add_neg_cancel, K_zero,
      one_smul] at h
    exact h
  induction a using QuantumGroup.induction_on generalizing x y with
  | algebraMap c => rw [algebraMap_smul, antipode_algebraMap, algebraMap_smul, map_smul,
      LinearMap.smul_apply, map_smul]
  | E i =>
    have h := hβ (E R vQ i) x y
    rw [TensorModule.E_smul_tmul, counit_E, zero_mul, map_add] at h
    change β (E R vQ i • x) y + β (Kt R vQ i • x) (E R vQ i • y) = 0 at h
    rw [hK] at h
    rw [antipode_E, neg_smul, map_neg, mul_smul]
    linear_combination h
  | F i =>
    have h := hβ (F R vQ i) x (Kt R vQ i • y)
    rw [TensorModule.F_smul_tmul, counit_F, zero_mul, map_add] at h
    change β (F R vQ i • x) (QuantumGroup.K R vQ (-ktilde R i) • Kt R vQ i • y) +
      β x (F R vQ i • Kt R vQ i • y) = 0 at h
    rw [← mul_smul, K_add, neg_add_cancel, K_zero, one_smul] at h
    rw [antipode_F, neg_smul, map_neg, mul_smul]
    linear_combination h
  | K ν => rw [hK, antipode_K]
  | add a b ha hb => rw [add_smul, map_add, LinearMap.add_apply, ha, hb, map_add, add_smul,
      map_add]
  | mul a b ha hb => rw [mul_smul, ha, hb, antipode_mul, mul_smul]

/-- **The invariant line.** Every `U`-invariant functional `φ` on `V_μ ⊗ V_{μ*}` is
`φ(v_l ⊗ v_h) • qtr_μ`. -/
theorem eq_smul_quantumTrace_of_invariant (φ : TensorModule 𝕂 Vμ Vμs →ₗ[𝕂] 𝕂)
    (hφ : ∀ (u : 𝕌) t, φ (u • t) = counit R vQ u * φ t) :
    φ = φ (TensorModule.mk Vμ Vμs (vl ⊗ₜ IrreducibleModule.hwv R vQ μs.1)) •
      quantumTrace P hR μ weight hdom hm w hw hlong := by
  set e := twistLowestEquiv P hR μ weight hdom hm w hw hlong
  let β : Vμ →ₗ[𝕂] Vμs →ₗ[𝕂] 𝕂 := (TensorProduct.mk 𝕂 Vμ Vμs).compr₂
    (φ ∘ₗ (TensorModule.mk Vμ Vμs).toLinearMap)
  have hlift : TensorProduct.lift β = φ ∘ₗ (TensorModule.mk Vμ Vμs).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  have hβ : ∀ (u : 𝕌) (x : Vμ) (y : Vμs), TensorProduct.lift β
      ((TensorModule.mk Vμ Vμs).symm (u • TensorModule.mk Vμ Vμs (x ⊗ₜ y))) =
        counit R vQ u * β x y := by
    intro u x y
    rw [hlift]
    exact hφ u _
  have hadj := pairing_smul_left_of_invariant P μ weight hdom hm w hw hlong β hβ
  let Γ : LinearMap.BilinForm 𝕂 Vμ := β.compl₂ e.symm.toLinearMap
  have hΓ : IsContravariant R vQ Γ := by
    intro a x x'
    change β (a • x) (e.symm x') = β x (e.symm (rho R vQ a • x'))
    rw [hadj, ← dualTwist_antipode, twistLowestEquiv_symm_smul]
  have key : ∀ (x : Vμ) (y : Vμs), β x y =
      Γ (IrreducibleModule.hwv R vQ μ.1) (IrreducibleModule.hwv R vQ μ.1) *
        quantumTracePairing P hR μ weight hdom hm w hw hlong x y := by
    intro x y
    have h := IrreducibleModule.eq_smul_form_of_isContravariant hR hvn_ratFunc hΓ x (e y)
    change β x (e.symm (e y)) = _ at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h
  have hc : φ (TensorModule.mk Vμ Vμs (vl ⊗ₜ IrreducibleModule.hwv R vQ μs.1)) =
      Γ (IrreducibleModule.hwv R vQ μ.1) (IrreducibleModule.hwv R vQ μ.1) := by
    have := key vl (IrreducibleModule.hwv R vQ μs.1)
    rw [quantumTracePairing_lowest_hwv, mul_one] at this
    exact this
  rw [hc]
  apply LinearMap.ext
  intro t
  obtain ⟨t, rfl⟩ := (TensorModule.mk Vμ Vμs).surjective t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact key x y
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

end Categorification.Stendhal.QuantumDual
