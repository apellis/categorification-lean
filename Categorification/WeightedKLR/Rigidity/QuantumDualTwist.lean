/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LieLean.Algebra.QuantumGroup.Hopf
import LieLean.Algebra.QuantumGroup.ContravariantForm
import LieLean.Algebra.QuantumGroup.Integrable
import LieLean.Algebra.QuantumGroup.RootDatumHom
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegative

/-!
# The twist relating the antipode and the contravariant anti-automorphism

Input for the quantum coevaluation and quantum trace of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §7.1 (the pairing `V_λ ⊗ V_{λ*} → ℚ(q)` fixed before
Lemma 7.3) and Proposition 7.20.

A pairing `β` of two `U`-modules is invariant (`β(Δ(u)(x ⊗ y)) = ε(u) β(x ⊗ y)`) exactly when
`β(a x, y) = β(x, S(a) y)` for the antipode `S` (`QuantumGroup.antipode`, [Lus] 3.3.1). For a
contravariant form `B` (`B(a x, y) = B(x, ρ(a) y)`, `QuantumGroup.rho`) and a linear map `Θ`,
`β(x, y) = B(x, Θ y)` has this property when `Θ(b y) = ψ(b) Θ(y)` for the automorphism
`ψ = ρ ∘ S⁻¹`. Here `ψ` is the composite of a diagonal automorphism and the Chevalley involution
(`QuantumDual.dualTwist`):

`ψ(Eᵢ) = -vᵢ Fᵢ`, `ψ(Fᵢ) = -vᵢ⁻¹ Eᵢ`, `ψ(K_μ) = K_{-μ}`,

and `ψ ∘ S = ρ` (`QuantumDual.dualTwist_antipode`), `ψ ∘ ψ = id`
(`QuantumDual.dualTwist_dualTwist`). A `U`-module `M` twisted by `ψ` (`QuantumDual.DualTwist M`)
has the weight spaces of `M` with negated weights and is integrable when `M` is.

## Main definitions and results

* `QuantumDual.dualTwist`, `dualTwist_E`, `dualTwist_F`, `dualTwist_K`.
* `QuantumDual.dualTwist_antipode`: `ψ (S u) = ρ u`.
* `QuantumDual.dualTwist_dualTwist`: `ψ (ψ u) = u`.
* `QuantumDual.DualTwist`, `DualTwist.mem_weightSpace_iff`, `DualTwist.isIntegrable`.

The computations are standard; the formulation is ours.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k) [NeZero v]

/-- The scalars `-vᵢ` of the diagonal part of the dual twist. -/
def dualTwistScalar (i : I) : kˣ :=
  Units.mk0 (-(v ^ D.d i)) (neg_ne_zero.mpr (pow_ne_zero _ (NeZero.ne v)))

/-- The automorphism `ψ = ρ ∘ S⁻¹` of `U`: `Eᵢ ↦ -vᵢ Fᵢ`, `Fᵢ ↦ -vᵢ⁻¹ Eᵢ`, `K_μ ↦ K_{-μ}`. -/
def dualTwist : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (chevalley R v).comp (diagHom R v (dualTwistScalar (D := D) v))

@[simp] theorem dualTwist_E (i : I) :
    dualTwist R v (E R v i) = (-(v ^ D.d i)) • F R v i := by
  simp only [dualTwist, AlgHom.comp_apply, diagHom_E, map_smul, chevalley_E]
  rfl

@[simp] theorem dualTwist_F (i : I) :
    dualTwist R v (F R v i) = (-(v ^ D.d i))⁻¹ • E R v i := by
  simp only [dualTwist, AlgHom.comp_apply, diagHom_F, map_smul, chevalley_F]
  rfl

@[simp] theorem dualTwist_K (μ : Y) : dualTwist R v (K R v μ) = K R v (-μ) := by
  simp only [dualTwist, AlgHom.comp_apply, diagHom_K, chevalley_K]

/-- `ψ` is an involution. -/
theorem dualTwist_comp_dualTwist :
    (dualTwist R v).comp (dualTwist R v) = AlgHom.id k (QuantumGroup R v) := by
  apply hom_ext
  · intro i
    have h : (-(v ^ D.d i) : k) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (NeZero.ne v))
    simp only [AlgHom.comp_apply, dualTwist_E, map_smul, dualTwist_F, smul_smul,
      mul_inv_cancel₀ h, one_smul, AlgHom.id_apply]
  · intro i
    have h : (-(v ^ D.d i) : k) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (NeZero.ne v))
    simp only [AlgHom.comp_apply, dualTwist_F, map_smul, dualTwist_E, smul_smul,
      inv_mul_cancel₀ h, one_smul, AlgHom.id_apply]
  · intro μ
    simp

theorem dualTwist_dualTwist (u : QuantumGroup R v) : dualTwist R v (dualTwist R v u) = u :=
  congrArg (fun f : QuantumGroup R v →ₐ[k] QuantumGroup R v => f u) (dualTwist_comp_dualTwist R v)

theorem dualTwist_injective : Function.Injective (dualTwist R v) :=
  Function.LeftInverse.injective (dualTwist_dualTwist R v)

theorem dualTwist_surjective : Function.Surjective (dualTwist R v) :=
  Function.RightInverse.surjective (dualTwist_dualTwist R v)

/-- **`ψ ∘ S = ρ`**: the dual twist turns the antipode into Lusztig's anti-automorphism `ρ`. -/
theorem dualTwist_antipode (u : QuantumGroup R v) :
    dualTwist R v (antipode R v u) = rho R v u := by
  have hv : v ≠ 0 := NeZero.ne v
  induction u using QuantumGroup.induction_on with
  | algebraMap c => simp
  | E i =>
    rw [antipode_E, map_neg, map_mul, dualTwist_K, dualTwist_E, neg_neg, mul_smul_comm, rho_E,
      rhoE, neg_smul, neg_neg]
  | F i =>
    rw [antipode_F, map_neg, map_mul, dualTwist_F, dualTwist_K, rho_F, rhoF, smul_mul_assoc,
      E_mul_K hv, smul_smul, ← neg_smul]
    congr 1
    have h1 : R.root i (-ktilde R i) = -(2 * (D.d i : ℤ)) := by
      rw [map_neg, root_ktilde, D.cartanMatrix_self]
      ring
    rw [h1, neg_neg, inv_neg, neg_mul, neg_neg, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hv]
    congr 1
    ring
  | K μ => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | mul x y hx hy => rw [antipode_mul, map_mul, hy, hx, rho_mul]

/-! ### Modules twisted by `ψ` -/

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- The `U`-module `M` with `u` acting as `ψ(u)`. -/
@[nolint unusedArguments]
def DualTwist (_R : D.RootDatum Y) (_v : k) (M : Type*) : Type _ := M

instance : AddCommGroup (DualTwist R v M) := inferInstanceAs (AddCommGroup M)

instance : Module k (DualTwist R v M) := inferInstanceAs (Module k M)

instance : Module (QuantumGroup R v) (DualTwist R v M) :=
  Module.compHom M (dualTwist R v).toRingHom

instance : IsScalarTower k (QuantumGroup R v) (DualTwist R v M) where
  smul_assoc c u m :=
    (congrArg (fun a : QuantumGroup R v => a • (show M from m))
      (map_smul (dualTwist R v) c u)).trans (smul_assoc c (dualTwist R v u) (show M from m))

variable {R v M}

/-- The identity map `M → DualTwist M`. -/
def DualTwist.of : M ≃ₗ[k] DualTwist R v M := LinearEquiv.refl k M

omit [IsScalarTower k (QuantumGroup R v) M] in
theorem DualTwist.smul_of (u : QuantumGroup R v) (m : M) :
    u • DualTwist.of (R := R) (v := v) m = DualTwist.of (dualTwist R v u • m) := rfl

omit [IsScalarTower k (QuantumGroup R v) M] in
theorem DualTwist.of_symm_smul (u : QuantumGroup R v) (m : DualTwist R v M) :
    DualTwist.of.symm (u • m) = dualTwist R v u • (DualTwist.of.symm m : M) := rfl

/-- The weight spaces of the twist are those of `M` with negated weights. -/
theorem DualTwist.mem_weightSpace_iff (Λ : Y →+ ℤ) (m : M) :
    DualTwist.of (R := R) (v := v) m ∈ weightSpace R v (DualTwist R v M) Λ ↔
      m ∈ weightSpace R v M (-Λ) := by
  constructor
  · intro h μ
    have := h (-μ)
    rw [DualTwist.smul_of, dualTwist_K, neg_neg] at this
    rw [AddMonoidHom.neg_apply, ← map_neg]
    exact this
  · intro h μ
    rw [DualTwist.smul_of, dualTwist_K, h (-μ), AddMonoidHom.neg_apply, map_neg, neg_neg]
    rfl

theorem DualTwist.weightSpace_eq (Λ : Y →+ ℤ) :
    weightSpace R v (DualTwist R v M) Λ =
      (weightSpace R v M (-Λ)).map (DualTwist.of (R := R) (v := v)).toLinearMap := by
  ext m
  constructor
  · intro h
    exact ⟨DualTwist.of.symm m, (DualTwist.mem_weightSpace_iff Λ _).mp h, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact (DualTwist.mem_weightSpace_iff Λ m).mpr hm

omit [IsScalarTower k (QuantumGroup R v) M] in
private theorem pow_smul_twist (a : QuantumGroup R v) (n : ℕ) (m : M) :
    a ^ n • DualTwist.of (R := R) (v := v) m =
      DualTwist.of (dualTwist R v a ^ n • m) := by
  rw [DualTwist.smul_of, map_pow]

/-- The twist of an integrable module is integrable. -/
theorem DualTwist.isIntegrable (hM : IsIntegrable R v M) :
    IsIntegrable R v (DualTwist R v M) where
  iSup_weightSpace_eq_top := by
    rw [eq_top_iff]
    intro m _
    have hm : (DualTwist.of.symm m : M) ∈ ⨆ Λ, weightSpace R v M Λ := by
      rw [hM.iSup_weightSpace_eq_top]; trivial
    have hle : ⨆ Λ, weightSpace R v M Λ ≤ (⨆ Λ, weightSpace R v (DualTwist R v M) Λ).comap
        (DualTwist.of (R := R) (v := v)).toLinearMap := by
      refine iSup_le fun Λ x hx => ?_
      refine Submodule.mem_iSup_of_mem (-Λ) ?_
      exact (DualTwist.mem_weightSpace_iff (-Λ) x).mpr (by rwa [neg_neg])
    exact hle hm
  exists_E_pow_smul_eq_zero i m := by
    obtain ⟨n, hn⟩ := hM.exists_F_pow_smul_eq_zero i (DualTwist.of.symm m)
    refine ⟨n, ?_⟩
    rw [show m = DualTwist.of (DualTwist.of.symm m) from rfl, pow_smul_twist, dualTwist_E,
      smul_pow, smul_assoc, hn, smul_zero]
    rfl
  exists_F_pow_smul_eq_zero i m := by
    obtain ⟨n, hn⟩ := hM.exists_E_pow_smul_eq_zero i (DualTwist.of.symm m)
    refine ⟨n, ?_⟩
    rw [show m = DualTwist.of (DualTwist.of.symm m) from rfl, pow_smul_twist, dualTwist_F,
      smul_pow, smul_assoc, hn, smul_zero]
    rfl

end Categorification.Stendhal.QuantumDual
