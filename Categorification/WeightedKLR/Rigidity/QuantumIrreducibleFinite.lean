/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumTracePairing

/-!
# Finite-dimensionality of `V_μ` in finite type

Input for the coevaluation `coev_μ` of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, §7.1 (the canonical element of the pairing of `V_μ` with `V_{μ*}`),
where `g` is finite-dimensional.

The weights of `L_q(Λ)` lie in `Λ - ℕ[I]` (`irreducible_weightSpace_eq_bot`). The map
`Θ : V_{μ*} → V_μ` (`QuantumDual.twistLowestLinear`) sends the weight `μ* - γ` to `γ - μ*` and is
injective; since `γ - μ* = μ - β + γ` for the content `β` of `w₀`, nonzero weight spaces of
`V_{μ*}` occur only for `γ ≤ β` (`dual_weightSpace_eq_bot`). Hence `V_{μ*}` is a finite sum of
finite-dimensional weight spaces (`finiteDimensional_dualIrreducible`), and so is `V_μ ≅ V_{μ*}`
(`finiteDimensional_irreducible`). The argument is standard; the formulation is ours.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module

section Weights

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

/-- **The weights of `L_q(Λ)` lie in `Λ - ℕ[I]`.** -/
theorem irreducible_weightSpace_eq_bot (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ Λ' : Y →+ ℤ}
    (h : ∀ δ, Λ' ≠ Λ - R.rootSum δ) :
    weightSpace R v (IrreducibleModule R v Λ) Λ' = ⊥ := by
  refine le_bot_iff.mp ((weightSpace_quotient_le_map hv' VermaModule.iSup_weightSpace_eq_top
    (VermaModule.maxSubmodule R v Λ) Λ').trans ?_)
  rw [VermaModule.weightSpace_eq_bot hv' h, Submodule.map_bot]

end Weights

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

include hR hdom hm hw hlong

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "Θ" => twistLowestLinear P hR μ weight hdom hm w hw hlong
local notation "β" => lowestContent P weight w

/-- `Θ` sends the weight `Λ` of `V_{μ*}` to the weight `-Λ` of `V_μ`. -/
theorem twistLowestLinear_mem_weightSpace {Λ : Y →+ ℤ} {y : Vμs}
    (hy : y ∈ weightSpace R vQ Vμs Λ) : Θ y ∈ weightSpace R vQ Vμ (-Λ) := by
  have h : twistLowest P hR μ weight hdom hm w hw hlong y ∈
      weightSpace R vQ (DualTwist R vQ Vμ) Λ := fun ν => by
    rw [← LinearMap.map_smul, hy ν, LinearMap.map_smul_of_tower]
  exact (DualTwist.mem_weightSpace_iff Λ _).mp h

/-- The weight spaces `μ* - γ` of `V_{μ*}` vanish unless `γ ≤ β`. -/
theorem dual_weightSpace_eq_bot {γ : I →₀ ℕ} (hγ : ¬ γ ≤ β) :
    weightSpace R vQ Vμs (μs.1 - R.rootSum γ) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  by_contra hne
  have hΘ := twistLowestLinear_mem_weightSpace P hR μ weight hdom hm w hw hlong hy
  have hΘ0 : Θ y ≠ 0 := fun h0 =>
    hne (twistLowestLinear_injective P hR μ weight hdom hm w hw hlong (h0.trans (map_zero _).symm))
  have hex : ∃ δ, -(μs.1 - R.rootSum γ) = μ.1 - R.rootSum δ := by
    by_contra! hall
    have hb := irreducible_weightSpace_eq_bot (R := R) (v := vQ) hvn_ratFunc
      (Λ := μ.1) hall
    rw [hb] at hΘ
    exact hΘ0 ((Submodule.mem_bot _).mp hΘ)
  obtain ⟨δ, hδ⟩ := hex
  have hsum : R.rootSum (γ + δ) = R.rootSum β := by
    rw [dualWeight_val] at hδ
    have h2 := congrArg (fun z => μ.1 - z) hδ
    simp only [sub_neg_eq_add, sub_sub_cancel] at h2
    rw [R.rootSum_add, ← h2]
    abel
  have heq : γ + δ = β := by
    by_contra hne'
    obtain ⟨ν, hν⟩ := R.exists_rootSum_ne hR hne'
    exact hν (by rw [hsum])
  exact hγ (heq ▸ le_self_add)

/-- **`V_{μ*}` is finite-dimensional** (finite type). -/
theorem finiteDimensional_dualIrreducible : FiniteDimensional 𝕂 Vμs := by
  have hint :=
    (IrreducibleModule.isIntegrable hR hvn_ratFunc (v := vQ) μs.2).iSup_weightSpace_eq_top
  let S : (Finset.Iic β) → Submodule 𝕂 Vμs := fun γ => weightSpace R vQ Vμs (μs.1 - R.rootSum γ.1)
  have hfin : ∀ γ, FiniteDimensional 𝕂 (S γ) := fun γ =>
    IrreducibleModule.finiteDimensional_weightSpace hR hvn_ratFunc _
  have htop : (⊤ : Submodule 𝕂 Vμs) ≤ (⨆ γ, S γ : Submodule 𝕂 Vμs) := by
    rw [← hint]
    refine iSup_le fun Λ => ?_
    by_cases hΛ : ∃ γ, Λ = μs.1 - R.rootSum γ
    · obtain ⟨γ, rfl⟩ := hΛ
      by_cases hγ : γ ≤ β
      · exact le_iSup_of_le ⟨γ, Finset.mem_Iic.mpr hγ⟩ le_rfl
      · rw [dual_weightSpace_eq_bot P hR μ weight hdom hm w hw hlong hγ]
        exact bot_le
    · simp only [not_exists] at hΛ
      rw [irreducible_weightSpace_eq_bot hvn_ratFunc hΛ]
      exact bot_le
  have : FiniteDimensional 𝕂 (⨆ γ, S γ : Submodule 𝕂 Vμs) := Submodule.finiteDimensional_iSup S
  have h : (⨆ γ, S γ : Submodule 𝕂 Vμs) = ⊤ := top_le_iff.mp htop
  rw [h] at this
  exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl)

/-- **`V_μ` is finite-dimensional** (finite type). -/
theorem finiteDimensional_irreducible : FiniteDimensional 𝕂 Vμ := by
  have := finiteDimensional_dualIrreducible P hR μ weight hdom hm w hw hlong
  exact Module.Finite.equiv (twistLowestEquiv P hR μ weight hdom hm w hw hlong)

end Categorification.Stendhal.QuantumDual
