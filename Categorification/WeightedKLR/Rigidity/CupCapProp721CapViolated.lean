/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendQuot

/-!
# `K^{λ⁺}_λ` as the model modulo its bottom-violated part

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap after `λ_j`. Under the isomorphism `K̃^{λ⁺}_λ ≅ L ⊗ e T̃^{λ⁺}` of
Lemma 7.17 (`CupCap.midCapModelEquiv`), the violated diagrams of `K̃^{λ⁺}_λ` correspond to the
bottom-violated part `model · V_{λ⁺}` of the model (`CupCap.map_midCapModelEquiv_violated`):
the diagrams violated above the cap act through diagrams violated below it
(`CupCap.midLeftAlg_mem_midBotViolSub`). Hence `K^{λ⁺}_λ` is the model modulo `model · V_{λ⁺}`
(`CupCap.capModelQuotEquiv`). This is the form of `K^{λ⁺}_λ` that `𝔉_i` acts on through the
right action of `T̃^{λ⁺}` (`CupCap.appendViolQuotEquiv`).

## Main definitions

* `CupCap.midBotViolEnv`: `model · V_{λ⁺}` as a sub-bimodule.
* `CupCap.capModelQuotEquiv`: `K^{λ⁺}_λ ≅ model / model · V_{λ⁺}`.

## Main results

* `CupCap.map_midCapModelEquiv_violated`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "Ev" => Env k Q Λ Λc j hj ν ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L

/-- The action of `T̃^λ` preserves the bottom-violated part. -/
theorem midLeftAlg_mem_midBotViolSub_of_mem (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (a : StendhalAlgebra k Q Λ ν) {y : MidModel j hj Q Λ Λc ν ν₀ L} (hy : y ∈ BV) :
    midLeftAlg L hL hR a y ∈ BV := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, w, rfl⟩ := hx
    rw [midLeftAlg_smul]
    exact op_smul_mem_midBotViolSub ν L hb _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [midLeftAlg_smul]; exact Submodule.smul_mem _ r hx

/-- The bimodule action preserves the bottom-violated part. -/
theorem midEnvAlg_mem_midBotViolSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (r : Ev)
    {y : MidModel j hj Q Λ Λc ν ν₀ L} (hy : y ∈ BV) : midEnvAlg L hL hR r y ∈ BV := by
  induction r using TensorProduct.inductionOn with
  | tmul a c =>
    have h := midEnvAlg_mk hR a (unop c) y
    change midEnvAlg L hL hR (Env.mk a (unop c)) y ∈ _
    rw [h]
    exact midLeftAlg_mem_midBotViolSub_of_mem hR a (Submodule.smul_mem _ _ hy)
  | add r r' hr hr' =>
    refine (congrArg (· ∈ BV) (LinearMap.congr_fun (map_add (midEnvAlg L hL hR) r r') y)).mpr ?_
    rw [LinearMap.add_apply]
    exact add_mem hr hr'

variable (L hL) in
/-- **The bottom-violated part `model · V_{λ⁺}` as a sub-bimodule** of the model. -/
def midBotViolEnv (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Submodule Ev (MidBimod L hL hR) where
  carrier := {y | ofMidBimod L hL hR y ∈ BV}
  add_mem' {_ _} hx hy := (BV).add_mem hx hy
  zero_mem' := (BV).zero_mem
  smul_mem' r _ hy := midEnvAlg_mem_midBotViolSub hR r hy

theorem mem_midBotViolEnv (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (y : MidBimod L hL hR) :
    y ∈ midBotViolEnv L hL hR ↔ ofMidBimod L hL hR y ∈ BV := Iff.rfl

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)

/-- **The violated diagrams of `K̃^{λ⁺}_λ` are the bottom-violated part of the model**
(arXiv:1309.3796v3, §7.3), under the isomorphism of Lemma 7.17. -/
theorem map_midCapModelEquiv_violated :
    (violated k Q Λ Λc j hj ν ν₀ L).map (midCapModelEquiv hP hPL hκ hR).toLinearMap =
      midBotViolEnv L hL hR := by
  set E := midCapModelEquiv hP hPL hκ hR
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ (⟨a, ha, y, rfl⟩ | ⟨b, hb, y, rfl⟩)
    · change E (Env.mk a 1 • y) ∈ midBotViolEnv L hL hR
      rw [map_smul, mem_midBotViolEnv]
      have h := midEnvAlg_mk hR a 1 (ofMidBimod L hL hR (E y))
      change midEnvAlg L hL hR (Env.mk a 1) (ofMidBimod L hL hR (E y)) ∈ BV
      rw [h, op_one, one_smul]
      exact midLeftAlg_mem_midBotViolSub ν hL hR ha _
    · change E (Env.mk 1 b • y) ∈ midBotViolEnv L hL hR
      rw [map_smul, mem_midBotViolEnv]
      have h := midEnvAlg_mk hR 1 b (ofMidBimod L hL hR (E y))
      change midEnvAlg L hL hR (Env.mk 1 b) (ofMidBimod L hL hR (E y)) ∈ BV
      rw [h, map_one, Module.End.one_apply]
      exact op_smul_mem_midBotViolSub ν L hb _
  · intro y hy
    rw [mem_midBotViolEnv] at hy
    change toMidBimod L hL hR (ofMidBimod L hL hR y) ∈ _
    generalize ofMidBimod L hL hR y = x at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, w, rfl⟩ := hx
      refine ⟨Env.mk 1 b • E.symm (toMidBimod L hL hR w),
        Submodule.subset_span (Or.inr ⟨b, hb, _, rfl⟩), ?_⟩
      change E (Env.mk 1 b • E.symm (toMidBimod L hL hR w)) = _
      rw [map_smul, LinearEquiv.apply_symm_apply]
      have h := midEnvAlg_mk hR 1 b w
      rw [map_one, Module.End.one_apply] at h
      exact h
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      have h := Submodule.smul_mem _ (Env.mk 1 (unop r) : Ev) hx
      have h2 := midEnvAlg_mk hR 1 (unop r) x
      rw [map_one, Module.End.one_apply, op_unop] at h2
      change midEnvAlg L hL hR (Env.mk 1 (unop r)) x ∈ _ at h
      rw [h2] at h
      exact h

/-- **`K^{λ⁺}_λ` is the model modulo its bottom-violated part** (arXiv:1309.3796v3, §7.3), for a
cap after `λ_j`, under the hypotheses of Lemma 7.17. -/
def capModelQuotEquiv :
    Cap k Q Λ Λc j hj ν ν₀ L ≃ₗ[Ev] MidBimod L hL hR ⧸ midBotViolEnv L hL hR :=
  Submodule.Quotient.equiv _ _ (midCapModelEquiv hP hPL hκ hR)
    (map_midCapModelEquiv_violated hP hPL hκ hR)

theorem capModelQuotEquiv_mk (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    capModelQuotEquiv hP hPL hκ hR (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (midCapModelEquiv hP hPL hκ hR y) := rfl

end Categorification.Stendhal.CupCap
