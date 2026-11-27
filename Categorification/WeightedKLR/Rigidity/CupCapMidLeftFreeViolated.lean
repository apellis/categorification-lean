/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeBijective
import Categorification.WeightedKLR.Rigidity.CupCapMidTripleBasis

/-!
# Bottom violation lies in top violation, for a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module. In the model of `K̃^{λ⁺}_λ` with the left action of `T̃^λ`, let
`V_λ K̃` be the `T̃^λ`-span of the elements `a · y` with `a` in the violating ideal of `T̃^λ`.
Every element `y · b` with `b` in the violating ideal of `T̃^{λ⁺}` lies in `V_λ K̃`
(`op_smul_mem_midViolatedSub`).

The argument uses the surjectivity of the comparison map `Θ` over the block shuffles: the model
is spanned over `T̃^λ` by the block generators `v γ_g`, and `γ_g · e(i)` is zero unless `i` is
the bottom of `g`. If the bottom of a block generator with `t_g` cap-good is violated, so is its
top `s_g` (`MidTriple.isViolated_of_isViolated_bot`): the strands keep their order, and the
first strand at the maximum is the red `μ`. So `γ_g · e(i) = e(s_g) · γ_g · e(i)` lies in
`V_λ K̃`. For `t_g` not cap-good the piece `L e(t_g)` vanishes.

Route hypotheses, as for the surjectivity of `Θ`: the cup scalars are units and `L` satisfies
the pull-off identity.

## Main definitions

* `midViolatedSub`: the `T̃^λ`-span of the top-violated elements of the model.

## Main results

* `MidTriple.isViolated_of_isViolated_bot`: a violated bottom of a triple has a violated top.
* `op_smul_mem_midViolatedSub`: bottom-violated elements of the model are top-violated.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

/-- **A violated bottom of a triple has a violated top**: the strands of `i` and of `t` keep
their order at the bottom, and the first strand of `t` is the red `μ`, so a black leftmost
bottom strand is the leftmost strand of `i`. -/
theorem MidTriple.isViolated_of_isViolated_bot (τ : MidTriple ℓ j ν ν₀)
    (h : IsViolated (MidTriple.toGen (hj := hj) τ).1.bot) : IsViolated τ.i := by
  obtain ⟨h0, hb⟩ := h
  obtain ⟨p, hp⟩ := τ.ε.surjective ⟨0, h0⟩
  have hlbl : ∀ x, (MidTriple.toGen (hj := hj) τ).1.bot.lbl x =
      (τ.u⁻¹ • midSeq j hj (τ.w • τ.i) τ.t).lbl x := fun _ => rfl
  rw [hlbl, ← hp] at hb
  rcases p with a | q
  · rw [bot_lbl_inl τ.u_inl, inv_smul_smul] at hb
    have ha : a.val = 0 := by
      by_contra hne
      have : τ.ε (.inl ⟨0, by omega⟩) < τ.ε (.inl a) :=
        τ.hε.1 (show (⟨0, by omega⟩ : Fin m) < a from Fin.mk_lt_of_lt_val (by omega))
      rw [hp] at this
      exact absurd (Fin.lt_def.1 this) (Nat.not_lt_zero _)
    refine ⟨by omega, ?_⟩
    have ha' : a = ⟨0, by omega⟩ := Fin.ext ha
    rw [← ha']
    rcases hc : τ.i.lbl a with c | c <;> rw [hc] at hb
    · rfl
    · exact absurd hb (by simp)
  · rw [bot_lbl_inr τ.u_inr] at hb
    have hN := two_le_card_stendhalWeight ν₀
    have hq : q.val = 0 := by
      by_contra hne
      have : τ.ε (.inr ⟨0, by omega⟩) < τ.ε (.inr q) :=
        τ.hε.2.1 (show (⟨0, by omega⟩ : Fin N) < q from Fin.mk_lt_of_lt_val (by omega))
      rw [hp] at this
      exact absurd (Fin.lt_def.1 this) (Nat.not_lt_zero _)
    have hq' : q = ⟨0, by omega⟩ := Fin.ext hq
    rw [hq', τ.hcap.1] at hb
    exact absurd hb (by simp)

/-- **A violated bottom of a block shuffle has a violated top**, when `t` is cap-good. -/
theorem MidBlockShuffle.isViolated_s_of_isViolated_bot (b : MidBlockShuffle j hj ν ν₀)
    (hcap : IsCapGood ν₀ b.1.1.t) (h : IsViolated b.1.1.bot) : IsViolated b.1.1.s := by
  set τ := (midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩
  have hg : (MidTriple.toGen (hj := hj) τ).1 = b.1.1 :=
    congrArg Subtype.val ((midTripleEquiv j hj ν ν₀).apply_symm_apply ⟨b.1.1, hcap⟩)
  have hi := τ.isViolated_of_isViolated_bot (hj := hj) (by rw [hg]; exact h)
  rwa [(midTripleEquiv_symm_block b hcap).1] at hi

variable [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "V" => StendhalAlgebra.violatedIdeal k Q Λ ν

/-- The idempotent `e(i)` of `T̃^{λ⁺}` kills a generator `γ_g` from the right unless `i` is its
bottom. -/
theorem midGenElt_mul_e_of_ne
    {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (g : MidGen j hj ν ν₀)
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hi : IsRedOrdered i) (hne : g.bot ≠ i) :
    midGenElt Q Λ Λc ρ₃ g * StendhalAlgebra.e (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj) i hi =
      0 := by
  rw [← topMap_e_of_isRedOrdered (Λ := plusLabels Λ Λc j hj) i hi, midGenElt, midGenKLR]
  change topMap k Q (plusLabels Λ Λc j hj) (ν + ν₀) _ * _ = 0
  rw [← map_mul, mul_assoc, KLRAlgebra.e_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hne),
    mul_zero, map_zero]

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

variable (L hL) in
/-- **The top-violated part `V_λ K̃` of the model**: the `T̃^λ`-span of the elements `a · y`
with `a` in the violating ideal of `T̃^λ`. -/
def midViolatedSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Submodule T (MidLeftModel L hL hR) :=
  Submodule.span T {z | ∃ a ∈ V, ∃ y : MidLeftModel L hL hR, z = a • y}

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem smul_mem_midViolatedSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) {a : T} (ha : a ∈ V)
    (y : MidLeftModel L hL hR) : a • y ∈ midViolatedSub L hL hR :=
  Submodule.subset_span ⟨a, ha, y, rfl⟩

/-- The right action of `T̃^{λ⁺}` on the model with its left action. -/
instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Module Tpᵐᵒᵖ (MidLeftModel L hL hR) :=
  inferInstanceAs (Module Tpᵐᵒᵖ (MidModel j hj Q Λ Λc ν ν₀ L))

variable (L hL) in
/-- The right action of `T̃^{λ⁺}` on the model, as a left `T̃^λ`-linear map. -/
def midRightLin (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (b : Tpᵐᵒᵖ) :
    MidLeftModel L hL hR →ₗ[T] MidLeftModel L hL hR where
  toFun y := b • y
  map_add' y y' := smul_add b y y'
  map_smul' a y := (midLeftAlg_smul hR a b y).symm

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem midRightLin_apply (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (b : Tpᵐᵒᵖ)
    (y : MidLeftModel L hL hR) :
    midRightLin L hL hR b y = b • y := rfl

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- `V_λ K̃` is stable under the right action of `T̃^{λ⁺}`. -/
theorem midRightLin_mem_midViolatedSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (b : Tpᵐᵒᵖ)
    {y : MidLeftModel L hL hR} (hy : y ∈ midViolatedSub L hL hR) :
    midRightLin L hL hR b y ∈ midViolatedSub L hL hR := by
  have : (midViolatedSub L hL hR).map (midRightLin L hL hR b) ≤ midViolatedSub L hL hR := by
    rw [midViolatedSub, Submodule.map_span_le]
    rintro _ ⟨a, ha, y, rfl⟩
    rw [map_smul]
    exact smul_mem_midViolatedSub hR ha _
  exact this (Submodule.mem_map_of_mem hy)

variable {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-- `γ_g · e(i)` lies in `V_λ K̃` for a block generator and a violated `i`. -/
theorem midRightLin_e_tmul_mem (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hi : IsRedOrdered i) (hv : IsViolated i)
    (b : MidBlockShuffle j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc b.1.1)) :
    midRightLin L hL hR (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj) i hi))
      (Ind.tmul (midGenCorner Q Λ Λc ρ₃ b.1.1) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L) ∈
        midViolatedSub L hL hR := by
  by_cases hcap : IsCapGood ν₀ b.1.1.t
  · by_cases hb : b.1.1.bot = i
    · subst hb
      have hs := MidBlockShuffle.isViolated_s_of_isViolated_bot b hcap hv
      rw [← midLeftAlg_e_tmul_midGenCorner hR b.1.1 (v : L)]
      have := smul_mem_midViolatedSub hR
        (TwoSidedIdeal.subset_span ⟨b.1.1.s, b.1.1.hs, hs, rfl⟩ :
          StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs ∈ V)
        (midRightLin L hL hR (op (StendhalAlgebra.e (k := k) (Q := Q)
          (Λ := plusLabels Λ Λc j hj) b.1.1.bot hi))
          (Ind.tmul (midGenCorner Q Λ Λc ρ₃ b.1.1) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L))
      rwa [← map_smul] at this
    · rw [midRightLin_apply]
      change (op _ : Tpᵐᵒᵖ) • (Ind.tmul (midGenCorner Q Λ Λc ρ₃ b.1.1) (v : L) :
        MidModel j hj Q Λ Λc ν ν₀ L) ∈ _
      rw [midGenCorner_eq_midGen, op_smul_tmul_midGen, midGenElt_mul_e_of_ne _ _ _ hb,
        tmul_midGen_zero]
      exact zero_mem _
  · have hv0 : (v : L) = 0 := by
      have h := idemPart_eq_bot_of_not_isCapGood L hL b.1.1.t b.1.1.ht hcap
      have hmem : (v : L) ∈ BalancedTensor.idemPart k L
          (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) b.1.1.t b.1.1.ht)) := v.2
      rw [h] at hmem
      exact hmem
    rw [hv0, Ind.tmul_zero, map_zero]
    exact zero_mem _

/-- **`y · e(i)` lies in `V_λ K̃` for a violated `i`**, by the surjectivity of `Θ`. -/
theorem midRightLin_e_mem (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hi : IsRedOrdered i) (hv : IsViolated i)
    (y : MidLeftModel L hL hR) :
    midRightLin L hL hR (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj) i hi))
      y ∈ midViolatedSub L hL hR := by
  classical
  obtain ⟨x, rfl⟩ := midThetaBlock_surjective hR ρ₃ hρ₃ hP hκ y
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x x' hx hx' => rw [map_add, map_add]; exact add_mem hx hx'
  | of b x =>
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => rw [map_add, map_add, map_add]; exact add_mem hx hx'
    | tmul a v =>
      have h := midThetaBlock_lof (ρ₃ := ρ₃) (L := L) (hL := hL)
        (Q := Q) (Λ := Λ) (Λc := Λc) hR b (a ⊗ₜ v)
      change midRightLin L hL hR _ (midThetaBlock L hL ρ₃ hR (DirectSum.lof T _
        (fun g => MidLeftSummand Q Λ Λc L g.1) b (a ⊗ₜ v))) ∈ _
      rw [h, midTheta_of_tmul]
      change midRightLin L hL hR _ ((a : T) • midLeftGen L hL ρ₃ hR b.1 v) ∈ _
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      rw [midLeftGen_apply]
      exact midRightLin_e_tmul_mem hR i hi hv b v

/-- **Bottom violation lies in top violation** (arXiv:1309.3796v3, §7.3, after Lemma 7.19):
for `b` in the violating ideal of `T̃^{λ⁺}`, every `y · b` lies in `V_λ K̃`. -/
theorem op_smul_mem_midViolatedSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    {b : Tp} (hb : b ∈ StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀))
    (y : MidLeftModel L hL hR) :
    midRightLin L hL hR (op b) y ∈ midViolatedSub L hL hR := by
  induction hb using TwoSidedIdeal.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨i, hi, hv, rfl⟩ := hx
    exact midRightLin_e_mem hR hρ₃ hP hκ i hi hv y
  | zero =>
    have h0 : midRightLin L hL hR (op 0) y = 0 := by
      rw [midRightLin_apply, op_zero]
      exact zero_smul Tpᵐᵒᵖ y
    rw [h0]
    exact zero_mem _
  | add x x' _ _ hx hx' =>
    rw [midRightLin_apply, op_add, add_smul]
    exact add_mem (hx y) (hx' y)
  | neg x _ hx =>
    rw [midRightLin_apply, op_neg, neg_smul]
    exact neg_mem (hx y)
  | left_absorb a x _ hx =>
    rw [midRightLin_apply, op_mul, mul_smul]
    exact hx _
  | right_absorb c x _ hx =>
    rw [midRightLin_apply, op_mul, mul_smul]
    exact midRightLin_mem_midViolatedSub hR (op c) (hx y)

end Categorification.Stendhal.CupCap
