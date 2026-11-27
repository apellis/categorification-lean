/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerCorner
import Categorification.WeightedKLR.Rigidity.CupCapEndFree

/-!
# The corner of the maximum after `λ_j` as a sum of idempotent right ideals

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap after the red strand `λ_j`.
For symmetric `Q`, the corner `e T̃^{λ⁺}` of the maximum, as a left module over `T̃^{(μ,μ*)}`
acting in the window at `midPos j s`, is the direct sum `⨁_g T̃^{(μ,μ*)} e(t_g)` over the
generators `g = (s, t, d, u)` (`MidGen`): every element is uniquely `∑_g y_g γ_g` with
`y_g e(t_g) = y_g` (`midIdemSum_bijective`). The coordinates come from the bases with dots on top
(Proposition 4.16), with the reduced words of `T̃^{λ⁺}` adapted to the window (`midWord`): the
basis term of `T̃^{λ⁺}` indexed by a pair `(g, y)` is `y γ_g`, and these are exactly the basis
terms in the corner of the maximum.

Consequently the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` of `K̃` is `⨁_g L e(t_g)`
(`midModelEquiv`).

## Main results

* `CupCap.topBasisSeq_repr_midGenSum`: the coordinates of `∑_g y_g γ_g`.
* `CupCap.midIdemSum_bijective`: the corner of the maximum is `⨁_g T̃^{(μ,μ*)} e(t_g)`.
* `CupCap.midModelEquiv`: the model of `K̃` is `⨁_g L e(t_g)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

-- the `ℤ`-algebra structures used by the balanced tensor products of `InductionAlong`
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-! ### Coordinates of `y γ_g` -/

/-- A basis term whose bottom is not the loading of `g` kills `γ_g`. -/
theorem midStendhal_topTerm_mul_midGenElt_of_ne (hρ₂ : ∀ b, wordProd N (ρ₂ b) = b)
    (g : MidGen j hj ν ν₀) (y : {b // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ b}) (hy : y.1.1 ≠ g.t) :
    σ (topTerm Q Λc hρ₂ y) * midGenElt Q Λ Λc ρ₃ g = 0 := by
  rw [← midStendhal_e_mul_midGenElt (g := g), ← mul_assoc, ← map_mul, topTerm_mul_e,
    ite_eq_right_of_eq_false _ _ (eq_false hy), map_zero, zero_mul]

variable (Q Λ Λc ρ₃) in
/-- The `k`-linear map `y ↦ y γ_g`. -/
def midGenMul (g : MidGen j hj ν ν₀) : Tc →ₗ[k] Tp where
  toFun c := σ c * midGenElt Q Λ Λc ρ₃ g
  map_add' c c' := by rw [map_add, add_mul]
  map_smul' r c := by rw [map_smul, smul_mul_assoc]; rfl

theorem midGenMul_apply (g : MidGen j hj ν ν₀) (c : Tc) :
    midGenMul Q Λ Λc ρ₃ g c = σ c * midGenElt Q Λ Λc ρ₃ g := rfl

open Classical in
/-- **The coordinates of `y γ_g`** in the basis of `T̃^{λ⁺}` with dots on top: at the basis term
indexed by a pair `(g', y')` it is the coordinate of `y` at `y'` if `g = g'`, and `0` otherwise. -/
theorem topBasisSeq_repr_midGenMul (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (g : MidGen j hj ν ν₀) (c : Tc)
    (p : MidPair j hj ν ρ₂) :
    (topBasisSeq Q (plusLabels Λ Λc j hj) hQ (midWord j hj ρ₂ ρ₃)
        (midWord_spec hρ₂ hρ₃)).repr (midGenMul Q Λ Λc ρ₃ g c) (midPairIdx ρ₃ hρ₂ hρ₃ p) =
      if g = p.1.1 then (topBasis Q Λc hQ ρ₂ hρ₂).repr c p.1.2 else 0 := by
  classical
  set Bp := topBasisSeq Q (plusLabels Λ Λc j hj) hQ (midWord j hj ρ₂ ρ₃) (midWord_spec hρ₂ hρ₃)
  set Bc := topBasis Q Λc hQ ρ₂ hρ₂
  set b₀ := midPairIdx ρ₃ hρ₂ hρ₃ p
  have hb : ∀ y, Bp.repr (midGenMul Q Λ Λc ρ₃ g (Bc y)) b₀ =
      if g = p.1.1 then Bc.repr (Bc y) p.1.2 else 0 := fun y => by
    rw [topBasis_apply, midGenMul_apply]
    by_cases hy : y.1.1 = g.t
    · rw [midStendhal_topTerm_mul_midGenElt hρ₂ hρ₃ ⟨(g, y), hy⟩, ← topBasisSeq_apply hQ _
        (midWord_spec hρ₂ hρ₃), Bp.repr_self, ← topBasis_apply hQ ρ₂ hρ₂ y, Bc.repr_self,
        Finsupp.single_apply, Finsupp.single_apply]
      have hinj := midPairIdx_injective (j := j) (hj := hj) (ν := ν) (ρ₃ := ρ₃) hρ₂ hρ₃
      by_cases hg : g = p.1.1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)]
        apply if_congr _ rfl rfl
        constructor
        · intro h
          exact congrArg (fun q : MidPair j hj ν ρ₂ => q.1.2) (hinj h)
        · intro h
          exact congrArg _ (Subtype.ext (Prod.ext hg h))
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hg)]
        exact ite_eq_right_of_eq_false _ _ (eq_false fun h =>
          hg (congrArg (fun q : MidPair j hj ν ρ₂ => q.1.1) (hinj h)))
    · rw [midStendhal_topTerm_mul_midGenElt_of_ne _ g y hy, map_zero, Finsupp.coe_zero,
        Pi.zero_apply]
      split_ifs with hg
      · rw [← topBasis_apply hQ ρ₂ hρ₂ y, Bc.repr_self]
        refine (Finsupp.single_apply_eq_zero.2 fun hh => ?_).symm
        subst hg
        exact absurd (by rw [← hh]; exact p.2) hy
      · rfl
  have hext := Bc.ext (f₁ := (Bp.coord b₀).comp (midGenMul Q Λ Λc ρ₃ g))
    (f₂ := if g = p.1.1 then Bc.coord p.1.2 else 0) fun y => by
      rw [LinearMap.comp_apply, Bp.coord_apply, hb]
      split_ifs <;> rfl
  have := LinearMap.congr_fun hext c
  rw [LinearMap.comp_apply, Bp.coord_apply] at this
  rw [this]
  split_ifs <;> rfl

/-! ### The corner of the maximum as a sum of idempotent right ideals -/

variable (Q Λc) in
/-- The idempotent `e(t_g)` of a generator, in the opposite of `T̃^{(μ,μ*)}`. -/
def midGenIdem (g : MidGen j hj ν ν₀) : Tcᵐᵒᵖ := op (StendhalAlgebra.e g.t g.ht)

theorem isIdempotentElem_midGenIdem (g : MidGen j hj ν ν₀) :
    IsIdempotentElem (midGenIdem (k := k) Q Λc g) := by
  change op _ * op _ = op _
  rw [← op_mul]
  congr 1
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e _ * StendhalAlgebraAllOrders.e _ = _
  rw [StendhalAlgebraAllOrders.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

variable (Q Λ Λc ρ₃) in
/-- The generator `γ_g` as an element of the corner `e T̃^{λ⁺}`. -/
def midGenCorner (g : MidGen j hj ν ν₀) : Corner (midOp j hj Q Λ Λc ν ν₀) :=
  ⟨op (midGenElt Q Λ Λc ρ₃ g), by
    change op _ * midOp j hj Q Λ Λc ν ν₀ 1 = op _
    rw [midOp_apply, unop_one, ← op_mul, midStendhal_one_mul_midGenElt]⟩

theorem midGenIdem_smul_midGenCorner (g : MidGen j hj ν ν₀) :
    op (midGenIdem Q Λc g) • midGenCorner Q Λ Λc ρ₃ g = midGenCorner Q Λ Λc ρ₃ g := by
  apply Subtype.ext
  change op _ * op (σ _) = op _
  rw [← op_mul]
  congr 1
  exact midStendhal_e_mul_midGenElt g

/-- The sum `∑_g y_g γ_g` in `T̃^{λ⁺}`. -/
theorem unop_midIdemSum_single [DecidableEq (MidGen j hj ν ν₀)] (g : MidGen j hj ν ν₀)
    (a : BalancedTensor.idemLeft ℤ (midGenIdem (k := k) Q Λc g)) :
    unop (BalancedTensor.idemSum ℤ (Corner (midOp j hj Q Λ Λc ν ν₀)) (midGenIdem Q Λc)
        (midGenCorner Q Λ Λc ρ₃) (DFinsupp.single g a)).1 =
      midGenMul Q Λ Λc ρ₃ g (unop (a : Tcᵐᵒᵖ)) := by
  rw [BalancedTensor.idemSum_single]
  rfl

/-- **The coordinates of `∑_g y_g γ_g`**: at the basis term indexed by `(g, y)` it is the
coordinate of `y_g` at `y`. -/
theorem topBasisSeq_repr_midGenSum [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (a : Π₀ g : MidGen j hj ν ν₀, BalancedTensor.idemLeft ℤ (midGenIdem (k := k) Q Λc g))
    (p : MidPair j hj ν ρ₂) :
    (topBasisSeq Q (plusLabels Λ Λc j hj) hQ (midWord j hj ρ₂ ρ₃) (midWord_spec hρ₂ hρ₃)).repr
        (unop (BalancedTensor.idemSum ℤ (Corner (midOp j hj Q Λ Λc ν ν₀)) (midGenIdem Q Λc)
          (midGenCorner Q Λ Λc ρ₃) a).1) (midPairIdx ρ₃ hρ₂ hρ₃ p) =
      (topBasis Q Λc hQ ρ₂ hρ₂).repr (unop ((a p.1.1 : Tcᵐᵒᵖ))) p.1.2 := by
  classical
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha g b f _ _ ih =>
    rw [map_add, Submodule.coe_add, unop_add, map_add, Finsupp.add_apply, ih,
      unop_midIdemSum_single, topBasisSeq_repr_midGenMul hQ hρ₂ hρ₃, DFinsupp.add_apply,
      Submodule.coe_add, unop_add, map_add, Finsupp.add_apply]
    congr 1
    by_cases hg : g = p.1.1
    · subst hg
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), DFinsupp.single_eq_same]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hg), DFinsupp.single_eq_of_ne (Ne.symm hg)]
      simp

/-- **The corner of the maximum of `T̃^{λ⁺}` is `⨁_g T̃^{(μ,μ*)} e(t_g)`** (arXiv:1309.3796v3,
proof of Lemma 7.17, for symmetric `Q`): every element of `e T̃^{λ⁺}` is uniquely `∑_g y_g γ_g`
with `y_g e(t_g) = y_g`. -/
theorem midIdemSum_bijective [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Bijective (BalancedTensor.idemSum ℤ (Corner (midOp j hj Q Λ Λc ν ν₀))
      (midGenIdem (k := k) Q Λc) (midGenCorner Q Λ Λc ρ₃)) := by
  classical
  set Bp := topBasisSeq Q (plusLabels Λ Λc j hj) hQ (midWord j hj ρ₂ ρ₃) (midWord_spec hρ₂ hρ₃)
  set Bc := topBasis Q Λc hQ ρ₂ hρ₂
  constructor
  · intro a a' h
    refine DFinsupp.ext fun g => Subtype.ext (unop_injective (Bc.ext_elem fun y => ?_))
    by_cases hy : y.1.1 = g.t
    · have h₁ := topBasisSeq_repr_midGenSum (Λ := Λ) hQ hρ₂ hρ₃ a ⟨(g, y), hy⟩
      have h₂ := topBasisSeq_repr_midGenSum (Λ := Λ) hQ hρ₂ hρ₃ a' ⟨(g, y), hy⟩
      rw [h] at h₁
      exact h₁.symm.trans h₂
    · have hz : ∀ c : BalancedTensor.idemLeft ℤ (midGenIdem (k := k) Q Λc g),
          Bc.repr (unop (c : Tcᵐᵒᵖ)) y = 0 := fun c => by
        have hc : unop (c : Tcᵐᵒᵖ) * StendhalAlgebra.e g.t g.ht = unop (c : Tcᵐᵒᵖ) :=
          congrArg unop c.2
        rw [← hc, topBasis_repr_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hy)]
      rw [hz, hz]
  · intro z
    have hz : σ 1 * unop z.1 = unop z.1 := congrArg unop z.2
    let Ψ : (Π₀ g : MidGen j hj ν ν₀, BalancedTensor.idemLeft ℤ (midGenIdem (k := k) Q Λc g)) →+
        Tp :=
      (opAddEquiv.symm : Tpᵐᵒᵖ ≃+ Tp).toAddMonoidHom.comp
        ((Submodule.subtype _).toAddMonoidHom.comp
          (BalancedTensor.idemSum ℤ (Corner (midOp j hj Q Λ Λc ν ν₀)) (midGenIdem (k := k) Q Λc)
            (midGenCorner Q Λ Λc ρ₃)).toAddMonoidHom)
    have hΨ : ∀ a, Ψ a = unop (BalancedTensor.idemSum ℤ (Corner (midOp j hj Q Λ Λc ν ν₀))
        (midGenIdem (k := k) Q Λc) (midGenCorner Q Λ Λc ρ₃) a).1 := fun _ => rfl
    suffices hmem : unop z.1 ∈ AddMonoidHom.mrange Ψ by
      obtain ⟨a, ha⟩ := AddMonoidHom.mem_mrange.1 hmem
      exact ⟨a, Subtype.ext (unop_injective ((hΨ a).symm.trans ha))⟩
    have hexp : unop z.1 = ∑ b ∈ (Bp.repr (unop z.1)).support,
        Bp.repr (unop z.1) b • (σ 1 * Bp b) := by
      conv_lhs => rw [← hz, ← Bp.linearCombination_repr (unop z.1)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => mul_smul_comm _ _ _
    rw [hexp]
    refine AddSubmonoid.sum_mem _ fun b _ => ?_
    rw [topBasisSeq_apply, midStendhal_one_mul_topTermSeq]
    split_ifs with hb
    · obtain ⟨p, rfl⟩ := exists_midPairIdx ρ₂ ρ₃ hρ₂ hρ₃ b hb
      set r := Bp.repr (unop z.1) (midPairIdx ρ₃ hρ₂ hρ₃ p)
      have hmemL : op (r • topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2) ∈
          BalancedTensor.idemLeft ℤ (midGenIdem (k := k) Q Λc p.1.1) := by
        change op _ * op _ = op _
        rw [← op_mul, smul_mul_assoc, topTerm_mul_e, ite_eq_left_of_eq_true _ _ (eq_true p.2)]
      refine AddMonoidHom.mem_mrange.2 ⟨DFinsupp.single p.1.1 ⟨_, hmemL⟩, ?_⟩
      rw [hΨ, unop_midIdemSum_single, midGenMul_apply]
      change σ (r • _) * _ = _
      rw [map_smul, smul_mul_assoc, midStendhal_topTerm_mul_midGenElt hρ₂ hρ₃ p]
    · rw [smul_zero]
      exact AddSubmonoid.zero_mem _

/-! ### The model of `K̃` -/

variable (j hj Q Λ Λc ν ν₀ ρ₃) in
variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- **The model of `K̃` for a cap after `λ_j` is `⨁_g L e(t_g)`** (arXiv:1309.3796v3, proof of
Lemma 7.17, for symmetric `Q`): `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺} ≅ ⨁_g L e(t_g)` over the generators
`g = (s, t, d, u)`, `ℓ' γ_g ↦ (ℓ')_g`. -/
def midModelEquiv [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    MidModel j hj Q Λ Λc ν ν₀ L ≃ₗ[ℤ] Π₀ g : MidGen j hj ν ν₀, BalancedTensor.idemPart ℤ L
      (midGenIdem (k := k) Q Λc g) :=
  BalancedTensor.idemEquiv (B := Tpᵐᵒᵖ) isIdempotentElem_midGenIdem
    (midGenIdem_smul_midGenCorner (ρ₃ := ρ₃)) (midIdemSum_bijective hQ hρ₂ hρ₃)

end Categorification.Stendhal.CupCap
