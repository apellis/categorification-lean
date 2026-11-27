/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndCorner

/-!
# The end corner of `T̃^{λ⁺}` as a sum of idempotent right ideals

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. For symmetric `Q`,
the corner `e T̃^{λ⁺}` of the end block, as a left module over `T̃^{(μ,μ*)}` acting at the
maximum on the last `N` strands, is the direct sum `⨁_g T̃^{(μ,μ*)} e(j_g)` over the generators
`g = (x, j, u)` (`EndGen`): every element is uniquely `∑_g y_g γ_g` with `y_g e(j_g) = y_g`
(`endIdemSum_bijective`). The coordinates come from the bases with dots on top
(Proposition 4.16): the basis term of `T̃^{λ⁺}` indexed by a pair `(g, y)` is `y γ_g`, and these
are exactly the basis terms in the end corner.

Consequently the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` of `K̃` is `⨁_g L e(j_g)`
(`endModelEquiv`).

## Main results

* `topTerm_mul_e`, `topBasis_repr_mul_e`: right multiplication by an idempotent on the basis.
* `topBasis_repr_genSum`: the coordinates of `∑_g y_g γ_g`.
* `endIdemSum_bijective`: the end corner is `⨁_g T̃^{(μ,μ*)} e(j_g)`.
* `endModelEquiv`: the model of `K̃` is `⨁_g L e(j_g)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

-- the `ℤ`-algebra structures used by the balanced tensor products of `InductionAlong`
attribute [local instance 1200] Ring.toIntAlgebra

section Idempotent

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- Right multiplication by `e(j)` keeps the basis terms with bottom `j`. -/
theorem topTerm_mul_e {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : ∀ w, wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    (y : {b // IsTopTerm ρ b}) (j : Seq (stendhalWeight ℓ ν)) (hj : IsRedOrdered j) :
    topTerm Q Λ hρ y * StendhalAlgebra.e j hj = if y.1.1 = j then topTerm Q Λ hρ y else 0 := by
  apply Subtype.ext
  change ofKLR k Q Λ ν (topElt ρ y.1) * ofKLR k Q Λ ν (KLRAlgebra.e j) = _
  rw [← map_mul, topElt, mul_assoc, KLRAlgebra.e_mul_e]
  split_ifs with h
  · rfl
  · rw [mul_zero, map_zero]; rfl

/-- The coordinates of `c e(j)` in the basis with dots on top. -/
theorem topBasis_repr_mul_e (hQ : KLRSymm Q)
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    (c : StendhalAlgebra k Q Λ ν) (j : Seq (stendhalWeight ℓ ν)) (hj : IsRedOrdered j)
    (y : {b // IsTopTerm ρ b}) :
    (topBasis Q Λ hQ ρ hρ).repr (c * StendhalAlgebra.e j hj) y =
      if y.1.1 = j then (topBasis Q Λ hQ ρ hρ).repr c y else 0 := by
  set B := topBasis Q Λ hQ ρ hρ
  have hb : ∀ y', B.repr (B y' * StendhalAlgebra.e j hj) y =
      if y.1.1 = j then B.repr (B y') y else 0 := fun y' => by
    rw [topBasis_apply, topTerm_mul_e, ← topBasis_apply hQ ρ hρ]
    by_cases h' : y'.1.1 = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h')]
      by_cases h : y.1.1 = j
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h), B.repr_self,
          Finsupp.single_apply_eq_zero.2 fun hh => (h (by rw [hh]; exact h')).elim]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h'), map_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with h
      · rw [B.repr_self, Finsupp.single_apply_eq_zero.2 fun hh => (h' (by rw [← hh]; exact h)).elim]
      · rfl
  have hext := B.ext (f₁ := (B.coord y).comp (LinearMap.mulRight k (StendhalAlgebra.e j hj)))
    (f₂ := if y.1.1 = j then B.coord y else 0) fun y' => by
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, B.coord_apply, hb]
      split_ifs <;> rfl
  have := LinearMap.congr_fun hext c
  rw [LinearMap.comp_apply, LinearMap.mulRight_apply, B.coord_apply] at this
  rw [this]
  split_ifs <;> rfl

end Idempotent

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-! ### Coordinates of `y γ_g` -/

/-- A basis term whose bottom is not the loading of `g` kills `γ_g`. -/
theorem endStendhal_topTerm_mul_genElt_of_ne (hρ₂ : ∀ b, wordProd N (ρ₂ b) = b)
    (g : EndGen ν₀ ρ₁) (y : {b // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ b}) (hy : y.1.1 ≠ g.1.2.1) :
    endStendhal Q Λ Λc ν ν₀ (topTerm Q Λc hρ₂ y) * genElt Q Λ Λc ρ₁ ρ₃ g = 0 := by
  rw [← endStendhal_e_mul_genElt (g := g), ← mul_assoc, ← map_mul, topTerm_mul_e,
    ite_eq_right_of_eq_false _ _ (eq_false hy), map_zero, zero_mul]

variable (Q Λ Λc ρ₃) in
/-- The `k`-linear map `y ↦ y γ_g`. -/
def genMul (g : EndGen ν₀ ρ₁) : Tc →ₗ[k] Tp where
  toFun c := endStendhal Q Λ Λc ν ν₀ c * genElt Q Λ Λc ρ₁ ρ₃ g
  map_add' c c' := by rw [map_add, add_mul]
  map_smul' r c := by rw [map_smul, smul_mul_assoc]; rfl

theorem genMul_apply (g : EndGen ν₀ ρ₁) (c : Tc) :
    genMul Q Λ Λc ρ₃ g c = endStendhal Q Λ Λc ν ν₀ c * genElt Q Λ Λc ρ₁ ρ₃ g := rfl

open Classical in
/-- **The coordinates of `y γ_g`** in the basis of `T̃^{λ⁺}` with dots on top: at the basis term
indexed by a pair `(g', y')` it is the coordinate of `y` at `y'` if `g = g'`, and `0` otherwise. -/
theorem topBasis_repr_genMul (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (g : EndGen ν₀ ρ₁) (c : Tc)
    (p : EndPair ρ₁ ρ₂) :
    (topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃) (endWord_spec hρ₁ hρ₂ hρ₃)).repr
        (genMul Q Λ Λc ρ₃ g c) (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p) =
      if g = p.1.1 then (topBasis Q Λc hQ ρ₂ hρ₂).repr c p.1.2 else 0 := by
  classical
  set Bp := topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃)
    (endWord_spec hρ₁ hρ₂ hρ₃)
  set Bc := topBasis Q Λc hQ ρ₂ hρ₂
  set b₀ := endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p
  have hb : ∀ y, Bp.repr (genMul Q Λ Λc ρ₃ g (Bc y)) b₀ =
      if g = p.1.1 then Bc.repr (Bc y) p.1.2 else 0 := fun y => by
    rw [topBasis_apply, genMul_apply]
    by_cases hy : y.1.1 = g.1.2.1
    · rw [endStendhal_topTerm_mul_genElt ρ₂ hρ₁ hρ₂ hρ₃ ⟨(g, y), hy⟩, ← topBasis_apply hQ _
        (endWord_spec hρ₁ hρ₂ hρ₃), Bp.repr_self, ← topBasis_apply hQ ρ₂ hρ₂ y, Bc.repr_self,
        Finsupp.single_apply,
        Finsupp.single_apply]
      have hinj := endPairIdx_injective (endWord_spec hρ₁ hρ₂ hρ₃)
      by_cases hg : g = p.1.1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)]
        apply if_congr _ rfl rfl
        constructor
        · intro h
          have := congrArg (fun q : EndPair ρ₁ ρ₂ => q.1.2) (hinj h)
          exact this
        · intro h
          refine congrArg _ (Subtype.ext (Prod.ext hg ?_))
          exact h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hg)]
        exact ite_eq_right_of_eq_false _ _ (eq_false fun h =>
          hg (congrArg (fun q : EndPair ρ₁ ρ₂ => q.1.1) (hinj h)))
    · rw [endStendhal_topTerm_mul_genElt_of_ne _ g y hy, map_zero, Finsupp.coe_zero,
        Pi.zero_apply]
      split_ifs with hg
      · rw [← topBasis_apply hQ ρ₂ hρ₂ y, Bc.repr_self]
        refine (Finsupp.single_apply_eq_zero.2 fun hh => ?_).symm
        subst hg
        exact absurd (by rw [← hh]; exact p.2) hy
      · rfl
  have hext := Bc.ext (f₁ := (Bp.coord b₀).comp (genMul Q Λ Λc ρ₃ g))
    (f₂ := if g = p.1.1 then Bc.coord p.1.2 else 0) fun y => by
      rw [LinearMap.comp_apply, Bp.coord_apply, hb]
      split_ifs <;> rfl
  have := LinearMap.congr_fun hext c
  rw [LinearMap.comp_apply, Bp.coord_apply] at this
  rw [this]
  split_ifs <;> rfl

/-! ### The end corner as a sum of idempotent right ideals -/

variable (Q Λc) in
/-- The idempotent `e(j_g)` of a generator, in the opposite of `T̃^{(μ,μ*)}`. -/
def genIdem (g : EndGen ν₀ ρ₁) : Tcᵐᵒᵖ := op (StendhalAlgebra.e g.1.2.1 g.2.1)

theorem isIdempotentElem_genIdem (g : EndGen ν₀ ρ₁) :
    IsIdempotentElem (genIdem (k := k) Q Λc g) := by
  change op _ * op _ = op _
  rw [← op_mul]
  congr 1
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e _ * StendhalAlgebraAllOrders.e _ = _
  rw [StendhalAlgebraAllOrders.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

variable (Q Λ Λc ρ₃) in
/-- The generator `γ_g` as an element of the corner `e T̃^{λ⁺}`. -/
def genCorner (g : EndGen ν₀ ρ₁) : Corner (endOp Q Λ Λc ν ν₀) :=
  ⟨op (genElt Q Λ Λc ρ₁ ρ₃ g), by
    change op _ * endOp Q Λ Λc ν ν₀ 1 = op _
    rw [endOp_apply, unop_one, ← op_mul, endStendhal_one_mul_genElt]⟩

theorem genIdem_smul_genCorner (g : EndGen ν₀ ρ₁) :
    op (genIdem Q Λc g) • genCorner Q Λ Λc ρ₃ g = genCorner Q Λ Λc ρ₃ g := by
  apply Subtype.ext
  change op _ * op (endStendhal Q Λ Λc ν ν₀ _) = op _
  rw [← op_mul]
  congr 1
  exact endStendhal_e_mul_genElt g

/-- The sum `∑_g y_g γ_g` in `T̃^{λ⁺}`. -/
theorem unop_idemSum_single [DecidableEq (EndGen ν₀ ρ₁)] (g : EndGen ν₀ ρ₁)
    (a : BalancedTensor.idemLeft ℤ (genIdem (k := k) Q Λc g)) :
    unop (BalancedTensor.idemSum ℤ (Corner (endOp Q Λ Λc ν ν₀)) (genIdem Q Λc)
        (genCorner Q Λ Λc ρ₃) (DFinsupp.single g a)).1 =
      genMul Q Λ Λc ρ₃ g (unop (a : Tcᵐᵒᵖ)) := by
  rw [BalancedTensor.idemSum_single]
  rfl

/-- **The coordinates of `∑_g y_g γ_g`**: at the basis term indexed by `(g, y)` it is the
coordinate of `y_g` at `y`. -/
theorem topBasis_repr_genSum [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (a : Π₀ g : EndGen ν₀ ρ₁, BalancedTensor.idemLeft ℤ (genIdem (k := k) Q Λc g))
    (p : EndPair ρ₁ ρ₂) :
    (topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃) (endWord_spec hρ₁ hρ₂ hρ₃)).repr
        (unop (BalancedTensor.idemSum ℤ (Corner (endOp Q Λ Λc ν ν₀)) (genIdem Q Λc)
          (genCorner Q Λ Λc ρ₃) a).1) (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p) =
      (topBasis Q Λc hQ ρ₂ hρ₂).repr (unop ((a p.1.1 : Tcᵐᵒᵖ))) p.1.2 := by
  classical
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha g b f _ _ ih =>
    rw [map_add, Submodule.coe_add, unop_add, map_add, Finsupp.add_apply, ih,
      unop_idemSum_single, topBasis_repr_genMul hQ hρ₁ hρ₂ hρ₃, DFinsupp.add_apply,
      Submodule.coe_add, unop_add, map_add, Finsupp.add_apply]
    congr 1
    by_cases hg : g = p.1.1
    · subst hg
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), DFinsupp.single_eq_same]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hg), DFinsupp.single_eq_of_ne (Ne.symm hg)]
      simp

/-- **The end corner of `T̃^{λ⁺}` is `⨁_g T̃^{(μ,μ*)} e(j_g)`** (arXiv:1309.3796v3, proof of
Lemma 7.17, for symmetric `Q`): every element of `e T̃^{λ⁺}` is uniquely `∑_g y_g γ_g` with
`y_g e(j_g) = y_g`. -/
theorem endIdemSum_bijective [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Bijective (BalancedTensor.idemSum ℤ (Corner (endOp Q Λ Λc ν ν₀))
      (genIdem (k := k) (ρ₁ := ρ₁) Q Λc) (genCorner Q Λ Λc ρ₃)) := by
  classical
  set Bp := topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃)
    (endWord_spec hρ₁ hρ₂ hρ₃)
  set Bc := topBasis Q Λc hQ ρ₂ hρ₂
  constructor
  · intro a a' h
    refine DFinsupp.ext fun g => Subtype.ext (unop_injective (Bc.ext_elem fun y => ?_))
    by_cases hy : y.1.1 = g.1.2.1
    · have h₁ := topBasis_repr_genSum (Λ := Λ) hQ hρ₁ hρ₂ hρ₃ a ⟨(g, y), hy⟩
      have h₂ := topBasis_repr_genSum (Λ := Λ) hQ hρ₁ hρ₂ hρ₃ a' ⟨(g, y), hy⟩
      rw [h] at h₁
      exact h₁.symm.trans h₂
    · have hz : ∀ c : BalancedTensor.idemLeft ℤ (genIdem (k := k) Q Λc g),
          Bc.repr (unop (c : Tcᵐᵒᵖ)) y = 0 := fun c => by
        have hc : unop (c : Tcᵐᵒᵖ) * StendhalAlgebra.e g.1.2.1 g.2.1 = unop (c : Tcᵐᵒᵖ) :=
          congrArg unop c.2
        rw [← hc, topBasis_repr_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hy)]
      rw [hz, hz]
  · intro z
    have hz : endStendhal Q Λ Λc ν ν₀ 1 * unop z.1 = unop z.1 := congrArg unop z.2
    let Ψ : (Π₀ g : EndGen ν₀ ρ₁, BalancedTensor.idemLeft ℤ (genIdem (k := k) Q Λc g)) →+ Tp :=
      (opAddEquiv.symm : Tpᵐᵒᵖ ≃+ Tp).toAddMonoidHom.comp
        ((Submodule.subtype _).toAddMonoidHom.comp
          (BalancedTensor.idemSum ℤ (Corner (endOp Q Λ Λc ν ν₀)) (genIdem (k := k) Q Λc)
            (genCorner Q Λ Λc ρ₃)).toAddMonoidHom)
    have hΨ : ∀ a, Ψ a = unop (BalancedTensor.idemSum ℤ (Corner (endOp Q Λ Λc ν ν₀))
        (genIdem (k := k) Q Λc) (genCorner Q Λ Λc ρ₃) a).1 := fun _ => rfl
    suffices hmem : unop z.1 ∈ AddMonoidHom.mrange Ψ by
      obtain ⟨a, ha⟩ := AddMonoidHom.mem_mrange.1 hmem
      exact ⟨a, Subtype.ext (unop_injective ((hΨ a).symm.trans ha))⟩
    have hexp : unop z.1 = ∑ b ∈ (Bp.repr (unop z.1)).support,
        Bp.repr (unop z.1) b • (endStendhal Q Λ Λc ν ν₀ 1 * Bp b) := by
      conv_lhs => rw [← hz, ← Bp.linearCombination_repr (unop z.1)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => mul_smul_comm _ _ _
    rw [hexp]
    refine AddSubmonoid.sum_mem _ fun b _ => ?_
    rw [topBasis_apply, endStendhal_one_mul_topTerm]
    split_ifs with hb
    · obtain ⟨p, rfl⟩ := exists_endPairIdx ρ₁ ρ₂ ρ₃ hρ₁ hρ₂ hρ₃ b hb
      set r := Bp.repr (unop z.1) (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p)
      have hmemL : op (r • topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2) ∈
          BalancedTensor.idemLeft ℤ (genIdem (k := k) Q Λc p.1.1) := by
        change op _ * op _ = op _
        rw [← op_mul, smul_mul_assoc, topTerm_mul_e, ite_eq_left_of_eq_true _ _ (eq_true p.2)]
      refine AddMonoidHom.mem_mrange.2 ⟨DFinsupp.single p.1.1 ⟨_, hmemL⟩, ?_⟩
      rw [hΨ, unop_idemSum_single, genMul_apply]
      change endStendhal Q Λ Λc ν ν₀ (r • _) * _ = _
      rw [map_smul, smul_mul_assoc, endStendhal_topTerm_mul_genElt ρ₂ hρ₁ hρ₂ hρ₃ p]
    · rw [smul_zero]
      exact AddSubmonoid.zero_mem _

/-! ### The model of `K̃` -/

variable (Q Λ Λc ν ν₀ ρ₁ ρ₃) in
variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- **The model of `K̃` for a cap at the right end is `⨁_g L e(j_g)`** (arXiv:1309.3796v3, proof
of Lemma 7.17, for symmetric `Q`): `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺} ≅ ⨁_g L e(j_g)` over the
generators `g = (x, j, u)`, `ℓ' γ_g ↦ (ℓ')_g`. -/
def endModelEquiv [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    EndModel Q Λ Λc ν ν₀ L ≃ₗ[ℤ] Π₀ g : EndGen ν₀ ρ₁, BalancedTensor.idemPart ℤ L
      (genIdem (k := k) Q Λc g) :=
  BalancedTensor.idemEquiv (B := Tpᵐᵒᵖ) isIdempotentElem_genIdem genIdem_smul_genCorner
    (endIdemSum_bijective hQ hρ₁ hρ₂ hρ₃)

end Categorification.Stendhal.CupCap
