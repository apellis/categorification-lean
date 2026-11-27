/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftProjectiveGen

/-!
# The violated diagrams of `K̃^{λ⁺}_λ` for a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, the discussion after Lemma 7.17, in the case `j = ℓ`. By the
basis `B″` (`baseBasis_apply`), `K̃^{λ⁺}_λ` is `⨁_q T̃^λ e(i_q)` as a left `T̃^λ`-module, the
sum over the base indices `q = ((e(i), t, u), b′)`: every element is uniquely `∑_q a_q c_q`
with `a_q e(i_q) = a_q` (`baseSum`, `baseBasis_repr_baseSum`, `baseSum_surjective`).

The violated diagrams are exactly the sums `∑_q a_q c_q` with every `a_q` in the violating
ideal of `T̃^λ` (`violated_le_baseViolated`). Those factoring through a violated diagram of
`T̃^λ` above the cap are of this form by definition. For those factoring through a violated
idempotent `e(s)` of `T̃^{λ⁺}` below the cap: `c_q e(s)` vanishes unless `s` is the bottom of
the generator of `q`, a shuffle of `i_q` with the loading `t` at the maximum. Its leftmost
strand is then the leftmost strand of `i_q` or of `t`; the latter is the red strand `μ` (`t` is
cap-good, since `L e(t) ≠ 0`), so `e(s)` violated forces `e(i_q)` violated
(`isViolated_top_of_isViolated_bot`), and `c_q = e(i_q) c_q` is violated from above.

## Main definitions

* `CupCap.baseSum`: the map `(a_q)_q ↦ ∑_q a_q c_q`.
* `CupCap.baseViolated`: the sums `∑_q a_q c_q` with violated coefficients.

## Main results

* `CupCap.baseBasis_repr_baseSum`: the coordinates of `∑_q a_q c_q` in `B″`.
* `CupCap.baseSum_mul_e_eq`: the coefficients `a_q e(i_q)` are determined by the sum.
* `CupCap.violated_le_baseViolated`: every violated diagram has violated coefficients.
* `CupCap.mul_e_mem_violatedIdeal_of_baseSum_mem`: the coefficients of a violated sum are
  violated.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "V" => StendhalAlgebra.violatedIdeal k Q Λ ν

/-! ### The leftmost strand of a shuffle -/

omit [DecidableEq I] in
/-- **The leftmost strand of the bottom of a generator** is the leftmost strand of `i` or of
`t`: if the bottom `u⁻¹ (i t)` is violated and `t` starts with the red strand `μ`, then `i` is
violated. -/
theorem isViolated_top_of_isViolated_bot {ρ₁ : Perm (Fin m) → List ℕ} (g : EndGen ν₀ ρ₁)
    (ht : IsCapGood ν₀ g.1.2.1) (hv : IsViolated g.bot) : IsViolated g.1.1.1.1 := by
  obtain ⟨h0, hl⟩ := hv
  have hM := m_add_N_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hN := two_le_card_stendhalWeight ν₀
  set u := g.1.2.2 with hu
  set p : Fin M := u.1 ⟨0, h0⟩ with hp
  have hlp : g.bot.lbl ⟨0, h0⟩ = (endSeq g.1.1.1.1 g.1.2.1).lbl p := by
    change (endSeq g.1.1.1.1 g.1.2.1).1 ((u.1⁻¹).symm ⟨0, h0⟩) = _
    rfl
  have hinv : u.1⁻¹ p = ⟨0, h0⟩ := u.1.symm_apply_apply _
  rw [hlp] at hl
  by_cases hpm : p.val < m
  · have hp0 : p.val = 0 := by
      by_contra hne
      have hlt : (⟨0, by omega⟩ : Fin m) < ⟨p.val, hpm⟩ := by
        change 0 < p.val; omega
      have h1 := u.2.1 hlt
      have he : blockEquiv hM (Sum.inl ⟨p.val, hpm⟩) = p := Fin.ext (by simp)
      simp only [he, hinv] at h1
      exact Nat.not_lt_zero _ h1
    refine ⟨by omega, ?_⟩
    rw [endSeq_lbl_lt _ _ p hpm] at hl
    have hf : (⟨p.val, hpm⟩ : Fin m) = ⟨0, by omega⟩ := Fin.ext hp0
    rw [hf] at hl
    revert hl
    cases g.1.1.1.1.lbl ⟨0, by omega⟩ <;> simp
  · exfalso
    have hpN : p.val - m < N := by omega
    have hp0 : p.val - m = 0 := by
      by_contra hne
      have hlt : (⟨0, by omega⟩ : Fin N) < ⟨p.val - m, hpN⟩ := by
        change 0 < p.val - m; omega
      have h1 := u.2.2 hlt
      have he : blockEquiv hM (Sum.inr ⟨p.val - m, hpN⟩) = p := Fin.ext (by simp; omega)
      simp only [he, hinv] at h1
      exact Nat.not_lt_zero _ h1
    rw [endSeq_lbl_ge _ _ p (by omega)] at hl
    have hf : (⟨p.val - m, by omega⟩ : Fin N) = ⟨0, by omega⟩ := Fin.ext hp0
    rw [hf, ht.1] at hl
    simp at hl

/-! ### Sums over the base indices -/

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [Module k L]
  [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- The scalars of `K̃^{λ⁺}_λ` (right scalars of `T̃^{λ⁺}`) are the left scalars of `T̃^λ`. -/
theorem smul_envMk_left_smul (c : k) (a : T) (z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    c • ((Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z) =
      (Env.mk (c • a) 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z := by
  rw [capTilde_smul_def, envScalar_apply, ← mul_smul, Env.mk_mul_mk, one_mul, one_mul,
    Algebra.algebraMap_eq_smul_one, Env.mk_smul_right]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem envMk_left_smul_left_smul (a a' : T) (z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • (Env.mk a' 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z =
      (Env.mk (a * a') 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z := by
  rw [← mul_smul, Env.mk_mul_mk, one_mul]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem envMk_right_smul_left_smul (a : T) (b : Tp) (z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    (Env.mk 1 b : Env k Q Λ Λc ℓ le_rfl ν ν₀) • (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z =
      (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • (Env.mk 1 b : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z :=
          by
  rw [← mul_smul, ← mul_smul, Env.mk_mul_mk, Env.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- The `k`-linear map `a ↦ a c_q`. -/
def baseMul [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2))))
    (q : BaseIdx ν₀ ρ₁ ι) : T →ₗ[k] CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L where
  toFun a := (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
    baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q
  map_add' a a' := by rw [Env.mk_add_left, add_smul]
  map_smul' c a := by rw [RingHom.id_apply, smul_envMk_left_smul]

open Classical in
variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **The map `(a_q)_q ↦ ∑_q a_q c_q`** from `⨁_q T̃^λ` to `K̃^{λ⁺}_λ`. -/
def baseSum [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
    (Π₀ _ : BaseIdx ν₀ ρ₁ ι, T) →ₗ[k] CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L :=
  DFinsupp.lsum ℕ (baseMul Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B')

open Classical in
theorem baseSum_single [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) (q
          : BaseIdx ν₀ ρ₁ ι) (a : T) :
    baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' (DFinsupp.single q a) = (Env.mk a 1 : Env k
        Q Λ Λc ℓ le_rfl ν ν₀) • baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q := by
  rw [baseSum, DFinsupp.lsum_single]
  rfl

/-- `x c_q` vanishes unless the bottom of `x` is the top of `q`. -/
theorem envMk_topTerm_smul_baseElt [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) (q
          : BaseIdx ν₀ ρ₁ ι) (y : {x // IsTopTerm ρ₁ x}) :
    (Env.mk (topTerm Q Λ (fun w => (hρ₁ w).2) y) 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • baseElt Q Λ Λc ν₀
        ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q =
      if h : y.1.1 = q.top then baseBasis Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ⟨q, ⟨y, h⟩⟩
          else 0 := by
  rw [← envMk_e_smul_baseElt L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q, envMk_left_smul_left_smul,
      topTerm_mul_e]
  split_ifs with h
  · rw [baseBasis_apply]
  · rw [Env.mk, TensorProduct.zero_tmul, zero_smul]

open Classical in
/-- **The coordinates of `∑_q a_q c_q` in `B″`**: at the index `(q, x)` it is the coordinate of
`a_q` at the basis term `x` of `T̃^λ`. -/
theorem baseBasis_repr_baseSum [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) (A
          : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T)
    (r : Σ q : BaseIdx ν₀ ρ₁ ι, {x : {x // IsTopTerm ρ₁ x} // x.1.1 = q.top}) :
    (baseBasis Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B').repr (baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁
        hρ₂ hρ₃ hκ hL hP B' A) r = (topBasis Q Λ hQ ρ₁ hρ₁).repr (A r.1) r.2.1 := by
  have hext : ((baseBasis Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B').coord r).comp (baseSum Q Λ
      Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') =
      ((topBasis Q Λ hQ ρ₁ hρ₁).coord r.2.1).comp
        (DFinsupp.lapply r.1 : (Π₀ _ : BaseIdx ν₀ ρ₁ ι, T) →ₗ[k] T) := by
    refine DFinsupp.lhom_ext fun q a => ?_
    have hlin : ((baseBasis Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B').coord r).comp ((baseSum Q
        Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B').comp (DFinsupp.lsingle q)) =
        ((topBasis Q Λ hQ ρ₁ hρ₁).coord r.2.1).comp
          ((DFinsupp.lapply r.1 : (Π₀ _ : BaseIdx ν₀ ρ₁ ι, T) →ₗ[k] T).comp
            (DFinsupp.lsingle q)) := by
      refine (topBasis Q Λ hQ ρ₁ hρ₁).ext fun y => ?_
      simp only [LinearMap.comp_apply, DFinsupp.lsingle_apply, DFinsupp.lapply_apply,
        Module.Basis.coord_apply, topBasis_apply]
      rw [baseSum_single, envMk_topTerm_smul_baseElt L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B']
      obtain ⟨q', x', hx'⟩ := r
      by_cases hq : q = q'
      · subst hq
        rw [DFinsupp.single_eq_same, ← topBasis_apply hQ ρ₁ hρ₁, Module.Basis.repr_self]
        by_cases hy : y = x'
        · subst hy
          split_ifs
          rw [Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_same]
        · rw [Finsupp.single_eq_of_ne' hy]
          split_ifs with h
          · rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne']
            intro he
            exact hy (congrArg (fun s : Σ q : BaseIdx ν₀ ρ₁ ι,
              {x : {x // IsTopTerm ρ₁ x} // x.1.1 = q.top} => s.2.1) he)
          · rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      · rw [DFinsupp.single_eq_of_ne (Ne.symm hq), map_zero, Finsupp.coe_zero, Pi.zero_apply]
        split_ifs with h
        · rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne']
          intro he
          exact hq (congrArg Sigma.fst he)
        · rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact LinearMap.congr_fun hlin a
  exact LinearMap.congr_fun hext A

open Classical in
/-- **Every element of `K̃^{λ⁺}_λ` is a sum `∑_q a_q c_q`.** -/
theorem baseSum_surjective [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
          Function.Surjective (baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (baseBasis Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP
      B').span_eq, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact ⟨DFinsupp.single r.1 (topTerm Q Λ (fun w => (hρ₁ w).2) r.2.1), by
    rw [baseSum_single, baseBasis_apply]⟩

open Classical in
/-- `T̃^λ` acts on `∑_q a_q c_q` through the coefficients. -/
theorem envMk_smul_baseSum [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) (a
          : T) (A : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T) :
    (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
        A = baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' (A.mapRange (fun _ x => a * x) (fun
            _ => mul_zero a)) := by
  induction A using DFinsupp.induction with
  | h0 => rw [map_zero, smul_zero, DFinsupp.mapRange_zero, map_zero]
  | ha q b f _ _ ih =>
    rw [map_add, smul_add, ih, DFinsupp.mapRange_add _ _ (fun _ x y => mul_add a x y), map_add,
      DFinsupp.mapRange_single, baseSum_single, baseSum_single, envMk_left_smul_left_smul]

/-- **Uniqueness of the coefficients**: the sum `∑_q a_q c_q` determines each `a_q e(i_q)`. -/
theorem baseSum_mul_e_eq [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) {A
          A' : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T} (h : baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
              A = baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' A')
    (q : BaseIdx ν₀ ρ₁ ι) :
    A q * StendhalAlgebra.e q.top q.isRedOrdered_top =
      A' q * StendhalAlgebra.e q.top q.isRedOrdered_top := by
  refine (topBasis Q Λ hQ ρ₁ hρ₁).ext_elem fun y => ?_
  rw [topBasis_repr_mul_e, topBasis_repr_mul_e]
  split_ifs with hy
  · have h₁ := baseBasis_repr_baseSum L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' A ⟨q, ⟨y, hy⟩⟩
    have h₂ := baseBasis_repr_baseSum L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' A' ⟨q, ⟨y, hy⟩⟩
    rw [h] at h₁
    exact h₁.symm.trans h₂
  · rfl

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- The sums `∑_q a_q c_q` whose coefficients are all violated. -/
def baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
          Set (CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :=
  {z | ∃ A : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T, (∀ q, A q ∈ V) ∧ baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ
      hL hP B' A = z}

theorem zero_mem_baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
    (0 : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL
        hP B' :=
  ⟨0, fun _ => (V).zero_mem, map_zero _⟩

theorem add_mem_baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) {z
          z' : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L}
    (hz : z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B')
    (hz' : z' ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') :
    z + z' ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' := by
  obtain ⟨A, hA, rfl⟩ := hz
  obtain ⟨A', hA', rfl⟩ := hz'
  exact ⟨A + A', fun q => (V).add_mem (hA q) (hA' q), map_add _ _ _⟩

theorem neg_mem_baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) {z
          : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L}
    (hz : z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') :
    -z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' := by
  obtain ⟨A, hA, rfl⟩ := hz
  exact ⟨-A, fun q => (V).neg_mem (hA q), by rw [← map_neg]⟩

open Classical in
theorem envMk_left_smul_mem_baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) (a
          : T) {z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L}
    (hz : z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') :
    (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃
        hκ hL hP B' := by
  obtain ⟨A, hA, rfl⟩ := hz
  rw [envMk_smul_baseSum]
  exact ⟨_, fun q => (V).mul_mem_left a _ (hA q), rfl⟩

open Classical in
theorem envMk_violated_smul_mem_baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) {a
          : T} (ha : a ∈ V) (z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    (Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃
        hκ hL hP B' := by
  obtain ⟨A, rfl⟩ := baseSum_surjective L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' z
  rw [envMk_smul_baseSum]
  exact ⟨_, fun q => (V).mul_mem_right a _ ha, rfl⟩

open Classical in
/-- `T̃^{λ⁺}` acting from below keeps the sums with violated coefficients. -/
theorem envMk_right_smul_mem_baseViolatedSet [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) (b
          : Tp) {z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L}
    (hz : z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') :
    (Env.mk 1 b : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃
        hκ hL hP B' := by
  obtain ⟨A, hA, rfl⟩ := hz
  induction A using DFinsupp.induction with
  | h0 => rw [map_zero, smul_zero]; exact zero_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
  | ha q c f hf _ ih =>
    have hc : c ∈ V := by simpa [hf] using hA q
    have hf' : ∀ q', f q' ∈ V := fun q' => by
      by_cases e : q' = q
      · subst e; rw [hf]; exact (V).zero_mem
      · simpa [DFinsupp.single_eq_of_ne e] using hA q'
    rw [map_add, smul_add]
    refine add_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ?_ (ih hf')
    rw [baseSum_single, envMk_right_smul_left_smul]
    exact envMk_violated_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' hc _

open Classical in
/-- **A violated idempotent of `T̃^{λ⁺}` below the cap gives violated coefficients**: `c_q e(s)`
vanishes unless `s` is the bottom of `q`, and then `e(i_q)` is violated. -/
theorem envMk_e_smul_mem_baseViolatedSet [Nontrivial k] [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm
    Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2))))
    (s : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hs : IsRedOrdered s) (hv : IsViolated s)
    (z : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    (Env.mk 1 (StendhalAlgebra.e s hs) : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z ∈ baseViolatedSet Q Λ Λc ν₀
        ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' := by
  obtain ⟨A, rfl⟩ := baseSum_surjective L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' z
  induction A using DFinsupp.induction with
  | h0 => rw [map_zero, smul_zero]; exact zero_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
  | ha q c f _ _ ih =>
    rw [map_add, smul_add]
    refine add_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ?_ ih
    rw [baseSum_single, envMk_right_smul_left_smul, envMk_e_smul_baseElt_right]
    split_ifs with hb
    · have hcap : IsCapGood ν₀ q.1.1.1.2.1 := by
        by_contra hc
        exact (isEmpty_of_basis_idemPart hL _ _ hc (B' ⟨q.1.1.1.2.1, q.1.1.2.1⟩)).false q.2
      have htop : IsViolated q.top :=
        isViolated_top_of_isViolated_bot q.1.1 hcap (hb ▸ hv)
      have he : StendhalAlgebra.e q.top q.isRedOrdered_top ∈ V :=
        TwoSidedIdeal.subset_span ⟨q.top, q.isRedOrdered_top, htop, rfl⟩
      rw [← envMk_e_smul_baseElt L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q, envMk_left_smul_left_smul]
      exact envMk_violated_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ((V).mul_mem_left c
          _ he) _
    · rw [smul_zero]
      exact zero_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem envMk_neg_right (b : Tp) : (Env.mk 1 (-b) : Env k Q Λ Λc ℓ le_rfl ν ν₀) = -Env.mk 1 b :=
  eq_neg_of_add_eq_zero_left (by rw [← Env.mk_add_right, neg_add_cancel, Env.mk_zero_right])

/-- **The diagrams factoring through a violated diagram of `T̃^{λ⁺}` below the cap** have
violated coefficients. -/
theorem envMk_violated_right_smul_mem_baseViolatedSet [Nontrivial k] [DecidableEq (EndGen ν₀ ρ₁)]
    (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) {b
          : Tp}
    (hb : b ∈ StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)) (z : CapTilde k
        Q Λ Λc ℓ le_rfl ν ν₀ L) :
    (Env.mk 1 b : Env k Q Λ Λc ℓ le_rfl ν ν₀) • z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃
        hκ hL hP B' := by
  unfold StendhalAlgebra.violatedIdeal at hb
  induction hb using TwoSidedIdeal.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨s, hs, hv, rfl⟩ := hx
    exact envMk_e_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' s hs hv z
  | zero =>
    rw [Env.mk_zero_right, zero_smul]
    exact zero_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
  | add x x' _ _ ih ih' =>
    rw [Env.mk_add_right, add_smul]
    exact add_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' (ih z) (ih' z)
  | neg x _ ih =>
    rw [envMk_neg_right, neg_smul]
    exact neg_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' (ih z)
  | left_absorb c x _ ih =>
    have he : (Env.mk 1 (c * x) : Env k Q Λ Λc ℓ le_rfl ν ν₀) = Env.mk 1 x * Env.mk 1 c := by
      rw [Env.mk_mul_mk, one_mul]
    rw [he, mul_smul]
    exact ih _
  | right_absorb c x _ ih =>
    have he : (Env.mk 1 (x * c) : Env k Q Λ Λc ℓ le_rfl ν ν₀) = Env.mk 1 c * Env.mk 1 x := by
      rw [Env.mk_mul_mk, one_mul]
    rw [he, mul_smul]
    exact envMk_right_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' c (ih z)

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **The sums `∑_q a_q c_q` with violated coefficients**, a sub-bimodule of `K̃^{λ⁺}_λ`. -/
def baseViolated [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
          Submodule (Env k Q Λ Λc ℓ le_rfl ν ν₀) (CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) where
  carrier := baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
  zero_mem' := zero_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
  add_mem' := add_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
  smul_mem' r z hz := by
    change r • z ∈ baseViolatedSet Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
    induction r using TensorProduct.inductionOn with
    | tmul a b =>
      have he : (a ⊗ₜ[k] b : Env k Q Λ Λc ℓ le_rfl ν ν₀) = Env.mk a 1 * Env.mk 1 (unop b) := by
        rw [Env.mk_mul_mk, mul_one, mul_one]
        rfl
      rw [he, mul_smul]
      exact envMk_left_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' a
        (envMk_right_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' (unop b) hz)
    | add r r' hr hr' =>
      rw [add_smul]
      exact add_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' hr hr'

/-- **Every violated diagram of `K̃^{λ⁺}_λ` has violated coefficients** (arXiv:1309.3796v3,
after Lemma 7.17, `j = ℓ`): the bottom-violated diagrams lie in `V_λ K̃^{λ⁺}_λ`, since the
loadings at the maximum start with the red strand `μ`. -/
theorem violated_le_baseViolated [Nontrivial k] [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
    violated k Q Λ Λc ℓ le_rfl ν ν₀ L ≤ baseViolated Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' :=
        by
  refine Submodule.span_le.2 ?_
  rintro z (⟨a, ha, y, rfl⟩ | ⟨b, hb, y, rfl⟩)
  · exact envMk_violated_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ha y
  · exact envMk_violated_right_smul_mem_baseViolatedSet L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' hb y

/-- **The coefficients of a violated sum are violated**: if `∑_q a_q c_q` is violated, then
every `a_q e(i_q)` lies in the violating ideal of `T̃^λ`. -/
theorem mul_e_mem_violatedIdeal_of_baseSum_mem [Nontrivial k] [DecidableEq (EndGen ν₀ ρ₁)] (hQ :
    KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2))))
    {A : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T} (h : baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' A ∈
        violated k Q Λ Λc ℓ le_rfl ν ν₀ L)
    (q : BaseIdx ν₀ ρ₁ ι) : A q * StendhalAlgebra.e q.top q.isRedOrdered_top ∈ V := by
  obtain ⟨A', hA', hA⟩ := violated_le_baseViolated L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' h
  rw [← baseSum_mul_e_eq L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' hA]
  exact (V).mul_mem_right _ _ (hA' q)

end Categorification.Stendhal.CupCap
