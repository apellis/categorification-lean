/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndBasis
import Categorification.WeightedKLR.Rigidity.CupCapMidCapBasisApply

/-!
# The basis `B″` of `K̃^{λ⁺}_λ` as a left `T̃^λ`-module, for a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17 and the discussion after it, in the case
`j = ℓ`. The element of the basis `B″` (`capBasis`) indexed by a generator `g = (x, t, u)` and
`b′ ∈ B′_t` is `x · c_{(i, t, u), b′}`, where `i` is the bottom of the basis term `x` of `T̃^λ` and
`c_{(i, t, u), b′}` is the element of `B″` indexed by the base generator `(e(i), t, u)` and `b′`
(`capBasis_eq_smul_base`): the diagram `x` sits on the first `m` strands, above the cap.

Consequently, reindexing `B″` by the pairs of a base index `q = ((e(i), t, u), b′)` and a basis
term `x` of `T̃^λ` with bottom `i` (`baseIdxEquiv`), the element of index `(q, x)` is
`x · c_q` (`baseBasis_apply`).

## Main definitions

* `CupCap.baseGen`: the base generator `(e(i), t, u)` of a generator `(x, t, u)`.
* `CupCap.BaseIdx`: the pairs of a base generator and an element of `B′_t`.
* `CupCap.baseIdxEquiv`: the index set of `B″` as pairs `(q, x)`.
* `CupCap.baseElt`: the elements `c_q` of `K̃^{λ⁺}_λ`.

## Main results

* `CupCap.capBasis_apply`: the element of `B″` of index `(g, b′)` is `b′ γ_g` in the model.
* `CupCap.capBasis_eq_smul_base`: it is `x · c_{(base g, b′)}`.
* `CupCap.baseBasis_apply`: the reindexed basis is `(q, x) ↦ x · c_q`.
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
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "bot" => botMap k Q Λ Λc ℓ le_rfl ν ν₀

/-! ### Base terms -/

omit [DecidableEq I] in
theorem rho_one_eq_nil {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) : ρ₁ 1 = [] := by
  have h := (hρ₁ 1).1.2
  rw [(hρ₁ 1).2, length_one] at h
  exact List.length_eq_zero_iff.1 h

omit [DecidableEq I] in
/-- The idempotent `e(i)` is a basis term with dots on top. -/
theorem isTopTerm_base {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) {i : Seq (stendhalWeight ℓ ν)}
    (hi : IsRedOrdered i) : IsTopTerm ρ₁ (i, 1, 0) := by
  refine ⟨hi, by rw [one_smul]; exact hi, fun a ha => by simp at ha, ?_⟩
  change NoRedCross (ρ₁ 1) i
  rw [rho_one_eq_nil hρ₁]
  trivial

theorem topElt_base {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) (i : Seq (stendhalWeight ℓ ν)) :
    topElt (Q := Q) (Λ := Λ) ρ₁ (i, 1, 0) = KLRAlgebra.e i := by
  rw [topElt]
  change pol (monomial 0 1) * ψw (ρ₁ 1) * _ = _
  rw [rho_one_eq_nil hρ₁, ψw_nil, monomial_zero', C_1, map_one, one_mul, one_mul]

/-- The quotient map sends a basis term with dots on top to itself. -/
theorem topMap_topElt {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : ∀ w, wordProd m (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    topMap k Q Λ ν (topElt ρ b.1) = topTerm Q Λ hρ b := by
  apply Subtype.ext
  change ofKLR k Q Λ ν _ * redOrderedIdem k Q Λ ν = _
  rw [topTerm_val]
  have h := ro_mul_ofKLR_topElt_mul_ro (Q := Q) (Λ := Λ) hρ b.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true b.2)] at h
  have hE := isIdempotentElem_redOrderedIdem (k := k) (Q := Q) (Λ := Λ) (ν := ν)
  conv_lhs => rw [← h]
  rw [mul_assoc, hE.eq, h]

/-- The base term `e(i)` of `T̃^λ` is the idempotent `e(i)`. -/
theorem topTerm_base {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) {i : Seq (stendhalWeight ℓ ν)}
    (hi : IsRedOrdered i) :
    topTerm Q Λ (fun w => (hρ₁ w).2) ⟨(i, 1, 0), isTopTerm_base hρ₁ hi⟩ =
      StendhalAlgebra.e i hi := by
  apply Subtype.ext
  rw [topTerm_val]
  change ofKLR k Q Λ ν (topElt ρ₁ (i, 1, 0)) = StendhalAlgebraAllOrders.e i
  rw [topElt_base hρ₁]
  rfl

/-! ### Base generators -/

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-- The base generator `(e(i), t, u)` of a generator `g = (x, t, u)`, `i` the bottom of `x`. -/
abbrev baseGen (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) (g : EndGen ν₀ ρ₁) :
    EndGen ν₀ ρ₁ :=
  ⟨(⟨(g.1.1.1.1, 1, 0), isTopTerm_base hρ₁ g.1.1.2.1⟩, g.1.2), g.2⟩

/-- **The generators act by the diagrams of `λ`**: `x · γ_{(e(i), t, u)} = γ_{(x, t, u)}`. -/
theorem prefixStendhal_topTerm_mul_genElt_base
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) (g : EndGen ν₀ ρ₁) :
    prefixStendhal Q Λ Λc ν ν₀ (topTerm Q Λ (fun w => (hρ₁ w).2) g.1.1) *
        genElt Q Λ Λc ρ₁ ρ₃ (baseGen hρ₁ g) = genElt Q Λ Λc ρ₁ ρ₃ g := by
  rw [← topMap_topElt, genElt, genElt, genKLR, genKLR]
  change _ * bot (prefixMapKLR Q Λ Λc ν ν₀ (topElt ρ₁ (g.1.1.1.1, 1, 0)) * _ * _ * _) = _
  rw [topElt_base hρ₁, prefixMapKLR_e, mul_assoc, mul_assoc, prefixStendhal_topMap_mul,
    ← prefixMapKLR_e, ← mul_assoc, ← prefixMapKLR_mul, topElt_mul_e, ← mul_assoc]
  rfl

/-- `γ_g e(t)` is `γ_g` if `t` is the bottom of `g`, and `0` otherwise. -/
theorem genElt_mul_e (g : EndGen ν₀ ρ₁) (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : IsRedOrdered t) :
    genElt Q Λ Λc ρ₁ ρ₃ g * StendhalAlgebra.e t ht =
      if g.bot = t then genElt Q Λ Λc ρ₁ ρ₃ g else 0 := by
  have he : (StendhalAlgebra.e t ht : Tp) = bot (KLRAlgebra.e t) :=
    Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem t).trans (ite_eq_left ht)).symm
  rw [he, genElt, ← map_mul, genKLR, mul_assoc, KLRAlgebra.e_mul_e]
  split_ifs
  · rfl
  · rw [mul_zero, map_zero]

theorem genCorner_eq_endGen (g : EndGen ν₀ ρ₁) :
    genCorner Q Λ Λc ρ₃ g = endGen Q Λ Λc ν ν₀ (genElt Q Λ Λc ρ₁ ρ₃ g) :=
  Subtype.ext (by rw [endGen_val, endStendhal_one_mul_genElt]; rfl)

/-! ### The basis `B″` -/

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [Module k L]
  [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem envMk_left_smul_tmul_genCorner (z : T) (g : EndGen ν₀ ρ₁) (v : L) :
    (Env.mk z 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        (Ind.tmul (genCorner Q Λ Λc ρ₃ g) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (prefixStendhal Q Λ Λc ν ν₀ z * genElt Q Λ Λc ρ₁ ρ₃ g)) v := by
  rw [envMk_smul]
  have h1 : (op (1 : Tp) : Tpᵐᵒᵖ) = 1 := rfl
  rw [h1, one_smul, genCorner_eq_endGen, leftAct_endGen]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem envMk_right_smul_tmul_genCorner (b : Tp) (g : EndGen ν₀ ρ₁) (v : L) :
    (Env.mk 1 b : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        (Ind.tmul (genCorner Q Λ Λc ρ₃ g) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (genElt Q Λ Λc ρ₁ ρ₃ g * b)) v := by
  rw [envMk_smul, genCorner_eq_endGen, op_smul_tmul_endGen, leftAct_one, LinearMap.id_apply]

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem envMk_topTerm_smul_tmul_base (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (g : EndGen ν₀ ρ₁) (v : L) :
    (Env.mk (topTerm Q Λ (fun w => (hρ₁ w).2) g.1.1) 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        (Ind.tmul (genCorner Q Λ Λc ρ₃ (baseGen hρ₁ g)) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (genCorner Q Λ Λc ρ₃ g) v := by
  rw [envMk_left_smul_tmul_genCorner, prefixStendhal_topTerm_mul_genElt_base,
    genCorner_eq_endGen]

/-- **The elements of the basis `B″`** for the cap at the right end: the element of index
`(g, b′)` corresponds to `b′ γ_g` in the model. -/
theorem capBasis_apply [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    (x : Σ g : EndGen ν₀ ρ₁, ι ⟨g.1.2.1, g.2.1⟩) :
    capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' x =
      (capModelEquiv Q Λ Λc ν₀ L hκ hL hP).symm
        (Ind.tmul (genCorner Q Λ Λc ρ₃ x.1) ((B' ⟨x.1.1.2.1, x.1.2.1⟩ x.2 : _) : L)) := by
  rw [capBasis, Module.Basis.map_apply, DFinsupp.basis_apply']
  change (capModelEquiv Q Λ Λc ν₀ L hκ hL hP).symm
    ((endModelEquiv Q Λ Λc ν ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃).symm
      (DFinsupp.mapRange (fun g => (idemPartEquiv L (genIdem (k := k) Q Λc g)).symm)
        (fun _ => map_zero _) (DFinsupp.single x.1 (B' ⟨x.1.1.2.1, x.1.2.1⟩ x.2)))) = _
  rw [DFinsupp.mapRange_single]
  congr 1
  exact BalancedTensor.idemEquiv_symm_single _ _ _ x.1 _

/-- **`B″` is obtained from its base elements by the diagrams of `λ`**: the element of index
`((x, t, u), b′)` is `x · c`, `c` the element of index `((e(i), t, u), b′)`. -/
theorem capBasis_eq_smul_base [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    (x : Σ g : EndGen ν₀ ρ₁, ι ⟨g.1.2.1, g.2.1⟩) :
    capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' x =
      (Env.mk (topTerm Q Λ (fun w => (hρ₁ w).2) x.1.1.1) 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ⟨baseGen hρ₁ x.1, x.2⟩ := by
  rw [capBasis_apply, capBasis_apply, ← map_smul, envMk_topTerm_smul_tmul_base L hρ₁]

/-- The right action of `e(t)` on `B″`: it keeps the elements whose generator has bottom `t`. -/
theorem envMk_e_smul_capBasis [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    (x : Σ g : EndGen ν₀ ρ₁, ι ⟨g.1.2.1, g.2.1⟩) (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : IsRedOrdered t) :
    (Env.mk 1 (StendhalAlgebra.e t ht) : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' x =
      if x.1.bot = t then capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' x else 0 := by
  apply (capModelEquiv Q Λ Λc ν₀ L hκ hL hP).injective
  rw [map_smul, capBasis_apply, LinearEquiv.apply_symm_apply, envMk_right_smul_tmul_genCorner,
    genElt_mul_e]
  split_ifs
  · rw [LinearEquiv.apply_symm_apply, ← genCorner_eq_endGen]
  · rw [map_zero, endGen_zero, Ind.zero_tmul]

/-! ### Reindexing `B″` by base generators -/

variable (ν₀ ρ₁) in
/-- The base generators `(e(i), t, u)`. -/
abbrev BaseGen : Type := {g : EndGen ν₀ ρ₁ // g.1.1.1.2 = (1, 0)}

variable (ν₀ ρ₁) in
/-- The pairs of a base generator `(e(i), t, u)` and an element of `B′_t`. -/
abbrev BaseIdx (ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*) : Type _ :=
  Σ c : BaseGen ν₀ ρ₁, ι ⟨c.1.1.2.1, c.1.2.1⟩

/-- The bottom `i` of the base generator of an index. -/
abbrev BaseIdx.top {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) : Seq (stendhalWeight ℓ ν) :=
  q.1.1.1.1.1.1

omit [DecidableEq I] in
theorem BaseIdx.isRedOrdered_top {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) : IsRedOrdered q.top :=
  q.1.1.1.1.2.1

/-- **The index set of `B″` as pairs `(q, x)`** of a base index `q = ((e(i), t, u), b′)` and a
basis term `x` of `T̃^λ` with dots on top and bottom `i`. -/
def baseIdxEquiv (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*) :
    (Σ g : EndGen ν₀ ρ₁, ι ⟨g.1.2.1, g.2.1⟩) ≃
      Σ q : BaseIdx ν₀ ρ₁ ι, {x : {x // IsTopTerm ρ₁ x} // x.1.1 = q.top} where
  toFun p := ⟨⟨⟨baseGen hρ₁ p.1, rfl⟩, p.2⟩, ⟨p.1.1.1, rfl⟩⟩
  invFun r := ⟨⟨(r.2.1, r.1.1.1.1.2), r.1.1.1.2.1, r.2.2.symm ▸ r.1.1.1.2.2⟩, r.1.2⟩
  left_inv p := rfl
  right_inv r := by
    obtain ⟨⟨⟨⟨⟨⟨⟨i, w, d⟩, hx₀⟩, t, u⟩, hg⟩, hc⟩, b⟩, ⟨⟨⟨i', w', d'⟩, hx⟩, hxi⟩⟩ := r
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    obtain rfl : i' = i := hxi
    rfl

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **The basis `B″` indexed by pairs `(q, x)`** (`baseIdxEquiv`). -/
def baseBasis [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    Module.Basis (Σ q : BaseIdx ν₀ ρ₁ ι, {x : {x // IsTopTerm ρ₁ x} // x.1.1 = q.top}) k
      (CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :=
  (capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B').reindex (baseIdxEquiv hρ₁ ι)

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **The base elements** `c_q` of `K̃^{λ⁺}_λ`: the elements of `B″` indexed by the base
generators `(e(i), t, u)` and `b′ ∈ B′_t`. -/
def baseElt [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
          : BaseIdx ν₀ ρ₁ ι) : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L :=
  capBasis Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ⟨q.1.1, q.2⟩

/-- **The basis `B″` as a left `T̃^λ`-family**: the element of index `(q, x)` is `x · c_q`. -/
theorem baseBasis_apply [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    (r : Σ q : BaseIdx ν₀ ρ₁ ι, {x : {x // IsTopTerm ρ₁ x} // x.1.1 = q.top}) :
    baseBasis Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' r =
      (Env.mk (topTerm Q Λ (fun w => (hρ₁ w).2) r.2.1) 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' r.1 := by
  obtain ⟨p, rfl⟩ := (baseIdxEquiv hρ₁ ι).surjective r
  rw [baseBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  exact capBasis_eq_smul_base L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' p

/-- The base element `c_q` is fixed by the idempotent `e(i)` of its top `i`. -/
theorem envMk_e_smul_baseElt [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
          : BaseIdx ν₀ ρ₁ ι) :
    (Env.mk (StendhalAlgebra.e q.top q.isRedOrdered_top) 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q =
      baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q := by
  obtain ⟨⟨⟨⟨⟨⟨i, w, d⟩, hx₀⟩, t, u⟩, hg⟩, hc⟩, b⟩ := q
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  have h := capBasis_eq_smul_base (Λ := Λ) L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B'
    ⟨⟨(⟨(i, 1, 0), hx₀⟩, t, u), hg⟩, b⟩
  rw [topTerm_base hρ₁ hx₀.1] at h
  exact h.symm

/-- **The right action of `e(t)` on the base elements**: it keeps `c_q` if `t` is the bottom of
its generator, and kills it otherwise. -/
theorem envMk_e_smul_baseElt_right [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
          : BaseIdx ν₀ ρ₁ ι)
    (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (ht : IsRedOrdered t) :
    (Env.mk 1 (StendhalAlgebra.e t ht) : Env k Q Λ Λc ℓ le_rfl ν ν₀) •
        baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q =
      if q.1.1.bot = t then baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q else 0 :=
  envMk_e_smul_capBasis L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' ⟨q.1.1, q.2⟩ t ht

end Categorification.Stendhal.CupCap
