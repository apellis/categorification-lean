/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftProjectiveViolated
import Categorification.WeightedKLR.Rigidity.CupCapFunctor

/-!
# `K^{λ⁺}_λ` is projective as a left `T^λ`-module, for a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, the discussion after Lemma 7.17, in the case `j = ℓ` (the cap
right of all red strands of `λ`). For symmetric `Q`, with (max1) scalars that are units, `L`
supported on the loadings `μ ⋯ μ*`, the pull-off identity `PullOffLeft` and bases `B′_t` of the
pieces `L e(t)`, the bimodule `K^{λ⁺}_λ` is, as a left `T^λ`-module,
`⨁_q T^λ e(i_q) ≅ ⨁_{(i, t, u)} T^λ e(i) ⊗_k L e(t)`, the sum over the base indices
`q = ((e(i), t, u), b′)` (`capBimoduleEquiv`). Each summand `T^λ e(i)` is a direct summand of
`T^λ`, so `K^{λ⁺}_λ` is a projective left `T^λ`-module (`projective_capBimodule`). The same holds
when each `L e(t)` is free over `k`, in particular when `k` is a field
(`projective_capBimodule_of_free`).

The isomorphism comes from `B″`: `K̃^{λ⁺}_λ = ⨁_q T̃^λ c_q` (`baseSum`), and the violated
diagrams are the sums with violated coefficients (`violated_le_baseViolated`), so the quotient
by them is `⨁_q T^λ c_q`.

Route hypotheses (tracked, see the README): `hκ`, `hL`, `hP`, as for `capBasis`; the freeness of
the pieces `L e(t)` over `k`, where Webster's argument needs only projectivity.

## Main definitions

* `CupCap.capBimoduleEquiv`: `K^{λ⁺}_λ ≅ ⨁_q T^λ e(i_q)` as left `T^λ`-modules.

## Main results

* `CupCap.projective_capBimodule`: `K^{λ⁺}_λ` is a projective left `T^λ`-module.
* `CupCap.projective_capBimodule_of_free`: the same, for free pieces `L e(t)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

attribute [local instance 1200] Ring.toIntAlgebra

/-! ### Idempotent left ideals are projective -/

/-- The left ideal `R e` of an idempotent is a projective `R`-module. -/
theorem projective_span_singleton_of_isIdempotentElem {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) : Module.Projective R (Submodule.span R {e}) := by
  refine Module.Projective.of_split (Submodule.span R {e}).subtype
    { toFun := fun r => ⟨r * e, Submodule.mem_span_singleton.2 ⟨r, smul_eq_mul r e⟩⟩
      map_add' := fun r r' => Subtype.ext (add_mul r r' e)
      map_smul' := fun c r => Subtype.ext (by
        change c * r * e = c * (r * e)
        rw [mul_assoc]) } ?_
  refine LinearMap.ext fun p => Subtype.ext ?_
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 p.2
  change (p : R) * e = p
  rw [← hr, smul_eq_mul, mul_assoc, he.eq]

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "V" => StendhalAlgebra.violatedIdeal k Q Λ ν

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-- The idempotent `e(i)` in `T^λ`. -/
abbrev tensorIdem (i : Seq (stendhalWeight ℓ ν)) (hi : IsRedOrdered i) : TA :=
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e i hi)

theorem isIdempotentElem_tensorIdem (i : Seq (stendhalWeight ℓ ν)) (hi : IsRedOrdered i) :
    IsIdempotentElem (tensorIdem (k := k) (Q := Q) (Λ := Λ) i hi) := by
  change _ * _ = _
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e _ * StendhalAlgebraAllOrders.e _ = _
  rw [StendhalAlgebraAllOrders.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

theorem tensorAlgebra_mk_eq_zero {a : T} (ha : a ∈ V) : TensorProductAlgebra.mk Q Λ ν a = 0 := by
  rw [← map_zero (TensorProductAlgebra.mk Q Λ ν)]
  exact (RingCon.eq _).2 (((V).rel_iff a 0).2 (by rwa [sub_zero]))

variable (L : Type) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [Module k L]
  [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- The class in `K^{λ⁺}_λ` of an element of `K̃^{λ⁺}_λ`. -/
def toCapBimodule (y : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    CapBimodule k Q Λ Λc ℓ le_rfl ν ν₀ L :=
  Submodule.Quotient.mk y

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem toCapBimodule_envMk_smul (a : T) (y : CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :
    toCapBimodule L ((Env.mk a 1 : Env k Q Λ Λc ℓ le_rfl ν ν₀) • y) =
      TensorProductAlgebra.mk Q Λ ν a • toCapBimodule L y :=
  rfl

variable (Q Λ ν) in
/-- The summand `T^λ e(i_q)` of a base index. -/
abbrev baseIdeal {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) : Submodule TA TA :=
  Submodule.span TA {tensorIdem (k := k) (Q := Q) (Λ := Λ) q.top q.isRedOrdered_top}

theorem mk_mul_mem_baseIdeal {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) (a : T) :
    TensorProductAlgebra.mk Q Λ ν a * tensorIdem q.top q.isRedOrdered_top ∈ baseIdeal Q Λ ν q :=
  Submodule.mem_span_singleton.2 ⟨_, smul_eq_mul _ _⟩

variable (Q Λ ν) in
/-- The coefficient `a e(i_q)` in `T^λ e(i_q)`. -/
def baseCoeffFun {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) (a : T) : baseIdeal Q Λ ν q :=
  ⟨TensorProductAlgebra.mk Q Λ ν a * tensorIdem q.top q.isRedOrdered_top,
    mk_mul_mem_baseIdeal q a⟩

theorem baseCoeffFun_zero {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) : baseCoeffFun Q Λ ν q 0 = 0 :=
  Subtype.ext (by
    change TensorProductAlgebra.mk Q Λ ν 0 * _ = 0
    rw [map_zero, zero_mul])

theorem baseCoeffFun_add {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (q : BaseIdx ν₀ ρ₁ ι) (a a' : T) :
    baseCoeffFun Q Λ ν q (a + a') = baseCoeffFun Q Λ ν q a + baseCoeffFun Q Λ ν q a' :=
  Subtype.ext (by
    change TensorProductAlgebra.mk Q Λ ν (a + a') * _ =
      TensorProductAlgebra.mk Q Λ ν a * _ + TensorProductAlgebra.mk Q Λ ν a' * _
    rw [map_add, add_mul])

variable (Q Λ ν) in
/-- The coefficients `(a_q)_q ↦ (a_q e(i_q))_q` in `⨁_q T^λ e(i_q)`. -/
def baseCoeff {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (A : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T) : Π₀ q : BaseIdx ν₀ ρ₁ ι, baseIdeal Q Λ ν q :=
  A.mapRange (baseCoeffFun Q Λ ν) baseCoeffFun_zero

theorem baseCoeff_surjective {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*} :
    Function.Surjective (baseCoeff Q Λ ν (ρ₁ := ρ₁) (ι := ι)) := by
  classical
  have h : ∀ (q : BaseIdx ν₀ ρ₁ ι) (p : baseIdeal Q Λ ν q), ∃ a : T,
      baseCoeffFun Q Λ ν q a = p := fun q p => by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 p.2
    obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k) (V).ringCon r
    exact ⟨a, Subtype.ext hr⟩
  intro b
  refine ⟨b.mapRange (fun q p => if p = 0 then 0 else (h q p).choose) fun q => by simp, ?_⟩
  refine DFinsupp.ext fun q => ?_
  rw [baseCoeff, DFinsupp.mapRange_apply, DFinsupp.mapRange_apply]
  split_ifs with hq
  · rw [hq, baseCoeffFun_zero]
  · exact (h q (b q)).choose_spec

open Classical in
variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **The map `⨁_q T^λ e(i_q) → K^{λ⁺}_λ`**, `(b_q)_q ↦ ∑_q b_q c_q`. -/
def capBimoduleMap [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    (Π₀ q : BaseIdx ν₀ ρ₁ ι, baseIdeal Q Λ ν q) →ₗ[TA] CapBimodule k Q Λ Λc ℓ le_rfl ν ν₀ L :=
  DFinsupp.coprodMap fun q => (LinearMap.toSpanSingleton TA _
    (toCapBimodule L (baseElt Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q))).comp (baseIdeal Q Λ
        ν q).subtype

open Classical in
theorem capBimoduleMap_baseCoeff [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
          : Π₀ _ : BaseIdx ν₀ ρ₁ ι, T) :
    capBimoduleMap Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' (baseCoeff Q Λ ν A) = toCapBimodule
        L (baseSum Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' A) := by
  induction A using DFinsupp.induction with
  | h0 =>
    rw [baseCoeff, DFinsupp.mapRange_zero, map_zero, map_zero]
    exact (Submodule.Quotient.mk_zero _).symm
  | ha q a f _ _ ih =>
    have hadd : baseCoeff Q Λ ν (DFinsupp.single q a + f) =
        baseCoeff Q Λ ν (DFinsupp.single q a) + baseCoeff Q Λ ν f :=
      DFinsupp.mapRange_add _ _ baseCoeffFun_add _ _
    rw [hadd, map_add, ih, map_add]
    change _ = toCapBimodule L _ + toCapBimodule L _
    congr 1
    rw [baseCoeff, DFinsupp.mapRange_single, capBimoduleMap, DFinsupp.coprodMap_apply_single,
      LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
      baseSum_single, toCapBimodule_envMk_smul]
    change (TensorProductAlgebra.mk Q Λ ν a * TensorProductAlgebra.mk Q Λ ν
      (StendhalAlgebra.e q.top q.isRedOrdered_top)) • _ = _
    rw [mul_smul, ← toCapBimodule_envMk_smul, envMk_e_smul_baseElt L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' q]

/-- **`K^{λ⁺}_λ ≅ ⨁_q T^λ e(i_q)` as left `T^λ`-modules** (arXiv:1309.3796v3, after
Lemma 7.17, for the cap at the right end and symmetric `Q`): the sum is over the base indices
`q = ((e(i), t, u), b′)`, `b′ ∈ B′_t`, so `K^{λ⁺}_λ ≅ ⨁_{(i, t, u)} T^λ e(i) ⊗_k L e(t)`. -/
def capBimoduleEquiv [Nontrivial k] [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    (Π₀ q : BaseIdx ν₀ ρ₁ ι, baseIdeal Q Λ ν q) ≃ₗ[TA] CapBimodule k Q Λ Λc ℓ le_rfl ν ν₀ L :=
  LinearEquiv.ofBijective (capBimoduleMap Q Λ Λc ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B') (by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => ?_, fun z => ?_⟩
    · obtain ⟨A, rfl⟩ := baseCoeff_surjective b
      rw [capBimoduleMap_baseCoeff] at hb
      have hv := (Submodule.Quotient.mk_eq_zero _).1 hb
      refine DFinsupp.ext fun q => Subtype.ext ?_
      change TensorProductAlgebra.mk Q Λ ν (A q) * _ = 0
      rw [← map_mul]
      exact tensorAlgebra_mk_eq_zero (mul_e_mem_violatedIdeal_of_baseSum_mem L hQ hρ₁ hρ₂ hρ₃ hκ hL
          hP B' hv q)
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨A, rfl⟩ := baseSum_surjective L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' y
      exact ⟨baseCoeff Q Λ ν A, capBimoduleMap_baseCoeff L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B' A⟩)

/-- **`K^{λ⁺}_λ` is a projective left `T^λ`-module** (arXiv:1309.3796v3, after Lemma 7.17, for
the cap at the right end and symmetric `Q`), given bases of the pieces `L e(t)`. -/
theorem projective_capBimodule [Nontrivial k] [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
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
    Module.Projective TA (CapBimodule k Q Λ Λc ℓ le_rfl ν ν₀ L) := by
  have : ∀ q : BaseIdx ν₀ ρ₁ ι, Module.Projective TA (baseIdeal Q Λ ν q) := fun q =>
    projective_span_singleton_of_isIdempotentElem (isIdempotentElem_tensorIdem _ _)
  exact Module.Projective.of_equiv' (capBimoduleEquiv L hQ hρ₁ hρ₂ hρ₃ hκ hL hP B')

/-- **`K^{λ⁺}_λ` is a projective left `T^λ`-module** (arXiv:1309.3796v3, after Lemma 7.17, for
the cap at the right end and symmetric `Q`) when each piece `L e(t)` is free over `k`; this
holds when `k` is a field.

Route hypotheses (tracked, see the README): `hκ`, `hL`, `hP`, as for `capBasis`, and the freeness
of the pieces, where Webster's argument needs only their projectivity. -/
theorem projective_capBimodule_of_free [Nontrivial k] (hQ : KLRSymm Q)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    [∀ t : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j}, Module.Free k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2)))] :
    Module.Projective TA (CapBimodule k Q Λ Λc ℓ le_rfl ν ν₀ L) := by
  classical
  choose ρ₁ hρ₁ using fun w => exists_reduced m w
  choose ρ₂ hρ₂ using fun w => exists_reduced N w
  choose ρ₃ hρ₃ using fun w => exists_reduced M w
  exact projective_capBimodule (ρ₁ := ρ₁) (ρ₃ := ρ₃) L hQ hρ₁ hρ₂ hρ₃ hκ hL hP
    (fun _ => Module.Free.chooseBasis k _)

end Categorification.Stendhal.CupCap
