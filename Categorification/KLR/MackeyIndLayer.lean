/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyRightFree

/-!
# The layers of the Mackey filtration of an induced module

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, applied to an induced module
`Ind N = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} N`. For a top cut at `n`, the step `F_c ⊆ Ind N`
(`indMackeyStep n c`) is the span of the `r ⊗ x` with `r` in the step `c` of the Mackey
filtration of the KLR algebra (`mackeyFilt n |ν| c`), and `F_{c-1}` is `indMackeyLower n c`
(`⊥` for `c = 0`). In the coordinates `Ind N ≅ ⊕_u N` of Proposition 2.16 (`indDecompOf`),

* `F_{c-1}` consists of the elements whose coordinates vanish at every shuffle `u` such that
  `u⁻¹` has at least `c` strands from the bottom block `ν'` to the top positions `< n`
  (`mem_indMackeyLower_iff`);
* the layer `F_c / F_{c-1}` (`IndMackeyLayer n c`) is `⊕_{u : crossCount(u⁻¹) = c} N` as a
  `k`-module (`indMackeyLayerEquiv`), the class of `ŵ_u^* ⊗ x` being `x` at `u`
  (`indMackeyLayerEquiv_mk_hatWRevSubOf`);
* every element of `R(ν + ν')` preserving the Mackey filtration acts on the layer
  (`indMackeyLayerAct`), and a loading idempotent `e(s)` acts on the coordinate at `u` by
  `1_{u s}` (`indMackeyLayerEquiv_act_e`).

Symmetric `Q` (`KLRSymm Q`) for the coordinates, any commutative ring `k`, any choice `σ` of
reduced words for the shuffles.

## Main definitions

* `KLRAlgebra.indMackeyStep`, `KLRAlgebra.indMackeyLower`, `KLRAlgebra.IndMackeyLayer`,
  `KLRAlgebra.indMackeyLayerAct`, `KLRAlgebra.indMackeyLayerEquiv`.

## Main results

* `KLRAlgebra.mem_indMackeyStep_iff`, `KLRAlgebra.mem_indMackeyLower_iff`.
* `KLRAlgebra.indMackeyLayerEquiv_mk`, `KLRAlgebra.indMackeyLayerEquiv_mk_hatWRevSubOf`,
  `KLRAlgebra.indMackeyLayerEquiv_act_e`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' : Multiset I} (N : Type*) [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν ν') N] [IsScalarTower k (TensorKLR Q ν ν') N]

local notation "m" => Multiset.card (ν + ν')
local notation "Sh" => Shuffle (Seq.card_add' ν ν')

section Steps

variable (Q ν ν') in
/-- The step `F_c` of the Mackey filtration of `Ind N`, for the top cut at `n`. -/
def indMackeyStep (n c : ℕ) : Submodule k (Ind Q ν ν' N) :=
  Submodule.span k {y | ∃ (w : IndBimod Q ν ν') (x : N),
    (w : KLRAlgebra k Q (ν + ν')) ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c ∧
      BalancedTensor.tmul w x = y}

variable (Q ν ν') in
/-- The step `F_{c-1}` below `F_c` (`⊥` for `c = 0`). -/
def indMackeyLower (n : ℕ) : ℕ → Submodule k (Ind Q ν ν' N)
  | 0 => ⊥
  | c + 1 => indMackeyStep Q ν ν' N n c

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
theorem indMackeyStep_mono {n c c' : ℕ} (hc : c ≤ c') :
    indMackeyStep Q ν ν' N n c ≤ indMackeyStep Q ν ν' N n c' :=
  Submodule.span_mono fun _ ⟨w, x, hw, hy⟩ => ⟨w, x, mackeyFilt_mono hc hw, hy⟩

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
theorem indMackeyLower_le (n c : ℕ) :
    indMackeyLower Q ν ν' N n c ≤ indMackeyStep Q ν ν' N n c := by
  cases c with
  | zero => exact bot_le
  | succ c => exact indMackeyStep_mono N (Nat.le_succ c)

variable (Q ν ν') in
/-- The layer `F_c / F_{c-1}` of the Mackey filtration of `Ind N`. -/
abbrev IndMackeyLayer (n c : ℕ) : Type _ :=
  indMackeyStep Q ν ν' N n c ⧸
    (indMackeyLower Q ν ν' N n c).comap (indMackeyStep Q ν ν' N n c).subtype

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
/-- An element preserving every step of the Mackey filtration of `R(ν + ν')` preserves every
step of the Mackey filtration of `Ind N`. -/
theorem smul_mem_indMackeyStep {n : ℕ} {z : KLRAlgebra k Q (ν + ν')}
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c →
      z * y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c)
    {c : ℕ} {y : Ind Q ν ν' N} (hy : y ∈ indMackeyStep Q ν ν' N n c) :
    z • y ∈ indMackeyStep Q ν ν' N n c := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, x, hw, rfl⟩ := hy
    rw [BalancedTensor.smul_tmul']
    exact Submodule.subset_span ⟨z • w, x, hz c _ hw, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ a h

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
theorem smul_mem_indMackeyLower {n : ℕ} {z : KLRAlgebra k Q (ν + ν')}
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c →
      z * y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c)
    {c : ℕ} {y : Ind Q ν ν' N} (hy : y ∈ indMackeyLower Q ν ν' N n c) :
    z • y ∈ indMackeyLower Q ν ν' N n c := by
  cases c with
  | zero =>
    rw [indMackeyLower, Submodule.mem_bot] at hy ⊢
    rw [hy, smul_zero]
  | succ c => exact smul_mem_indMackeyStep N hz hy

/-- The action on the layer of an element preserving the Mackey filtration. -/
def indMackeyLayerAct {n : ℕ} (z : KLRAlgebra k Q (ν + ν'))
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c →
      z * y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c) (c : ℕ) :
    IndMackeyLayer Q ν ν' N n c →ₗ[k] IndMackeyLayer Q ν ν' N n c :=
  Submodule.mapQ _ _
    (((DistribSMul.toLinearMap k (Ind Q ν ν' N) z).comp
      (indMackeyStep Q ν ν' N n c).subtype).codRestrict _ fun y =>
        smul_mem_indMackeyStep N hz y.2)
    fun _ hy => smul_mem_indMackeyLower N hz hy

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
theorem indMackeyLayerAct_mk {n : ℕ} (z : KLRAlgebra k Q (ν + ν'))
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c →
      z * y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c) {c : ℕ}
    (y : indMackeyStep Q ν ν' N n c) :
    indMackeyLayerAct N z hz c (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨z • (y : Ind Q ν ν' N), smul_mem_indMackeyStep N hz y.2⟩ :=
  rfl

end Steps

section Coords

variable (hsym : KLRSymm Q) {σ : Shuffle (Seq.card_add' ν ν') → List ℕ}
  (hσ : ∀ u : Shuffle (Seq.card_add' ν ν'), IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

include hsym hσ in
/-- `F_c` in the coordinates of Proposition 2.16. -/
theorem mem_indMackeyStep_iff {n c : ℕ} (hn : n ≤ m) (y : Ind Q ν ν' N) :
    y ∈ indMackeyStep Q ν ν' N n c ↔
      ∀ u : Sh, c < crossCount n (Multiset.card ν) u.1⁻¹ → indDecompOf σ hsym hσ N y u = 0 :=
  mem_span_tmul_mackeyFilt_iff hsym hσ N hn y

include hsym hσ in
/-- `F_{c-1}` in the coordinates of Proposition 2.16. -/
theorem mem_indMackeyLower_iff {n c : ℕ} (hn : n ≤ m) (y : Ind Q ν ν' N) :
    y ∈ indMackeyLower Q ν ν' N n c ↔
      ∀ u : Sh, c ≤ crossCount n (Multiset.card ν) u.1⁻¹ → indDecompOf σ hsym hσ N y u = 0 := by
  cases c with
  | zero =>
    rw [indMackeyLower, Submodule.mem_bot]
    refine ⟨fun h u _ => by rw [h, map_zero]; rfl, fun h => ?_⟩
    apply (indDecompOf σ hsym hσ N).injective
    rw [map_zero]
    exact funext fun u => h u (Nat.zero_le _)
  | succ c =>
    rw [indMackeyLower, mem_indMackeyStep_iff N hsym hσ hn]
    exact forall_congr' fun u => imp_congr_left Nat.lt_iff_add_one_le

/-- The shuffles `u` such that `u⁻¹` has exactly `c` crossing strands. -/
abbrev LayerShuffle (n c : ℕ) : Type _ := {u : Sh // crossCount n (Multiset.card ν) u.1⁻¹ = c}

include hsym hσ in
/-- The coordinates of `F_c` at the shuffles of the layer. -/
def indMackeyLayerCoord (n c : ℕ) :
    indMackeyStep Q ν ν' N n c →ₗ[k] (LayerShuffle (ν := ν) (ν' := ν') n c → N) :=
  (LinearMap.pi fun u : LayerShuffle (ν := ν) (ν' := ν') n c => LinearMap.proj u.1).comp
    ((indDecompOf σ hsym hσ N).toLinearMap.comp (indMackeyStep Q ν ν' N n c).subtype)

theorem indMackeyLayerCoord_apply {n c : ℕ} (y : indMackeyStep Q ν ν' N n c)
    (u : LayerShuffle (ν := ν) (ν' := ν') n c) :
    indMackeyLayerCoord N hsym hσ n c y u = indDecompOf σ hsym hσ N y u.1 := rfl

include hsym hσ in
theorem ker_indMackeyLayerCoord {n c : ℕ} (hn : n ≤ m) :
    LinearMap.ker (indMackeyLayerCoord N hsym hσ n c) =
      (indMackeyLower Q ν ν' N n c).comap (indMackeyStep Q ν ν' N n c).subtype := by
  ext y
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    mem_indMackeyLower_iff N hsym hσ hn]
  have hy := (mem_indMackeyStep_iff N hsym hσ hn (y : Ind Q ν ν' N)).1 y.2
  constructor
  · intro h u hu
    rcases hu.lt_or_eq with hlt | heq
    · exact hy u hlt
    · exact congrFun h ⟨u, heq.symm⟩
  · intro h
    exact funext fun u => h u.1 u.2.ge

include hsym hσ in
theorem indMackeyLayerCoord_surjective {n c : ℕ} (hn : n ≤ m) :
    Function.Surjective (indMackeyLayerCoord N hsym hσ n c) := by
  classical
  intro g
  let g' : Sh → N := fun u =>
    if hu : crossCount n (Multiset.card ν) u.1⁻¹ = c then g ⟨u, hu⟩ else 0
  have hmem : (indDecompOf σ hsym hσ N).symm g' ∈ indMackeyStep Q ν ν' N n c := by
    rw [mem_indMackeyStep_iff N hsym hσ hn, LinearEquiv.apply_symm_apply]
    intro u hu
    exact dite_eq_right_of_eq_false (eq_false (ne_of_gt hu))
  refine ⟨⟨_, hmem⟩, funext fun u => ?_⟩
  rw [indMackeyLayerCoord_apply]
  change (indDecompOf σ hsym hσ N) ((indDecompOf σ hsym hσ N).symm g') u.1 = g u
  rw [LinearEquiv.apply_symm_apply]
  exact dite_eq_left_of_eq_true (eq_true u.2)

include hsym hσ in
/-- **The layers of the Mackey filtration of `Ind N`**:
`F_c / F_{c-1} ≅ ⊕_{u : crossCount(u⁻¹) = c} N` as `k`-modules. -/
def indMackeyLayerEquiv {n : ℕ} (hn : n ≤ m) (c : ℕ) :
    IndMackeyLayer Q ν ν' N n c ≃ₗ[k] (LayerShuffle (ν := ν) (ν' := ν') n c → N) :=
  (Submodule.quotEquivOfEq _ _ (ker_indMackeyLayerCoord N hsym hσ hn).symm).trans
    ((indMackeyLayerCoord N hsym hσ n c).quotKerEquivOfSurjective
      (indMackeyLayerCoord_surjective N hsym hσ hn))

theorem indMackeyLayerEquiv_mk {n : ℕ} (hn : n ≤ m) {c : ℕ}
    (y : indMackeyStep Q ν ν' N n c) (u : LayerShuffle (ν := ν) (ν' := ν') n c) :
    indMackeyLayerEquiv N hsym hσ hn c (Submodule.Quotient.mk y) u =
      indDecompOf σ hsym hσ N y u.1 := rfl

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
include hσ in
theorem tmul_hatWRevSubOf_mem_indMackeyStep {n : ℕ} (hn : n ≤ m) (u : Sh) (x : N) :
    (BalancedTensor.tmul (hatWRevSubOf σ u) x : Ind Q ν ν' N) ∈
      indMackeyStep Q ν ν' N n (crossCount n (Multiset.card ν) u.1⁻¹) :=
  Submodule.subset_span ⟨hatWRevSubOf σ u, x, by
    rw [coe_hatWRevSubOf]; exact hatWRevOf_mem_mackeyFilt hσ hn u, rfl⟩

/-- The class of `ŵ_u^* ⊗ x` in the layer is `x` at `u`. -/
theorem indMackeyLayerEquiv_mk_hatWRevSubOf {n c : ℕ} (hn : n ≤ m) (u : Sh)
    (hu : crossCount n (Multiset.card ν) u.1⁻¹ = c) (x : N) :
    indMackeyLayerEquiv N hsym hσ hn c (Submodule.Quotient.mk
      ⟨_, hu ▸ tmul_hatWRevSubOf_mem_indMackeyStep N hσ hn u x⟩) =
      Pi.single ⟨u, hu⟩ x := by
  funext u'
  rw [indMackeyLayerEquiv_mk]
  change indDecompOf σ hsym hσ N (BalancedTensor.tmul (hatWRevSubOf σ u) x) u'.1 = _
  rw [indDecompOf_tmul_hatWRevSubOf, Pi.single_apply, Pi.single_apply]
  by_cases h : u'.1 = u
  · rw [ite_eq_left h, ite_eq_left (Subtype.ext h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (congrArg Subtype.val h')]

theorem indMackeyLayerEquiv_act_e {n : ℕ} (hn : n ≤ m) {c : ℕ} (s : Seq (ν + ν'))
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c →
      (e s : KLRAlgebra k Q (ν + ν')) * y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c)
    (v : IndMackeyLayer Q ν ν' N n c) (u : LayerShuffle (ν := ν) (ν' := ν') n c) :
    indMackeyLayerEquiv N hsym hσ hn c (indMackeyLayerAct N (e s) hz c v) u =
      concatIdem (Q := Q) (u.1.1 • s) • indMackeyLayerEquiv N hsym hσ hn c v u := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [indMackeyLayerAct_mk, indMackeyLayerEquiv_mk, indMackeyLayerEquiv_mk]
  exact indDecompOf_e_smul σ hsym hσ N s y u.1

end Coords

end KLRAlgebra

end Categorification.KLR
