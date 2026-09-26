/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Kleshchev
import Categorification.KLR.Crystal.Socle

/-!
# KL I, Theorem 3.17: characters of simple modules are linearly independent

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Theorem 3.17** (TeX lines 2240–2255; Kleshchev's
book, Theorem 5.3.1):

> The character map `ch : G₀(R(ν)) → ℤ[q, q⁻¹] Seq(ν)` is injective. Equivalently, the characters
> of irreducible modules (one from each equivalence class up to grading shifts) are linearly
> independent functions on `Seq(ν)`.

This file proves the **ungraded** form: over any field `k`, for `Q` satisfying the hypotheses of
the basis theorem (`hPQ`, `hP`), the dimension characters `s ↦ dim_k 1_s L` of pairwise
non-isomorphic simple finite-dimensional `R(ν)`-modules `L` on which the dots act nilpotently are
linearly independent over `ℤ`. (Simple graded modules satisfy these hypotheses,
`KLRAlgebra.crystal_hypotheses_of_isGradedSimple`.)

## Proof (Kleshchev, Theorem 5.3.1)

Induction on `|ν|`. Suppose `∑_t c_t ch(L_t) = 0` with some `c_t ≠ 0`. For `|ν| = 0` the algebra
`R(0)` acts by scalars, so all simple modules are isomorphic and the relation is `c_t dim L_t = 0`.
For `|ν| > 0` pick `i` and let `ε = max {ε_i(L_t) | c_t ≠ 0} > 0` (the last letter of a sequence in
the support of some `L_t` with `c_t ≠ 0` gives `ε_i(L_t) > 0`), so `ν = μ + εi`. Restricting the
relation to the sequences `j i^ε` (KL I, Lemma 3.5) kills the `L_t` with `ε_i(L_t) < ε`, and for
`ε_i(L_t) = ε`, Lemma 3.8 gives `Δ_{i^ε} L_t ≅ N_t ⊠ L(i^ε)` with `N_t` simple, `ε_i(N_t) = 0`, so
`ch(L_t)(j i^ε) = ch(N_t)(j) · dim L(i^ε)`. The `N_t` are pairwise non-isomorphic: `L_t` is a
simple quotient of `Ind (N_t ⊠ L(i^ε))`, which has a unique maximal submodule (Lemma 3.7). The
induction hypothesis for `μ` gives `c_t dim L(i^ε) = 0`, a contradiction.

The ingredients are Lemmas 3.5, 3.7 and 3.8 only (in particular neither Lemma 3.9 nor the crystal
operators `ẽ_i`, `f̃_i` are needed: only the top power `ẽ_i^ε` enters, as `HW(Δ_{i^ε} L)`).

## Main results

* `KLRAlgebra.dimCh Q ν M s = dim_k 1_s M` : the (ungraded) character.
* `KLRAlgebra.dimCh_append_const` : `ch(L)(j i^ε) = ch(HW(Δ_{i^ε} L))(j) · dim L(i^ε)` for `L`
  simple with `ε_i(L) = ε` (Lemmas 3.5 and 3.8).
* `KLRAlgebra.nonempty_equiv_of_hwSpace_equiv` : `HW(Δ_{i^ε} L) ≅ HW(Δ_{i^ε} L')` implies
  `L ≅ L'` (Lemma 3.7).
* `KLRAlgebra.thm_3_17_ungraded` (**KL I, Theorem 3.17, ungraded**): the characters of pairwise
  non-isomorphic simple modules (finite-dimensional, nilpotent dots) are `ℤ`-linearly independent.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### Characters -/

section DimCh

variable (Q) (ν : Multiset I) (M : Type*) [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M]

/-- The ungraded character `ch(M)(s) = dim_k 1_s M` of an `R(ν)`-module. -/
def dimCh (s : Seq ν) : ℕ := Module.finrank K (fixSub K M (e s : KLRAlgebra K Q ν))

end DimCh

section FixSubCongr

variable {A : Type*} [Ring A] [Algebra K A]
  {M : Type*} [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
  {M' : Type*} [AddCommGroup M'] [Module K M'] [Module A M'] [IsScalarTower K A M']

omit [DecidableEq I] in
/-- An `A`-linear isomorphism restricts to `a M ≅ a M'`. -/
def fixSubCongr (f : M ≃ₗ[A] M') (a : A) : fixSub K M a ≃ₗ[K] fixSub K M' a where
  toFun v := ⟨f v, by rw [mem_fixSub, ← map_smul, mem_fixSub.1 v.2]⟩
  invFun w := ⟨f.symm w, by rw [mem_fixSub, ← map_smul, mem_fixSub.1 w.2]⟩
  map_add' v w := Subtype.ext (map_add f _ _)
  map_smul' c v := Subtype.ext (f.toLinearMap.map_smul_of_tower c v)
  left_inv v := Subtype.ext (f.symm_apply_apply _)
  right_inv w := Subtype.ext (f.apply_symm_apply _)

omit [DecidableEq I] in
theorem finrank_fixSub_congr (f : M ≃ₗ[A] M') (a : A) :
    Module.finrank K (fixSub K M a) = Module.finrank K (fixSub K M' a) :=
  (fixSubCongr f a).finrank_eq

omit [DecidableEq I] in
theorem fixSub_one : fixSub K M (1 : A) = ⊤ :=
  eq_top_iff.2 fun v _ => by rw [mem_fixSub, one_smul]

end FixSubCongr

/-! ### The top power `Δ_{i^ε}` on characters -/

section Top

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {L : Type*} [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q (μ + ν')) L]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L]

omit [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L] in
/-- Nilpotent dots on `M` give nilpotent dots on `HW(Δ M)`. -/
theorem smulNilpotent_hwSpace [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L]
    (a : Fin (Multiset.card μ))
    (h : SmulNilpotent (x (Seq.posL ν' a) : KLRAlgebra K Q (μ + ν')) L) :
    SmulNilpotent (x a : KLRAlgebra K Q μ) (HWSpace Q μ ν' (ResSub Q μ ν' L)) := by
  obtain ⟨m, hm⟩ := h
  have key : ∀ (r : ℕ) (w : HWSpace Q μ ν' (ResSub Q μ ν' L)),
      ((((x a : KLRAlgebra K Q μ) ^ r • w : HWSpace Q μ ν' (ResSub Q μ ν' L)) :
        ResSub Q μ ν' L) : L) =
        (x (Seq.posL ν' a) : KLRAlgebra K Q (μ + ν')) ^ r • ((w : ResSub Q μ ν' L) : L) := by
    intro r
    induction r with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ r ih =>
      intro w
      rw [pow_succ, mul_smul, ih, coe_hw_smul, coe_resSub_smul, concat_x_tmul_one, mul_smul,
        mem_fixSub.1 (w : ResSub Q μ ν' L).2, ← mul_smul, ← pow_succ]
  exact ⟨m, fun w => Subtype.ext (Subtype.ext (by
    rw [key, hm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]))⟩

omit [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L] in
/-- A sequence `j i^ε` with `ε > ε_i(M)` is not in the support of `M`. -/
theorem dimCh_append_const_eq_zero [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L]
    (hlt : epsI Q (μ + ν') i L < Multiset.card ν') (j : Seq μ) :
    dimCh Q (μ + ν') L (j.append (Seq.constSeq hν')) = 0 := by
  have hbot : fixSub K L (e (j.append (Seq.constSeq hν')) : KLRAlgebra K Q (μ + ν')) = ⊥ := by
    by_contra h
    have h1 := tailLen_le_epsI (i := i) h
    have h2 := Seq.le_tailLen_append_const hν' (i := i) j
    omega
  rw [dimCh, hbot, finrank_bot]

variable [FiniteDimensional K L] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) L]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) L)
  (hε : epsI Q (μ + ν') i L = Multiset.card ν')

include hν' hPQ hP hnil hε in
/-- **The character of `Δ_{i^ε} L`** (KL I, Lemmas 3.5 and 3.8): for `L` simple with
`ε_i(L) = ε = card ν'`, `ch(L)(j i^ε) = ch(HW(Δ_{i^ε} L))(j) · dim L(i^ε)`. -/
theorem dimCh_append_const (j : Seq μ) :
    dimCh Q (μ + ν') L (j.append (Seq.constSeq hν')) =
      dimCh Q μ (HWSpace Q μ ν' (ResSub Q μ ν' L)) j * Module.finrank K (KLRRep hν' Q) := by
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
      (ResSub Q μ ν' L) := fun b => smulNilpotent_resSub b (hnil _)
  haveI := (lemma_3_8 hν' hPQ hP hnil hε).1
  rw [dimCh, ← finrank_fixSub_resSub hν' j,
    ← finrank_fixSub_congr (hwEquiv hν' hPQ hP hnilΔ),
    finrank_fixSub_extTensor (K := K) (e_mul_self j) IsIdempotentElem.one, fixSub_one, finrank_top]
  rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν' hPQ hP in
/-- **Recovering `L` from `HW(Δ_{i^ε} L)`** (KL I, Lemma 3.7): if `L`, `L'` are simple
(finite-dimensional, nilpotent dots) with `ε_i(L) = ε_i(L') = ε = card ν'` and
`HW(Δ_{i^ε} L) ≅ HW(Δ_{i^ε} L')`, then `L ≅ L'`: both are simple quotients of
`Ind (HW(Δ_{i^ε} L') ⊠ L(i^ε))`, which has a unique maximal submodule. -/
theorem nonempty_equiv_of_hwSpace_equiv
    {L' : Type*} [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q (μ + ν')) L']
    [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L'] [FiniteDimensional K L']
    [IsSimpleModule (KLRAlgebra K Q (μ + ν')) L']
    (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) L)
    (hnil' : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) L')
    (hε : epsI Q (μ + ν') i L = Multiset.card ν') (hε' : epsI Q (μ + ν') i L' = Multiset.card ν')
    (φ : HWSpace Q μ ν' (ResSub Q μ ν' L') ≃ₗ[KLRAlgebra K Q μ]
      HWSpace Q μ ν' (ResSub Q μ ν' L)) :
    Nonempty (L ≃ₗ[KLRAlgebra K Q (μ + ν')] L') := by
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
      (ResSub Q μ ν' L) := fun b => smulNilpotent_resSub b (hnil _)
  have hnilΔ' : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
      (ResSub Q μ ν' L') := fun b => smulNilpotent_resSub b (hnil' _)
  obtain ⟨h1, h2, h3⟩ := lemma_3_8 hν' hPQ hP hnil hε
  obtain ⟨h1', h2', h3'⟩ := lemma_3_8 hν' hPQ hP hnil' hε'
  set N := HWSpace Q μ ν' (ResSub Q μ ν' L')
  haveI : Nontrivial N := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) N
  obtain ⟨P', -, huniq, -⟩ := lemma_3_7_head hν' hPQ hP (N := N) h3'
  let Φ := hwEquiv hν' hPQ hP hnilΔ
  let Φ' := hwEquiv hν' hPQ hP hnilΔ'
  let g' : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' L' := Φ'.toLinearMap
  let g : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' L :=
    Φ.toLinearMap ∘ₗ (ExtTensor.congr φ (LinearEquiv.refl _ _)).toLinearMap
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  have hy0 : ExtTensor.tmul v (lMk hν' Q 1) ≠ 0 :=
    extTensor_tmul_ne_zero (K := K) (A := KLRAlgebra K Q μ) (B := KLRAlgebra K Q ν') hv
      (lMk_one_ne_zero (K := K) (Q := Q) hν')
  have hg0 : g ≠ 0 := fun h0 => hy0 (by
    have := LinearMap.congr_fun h0 (ExtTensor.tmul v (lMk hν' Q 1))
    rw [LinearMap.zero_apply] at this
    exact (ExtTensor.congr φ (LinearEquiv.refl _ _)).injective
      (Φ.injective (this.trans (map_zero Φ).symm) |>.trans (map_zero _).symm))
  have hg0' : g' ≠ 0 := fun h0 => hy0 (by
    have := LinearMap.congr_fun h0 (ExtTensor.tmul v (lMk hν' Q 1))
    rw [LinearMap.zero_apply] at this
    exact Φ'.injective (this.trans (map_zero Φ').symm))
  have hπ := indAdjBwd_surjective hg0
  have hπ' := indAdjBwd_surjective hg0'
  have hc : IsCoatom (LinearMap.ker (indAdjBwd g)) := by
    haveI := IsSimpleModule.congr ((indAdjBwd g).quotKerEquivOfSurjective hπ)
    exact isSimpleModule_iff_isCoatom.1 inferInstance
  have hc' : IsCoatom (LinearMap.ker (indAdjBwd g')) := by
    haveI := IsSimpleModule.congr ((indAdjBwd g').quotKerEquivOfSurjective hπ')
    exact isSimpleModule_iff_isCoatom.1 inferInstance
  have hker : LinearMap.ker (indAdjBwd g) = LinearMap.ker (indAdjBwd g') :=
    (huniq _ hc).trans (huniq _ hc').symm
  exact ⟨((indAdjBwd g).quotKerEquivOfSurjective hπ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((indAdjBwd g').quotKerEquivOfSurjective hπ'))⟩

end Top

/-! ### The weight `0` -/

section Zero

variable {ν : Multiset I}

omit [DecidableEq I] in
theorem subsingleton_seq_of_card_eq_zero (h : Multiset.card ν = 0) : Subsingleton (Seq ν) :=
  ⟨fun s t => Subtype.ext (funext fun a => absurd a.2 (by omega))⟩

/-- `R(ν)` acts by scalars if `|ν| = 0`. -/
theorem exists_eq_algebraMap_of_card_eq_zero (h : Multiset.card ν = 0) (r : KLRAlgebra K Q ν) :
    ∃ c : K, r = algebraMap K (KLRAlgebra K Q ν) c := by
  have hr : r ∈ Algebra.adjoin K (Set.range (e (k := K) (Q := Q) (ν := ν)) ∪ Set.range x ∪
      Set.range ψ) := by rw [adjoin_gens]; trivial
  haveI := subsingleton_seq_of_card_eq_zero h
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨s, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩
    · refine ⟨1, ?_⟩
      rw [map_one, ← sum_e, Fintype.sum_subsingleton _ s]
    · exact absurd a.2 (by omega)
    · exact ⟨0, by rw [map_zero, ψ_eq_zero j (by omega)]⟩
  | algebraMap c => exact ⟨c, rfl⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, rfl⟩ := hy
    obtain ⟨d, rfl⟩ := hz
    exact ⟨c + d, (map_add _ _ _).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨c, rfl⟩ := hy
    obtain ⟨d, rfl⟩ := hz
    exact ⟨c * d, (map_mul _ _ _).symm⟩

variable {L : Type*} [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q ν) L]
  [IsScalarTower K (KLRAlgebra K Q ν) L] [IsSimpleModule (KLRAlgebra K Q ν) L]

omit [IsSimpleModule (KLRAlgebra K Q ν) L] in
theorem mem_span_of_card_eq_zero (h : Multiset.card ν = 0) (v : L) (r : KLRAlgebra K Q ν) :
    r • v ∈ Submodule.span K {v} := by
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_card_eq_zero h r
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)

include Q in
/-- A simple `R(ν)`-module is one-dimensional if `|ν| = 0`. -/
theorem finrank_eq_one_of_card_eq_zero (h : Multiset.card ν = 0) : Module.finrank K L = 1 := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) L
  obtain ⟨v, hv⟩ := exists_ne (0 : L)
  let S : Submodule (KLRAlgebra K Q ν) L :=
    { carrier := Submodule.span K {v}
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun r w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        obtain ⟨d, rfl⟩ := exists_eq_algebraMap_of_card_eq_zero h r
        rw [algebraMap_smul, smul_smul]
        exact Submodule.mem_span_singleton.2 ⟨d * c, rfl⟩ }
  have hS : S = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left fun h0 => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h0] at this
    exact (Submodule.mem_bot _).1 this)
  have htop : Submodule.span K {v} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have : w ∈ S := hS ▸ Submodule.mem_top
    exact this
  rw [← finrank_top K L, ← htop, finrank_span_singleton hv]

include Q in
/-- All simple `R(ν)`-modules are isomorphic if `|ν| = 0`. -/
theorem nonempty_equiv_of_card_eq_zero (h : Multiset.card ν = 0)
    {L' : Type*} [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q ν) L']
    [IsScalarTower K (KLRAlgebra K Q ν) L'] [IsSimpleModule (KLRAlgebra K Q ν) L'] :
    Nonempty (L ≃ₗ[KLRAlgebra K Q ν] L') := by
  have h1 := finrank_eq_one_of_card_eq_zero (Q := Q) (L := L) h
  have h2 := finrank_eq_one_of_card_eq_zero (Q := Q) (L := L') h
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h1
  haveI : FiniteDimensional K L' := Module.finite_of_finrank_eq_succ h2
  let f : L ≃ₗ[K] L' := LinearEquiv.ofFinrankEq L L' (h1.trans h2.symm)
  exact ⟨{ f with
    map_smul' := fun r v => by
      obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_card_eq_zero h r
      simp only [algebraMap_smul, RingHom.id_apply]
      exact f.map_smul c v }⟩

end Zero

/-! ### Theorem 3.17 -/

section Thm317

variable {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

universe u v

include hPQ hP in
/-- The induction behind Theorem 3.17. -/
theorem thm_3_17_aux (n : ℕ) : ∀ (ν : Multiset I), Multiset.card ν = n →
    ∀ {T : Type v} [Fintype T] (L : T → Type u) [∀ t, AddCommGroup (L t)]
      [∀ t, Module K (L t)] [∀ t, Module (KLRAlgebra K Q ν) (L t)]
      [∀ t, IsScalarTower K (KLRAlgebra K Q ν) (L t)] [∀ t, FiniteDimensional K (L t)]
      [∀ t, IsSimpleModule (KLRAlgebra K Q ν) (L t)],
      (∀ t a, SmulNilpotent (x a : KLRAlgebra K Q ν) (L t)) →
      (∀ t t', Nonempty (L t ≃ₗ[KLRAlgebra K Q ν] L t') → t = t') →
      ∀ c : T → ℤ, (∀ s, ∑ t, c t * (dimCh Q ν (L t) s : ℤ) = 0) → c = 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hν T _ L _ _ _ _ _ _ hnil hL c hc
  by_contra hc0
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hc0
  simp only [Pi.zero_apply] at ht₀
  haveI : ∀ t, Nontrivial (L t) := fun t => IsSimpleModule.nontrivial (KLRAlgebra K Q ν) (L t)
  obtain ⟨s₀, hs₀⟩ := seqSupp_nonempty (Q := Q) (ν := ν) (M := L t₀)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `|ν| = 0`: all simple modules are isomorphic
    subst hn
    haveI : Subsingleton T := ⟨fun t t' => hL t t' (nonempty_equiv_of_card_eq_zero hν)⟩
    have h := hc s₀
    rw [Fintype.sum_subsingleton _ t₀] at h
    have hpos : 0 < dimCh Q ν (L t₀) s₀ := by
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (mem_seqSupp.1 hs₀)
      exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩
    rcases mul_eq_zero.1 h with h | h
    · exact ht₀ h
    · omega
  -- the last letter `i` of a sequence in the support of `L t₀`
  set i : I := s₀.1 ⟨Multiset.card ν - 1, by omega⟩
  have hi : 1 ≤ epsI Q ν i (L t₀) := by
    have : Seq.HasTail i s₀ 1 := ⟨by omega, fun a ha => by
      rw [show a = ⟨Multiset.card ν - 1, by omega⟩ from
        Fin.ext (show a.val = Multiset.card ν - 1 by have := a.2; omega)]⟩
    exact (Seq.le_tailLen this).trans (tailLen_le_epsI (mem_seqSupp.1 hs₀))
  set S := Finset.univ.filter fun t => c t ≠ 0
  have ht₀S : t₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, ht₀⟩
  set ε := S.sup fun t => epsI Q ν i (L t) with hεdef
  have hεle : ∀ t ∈ S, epsI Q ν i (L t) ≤ ε := fun t ht => Finset.le_sup (f := fun t =>
    epsI Q ν i (L t)) ht
  obtain ⟨t₁, ht₁S, ht₁⟩ := Finset.exists_mem_eq_sup S ⟨t₀, ht₀S⟩ fun t => epsI Q ν i (L t)
  have hε1 : 1 ≤ ε := hi.trans (hεle t₀ ht₀S)
  -- `ν = μ + ε i`
  obtain ⟨s₁, hs₁, hst₁⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := ν) (i := i) (M := L t₁)
  have hrep : Multiset.replicate ε i ≤ ν :=
    replicate_le_of_hasTail (Seq.hasTail_iff.2 (by rw [hst₁, ← ht₁]))
  obtain ⟨μ, hμ⟩ := Multiset.le_iff_exists_add.1 hrep
  rw [add_comm] at hμ
  clear_value ε i
  obtain ⟨ν', hν'def⟩ : ∃ ν', Multiset.replicate ε i = ν' := ⟨_, rfl⟩
  rw [hν'def] at hμ
  subst hμ
  have hν' : ∀ a ∈ ν', a = i := fun a ha => Multiset.eq_of_mem_replicate (hν'def ▸ ha)
  have hcard : Multiset.card ν' = ε := by rw [← hν'def, Multiset.card_replicate]
  -- the modules `N_t = HW(Δ_{i^ε} L_t)` for `ε_i(L_t) = ε`
  let T' := {t : T // epsI Q (μ + ν') i (L t) = Multiset.card ν'}
  let N : T' → Type u := fun t => HWSpace Q μ ν' (ResSub Q μ ν' (L t.1))
  haveI hNs : ∀ t : T', IsSimpleModule (KLRAlgebra K Q μ) (N t) := fun t =>
    (lemma_3_8 hν' hPQ hP (hnil t.1) t.2).2.1
  have hNnil : ∀ (t : T') (a : Fin (Multiset.card μ)),
      SmulNilpotent (x a : KLRAlgebra K Q μ) (N t) := fun t a =>
    smulNilpotent_hwSpace a (hnil t.1 _)
  have hNL : ∀ t t' : T', Nonempty (N t ≃ₗ[KLRAlgebra K Q μ] N t') → t = t' := by
    rintro t t' ⟨φ⟩
    exact Subtype.ext (hL t.1 t'.1 (nonempty_equiv_of_hwSpace_equiv hν' hPQ hP (hnil t.1)
      (hnil t'.1) t.2 t'.2 φ.symm))
  set d := Module.finrank K (KLRRep hν' Q)
  have hd : 0 < d := Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, lMk_one_ne_zero hν'⟩
  have hμcard : Multiset.card μ < n := by
    rw [← hν, Multiset.card_add, hcard]; omega
  have hrel : ∀ j : Seq μ, ∑ t : T', (c t.1 * d) * (dimCh Q μ (N t) j : ℤ) = 0 := by
    intro j
    have h := hc (j.append (Seq.constSeq hν'))
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun t => epsI Q (μ + ν') i (L t) = Multiset.card ν')] at h
    have h0 : ∑ t : {t : T // ¬ epsI Q (μ + ν') i (L t) = Multiset.card ν'},
        c t.1 * (dimCh Q (μ + ν') (L t.1) (j.append (Seq.constSeq hν')) : ℤ) = 0 := by
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hct : c t.1 = 0
      · rw [hct, zero_mul]
      · have hle := hεle t.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hct⟩)
        rw [dimCh_append_const_eq_zero hν' (by have := t.2; omega) j, Nat.cast_zero, mul_zero]
    rw [h0, add_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [dimCh_append_const hν' hPQ hP (hnil t.1) t.2 j]
    push_cast
    ring
  have := ih (Multiset.card μ) hμcard μ rfl N hNnil hNL (fun t => c t.1 * d) hrel
  have ht₁' : epsI Q (μ + ν') i (L t₁) = Multiset.card ν' := by rw [hcard, ← ht₁, hεdef]
  have := congrFun this ⟨t₁, ht₁'⟩
  simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at this
  rcases this with h | h
  · exact (Finset.mem_filter.1 ht₁S).2 h
  · omega

include hPQ hP in
/-- **KL I, Theorem 3.17** (ungraded; Kleshchev, Theorem 5.3.1): over any field, the characters
`s ↦ dim_k 1_s L_t` of pairwise non-isomorphic simple `R(ν)`-modules `L_t` (finite-dimensional,
with nilpotent dots; e.g. simple graded modules) are linearly independent over `ℤ`. -/
theorem thm_3_17_ungraded {ν : Multiset I} {T : Type v} (L : T → Type u)
    [∀ t, AddCommGroup (L t)] [∀ t, Module K (L t)] [∀ t, Module (KLRAlgebra K Q ν) (L t)]
    [∀ t, IsScalarTower K (KLRAlgebra K Q ν) (L t)] [∀ t, FiniteDimensional K (L t)]
    [∀ t, IsSimpleModule (KLRAlgebra K Q ν) (L t)]
    (hnil : ∀ t a, SmulNilpotent (x a : KLRAlgebra K Q ν) (L t))
    (hL : ∀ t t', Nonempty (L t ≃ₗ[KLRAlgebra K Q ν] L t') → t = t') :
    LinearIndependent ℤ (fun t => fun s : Seq ν => (dimCh Q ν (L t) s : ℤ)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro F
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hc := thm_3_17_aux hPQ hP _ ν rfl (T := F) (fun t => L t.1) (fun t => hnil t.1)
    (fun t t' h => Subtype.ext (hL t.1 t'.1 h)) g (fun s => by
      have := congrFun hg s
      simpa [Finset.sum_apply] using this)
  exact congrFun hc

end Thm317

end KLRAlgebra

end Categorification.KLR
