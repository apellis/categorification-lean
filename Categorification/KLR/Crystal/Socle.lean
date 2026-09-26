/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Kleshchev

/-!
# KL I, Proposition 3.10: the socle of `Δ_{i^n} M`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Proposition 3.10** (TeX lines 2158–2166; Kleshchev's
book, Theorem 5.1.6):

> For any irreducible `M ∈ R(ν)-mod` and `0 ≤ n ≤ ε_i(M)`, `soc Δ_{i^n} M` is an irreducible
> `R(ν - ni) ⊗ R(ni)`-module of the form `L ⊗ L(i^n)` with `ε_i(L) = ε_i(M) - n`.

We work ungraded, for finite-dimensional `M` with nilpotent dots, writing `ν = (μ' + ν'') + ν'`
with `ν''`, `ν'` of all labels `i`, `card ν' = n`, `card ν'' = ε_i(M) - n`.

## Proof

It differs from the proof in Kleshchev's book, which uses the Kato theorem (KL I Proposition
3.11); here only KL I Lemma 2.1 (the socle of `L(i^m)` as a module over the dots,
`NilHecke.coinvSocle_eq_span_xDelta`) is used. Let `ε = ε_i(M)` and let
`Δ_{i^ε} M ≅ K ⊠ L(i^ε)` with `K` irreducible (Lemma 3.8, applied to `M` viewed as a module over
`R(μ' + (ν'' + ν'))`, `CastMod`). For a simple submodule `S ⊆ Δ_{i^n} M`, the subspace
`T_S = 1_{μ',ν''} S ⊆ S` is nonzero (Lemma 3.6 gives `ε_i(HW(S)) = ε - n`), lies in
`Δ_{i^ε} M`, and is stable under `R(μ') ⊗ 1` and under all dots of the last `ε` strands
(associativity of `ι`, `KLRAlgebra.concat_assoc`). Every nonzero subspace of `K ⊠ L(i^ε)` with
these stability properties contains `K ⊗ [x^δ]` (`KLRAlgebra.tmul_xDelta_mem`). Hence any two
simple submodules of `Δ_{i^n} M` intersect, i.e. coincide.

## Main results

* `KLRAlgebra.CastMod h M` : an `R(ν₂)`-module as an `R(ν₁)`-module along `castKLR`
  (`h : ν₁ = ν₂`), with `isSimpleModule_castMod`, `epsI_castMod`, `smulNilpotent_castMod`.
* `KLRAlgebra.prop_3_10_socle` (**KL I, Proposition 3.10**): for `0 ≤ n ≤ ε_i(M)`, two simple
  submodules of `Δ_{i^n} M` are equal, so `soc Δ_{i^n} M` is irreducible (it is nonzero,
  `nontrivial_resSub_iff`); `KLRAlgebra.socle_resSub_unique` is the same statement for
  `ν = (μ' + ν'') + ν'` with `card ν'' = ε_i(M) - n`;
  `KLRAlgebra.socle_resSub_form` : the socle `S` is `HW(S) ⊠ L(i^n)` (`hwEquiv`) with `HW(S)`
  irreducible and `ε_i(HW(S)) + n = ε_i(M)`.
* `KLRAlgebra.tmul_xDelta_mem` : a nonzero subspace of `K ⊠ L(i^m)` (`K` simple) stable under
  `R(μ) ⊗ 1` and the dots contains `K ⊗ [x^δ]`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### Transport of modules along equalities of weights -/

section CastMod

variable {ν₁ ν₂ : Multiset I}

/-- An `R(ν₂)`-module `M`, viewed as an `R(ν₁)`-module along `castKLR h : R(ν₁) ≃ R(ν₂)`. -/
def CastMod (_h : ν₁ = ν₂) (M : Type*) : Type _ := M

variable (h : ν₁ = ν₂) (M : Type*) [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ν₂) M] [IsScalarTower K (KLRAlgebra K Q ν₂) M]

instance : AddCommGroup (CastMod h M) := inferInstanceAs (AddCommGroup M)

instance : Module K (CastMod h M) := inferInstanceAs (Module K M)

instance [FiniteDimensional K M] : FiniteDimensional K (CastMod h M) :=
  inferInstanceAs (FiniteDimensional K M)

instance : Module (KLRAlgebra K Q ν₁) (CastMod h M) :=
  Module.compHom M (castKLR Q h).toRingHom

variable {h M}

/-- The identity `M → CastMod h M`. -/
def CastMod.of (m : M) : CastMod h M := m

/-- The identity `CastMod h M → M`. -/
def CastMod.val (m : CastMod h M) : M := m

omit [Module K M] [IsScalarTower K (KLRAlgebra K Q ν₂) M] in
theorem castMod_smul_val (r : KLRAlgebra K Q ν₁) (m : CastMod h M) :
    CastMod.val (r • m) = castKLR Q h r • CastMod.val m := rfl

omit [Module K M] [IsScalarTower K (KLRAlgebra K Q ν₂) M] in
theorem castMod_smul (r : KLRAlgebra K Q ν₁) (m : M) :
    r • (CastMod.of (h := h) m) = CastMod.of (castKLR Q h r • m) := rfl

instance : IsScalarTower K (KLRAlgebra K Q ν₁) (CastMod h M) where
  smul_assoc c r m := by
    change CastMod.of (h := h) (castKLR Q h (c • r) • CastMod.val m) =
      CastMod.of (c • (castKLR Q h r • CastMod.val m))
    rw [map_smul, smul_assoc]

omit [Module K M] [IsScalarTower K (KLRAlgebra K Q ν₂) M] in
variable (h M) in
theorem isSimpleModule_castMod [IsSimpleModule (KLRAlgebra K Q ν₂) M] :
    IsSimpleModule (KLRAlgebra K Q ν₁) (CastMod h M) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ν₂) M
  haveI : Nontrivial (CastMod h M) := inferInstanceAs (Nontrivial M)
  refine ⟨fun P => ?_⟩
  let P' : Submodule (KLRAlgebra K Q ν₂) M :=
    { carrier := {m | CastMod.of (h := h) m ∈ P}
      add_mem' := fun ha hb => P.add_mem ha hb
      zero_mem' := P.zero_mem
      smul_mem' := fun r m hm => by
        have := P.smul_mem (castKLR Q h.symm r) (show CastMod.of (h := h) m ∈ P from hm)
        rw [castMod_smul, castKLR_castAlg_symm] at this
        exact this }
  rcases IsSimpleOrder.eq_bot_or_eq_top P' with h' | h'
  · left
    ext m
    exact (Submodule.ext_iff.1 h' (CastMod.val m)).trans Iff.rfl
  · right
    ext m
    exact (Submodule.ext_iff.1 h' (CastMod.val m)).trans Iff.rfl

variable (h M) in
theorem epsI_castMod (i : I) :
    epsI Q ν₁ i (CastMod h M) = epsI Q ν₂ i M := by
  subst h; rfl

omit [Module K M] [IsScalarTower K (KLRAlgebra K Q ν₂) M] in
theorem smulNilpotent_castMod {a : KLRAlgebra K Q ν₁}
    (ha : SmulNilpotent (castKLR Q h a) M) : SmulNilpotent a (CastMod h M) := by
  obtain ⟨N, hN⟩ := ha
  exact ⟨N, fun m => by
    change CastMod.of (h := h) (castKLR Q h (a ^ N) • CastMod.val m) = CastMod.of 0
    rw [map_pow, hN]⟩

end CastMod

/-! ### Associativity bookkeeping -/

section Assoc

variable {μ μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)

omit [DecidableEq I] in
include hν'' hν' in
theorem forall_add_of_forall : ∀ a ∈ ν'' + ν', a = i := fun a ha =>
  (Multiset.mem_add.1 ha).elim (hν'' a) (hν' a)

include hν'' hν' in
/-- `1_{ν'',ν'} = 1` when all labels are `i`. -/
theorem oneConcat_eq_one_of_forall :
    (oneConcat Q ν'' ν' : KLRAlgebra K Q (ν'' + ν')) = 1 := by
  have huniv : concatSet ν'' ν' = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro s
    letI := Seq.uniqueOfForall (forall_add_of_forall hν'' hν')
    exact mem_concatSet.2 ⟨Seq.constSeq hν'', Seq.constSeq hν', Subsingleton.elim _ _⟩
  rw [oneConcat, eSum, huniv, sum_e]

include hν'' hν' in
/-- `ι_{μ',ν''+ν'}(a ⊗ 1) = ι_{μ'+ν'',ν'}(ι_{μ',ν''}(a ⊗ 1) ⊗ 1)` (all labels of `ν''`, `ν'`
equal to `i`), up to `R(μ' + (ν'' + ν')) ≃ R((μ' + ν'') + ν')`. -/
theorem castKLR_concat_tmul_one (a : KLRAlgebra K Q μ') :
    castKLR Q (add_assoc μ' ν'' ν').symm (concat Q μ' (ν'' + ν') (a ⊗ₜ 1)) =
      concat Q (μ' + ν'') ν' (concat Q μ' ν'' (a ⊗ₜ 1) ⊗ₜ 1) := by
  have h := concat_assoc (Q := Q) a (1 : KLRAlgebra K Q ν'') (1 : KLRAlgebra K Q ν')
  rw [concat_one_tmul_one, oneConcat_eq_one_of_forall hν'' hν'] at h
  rw [← h, castKLR_symm_castAlg]

variable {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]

/-- Every dot acts on `Δ M = 1_{μ,ν'} M` through `R(μ) ⊗ R(ν')`, by an element commuting with
`1_T ⊗ 1` for every sum of idempotents `1_T`. -/
theorem exists_tensor_dot (a : Fin (Multiset.card (μ + ν'))) :
    ∃ t : TensorKLR Q μ ν', (∀ v : ResSub Q μ ν' M,
      ((t • v : ResSub Q μ ν' M) : M) = (x a : KLRAlgebra K Q (μ + ν')) • (v : M)) ∧
        ∀ T₀ : Finset (Seq μ), Commute t (eSum Q T₀ ⊗ₜ[K] (1 : KLRAlgebra K Q ν')) := by
  obtain ⟨c, rfl⟩ := (blockEquiv (Seq.card_add' μ ν')).surjective a
  cases c with
  | inl a' =>
    refine ⟨x a' ⊗ₜ 1, fun v => ?_, fun T₀ => ?_⟩
    · rw [coe_resSub_smul, concat_x_tmul_one, mul_smul, mem_fixSub.1 v.2]; rfl
    · rw [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, x_mul_eSum]
  | inr b' =>
    refine ⟨1 ⊗ₜ x b', fun v => ?_, fun T₀ => ?_⟩
    · rw [coe_resSub_smul, concat_one_tmul_x, mul_smul, mem_fixSub.1 v.2]; rfl
    · rw [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one]

end Assoc

/-! ### Subspaces of `K ⊠ L(i^n)` stable under `R(μ) ⊗ 1` and the dots -/

section Stable

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {V : Type*} [AddCommGroup V] [Module K V] [Module (KLRAlgebra K Q μ) V]
  [IsScalarTower K (KLRAlgebra K Q μ) V]

include hν' in
/-- **Every nonzero subspace of `V ⊠ L(i^n)` (`V` simple) stable under `R(μ) ⊗ 1` and under the
dots `1 ⊗ x_b` contains `V ⊗ [x^δ]`.** -/
theorem tmul_xDelta_mem [IsSimpleModule (KLRAlgebra K Q μ) V]
    {P : Submodule K (ExtTensor K V (KLRRep hν' Q))} (hP : P ≠ ⊥)
    (ha : ∀ a : KLRAlgebra K Q μ, ∀ y ∈ P, (a ⊗ₜ[K] 1 : TensorKLR Q μ ν') • y ∈ P)
    (hx : ∀ b, ∀ y ∈ P, ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') • y ∈ P)
    (w₀ : V) : ExtTensor.tmul w₀ (lMk hν' Q (xDelta (Multiset.card ν'))) ∈ P := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  let T : Fin (Multiset.card ν') → Module.End K (ExtTensor K V (KLRRep hν' Q)) := fun b =>
    Algebra.lsmul K K _ ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
  have hD : ∀ ρ : List (Fin (Multiset.card ν')), (Multiset.card ν').choose 2 < ρ.length →
      (ρ.map T).prod = 0 := by
    intro ρ hρ
    have h1 : (ρ.map T).prod = Algebra.lsmul K K (ExtTensor K V (KLRRep hν' Q))
        ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol (ρ.map (X (R := K))).prod : TensorKLR Q μ ν') := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_list_prod, map_list_prod, map_list_prod,
        List.map_map, List.map_map]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro b _
      simp only [Function.comp_apply, pol_X, Algebra.TensorProduct.includeRight_apply, T]
    rw [h1]
    ext y
    simp only [Algebra.lsmul_coe, LinearMap.zero_apply]
    exact one_tmul_pol_smul_eq_zero hν' (prod_x_mem_coinvIdeal ρ hρ) y
  obtain ⟨y, hy, hy0, hyx⟩ := exists_ne_zero_forall_eq_zero T _ hD (P : Set _)
    (fun b v hv => hx b v hv) hz hz0
  obtain ⟨w, rfl⟩ := exists_eq_tmul_xDelta hν' hyx
  have hw0 : w ≠ 0 := fun h => hy0 (by rw [h, ExtTensor.zero_tmul])
  have hspan : Submodule.span (KLRAlgebra K Q μ) {w} = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (by
      rw [Submodule.span_singleton_eq_bot]; exact hw0)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 (hspan ▸ Submodule.mem_top : w₀ ∈ _)
  have := ha a _ hy
  rwa [ExtTensor.smul_tmul, one_smul] at this

end Stable

/-! ### Proposition 3.10 -/

section Prop310

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ((μ' + ν'') + ν')) M)

/-- `M` as a module over `R(μ' + (ν'' + ν'))`. -/
abbrev MAssoc (μ' ν'' ν' : Multiset I) (M : Type*) : Type _ :=
  CastMod (add_assoc μ' ν'' ν').symm M

omit [Module K M] [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) M] in
include hnil in
theorem smulNilpotent_mAssoc (a : Fin (Multiset.card (μ' + (ν'' + ν')))) :
    SmulNilpotent (x a : KLRAlgebra K Q (μ' + (ν'' + ν'))) (MAssoc μ' ν'' ν' M) :=
  smulNilpotent_castMod (by rw [castKLR_x]; exact hnil _)

omit [Module K M] [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) M] in
include hν'' hν' in
theorem oneConcat_smul_mAssoc (m : M) :
    (oneConcat Q μ' (ν'' + ν') : KLRAlgebra K Q (μ' + (ν'' + ν'))) •
        CastMod.of (h := (add_assoc μ' ν'' ν').symm) m =
      CastMod.of (concat Q (μ' + ν'') ν' (oneConcat Q μ' ν'' ⊗ₜ[K] 1) • m) := by
  rw [castMod_smul, ← concat_one_tmul_one, castKLR_concat_tmul_one hν'' hν',
    concat_one_tmul_one]

/-- The dots of the last `card ν'' + card ν'` strands act on `Δ_{i^ε} M` as dots of `M`. -/
theorem one_tmul_x_smul_mAssoc (b : Fin (Multiset.card (ν'' + ν')))
    (z : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
    CastMod.val ((((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b : TensorKLR Q μ' (ν'' + ν')) • z :
        ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) : MAssoc μ' ν'' ν' M) =
      (x (Fin.cast (congrArg Multiset.card (add_assoc μ' ν'' ν').symm) (Seq.posR μ' b)) :
        KLRAlgebra K Q ((μ' + ν'') + ν')) • CastMod.val (z : MAssoc μ' ν'' ν' M) := by
  rw [coe_resSub_smul, concat_one_tmul_x, mul_smul, mem_fixSub.1 z.2, castMod_smul_val,
    castKLR_x]

include hν'' hν' in
theorem concat_tmul_one_smul_mAssoc (a : KLRAlgebra K Q μ')
    (z : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
    CastMod.val (((a ⊗ₜ[K] 1 : TensorKLR Q μ' (ν'' + ν')) • z :
        ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) : MAssoc μ' ν'' ν' M) =
      concat Q (μ' + ν'') ν' (concat Q μ' ν'' (a ⊗ₜ 1) ⊗ₜ[K] 1) •
        CastMod.val (z : MAssoc μ' ν'' ν' M) := by
  rw [coe_resSub_smul, castMod_smul_val, castKLR_concat_tmul_one hν'' hν']

variable [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν')) M]

omit [FiniteDimensional K M] in
include hν' hPQ hP in
theorem epsI_eq_of_embedding' {N : Type*} [AddCommGroup N] [Module K N]
    [Module (KLRAlgebra K Q (μ' + ν'')) N] [IsScalarTower K (KLRAlgebra K Q (μ' + ν'')) N]
    [FiniteDimensional K N] [Nontrivial N] {c : ℕ}
    (hε : epsI Q ((μ' + ν'') + ν') i M = c + Multiset.card ν')
    (f : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q (μ' + ν'') ν'] ResSub Q (μ' + ν'') ν' M)
    (hf : Function.Injective f) : epsI Q (μ' + ν'') i N = c := by
  have := lemma_3_6 hν' hPQ hP f hf
  omega

variable (hε : epsI Q ((μ' + ν'') + ν') i M = Multiset.card ν'' + Multiset.card ν')

include hν' hPQ hP hnil hε in
/-- A simple submodule `S ⊆ Δ_{i^n} M` is `HW(S) ⊠ L(i^n)` with `ε_i(HW(S)) = ε_i(M) - n`. -/
theorem epsI_hwSpace_of_simple
    (S : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S] :
    epsI Q (μ' + ν'') i (HWSpace Q (μ' + ν'') ν' S) = Multiset.card ν'' := by
  have hnilS := fun b => smulNilpotent_submodule S (smulNilpotent_resSub b (hnil _))
  haveI : FiniteDimensional K S :=
    Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  haveI := isSimpleModule_hwSpace hν' hPQ hP hnilS
  haveI : Nontrivial (HWSpace Q (μ' + ν'') ν' S) := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ' + ν'')) _
  exact epsI_eq_of_embedding' hν' hPQ hP hε (S.subtype ∘ₗ (hwEquiv hν' hPQ hP hnilS).toLinearMap)
    (Subtype.val_injective.comp (hwEquiv hν' hPQ hP hnilS).injective)

include hν'' hν' hPQ hP hnil hε in
/-- A simple submodule of `Δ_{i^n} M` contains a nonzero vector fixed by `1_{μ',ν''} ⊗ 1`. -/
theorem exists_mem_ne_zero_fixed
    (S : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S] :
    ∃ v ∈ S, v ≠ 0 ∧
      (oneConcat Q μ' ν'' ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q (μ' + ν'') ν') • v = v := by
  have hnilS := fun b => smulNilpotent_submodule S (smulNilpotent_resSub b (hnil _))
  haveI : FiniteDimensional K S :=
    Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  haveI := isSimpleModule_hwSpace hν' hPQ hP hnilS
  haveI : Nontrivial (HWSpace Q (μ' + ν'') ν' S) := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ' + ν'')) _
  have hN := epsI_hwSpace_of_simple hν' hPQ hP hnil hε S
  obtain ⟨j, hj, hjt⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ' + ν'') (i := i)
    (M := HWSpace Q (μ' + ν'') ν' S)
  have hjc : j ∈ concatSet μ' ν'' :=
    (mem_concatSet_iff_hasTail hν'').2 (Seq.hasTail_iff.2 (by omega))
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hj
  have hw1 : (oneConcat Q μ' ν'' : KLRAlgebra K Q (μ' + ν'')) • w = w := by
    rw [← mem_fixSub.1 hw, smul_smul, oneConcat_mul_e hjc]
  refine ⟨((w : S) : ResSub Q (μ' + ν'') ν' M), (w : S).2, ?_, ?_⟩
  · intro h0
    exact hw0 (Subtype.ext (Subtype.ext h0))
  · have := congrArg (fun z : HWSpace Q (μ' + ν'') ν' S =>
      ((z : S) : ResSub Q (μ' + ν'') ν' M)) hw1
    simp only [coe_hw_smul, Submodule.coe_smul] at this
    exact this

section Inst

variable [IsSimpleModule (TensorKLR Q μ' (ν'' + ν'))
    (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))]
  [IsSimpleModule (KLRAlgebra K Q μ')
    (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))]

/-- The vector `Φ(w₀ ⊗ [x^δ]) ∈ Δ_{i^ε} M ⊆ M`, `Φ : K ⊠ L(i^ε) ≅ Δ_{i^ε} M` (Lemma 3.8). -/
def socVec (w₀ : HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) : M :=
  CastMod.val ((hwEquiv (forall_add_of_forall hν'' hν') hPQ hP
    (fun b => smulNilpotent_resSub b (smulNilpotent_mAssoc hnil _))
    (ExtTensor.tmul w₀ (lMk (forall_add_of_forall hν'' hν') Q
      (xDelta (Multiset.card (ν'' + ν'))))) :
    ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) : MAssoc μ' ν'' ν' M)

omit [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  [IsSimpleModule (KLRAlgebra K Q μ')
    (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))] in
theorem socVec_ne_zero
    {w₀ : HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))}
    (hw₀ : w₀ ≠ 0) : socVec hν'' hν' hPQ hP hnil w₀ ≠ 0 := by
  intro h0
  have h1 := Subtype.ext (show ((hwEquiv (forall_add_of_forall hν'' hν') hPQ hP
    (fun b => smulNilpotent_resSub b (smulNilpotent_mAssoc hnil _))
    (ExtTensor.tmul w₀ (lMk (forall_add_of_forall hν'' hν') Q
      (xDelta (Multiset.card (ν'' + ν'))))) :
    ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) : MAssoc μ' ν'' ν' M) =
      ((0 : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) : MAssoc μ' ν'' ν' M) from h0)
  rw [LinearEquiv.map_eq_zero_iff] at h1
  exact extTensor_tmul_ne_zero (A := KLRAlgebra K Q μ') (B := KLRAlgebra K Q (ν'' + ν')) hw₀
    (lMk_xDelta_ne_zero (forall_add_of_forall hν'' hν')) h1

include hPQ hP hnil hε in
/-- **The key step**: every simple submodule `S ⊆ Δ_{i^n} M` contains the vector
`socVec w₀ = Φ(w₀ ⊗ [x^δ])` (it does not depend on `S`). -/
theorem exists_mem_eq_socVec
    (S : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S]
    (w₀ : HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) :
    ∃ v ∈ S, ((v : ResSub Q (μ' + ν'') ν' M) : M) = socVec hν'' hν' hPQ hP hnil w₀ := by
  have hνε := forall_add_of_forall hν'' hν'
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b :
      TensorKLR Q μ' (ν'' + ν')) (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :=
    fun b => smulNilpotent_resSub b (smulNilpotent_mAssoc hnil _)
  let Φ := hwEquiv hνε hPQ hP hnilΔ
  let P : Submodule K (ExtTensor K
      (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) (KLRRep hνε Q)) :=
    { carrier := {y | ∃ v ∈ S, (oneConcat Q μ' ν'' ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q (μ' + ν'') ν') • v = v ∧ ((v : ResSub Q (μ' + ν'') ν' M) : M) =
        CastMod.val ((Φ y : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) : MAssoc μ' ν'' ν' M)}
      zero_mem' := ⟨0, S.zero_mem, smul_zero _, by
        rw [map_zero]; rfl⟩
      add_mem' := by
        rintro y y' ⟨v, hv, hEv, hvy⟩ ⟨v', hv', hEv', hvy'⟩
        refine ⟨v + v', S.add_mem hv hv', by rw [smul_add, hEv, hEv'], ?_⟩
        rw [map_add, Submodule.coe_add, Submodule.coe_add, hvy, hvy']
        rfl
      smul_mem' := by
        rintro c y ⟨v, hv, hEv, hvy⟩
        refine ⟨c • v, S.smul_of_tower_mem c hv, by rw [smul_comm, hEv], ?_⟩
        rw [show Φ (c • y) = c • Φ y from Φ.toLinearMap.map_smul_of_tower c y,
          Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, hvy]
        rfl }
  have hP0 : P ≠ ⊥ := by
    obtain ⟨v₀, hv₀, hv₀0, hEv₀⟩ := exists_mem_ne_zero_fixed hν'' hν' hPQ hP hnil hε S
    have hz : CastMod.of (h := (add_assoc μ' ν'' ν').symm) ((v₀ : ResSub Q (μ' + ν'') ν' M) : M) ∈
        fixSub K (MAssoc μ' ν'' ν' M) (oneConcat Q μ' (ν'' + ν')) := by
      rw [mem_fixSub, oneConcat_smul_mAssoc hν'' hν', ← coe_resSub_smul, hEv₀]
    rw [Submodule.ne_bot_iff]
    refine ⟨Φ.symm ⟨_, hz⟩, ⟨v₀, hv₀, hEv₀, ?_⟩, ?_⟩
    · show _ = CastMod.val ((Φ (Φ.symm ⟨_, hz⟩) : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
        MAssoc μ' ν'' ν' M)
      rw [LinearEquiv.apply_symm_apply]; rfl
    · intro h0
      apply hv₀0
      have h1 := congrArg (fun y => ((Φ y : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
        MAssoc μ' ν'' ν' M)) h0
      simp only [LinearEquiv.apply_symm_apply, map_zero, ZeroMemClass.coe_zero] at h1
      exact Subtype.ext h1
  have ha : ∀ a : KLRAlgebra K Q μ', ∀ y ∈ P,
      (a ⊗ₜ[K] 1 : TensorKLR Q μ' (ν'' + ν')) • y ∈ P := by
    rintro a y ⟨v, hv, hEv, hvy⟩
    refine ⟨(concat Q μ' ν'' (a ⊗ₜ 1) ⊗ₜ[K] 1 : TensorKLR Q (μ' + ν'') ν') • v,
      S.smul_mem _ hv, ?_, ?_⟩
    · rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, oneConcat_mul_concat, mul_one]
    · rw [map_smul, concat_tmul_one_smul_mAssoc hν'' hν', ← hvy, coe_resSub_smul]
  have hx : ∀ b, ∀ y ∈ P,
      ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b : TensorKLR Q μ' (ν'' + ν')) • y ∈ P := by
    rintro b y ⟨v, hv, hEv, hvy⟩
    obtain ⟨t, ht, htc⟩ := exists_tensor_dot (Q := Q) (M := M) (μ := μ' + ν'') (ν' := ν')
      (Fin.cast (congrArg Multiset.card (add_assoc μ' ν'' ν').symm) (Seq.posR μ' b))
    refine ⟨t • v, S.smul_mem t hv, ?_, ?_⟩
    · have hc : Commute t (oneConcat Q μ' ν'' ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q (μ' + ν'') ν') := htc (concatSet μ' ν'')
      rw [smul_smul, ← hc.eq, mul_smul, hEv]
    · rw [map_smul, one_tmul_x_smul_mAssoc, ← hvy, ht]
  have hmem := tmul_xDelta_mem hνε hP0 ha hx w₀
  obtain ⟨v, hv, -, hvy⟩ := hmem
  exact ⟨v, hv, hvy⟩

include hν'' hν' hPQ hP hnil hε in
/-- Proposition 3.10, given the conclusions of Lemma 3.8 for `Δ_{i^ε} M` as instances: any two
simple submodules of `Δ_{i^n} M` coincide. -/
theorem socle_eq_of_inst
    (S₁ S₂ : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S₁]
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S₂] : S₁ = S₂ := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q μ')
    (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))
  obtain ⟨w₀, hw₀⟩ := exists_ne
    (0 : HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))
  obtain ⟨v₁, hv₁, h₁⟩ := exists_mem_eq_socVec hν'' hν' hPQ hP hnil hε S₁ w₀
  obtain ⟨v₂, hv₂, h₂⟩ := exists_mem_eq_socVec hν'' hν' hPQ hP hnil hε S₂ w₀
  have h12 : v₁ = v₂ := Subtype.ext (h₁.trans h₂.symm)
  have hv0 : v₁ ≠ 0 := fun h0 => socVec_ne_zero hν'' hν' hPQ hP hnil hw₀
    (by rw [← h₁, h0]; rfl)
  have hinf : S₁ ⊓ S₂ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v₁, ⟨hv₁, h12 ▸ hv₂⟩, hv0⟩
  have hA₁ := isSimpleModule_iff_isAtom.1 ‹IsSimpleModule _ S₁›
  have hA₂ := isSimpleModule_iff_isAtom.1 ‹IsSimpleModule _ S₂›
  have hle : S₁ ≤ S₂ := by
    rcases hA₁.le_iff.1 (inf_le_left : S₁ ⊓ S₂ ≤ S₁) with h | h
    · exact absurd h hinf
    · rw [← h]; exact inf_le_right
  exact ((hA₂.le_iff.1 hle).resolve_left hA₁.1)

end Inst

include hν'' hν' hPQ hP hnil hε in
/-- **KL I, Proposition 3.10** (ungraded): for `M` irreducible (finite-dimensional, nilpotent
dots) with `ε_i(M) = card ν'' + n`, `n = card ν'`, the socle of `Δ_{i^n} M` is irreducible:
any two simple `R(μ' + ν'') ⊗ R(ν')`-submodules of `Δ_{i^n} M` coincide. -/
theorem socle_resSub_unique
    (S₁ S₂ : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S₁]
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S₂] : S₁ = S₂ := by
  have hνε := forall_add_of_forall hν'' hν'
  haveI := isSimpleModule_castMod (Q := Q) (add_assoc μ' ν'' ν').symm M
  have hε' : epsI Q (μ' + (ν'' + ν')) i (MAssoc μ' ν'' ν' M) = Multiset.card (ν'' + ν') := by
    rw [epsI_castMod, hε, Multiset.card_add]
  obtain ⟨h1, h2, -⟩ := lemma_3_8 hνε hPQ hP (smulNilpotent_mAssoc hnil) hε'
  exact socle_eq_of_inst hν'' hν' hPQ hP hnil hε S₁ S₂

omit [FiniteDimensional K M] in
include hν' hε in
/-- `Δ_{i^n} M ≠ 0` (as `n ≤ ε_i(M)`), so it has a (unique) simple submodule. -/
theorem nontrivial_resSub_of_prop_3_10 : Nontrivial (ResSub Q (μ' + ν'') ν' M) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ((μ' + ν'') + ν')) M
  exact (nontrivial_resSub_iff hν').2 (by omega)

include hν' hPQ hP hnil hε in
/-- **KL I, Proposition 3.10, the form of the socle**: the simple submodule `S` of `Δ_{i^n} M`
is `HW(S) ⊠ L(i^n)` (`hwEquiv`) with `HW(S)` irreducible and `ε_i(HW(S)) = ε_i(M) - n`. -/
theorem socle_resSub_form
    (S : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    [IsSimpleModule (TensorKLR Q (μ' + ν'') ν') S] :
    IsSimpleModule (KLRAlgebra K Q (μ' + ν'')) (HWSpace Q (μ' + ν'') ν' S) ∧
      epsI Q (μ' + ν'') i (HWSpace Q (μ' + ν'') ν' S) + Multiset.card ν' =
        epsI Q ((μ' + ν'') + ν') i M := by
  have hnilS := fun b => smulNilpotent_submodule S (smulNilpotent_resSub b (hnil _))
  haveI : FiniteDimensional K S :=
    Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  refine ⟨isSimpleModule_hwSpace hν' hPQ hP hnilS, ?_⟩
  rw [epsI_hwSpace_of_simple hν' hPQ hP hnil hε S, hε]

end Prop310

/-! ### Proposition 3.10 for `0 ≤ n ≤ ε_i(M)` -/

section General

omit [DecidableEq I] in
/-- A sequence of weight `μ` with a tail of `d` letters `i` forces `d i ≤ μ`. -/
theorem replicate_le_of_hasTail [DecidableEq I] {μ : Multiset I} {i : I} {d : ℕ} {j : Seq μ}
    (hj : Seq.HasTail i j d) : Multiset.replicate d i ≤ μ := by
  rw [← Multiset.le_count_iff_replicate_le]
  have hμ : μ = Finset.univ.val.map j.1 := j.2.symm
  have hd := hj.1
  calc d = (Finset.univ : Finset (Fin d)).card := by simp
    _ ≤ (Finset.univ.filter fun a : Fin (Multiset.card μ) => i = j.1 a).card := by
      refine Finset.card_le_card_of_injOn
        (fun b : Fin d => (⟨Multiset.card μ - d + b.val, by omega⟩ : Fin (Multiset.card μ)))
        (fun b _ => ?_) (fun b _ b' _ hbb => ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hj.2 _ (by simp only; omega)).symm
      · have := congrArg Fin.val hbb
        simp only at this
        exact Fin.ext (by omega)
    _ = Multiset.count i μ := by
      conv_rhs => rw [hμ]
      rw [Multiset.count_map, Finset.card, Finset.filter_val]

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M] [FiniteDimensional K M]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) M)

omit [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M] in
include hν' in
/-- If `n ≤ ε_i(M)` then `μ = μ' + (ε_i(M) - n) i` for some `μ'`. -/
theorem exists_eq_add_replicate [Nontrivial M]
    (hle : Multiset.card ν' ≤ epsI Q (μ + ν') i M) :
    ∃ μ' : Multiset I,
      μ = μ' + Multiset.replicate (epsI Q (μ + ν') i M - Multiset.card ν') i := by
  obtain ⟨s, hs, hst⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ + ν') (i := i) (M := M)
  have hsc : s ∈ concatSet μ ν' :=
    (mem_concatSet_iff_hasTail hν').2 (Seq.hasTail_iff.2 (by omega))
  obtain ⟨j, c, rfl⟩ := mem_concatSet.1 hsc
  have hj : Seq.HasTail i j (epsI Q (μ + ν') i M - Multiset.card ν') := by
    have htail := Seq.hasTail_tailLen (i := i) (j.append c)
    have hc := Multiset.card_add μ ν'
    refine ⟨by have := htail.1; omega, fun a ha => ?_⟩
    have := htail.2 (Seq.posL ν' a) (by simp only [Seq.posL_val]; omega)
    rwa [Seq.append_posL] at this
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.1 (replicate_le_of_hasTail hj)
  exact ⟨u, hu.trans (add_comm _ _)⟩

include hν' hPQ hP hnil in
/-- **KL I, Proposition 3.10** (ungraded): for `M` irreducible (finite-dimensional, nilpotent
dots) and `0 ≤ n ≤ ε_i(M)` (`n = card ν'`), the socle of `Δ_{i^n} M` is irreducible: any two
simple submodules coincide. -/
theorem prop_3_10_socle (hle : Multiset.card ν' ≤ epsI Q (μ + ν') i M)
    (S₁ S₂ : Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' M))
    [IsSimpleModule (TensorKLR Q μ ν') S₁] [IsSimpleModule (TensorKLR Q μ ν') S₂] :
    S₁ = S₂ := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) M
  obtain ⟨μ', hμ'⟩ := exists_eq_add_replicate hν' hle
  set d := epsI Q (μ + ν') i M - Multiset.card ν' with hd
  have hε : epsI Q (μ + ν') i M = Multiset.card (Multiset.replicate d i) + Multiset.card ν' := by
    rw [Multiset.card_replicate]; omega
  clear_value d
  subst hμ'
  exact socle_resSub_unique (ν'' := Multiset.replicate d i)
    (fun a ha => Multiset.eq_of_mem_replicate ha) hν' hPQ hP hnil hε S₁ S₂

end General

end KLRAlgebra

end Categorification.KLR
