/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.CrystalOps

/-!
# Tops of simple modules and KL I, Lemma 3.13

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Lemma 3.13** (TeX lines 2213–2224; Kleshchev's
book, Lemma 5.2.1): for irreducible `M`,

  `soc Δ_{i^n} M ≅ (ẽ_i^n M) ⊠ L(i^n)`,   `hd Ind (M ⊠ L(i^n)) ≅ f̃_i^n M`.

For a simple module `L` with `ε = ε_i(L)` write `ν = μ' + εi` and call
`top(L) = HW(Δ_{i^ε} L)` (an irreducible `R(μ')`-module with `ε_i = 0`, Lemma 3.8; it is
`ẽ_i^{ε} L`). By `KLRAlgebra.nonempty_equiv_of_hwSpace_equiv` (Lemma 3.7), **a simple module is
determined by `ε_i` and its top**. This file shows that the modules on both sides of Lemma 3.13
have the same `ε_i` and the same top, in the following one-step forms:

* `KLRAlgebra.top_socle_resSub` (**Lemma 3.13 (1), top form**): for the simple socle `S` of
  `Δ_{i^n} M` (`ε_i(M) = ε + n`), `S ≅ HW(S) ⊠ L(i^n)` with `ε_i(HW(S)) = ε` and
  `top(HW(S)) ≅ top(M)`;
* `KLRAlgebra.top_crystalE` : `top(ẽ_i M) ≅ top(M)` (`ε_i(ẽ_i M) = ε_i(M) - 1`);
* `KLRAlgebra.top_crystalF` (**Lemma 3.13 (2), top form**): `top(hd Ind (N ⊠ L(i^n))) ≅ top(N)`
  (and `ε_i(hd Ind (N ⊠ L(i^n))) = ε_i(N) + n`); for `n = 1`, `top(f̃_i N) ≅ top(N)`.

Iterating `top_crystalE` (resp. `top_crystalF` with `n = 1`) shows that `ẽ_i^n M` and
`HW(soc Δ_{i^n} M)` (resp. `f̃_i^n N` and `hd Ind (N ⊠ L(i^n))`) have the same `ε_i` and the same
top, hence are isomorphic; the iterated statements themselves require transporting modules along
the reassociations `R((μ + i) + i) ≅ R(μ + (i + i))` (`CastMod`), which is not carried out here.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

theorem smulNilpotent_hwSpace_of {μ ν' : Multiset I} {S : Type*} [AddCommGroup S] [Module K S]
    [Module (TensorKLR Q μ ν') S] [IsScalarTower K (TensorKLR Q μ ν') S]
    {a : KLRAlgebra K Q μ} (h : SmulNilpotent (a ⊗ₜ[K] (1 : KLRAlgebra K Q ν') :
      TensorKLR Q μ ν') S) : SmulNilpotent a (HWSpace Q μ ν' S) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun w => Subtype.ext ?_⟩
  have key : ∀ (r : ℕ) (w : HWSpace Q μ ν' S), ((a ^ r • w : HWSpace Q μ ν' S) : S) =
      (a ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q μ ν') ^ r • (w : S) := by
    intro r
    induction r with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ r ih =>
      intro w
      rw [pow_succ, mul_smul, ih, coe_hw_smul, ← mul_smul, ← pow_succ]
  rw [key, hm, ZeroMemClass.coe_zero]

section Tops

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) M] [FiniteDimensional K M]
  [IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ((μ' + ν'') + ν')) M)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ' + ν'')) N]
  [IsScalarTower K (KLRAlgebra K Q (μ' + ν'')) N] [FiniteDimensional K N]
  [IsSimpleModule (KLRAlgebra K Q (μ' + ν'')) N]
  (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ' + ν'')) N)

include hν'' hν' hPQ hP hnil hnilN in
/-- **KL I, Lemma 3.13 (1), top form**: let `ε_i(M) = ε + n` (`ε = card ν''`, `n = card ν'`) and
let `S` be the (unique, Proposition 3.10) simple submodule of `Δ_{i^n} M`, `S ≅ N ⊠ L(i^n)` (e.g.
`N = HW(S)`, `socle_resSub_form`). Then `ε_i(N) = ε` and `top(N) ≅ top(M)`, i.e.
`HW(Δ_{i^ε} N) ≅ HW(Δ_{i^{ε+n}} M)`. -/
theorem top_of_socle
    (hε : epsI Q ((μ' + ν'') + ν') i M = Multiset.card ν'' + Multiset.card ν')
    (S : Submodule (TensorKLR Q (μ' + ν'') ν') (ResSub Q (μ' + ν'') ν' M))
    (φ : ExtTensor K N (KLRRep hν' Q) ≃ₗ[TensorKLR Q (μ' + ν'') ν'] S) :
    epsI Q (μ' + ν'') i N = Multiset.card ν'' ∧
      Nonempty (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N) ≃ₗ[KLRAlgebra K Q μ']
        HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ' + ν'')) N
  let f := S.subtype ∘ₗ φ.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hεN : epsI Q (μ' + ν'') i N = Multiset.card ν'' := by
    have := lemma_3_6 hν' hPQ hP f hf
    omega
  exact ⟨hεN, nonempty_hwSpace_equiv_of_embedding hν'' hν' hPQ hP f hnil hε hnilN hεN hf⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν'' hν' hPQ hP hnilN in
/-- **KL I, Lemma 3.13 (2), top form**: for `N` irreducible with `ε_i(N) = ε = card ν''`, the head
`L = hd Ind (N ⊠ L(i^n))` (`CrystalF`; `f̃_i N` for `n = 1`) has `ε_i(L) = ε + n`
(`epsI_crystalF`) and `top(L) ≅ top(N)`: `HW(Δ_{i^ε} N) ≅ HW(Δ_{i^{ε+n}} L)`. -/
theorem top_crystalF (hεN : epsI Q (μ' + ν'') i N = Multiset.card ν'') :
    Nonempty (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N) ≃ₗ[KLRAlgebra K Q μ']
      HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν')
        (MAssoc μ' ν'' ν' (CrystalF Q (μ' + ν'') hν' N)))) := by
  haveI := isSimpleModule_crystalF hν' hPQ hP hnilN
  haveI := instFiniteDimensionalCrystalF hν' hPQ hP (μ := μ' + ν'') (N := N)
  haveI := isSimpleModule_extTensor hν' (Q := Q) (μ := μ' + ν'') (V := N)
  have hnilF := smulNilpotent_crystalF hν' hPQ hP hnilN
  have hεF : epsI Q ((μ' + ν'') + ν') i (CrystalF Q (μ' + ν'') hν' N) =
      Multiset.card ν'' + Multiset.card ν' := by
    rw [epsI_crystalF hν' hPQ hP hnilN, hεN]
  have hc := (isCoatom_crystalFRad hν' hPQ hP hnilN).1
  let f : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q (μ' + ν'') ν']
      ResSub Q (μ' + ν'') ν' (CrystalF Q (μ' + ν'') hν' N) :=
    indAdjFwd (crystalFRad Q (μ' + ν'') hν' N).mkQ
  have hf0 : f ≠ 0 := by
    intro h0
    apply hc.1
    refine eq_top_of_tmul_oneConcat_mem fun y => ?_
    have h2 := congrArg Subtype.val (LinearMap.congr_fun h0 y)
    rw [coe_indAdjFwd_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right fun h =>
      hf0 (LinearMap.ker_eq_top.1 h)
  exact nonempty_hwSpace_equiv_of_embedding hν'' hν' hPQ hP f hnilF hεF hnilN hεN hf

end Tops

section TopE

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ + ν')) N]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) N] [FiniteDimensional K N]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) N]
  (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) N)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν' hν'1 hPQ hP hnilN in
/-- For `ε_i(N) > 0`, `ẽ_i N ⊠ L(i) ↪ Δ_i N`: the socle of `Δ_i N` is `ẽ_i N ⊠ L(i)`. -/
theorem exists_injective_crystalE_extTensor (hpos : 0 < epsI Q (μ + ν') i N) :
    ∃ f : ExtTensor K (CrystalE Q μ ν' N) (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' N,
      Function.Injective f := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) N
  haveI : Nontrivial (ResSub Q μ ν' N) := (nontrivial_resSub_iff hν').2 (by rw [hν'1]; exact hpos)
  haveI : IsArtinian (TensorKLR Q μ ν') (ResSub Q μ ν' N) := isArtinian_of_tower K inferInstance
  haveI : IsAtomic (Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' N)) :=
    isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨S₀, hS₀, -⟩ := (eq_bot_or_exists_atom_le
    (⊤ : Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' N))).resolve_left top_ne_bot
  haveI : IsSimpleModule (TensorKLR Q μ ν') S₀ := isSimpleModule_iff_isAtom.2 hS₀
  haveI : FiniteDimensional K S₀ := finiteDimensional_submodule' S₀
  have hnilS₀ := fun b => smulNilpotent_submodule S₀ (smulNilpotent_resSub (μ := μ) b (hnilN _))
  have hHW : IsSimpleModule (KLRAlgebra K Q μ) (HWSpace Q μ ν' S₀) :=
    isSimpleModule_hwSpace hν' hPQ hP (S := S₀) hnilS₀
  let Φ := hwEquiv hν' hPQ hP hnilS₀
  let θ : HWSpace Q μ ν' S₀ →ₗ[KLRAlgebra K Q μ] ResLeft Q μ ν' N :=
    { toFun := fun w => ResLeft.ofRes ((w : S₀) : ResSub Q μ ν' N)
      map_add' := fun w w' => rfl
      map_smul' := fun a w => rfl }
  have hθ : Function.Injective θ := fun w w' h =>
    Subtype.ext (Subtype.ext (resLeft_toRes_injective h))
  let e₁ := LinearEquiv.ofInjective θ hθ
  haveI : IsSimpleModule (KLRAlgebra K Q μ) (LinearMap.range θ) :=
    @IsSimpleModule.congr _ _ _ _ _ _ _ _ e₁.symm hHW
  have hat : IsAtom (LinearMap.range θ) := isSimpleModule_iff_isAtom.1 inferInstance
  have heq := crystalESub_eq_of_isAtom hν' hν'1 hPQ hP hnilN hat
  let ρ : HWSpace Q μ ν' S₀ ≃ₗ[KLRAlgebra K Q μ] CrystalE Q μ ν' N :=
    e₁.trans (LinearEquiv.ofEq _ _ heq.symm)
  let g : ExtTensor K (CrystalE Q μ ν' N) (KLRRep hν' Q) ≃ₗ[TensorKLR Q μ ν']
      ExtTensor K (HWSpace Q μ ν' S₀) (KLRRep hν' Q) :=
    ExtTensor.congr ρ.symm (LinearEquiv.refl _ _)
  refine ⟨S₀.subtype ∘ₗ (Φ.toLinearMap ∘ₗ g.toLinearMap), fun y y' h => ?_⟩
  have h1 : ((Φ (g y) : S₀) : ResSub Q μ ν' N) = ((Φ (g y') : S₀) : ResSub Q μ ν' N) := h
  exact g.injective (Φ.injective (Subtype.ext h1))

end TopE

section TopE'

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) M] [FiniteDimensional K M]
  [IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ((μ' + ν'') + ν')) M)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν'' hν' hν'1 hPQ hP hnil in
/-- **`ẽ_i` preserves tops**: for `M` irreducible with `ε_i(M) = ε + 1` (`ε = card ν''`),
`ε_i(ẽ_i M) = ε` and `top(ẽ_i M) ≅ top(M)`: `HW(Δ_{i^ε} ẽ_i M) ≅ HW(Δ_{i^{ε+1}} M)`. Iterating,
`top(ẽ_i^n M) ≅ top(M)` (Lemma 3.13 (1) combined with `top_of_socle`). -/
theorem top_crystalE
    (hε : epsI Q ((μ' + ν'') + ν') i M = Multiset.card ν'' + Multiset.card ν') :
    epsI Q (μ' + ν'') i (CrystalE Q (μ' + ν'') ν' M) = Multiset.card ν'' ∧
      Nonempty (HWSpace Q μ' ν'' (ResSub Q μ' ν'' (CrystalE Q (μ' + ν'') ν' M)) ≃ₗ[KLRAlgebra K Q μ']
        HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) := by
  have hpos : 0 < epsI Q ((μ' + ν'') + ν') i M := by rw [hε, hν'1]; omega
  haveI := isSimpleModule_crystalE hν' hν'1 hPQ hP hnil hpos
  haveI : FiniteDimensional K (CrystalE Q (μ' + ν'') ν' M) := finiteDimensional_submodule' _
  have hnilE := smulNilpotent_crystalE hnil
  have hεE : epsI Q (μ' + ν'') i (CrystalE Q (μ' + ν'') ν' M) = Multiset.card ν'' := by
    have := epsI_crystalE hν' hν'1 hPQ hP hnil hpos
    rw [hε, hν'1] at this
    omega
  obtain ⟨f, hf⟩ := exists_injective_crystalE_extTensor hν' hν'1 hPQ hP hnil hpos
  exact ⟨hεE, nonempty_hwSpace_equiv_of_embedding hν'' hν' hPQ hP f hnil hε hnilE hεE hf⟩

end TopE'

end KLRAlgebra

end Categorification.KLR
