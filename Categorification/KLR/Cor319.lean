/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Thm317Graded
import Categorification.KLR.K0Free

/-!
# KL I, Corollary 3.19: simple `R(ν)`-modules have only scalar endomorphisms

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Corollary 3.19** (TeX lines 2270–2273):

> A (graded) irreducible `R(ν)`-module is absolutely irreducible, for any `Γ`, `𝕜` and weight
> `ν`.

The paper deduces this from Proposition 3.18 (the number of simple modules does not depend on
the field). We prove directly the form of the statement that is used later (Proposition 3.20 and
the duality of the bases `[P_b]`, `[S_b]`): **every endomorphism of a simple `R(ν)`-module is a
scalar**, `End_{R(ν)}(S) = 𝕜`. (For a finite-dimensional simple module over a `𝕜`-algebra this is
equivalent to absolute irreducibility, by the Jacobson density theorem; the density theorem is not
formalized here.)

## Proof

Induction on `|ν|`, following the structure of the proof of Theorem 3.17. For `|ν| = 0` a simple
module is one-dimensional. For `|ν| > 0` choose `i` with `ε = ε_i(S) > 0`, so `ν = μ + εi`. By
Lemma 3.8, `N = HW(Δ_{i^ε} S)` (the vectors of `1_{μ, εi} S` killed by the crossings of the last
`ε` strands) is a nonzero simple `R(μ)`-module with nilpotent dots, contained in `S`. An
endomorphism `φ` of `S` commutes with `R(ν)`, hence preserves `N` and restricts to an
`R(μ)`-endomorphism of `N`, which is a scalar `c` by induction. Then `φ - c` kills `N ≠ 0`, so it is
not injective, hence zero by Schur's lemma.

## Main results

* `KLRAlgebra.hwMapOf` : functoriality of `HW(-)` for `R(μ) ⊗ R(ν')`-linear maps.
* `KLRAlgebra.exists_eq_smul_of_isSimpleModule` (**KL I, Corollary 3.19**, ungraded form): for a
  simple finite-dimensional `R(ν)`-module `S` with nilpotent dots (e.g. a graded simple module),
  every `R(ν)`-endomorphism of `S` is a scalar.
* `KLRAlgebra.endZero_eq_bot`, `KLRAlgebra.finrank_endZero_eq_one` : for a graded simple
  `R(ν)`-module, `END(S)_0 = 𝕜`; `GradingDatum.finrank_endZero_top` for the tops `S_b`.
* `GradingDatum.pairing_k0Basis_g0Basis_eq` : **the bases `[P_b]` of `K₀(R(ν))` and `[S_b]` of
  `G₀(R(ν))` are dual**: `([P_b], [S_{b'}]) = δ_{b b'}`.
-/

noncomputable section

namespace Categorification.KLR

open Graded MvPolynomial

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### Functoriality of `HW` -/

section HWMap

variable {μ ν' : Multiset I}
  {S : Type*} [AddCommGroup S] [Module K S] [Module (TensorKLR Q μ ν') S]
  [IsScalarTower K (TensorKLR Q μ ν') S]
  {S' : Type*} [AddCommGroup S'] [Module K S'] [Module (TensorKLR Q μ ν') S']
  [IsScalarTower K (TensorKLR Q μ ν') S']

/-- An `R(μ) ⊗ R(ν')`-linear map restricts to the highest weight spaces. -/
def hwMapOf (f : S →ₗ[TensorKLR Q μ ν'] S') :
    HWSpace Q μ ν' S →ₗ[KLRAlgebra K Q μ] HWSpace Q μ ν' S' where
  toFun v := ⟨f v, fun j => by rw [← map_smul, v.2 j, map_zero]⟩
  map_add' v w := Subtype.ext (map_add f _ _)
  map_smul' a v := Subtype.ext (by
    show f ((a ⊗ₜ[K] 1 : TensorKLR Q μ ν') • (v : S)) = (a ⊗ₜ[K] 1 : TensorKLR Q μ ν') • f v
    rw [map_smul])

@[simp] theorem coe_hwMapOf (f : S →ₗ[TensorKLR Q μ ν'] S') (v : HWSpace Q μ ν' S) :
    ((hwMapOf f v : HWSpace Q μ ν' S') : S') = f v := rfl

end HWMap

/-! ### Corollary 3.19 -/

section Cor319

variable {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

universe u

/-- An endomorphism of a one-dimensional module is a scalar. -/
theorem exists_eq_smul_of_finrank_eq_one {A : Type*} [Ring A] [Algebra K A] {L : Type*}
    [AddCommGroup L] [Module K L] [Module A L] [IsScalarTower K A L]
    (h : Module.finrank K L = 1) (φ : L →ₗ[A] L) : ∃ c : K, ∀ v, φ v = c • v := by
  obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.1 h
  obtain ⟨c, hc⟩ := hspan (φ v₀)
  refine ⟨c, fun v => ?_⟩
  obtain ⟨d, rfl⟩ := hspan v
  rw [φ.map_smul_of_tower, ← hc, smul_comm]

include hPQ hP in
/-- The induction behind Corollary 3.19. -/
theorem end_scalar_aux (n : ℕ) : ∀ (ν : Multiset I), Multiset.card ν = n →
    ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q ν) L]
      [IsScalarTower K (KLRAlgebra K Q ν) L] [FiniteDimensional K L]
      [IsSimpleModule (KLRAlgebra K Q ν) L],
      (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L) →
      ∀ φ : L →ₗ[KLRAlgebra K Q ν] L, ∃ c : K, ∀ v, φ v = c • v := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hν L _ _ _ _ _ _ hnil φ
  haveI : Nontrivial L := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact exists_eq_smul_of_finrank_eq_one (finrank_eq_one_of_card_eq_zero (Q := Q) hν) φ
  obtain ⟨s₀, hs₀⟩ := seqSupp_nonempty (Q := Q) (ν := ν) (M := L)
  -- the last letter `i` of a sequence in the support of `L`
  set i : I := s₀.1 ⟨Multiset.card ν - 1, by omega⟩
  have hi : 1 ≤ epsI Q ν i L := by
    have : Seq.HasTail i s₀ 1 := ⟨by omega, fun a ha => by
      rw [show a = ⟨Multiset.card ν - 1, by omega⟩ from
        Fin.ext (show a.val = Multiset.card ν - 1 by have := a.2; omega)]⟩
    exact (Seq.le_tailLen this).trans (tailLen_le_epsI (mem_seqSupp.1 hs₀))
  set ε := epsI Q ν i L with hεdef
  -- `ν = μ + ε i`
  obtain ⟨s₁, hs₁, hst₁⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := ν) (i := i) (M := L)
  have hrep : Multiset.replicate ε i ≤ ν :=
    replicate_le_of_hasTail (Seq.hasTail_iff.2 (by rw [hst₁]))
  obtain ⟨μ, hμ⟩ := Multiset.le_iff_exists_add.1 hrep
  rw [add_comm] at hμ
  clear_value ε i
  obtain ⟨ν', hν'def⟩ : ∃ ν', Multiset.replicate ε i = ν' := ⟨_, rfl⟩
  rw [hν'def] at hμ
  subst hμ
  have hν' : ∀ a ∈ ν', a = i := fun a ha => Multiset.eq_of_mem_replicate (hν'def ▸ ha)
  have hcard : Multiset.card ν' = ε := by rw [← hν'def, Multiset.card_replicate]
  have hε : epsI Q (μ + ν') i L = Multiset.card ν' := by rw [hcard, hεdef]
  -- `N = HW(Δ_{i^ε} L)`
  set N := HWSpace Q μ ν' (ResSub Q μ ν' L)
  haveI hNs : IsSimpleModule (KLRAlgebra K Q μ) N := (lemma_3_8 hν' hPQ hP hnil hε).2.1
  haveI : Nontrivial N := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) N
  have hNnil : ∀ a : Fin (Multiset.card μ), SmulNilpotent (x a : KLRAlgebra K Q μ) N :=
    fun a => smulNilpotent_hwSpace a (hnil _)
  have hμcard : Multiset.card μ < n := by
    rw [← hν, Multiset.card_add, hcard]; omega
  obtain ⟨c, hc⟩ := ih (Multiset.card μ) hμcard μ rfl N hNnil (hwMapOf (resSubMap φ))
  refine ⟨c, fun v => ?_⟩
  -- `φ - c` kills `N ≠ 0`, hence is zero
  set ψ : L →ₗ[KLRAlgebra K Q (μ + ν')] L := φ - c • LinearMap.id
  obtain ⟨w, hw⟩ := exists_ne (0 : N)
  have hψw : ψ ((w : ResSub Q μ ν' L) : L) = 0 := by
    have h1 : φ ((w : ResSub Q μ ν' L) : L) = c • ((w : ResSub Q μ ν' L) : L) :=
      congrArg (fun z : N => ((z : ResSub Q μ ν' L) : L)) (hc w)
    simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h1, sub_self]
  have hψ : ψ = 0 := by
    rcases LinearMap.bijective_or_eq_zero ψ with hb | h0
    · exfalso
      apply hw
      apply Subtype.ext
      apply Subtype.ext
      exact hb.1 (hψw.trans (map_zero ψ).symm)
    · exact h0
  have := LinearMap.congr_fun hψ v
  simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.zero_apply, sub_eq_zero] at this
  exact this

include hPQ hP in
/-- **KL I, Corollary 3.19** (in the form `End_{R(ν)}(S) = 𝕜`): every endomorphism of a simple
finite-dimensional `R(ν)`-module on which the dots act nilpotently (e.g. a graded simple module)
is a scalar. -/
theorem exists_eq_smul_of_isSimpleModule {ν : Multiset I} {L : Type*} [AddCommGroup L]
    [Module K L] [Module (KLRAlgebra K Q ν) L] [IsScalarTower K (KLRAlgebra K Q ν) L]
    [FiniteDimensional K L] [IsSimpleModule (KLRAlgebra K Q ν) L]
    (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L) (φ : L →ₗ[KLRAlgebra K Q ν] L) :
    ∃ c : K, ∀ v, φ v = c • v :=
  end_scalar_aux hPQ hP _ ν rfl L hnil φ

include hPQ hP in
/-- `End_{R(ν)}(S) = 𝕜` as a subalgebra statement. -/
theorem end_eq_bot {ν : Multiset I} {L : Type*} [AddCommGroup L]
    [Module K L] [Module (KLRAlgebra K Q ν) L] [IsScalarTower K (KLRAlgebra K Q ν) L]
    [FiniteDimensional K L] [IsSimpleModule (KLRAlgebra K Q ν) L]
    (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L) :
    (⊤ : Subalgebra K (Module.End (KLRAlgebra K Q ν) L)) = ⊥ := by
  refine eq_bot_iff.2 fun φ _ => Algebra.mem_bot.2 ?_
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSimpleModule hPQ hP hnil φ
  exact ⟨c, LinearMap.ext fun v => by rw [Module.algebraMap_end_apply, hc]⟩

variable (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)

include hPQ hP hG in
/-- **KL I, Corollary 3.19, graded form**: for a graded simple `R(ν)`-module `S` (dots of positive
degree), the degree-zero endomorphisms are the scalars, `END(S)_0 = 𝕜`. -/
theorem endZero_eq_bot {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module K M]
    [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M]
    (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul (G.grade ν) ℳ]
    (hS : IsGradedSimple (G.grade ν) ℳ) :
    endZero (KLRAlgebra K Q ν) ℳ = ⊥ := by
  obtain ⟨hfd, hsimple, hnil⟩ := crystal_hypotheses_of_isGradedSimple G hG ℳ hPQ hP hS
  refine eq_bot_iff.2 fun φ _ => ?_
  have := end_eq_bot hPQ hP hnil ▸ (Algebra.mem_top : φ ∈ (⊤ : Subalgebra K _))
  exact this

include hPQ hP hG in
/-- `dim_𝕜 END(S)_0 = 1` for a graded simple `R(ν)`-module `S`. -/
theorem finrank_endZero_eq_one {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module K M]
    [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M]
    (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul (G.grade ν) ℳ]
    (hS : IsGradedSimple (G.grade ν) ℳ) :
    Module.finrank K (endZero (KLRAlgebra K Q ν) ℳ) = 1 := by
  obtain ⟨hfd, hsimple, hnil⟩ := crystal_hypotheses_of_isGradedSimple G hG ℳ hPQ hP hS
  haveI : Nontrivial M := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) M
  rw [endZero_eq_bot hPQ hP G hG ℳ hS, Subalgebra.finrank_bot]

end Cor319

end KLRAlgebra

namespace GradingDatum

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)
  (ν : Multiset I)

include hPQ hP hG in
/-- **KL I, Corollary 3.19** for the tops `S_b` of the indecomposable projectives:
`dim_𝕜 END(S_b)_0 = 1`. -/
theorem finrank_endZero_top (b : GProj.IndecClass (G.grade ν)) :
    Module.finrank K (endZero (KLRAlgebra K Q ν) b.top.grading) = 1 :=
  KLRAlgebra.finrank_endZero_eq_one hPQ hP G hG b.top.grading
    (GProj.IndecClass.isGradedSimple_top b)

open scoped Classical in
include hPQ hP hG in
/-- **KL I, §2.5 with Corollary 3.19: the bases `[P_b]` of `K₀(R(ν))` and `[S_b]` of `G₀(R(ν))`
are dual**: `([P_b], [S_{b'}]) = δ_{b b'}`. -/
theorem pairing_k0Basis_g0Basis_eq (b b' : GProj.IndecClass (G.grade ν)) :
    pairing (G.k0Basis hPQ hP hG ν b) (G.g0Basis hPQ hP hG ν b') = if b = b' then 1 else 0 := by
  rw [pairing_k0Basis_g0Basis, G.finrank_endZero_top hPQ hP hG ν b]
  split_ifs <;> rfl

end GradingDatum

end Categorification.KLR
