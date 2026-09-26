/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop320
import Categorification.KLR.KL2.K0Free2

/-!
# KL II: Corollary 3.19 and Proposition 3.18 of KL I for an arbitrary Cartan datum

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, paragraph "Grothendieck group as the quantum group" (TeX, before
Theorem 8): "the proof of [KL I, Theorem 1.1] carries over to an arbitrary Cartan datum". The
steps of that proof are KL I (arXiv:0803.4121v2) §3.2, **Proposition 3.18** (`γ_{ℚ(q)}` is an
isomorphism) and **Corollary 3.19** (simple modules are absolutely irreducible).

## General lemmas

The KL I files state these results for the rings of a graph. Their proofs only use the basis
theorem hypotheses (`Q_ab(u, v) = P_ba(u, v) P_ab(v, u)` with `P_ab ≠ 0`) and dots of positive
degree, so we first record the relevant consequences once for any such `GradingDatum`:

* `GradingDatum.pairing_g0Basis_eq_invert` : `(z, [S_c]) = \overline{z_c}` for `z = ∑_c z_c [P_c]`
  (duality of the bases `[P_b]`, `[S_b]`, i.e. KL I §2.5 with Corollary 3.19).
* `GradingDatum.chG0_g0Basis_eq` : `ch(S_c)_j = \overline{a_{jc}}` where `[P_j] = ∑_c a_{jc} [P_c]`.
* `GradingDatum.linearIndependent_chMap_g0Basis` : the characters of the simples are linearly
  independent (KL I, Theorem 3.17).
* `GradingDatum.exists_rowComb_projP` : **the key step of KL I, Proposition 3.18**: each `[P_b]` is
  a `ℚ(v)`-linear combination of the `[P_j]`, `j ∈ Seq(ν)` (coordinates specialised along
  `q ↦ v⁻¹`).

## KL II

For a Cartan datum `C` (`deg x_{a,i} = i_a · i_a`) and a field `k`:

* `KL2Gamma.exists_eq_smul_of_isSimpleModule2`, `KL2Gamma.finrank_endZero_top2` : **KL I,
  Corollary 3.19 for KL II**: every endomorphism of a simple `R(ν)`-module (finite-dimensional,
  nilpotent dots) is a scalar; `dim END(S_b)_0 = 1`. The KL I proof
  (`KLRAlgebra.exists_eq_smul_of_isSimpleModule`) is already stated for any `Q` satisfying the
  basis theorem hypotheses; here it is instantiated at `klQ2`.
* `KL2Gamma.K0Q2grade_le_map_gammaQ2` : `K₀(R(ν))_{ℚ(q)} ⊆ γ_{ℚ(q)}('f_ν)` (unconditionally).
* `KL2Gamma.gammaF2_surjective`, `KL2Gamma.gammaF2_bijective`, `KL2Gamma.gammaF2Equiv` : **KL I,
  Proposition 3.18 for KL II**: `γ_{ℚ(q)} : f ≅ K₀(R)_{ℚ(q)}` as `ℚ(q)`-algebras, under the
  Gabber–Kac hypothesis `hGK : C.GabberKac vQ C.c` used to define `f` (injectivity is
  `KL2Gamma.gammaF2_injective`).
-/

noncomputable section

namespace Categorification.KLR

open Graded LaurentPolynomial QuantumGroup KLRAlgebra KLGamma

variable {I : Type*} [DecidableEq I]

/-! ### General lemmas for grading data satisfying the basis theorem -/

namespace GradingDatum

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)

include hPQ hP hG

/-- Finitely many indecomposable projectives (KL I §2.5), as an instance-friendly statement. -/
theorem finite_indecClass (ν : Multiset I) : Finite (GProj.IndecClass (G.grade ν)) :=
  (G.finite_and_card_indecClass_le hPQ hP hG ν).1

/-- **Duality of `[P_b]` and `[S_b]`** (KL I §2.5 and Corollary 3.19): `(z, [S_c]) = \overline{z_c}`
where `z = ∑_c z_c [P_c]`. -/
theorem pairing_g0Basis_eq_invert {ν : Multiset I} (z : K0 (G.grade ν))
    (c : GProj.IndecClass (G.grade ν)) :
    pairing z (G.g0Basis hPQ hP hG ν c) =
      toLaurentSeries (invert ((G.k0Basis hPQ hP hG ν).repr z c)) := by
  classical
  haveI := G.finite_indecClass hPQ hP hG ν
  haveI := Fintype.ofFinite (GProj.IndecClass (G.grade ν))
  conv_lhs => rw [← (G.k0Basis hPQ hP hG ν).sum_repr z]
  rw [map_sum, AddMonoidHom.finset_sum_apply]
  have hterm : ∀ b', pairing ((G.k0Basis hPQ hP hG ν).repr z b' • G.k0Basis hPQ hP hG ν b')
      (G.g0Basis hPQ hP hG ν c) = toLaurentSeries (invert ((G.k0Basis hPQ hP hG ν).repr z b') *
        LaurentPolynomial.C (if b' = c then 1 else 0)) := fun b' => by
    refine pairing_smul_left_of_eq ?_ _
    rw [G.pairing_k0Basis_g0Basis_eq hPQ hP hG, toLaurentSeries_C]
    split_ifs <;> simp [HahnSeries.single_zero_one]
  simp only [hterm]
  rw [Finset.sum_eq_single c (fun b' _ hb' => by rw [if_neg hb', map_zero, mul_zero, map_zero])
    (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, map_one, mul_one]

/-- **The characters of the simples in terms of the coordinates of the `[P_j]`**:
`ch(S_c)_j = \overline{a_{jc}}` where `[P_j] = ∑_c a_{jc} [P_c]` (KL I, proof of
Proposition 3.18, with Corollary 3.19). -/
theorem chG0_g0Basis_eq {ν : Multiset I} (j : Seq ν) (c : GProj.IndecClass (G.grade ν)) :
    chG0 G j (G.g0Basis hPQ hP hG ν c) =
      invert ((G.k0Basis hPQ hP hG ν).repr (K0.of (G.projP j)) c) := by
  apply toLaurentSeries_injective
  rw [← GradingDatum.pairing_projP, pairing_g0Basis_eq_invert]

theorem chG0_g0Basis_eq_gdimPoly {ν : Multiset I} (j : Seq ν)
    (c : GProj.IndecClass (G.grade ν)) :
    chG0 G j (G.g0Basis hPQ hP hG ν c) =
      gdimPoly (idem c.top.grading (e j : KLRAlgebra K Q ν)) := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  rw [GradingDatum.g0Basis, G0.topBasis_apply, chG0_of]
  rfl

/-- **KL I, Theorem 3.17 in the form used for Proposition 3.18**: the characters of the simples
`[S_b]` are linearly independent over `ℤ[q, q⁻¹]`. -/
theorem linearIndependent_chMap_g0Basis (ν : Multiset I) :
    LinearIndependent (LaurentPolynomial ℤ) (fun b => chMap G (G.g0Basis hPQ hP hG ν b)) :=
  (G.g0Basis hPQ hP hG ν).linearIndependent.map' _
    (LinearMap.ker_eq_bot.2 (thm_3_17_G0 hPQ hP G hG))

open scoped Classical in
/-- **The key step of KL I, Proposition 3.18** ("dualizing `ch`"), for any grading datum
satisfying the basis theorem with dots of positive degree: writing `[P_j] = ∑_b a_{jb} [P_b]`, for
every `b` there are `c_j ∈ ℚ(v)` with `∑_j c_j a_{jb'}(v⁻¹) = δ_{b b'}`. -/
theorem exists_rowComb_projP {ν : Multiset I} (b : GProj.IndecClass (G.grade ν)) :
    ∃ c : Seq ν → RatFunc ℚ, ∀ b',
      ∑ j, c j * qToV ((G.k0Basis hPQ hP hG ν).repr (K0.of (G.projP j)) b') =
        if b' = b then 1 else 0 := by
  classical
  haveI := G.finite_indecClass hPQ hP hG ν
  haveI := Fintype.ofFinite (GProj.IndecClass (G.grade ν))
  have hK := linearIndependent_laurentEval _ (G.linearIndependent_chMap_g0Basis hPQ hP hG ν)
  have hK' : LinearIndependent (RatFunc ℚ)
      (fun b j => qToV ((G.k0Basis hPQ hP hG ν).repr (K0.of (G.projP j)) b)) := by
    convert hK using 1
    funext b' j
    show _ = laurentEval vQ (chG0 G j (G.g0Basis hPQ hP hG ν b'))
    rw [chG0_g0Basis_eq, laurentEval_vQ_invert]
  exact exists_rowComb_eq_single
    (fun j b => qToV ((G.k0Basis hPQ hP hG ν).repr (K0.of (G.projP j)) b)) hK' b

end GradingDatum

/-! ### KL II: Corollary 3.19 -/

namespace KL2Gamma

variable (k : Type*) [Field k] (C : CartanDatum I)

local notation "G2" => klGradingDatum2 k C

/-- The basis `[P_b]` of `K₀(R(ν))` for the rings of KL II. -/
abbrev k0B2 (ν : Multiset I) :=
  (G2).k0Basis (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C) ν

/-- The basis `[S_b]` of `G₀(R(ν))` for the rings of KL II. -/
abbrev g0B2 (ν : Multiset I) :=
  (G2).g0Basis (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C) ν

theorem finite_indecClass2 (ν : Multiset I) : Finite (GProj.IndecClass ((G2).grade ν)) :=
  (G2).finite_indecClass (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C) ν

variable {k C} in
/-- **KL I, Corollary 3.19, for KL II** (in the form `End_{R(ν)}(S) = 𝕜`): for an arbitrary Cartan
datum, every endomorphism of a simple finite-dimensional `R(ν)`-module on which the dots act
nilpotently (e.g. a graded simple module) is a scalar. -/
theorem exists_eq_smul_of_isSimpleModule2 {ν : Multiset I} {L : Type*} [AddCommGroup L]
    [Module k L] [Module (R2 k C ν) L] [IsScalarTower k (R2 k C ν) L]
    [FiniteDimensional k L] [IsSimpleModule (R2 k C ν) L]
    (hnil : ∀ a, SmulNilpotent (x a : R2 k C ν) L) (φ : L →ₗ[R2 k C ν] L) :
    ∃ c : k, ∀ v, φ v = c • v :=
  KLRAlgebra.exists_eq_smul_of_isSimpleModule
    (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) hnil φ

variable {k C} in
/-- **KL I, Corollary 3.19, graded form, for KL II**: for a graded simple `R(ν)`-module `S`,
`END(S)_0 = 𝕜`. -/
theorem endZero_eq_bot2 {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module k M]
    [Module (R2 k C ν) M] [IsScalarTower k (R2 k C ν) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul ((G2).grade ν) ℳ]
    (hS : IsGradedSimple ((G2).grade ν) ℳ) :
    endZero (R2 k C ν) ℳ = ⊥ :=
  KLRAlgebra.endZero_eq_bot (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (G2) (klGradingDatum2_degX_pos k C) ℳ hS

/-- **KL I, Corollary 3.19, for KL II**, for the tops `S_b` of the indecomposable projectives:
`dim_𝕜 END(S_b)_0 = 1`. -/
theorem finrank_endZero_top2 {ν : Multiset I} (b : GProj.IndecClass ((G2).grade ν)) :
    Module.finrank k (endZero (R2 k C ν) b.top.grading) = 1 :=
  (G2).finrank_endZero_top (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C) ν b

/-- `(z, [S_c]) = \overline{z_c}` for the rings of KL II. -/
theorem pairing_g0B2 {ν : Multiset I} (z : K0 ((G2).grade ν))
    (c : GProj.IndecClass ((G2).grade ν)) :
    pairing z (g0B2 k C ν c) = toLaurentSeries (invert ((k0B2 k C ν).repr z c)) :=
  (G2).pairing_g0Basis_eq_invert _ _ _ z c

/-! ### KL II: Proposition 3.18 -/

/-- **The key step of KL I, Proposition 3.18, for KL II**: each basis vector `[P_b]` of
`K₀(R(ν))` is a `ℚ(v)`-linear combination of the classes `[P_j]`, `j ∈ Seq(ν)`, in
`K₀(R)_{ℚ(v)}`. -/
theorem exists_toK0Q2_k0B2_eq_sum {ν : Multiset I} (b : GProj.IndecClass ((G2).grade ν)) :
    ∃ c : Seq ν → RatFunc ℚ, toK0Q2 k C (DirectSum.of (G2).K0fam ν (k0B2 k C ν b)) =
      ∑ j, c j • toK0Q2 k C (DirectSum.of (G2).K0fam ν (K0.of ((G2).projP j))) := by
  classical
  haveI := finite_indecClass2 k C ν
  haveI := Fintype.ofFinite (GProj.IndecClass ((G2).grade ν))
  obtain ⟨c, hc⟩ := (G2).exists_rowComb_projP
    (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C) b
  refine ⟨c, ?_⟩
  have hPj : ∀ j, toK0Q2 k C (DirectSum.of (G2).K0fam ν (K0.of ((G2).projP j))) =
      ∑ b', qToV ((k0B2 k C ν).repr (K0.of ((G2).projP j)) b') •
        toK0Q2 k C (DirectSum.of (G2).K0fam ν (k0B2 k C ν b')) := fun j => by
    conv_lhs => rw [← (k0B2 k C ν).sum_repr (K0.of ((G2).projP j))]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [K0R_of_smul2, toK0Q2_smul]
  simp only [hPj, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- `[P_j] = γ_{ℚ(q)}(θ_{j_1} ⋯ θ_{j_m})` (KL II). -/
theorem toK0Q2_projP_eq_gammaQ2 {ν : Multiset I} (j : Seq ν) :
    toK0Q2 k C (DirectSum.of (G2).K0fam ν (K0.of ((G2).projP j))) =
      gammaQ2 k C (PreF.word (FreeMonoid.ofList (List.ofFn j.1))) := by
  rw [gammaQ2_word, FreeMonoid.toList_ofList,
    clsSeq2_eq k C _ ((Fin.univ_val_map _).symm.trans j.2), seq_ofList_ofFn]
  rfl

/-- The weight-`ν` part of `K₀(R)_{ℚ(v)}` (KL II): the `ℚ(v)`-span of the image of `K₀(R(ν))`. -/
def K0Q2grade (ν : Multiset I) : Submodule (RatFunc ℚ) (K0Q2 k C) :=
  Submodule.span (RatFunc ℚ) (toK0Q2 k C '' Set.range (DirectSum.of (G2).K0fam ν))

/-- `K₀(R)_{ℚ(v)}` is spanned over `ℚ(v)` by the image of `K₀(R)` (KL II). -/
theorem toK0Q2_span_eq_top :
    Submodule.span (RatFunc ℚ) (Set.range (toK0Q2 k C)) = ⊤ := by
  letI := qToVAlgebra
  refine eq_top_iff.2 fun z _ => ?_
  refine TensorProduct.induction_on (motive := fun z : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (G2).K0R => (z : K0Q2 k C) ∈ Submodule.span (RatFunc ℚ) (Set.range (toK0Q2 k C)))
    z ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro a x
    have : (a ⊗ₜ[LaurentPolynomial ℤ] x : TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ)
        (G2).K0R) = (a • toK0Q2 k C x : K0Q2 k C) := by
      change _ = a • (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change (a ⊗ₜ[LaurentPolynomial ℤ] x : K0Q2 k C) ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

/-- **KL I, Proposition 3.18, weight by weight, for KL II** (unconditionally, on `'f`): every
element of `K₀(R(ν))_{ℚ(q)}` is `γ_{ℚ(q)}(x)` for some `x ∈ 'f_ν`. -/
theorem K0Q2grade_le_map_gammaQ2 (ν : Multiset I) :
    K0Q2grade k C ν ≤ (PreF.grade (RatFunc ℚ) ν).map (gammaQ2 k C).toLinearMap := by
  classical
  haveI := finite_indecClass2 k C ν
  haveI := Fintype.ofFinite (GProj.IndecClass ((G2).grade ν))
  have hP : ∀ j : Seq ν, toK0Q2 k C (DirectSum.of (G2).K0fam ν (K0.of ((G2).projP j))) ∈
      (PreF.grade (RatFunc ℚ) ν).map (gammaQ2 k C).toLinearMap := fun j =>
    ⟨_, word_ofFn_mem_grade j, (toK0Q2_projP_eq_gammaQ2 k C j).symm⟩
  have hb : ∀ b, toK0Q2 k C (DirectSum.of (G2).K0fam ν (k0B2 k C ν b)) ∈
      (PreF.grade (RatFunc ℚ) ν).map (gammaQ2 k C).toLinearMap := fun b => by
    obtain ⟨c, hc⟩ := exists_toK0Q2_k0B2_eq_sum k C b
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hP j)
  rw [K0Q2grade, Submodule.span_le]
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  rw [← (k0B2 k C ν).sum_repr z, map_sum, map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [K0R_of_smul2, toK0Q2_smul]
  exact Submodule.smul_mem _ _ (hb b)

/-- **KL I, Proposition 3.18, for KL II** (surjectivity): `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is
surjective, for an arbitrary Cartan datum. -/
theorem gammaF2_surjective (hGK : C.GabberKac vQ C.c) :
    Function.Surjective (gammaF2 k C hGK) := by
  have hle : ∀ ν, K0Q2grade k C ν ≤ LinearMap.range (gammaF2 k C hGK).toLinearMap := fun ν => by
    refine (K0Q2grade_le_map_gammaQ2 k C ν).trans ?_
    rintro _ ⟨x, -, rfl⟩
    exact ⟨PreF.π C.dot vQ C.c x, gammaF2_π k C hGK x⟩
  have htop : LinearMap.range (gammaF2 k C hGK).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← toK0Q2_span_eq_top k C, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    induction z using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of ν x => exact hle ν (Submodule.subset_span ⟨_, ⟨x, rfl⟩, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  exact LinearMap.range_eq_top.1 htop

/-- **KL I, Proposition 3.18, for KL II**: `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is bijective (with the
injectivity `gammaF2_injective`), under the Gabber–Kac hypothesis used to define it on `f`. -/
theorem gammaF2_bijective (hGK : C.GabberKac vQ C.c) :
    Function.Bijective (gammaF2 k C hGK) :=
  ⟨gammaF2_injective k C hGK, gammaF2_surjective k C hGK⟩

/-- **KL I, Proposition 3.18, for KL II**: the isomorphism of `ℚ(q)`-algebras
`γ_{ℚ(q)} : f ≅ K₀(R)_{ℚ(q)}` for an arbitrary Cartan datum (under the Gabber–Kac hypothesis). -/
def gammaF2Equiv (hGK : C.GabberKac vQ C.c) : C.F ≃ₐ[RatFunc ℚ] K0Q2 k C :=
  AlgEquiv.ofBijective (gammaF2 k C hGK) (gammaF2_bijective k C hGK)

@[simp] theorem gammaF2Equiv_apply (hGK : C.GabberKac vQ C.c) (x : C.F) :
    gammaF2Equiv k C hGK x = gammaF2 k C hGK x := rfl

end KL2Gamma

end Categorification.KLR
