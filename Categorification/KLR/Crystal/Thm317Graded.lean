/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Thm317
import Categorification.KLR.Crystal.GradedBridge
import Categorification.Algebra.Graded.G0
import Categorification.KLR.K0Free
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Submodule

/-!
# KL I, Theorem 3.17: graded characters of simple modules are linearly independent

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Theorem 3.17** (TeX lines 2240–2255):

> The character map `ch : G₀(R(ν)) → ℤ[q, q⁻¹] Seq(ν)` is injective. Equivalently, the characters
> of irreducible modules (one from each equivalence class up to grading shifts) are linearly
> independent functions on `Seq(ν)`.

The paper remarks that the graded case follows "identically" from Kleshchev's ungraded
argument. We deduce it instead from the ungraded statement (`KLRAlgebra.thm_3_17_ungraded`) by
specialization at `q = 1`:

* graded simple modules which are not isomorphic up to a grading shift are not isomorphic as
  ungraded modules (`IsGradedSimple.exists_gradedEquiv_shift_of_ne_zero`), and graded simple
  modules are finite-dimensional, simple, and have nilpotent dots
  (`crystal_hypotheses_of_isGradedSimple`);
* the graded character `gdim (1_s M) ∈ ℤ[q, q⁻¹]` specializes at `q = 1` to `dim 1_s M`
  (`evalOne_gdimPoly`);
* a family of vectors over `ℤ[q, q⁻¹]` whose specialization at `q = 1` is linearly independent
  over `ℤ` is linearly independent (`linearIndependent_of_evalOne`): a relation has all
  coefficients in `ker(ev₁) = (q - 1)`, hence (dividing by `q - 1`) in every power `(q - 1)^n`,
  hence zero by the Krull intersection theorem (`ℤ[q, q⁻¹]` is a Noetherian domain).

## Main results

* `Categorification.evalOne`, `Categorification.linearIndependent_of_evalOne`.
* `Categorification.Graded.finrank_eq_sum_finrank` : `dim M = ∑_d dim M_d`, and
  `Categorification.Graded.evalOne_gdimPoly` : `gdim M (1) = dim M`.
* `KLRAlgebra.thm_3_17` (**KL I, Theorem 3.17**, second form): for graded simple
  `R(ν)`-modules `S_t` (a grading datum with dots of positive degree), pairwise non-isomorphic up
  to grading shift, the graded characters `s ↦ gdim (1_s S_t) ∈ ℤ[q, q⁻¹]` are linearly
  independent over `ℤ[q, q⁻¹]`.
* `KLRAlgebra.chMap` : the `ℤ[q, q⁻¹]`-linear character map
  `ch : G₀(R(ν)) → (Seq(ν) → ℤ[q, q⁻¹])`, `[M] ↦ (gdim 1_s M)_s`, and `KLRAlgebra.thm_3_17_G0`
  (**KL I, Theorem 3.17**): **`ch` is injective** (the basis `[S_b]` of `G₀(R(ν))`,
  `Graded.G0.topBasis`, is mapped to a linearly independent family).
-/

noncomputable section

namespace Categorification

open LaurentPolynomial Polynomial

/-! ### Specialization at `q = 1` -/

section EvalOne

/-- Evaluation `ℤ[q, q⁻¹] → ℤ` at `q = 1`. -/
abbrev evalOne : LaurentPolynomial ℤ →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) 1

theorem evalOne_T (n : ℤ) : evalOne (T n) = 1 := by
  rw [eval₂_T, one_zpow, Units.val_one]

theorem evalOne_single (n c : ℤ) : evalOne (Finsupp.single n c) = c := by
  rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, LaurentPolynomial.eval₂_C, evalOne_T, mul_one,
    RingHom.id_apply]

theorem evalOne_eq_sum (p : LaurentPolynomial ℤ) : evalOne p = p.sum fun _ c => c := by
  induction p using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.sum_zero_index]
  | add p q hp hq =>
    rw [map_add, hp, hq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  | single n c =>
    rw [evalOne_single, Finsupp.sum_single_index rfl]

theorem T_one_sub_one_ne_zero : (T 1 - 1 : LaurentPolynomial ℤ) ≠ 0 := by
  have : (T 1 - 1 : LaurentPolynomial ℤ) = toLaurent (Polynomial.X - Polynomial.C 1) := by
    rw [map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C, map_one]
  rw [this]
  exact fun h => Polynomial.X_sub_C_ne_zero (1 : ℤ)
    (Polynomial.toLaurent_injective (h.trans (map_zero _).symm))

/-- `ker(ev₁) = (q - 1)`. -/
theorem exists_eq_mul_of_evalOne_eq_zero {p : LaurentPolynomial ℤ} (hp : evalOne p = 0) :
    ∃ p' : LaurentPolynomial ℤ, p = (T 1 - 1) * p' := by
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hroot : f.IsRoot 1 := by
    have := congrArg evalOne hf
    rw [eval₂_toLaurent, map_mul, hp, zero_mul, Units.val_one] at this
    exact this
  have hdiv := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := f)).2 hroot
  refine ⟨toLaurent (f /ₘ (Polynomial.X - Polynomial.C 1)) * T (-(n : ℤ)), ?_⟩
  have hT : (T (n : ℤ) * T (-(n : ℤ)) : LaurentPolynomial ℤ) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  calc p = p * T (n : ℤ) * T (-(n : ℤ)) := by rw [mul_assoc, hT, mul_one]
    _ = toLaurent f * T (-(n : ℤ)) := by rw [hf]
    _ = _ := by
      conv_lhs => rw [← hdiv]
      rw [map_mul, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C, map_one,
        mul_assoc]

instance : IsNoetherianRing (LaurentPolynomial ℤ) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : ℤ[X])) _ inferInstance

/-- **Specialization at `q = 1`**: a family of `ℤ[q, q⁻¹]`-valued functions whose specialization
at `q = 1` is `ℤ`-linearly independent is `ℤ[q, q⁻¹]`-linearly independent. -/
theorem linearIndependent_of_evalOne {ι X : Type*} [Fintype ι]
    (v : ι → X → LaurentPolynomial ℤ)
    (h : LinearIndependent ℤ (fun t s => evalOne (v t s))) :
    LinearIndependent (LaurentPolynomial ℤ) v := by
  classical
  rw [Fintype.linearIndependent_iff] at h ⊢
  set I := RingHom.ker evalOne with hI
  have hI1 : (T 1 - 1 : LaurentPolynomial ℤ) ∈ I := by
    rw [RingHom.mem_ker, map_sub, evalOne_T, map_one, sub_self]
  have key : ∀ (n : ℕ) (g : ι → LaurentPolynomial ℤ), ∑ t, g t • v t = 0 → ∀ t, g t ∈ I ^ n := by
    intro n
    induction n with
    | zero => intro g _ t; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n ih =>
      intro g hg
      have hε : ∀ t, evalOne (g t) = 0 := by
        refine h (fun t => evalOne (g t)) ?_
        funext s
        have := congrFun hg s
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
        rw [← map_zero evalOne, ← this, map_sum]
        simp only [map_mul]
      choose g' hg' using fun t => exists_eq_mul_of_evalOne_eq_zero (hε t)
      have hg'0 : ∑ t, g' t • v t = 0 := by
        funext s
        have := congrFun hg s
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hg',
          mul_assoc] at this ⊢
        rw [← Finset.mul_sum] at this
        exact (mul_eq_zero.1 this).resolve_left T_one_sub_one_ne_zero
      intro t
      rw [hg' t, pow_succ']
      exact Ideal.mul_mem_mul hI1 (ih g' hg'0 t)
  intro g hg t
  have hmem : g t ∈ ⨅ n, I ^ n := Submodule.mem_iInf _ |>.2 fun n => key n g hg t
  rw [Ideal.iInf_pow_eq_bot_of_isDomain I (fun h1 => by
    have : (1 : LaurentPolynomial ℤ) ∈ I := h1 ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this)] at hmem
  exact (Submodule.mem_bot _).1 hmem

end EvalOne

/-! ### Graded dimension at `q = 1` -/

namespace Graded

open DirectSum

section Sum

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **`dim M = ∑_d dim M_d`** for a graded vector space whose nonzero pieces lie in `S`. -/
theorem finrank_eq_sum_finrank (ℳ : ℤ → Submodule K M) [Decomposition ℳ] (S : Finset ℤ)
    (hS : ∀ d ∉ S, ℳ d = ⊥) [∀ d, FiniteDimensional K (ℳ d)] :
    Module.finrank K M = ∑ d ∈ S, Module.finrank K (ℳ d) := by
  classical
  let φ : M →ₗ[K] ((d : S) → ℳ d) :=
    LinearMap.pi fun d => (DirectSum.component K ℤ (fun i => ℳ i) d).comp
      (decomposeLinearEquiv ℳ).toLinearMap
  have hφ : ∀ m (d : S), ((φ m d : ℳ d) : M) = (decompose ℳ m d : M) := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    rw [Submodule.mem_bot, ← sum_support_decompose ℳ m]
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases hd : d ∈ S
    · have := congrArg (fun f => ((f ⟨d, hd⟩ : ℳ d) : M)) hm
      simpa [hφ] using this
    · have hmem := (decompose ℳ m d).2
      generalize ((decompose ℳ m d : ℳ d) : M) = z at hmem ⊢
      rw [hS d hd, Submodule.mem_bot] at hmem
      exact hmem
  have hsurj : Function.Surjective φ := by
    intro f
    refine ⟨∑ d : S, (f d : M), funext fun d => Subtype.ext ?_⟩
    rw [hφ, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum,
      Finset.sum_eq_single d]
    · exact decompose_of_mem_same ℳ (f d).2
    · intro d' _ hd'
      exact decompose_of_mem_ne ℳ (f d').2 (fun h => hd' (Subtype.ext h))
    · intro h; exact absurd (Finset.mem_univ d) h
  rw [(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort S fun d => Module.finrank K (ℳ d)

/-- **`gdim M` at `q = 1` is `dim M`**. -/
theorem evalOne_gdimPoly (ℳ : ℤ → Submodule K M) [Decomposition ℳ] [FiniteDimensional K M] :
    evalOne (gdimPoly ℳ) = Module.finrank K M := by
  rw [evalOne_eq_sum, Finsupp.sum, finrank_eq_sum_finrank ℳ (gdimPoly ℳ).support (fun d hd => ?_),
    Nat.cast_sum]
  · exact Finset.sum_congr rfl fun d _ => gdimPoly_apply ℳ d
  · rw [Finsupp.not_mem_support_iff, gdimPoly_apply, Nat.cast_eq_zero,
      Submodule.finrank_eq_zero] at hd
    exact hd

end Sum

end Graded

/-! ### Theorem 3.17 -/

namespace KLR

namespace KLRAlgebra

open Graded DirectSum

variable {I : Type*} [DecidableEq I] {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)

section GCh

variable {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M] [FiniteDimensional K M]
  (ℳ : ℤ → Submodule K M) [Decomposition ℳ] [SetLike.GradedSMul (G.grade ν) ℳ]

omit [IsScalarTower K (KLRAlgebra K Q ν) M] in
include G in
/-- The graded character `gdim (1_s M)` specializes at `q = 1` to `dim 1_s M`. -/
theorem evalOne_gdimPoly_idem [IsScalarTower K (KLRAlgebra K Q ν) M] (s : Seq ν) :
    evalOne (gdimPoly (idem ℳ (e s : KLRAlgebra K Q ν))) = dimCh Q ν M s := by
  letI := idemDecomposition ℳ (G.e_mem_grade s)
  rw [evalOne_gdimPoly]
  rfl

end GCh

universe u v

include hPQ hP hG in
/-- **KL I, Theorem 3.17** (the character map is injective; equivalently, the characters of
the irreducible modules, one from each class up to grading shift, are linearly independent):
let `(S_t, 𝒮_t)` be graded simple `R(ν)`-modules (for a grading datum with dots of positive
degree), pairwise non-isomorphic up to grading shift. Then the graded characters
`s ↦ gdim (1_s S_t) ∈ ℤ[q, q⁻¹]` are linearly independent over `ℤ[q, q⁻¹]`. -/
theorem thm_3_17 {ν : Multiset I} {T : Type v} (S : T → Type u) [∀ t, AddCommGroup (S t)]
    [∀ t, Module K (S t)] [∀ t, Module (KLRAlgebra K Q ν) (S t)]
    [∀ t, IsScalarTower K (KLRAlgebra K Q ν) (S t)]
    (𝒮 : ∀ t, ℤ → Submodule K (S t)) [∀ t, Decomposition (𝒮 t)]
    [∀ t, SetLike.GradedSMul (G.grade ν) (𝒮 t)] (hS : ∀ t, IsGradedSimple (G.grade ν) (𝒮 t))
    (hL : ∀ t t' (c : ℤ), Nonempty (𝒮 t ≃ᵍ[KLRAlgebra K Q ν] Graded.shift (𝒮 t') c) → t = t') :
    LinearIndependent (LaurentPolynomial ℤ)
      (fun t => fun s : Seq ν => gdimPoly (idem (𝒮 t) (e s : KLRAlgebra K Q ν))) := by
  classical
  have hyp := fun t => crystal_hypotheses_of_isGradedSimple G hG (𝒮 t) hPQ hP (hS t)
  haveI : ∀ t, FiniteDimensional K (S t) := fun t => (hyp t).1
  haveI : ∀ t, IsSimpleModule (KLRAlgebra K Q ν) (S t) := fun t => (hyp t).2.1
  have hL' : ∀ t t', Nonempty (S t ≃ₗ[KLRAlgebra K Q ν] S t') → t = t' := by
    rintro t t' ⟨φ⟩
    haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) (S t)
    have hφ : φ.toLinearMap ≠ 0 := by
      intro h0
      obtain ⟨v, hv⟩ := exists_ne (0 : S t)
      exact hv (φ.injective (by simpa using LinearMap.congr_fun h0 v))
    obtain ⟨c, hc⟩ := (hS t).exists_gradedEquiv_shift_of_ne_zero (hS t') hφ
    exact hL t t' c hc
  have hU := thm_3_17_ungraded hPQ hP S (fun t => (hyp t).2.2) hL'
  rw [linearIndependent_iff_finset_linearIndependent]
  intro F
  apply linearIndependent_of_evalOne
  have heq : (fun (t : F) (s : Seq ν) =>
      evalOne (gdimPoly (idem (𝒮 t.1) (e s : KLRAlgebra K Q ν)))) =
      fun (t : F) (s : Seq ν) => (dimCh Q ν (S t.1) s : ℤ) := by
    funext t s
    exact evalOne_gdimPoly_idem G (𝒮 t.1) s
  show LinearIndependent ℤ (fun (t : F) (s : Seq ν) =>
      evalOne (gdimPoly (idem (𝒮 t.1) (e s : KLRAlgebra K Q ν))))
  rw [heq]
  exact hU.comp (fun t : F => t.1) Subtype.val_injective

/-! ### The character map on `G₀` -/

section G0Char

variable {ν : Multiset I}

omit [DecidableEq I] in
/-- Degree-preserving isomorphisms preserve `gdim (e M)`. -/
theorem gdimPoly_idem_congr {A : Type*} [Ring A] [Algebra K A] {M N : Type*} [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] [AddCommGroup N] [Module K N] [Module A N]
    [IsScalarTower K A N] {ℳ : ℤ → Submodule K M} {𝒩 : ℤ → Submodule K N}
    (f : ℳ ≃ᵍ[A] 𝒩) (a : A) : gdimPoly (idem ℳ a) = gdimPoly (idem 𝒩 a) := by
  have h : (fun d => (Module.finrank K (idem ℳ a d) : ℤ)) =
      fun d => (Module.finrank K (idem 𝒩 a d) : ℤ) := by
    funext d
    let F := f.toLinearEquiv
    let φ : idem ℳ a d ≃ₗ[K] idem 𝒩 a d :=
      { toFun := fun x => ⟨⟨F x.1.1, by
            show a • F x.1.1 = F x.1.1
            rw [← map_smul, mem_idemSubspace.1 x.1.2]⟩, f.map_mem x.2⟩
        invFun := fun y => ⟨⟨F.symm y.1.1, by
            show a • F.symm y.1.1 = F.symm y.1.1
            rw [← map_smul, mem_idemSubspace.1 y.1.2]⟩, f.symm_map_mem' y.2⟩
        map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F _ _))
        map_smul' := fun c x => Subtype.ext (Subtype.ext
          (F.toLinearMap.map_smul_of_tower c _))
        left_inv := fun x => Subtype.ext (Subtype.ext (F.symm_apply_apply _))
        right_inv := fun y => Subtype.ext (Subtype.ext (F.apply_symm_apply _)) }
    rw [φ.finrank_eq]
  unfold gdimPoly
  rw [h]

theorem chG0_hses (s : Seq ν) {M N P : GFin (G.grade ν)} (S : GFin.ShortExact M N P) :
    gdimPoly (idem N.grading (e s : KLRAlgebra K Q ν)) =
      gdimPoly (idem M.grading (e s : KLRAlgebra K Q ν)) +
        gdimPoly (idem P.grading (e s : KLRAlgebra K Q ν)) := by
  letI := idemDecomposition M.grading (G.e_mem_grade s)
  letI := idemDecomposition N.grading (G.e_mem_grade s)
  letI := idemDecomposition P.grading (G.e_mem_grade s)
  haveI := HasGdim.of_finiteDimensional N.grading
  apply toLaurentSeries_injective
  rw [map_add, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly]
  exact gdim_idem_eq_add_of_exact (e_mul_self s) (G.e_mem_grade s) S.preservesGrading_f
    S.preservesGrading_g S.injective S.surjective S.exact

/-- The `s`-component of the character, `[M] ↦ gdim (1_s M)`, on `G₀(R(ν))`. -/
def chG0 (s : Seq ν) : G0 (G.grade ν) →+ LaurentPolynomial ℤ :=
  Categorification.Graded.G0.lift (fun M => gdimPoly (idem M.grading (e s : KLRAlgebra K Q ν)))
    (fun f => gdimPoly_idem_congr f _) (chG0_hses G s)

@[simp] theorem chG0_of (s : Seq ν) (M : GFin (G.grade ν)) :
    chG0 G s (Categorification.Graded.G0.of M) =
      gdimPoly (idem M.grading (e s : KLRAlgebra K Q ν)) :=
  Categorification.Graded.G0.lift_of _ (fun f => gdimPoly_idem_congr f _) (chG0_hses G s) M

theorem chG0_T_smul (s : Seq ν) (a : ℤ) (x : G0 (G.grade ν)) :
    chG0 G s ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) =
      LaurentPolynomial.T a * chG0 G s x := by
  rw [Categorification.Graded.G0.T_smul]
  have : (chG0 G s).comp (Categorification.Graded.G0.shiftHom a) =
      (AddMonoidHom.mulLeft (LaurentPolynomial.T a : LaurentPolynomial ℤ)).comp (chG0 G s) :=
    Categorification.Graded.G0.hom_ext fun M => by
      simp only [AddMonoidHom.comp_apply, Categorification.Graded.G0.shiftHom_of, chG0_of, AddMonoidHom.coe_mulLeft]
      letI := idemDecomposition M.grading (G.e_mem_grade s)
      exact gdimPoly_shift (idem M.grading (e s : KLRAlgebra K Q ν)) a
  exact DFunLike.congr_fun this x

theorem chG0_smul (s : Seq ν) (p : LaurentPolynomial ℤ) (x : G0 (G.grade ν)) :
    chG0 G s (p • x) = p * chG0 G s x := by
  induction p using Finsupp.induction_linear with
  | zero => rw [zero_smul, map_zero, zero_mul]
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_mul]
  | single a c =>
    have h : (Finsupp.single a c : LaurentPolynomial ℤ) = c • LaurentPolynomial.T a := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.smul_eq_C_mul]
    rw [h, smul_assoc, map_zsmul, chG0_T_smul, smul_mul_assoc]

/-- **The character map** `ch : G₀(R(ν)) → ℤ[q, q⁻¹] Seq(ν)`, `[M] ↦ (gdim 1_s M)_s`
(KL I, §3.2; `ℤ[q, q⁻¹]`-linear). -/
def chMap : G0 (G.grade ν) →ₗ[LaurentPolynomial ℤ] (Seq ν → LaurentPolynomial ℤ) where
  toFun x s := chG0 G s x
  map_add' x y := funext fun _ => map_add _ x y
  map_smul' p x := funext fun s => chG0_smul G s p x

include hPQ hP hG in
/-- **KL I, Theorem 3.17**: the character map `ch : G₀(R(ν)) → ℤ[q, q⁻¹] Seq(ν)` is injective
(for `Q` satisfying the hypotheses of the basis theorem and a grading datum with dots of positive
degree). -/
theorem thm_3_17_G0 : Function.Injective (chMap G (ν := ν)) := by
  classical
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  let B := Categorification.Graded.G0.topBasis (G.finiteDimensional_top hPQ hP hG ν)
  have hB : ∀ b, chMap G (B b) =
      fun s => gdimPoly (idem b.top.grading (e s : KLRAlgebra K Q ν)) := by
    intro b
    funext s
    have hb : B b = Categorification.Graded.G0.of
        (GProj.IndecClass.topFin (G.finiteDimensional_top hPQ hP hG ν) b) :=
      Categorification.Graded.G0.topBasis_apply _ b
    show chG0 G s (B b) = _
    rw [hb, chG0_of]
    rfl
  have hL : ∀ (b b' : GProj.IndecClass (G.grade ν)) (c : ℤ),
      Nonempty (b.top.grading ≃ᵍ[KLRAlgebra K Q ν] Graded.shift b'.top.grading c) → b = b' := by
    rintro b b' c ⟨f⟩
    have f' : Graded.shift b.top.grading 0 ≃ᵍ[KLRAlgebra K Q ν]
        Graded.shift b'.top.grading c :=
      (GradedEquiv.ofEq (A := KLRAlgebra K Q ν) (shift_zero b.top.grading)).trans f
    exact (GProj.IndecClass.eq_of_gradedEquiv_top_shift f').1
  have hli : LinearIndependent (LaurentPolynomial ℤ) (fun b => chMap G (B b)) := by
    rw [show (fun b => chMap G (B b)) = fun b s =>
      gdimPoly (idem b.top.grading (e s : KLRAlgebra K Q ν)) from funext hB]
    exact thm_3_17 hPQ hP G hG (T := GProj.IndecClass (G.grade ν)) (fun b => b.top.carrier)
      (fun b => b.top.grading) (fun b => GProj.IndecClass.isGradedSimple_top b) hL
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  have h0 : Finsupp.linearCombination (LaurentPolynomial ℤ) (fun b => chMap G (B b))
      (B.repr x) = 0 := by
    have := Finsupp.apply_linearCombination (LaurentPolynomial ℤ) (chMap G (ν := ν)) B (B.repr x)
    rw [B.linearCombination_repr, hx] at this
    exact this.symm
  have := (linearIndependent_iff.1 hli) _ h0
  rw [← B.linearCombination_repr x, this, map_zero]

end G0Char

end KLRAlgebra

end KLR

end Categorification
