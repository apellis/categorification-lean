/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Thm317Graded
import Categorification.KLR.Prop34

/-!
# KL I, Proposition 3.18: `γ_{ℚ(q)}` is an isomorphism

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §3.2, **Proposition 3.18** (TeX lines 2257–2268):

> Passing to the fraction field `ℚ(q)` of `ℤ[q, q⁻¹]` and dualizing the map `ch`, which then
> becomes the composition `ℚ(q) Seq(ν) → f_ν → K₀(R(ν))_{ℚ(q)}`, we conclude that `γ_{ℚ(q)}`,
> restricted to weight `ν`, is a surjective map of `ℚ(q)`-vector spaces. […]
> **Proposition 3.18.** `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is an isomorphism.

## The argument formalized here

Fix `ν`, let `[P_b]` be the basis of `K₀(R(ν))` (indecomposable projectives, `k0Basis`) and
`[S_b]` the basis of `G₀(R(ν))` (their simple tops, `g0Basis`). Write `[P_j] = ∑_b a_{jb} [P_b]`
for `j ∈ Seq(ν)`. The pairing `([P], [M]) = gdim HOM(P, M)` is antilinear in `P`
(`Graded.pairing_smul_left_of_eq`), `([P_j], [M]) = ch(M)_j` (`GradingDatum.pairing_projP`, KL I
eq. `eq_char1`), and `([P_b], [S_c]) = δ_{bc} d_b` with `d_b = dim END(S_b)_0`
(`pairing_k0Basis_g0Basis`). Hence (`chG0_g0B`)

  `ch(S_b)_j = \overline{a_{jb}} · d_b`.

By Theorem 3.17 (`thm_3_17_G0`) the characters `ch(S_b)` are linearly independent over
`ℤ[q, q⁻¹]`, so (`d_b ≠ 0`, `endDim_ne_zero`) the columns `j ↦ a_{jb}` are linearly independent
over `ℚ(v)` after `q ↦ v⁻¹` (`linearIndependent_laurentEval`: `ℚ(v)` is the fraction field of
`ℤ[v, v⁻¹]`, `isFractionRing_vAlgebra`). Therefore the rows span: each `[P_b]` is a
`ℚ(v)`-linear combination of the `[P_j] = γ(θ_{j_1} ⋯ θ_{j_m})` (`exists_rowComb_eq_single`,
a rank argument with `Matrix.rank_transpose`; `exists_toK0Q_k0B_eq_sum`). This is the paper's
"dualizing `ch`". Corollary 3.19 (`d_b = 1`) is not needed here.

## Main results

* `Graded.pairing_T_smul_left`, `Graded.pairing_smul_left_of_eq` : `(p x, y) = p̄ (x, y)`.
* `GradingDatum.pairing_projP` : `([P_s], y) = ch(y)_s` on all of `G₀(R(ν))`.
* `KLGamma.isFractionRing_vAlgebra`, `KLGamma.linearIndependent_laurentEval`.
* `KLGamma.K0Qgrade_le_map_gammaQ` : **KL I, Proposition 3.18, weight by weight**:
  `K₀(R(ν))_{ℚ(q)} ⊆ γ_{ℚ(q)}('f_ν)` (unconditionally, on `'f`).
* `KLGamma.gammaF_surjective`, `KLGamma.gammaF_bijective`, `KLGamma.gammaFEquiv` :
  **KL I, Proposition 3.18**: `γ_{ℚ(q)} : f ≅ K₀(R)_{ℚ(q)}` as `ℚ(q)`-algebras (injectivity is
  Proposition 3.4, `gammaF_injective`), under the Gabber–Kac hypothesis `hGK` used to define `f`.

As in the rest of the repository, `ℚ(q)` is realised as `ℚ(v) = RatFunc ℚ` with `q ↦ v⁻¹`
(`KLGamma.qToV`), and `K₀(R)_{ℚ(q)} = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` (`KLGamma.K0Q`).
-/

noncomputable section

namespace Categorification

open LaurentPolynomial Graded

section PairingShift

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- `([P{a}], [M]) = q^{-a} ([P], [M])`. -/
theorem Graded.pairing_T_smul_left (a : ℤ) (x : K0 𝒜) (y : G0 𝒜) :
    pairing ((T a : LaurentPolynomial ℤ) • x) y = HahnSeries.single (-a) 1 * pairing x y := by
  rw [K0.T_smul]
  induction x using K0.induction_on with
  | of P =>
    induction y using G0.induction_on with
    | of M =>
      rw [K0.shiftHom_of, pairing_of_of, pairing_of_of, ← GProj.gdim_comp_add]
      congr 1
      funext d
      exact homGrade_shift_left a d
    | zero => simp
    | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
    | neg y hy => simp only [map_neg, mul_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, mul_add, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, mul_neg, hx]

/-- `(p x, y) = p̄ (x, y)` when `(x, y)` is a Laurent polynomial. -/
theorem Graded.pairing_smul_left_of_eq {x : K0 𝒜} {y : G0 𝒜} {r : LaurentPolynomial ℤ}
    (h : pairing x y = toLaurentSeries r) (p : LaurentPolynomial ℤ) :
    pairing (p • x) y = toLaurentSeries (invert p * r) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' =>
    rw [add_smul, map_add, AddMonoidHom.add_apply, hp, hp', map_add, add_mul, map_add]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, smul_assoc, map_zsmul]
    change m • pairing ((T n : LaurentPolynomial ℤ) • x) y = _
    rw [pairing_T_smul_left, h, ← toLaurentSeries_T_mul, map_zsmul, invert_T, smul_mul_assoc,
      map_zsmul]

end PairingShift

/-! ### Linear algebra over a field -/

/-- Linear independence of families of functions `J → R` over a domain `R` passes to its
fraction field. -/
theorem linearIndependent_algebraMap_of_isFractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {B J : Type*} (w : B → J → R)
    (hw : LinearIndependent R w) :
    LinearIndependent K (fun b j => algebraMap R K (w b j)) := by
  let Φ : (J → R) →ₗ[R] (J → K) :=
    LinearMap.pi fun j => (Algebra.linearMap R K).comp (LinearMap.proj j)
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro f g h
    funext j
    exact IsFractionRing.injective R K (congrFun h j)
  exact (hw.map' Φ hΦ).localization K (nonZeroDivisors R)

/-- If the columns of a `J × B` matrix over a field are linearly independent, each standard row
vector is a linear combination of its rows (rank of the transpose). -/
theorem exists_rowComb_eq_single {K B J : Type*} [Field K] [Fintype B] [Fintype J]
    [DecidableEq B] (A : J → B → K) (h : LinearIndependent K (fun b j => A j b)) (b : B) :
    ∃ c : J → K, ∀ b', ∑ j, c j * A j b' = if b' = b then 1 else 0 := by
  classical
  let M : Matrix J B K := Matrix.of A
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    rw [Fintype.linearIndependent_iff] at h
    have := h v (by
      funext j
      have := congrFun hv j
      simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
    rw [Submodule.mem_bot]
    funext b
    exact this b
  have hr : M.rank = Fintype.card B := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have htop : LinearMap.range M.transpose.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [← Matrix.rank, Matrix.rank_transpose, hr, Module.finrank_fintype_fun_eq_card]
  obtain ⟨c, hc⟩ : Pi.single b 1 ∈ LinearMap.range M.transpose.mulVecLin := htop ▸ Submodule.mem_top
  refine ⟨c, fun b' => ?_⟩
  have := congrFun hc b'
  rw [Matrix.mulVecLin_apply] at this
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, M, Matrix.of_apply] at this
  rw [Pi.single_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

namespace KLR

open KLRAlgebra

variable {I : Type*} [DecidableEq I] {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-- **KL I, equation `eq_char1`, on `G₀`**: `([P_s], y) = ch(y)_s` for all `y ∈ G₀(R(ν))`. -/
theorem GradingDatum.pairing_projP (G : GradingDatum Q) {ν : Multiset I} (s : Seq ν)
    (y : G0 (G.grade ν)) :
    pairing (K0.of (G.projP s)) y = toLaurentSeries (chG0 G s y) := by
  have : pairing (K0.of (G.projP s)) = toLaurentSeries.comp (chG0 G s) := G0.hom_ext fun M => by
    rw [pairing_of_of, AddMonoidHom.comp_apply, chG0_of]
    letI := idemDecomposition M.grading (G.e_mem_grade s)
    haveI := M.finiteDimensional
    rw [toLaurentSeries_gdimPoly]
    exact gdim_homGrade_ofIdempotent (e_mul_self s) (G.e_mem_grade s)
  exact DFunLike.congr_fun this y

namespace KLGamma

open QuantumGroup Polynomial

/-! ### `ℚ(v)` is the fraction field of `ℤ[v, v⁻¹]` -/

theorem laurentEval_C {K : Type*} [CommRing K] (v : Kˣ) (a : ℤ) :
    laurentEval v (LaurentPolynomial.C a) = a := by
  rw [← RingHom.comp_apply, RingHom.ext_int ((laurentEval v).comp LaurentPolynomial.C)
    (Int.castRingHom K)]
  rfl

/-- `p(v) = p̄(v⁻¹)`: evaluation at `v` is `qToV` (`q ↦ v⁻¹`) after the bar involution. -/
theorem laurentEval_vQ_invert (p : LaurentPolynomial ℤ) :
    laurentEval vQ (invert p) = qToV p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add]
  | C_mul_T n a =>
    rw [map_mul, invert_C, invert_T, map_mul, map_mul, laurentEval_T, qToV_T, qToV,
      laurentEval_C, laurentEval_C]

theorem laurentEval_vQ_injective : Function.Injective (laurentEval (vQ : (RatFunc ℚ)ˣ)) := by
  intro p p' h
  apply invert.injective
  apply qToV_injective
  have hi : ∀ q : LaurentPolynomial ℤ, invert (invert q) = q := fun q => by ext n; simp
  rwa [← laurentEval_vQ_invert, ← laurentEval_vQ_invert, hi, hi]

/-- Evaluation at `v` on integral polynomials agrees with the inclusion `ℚ[X] ⊆ ℚ(v)`. -/
theorem laurentEval_vQ_toLaurent (g : ℤ[X]) :
    laurentEval vQ (toLaurent g) =
      algebraMap ℚ[X] (RatFunc ℚ) (g.map (algebraMap ℤ ℚ)) := by
  have : (laurentEval (vQ : (RatFunc ℚ)ˣ)).comp toLaurent =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (algebraMap ℤ ℚ)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.toLaurent_C, laurentEval_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, eq_intCast, map_intCast]
      exact (map_intCast _ a).symm
    · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.toLaurent_X, laurentEval_T,
        Polynomial.coe_mapRingHom, Polynomial.map_X, RatFunc.algebraMap_X, zpow_one, vQ_val]
  exact congrArg (fun f : ℤ[X] →+* RatFunc ℚ => f g) this

/-- Every polynomial over `ℚ` is `p(v) / N` with `p ∈ ℤ[v]`, `N ∈ ℤ \ 0`. -/
theorem exists_laurentEval_eq_mul (p : ℚ[X]) :
    ∃ (x : LaurentPolynomial ℤ) (N : ℤ), N ≠ 0 ∧
      algebraMap ℚ[X] (RatFunc ℚ) p * N = laurentEval vQ x := by
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) p
  refine ⟨toLaurent (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p), b,
    nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [laurentEval_vQ_toLaurent, hb, map_zsmul, zsmul_eq_mul, mul_comm]

/-- **`ℚ(v)` is the fraction field of `ℤ[v, v⁻¹]`** (`q ↦ v`): every element is a quotient of
Laurent polynomials in `v` with integer coefficients. -/
theorem exists_eq_laurentEval_div (z : RatFunc ℚ) :
    ∃ x y : LaurentPolynomial ℤ, z = laurentEval vQ x / laurentEval vQ y := by
  haveI : CharZero (RatFunc ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (RatFunc ℚ)).injective
  obtain ⟨xn, Nn, hNn, hn⟩ := exists_laurentEval_eq_mul (RatFunc.num z)
  obtain ⟨xd, Nd, hNd, hd⟩ := exists_laurentEval_eq_mul (RatFunc.denom z)
  refine ⟨xn * LaurentPolynomial.C Nd, xd * LaurentPolynomial.C Nn, ?_⟩
  have hden : algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom z) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 (RatFunc.denom_ne_zero z)
  have hNn' : (Nn : RatFunc ℚ) ≠ 0 := Int.cast_ne_zero.2 hNn
  have hNd' : (Nd : RatFunc ℚ) ≠ 0 := Int.cast_ne_zero.2 hNd
  have hz := RatFunc.num_div_denom z
  rw [map_mul, map_mul, laurentEval_C, laurentEval_C, ← hn, ← hd]
  generalize algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num z) = a at hz ⊢
  generalize algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom z) = d at hz hden ⊢
  subst hz
  field_simp
  ring

/-- The `ℤ[q, q⁻¹]`-algebra structure on `ℚ(v)` with `q ↦ v` (not a global instance). -/
@[reducible] def vAlgebra : Algebra (LaurentPolynomial ℤ) (RatFunc ℚ) :=
  (laurentEval (vQ : (RatFunc ℚ)ˣ)).toAlgebra

theorem isFractionRing_vAlgebra :
    @IsFractionRing (LaurentPolynomial ℤ) _ (RatFunc ℚ) _ vAlgebra := by
  letI := vAlgebra
  letI : SMul (LaurentPolynomial ℤ) (RatFunc ℚ) := Algebra.toSMul
  haveI : FaithfulSMul (LaurentPolynomial ℤ) (RatFunc ℚ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 laurentEval_vQ_injective
  exact IsFractionRing.of_field _ _ exists_eq_laurentEval_div

/-- **Linear independence over `ℤ[q, q⁻¹]` passes to `ℚ(v)`** (along `q ↦ v`). -/
theorem linearIndependent_laurentEval {B J : Type*} (w : B → J → LaurentPolynomial ℤ)
    (hw : LinearIndependent (LaurentPolynomial ℤ) w) :
    LinearIndependent (RatFunc ℚ) (fun b j => laurentEval vQ (w b j)) :=
  @linearIndependent_algebraMap_of_isFractionRing _ _ _ _ _ vAlgebra isFractionRing_vAlgebra
    _ _ w hw

/-! ### Proposition 3.18 -/

section Prop318

variable (k : Type*) [Field k] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-- The basis `[P_b]` of `K₀(R(ν))` for the rings of KL I. -/
abbrev k0B (ν : Multiset I) :=
  (Gkl).k0Basis (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec) (fun a b _ => KL1.klP_ne_zero _ a b)
    KL1.klGradingDatum_degX_pos ν

/-- The basis `[S_b]` of `G₀(R(ν))` for the rings of KL I. -/
abbrev g0B (ν : Multiset I) :=
  (Gkl).g0Basis (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec) (fun a b _ => KL1.klP_ne_zero _ a b)
    KL1.klGradingDatum_degX_pos ν

/-- `dim_k END(S_b)_0`. -/
abbrev endDim {ν : Multiset I} (b : GProj.IndecClass ((Gkl).grade ν)) : ℕ :=
  Module.finrank k (endZero (KLRAlgebra k (klQ Γ) ν) b.top.grading)

theorem toLaurentSeries_C (c : ℤ) :
    toLaurentSeries (LaurentPolynomial.C c) = HahnSeries.single (0 : ℤ) c := by
  ext d
  rw [coeff_toLaurentSeries, LaurentPolynomial.C_apply, HahnSeries.coeff_single]
  by_cases h : d = 0 <;> simp [h, eq_comm]

/-- **The characters of the simples in terms of the coordinates of the `[P_j]`**:
`ch(S_b)_j = \overline{a_{j b}} · dim END(S_b)_0`, where `[P_j] = ∑_b a_{j b} [P_b]`. -/
theorem chG0_g0B {ν : Multiset I} (j : Seq ν) (b : GProj.IndecClass ((Gkl).grade ν)) :
    chG0 (Gkl) j (g0B k Γ ν b) =
      invert ((k0B k Γ ν).repr (K0.of ((Gkl).projP j)) b) * LaurentPolynomial.C (endDim k Γ b : ℤ) := by
  classical
  haveI := ((Gkl).finite_and_card_indecClass_le (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν).1
  haveI := Fintype.ofFinite (GProj.IndecClass ((Gkl).grade ν))
  apply toLaurentSeries_injective
  rw [← GradingDatum.pairing_projP]
  conv_lhs => rw [← (k0B k Γ ν).sum_repr (K0.of ((Gkl).projP j))]
  rw [map_sum, AddMonoidHom.finset_sum_apply]
  have hterm : ∀ b', pairing ((k0B k Γ ν).repr (K0.of ((Gkl).projP j)) b' • k0B k Γ ν b')
      (g0B k Γ ν b) = toLaurentSeries (invert ((k0B k Γ ν).repr (K0.of ((Gkl).projP j)) b') *
        LaurentPolynomial.C (if b' = b then (endDim k Γ b' : ℤ) else 0)) := fun b' => by
    refine pairing_smul_left_of_eq ?_ _
    rw [GradingDatum.pairing_k0Basis_g0Basis, toLaurentSeries_C]
    split_ifs <;> simp
  simp only [hterm]
  rw [Finset.sum_eq_single b (fun b' _ hb' => by rw [if_neg hb', map_zero, mul_zero, map_zero])
    (fun h => absurd (Finset.mem_univ b) h), if_pos rfl]

/-- **KL I, Theorem 3.17 in the form used for Proposition 3.18**: the characters of the simples
`[S_b]` are linearly independent over `ℤ[q, q⁻¹]`. -/
theorem linearIndependent_chMap_g0B (ν : Multiset I) :
    LinearIndependent (LaurentPolynomial ℤ) (fun b => chMap (Gkl) (g0B k Γ ν b)) :=
  (g0B k Γ ν).linearIndependent.map' _ (LinearMap.ker_eq_bot.2
    (thm_3_17_G0 (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec) (fun a b _ => KL1.klP_ne_zero _ a b)
      (Gkl) KL1.klGradingDatum_degX_pos))

/-- `dim END(S_b)_0 ≠ 0` (otherwise the character of `S_b` would vanish). -/
theorem endDim_ne_zero {ν : Multiset I} (b : GProj.IndecClass ((Gkl).grade ν)) :
    endDim k Γ b ≠ 0 := by
  intro h
  apply (linearIndependent_chMap_g0B k Γ ν).ne_zero b
  funext j
  show chG0 (Gkl) j (g0B k Γ ν b) = 0
  rw [chG0_g0B, h, Nat.cast_zero, map_zero, mul_zero]

/-- **The key step of KL I, Proposition 3.18**: each basis vector `[P_b]` of `K₀(R(ν))` is a
`ℚ(v)`-linear combination of the classes `[P_j]`, `j ∈ Seq(ν)`, in `K₀(R)_{ℚ(v)}`. -/
theorem exists_toK0Q_k0B_eq_sum {ν : Multiset I} (b : GProj.IndecClass ((Gkl).grade ν)) :
    ∃ c : Seq ν → RatFunc ℚ, toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (k0B k Γ ν b)) =
      ∑ j, c j • toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (K0.of ((Gkl).projP j))) := by
  classical
  haveI := ((Gkl).finite_and_card_indecClass_le (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν).1
  haveI := Fintype.ofFinite (GProj.IndecClass ((Gkl).grade ν))
  set A : Seq ν → GProj.IndecClass ((Gkl).grade ν) → LaurentPolynomial ℤ :=
    fun j b => (k0B k Γ ν).repr (K0.of ((Gkl).projP j)) b with hA
  have hK := linearIndependent_laurentEval _ (linearIndependent_chMap_g0B k Γ ν)
  have hval : ∀ b j, laurentEval vQ (chMap (Gkl) (g0B k Γ ν b) j) =
      ((endDim k Γ b : ℤ) : RatFunc ℚ) * qToV (A j b) := fun b j => by
    show laurentEval vQ (chG0 (Gkl) j (g0B k Γ ν b)) = _
    rw [chG0_g0B, map_mul, laurentEval_vQ_invert, laurentEval_C, mul_comm]
  have hd : ∀ b : GProj.IndecClass ((Gkl).grade ν), ((endDim k Γ b : ℤ) : RatFunc ℚ) ≠ 0 :=
    fun b => by
      haveI : CharZero (RatFunc ℚ) :=
        charZero_of_injective_algebraMap (algebraMap ℚ (RatFunc ℚ)).injective
      exact_mod_cast endDim_ne_zero k Γ b
  have hK' : LinearIndependent (RatFunc ℚ) (fun b j => qToV (A j b)) := by
    have := hK.units_smul (fun b => (Units.mk0 _ (hd b))⁻¹)
    convert this using 1
    funext b j
    simp only [Pi.smul_apply', hval, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    show qToV (A j b) = ((endDim k Γ b : ℤ) : RatFunc ℚ)⁻¹ *
      (((endDim k Γ b : ℤ) : RatFunc ℚ) * qToV (A j b))
    rw [inv_mul_cancel_left₀ (hd b)]
  obtain ⟨c, hc⟩ := exists_rowComb_eq_single (fun j b => qToV (A j b)) hK' b
  refine ⟨c, ?_⟩
  have hPj : ∀ j, toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (K0.of ((Gkl).projP j))) =
      ∑ b', qToV (A j b') • toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (k0B k Γ ν b')) := fun j => by
    conv_lhs => rw [← (k0B k Γ ν).sum_repr (K0.of ((Gkl).projP j))]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [K0R_of_smul, toK0Q_smul]
  simp only [hPj, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

omit [DecidableEq I] in
theorem seq_ofList_ofFn {ν : Multiset I} (j : Seq ν) :
    Seq.ofList (List.ofFn j.1) ((Fin.univ_val_map _).symm.trans j.2) = j := by
  apply Subtype.ext
  funext a
  show (Seq.ofList _ _).lbl a = j.1 a
  rw [Seq.ofList_lbl, List.getElem_ofFn]

/-- `[P_j] = γ_{ℚ(q)}(θ_{j_1} ⋯ θ_{j_m})` with `θ_{j_1} ⋯ θ_{j_m} ∈ 'f_ν`. -/
theorem toK0Q_projP_eq_gammaQ {ν : Multiset I} (j : Seq ν) :
    toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (K0.of ((Gkl).projP j))) =
      gammaQ k Γ (PreF.word (FreeMonoid.ofList (List.ofFn j.1))) := by
  rw [gammaQ_word, FreeMonoid.toList_ofList,
    clsSeq_eq k Γ _ ((Fin.univ_val_map _).symm.trans j.2), seq_ofList_ofFn]
  rfl

omit [DecidableEq I] in
theorem word_ofFn_mem_grade {ν : Multiset I} (j : Seq ν) :
    (PreF.word (FreeMonoid.ofList (List.ofFn j.1)) : PreF (RatFunc ℚ) I) ∈
      PreF.grade (RatFunc ℚ) ν := by
  rw [PreF.grade, PreF.supp_eq_span]
  refine Submodule.subset_span ⟨_, ?_, rfl⟩
  show ((FreeMonoid.toList (FreeMonoid.ofList (List.ofFn j.1)) : List I) : Multiset I) = ν
  rw [FreeMonoid.toList_ofList]
  exact (Fin.univ_val_map _).symm.trans j.2

/-- **KL I, Proposition 3.18, weight by weight** (unconditionally, on `'f`): every element of
`K₀(R(ν))_{ℚ(q)}` is `γ_{ℚ(q)}(x)` for some `x ∈ 'f_ν`. -/
theorem K0Qgrade_le_map_gammaQ (ν : Multiset I) :
    K0Qgrade k Γ ν ≤ (PreF.grade (RatFunc ℚ) ν).map (gammaQ k Γ).toLinearMap := by
  classical
  haveI := ((Gkl).finite_and_card_indecClass_le (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν).1
  haveI := Fintype.ofFinite (GProj.IndecClass ((Gkl).grade ν))
  have hP : ∀ j : Seq ν, toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (K0.of ((Gkl).projP j))) ∈
      (PreF.grade (RatFunc ℚ) ν).map (gammaQ k Γ).toLinearMap := fun j =>
    ⟨_, word_ofFn_mem_grade j, (toK0Q_projP_eq_gammaQ k Γ j).symm⟩
  have hb : ∀ b, toK0Q k Γ (DirectSum.of (Gkl).K0fam ν (k0B k Γ ν b)) ∈
      (PreF.grade (RatFunc ℚ) ν).map (gammaQ k Γ).toLinearMap := fun b => by
    obtain ⟨c, hc⟩ := exists_toK0Q_k0B_eq_sum k Γ b
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hP j)
  rw [K0Qgrade, Submodule.span_le]
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  rw [← (k0B k Γ ν).sum_repr z, map_sum, map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [K0R_of_smul, toK0Q_smul]
  exact Submodule.smul_mem _ _ (hb b)

/-- **KL I, Proposition 3.18** (surjectivity): `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is surjective. -/
theorem gammaF_surjective (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    Function.Surjective (gammaF k Γ hGK) := by
  have hle : ∀ ν, K0Qgrade k Γ ν ≤ LinearMap.range (gammaF k Γ hGK).toLinearMap := fun ν => by
    refine (K0Qgrade_le_map_gammaQ k Γ ν).trans ?_
    rintro _ ⟨x, -, rfl⟩
    exact ⟨KL.π Γ x, gammaF_π k Γ hGK x⟩
  have htop : LinearMap.range (gammaF k Γ hGK).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← toK0Q_span_eq_top k Γ, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    induction z using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of ν x => exact hle ν (Submodule.subset_span ⟨_, ⟨x, rfl⟩, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  exact LinearMap.range_eq_top.1 htop

/-- **KL I, Proposition 3.18**: `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is bijective (with Proposition 3.4,
`gammaF_injective`), under the Gabber–Kac hypothesis used to define it on `f`. -/
theorem gammaF_bijective (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    Function.Bijective (gammaF k Γ hGK) :=
  ⟨gammaF_injective k Γ hGK, gammaF_surjective k Γ hGK⟩

/-- **KL I, Proposition 3.18**: the isomorphism of `ℚ(q)`-algebras
`γ_{ℚ(q)} : f ≅ K₀(R)_{ℚ(q)}` (under the Gabber–Kac hypothesis). -/
def gammaFEquiv (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    KL.F Γ ≃ₐ[RatFunc ℚ] K0Q k Γ :=
  AlgEquiv.ofBijective (gammaF k Γ hGK) (gammaF_bijective k Γ hGK)

@[simp] theorem gammaFEquiv_apply (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (x : KL.F Γ) : gammaFEquiv k Γ hGK x = gammaF k Γ hGK x := rfl

end Prop318

end KLGamma

end KLR

end Categorification
