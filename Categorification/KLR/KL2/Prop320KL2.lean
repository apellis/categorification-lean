/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Prop318KL2

/-!
# KL II: Proposition 3.20 of KL I for an arbitrary Cartan datum

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3 (before Theorem 8): the proof of KL I, Theorem 1.1 carries over to an
arbitrary Cartan datum. Its integral step is KL I (arXiv:0803.4121v2), §3.2, **Proposition 3.20**
(TeX lines 2275–2303):

> `HOM(P(Y_b), S_c) = 0` if `b < c` and `HOM(P(Y_b), S_b) = 𝕜`,

whence the divided-power classes `[P_θ]` span `K₀(R(ν))` over `ℤ[q, q⁻¹]`.

## General form

The formalization of KL I (`Categorification.KLR.Prop320`) proves the key-maximal-sequence
induction `KLRAlgebra.isKeyMax_aux` for any `Q` satisfying the basis theorem hypotheses. The only
input specific to a given grading is the relation `[P_î] = f(i) [P_i]` between the projective of
the expanded sequence `î` and the divided-power projective `P_i`, with `f(i)` a Laurent polynomial
taking the value `∏_a n_a!` at `q = 1`. `GradingDatum.prop_3_20_of_div` and
`GradingDatum.k0Basis_mem_span_of_div` prove Proposition 3.20 and its consequence for **any**
grading datum with dots of positive degree and **any** such family of divided-power projectives.

## KL II

For the KL II rings of a Cartan datum `C` over a field, `f(i) = i! = ∏_a [n_a]_{q_{i_a}}^!`
(`q_c = q^{(c·c)/2}`, `KL2.divQFact2`), and `evalOne (i!) = ∏_a n_a!` (`evalOne_divQFact2`):

* `KL2Gamma.prop_3_20_KL2` : **KL I, Proposition 3.20, for KL II**.
* `KL2Gamma.k0B2_mem_span_projDiv2` : the classes `[P_θ]` of the KL II divided-power projectives
  span `K₀(R(ν))` over `ℤ[q, q⁻¹]`.
-/

noncomputable section

universe u

namespace Categorification.KLR

open Graded LaurentPolynomial QuantumGroup KLRAlgebra KLGamma

variable {I : Type u} [DecidableEq I]

/-! ### Proposition 3.20 for an arbitrary grading datum -/

namespace GradingDatum

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)
  (ν : Multiset I)
  (D : ∀ d : List (I × ℕ), (expandDiv d : Multiset I) = ν → GProj (G.grade ν))
  (f : List (I × ℕ) → LaurentPolynomial ℤ)
  (hD : ∀ d h, K0.of (G.projP (Seq.ofList (expandDiv d) h)) = f d • K0.of (D d h))
  (hf : ∀ d, evalOne (f d) = ((d.map fun q => q.2.factorial).prod : ℕ))

include hf in
omit [DecidableEq I] in
theorem ne_zero_of_evalOne_eq (d : List (I × ℕ)) : f d ≠ 0 := by
  intro h0
  have := hf d
  rw [h0, map_zero] at this
  have hpos : 0 < (d.map fun q => q.2.factorial).prod := List.prod_pos fun a ha => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
    exact Nat.factorial_pos _
  omega

include hPQ hP hG hD hf in
/-- **KL I, Proposition 3.20, for any grading datum** satisfying the basis theorem with dots of
positive degree, and any family of "divided-power projectives" `D d` with
`[P_{expandDiv d}] = f(d) [D d]` and `f(d)(1) = ∏ n_a!`: there are divided-power expressions `θ_b`
(`b` running over the simple `R(ν)`-modules `S_b` up to shift) and an injective `key` into a
linear order such that

* `HOM(D_{θ_b}, S_c) = 0` unless `key(b) ≤ key(c)`, and
* `HOM(D_{θ_b}, S_b)` is one-dimensional (`gdim = q^n`).

The proof is that of `KLGamma.prop_3_20` (KL I): `θ_b` is the run decomposition of the
key-maximal sequence of the support of `S_b`. -/
theorem prop_3_20_of_div :
    ∃ (θ : GProj.IndecClass (G.grade ν) → List (I × ℕ))
      (hθ : ∀ b, (expandDiv (θ b) : Multiset I) = ν)
      (key : GProj.IndecClass (G.grade ν) → List (Cardinal.{u} ×ₗ ℕ)),
      Function.Injective key ∧
      (∀ b c, pairing (K0.of (D (θ b) (hθ b))) (G.g0Basis hPQ hP hG ν c) ≠ 0 →
        key b ≤ key c) ∧
      ∀ b, ∃ n : ℤ, pairing (K0.of (D (θ b) (hθ b))) (G.g0Basis hPQ hP hG ν b) =
        HahnSeries.single n 1 := by
  classical
  haveI := G.finite_indecClass hPQ hP hG ν
  haveI := Fintype.ofFinite (GProj.IndecClass (G.grade ν))
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  let rk : I → Cardinal := embeddingToCardinal
  have hrk : Function.Injective rk := embeddingToCardinal.injective
  have hyp := fun c : GProj.IndecClass (G.grade ν) =>
    crystal_hypotheses_of_isGradedSimple G hG c.top.grading hPQ hP
      (GProj.IndecClass.isGradedSimple_top c)
  have hex : ∀ c : GProj.IndecClass (G.grade ν), ∃ s, IsKeyMax (K := K) Q rk ν c.top s :=
    fun c => by
      haveI := (hyp c).2.1
      haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) c.top
      exact exists_isKeyMax rk
  choose s hs using hex
  have hθ : ∀ c, (expandDiv (runs (List.ofFn (s c).1)) : Multiset I) = ν := fun c => by
    rw [expandDiv_runs]
    exact (Fin.univ_val_map _).symm.trans (s c).2
  set x : GProj.IndecClass (G.grade ν) → K0 (G.grade ν) :=
    fun c => K0.of (D (runs (List.ofFn (s c).1)) (hθ c)) with hxdef
  have hPx : ∀ c, K0.of (G.projP (s c)) = f (runs (List.ofFn (s c).1)) • x c := by
    intro c
    rw [hxdef, ← hD, seq_ofList_eq (s c) (expandDiv_runs _)]
  have hch : ∀ b c, chG0 G (s b) (G.g0Basis hPQ hP hG ν c) =
      invert (f (runs (List.ofFn (s b).1)) * (G.k0Basis hPQ hP hG ν).repr (x b) c) := by
    intro b c
    rw [G.chG0_g0Basis_eq hPQ hP hG, hPx, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hnonneg : ∀ (j : Seq ν) (c : GProj.IndecClass (G.grade ν)) (n : ℤ),
      0 ≤ chG0 G j (G.g0Basis hPQ hP hG ν c) n := by
    intro j c n
    haveI := (hyp c).1
    letI := idemDecomposition c.top.grading (G.e_mem_grade j)
    rw [G.chG0_g0Basis_eq_gdimPoly hPQ hP hG, gdimPoly_apply]
    exact Nat.cast_nonneg _
  have hevch : ∀ (j : Seq ν) (c : GProj.IndecClass (G.grade ν)),
      evalOne (chG0 G j (G.g0Basis hPQ hP hG ν c)) = dimCh (K := K) Q ν c.top j := by
    intro j c
    haveI := (hyp c).1
    rw [G.chG0_g0Basis_eq_gdimPoly hPQ hP hG]
    exact evalOne_gdimPoly_idem G c.top.grading j
  -- the key of `b`
  let key : GProj.IndecClass (G.grade ν) → List (Cardinal ×ₗ ℕ) := fun c => seqKey rk (s c)
  have htri : ∀ b c, (G.k0Basis hPQ hP hG ν).repr (x b) c ≠ 0 → key b ≤ key c := by
    intro b c hm
    haveI := (hyp c).1
    refine (hs c).2 (s b) (mem_seqSupp_iff_dimCh.2 fun h0 => hm ?_)
    have hzero : chG0 G (s b) (G.g0Basis hPQ hP hG ν c) = 0 :=
      eq_zero_of_evalOne_eq_zero (hnonneg _ c) (by rw [hevch, h0]; rfl)
    rw [hch] at hzero
    have := invert.injective (hzero.trans (map_zero _).symm)
    exact (mul_eq_zero.1 this).resolve_left (ne_zero_of_evalOne_eq f hf _)
  have hdiag : ∀ b, ∃ n, (G.k0Basis hPQ hP hG ν).repr (x b) b = T n := by
    intro b
    haveI := (hyp b).1
    haveI := (hyp b).2.1
    set m := (G.k0Basis hPQ hP hG ν).repr (x b) b
    -- `m` has nonnegative coefficients: `(x_b, [S_b]) = \bar m = gdim HOM(D_{θ_b}, S_b)`
    have hm0 : ∀ n, 0 ≤ m n := by
      intro n
      have h1 := G.pairing_g0Basis_eq_invert hPQ hP hG (x b) b
      rw [GradingDatum.g0Basis, G0.topBasis_apply, hxdef, pairing_of_of] at h1
      have h2 := congrArg (fun f : LaurentSeries ℤ => f.coeff (-n)) h1
      simp only [coeff_toLaurentSeries, invert_apply, neg_neg] at h2
      rw [← h2, coeff_gdim]
      exact Nat.cast_nonneg _
    -- `m(1) = 1`: `dim 1_{s_b} S_b = θ_b!`
    have hev := hevch (s b) b
    rw [(isKeyMax_aux hPQ hP rk _ ν rfl b.top (hyp b).2.2 (s b) (hs b)).1, hch,
      evalOne_invert, map_mul, hf] at hev
    have hpos : (0 : ℤ) < (runsFact (s b) : ℕ) := by
      rw [Nat.cast_pos, runsFact]
      exact List.prod_pos fun a ha => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
        exact Nat.factorial_pos _
    have hev1 : evalOne m = 1 := by
      have : ((runsFact (s b) : ℕ) : ℤ) * evalOne m = ((runsFact (s b) : ℕ) : ℤ) * 1 := by
        rw [mul_one]; exact hev
      exact mul_left_cancel₀ hpos.ne' this
    exact exists_eq_T_of_evalOne_eq_one hm0 hev1
  have hkey : Function.Injective key := by
    intro b c h
    have hsc : s b = s c := seqKey_injective rk hrk h
    haveI := (hyp b).1
    haveI := (hyp b).2.1
    haveI := (hyp c).1
    haveI := (hyp c).2.1
    have hsc' : IsKeyMax (K := K) Q rk ν c.top (s b) := hsc ▸ hs c
    obtain ⟨φ⟩ := (isKeyMax_aux hPQ hP rk _ ν rfl b.top (hyp b).2.2 (s b) (hs b)).2
      c.top (hyp c).2.2 hsc'
    haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) b.top
    have hφ : φ.toLinearMap ≠ 0 := by
      intro h0
      obtain ⟨v, hv⟩ := exists_ne (0 : b.top)
      exact hv (φ.injective (by simpa using LinearMap.congr_fun h0 v))
    obtain ⟨a, ⟨f⟩⟩ :=
      (GProj.IndecClass.isGradedSimple_top b).exists_gradedEquiv_shift_of_ne_zero
        (GProj.IndecClass.isGradedSimple_top c) hφ
    have f' : Graded.shift b.top.grading 0 ≃ᵍ[KLRAlgebra K Q ν]
        Graded.shift c.top.grading a :=
      (GradedEquiv.ofEq (A := KLRAlgebra K Q ν) (shift_zero b.top.grading)).trans f
    exact (GProj.IndecClass.eq_of_gradedEquiv_top_shift f').1
  refine ⟨_, hθ, key, hkey, fun b c h => htri b c fun hm => h ?_, fun b => ?_⟩
  · show pairing (x b) (G.g0Basis hPQ hP hG ν c) = 0
    rw [G.pairing_g0Basis_eq_invert hPQ hP hG, hm, map_zero, map_zero]
  · obtain ⟨n, hn⟩ := hdiag b
    refine ⟨-n, ?_⟩
    show pairing (x b) (G.g0Basis hPQ hP hG ν b) = _
    rw [G.pairing_g0Basis_eq_invert hPQ hP hG, hn, invert_T, toLaurentSeries_T]

include hPQ hP hG hD hf in
/-- **Consequence of KL I, Proposition 3.20, for any grading datum** (with a family of
divided-power projectives as in `prop_3_20_of_div`): the classes `[D_θ]` span `K₀(R(ν))` over
`ℤ[q, q⁻¹]`. -/
theorem k0Basis_mem_span_of_div (b : GProj.IndecClass (G.grade ν)) :
    G.k0Basis hPQ hP hG ν b ∈ Submodule.span (LaurentPolynomial ℤ)
      {z | ∃ (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν), z = K0.of (D d h)} := by
  classical
  haveI := G.finite_indecClass hPQ hP hG ν
  haveI := Fintype.ofFinite (GProj.IndecClass (G.grade ν))
  obtain ⟨θ, hθ, key, hkey, htri, hdiag⟩ := G.prop_3_20_of_div hPQ hP hG ν D f hD hf
  set x := fun c => K0.of (D (θ c) (hθ c)) with hx
  have htri' : ∀ b c, (G.k0Basis hPQ hP hG ν).repr (x b) c ≠ 0 → key b ≤ key c := fun b c hm =>
    htri b c fun h => hm (by
      rw [G.pairing_g0Basis_eq_invert hPQ hP hG] at h
      exact invert.injective (toLaurentSeries_injective (h.trans (map_zero _).symm) |>.trans
        (map_zero _).symm))
  have hdiag' : ∀ b, IsUnit ((G.k0Basis hPQ hP hG ν).repr (x b) b) := fun b => by
    obtain ⟨n, hn⟩ := hdiag b
    rw [G.pairing_g0Basis_eq_invert hPQ hP hG, ← toLaurentSeries_T] at hn
    have h := congrArg invert (toLaurentSeries_injective hn)
    have hi : ∀ q : LaurentPolynomial ℤ, invert (invert q) = q := fun q => by ext m; simp
    rw [hi, invert_T] at h
    rw [h]
    exact isUnit_T _
  refine Submodule.span_mono ?_
    (basis_mem_span_of_triangular (G.k0Basis hPQ hP hG ν) x key hkey htri' hdiag' b)
  rintro _ ⟨c, rfl⟩
  exact ⟨_, hθ c, rfl⟩

end GradingDatum

/-! ### KL II -/

namespace KL2Gamma

open KL2

/-- `[n]_{q^h}^!` takes the value `n!` at `q = 1`. -/
theorem evalOne_qfact_tUnit (h : ℤ) (n : ℕ) : evalOne (qfact (tUnit h) n) = n.factorial := by
  induction n with
  | zero => simp [qfact]
  | succ n ih =>
    rw [qfact_succ, map_mul, ih, qint_tUnit, map_sum]
    simp [evalOne_T, Nat.factorial_succ]
    ring

omit [DecidableEq I] in
/-- `i! = ∏_a [n_a]_{q_{i_a}}^!` takes the value `∏_a n_a!` at `q = 1`. -/
theorem evalOne_divQFact2 (C : CartanDatum I) (d : List (I × ℕ)) :
    evalOne (divQFact2 C d) = ((d.map fun q => q.2.factorial).prod : ℕ) := by
  rw [divQFact2, map_list_prod, List.map_map]
  push_cast [List.map_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp [evalOne_qfact_tUnit]

variable (k : Type*) [Field k] (C : CartanDatum I)

local notation "G2" => klGradingDatum2 k C

/-- **KL I, Proposition 3.20, for KL II** (an arbitrary Cartan datum, any field): for every
weight `ν` there are divided-power expressions `θ_b` (`b` running over the simple `R(ν)`-modules
`S_b` up to shift) and an injective `key` into a linear order such that

* `HOM(P_{θ_b}, S_c) = 0` unless `key(b) ≤ key(c)`, and
* `HOM(P_{θ_b}, S_b)` is one-dimensional (`gdim = q^n`),

where `P_θ = R(ν) ψ(1_θ) {-⟨θ⟩}` is the KL II divided-power projective (`KL2.projDiv2`) and
`([P], [M]) = gdim HOM(P, M)`. (The order is the one described in `KLGamma.prop_3_20`.) -/
theorem prop_3_20_KL2 (ν : Multiset I) :
    ∃ (θ : GProj.IndecClass ((G2).grade ν) → List (I × ℕ))
      (hθ : ∀ b, (expandDiv (θ b) : Multiset I) = ν)
      (key : GProj.IndecClass ((G2).grade ν) → List (Cardinal.{u} ×ₗ ℕ)),
      Function.Injective key ∧
      (∀ b c, pairing (K0.of (projDiv2 k C (θ b) (hθ b))) (g0B2 k C ν c) ≠ 0 → key b ≤ key c) ∧
      ∀ b, ∃ n : ℤ, pairing (K0.of (projDiv2 k C (θ b) (hθ b))) (g0B2 k C ν b) =
        HahnSeries.single n 1 :=
  (G2).prop_3_20_of_div _ _ _ ν (projDiv2 k C) (divQFact2 C)
    (fun d h => K0_projSeq2_expandDiv d h) (evalOne_divQFact2 C)

/-- **Consequence of KL I, Proposition 3.20, for KL II**: the classes `[P_θ]` of the KL II
divided-power projectives span `K₀(R(ν))` over `ℤ[q, q⁻¹]`. -/
theorem k0B2_mem_span_projDiv2 (ν : Multiset I) (b : GProj.IndecClass ((G2).grade ν)) :
    k0B2 k C ν b ∈ Submodule.span (LaurentPolynomial ℤ)
      {z | ∃ (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν),
        z = K0.of (projDiv2 k C d h)} :=
  (G2).k0Basis_mem_span_of_div _ _ _ ν (projDiv2 k C) (divQFact2 C)
    (fun d h => K0_projSeq2_expandDiv d h) (evalOne_divQFact2 C) b

end KL2Gamma

end Categorification.KLR
