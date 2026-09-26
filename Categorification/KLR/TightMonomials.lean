/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop34
import Categorification.KLR.DividedPowerK0
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.QuantumGroup.FormDivided

/-!
# KL I, §3.4: tight monomials and indecomposable projectives (Proposition 3.22)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §3.4 (TeX lines ~2402–2425):

> Following Lusztig, we say that a monomial `θ = θ_1^{(a_1)} ⋯ θ_k^{(a_k)}` is *tight* if it
> belongs to the canonical basis `𝐁` of `_𝒜 f`. It follows from the properties of the canonical
> basis that a monomial `θ` is tight if and only if `(θ, θ) - 1 ∈ q ℕ[q]` (or see Reineke,
> Proposition 3.1).
>
> **Proposition 3.22.** If a monomial `θ` is tight, the projective module `P_θ` is
> indecomposable.
>
> *Proof.* Tightness of `θ` implies that `HOM(P_θ, P_θ)` is a `ℤ_+`-graded `𝕜`-vector space which
> is one-dimensional in degree `0`. Therefore, any degree `0` endomorphism of `P_θ` is a multiple
> of the identity, and `P_θ` is indecomposable.

## What is formalized

The canonical basis `𝐁` is not available in this repository, so "tight" (membership in `𝐁`)
cannot be stated literally. The proof in the paper only uses the characterization of tightness
through the form, and that is what we formalize:

* `Graded.GProj.isIndec_of_coeff_homGdim_zero` : for any graded algebra with a graded dimension,
  if `dim_𝕜 HOM(P, P)_0 = 1` then `P` is indecomposable (the last sentence of the proof).
* `KLGamma.lsCast_homGdim_projDiv` : **`gdim HOM(P_θ, P_θ) = (θ, θ)`** for every divided-power
  monomial `θ = θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}`, where `(θ, θ)` is Lusztig's form on `'f`
  read in `ℚ((q))` via `Ψ : v ↦ q⁻¹` (`vToLS`; KL I: "our `q` is Lusztig's `v⁻¹`"). This is the
  identity `([P], [Q])' = (\bar{[P]}, [Q])` of KL I §3.2 (TeX lines ~2349–2357) for `P = Q = P_θ`,
  using that `[P_θ]` is bar-invariant; we prove it directly from `P_î ≅ P_θ^{⊕ [a]!}`
  (`K0_projP_expandDiv`), the comparison of forms on sequences (`lsCast_homForm_projP`) and the
  bar-invariance of the quantum factorials.
* `KLGamma.IsFormTight d` : `(θ_d, θ_d) ∈ 1 + q ℤ[[q]]` (in `ℚ((q))`, `q = v⁻¹`). By Lusztig
  (*Introduction to quantum groups*, 14.2) / Reineke (Prop. 3.1) this is equivalent to tightness
  of the monomial `θ_d`; that equivalence is **not** formalized.
* **`KLGamma.prop_3_22`** : if `IsFormTight d`, then `HOM(P_θ, P_θ)` is concentrated in degrees
  `≥ 0` and is one-dimensional in degree `0`, and `P_θ` is indecomposable.
* `KLGamma.isIndec_projDiv_of_coeff_form` : the weakest hypothesis the argument needs: the
  `q⁰`-coefficient of `(θ, θ)` is `1`.
* First example of §3.4 (TeX lines ~2427–2432), for any graph: `KLGamma.isFormTight_single`
  (`(θ_i^{(m)}, θ_i^{(m)}) = ∏_{s=1}^m (1 - q^{2s})⁻¹ ∈ 1 + q ℤ[[q]]`) and
  `KLGamma.prop_3_22_single` (`P_{i^{(m)}}` is indecomposable, with `END` in degrees `≥ 0`,
  one-dimensional in degree `0`).

The remaining examples of §3.4 (the tight monomials `θ_i^{(a)} θ_j^{(b)} θ_i^{(c)}`, `b ≥ a + c`,
for an edge `i — j`, and the cycle examples) and the remark that the argument works over `ℤ` are
not formalized.

## Remark on the printed criterion

The paper writes `(θ, θ) - 1 ∈ q ℕ[q]`; the values of the form are power series, not
polynomials: e.g. `(θ_i, θ_i) = (1 - q²)⁻¹ = 1 + q² + q⁴ + ⋯` (KL I Prop. 3.3(2)) although `θ_i`
is tight. The correct condition (Lusztig 14.2.2) is `(θ, θ) ∈ 1 + q ℤ[[q]]` (then automatically
with coefficients in `ℕ`, being a graded dimension). We use the power-series form.
-/

noncomputable section

namespace Categorification.Graded.GProj

open Module

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [HasGdim 𝒜]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- A nonzero object of `A-pmod` whose degree-zero endomorphism algebra is one-dimensional
(`k · id`) is indecomposable. -/
theorem isIndec_of_finrank_endZero_eq_one (P : GProj 𝒜)
    (h : finrank k (endZero A P.grading) = 1) : P.IsIndec A := by
  have hnt : Nontrivial P.carrier := by
    by_contra hP
    rw [not_nontrivial_iff_subsingleton] at hP
    have : Subsingleton (endZero A P.grading) := ⟨fun f g => Subtype.ext
      (LinearMap.ext fun x => Subsingleton.elim _ _)⟩
    rw [finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hnt, fun e he hidem => ?_⟩
  have hone : (1 : endZero A P.grading) ≠ 0 := fun h1 => by
    have : (1 : Module.End A P.carrier) = 0 := congrArg Subtype.val h1
    exact one_ne_zero this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : endZero A P.grading) hone).1 h ⟨e, he⟩
  have hce : (c • (1 : Module.End A P.carrier)) = e := congrArg Subtype.val hc
  have hc2 : c * c = c := by
    have h2 : (c • (1 : Module.End A P.carrier)) * (c • 1) = c • 1 := by rw [hce]; exact hidem
    rw [smul_mul_smul_comm, mul_one] at h2
    by_contra hne
    have := sub_eq_zero.2 h2
    rw [← sub_smul] at this
    exact one_ne_zero ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hc2 with rfl | rfl
  · left; rw [← hce, zero_smul]
  · right; rw [← hce, one_smul]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- `dim_k HOM(P, P)_0 = dim_k END(P)_0` (degree-zero maps are the degree-preserving ones). -/
theorem finrank_homGrade_zero_eq_finrank_endZero (P : GProj 𝒜) :
    finrank k (homGrade A P.grading P.grading 0) = finrank k (endZero A P.grading) := by
  refine (LinearEquiv.ofBijective (endZeroToHomGrade (A := A) P.grading)
    ⟨endZeroToHomGrade_injective P.grading, fun f => ?_⟩).finrank_eq.symm
  exact ⟨⟨f, preservesGrading_of_mem_homGrade_zero f.2⟩, rfl⟩

/-- **KL I, Proposition 3.22, the last step of the proof**: if `HOM(P, P)` is one-dimensional in
degree `0`, i.e. the `q⁰`-coefficient of `gdim HOM(P, P)` is `1`, then `P` is indecomposable. -/
theorem isIndec_of_coeff_homGdim_zero (P : GProj 𝒜) (h : (homGdim P P).coeff 0 = 1) :
    P.IsIndec A := by
  refine P.isIndec_of_finrank_endZero_eq_one ?_
  rw [homGdim, coeff_gdim] at h
  rw [← finrank_homGrade_zero_eq_finrank_endZero]
  exact_mod_cast h

end Categorification.Graded.GProj

namespace Categorification.KLR.KLGamma

open Graded KLRAlgebra LaurentPolynomial QuantumGroup Finset

/-! ### Bar-invariance of the quantum factorials in `ℤ[q, q⁻¹]` -/

theorem invert_qint_qUnitLP (n : ℕ) : invert (qint qUnitLP n) = qint qUnitLP n := by
  rw [qint_qUnitLP, map_sum, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [invert_T]
  congr 1
  have : ((n - 1 - j : ℕ) : ℤ) = n - 1 - j := by omega
  rw [this]
  ring

theorem invert_qfact_qUnitLP (n : ℕ) : invert (qfact qUnitLP n) = qfact qUnitLP n := by
  rw [qfact, map_prod]
  exact prod_congr rfl fun m _ => invert_qint_qUnitLP (m + 1)

/-- `i! = [a_1]! ⋯ [a_r]!` is bar-invariant. -/
theorem invert_divQFactLP {I : Type*} (d : List (I × ℕ)) : invert (divQFactLP d) = divQFactLP d := by
  rw [divQFactLP, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun q _ => invert_qfact_qUnitLP q.2

/-! ### The form `gdim HOM` and scalars -/

section Scalars

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- `(x, p y) = p (x, y)` in `ℚ((q))`, for `p ∈ ℤ[q, q⁻¹] ⊆ ℚ((q))`. -/
theorem lsCast_homForm_smul_right (p : LaurentPolynomial ℤ) (x y : K0 𝒜) :
    lsCast (K0.homForm 𝒜 x (p • y)) = vToLS (qToV p) * lsCast (K0.homForm 𝒜 x y) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_smul, map_add, map_add, hp, hp', map_add, map_add, add_mul]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, smul_assoc, map_zsmul, map_zsmul, K0.homForm_T_smul_right, map_zsmul, map_zsmul,
      vToLS_qToV_T, map_mul, lsCast_single, Int.cast_one, smul_mul_assoc]

/-- `(p x, y) = \bar p (x, y)` in `ℚ((q))`, for `p ∈ ℤ[q, q⁻¹] ⊆ ℚ((q))`. -/
theorem lsCast_homForm_smul_left (p : LaurentPolynomial ℤ) (x y : K0 𝒜) :
    lsCast (K0.homForm 𝒜 (p • x) y) = vToLS (qToV (invert p)) * lsCast (K0.homForm 𝒜 x y) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' =>
    rw [add_smul, map_add, AddMonoidHom.add_apply, map_add, hp, hp', map_add, map_add, map_add,
      add_mul]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, smul_assoc, map_zsmul (K0.homForm 𝒜)]
    show lsCast (m • K0.homForm 𝒜 (T n • x) y) = _
    rw [K0.homForm_T_smul_left, map_zsmul lsCast, map_zsmul invert, invert_T, map_zsmul qToV,
      map_zsmul vToLS, vToLS_qToV_T, map_mul, lsCast_single, Int.cast_one, smul_mul_assoc]

end Scalars

/-! ### `gdim HOM(P_θ, P_θ) = (θ, θ)` -/

section Form

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

omit [DecidableEq I] in
theorem word_ofList_replicate (i : I) (a : ℕ) :
    (PreF.word (FreeMonoid.ofList (List.replicate a i)) : PreF (RatFunc ℚ) I) = PreF.θ i ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, FreeMonoid.ofList_cons, PreF.word_of_mul, ih, pow_succ']

/-- `θ_î = [a_1]! ⋯ [a_r]! · θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}` in `'f`. -/
theorem word_expandDiv (d : List (I × ℕ)) :
    (PreF.word (FreeMonoid.ofList (expandDiv d)) : PreF (RatFunc ℚ) I) =
      (d.map fun q => qfact vQ q.2).prod • dpowMono Γ d := by
  induction d with
  | nil => simp [expandDiv, dpowMono]
  | cons q d ih =>
    rw [show expandDiv (q :: d) = expandDiv [q] ++ expandDiv d from expandDiv_append [q] d,
      FreeMonoid.ofList_append, PreF.word_mul, ih]
    have hd : dpowMono Γ (q :: d) = PreF.dpow (KL.C Γ).dot vQ q.1 q.2 * dpowMono Γ d := by
      simp only [dpowMono, List.map_cons, List.prod_cons]
    rw [hd, List.map_cons, List.prod_cons]
    have hx : expandDiv [q] = List.replicate q.2 q.1 := by simp [expandDiv]
    rw [hx, word_ofList_replicate, PreF.dpow, vi_ofGraph_vQ, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_comm (qfact vQ q.2), mul_assoc, mul_inv_cancel₀ (qfact_vQ_ne_zero q.2),
      mul_one]

/-- **`gdim HOM(P_θ, P_θ) = (θ, θ)`** for a divided-power monomial
`θ = θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}`, where the right side is Lusztig's form on `'f` read in
`ℚ((q))` via `Ψ : v ↦ q⁻¹`. (KL I §3.2, TeX lines ~2349–2357: `([P], [Q])' = (\bar{[P]}, [Q])`,
here with `\bar{[P_θ]} = [P_θ]`.) -/
theorem lsCast_homGdim_projDiv {ν : Multiset I} (d : List (I × ℕ))
    (h : (expandDiv d : Multiset I) = ν) :
    lsCast (GProj.homGdim (projDiv k Γ d h) (projDiv k Γ d h)) =
      vToLS ((KL.C Γ).form (dpowMono Γ d) (dpowMono Γ d)) := by
  set t := Seq.ofList (expandDiv d) h
  set c := divQFactLP d
  set Q := (d.map fun q => qfact vQ q.2).prod
  have hcQ : qToV c = Q := qToV_divQFactLP d
  have hQ : vToLS Q ≠ 0 := by
    rw [← hcQ]
    exact (map_ne_zero_iff _ vToLS_injective).2 (qToV_divQFactLP_ne_zero d)
  have key := lsCast_homForm_projP k Γ t t
  rw [wordFn_ofList_lbl, word_expandDiv Γ d] at key
  change lsCast (K0.homForm _ (K0.of (projSeq k Γ t)) (K0.of (projSeq k Γ t))) = _ at key
  have hform : (KL.C Γ).form (Q • dpowMono Γ d) (Q • dpowMono Γ d) =
      Q * (Q * (KL.C Γ).form (dpowMono Γ d) (dpowMono Γ d)) := by
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  rw [hform, K0_projP_expandDiv d h, lsCast_homForm_smul_left, lsCast_homForm_smul_right,
    invert_divQFactLP, map_mul, map_mul, hcQ, K0.homForm_of, ← mul_assoc, ← mul_assoc] at key
  exact mul_left_cancel₀ (mul_ne_zero hQ hQ) key

/-! ### Proposition 3.22 -/

/-- The monomial `θ_d` satisfies the form criterion for tightness: `(θ_d, θ_d) ∈ 1 + q ℤ[[q]]`
in `ℚ((q))` (`q = v⁻¹`). By Lusztig (*Introduction to quantum groups*, 14.2) and Reineke
(Prop. 3.1) this is equivalent to `θ_d` being tight (lying in the canonical basis); that
equivalence is not formalized here. -/
def IsFormTight (d : List (I × ℕ)) : Prop :=
  ∀ n : ℤ, n ≤ 0 → (vToLS ((KL.C Γ).form (dpowMono Γ d) (dpowMono Γ d))).coeff n =
    if n = 0 then 1 else 0

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem lsCast_coeff (x : LaurentSeries ℤ) (n : ℤ) : (lsCast x).coeff n = (x.coeff n : ℚ) :=
  rfl

/-- `dim_𝕜 HOM(P_θ, P_θ)_n` is the `q^n`-coefficient of `(θ, θ)`. -/
theorem finrank_homGrade_projDiv {ν : Multiset I} (d : List (I × ℕ))
    (h : (expandDiv d : Multiset I) = ν) (n : ℤ) :
    ((Module.finrank k (homGrade (KLRAlgebra k (klQ Γ) ν) (projDiv k Γ d h).grading
        (projDiv k Γ d h).grading n) : ℤ) : ℚ) =
      (vToLS ((KL.C Γ).form (dpowMono Γ d) (dpowMono Γ d))).coeff n := by
  rw [← lsCast_homGdim_projDiv k Γ d h, lsCast_coeff, GProj.homGdim, coeff_gdim]

/-- **KL I, Proposition 3.22 (under the form criterion for tightness)**: if
`(θ, θ) ∈ 1 + q ℤ[[q]]` for the divided-power monomial `θ = θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}`,
then `HOM(P_θ, P_θ)` is concentrated in degrees `≥ 0` and is one-dimensional in degree `0`, and
the projective module `P_θ` is indecomposable. -/
theorem prop_3_22 {ν : Multiset I} (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν)
    (ht : IsFormTight Γ d) :
    (∀ n : ℤ, n < 0 → Module.finrank k (homGrade (KLRAlgebra k (klQ Γ) ν)
        (projDiv k Γ d h).grading (projDiv k Γ d h).grading n) = 0) ∧
      Module.finrank k (homGrade (KLRAlgebra k (klQ Γ) ν) (projDiv k Γ d h).grading
        (projDiv k Γ d h).grading 0) = 1 ∧
      (projDiv k Γ d h).IsIndec (KLRAlgebra k (klQ Γ) ν) := by
  have hc : ∀ n, n ≤ 0 → Module.finrank k (homGrade (KLRAlgebra k (klQ Γ) ν)
      (projDiv k Γ d h).grading (projDiv k Γ d h).grading n) = if n = 0 then 1 else 0 := by
    intro n hn
    have e := finrank_homGrade_projDiv k Γ d h n
    rw [ht n hn] at e
    split_ifs at e ⊢ <;> exact_mod_cast e
  refine ⟨fun n hn => by rw [hc n hn.le, if_neg hn.ne], by rw [hc 0 le_rfl, if_pos rfl], ?_⟩
  refine GProj.isIndec_of_coeff_homGdim_zero _ ?_
  rw [GProj.homGdim, coeff_gdim, hc 0 le_rfl, if_pos rfl, Nat.cast_one]

/-- **KL I, Proposition 3.22, minimal hypothesis**: if the `q⁰`-coefficient of `(θ, θ)` is `1`,
then `P_θ` is indecomposable. -/
theorem isIndec_projDiv_of_coeff_form {ν : Multiset I} (d : List (I × ℕ))
    (h : (expandDiv d : Multiset I) = ν)
    (h0 : (vToLS ((KL.C Γ).form (dpowMono Γ d) (dpowMono Γ d))).coeff 0 = 1) :
    (projDiv k Γ d h).IsIndec (KLRAlgebra k (klQ Γ) ν) := by
  refine GProj.isIndec_of_coeff_homGdim_zero _ ?_
  have e := finrank_homGrade_projDiv k Γ d h 0
  rw [h0] at e
  rw [GProj.homGdim, coeff_gdim]
  exact_mod_cast e

/-! ### Example: divided powers `θ_i^{(m)}` (KL I §3.4, first example) -/

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem lsCast_geomSeries_of_pos {d : ℤ} (hd : 0 < d) :
    lsCast (geomSeries d) = (1 - HahnSeries.single d (1 : ℚ))⁻¹ := by
  have h := congrArg lsCast (one_sub_mul_geomSeries hd)
  rw [map_mul, map_sub, lsCast_single, Int.cast_one, lsCast.map_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- `Ψ((θ_i^{(m)}, θ_i^{(m)})) = ∏_{s=1}^m (1 - q^{2s})⁻¹ = ∏_s ∑_n q^{2sn}` (Lusztig 1.4.4). -/
theorem vToLS_form_dpowMono_single (i : I) (m : ℕ) :
    vToLS ((KL.C Γ).form (dpowMono Γ [(i, m)]) (dpowMono Γ [(i, m)])) =
      lsCast (∏ a : Fin m, geomSeries (2 * ((a : ℤ) + 1))) := by
  have hd : dpowMono Γ [(i, m)] = PreF.dpow (KL.C Γ).dot vQ i m := by
    simp [dpowMono]
  rw [hd, KL.form_dpow_dpow, map_prod, map_prod, ← Finset.prod_range (fun a =>
    lsCast (geomSeries (2 * ((a : ℤ) + 1))))]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [lsCast_geomSeries_of_pos (by omega), map_inv₀, map_sub, map_one, map_pow,
    show ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) = ((vQ ^ (-1 : ℤ) : (RatFunc ℚ)ˣ) : RatFunc ℚ) by
      rw [zpow_neg_one], vToLS_zpow, HahnSeries.single_pow, neg_neg, one_pow]
  rw [nsmul_eq_mul, mul_one]
  push_cast
  rfl

/-- **The divided powers `θ_i^{(m)}` satisfy the tightness criterion**:
`(θ_i^{(m)}, θ_i^{(m)}) = ∏_{s=1}^m (1 - q^{2s})⁻¹ ∈ 1 + q ℤ[[q]]`. -/
theorem isFormTight_single (i : I) (m : ℕ) : IsFormTight Γ [(i, m)] := by
  intro n hn
  rw [vToLS_form_dpowMono_single, lsCast_coeff,
    coeff_prod_geomSeries (fun a : Fin m => 2 * ((a : ℤ) + 1)) (fun a => by dsimp only; omega)]
  rcases hn.lt_or_eq with hlt | rfl
  · rw [if_neg hlt.ne]
    have : {u : Fin m →₀ ℕ | Finsupp.weight (fun a : Fin m => 2 * ((a : ℤ) + 1)) u = n} = ∅ :=
      Set.eq_empty_iff_forall_not_mem.2 fun u hu => by
        have := weight_nonneg (w := fun a : Fin m => 2 * ((a : ℤ) + 1)) (fun a => by dsimp only; omega) u
        rw [Set.mem_setOf_eq] at hu
        omega
    rw [this]; simp
  · rw [if_pos rfl]
    have : {u : Fin m →₀ ℕ | Finsupp.weight (fun a : Fin m => 2 * ((a : ℤ) + 1)) u = 0} =
        {0} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      refine ⟨fun hu => Finsupp.ext fun a => ?_, fun hu => by rw [hu, map_zero]⟩
      have := le_weight (w := fun a : Fin m => 2 * ((a : ℤ) + 1)) (fun a => by dsimp only; omega) u a
      rw [hu] at this
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, Nat.card_unique, Nat.cast_one, Int.cast_one]

/-- **KL I §3.4, first example**: the divided-power projective `P_{i^{(m)}}` is indecomposable,
and `HOM(P_{i^{(m)}}, P_{i^{(m)}})` is concentrated in degrees `≥ 0`, one-dimensional in degree
`0`. -/
theorem prop_3_22_single {ν : Multiset I} (i : I) (m : ℕ)
    (h : (expandDiv [(i, m)] : Multiset I) = ν) :
    (∀ n : ℤ, n < 0 → Module.finrank k (homGrade (KLRAlgebra k (klQ Γ) ν)
        (projDiv k Γ [(i, m)] h).grading (projDiv k Γ [(i, m)] h).grading n) = 0) ∧
      Module.finrank k (homGrade (KLRAlgebra k (klQ Γ) ν) (projDiv k Γ [(i, m)] h).grading
        (projDiv k Γ [(i, m)] h).grading 0) = 1 ∧
      (projDiv k Γ [(i, m)] h).IsIndec (KLRAlgebra k (klQ Γ) ν) :=
  prop_3_22 k Γ [(i, m)] h (isFormTight_single Γ i m)

end Form

end Categorification.KLR.KLGamma
