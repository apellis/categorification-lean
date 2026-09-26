/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Gamma2
import Categorification.KLR.Prop34

/-!
# `γ` is injective for an arbitrary Cartan datum (KL II; KL I Proposition 3.4)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, paragraph "Grothendieck group as the quantum group": "Homomorphism `γ`
intertwines the bilinear forms on `_𝒜 f` and `K₀(R)`, `(x, y) = (γ(x), γ(y))` … Due to the
quantum Gabber–Kac theorem, this homomorphism is injective." This is the KL II version of
`Categorification.KLR.Prop34` (KL I, Proposition 3.4), for a Cartan datum `C`, the KL II grading
and a field `k`.

## The argument

As in `Categorification.KLR.Prop34`, for every sequence `j ∈ Seq ν` we use the functional

`pairP2 j : K₀(R)_{ℚ(q)} → ℚ((q))`, `a ⊗ z ↦ Ψ(a) · ([P_j], z_ν)`,

with `( , ) = gdim HOM` (`K0.homForm`) and `Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹` (`KLGamma.vToLS`).
The comparison on words (`lsCast_homForm_projP2`) matches the KL II graded dimension
(`GradingDatum.gdim_cornerGrade` for `klGradingDatum2`):

`([P_j], [P_i]) = ∑_{w • i = j} q^{- ∑_{(a,b) ∈ inv(w)} i_a · i_b} ∏_a (1 - q^{i_a · i_a})⁻¹`

with Lusztig's form on words (`PreF.form_wordFn`, for the general `dot`), using
`Ψ(c_i) = Ψ((1 - v_i^{-2})⁻¹) = (1 - q^{i·i})⁻¹` (`vToLS_c2`). Hence
`pairP2_y (γ x) = Ψ((x, θ_y))` for all `x ∈ 'f` and words `y` (`pairP2_gammaQ2`), so
`ker γ ⊆ ℐ` (`ker_gammaQ2_le_radical`) **unconditionally**; the Gabber–Kac hypothesis is only
needed to define `γ` on `f = 'f/ℐ`.

## Main results

* `KL2.hasGdim_grade2` : `R(ν)` has a graded dimension for the KL II grading (instance).
* `lsCast_homForm_projP2` : `([P_j], [P_i]) = Ψ((θ_i, θ_j))`.
* `ker_gammaQ2_le_radical` : `γ(x) = 0` on `'f` implies `x ∈ ℐ` (unconditionally).
* `gammaQ2_eq_zero_iff` : under Gabber–Kac, `ker γ = ℐ` on `'f`.
* `gammaF2_injective`, `gammaA2_injective`, `gammaInt2_injective` : **`γ` is injective** on `f`
  over `ℚ(q)` and on `_𝒜 f` (`gammaInt2` additionally assumes, as in its definition, that
  `K₀(R) → K₀(R)_{ℚ(q)}` is injective).
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra LaurentPolynomial QuantumGroup TypeA Equiv KL2 KLGamma

namespace KL2

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {C : CartanDatum I} {ν : Multiset I}

omit [DecidableEq I] in
theorem degX_pos2 (a : I) : 0 < (klGradingDatum2 k C).degX a := C.dot_self_pos a

/-- **KL II: `R(ν)` has a graded dimension** (over a field). -/
instance hasGdim_grade2 : HasGdim ((klGradingDatum2 k C).grade ν) :=
  (klGradingDatum2 k C).hasGdim_grade' (klQ2_eq_klP2 (o := KL1.stdOrient) stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) degX_pos2

omit [DecidableEq I] in
/-- For KL II, `deg(ψ_ρ 1_i) = - ∑_{(a,b) ∈ inv(w)} i_a · i_b` for any reduced word `ρ` of `w`. -/
theorem degW_eq2 {ρ : List ℕ} (hρ : IsReduced (Multiset.card ν) ρ) (i : Seq ν) :
    (klGradingDatum2 k C).degW ρ i =
      -∑ p ∈ invSet (Multiset.card ν) (wordProd (Multiset.card ν) ρ),
        C.dot (i.lbl p.1) (i.lbl p.2) := by
  rw [(klGradingDatum2 k C).degW_eq_sum_invSet hρ, ← Finset.sum_neg_distrib]
  rfl

/-- **KL II: graded dimension of `1_j R(ν) 1_i`**:
`gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{- ∑_{(a,b) ∈ inv(w)} i_a · i_b} ∏_a (1 - q^{i_a · i_a})⁻¹`. -/
theorem gdim_cornerGrade2 (j i : Seq ν) :
    gdim ((klGradingDatum2 k C).cornerGrade j i) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
        HahnSeries.single (-∑ p ∈ invSet (Multiset.card ν) w, C.dot (i.lbl p.1) (i.lbl p.2)) 1 *
          ∏ a, geomSeries (C.dot (i.lbl a) (i.lbl a)) := by
  rw [(klGradingDatum2 k C).gdim_cornerGrade (klQ2_eq_klP2 (o := KL1.stdOrient) stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (fun w => canWord _ w)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) degX_pos2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [degW_eq2 (isReduced_canWord _ w), wordProd_canWord]
  rfl

/-- **KL II, the form on the `P_i`**: `([P_j], [P_i]) = gdim (1_j R(ν) 1_i)`, explicitly. -/
theorem homForm_projP2 (j i : Seq ν) :
    K0.homForm ((klGradingDatum2 k C).grade ν) (K0.of ((klGradingDatum2 k C).projP j))
      (K0.of ((klGradingDatum2 k C).projP i)) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
        HahnSeries.single (-∑ p ∈ invSet (Multiset.card ν) w, C.dot (i.lbl p.1) (i.lbl p.2)) 1 *
          ∏ a, geomSeries (C.dot (i.lbl a) (i.lbl a)) := by
  rw [GradingDatum.homForm_projP, gdim_cornerGrade2]

end KL2

namespace KL2Gamma

/-! ### Scalars -/

section Scalars

/-- `(1 - q^d) · (1 - q^d)⁻¹ = 1` in `ℚ((q))` for `d > 0`. -/
theorem lsCast_geomSeries {d : ℤ} (hd : 0 < d) :
    lsCast (geomSeries d) = (1 - HahnSeries.single d (1 : ℚ))⁻¹ := by
  have h := congrArg lsCast (one_sub_mul_geomSeries hd)
  rw [map_mul, map_sub, lsCast_single, Int.cast_one, lsCast.map_one] at h
  exact eq_inv_of_mul_eq_one_right h

variable {I : Type*} (C : CartanDatum I)

/-- `Ψ((θ_i, θ_i)) = Ψ((1 - v^{-(i·i)})⁻¹) = (1 - q^{i·i})⁻¹`. -/
theorem vToLS_c2 (i : I) : vToLS (C.c i) = lsCast (geomSeries (C.dot i i)) := by
  rw [lsCast_geomSeries (C.dot_self_pos i), CartanDatum.c, lusztigC, map_inv₀, map_sub, map_one,
    vToLS_zpow, neg_neg]

end Scalars

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (C : CartanDatum I)

local notation "G2" => klGradingDatum2 k C

/-! ### The functionals `pairP2 j` -/

section Pairing

/-- `z ↦ ([P_j], z_ν)` on `K₀(R)`, for `j ∈ Seq ν` (KL II grading). -/
def homFormP2 {ν : Multiset I} (j : Seq ν) : (G2).K0R →+ LaurentSeries ℤ :=
  (K0.homForm ((G2).grade ν) (K0.of ((G2).projP j))).comp
    (DirectSum.component (LaurentPolynomial ℤ) (Multiset I) (G2).K0fam ν).toAddMonoidHom

theorem homFormP2_of {ν : Multiset I} (j : Seq ν) (x : K0 ((G2).grade ν)) :
    homFormP2 k C j (DirectSum.of (G2).K0fam ν x) =
      K0.homForm ((G2).grade ν) (K0.of ((G2).projP j)) x := by
  rw [homFormP2, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), DirectSum.component.lof_self]

theorem homFormP2_of_ne {ν μ : Multiset I} (j : Seq ν) (x : K0 ((G2).grade μ)) (h : μ ≠ ν) :
    homFormP2 k C j (DirectSum.of (G2).K0fam μ x) = 0 := by
  rw [homFormP2, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), DirectSum.component.of, dif_neg h, map_zero]

theorem lsCast_homFormP2_smul {ν : Multiset I} (j : Seq ν) (p : LaurentPolynomial ℤ)
    (z : (G2).K0R) :
    lsCast (homFormP2 k C j (p • z)) = vToLS (qToV p) * lsCast (homFormP2 k C j z) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_smul, map_add, map_add, hp, hp', map_add, map_add, add_mul]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    have hTz : homFormP2 k C j ((T n : LaurentPolynomial ℤ) • z) =
        HahnSeries.single n 1 * homFormP2 k C j z := by
      simp only [homFormP2, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
      rw [LinearMap.map_smul, K0.homForm_T_smul_right]
    rw [hT, smul_assoc, map_zsmul, map_zsmul, hTz, map_zsmul, map_zsmul, vToLS_qToV_T, map_mul,
      lsCast_single, Int.cast_one, smul_mul_assoc]

attribute [local instance] qToVAlgebra

/-- **The functional `pairP2 j : K₀(R)_{ℚ(q)} → ℚ((q))`**, `a ⊗ z ↦ Ψ(a) · ([P_j], z_ν)`. -/
def pairP2 {ν : Multiset I} (j : Seq ν) : K0Q2 k C →+ LaurentSeries ℚ :=
  TensorProduct.liftAddHom
    ((AddMonoidHom.mul.compl₂ (lsCast.toAddMonoidHom.comp (homFormP2 k C j))).comp
      vToLS.toAddMonoidHom)
    (fun p a z => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.mul_apply,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
      rw [lsCast_homFormP2_smul, Algebra.smul_def, map_mul]
      change vToLS (qToV p) * _ * _ = _
      ring)

theorem pairP2_tmul {ν : Multiset I} (j : Seq ν) (a : RatFunc ℚ) (z : (G2).K0R) :
    pairP2 k C j (a ⊗ₜ[LaurentPolynomial ℤ] z) = vToLS a * lsCast (homFormP2 k C j z) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem pairP2_toK0Q2 {ν : Multiset I} (j : Seq ν) (z : (G2).K0R) :
    pairP2 k C j (toK0Q2 k C z) = lsCast (homFormP2 k C j z) := by
  change pairP2 k C j ((1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] z) = _
  rw [pairP2_tmul, map_one, one_mul]

/-- `pairP2 j` is `Ψ`-semilinear over `ℚ(v)`. -/
theorem pairP2_smul {ν : Multiset I} (j : Seq ν) (b : RatFunc ℚ) (t : K0Q2 k C) :
    pairP2 k C j (b • t) = vToLS b * pairP2 k C j t := by
  refine TensorProduct.induction_on (motive := fun t : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (G2).K0R => pairP2 k C j (b • (t : K0Q2 k C)) = vToLS b * pairP2 k C j t) t
    ?_ ?_ ?_
  · show pairP2 k C j (b • (0 : K0Q2 k C)) = _
    rw [smul_zero, map_zero, mul_zero]
  · intro a z
    change pairP2 k C j (b • a ⊗ₜ[LaurentPolynomial ℤ] z) = _
    rw [TensorProduct.smul_tmul', pairP2_tmul, pairP2_tmul, smul_eq_mul, map_mul, mul_assoc]
  · intro x y hx hy
    change pairP2 k C j (b • ((x : K0Q2 k C) + y)) = _
    rw [smul_add, map_add, hx, hy, map_add, mul_add]

end Pairing

/-! ### Comparison on words -/

section Comparison

/-- **The forms agree on words** (KL II §3: "`γ` intertwines the bilinear forms"):
`([P_j], [P_i]) = Ψ((θ_i, θ_j))` for `i, j ∈ Seq ν`, `Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹`. -/
theorem lsCast_homForm_projP2 {ν : Multiset I} (i j : Seq ν) :
    lsCast (K0.homForm ((G2).grade ν) (K0.of ((G2).projP j)) (K0.of ((G2).projP i))) =
      vToLS (C.form (PreF.wordFn i.lbl) (PreF.wordFn j.lbl)) := by
  rw [KL2.homForm_projP2, CartanDatum.form, PreF.form_wordFn, map_mul, map_prod, PreF.permSum,
    map_sum, map_sum, Finset.sum_filter]
  simp_rw [vToLS_c2]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hE : PreF.invWt C.dot i.lbl σ =
      ∑ p ∈ invSet (Multiset.card ν) σ, C.dot (i.lbl p.1) (i.lbl p.2) :=
    Finset.sum_congr rfl fun p _ => C.symm _ _
  by_cases h : σ • i = j
  · rw [if_pos h, if_pos ((smul_eq_iff σ i j).1 h), map_mul, map_prod, lsCast_single, vToLS_zpow,
      hE, Int.cast_one, mul_comm]
  · rw [if_neg h, if_neg (mt (smul_eq_iff σ i j).2 h), map_zero, mul_zero]

/-- `pairP2_y (γ(θ_w)) = ([P_y], [P_w]) = Ψ((θ_w, θ_y))` for words `w`, `y`. -/
theorem pairP2_gammaQ2_word (w y : FreeMonoid I) :
    pairP2 k C (Seq.ofList (FreeMonoid.toList y) rfl) (gammaQ2 k C (PreF.word w)) =
      vToLS (C.form (PreF.word w) (PreF.word y)) := by
  rw [gammaQ2_word, pairP2_toK0Q2]
  by_cases h : ((FreeMonoid.toList w : List I) : Multiset I) = (FreeMonoid.toList y : Multiset I)
  · rw [clsSeq2_eq k C _ h, homFormP2_of]
    change lsCast (K0.homForm _ (K0.of ((G2).projP _)) (K0.of ((G2).projP (Seq.ofList _ h)))) = _
    rw [lsCast_homForm_projP2, wordFn_ofList_lbl, wordFn_ofList_lbl, FreeMonoid.ofList_toList,
      FreeMonoid.ofList_toList]
  · rw [clsSeq2, homFormP2_of_ne k C _ _ h, map_zero, CartanDatum.form,
      PreF.form_eq_zero_of_wt_ne (a := w) (b := y) h, map_zero]

/-- `pairP2_y (γ x) = Ψ((x, θ_y))` for all `x ∈ 'f` and words `y`. -/
theorem pairP2_gammaQ2 (x : PreF (RatFunc ℚ) I) (y : FreeMonoid I) :
    pairP2 k C (Seq.ofList (FreeMonoid.toList y) rfl) (gammaQ2 k C x) =
      vToLS (C.form x (PreF.word y)) := by
  induction x using PreF.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, LinearMap.add_apply, map_add]
  | smul_word w r =>
    rw [map_smul, pairP2_smul, pairP2_gammaQ2_word, map_smul, LinearMap.smul_apply, smul_eq_mul,
      map_mul]

end Comparison

/-! ### Injectivity -/

section Injectivity

/-- **The kernel of `γ_{ℚ(q)}` on `'f` lies in the radical `ℐ` of Lusztig's form**
(unconditionally; KL II §3, KL I Prop. 3.4, proof). -/
theorem ker_gammaQ2_le_radical {x : PreF (RatFunc ℚ) I} (hx : gammaQ2 k C x = 0) :
    x ∈ PreF.radical C.dot vQ C.c := by
  have hw : ∀ y : FreeMonoid I, C.form x (PreF.word y) = 0 := fun y => by
    apply vToLS_injective
    rw [← pairP2_gammaQ2 k C, hx, map_zero, map_zero]
  refine PreF.mem_radical.2 fun y => ?_
  induction y using PreF.induction_linear with
  | zero => rw [map_zero]
  | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  | smul_word w r =>
    have := hw w
    rw [CartanDatum.form] at this
    rw [LinearMap.map_smul, this, smul_zero]

/-- Under the Gabber–Kac hypothesis, `ker γ_{ℚ(q)} = ℐ` on `'f`. -/
theorem gammaQ2_eq_zero_iff (hGK : C.GabberKac vQ C.c) (x : PreF (RatFunc ℚ) I) :
    gammaQ2 k C x = 0 ↔ x ∈ PreF.radical C.dot vQ C.c := by
  refine ⟨ker_gammaQ2_le_radical k C, fun hx => ?_⟩
  rw [← gammaF2_π k C hGK, PreF.π_eq_zero_iff.2 hx, map_zero]

/-- **KL II §3 (KL I, Proposition 3.4, for an arbitrary Cartan datum), over `ℚ(q)`**:
`γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is injective. The Gabber–Kac hypothesis `hGK` is used only to
define `γ_{ℚ(q)}` on `f = 'f/ℐ`. -/
theorem gammaF2_injective (hGK : C.GabberKac vQ C.c) : Function.Injective (gammaF2 k C hGK) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := PreF.π_surjective (dot := C.dot) (v := vQ) (c := C.c) z
  exact PreF.π_eq_zero_iff.2 (ker_gammaQ2_le_radical k C hz)

/-- **KL II §3**: the integral `γ : _𝒜 f → K₀(R)` (with values in the image of `K₀(R)` in
`K₀(R)_{ℚ(q)}`) is injective. -/
theorem gammaA2_injective (hGK : C.GabberKac vQ C.c) : Function.Injective (gammaA2 k C hGK) :=
  fun _ _ h => Subtype.ext (gammaF2_injective k C hGK (congrArg Subtype.val h))

/-- **KL II §3**: `γ : _𝒜 f → K₀(R)` is injective (where `gammaInt2` is defined, i.e. when
`K₀(R) → K₀(R)_{ℚ(q)}` is injective). -/
theorem gammaInt2_injective (hGK : C.GabberKac vQ C.c) (hinj : Function.Injective (toK0Q2 k C)) :
    Function.Injective (gammaInt2 k C hGK hinj) := fun _ _ h =>
  gammaA2_injective k C hGK ((K0RrangeEquiv2 k C hinj).symm.injective h)

end Injectivity

end KL2Gamma

end Categorification.KLR
