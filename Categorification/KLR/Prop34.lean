/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Gamma
import Categorification.KLR.Pairing
import Categorification.QuantumGroup.FormWords
import Categorification.QuantumGroup.Bar

/-!
# KL I, Proposition 3.4: `γ` is injective

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §3.1, **Proposition 3.4** (TeX lines ~2018–2066): "There is an injective
homomorphism of `ℤ[q,q⁻¹]`-algebras `γ : _𝒜 f → K₀(R)` …". The proof in the paper: "the
homomorphism `γ_{ℚ(q)}` respects the bilinear forms … Since the bilinear form on `f` is
non-degenerate, homomorphism `γ_{ℚ(q)}` is injective."

## The argument formalized here

We do not construct a bilinear form on all of `K₀(R)_{ℚ(q)} = K0Q k Γ` (that would need the
bar involution on `K₀`). Instead, for every sequence `j ∈ Seq ν` we build a functional

`pairP j : K₀(R)_{ℚ(q)} → ℚ((q))`, `a ⊗ z ↦ Ψ(a) · ([P_j], z_ν)`,

where `( , )` is the repository's form `gdim HOM` (`K0.homForm`), which is `ℤ[q, q⁻¹]`-linear in
its second argument (`K0.homForm_T_smul_right`), `z_ν` is the weight-`ν` component, and
`Ψ : ℚ(v) → ℚ((q))` is the injective ring map with `v ↦ q⁻¹` (`vToLS`; KL I: "our `q` is
Lusztig's `v⁻¹`"). The functional is well defined on the tensor product precisely because
`Ψ ∘ qToV` is the inclusion `ℤ[q, q⁻¹] → ℚ((q))` (`vToLS_qToV_T`), and it is `Ψ`-semilinear
(`pairP_smul`).

The comparison on words (`pairP_gammaQ_word`): for words `w`, `y`,

`pairP_y (γ(θ_w)) = ([P_y], [P_w]) = Ψ((θ_w, θ_y))`,

comparing `KL1.homForm_projP`
(`([P_j], [P_i]) = ∑_{σ • i = j} q^{-∑_{inv(σ)} i_a · i_b} (1 - q²)^{-m}`, KL I §2.5) with the
closed formula for Lusztig's form on words (`PreF.form_wordFn`,
`(θ_a, θ_b) = ∏ c_{a_x} ∑_{b ∘ σ = a} v^{∑_{inv σ} a_y · a_x}`), using
`Ψ((1 - v^{-2})⁻¹) = (1 - q²)⁻¹` (`vToLS_c`). By linearity, `pairP_y (γ x) = Ψ((x, θ_y))` for
all `x ∈ 'f` (`pairP_gammaQ`). Hence if `γ_{ℚ(q)}(x) = 0` then `(x, θ_y) = 0` for all words
`y`, i.e. `x` lies in the radical `ℐ` of Lusztig's form (`ker_gammaQ_le_radical`). This step
uses neither the Gabber–Kac theorem nor the bar involution.

## Main results

* `ker_gammaQ_le_radical` : **unconditionally**, `γ_{ℚ(q)}(x) = 0` on `'f` implies `x ∈ ℐ`
  (together with `gammaQ_eq_zero_of_mem_span`: `⟨Serre⟩ ⊆ ker γ_{ℚ(q)} ⊆ ℐ`).
* `gammaQ_eq_zero_iff` : under the Gabber–Kac hypothesis, `γ_{ℚ(q)}(x) = 0 ↔ x ∈ ℐ`.
* `gammaF_injective` : **KL I Prop. 3.4 over `ℚ(q)`**: `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is
  injective (the Gabber–Kac hypothesis `hGK` is needed only to *define* `γ_{ℚ(q)}` on `f`).
* `gammaA_injective`, `gammaInt_injective` : **KL I Prop. 3.4**: the integral
  `γ : _𝒜 f → K₀(R)` is injective (`gammaInt` additionally assumes, as in its definition, that
  `K₀(R) → K₀(R)_{ℚ(q)}` is injective).

All results are for a field `k` (so that `gdim HOM` is defined).
-/

noncomputable section

namespace Categorification.KLR.KLGamma

open Graded KLRAlgebra LaurentPolynomial QuantumGroup TypeA Equiv

/-! ### Scalars: `ℤ((q)) → ℚ((q)) ← ℚ(v)` -/

section Scalars

/-- The coefficient map `ℤ((q)) → ℚ((q))`. -/
def lsCast : LaurentSeries ℤ →+* LaurentSeries ℚ where
  toFun x := x.map (Int.castRingHom ℚ)
  map_one' := by
    ext n
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul (Int.castRingHom ℚ).toNonUnitalRingHom
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem lsCast_single (n : ℤ) (r : ℤ) :
    lsCast (HahnSeries.single n r) = HahnSeries.single n (r : ℚ) := by
  ext g
  change (Int.castRingHom ℚ) ((HahnSeries.single n r).coeff g) = _
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

/-- The injective ring map `Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹` (KL I §3.1: "our `q` is Lusztig's
`v⁻¹`"): the bar involution `v ↦ v⁻¹` followed by the Laurent expansion `v ↦ q`. -/
def vToLS : RatFunc ℚ →+* LaurentSeries ℚ :=
  (RatFunc.coeAlgHom ℚ).toRingHom.comp barQ

theorem vToLS_injective : Function.Injective vToLS := by
  intro a b h
  have h' : barQ a = barQ b := RatFunc.coe_injective h
  rw [← barQ_barQ a, h', barQ_barQ]

theorem single_neg_one_zpow (n : ℤ) :
    (HahnSeries.single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ^ n = HahnSeries.single (-n) 1 := by
  have hinv : (HahnSeries.single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) =
      (HahnSeries.single (1 : ℤ) (1 : ℚ))⁻¹ := by
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]
  have hne : (HahnSeries.single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ≠ 0 := by
    simp
  induction n using Int.induction_on with
  | hz => simp [HahnSeries.single_zero_one]
  | hp n ih =>
    rw [zpow_add_one₀ hne, ih, HahnSeries.single_mul_single, mul_one]
    exact congrArg (fun t => HahnSeries.single t (1 : ℚ)) (by ring)
  | hn n ih =>
    rw [zpow_sub_one₀ hne, ih, hinv, inv_inv, HahnSeries.single_mul_single, mul_one]
    exact congrArg (fun t => HahnSeries.single t (1 : ℚ)) (by ring)

theorem vToLS_vQ : vToLS (vQ : RatFunc ℚ) = HahnSeries.single (-1 : ℤ) (1 : ℚ) := by
  rw [vToLS, RingHom.comp_apply, vQ_val, barQ_X, map_inv₀]
  change ((RatFunc.X : RatFunc ℚ) : LaurentSeries ℚ)⁻¹ = _
  rw [RatFunc.coe_X]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]

/-- `Ψ(v^n) = q^{-n}`. -/
theorem vToLS_zpow (n : ℤ) :
    vToLS ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ) = HahnSeries.single (-n) 1 := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, vToLS_vQ, single_neg_one_zpow]

/-- `Ψ ∘ qToV` is the inclusion `ℤ[q, q⁻¹] → ℚ((q))` on the basis: `Ψ(qToV(q^n)) = q^n`. -/
theorem vToLS_qToV_T (n : ℤ) :
    vToLS (qToV (T n)) = HahnSeries.single n 1 := by
  rw [qToV_T, vToLS_zpow, neg_neg]

/-- `(1 - q²) · (1 - q²)⁻¹ = 1` in `ℚ((q))`. -/
theorem lsCast_geomSeries_two :
    lsCast (geomSeries 2) = (1 - HahnSeries.single (2 : ℤ) (1 : ℚ))⁻¹ := by
  have h := congrArg lsCast (one_sub_mul_geomSeries (d := 2) (by norm_num))
  rw [map_mul, map_sub, lsCast_single, Int.cast_one, lsCast.map_one] at h
  exact eq_inv_of_mul_eq_one_right h

variable {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- `Ψ((θ_i, θ_i)) = Ψ((1 - v^{-2})⁻¹) = (1 - q²)⁻¹`. -/
theorem vToLS_c (i : I) : vToLS ((KL.C Γ).c i) = lsCast (geomSeries 2) := by
  rw [lsCast_geomSeries_two, CartanDatum.c, lusztigC, map_inv₀, map_sub, map_one, vToLS_zpow,
    CartanDatum.ofGraph_dot_self, neg_neg]

end Scalars

/-! ### The functionals `pairP j` on `K₀(R)_{ℚ(q)}` -/

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

section Pairing

/-- `z ↦ ([P_j], z_ν)` on `K₀(R)`, for `j ∈ Seq ν` (`z_ν` the weight-`ν` component). -/
def homFormP {ν : Multiset I} (j : Seq ν) : (Gkl).K0R →+ LaurentSeries ℤ :=
  (K0.homForm ((Gkl).grade ν) (K0.of ((Gkl).projP j))).comp
    (DirectSum.component (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν).toAddMonoidHom

theorem homFormP_of {ν : Multiset I} (j : Seq ν) (x : K0 ((Gkl).grade ν)) :
    homFormP k Γ j (DirectSum.of (Gkl).K0fam ν x) =
      K0.homForm ((Gkl).grade ν) (K0.of ((Gkl).projP j)) x := by
  rw [homFormP, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), DirectSum.component.lof_self]

theorem homFormP_of_ne {ν μ : Multiset I} (j : Seq ν) (x : K0 ((Gkl).grade μ)) (h : μ ≠ ν) :
    homFormP k Γ j (DirectSum.of (Gkl).K0fam μ x) = 0 := by
  rw [homFormP, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), DirectSum.component.of, dif_neg h, map_zero]

/-- `([P_j], (p z)_ν) = p ([P_j], z_ν)`, read in `ℚ((q))` through `Ψ ∘ qToV`. -/
theorem lsCast_homFormP_smul {ν : Multiset I} (j : Seq ν) (p : LaurentPolynomial ℤ)
    (z : (Gkl).K0R) :
    lsCast (homFormP k Γ j (p • z)) = vToLS (qToV p) * lsCast (homFormP k Γ j z) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_smul, map_add, map_add, hp, hp', map_add, map_add, add_mul]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    have hTz : homFormP k Γ j ((T n : LaurentPolynomial ℤ) • z) =
        HahnSeries.single n 1 * homFormP k Γ j z := by
      simp only [homFormP, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
      rw [LinearMap.map_smul, K0.homForm_T_smul_right]
    rw [hT, smul_assoc, map_zsmul, map_zsmul, hTz, map_zsmul, map_zsmul, vToLS_qToV_T, map_mul,
      lsCast_single, Int.cast_one, smul_mul_assoc]

attribute [local instance] qToVAlgebra

/-- **The functional `pairP j : K₀(R)_{ℚ(q)} → ℚ((q))`**, `a ⊗ z ↦ Ψ(a) · ([P_j], z_ν)`. It is
well defined on `ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` because `Ψ ∘ qToV` is the inclusion
`ℤ[q, q⁻¹] ⊆ ℚ((q))` and `( , )` is linear in its second argument. -/
def pairP {ν : Multiset I} (j : Seq ν) : K0Q k Γ →+ LaurentSeries ℚ :=
  TensorProduct.liftAddHom
    ((AddMonoidHom.mul.compl₂ (lsCast.toAddMonoidHom.comp (homFormP k Γ j))).comp
      vToLS.toAddMonoidHom)
    (fun p a z => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.mul_apply,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
      rw [lsCast_homFormP_smul, Algebra.smul_def, map_mul]
      change vToLS (qToV p) * _ * _ = _
      ring)

theorem pairP_tmul {ν : Multiset I} (j : Seq ν) (a : RatFunc ℚ) (z : (Gkl).K0R) :
    pairP k Γ j (a ⊗ₜ[LaurentPolynomial ℤ] z) = vToLS a * lsCast (homFormP k Γ j z) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem pairP_toK0Q {ν : Multiset I} (j : Seq ν) (z : (Gkl).K0R) :
    pairP k Γ j (toK0Q k Γ z) = lsCast (homFormP k Γ j z) := by
  change pairP k Γ j ((1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] z) = _
  rw [pairP_tmul, map_one, one_mul]

/-- `pairP j` is `Ψ`-semilinear over `ℚ(v)`. -/
theorem pairP_smul {ν : Multiset I} (j : Seq ν) (b : RatFunc ℚ) (t : K0Q k Γ) :
    pairP k Γ j (b • t) = vToLS b * pairP k Γ j t := by
  refine TensorProduct.induction_on (motive := fun t : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (Gkl).K0R => pairP k Γ j (b • (t : K0Q k Γ)) = vToLS b * pairP k Γ j t) t
    ?_ ?_ ?_
  · show pairP k Γ j (b • (0 : K0Q k Γ)) = _
    rw [smul_zero, map_zero, mul_zero]
  · intro a z
    change pairP k Γ j (b • a ⊗ₜ[LaurentPolynomial ℤ] z) = _
    rw [TensorProduct.smul_tmul', pairP_tmul, pairP_tmul, smul_eq_mul, map_mul, mul_assoc]
  · intro x y hx hy
    change pairP k Γ j (b • ((x : K0Q k Γ) + y)) = _
    rw [smul_add, map_add, hx, hy, map_add, mul_add]

end Pairing

/-! ### Comparison on words -/

section Comparison

omit [DecidableEq I] in
/-- The word of the sequence `Seq.ofList l` is `θ_l`. -/
theorem wordFn_ofList_lbl {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) :
    (PreF.wordFn (Seq.ofList l h).lbl : PreF (RatFunc ℚ) I) = PreF.word (FreeMonoid.ofList l) := by
  have hl : Multiset.card ν = l.length := by rw [← h, Multiset.coe_card]
  rw [PreF.wordFn, List.ofFn_congr hl]
  congr 2
  conv_rhs => rw [← List.ofFn_getElem l]
  rfl

omit [DecidableEq I] in
theorem smul_eq_iff (σ : Perm (Fin (Multiset.card ν))) (i j : Seq ν) :
    σ • i = j ↔ ∀ x, j.lbl (σ x) = i.lbl x := by
  constructor
  · rintro rfl x
    simp [Seq.smul_apply]
  · intro h
    apply Subtype.ext
    funext y
    rw [Seq.smul_apply]
    have := h (σ.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

/-- **The forms agree on words**: `([P_j], [P_i]) = Ψ((θ_i, θ_j))` for `i, j ∈ Seq ν`, where
`Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹`. This compares `KL1.homForm_projP` (KL I §2.5) with the closed
formula `PreF.form_wordFn` for Lusztig's form. -/
theorem lsCast_homForm_projP {ν : Multiset I} (i j : Seq ν) :
    lsCast (K0.homForm ((Gkl).grade ν) (K0.of ((Gkl).projP j)) (K0.of ((Gkl).projP i))) =
      vToLS ((KL.C Γ).form (PreF.wordFn i.lbl) (PreF.wordFn j.lbl)) := by
  rw [KL1.homForm_projP, CartanDatum.form, PreF.form_wordFn, map_mul, map_prod, PreF.permSum,
    map_sum, map_sum, Finset.sum_filter]
  simp_rw [vToLS_c]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hE : PreF.invWt (KL.C Γ).dot i.lbl σ =
      ∑ p ∈ invSet (Multiset.card ν) σ, cartan Γ (i.lbl p.1) (i.lbl p.2) :=
    Finset.sum_congr rfl fun p _ => cartan_symm Γ _ _
  by_cases h : σ • i = j
  · rw [if_pos h, if_pos ((smul_eq_iff σ i j).1 h), map_mul, map_pow, lsCast_single, vToLS_zpow,
      hE, Int.cast_one, mul_comm]
  · rw [if_neg h, if_neg (mt (smul_eq_iff σ i j).2 h), map_zero, mul_zero]

/-- `pairP_y (γ(θ_w)) = ([P_y], [P_w]) = Ψ((θ_w, θ_y))` for words `w`, `y`. -/
theorem pairP_gammaQ_word (w y : FreeMonoid I) :
    pairP k Γ (Seq.ofList (FreeMonoid.toList y) rfl) (gammaQ k Γ (PreF.word w)) =
      vToLS ((KL.C Γ).form (PreF.word w) (PreF.word y)) := by
  rw [gammaQ_word, pairP_toK0Q]
  by_cases h : ((FreeMonoid.toList w : List I) : Multiset I) = (FreeMonoid.toList y : Multiset I)
  · rw [clsSeq_eq k Γ _ h, homFormP_of]
    change lsCast (K0.homForm _ (K0.of ((Gkl).projP _)) (K0.of ((Gkl).projP (Seq.ofList _ h)))) = _
    rw [lsCast_homForm_projP, wordFn_ofList_lbl, wordFn_ofList_lbl, FreeMonoid.ofList_toList,
      FreeMonoid.ofList_toList]
  · rw [clsSeq, homFormP_of_ne k Γ _ _ h, map_zero, CartanDatum.form,
      PreF.form_eq_zero_of_wt_ne (a := w) (b := y) h, map_zero]

/-- `pairP_y (γ x) = Ψ((x, θ_y))` for all `x ∈ 'f` and words `y`. -/
theorem pairP_gammaQ (x : PreF (RatFunc ℚ) I) (y : FreeMonoid I) :
    pairP k Γ (Seq.ofList (FreeMonoid.toList y) rfl) (gammaQ k Γ x) =
      vToLS ((KL.C Γ).form x (PreF.word y)) := by
  induction x using PreF.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, LinearMap.add_apply, map_add]
  | smul_word w r =>
    rw [map_smul, pairP_smul, pairP_gammaQ_word, map_smul, LinearMap.smul_apply, smul_eq_mul,
      map_mul]

end Comparison

/-! ### Injectivity -/

section Injectivity

/-- **The kernel of `γ_{ℚ(q)}` on `'f` lies in the radical `ℐ` of Lusztig's form**
(unconditionally; KL I Prop. 3.4, proof). -/
theorem ker_gammaQ_le_radical {x : PreF (RatFunc ℚ) I} (hx : gammaQ k Γ x = 0) :
    x ∈ PreF.radical (KL.C Γ).dot vQ (KL.C Γ).c := by
  have hw : ∀ y : FreeMonoid I, (KL.C Γ).form x (PreF.word y) = 0 := fun y => by
    apply vToLS_injective
    rw [← pairP_gammaQ k Γ, hx, map_zero, map_zero]
  refine PreF.mem_radical.2 fun y => ?_
  induction y using PreF.induction_linear with
  | zero => rw [map_zero]
  | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  | smul_word w r =>
    have := hw w
    rw [CartanDatum.form] at this
    rw [LinearMap.map_smul, this, smul_zero]

/-- Under the Gabber–Kac hypothesis, `ker γ_{ℚ(q)} = ℐ` on `'f`. -/
theorem gammaQ_eq_zero_iff (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (x : PreF (RatFunc ℚ) I) :
    gammaQ k Γ x = 0 ↔ x ∈ PreF.radical (KL.C Γ).dot vQ (KL.C Γ).c := by
  refine ⟨ker_gammaQ_le_radical k Γ, fun hx => ?_⟩
  rw [← gammaF_π k Γ hGK, PreF.π_eq_zero_iff.2 hx, map_zero]

/-- **KL I, Proposition 3.4, over `ℚ(q)`**: `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` is injective. The
Gabber–Kac hypothesis `hGK` is used only to define `γ_{ℚ(q)}` on `f = 'f/ℐ`. -/
theorem gammaF_injective (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    Function.Injective (gammaF k Γ hGK) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := PreF.π_surjective (dot := (KL.C Γ).dot) (v := vQ) (c := (KL.C Γ).c) z
  exact PreF.π_eq_zero_iff.2 (ker_gammaQ_le_radical k Γ hz)

/-- **KL I, Proposition 3.4**: the integral `γ : _𝒜 f → K₀(R)` (with values in the image of
`K₀(R)` in `K₀(R)_{ℚ(q)}`) is injective. -/
theorem gammaA_injective (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    Function.Injective (gammaA k Γ hGK) := fun _ _ h =>
  Subtype.ext (gammaF_injective k Γ hGK (congrArg Subtype.val h))

/-- **KL I, Proposition 3.4**: `γ : _𝒜 f → K₀(R)` is injective (where `gammaInt` is defined,
i.e. when `K₀(R) → K₀(R)_{ℚ(q)}` is injective). -/
theorem gammaInt_injective (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ)) :
    Function.Injective (gammaInt k Γ hGK hinj) := fun _ _ h =>
  gammaA_injective k Γ hGK ((K0RrangeEquiv k Γ hinj).symm.injective h)

end Injectivity

end Categorification.KLR.KLGamma

end
