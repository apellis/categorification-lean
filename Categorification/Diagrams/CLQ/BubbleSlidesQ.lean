/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.BubbleSlidesAll
import Categorification.Diagrams.CLQ.Rewriting
import Categorification.Diagrams.KL3.BubbleSlidesGen

/-!
# Bubble slides for distinct colours with Cautis–Lauda scalars

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Propositions 3.3 and 3.4, for the Cautis–Lauda scalars (S. Cautis, A. Lauda, *Implicit structure
in 2-representations of quantum groups*, arXiv:1111.1431v3, §2.1): the polynomial of the double
crossing of upward strands is `Q_ij = t_ij u^{d_ij} + t_ji v^{d_ji} + ∑ s_ij^{pq} u^p v^q`, and
the identities `crossr ∘ crossl`, `crossl ∘ crossr` carry the scalars `t_ji`, `t_ij`.

As in `Categorification.Diagrams.KL3.BubbleSlidesGen`, the slides in all degrees are the
generating function identities `C_R = C_L τ` and `W_L = τ W_R`, now with
`τ = t_ij⁻¹ ∑_s c_s x_j^{s_1} t^{d_ij - s_0}`, the sum over the monomials `u^{s_0} v^{s_1}` of `Q_ij`
with coefficients `c_s` (`τQ`). Weighted homogeneity of `Q_ij` gives `s_0 ≤ d_ij`, with
`s_1 = 0` if `s_0 = d_ij`, and the coefficient of `u^{d_ij}` is `t_ij`; so `τ_0 = 1`. The case
`i · j = 0` is included (`Q_ij = t_ij`, `τ = 1`).

## Main results

* `dg_cross_dots_cross_sum`: `ψ_ji x_i^m ψ_ij = ∑_s c_s x_i^{m + s_0} x_j^{s_1}` on `E_i E_j`.
* `slideA_real`, `slideB_real`: the slides of real bubbles.
* `slidesQ`: the bubble slides in all degrees.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## The monomials of `Q_ij` -/

section Poly

variable {k}

theorem ncEval_two_eq_sum {A : Type*} [Ring A] [Algebra k A] (y : Fin 2 → A)
    (p : MvPolynomial (Fin 2) k) :
    KLR.ncEval y p = ∑ s ∈ p.support, p.coeff s • (y 0 ^ s 0 * y 1 ^ s 1) := by
  unfold KLR.ncEval
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [List.ofFn_succ, Algebra.smul_def]

variable {sc}

/-- The monomials `u^{s_0} v^{s_1}` of `Q_ij` have `s_0 ≤ d_ij`, and `s_1 = 0` if `s_0 = d_ij`
(weighted homogeneity). -/
theorem qCL_support {i j : I} (h : i ≠ j) {s : Fin 2 →₀ ℕ} (hs : s ∈ (CL.qCL sc i j).support) :
    s 0 ≤ C.dij i j ∧ (s 0 = C.dij i j → s 1 = 0) := by
  have hw := CL.qCL_isWeightedHomogeneous sc h (MvPolynomial.mem_support_iff.mp hs)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hw
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul] at hw
  have h1 := C.dij_mul h
  have hi := C.dot_self_pos i
  have hj := C.dot_self_pos j
  have hs1 : (0 : ℤ) ≤ (s 1 : ℤ) * C.dot j j := by positivity
  constructor
  · by_contra hc
    push Not at hc
    have : ((C.dij i j : ℤ) + 1) * C.dot i i ≤ (s 0 : ℤ) * C.dot i i :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hi.le
    nlinarith
  · intro he
    rw [he] at hw
    have : (s 1 : ℤ) * C.dot j j = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact_mod_cast h'
    · omega

/-- The coefficient of `u^{d_ij}` in `Q_ij` is `t_ij`. -/
theorem qCL_coeff_top {i j : I} (h : i ≠ j) :
    (CL.qCL sc i j).coeff (Finsupp.single 0 (C.dij i j)) = (sc.t i j : k) := by
  by_cases h0 : C.dot i j = 0
  · have hd : C.dij i j = 0 := (C.dij_eq_zero_iff h).2 h0
    rw [CL.qCL_of_dot_eq_zero sc h0, hd, Finsupp.single_zero, MvPolynomial.coeff_C,
      ite_eq_left rfl]
  · have hd := dij_pos h h0
    have hd' := dij_pos (Ne.symm h) (by rwa [C.symm])
    have hne : Finsupp.single (1 : Fin 2) (C.dij j i) ≠ Finsupp.single 0 (C.dij i j) := by
      intro he
      have := congrArg (· 0) he
      simp at this
      omega
    have hsum : ∀ p ∈ Finset.range (C.dij i j), ∀ q : ℕ,
        Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q ≠ Finsupp.single 0 (C.dij i j) := by
      intro p hp q he
      have := congrArg (· 0) he
      simp at this
      have := Finset.mem_range.1 hp
      omega
    rw [CL.qCL_of_dot_ne_zero sc h0]
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
      MvPolynomial.monomial_mul_monomial, mul_one]
    simp [MvPolynomial.coeff_monomial, hne]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => ?_
    split_ifs <;> simp [MvPolynomial.coeff_monomial, hsum p hp q]

end Poly

/-! ## The double crossing of upward strands -/

/-- `eq_r2_ij-gen` as a sum over the monomials of `Q_cd`. -/
theorem dg_sqNe_sum (μ : X) (c d : I) (h : c ≠ d) :
    dg RD k sc μ [up c, up d] [up c, up d] [([], .cross true c d, []), ([], .cross true d c, [])] =
      ∑ s ∈ (CL.qCL sc c d).support, (CL.qCL sc c d).coeff s •
        dg RD k sc μ [up c, up d] [up c, up d]
          (List.replicate (s 0) ([], .dot (up c), [up d]) ++
            List.replicate (s 1) ([up c], .dot (up d), [])) := by
  rw [dg_sqNe RD k sc μ c d h, ncEval_two_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dgE_pow_single RD k sc μ _ _ (by schain), dgE_pow_single RD k sc μ _ _ (by schain),
    End.mul_def, dgE, dgE, dg_comp (by schain) (by schain)]
  exact dg_swap_dots RD k sc μ [] [] [] (up c) (up d) _ _

/-- The upward computation in the `i ≠ j` bubble slide: a crossing `E_i E_j ⟶ E_j E_i`, `m`
dots on the `i` strand, and the crossing back equal `x_i^m Q_ij(x_i, x_j)`. -/
theorem dg_cross_dots_cross_sum (ν : X) (i j : I) (h : i ≠ j) (m : ℕ) :
    dg RD k sc ν [up i, up j] [up i, up j]
        ([([], .cross true i j, [])] ++ List.replicate m ([up j], .dot (up i), []) ++
          [([], .cross true j i, [])]) =
      ∑ s ∈ (CL.qCL sc i j).support, (CL.qCL sc i j).coeff s •
        dg RD k sc ν [up i, up j] [up i, up j]
          (List.replicate (m + s 0) ([], .dot (up i), [up j]) ++
            List.replicate (s 1) ([up i], .dot (up j), [])) := by
  refine (dg_step RD k sc ν [] [([], .cross true j i, [])] [] [] (dg_slide_rep RD k sc ν i j h m)
    (by schain) (by schain) (by simp [whL]) rfl).trans ?_
  refine (dg_stepL RD k sc ν (List.replicate m ([], .dot (up i), [up j])) [] [] []
    (dg_sqNe_sum RD k sc ν i j h) (by schain) (by schain) (by simp [whL])).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, ctxL_dg_nil RD k sc ν (by schain) (by schain)]
  simp only [whL, List.map_replicate, List.map_append, List.nil_append, List.append_nil,
    List.replicate_add, List.append_assoc]

end Categorification.KL3.Diagram.CLQ
