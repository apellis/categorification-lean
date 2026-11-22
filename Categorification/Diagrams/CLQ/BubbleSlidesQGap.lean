/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.BubbleSlidesQ

/-!
# Bubble slides in all degrees with Cautis–Lauda scalars

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Propositions 3.3 and 3.4, for the Cautis–Lauda scalars (S. Cautis, A. Lauda, arXiv:1111.1431v3,
§2.1), in all degrees.

As in `Categorification.Diagrams.KL3.BubbleSlidesGen`, the case `0 < ⟨i, λ⟩ < d_ij`, where
neither family of bubbles is real, follows J. Brundan, A. Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, proof of Proposition 7.3(iii): the deformed braid relation on `E_i E_j E_i`
(KL III `eq_r3_hard-gen`, now with correction term `∑_s c_s ∑_{t < s_0} x₀^t x₁^{s_1} x₂^{s_0-1-t}`)
is closed up around an upward `j`-strand.

## Main results

* `dg_braidQ_sum`: the braid relation with correction on `E_c E_d E_c` for `c ≠ d`.
* `closeSumQ`: its closure around an upward `j`-strand.
* `mixedGrassQ`: the mixed Grassmannian relation in degrees `1, …, d_ij - ⟨i, λ⟩`.
* `slidesQ`: the bubble slides `C_R = C_L τ`, `W_L = τ W_R` in all degrees, for
  `τ = t_ij⁻¹ ∑_s c_s x_j^{s_1} t^{d_ij - s_0}` (`τQ`, with `τQ_zero`: `τ_0 = 1`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

theorem ncEval_C_X1_X0_X2 {A : Type*} [Ring A] [Algebra k A] (y : Fin 3 → A) (c : k)
    (b p q : ℕ) :
    KLR.ncEval y (MvPolynomial.C c * MvPolynomial.X 1 ^ b *
        (MvPolynomial.X 0 ^ p * MvPolynomial.X 2 ^ q) : MvPolynomial (Fin 3) k) =
      c • (y 0 ^ p * y 1 ^ b * y 2 ^ q) := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial, ncEval_monomial_aux, Algebra.smul_def]
  simp [List.ofFn_succ, Finsupp.single_apply, mul_assoc]

/-- **KL III `eq_r3_hard-gen`** for `c ≠ d` with the Cautis–Lauda polynomial `Q_cd`: on
`E_c E_d E_c`, `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁ + ∑_s c_s ∑_{t < s_0} x₀^t x₂^{s_0 - 1 - t} x₁^{s_1}`
(normal form, bottom to top), the sum over the monomials `u^{s_0} v^{s_1}` of `Q_cd`. -/
theorem dg_braidQ_sum (μ : X) (c d : I) (h : c ≠ d) :
    NF.dg (pres RD k sc) μ [up c, up d, up c] [up c, up d, up c]
        [([], .cross true c d, [up c]), ([up d], .cross true c c, []),
          ([], .cross true d c, [up c])] =
      NF.dg (pres RD k sc) μ [up c, up d, up c] [up c, up d, up c]
        [([up c], .cross true d c, []), ([], .cross true c c, [up d]),
          ([up c], .cross true c d, [])] +
      ∑ s ∈ (CL.qCL sc c d).support, (CL.qCL sc c d).coeff s •
        ∑ t ∈ Finset.range (s 0),
          NF.dg (pres RD k sc) μ [up c, up d, up c] [up c, up d, up c]
            (List.replicate t ([], .dot (up c), [up d, up c]) ++
              List.replicate (s 0 - 1 - t) ([up c, up d], .dot (up c), []) ++
              List.replicate (s 1) ([up c], .dot (up d), [up c])) := by
  have key := KLR.Diagram.braidQ_at (CL.qCL sc) (u := []) (v := []) h
    (KLR.Diagram.braidL c d c) (KLR.Diagram.braidR c d c) (KLR.Diagram.E0 c d c)
    (KLR.Diagram.E1 c d c) (KLR.Diagram.E2 c d c) rfl rfl rfl rfl rfl
  have key' := congrArg (functorEndAlg k (upFunctor RD k sc μ) _) key
  rw [map_sub, AlgHom.map_ncEval] at key'
  simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    upFunctor_diag, upDiag_eq_dg] at key'
  rw [← sub_eq_iff_eq_add']
  refine Eq.trans ?_ (key'.trans ?_)
  · rfl
  rw [KLR.qbar, Finsupp.sum, ncEval_sum_aux]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, ncEval_sum_aux, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ncEval_C_X1_X0_X2]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, upFunctor_diag, upDiag_eq_dg]
  change (NF.dgE (pres RD k sc) μ [up c, up d, up c] [([], .dot (up c), [up d, up c])]) ^ t *
      (NF.dgE (pres RD k sc) μ [up c, up d, up c] [([up c], .dot (up d), [up c])]) ^ s 1 *
      (NF.dgE (pres RD k sc) μ [up c, up d, up c] [([up c, up d], .dot (up c), [])]) ^ (s 0 - 1 - t) = _
  rw [NF.dgE_pow_single (pres RD k sc) μ _ _ (by schain), NF.dgE_pow_single (pres RD k sc) μ _ _ (by schain),
    NF.dgE_pow_single (pres RD k sc) μ _ _ (by schain), End.mul_def, End.mul_def, NF.dgE, NF.dgE, NF.dgE,
    NF.dg_comp (by schain) (by schain), NF.dg_comp (by schain) (by schain)]
  dstepQ (List.replicate (s 0 - 1 - t) ([up c, up d], .dot (up c), [])) [] [] []
    (NF.dg_swap_dots (pres RD k sc) μ [] [] [up c] (up c) (up d) (s 1) t)
  dstepQ [] (List.replicate (s 1) ([up c], .dot (up d), [up c])) [] []
    (NF.dg_swap_dots (pres RD k sc) μ [] [up d] [] (up c) (up c) (s 0 - 1 - t) t)
  simp [whL]

section Closure

variable (lam : X) (i j : I)

/-- The right curl on an upward `i`-strand in the region `λ` vanishes when `⟨i, λ⟩ ≥ 1` (KL III,
Definition 3.1, item iv), the sum being empty). -/
theorem dg_curlR_eq_zero (h1 : 1 ≤ ip RD i lam) :
    NF.dg (pres RD k sc) lam [up i] [up i]
        [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] = 0 := by
  rw [dg_curlR, show (-ip RD i lam + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero]

/-- The top part of the closure of `ψ₀ψ₁ψ₀` (strands `i, j, i`) around an upward `j`-strand
contains a right curl in the region `λ`, hence vanishes for `⟨i, λ⟩ ≥ 1`. -/
theorem closeBL_tail (h1 : 1 ≤ ip RD i lam) :
    NF.dg (pres RD k sc) lam [dn i, up i, up j] [up j]
      [([dn i, up i, up j], .cup (up i), []), ([dn i], .cross true i j, [up i, dn i]),
        ([dn i, up j], .cross true i i, [dn i]), ([dn i], .cross true j i, [up i, dn i]),
        ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])] = 0 := by
  dswapQ 0
  dswapQ 3
  rw [NF.dg_stepL_at _ 1 [dn i, up j] [] (dg_curlR_eq_zero RD k sc lam i h1) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm), map_zero]

/-- The left curl with `N` dots on its loop (below the crossing) in the outer region `ν + i_X`
vanishes when `N + ⟨i, ν + i_X⟩ + 1 ≤ 0` (`ptrL_nhDotL_nhCross`: the sum is empty). -/
theorem dg_curlL_dots_eq_zero (ν : X) (N : ℕ) (hN : (N : ℤ) + ip RD i (wt RD ν [up i]) + 1 ≤ 0) :
    NF.dg (pres RD k sc) ν [up i] [up i]
      ([([], .cup (dn i), [up i])] ++ List.replicate N ([dn i], .dot (up i), [up i]) ++
        [([dn i], .cross true i i, []), ([], .cap (up i), [up i])]) = 0 := by
  have e := ptrL_dg RD k sc ν i (List.replicate N ([], .dot (up i), [up i]) ++
    [([], .cross true i i, [])])
  rw [← NF.dg_comp (t := [up i, up i]) (by schain) (by schain)] at e
  change ptrL RD k sc ν i (nhDotL RD k sc ν i N ≫ nhCross RD k sc ν i) = _ at e
  rw [ptrL_nhDotL_nhCross, show ((N : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat = 0 by omega,
    Finset.sum_range_zero] at e
  refine Eq.trans ?_ e.symm
  congr 1
  lnf


/-- The closure of `ψ₁ψ₀ψ₁` (strands `i, j, i`, `N` dots on the first strand below it) around an
upward `j`-strand contains a left curl with `N` dots in the region `λ + j_X`, hence vanishes for
`N + ⟨i, λ + j_X⟩ + 1 ≤ 0`. -/
theorem closeBR_eq_zero (N : ℕ) (hN : (N : ℤ) + ip RD i (wt RD lam [up j]) + 1 ≤ 0) :
    NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), []), ([dn i, up i], .cross true j i, [dn i]),
          ([dn i], .cross true i i, [up j, dn i]), ([dn i, up i], .cross true i j, [dn i]),
          ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]) = 0 := by
  have e₁ := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := [up j]) (T := [up j]) []
    [([dn i], .cross true i i, [up j, dn i]), ([dn i, up i], .cross true i j, [dn i]),
      ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]
    (s := []) (s' := [dn i, up i]) (t := [up j]) (t' := [up i, up j, dn i])
    (A := [([], .cup (dn i), [])] ++ List.replicate N ([dn i], .dot (up i), []))
    (B := [([up j], .cup (up i), []), ([], .cross true j i, [dn i])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil, List.map_replicate,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₁ ⊢
  rw [e₁]
  have e₂ := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := [up j]) (T := [up j])
    ([([up j], .cup (up i), []), ([], .cross true j i, [dn i]),
      ([], .cup (dn i), [up i, up j, dn i])] ++
      List.replicate N ([dn i], .dot (up i), [up i, up j, dn i]) ++
      [([dn i], .cross true i i, [up j, dn i])]) []
    (s := [dn i, up i]) (s' := []) (t := [up i, up j, dn i]) (t' := [up j])
    (A := [([], .cap (up i), [])])
    (B := [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₂ ⊢
  rw [← e₂]
  have hz := dg_curlL_dots_eq_zero RD k sc i (wt RD lam [up j, dn i]) N (by
    rw [show wt RD (wt RD lam [up j, dn i]) [up i] = wt RD lam [up i, up j, dn i] by
      simp, ip_wt_up_up_dn]; exact hN)
  rw [NF.dg_stepL (pres RD k sc) lam [([up j], .cup (up i), []), ([], .cross true j i, [dn i])]
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] [up j, dn i] hz
    (by schain) (by schain) (by lnf), map_zero]

/-- The closure of the correction term `x₀^t x₂^s` (with `N` further dots on the first strand)
around an upward `j`-strand: a counterclockwise bubble with `N + t` dots to the left of the strand
and a clockwise bubble with `s` dots to its right. -/
theorem closeCorr (N t s : ℕ) :
    NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        List.replicate t ([dn i], .dot (up i), [up j, up i, dn i]) ++
        List.replicate s ([dn i, up i, up j], .dot (up i), [dn i]) ++
        [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]) =
      NF.bubLU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) (wt RD lam [up j]) i ((N + t : ℕ) : ℤ)) ≫
        NF.bubRU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) lam i (s : ℤ)) := by
  have e₁ := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := [up j]) (T := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]))
    (List.replicate s ([dn i, up i, up j], .dot (up i), [dn i]) ++
      [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])])
    (s := [dn i, up i]) (s' := [dn i, up i]) (t := [up j]) (t' := [up j, up i, dn i])
    (A := List.replicate t ([dn i], .dot (up i), []))
    (B := [([up j], .cup (up i), [])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil, List.map_replicate,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₁ ⊢
  rw [← e₁]
  have e₂ := NF.dg_interchange (P := pres RD k sc) (μ := lam) (S := [up j]) (T := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
      List.replicate t ([dn i], .dot (up i), [up j])) []
    (s := [dn i, up i]) (s' := []) (t := [up j]) (t' := [up j])
    (A := [([], .cap (up i), [])])
    (B := [([up j], .cup (up i), [])] ++ List.replicate s ([up j], .dot (up i), [dn i]) ++
      [([up j], .cap (dn i), [])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil, List.map_replicate, List.map_append,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₂ ⊢
  rw [← e₂, NF.ccwU_of_nonneg, NF.cwU_of_nonneg, NF.bubLU, NF.bubRU, NF.plcL_dg, NF.plcL_dg_nil]
  change _ = NF.dg (pres RD k sc) lam [up j] [up j] _ ≫ NF.dg (pres RD k sc) lam [up j] [up j] _
  rw [NF.dg_comp (by unfold ccwLs; schain) (by unfold cwLs; schain)]
  symm
  unfold cwLs
  dstepQ ((ccwLs i (N + t)).map (whL [] [up j])) [] [up j] [] (dg_cw_dots RD k sc lam i s)
  simp only [ccwLs, whL, List.map_cons, List.map_nil, List.map_replicate, List.map_append,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.replicate_add]

/-- `closeCorr` with `b` dots on the upward `j`-strand inside the closure: they leave through the
caps and sit on the strand above both bubbles. -/
theorem closeCorrQ (N t s b : ℕ) :
    NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        List.replicate t ([dn i], .dot (up i), [up j, up i, dn i]) ++
        List.replicate s ([dn i, up i, up j], .dot (up i), [dn i]) ++
        List.replicate b ([dn i, up i], .dot (up j), [up i, dn i]) ++
        [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]) =
      NF.bubLU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) (wt RD lam [up j]) i ((N + t : ℕ) : ℤ)) ≫
        NF.bubRU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) lam i (s : ℤ)) ≫ NF.dotsU (pres RD k sc) lam (up j) b := by
  dstepQ ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        List.replicate t ([dn i], .dot (up i), [up j, up i, dn i]) ++
        List.replicate s ([dn i, up i, up j], .dot (up i), [dn i])) [([], .cap (up i), [up j])] [] []
    (NF.dg_swap_rep' (pres RD k sc) lam [dn i, up i] [] [] (.cap (dn i)) (.dot (up j)) rfl b)
  dstepQ ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        List.replicate t ([dn i], .dot (up i), [up j, up i, dn i]) ++
        List.replicate s ([dn i, up i, up j], .dot (up i), [dn i]) ++
        [([dn i, up i, up j], .cap (dn i), [])]) [] [] []
    (NF.dg_swap_rep (pres RD k sc) lam [] [] [] (.cap (up i)) (.dot (up j)) rfl b)
  rw [← Category.assoc, ← closeCorr, NF.dotsU, NF.dg_comp (by schain) (by schain)]
  simp [Shape.dom, Shape.cod]

/-- **The closed deformed braid relation for `Q_ij`** (J. Brundan, A. Ellis, arXiv:1701.04133v2,
proof of Proposition 7.3(iii), for general Cautis–Lauda scalars): for `i ≠ j`, `⟨i, λ⟩ ≥ 1` and
`N + ⟨i, λ + j_X⟩ + 1 ≤ 0`, closing `dg_braidQ_sum` on the strands `i, j, i` around the upward
`j`-strand gives `∑_s c_s ∑_{t < s_0} ccw_{N+t} ⊗ E_j ⊗ cw_{s_0-1-t} · x_j^{s_1} = 0`, the sum
over the monomials `c_s u^{s_0} v^{s_1}` of `Q_ij`. -/
theorem closeSumQ (hij : i ≠ j) (h1 : 1 ≤ ip RD i lam) (N : ℕ)
    (hN : (N : ℤ) + ip RD i (wt RD lam [up j]) + 1 ≤ 0) :
    ∑ s ∈ (CL.qCL sc i j).support, (CL.qCL sc i j).coeff s •
      ∑ t ∈ Finset.range (s 0),
        NF.bubLU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) (wt RD lam [up j]) i ((N + t : ℕ) : ℤ)) ≫
          NF.bubRU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) lam i ((s 0 - 1 - t : ℕ) : ℤ)) ≫
            NF.dotsU (pres RD k sc) lam (up j) (s 1) = 0 := by
  have hD1 : NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        [([], .cross true i j, [up i]), ([up j], .cross true i i, []),
          ([], .cross true j i, [up i])].map (whL [dn i] [dn i]) ++
        [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]) = 0 := by
    rw [show [([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        [([], .cross true i j, [up i]), ([up j], .cross true i i, []),
          ([], .cross true j i, [up i])].map (whL [dn i] [dn i]) ++
        [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])] =
        ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j])) ++
        [([dn i, up i, up j], .cup (up i), []), ([dn i], .cross true i j, [up i, dn i]),
          ([dn i, up j], .cross true i i, [dn i]), ([dn i], .cross true j i, [up i, dn i]),
          ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])] by simp [whL],
      ← NF.dg_comp (t := [dn i, up i, up j]) (by schain) (by schain), closeBL_tail RD k sc lam i j h1,
      Limits.comp_zero]
  have key := NF.dg_stepL (pres RD k sc) lam (s₀ := [up j]) (t₀ := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
      [([dn i, up i, up j], .cup (up i), [])])
    [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])] [dn i] [dn i]
    (dg_braidQ_sum RD k sc (wt RD lam [dn i]) i j hij) (by schain) (by schain) rfl
  rw [hD1, map_add, map_sum, NF.ctxL_dg (pres RD k sc) lam (by schain) (by schain)] at key
  have hD2 := closeBR_eq_zero RD k sc lam i j N hN
  simp only [whL, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at key hD2
  rw [hD2, zero_add] at key
  refine Eq.trans ?_ key.symm
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [NF.ctxL_dg (pres RD k sc) lam (by schain) (by schain), ← closeCorrQ RD k sc lam i j N t (s 0 - 1 - t)]
  simp only [whL, List.map_replicate, List.map_append,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

end Closure

/-! ## Convolution with the coefficients of `Q_ij` -/

section ConvQ

variable {A : Type*} [Ring A] [Algebra k A]

theorem sum_range_ite_right (s0 d α : ℕ) (hs : s0 ≤ d) (f : ℕ → A) :
    ∑ a ∈ Finset.range (α + 1), (if s0 + (α - a) = d then f a else 0) =
      if d ≤ α + s0 then f (α + s0 - d) else 0 := by
  by_cases hd : d ≤ α + s0
  · rw [ite_eq_left hd]
    rw [Finset.sum_congr rfl (g := fun a => if a = α + s0 - d then f a else 0) fun a ha => by
      have := Finset.mem_range.1 ha
      exact if_congr (by omega) rfl rfl]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  · rw [ite_eq_right hd]
    exact Finset.sum_eq_zero fun a ha => ite_eq_right (by omega)

theorem sum_range_ite_left (s0 d β : ℕ) (hs : s0 ≤ d) (f : ℕ → A) :
    ∑ a ∈ Finset.range (β + 1), (if s0 + a = d then f (β - a) else 0) =
      if d ≤ β + s0 then f (β + s0 - d) else 0 := by
  by_cases hd : d ≤ β + s0
  · rw [ite_eq_left hd]
    rw [Finset.sum_congr rfl (g := fun a => if a = d - s0 then f (β + s0 - d) else 0) fun a ha => by
      have := Finset.mem_range.1 ha
      by_cases h : a = d - s0
      · rw [ite_eq_left (by omega), ite_eq_left h, show β - a = β + s0 - d by omega]
      · rw [ite_eq_right (by omega), ite_eq_right h]]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  · rw [ite_eq_right hd]
    exact Finset.sum_eq_zero fun a ha => ite_eq_right (by have := Finset.mem_range.1 ha; omega)

/-- Convolution on the right with the series whose coefficient of `t^e` is
`r ∑_{s ∈ P, s_0 + e = d} c_s D_{s_1}`. -/
theorem sconv_coeffSeries_right (u : ℕ → A) (P : Finset (Fin 2 →₀ ℕ)) (c : (Fin 2 →₀ ℕ) → k)
    (D : ℕ → A) (d : ℕ) (hP : ∀ s ∈ P, s 0 ≤ d) (r : k) (α : ℕ) :
    sconv u (fun e => r • ∑ s ∈ P.filter (fun s => s 0 + e = d), c s • D (s 1)) α =
      r • ∑ s ∈ P, c s • (if d ≤ α + s 0 then u (α + s 0 - d) * D (s 1) else 0) := by
  simp only [sconv, Finset.sum_filter, mul_smul_comm, Finset.mul_sum, mul_ite, mul_zero,
    ← Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← sum_range_ite_right (s 0) d α (hP s hs) (fun a => u a * D (s 1)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- Convolution on the left with the same series. -/
theorem sconv_coeffSeries_left (w : ℕ → A) (P : Finset (Fin 2 →₀ ℕ)) (c : (Fin 2 →₀ ℕ) → k)
    (D : ℕ → A) (d : ℕ) (hP : ∀ s ∈ P, s 0 ≤ d) (r : k) (β : ℕ) :
    sconv (fun e => r • ∑ s ∈ P.filter (fun s => s 0 + e = d), c s • D (s 1)) w β =
      r • ∑ s ∈ P, c s • (if d ≤ β + s 0 then D (s 1) * w (β + s 0 - d) else 0) := by
  simp only [sconv, Finset.sum_filter, smul_mul_assoc, Finset.sum_mul, ite_mul, zero_mul,
    ← Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← sum_range_ite_left (s 0) d β (hP s hs) (fun a => D (s 1) * w a), Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- Convolution is commutative when the coefficients of the two series commute. -/
theorem sconv_comm_of_commute (u w : ℕ → A) (h : ∀ a b, Commute (u a) (w b)) (n : ℕ) :
    sconv u w n = sconv w u n := by
  rw [sconv, sconv, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun a ha => ?_
  have := Finset.mem_range.1 ha
  rw [(h _ _).eq, show n - (n + 1 - 1 - a) = a by omega, show n + 1 - 1 - a = n - a by omega]

end ConvQ

/-! ## Bubble slides in all degrees -/

section GenQ

variable (lam : X) (i j : I)

/-- The coefficients of `τ = t_ij⁻¹ ∑_s c_s x_j^{s_1} t^{d_ij - s_0}`, the sum over the monomials
`c_s u^{s_0} v^{s_1}` of `Q_ij` (dots on the strand `j`). -/
abbrev τQ (e : ℕ) : End ((pres RD k sc).obj (ob RD lam [up j])) :=
  (↑(sc.t i j)⁻¹ : k) • ∑ s ∈ (CL.qCL sc i j).support.filter (fun s => s 0 + e = C.dij i j),
    (CL.qCL sc i j).coeff s • NF.dotsU (pres RD k sc) lam (up j) (s 1)

variable {i j}

theorem τQ_zero (hij : i ≠ j) : τQ RD k sc lam i j 0 = 1 := by
  rw [τQ]
  have hsub : (CL.qCL sc i j).support.filter (fun s => s 0 + 0 = C.dij i j) ⊆
      {Finsupp.single 0 (C.dij i j)} := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have h1 := (qCL_support hij hs.1).2 (by omega)
    rw [Finset.mem_singleton]
    ext x
    fin_cases x
    · simp; omega
    · simpa using h1
  rw [Finset.sum_subset hsub fun s hs hs' => by
    rw [Finset.mem_singleton] at hs
    subst hs
    have : Finsupp.single (0 : Fin 2) (C.dij i j) ∉ (CL.qCL sc i j).support := by
      intro hm; exact hs' (Finset.mem_filter.2 ⟨hm, by simp⟩)
    rw [MvPolynomial.notMem_support_iff.1 this, zero_smul]]
  rw [Finset.sum_singleton, qCL_coeff_top hij, smul_smul, Units.inv_mul, one_smul]
  simp [NF.dotsU_zero]

theorem qCL_support_le (hij : i ≠ j) : ∀ s ∈ (CL.qCL sc i j).support, s 0 ≤ C.dij i j :=
  fun _ hs => (qCL_support hij hs).1

theorem sconv_cLs_τQ (hij : i ≠ j) (α : ℕ) :
    sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) α =
      (↑(sc.t i j)⁻¹ : k) • ∑ s ∈ (CL.qCL sc i j).support, (CL.qCL sc i j).coeff s •
        (if C.dij i j ≤ α + s 0 then
          cLs RD k sc lam i (up j) (α + s 0 - C.dij i j) * NF.dotsU (pres RD k sc) lam (up j) (s 1) else 0) :=
  sconv_coeffSeries_right k _ _ _ _ _ (qCL_support_le k sc hij) _ α

theorem sconv_τQ_wRs (hij : i ≠ j) (β : ℕ) :
    sconv (τQ RD k sc lam i j) (wRs RD k sc lam i (up j)) β =
      (↑(sc.t i j)⁻¹ : k) • ∑ s ∈ (CL.qCL sc i j).support, (CL.qCL sc i j).coeff s •
        (if C.dij i j ≤ β + s 0 then
          NF.dotsU (pres RD k sc) lam (up j) (s 1) * wRs RD k sc lam i (up j) (β + s 0 - C.dij i j) else 0) :=
  sconv_coeffSeries_left k _ _ _ _ _ (qCL_support_le k sc hij) _ β

theorem bubRU_ccwU (m : ℕ) :
    NF.bubRU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) lam i m) = NF.dg (pres RD k sc) lam [up j] [up j]
      ([([up j], .cup (dn i), [])] ++ List.replicate m ([up j, dn i], .dot (up i), []) ++
        [([up j], .cap (up i), [])]) := by
  rw [NF.ccwU_of_nonneg, NF.bubRU, NF.plcL_dg_nil]
  simp [ccwLs, whL]

theorem bubLU_ccwU (m : ℕ) :
    NF.bubLU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) (wt RD lam [up j]) i m) = NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate m ([dn i], .dot (up i), [up j]) ++
        [([], .cap (up i), [up j])]) := by
  rw [NF.ccwU_of_nonneg, NF.bubLU, NF.plcL_dg]
  simp [ccwLs, whL]

theorem bubLU_cwU (m : ℕ) :
    NF.bubLU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) (wt RD lam [up j]) i m) = NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (up i), [up j])] ++ List.replicate m ([up i], .dot (dn i), [up j]) ++
        [([], .cap (dn i), [up j])]) := by
  rw [NF.cwU_of_nonneg, NF.bubLU, NF.plcL_dg]
  simp [cwLs, whL]

theorem bubRU_cwU (m : ℕ) :
    NF.bubRU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) lam i m) = NF.dg (pres RD k sc) lam [up j] [up j]
      ([([up j], .cup (up i), [])] ++ List.replicate m ([up j, up i], .dot (dn i), []) ++
        [([up j], .cap (dn i), [])]) := by
  rw [NF.cwU_of_nonneg, NF.bubRU, NF.plcL_dg_nil]
  simp [cwLs, whL]

theorem slideAQ_real (hij : i ≠ j) (α : ℕ) (hα : 0 ≤ -ip RD i lam - 1 + α) :
    cRs RD k sc lam i (up j) α = sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) α := by
  have hw := ip_wt_up_ne RD hij lam
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -ip RD i lam - 1 + α := ⟨_, Int.toNat_of_nonneg hα⟩
  have h := dg_ccw_slide_sum RD k sc lam i j hij m
  rw [sconv_cLs_τQ RD k sc lam hij, cRs, ← hm, bubRU_ccwU,
    ← one_smul k (NF.dg (pres RD k sc) lam [up j] [up j] _), ← Units.inv_mul (sc.t i j), mul_smul, h]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  have e : NF.dg (pres RD k sc) lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate (m + s 0) ([dn i], .dot (up i), [up j]) ++
        [([], .cap (up i), [up j])] ++ List.replicate (s 1) ([], .dot (up j), [])) =
      NF.bubLU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) (wt RD lam [up j]) i ((m + s 0 : ℕ) : ℤ)) ≫
        NF.dotsU (pres RD k sc) lam (up j) (s 1) := by
    rw [bubLU_ccwU, NF.dotsU, NF.dg_comp (by schain) (by schain)]
  rw [e]
  split_ifs with hs
  · rw [End.mul_def, cLs, ← NF.bubLU_comm]
    congr 3
    push_cast [Nat.cast_sub hs]
    omega
  · rw [ccwU_eq_zero RD k sc _ i _ (by push_cast; omega), bubLU_zero, Limits.zero_comp]

theorem slideBQ_real (hij : i ≠ j) (β : ℕ) (hβ : 0 ≤ ip RD i (wt RD lam [up j]) - 1 + β) :
    wLs RD k sc lam i (up j) β = sconv (τQ RD k sc lam i j) (wRs RD k sc lam i (up j)) β := by
  have hw := ip_wt_up_ne RD hij lam
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = ip RD i (wt RD lam [up j]) - 1 + β :=
    ⟨_, Int.toNat_of_nonneg hβ⟩
  have h := dg_cw_slide_sum RD k sc lam i j hij m
  rw [sconv_τQ_wRs RD k sc lam hij, wLs, ← hm, bubLU_cwU,
    ← one_smul k (NF.dg (pres RD k sc) lam [up j] [up j] _), ← Units.inv_mul (sc.t i j), mul_smul, h]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  have e : NF.dg (pres RD k sc) lam [up j] [up j]
      ([([up j], .cup (up i), [])] ++ List.replicate (m + s 0) ([up j, up i], .dot (dn i), []) ++
        [([up j], .cap (dn i), [])] ++ List.replicate (s 1) ([], .dot (up j), [])) =
      NF.bubRU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) lam i ((m + s 0 : ℕ) : ℤ)) ≫
        NF.dotsU (pres RD k sc) lam (up j) (s 1) := by
    rw [bubRU_cwU, NF.dotsU, NF.dg_comp (by schain) (by schain)]
  rw [e]
  split_ifs with hs
  · rw [End.mul_def, wRs]
    congr 3
    push_cast [Nat.cast_sub hs]
    omega
  · rw [cwU_eq_zero RD k sc _ i _ (by push_cast; omega), bubRU_zero, Limits.zero_comp]

/-- **The mixed Grassmannian relation in low degrees for `Q_ij`** (Brundan–Ellis,
arXiv:1701.04133v2, proof of Proposition 7.3(iii)): for `i ≠ j`, `h = ⟨i, λ⟩ ≥ 1` and
`1 ≤ n ≤ d_ij - h`, the degree `n` coefficient of `C_L τ W_R` vanishes. -/
theorem mixedGrassQ (hij : i ≠ j) (h1 : 1 ≤ ip RD i lam) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : (n : ℤ) + ip RD i lam ≤ C.dij i j) :
    sconv (sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j)) (wRs RD k sc lam i (up j)) n =
      0 := by
  have hw := ip_wt_up_ne RD hij lam
  have hh : ((ip RD i lam).toNat : ℤ) = ip RD i lam := Int.toNat_of_nonneg (by omega)
  have hS := closeSumQ RD k sc lam i j hij h1 (n - 1) (by push_cast [Nat.cast_sub hn1]; omega)
  have key : ∀ s ∈ (CL.qCL sc i j).support,
      ∑ α ∈ Finset.range (n + 1),
        (if C.dij i j ≤ α + s 0 then
          cLs RD k sc lam i (up j) (α + s 0 - C.dij i j) * NF.dotsU (pres RD k sc) lam (up j) (s 1) else 0) *
          wRs RD k sc lam i (up j) (n - α) =
      ∑ t ∈ Finset.range (s 0),
        NF.bubLU (pres RD k sc) lam (up j) (NF.ccwU (pres RD k sc) (wt RD lam [up j]) i ((n - 1 + t : ℕ) : ℤ)) ≫
          NF.bubRU (pres RD k sc) lam (up j) (NF.cwU (pres RD k sc) lam i ((s 0 - 1 - t : ℕ) : ℤ)) ≫
            NF.dotsU (pres RD k sc) lam (up j) (s 1) := by
    intro s hs
    have hs0 := qCL_support_le k sc hij s hs
    have hsubL : Finset.Ico (C.dij i j - s 0) (n + 1) ⊆ Finset.range (n + 1) := by
      intro a ha
      simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢
      omega
    rw [← Finset.sum_subset hsubL fun a ha hna => by
      simp only [Finset.mem_Ico, Finset.mem_range, not_and, not_lt] at ha hna
      rw [ite_eq_right (by omega), zero_mul]]
    rw [Finset.sum_Ico_eq_sum_range]
    have hsubR : Finset.Ico (C.dij i j - (ip RD i lam).toNat - n)
        (C.dij i j - (ip RD i lam).toNat - n + (n + 1 - (C.dij i j - s 0))) ⊆
          Finset.range (s 0) := by
      intro t ht
      simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢
      omega
    rw [← Finset.sum_subset hsubR fun t ht hnt => by
      simp only [Finset.mem_Ico, Finset.mem_range, not_and, not_lt] at ht hnt
      by_cases hlt : t < C.dij i j - (ip RD i lam).toNat - n
      · rw [ccwU_eq_zero RD k sc _ i _ (by omega), bubLU_zero, Limits.zero_comp]
      · rw [cwU_eq_zero RD k sc _ i _ (by omega), bubRU_zero]
        simp only [Limits.zero_comp, Limits.comp_zero]]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    rw [ite_eq_left (by omega), End.mul_def, End.mul_def, cLs, wRs, ← Category.assoc,
      ← NF.bubLU_comm]
    have e1 : -ip RD i (wt RD lam [up j]) - 1 +
        ((C.dij i j - s 0 + a + s 0 - C.dij i j : ℕ) : ℤ) =
          ((n - 1 + (C.dij i j - (ip RD i lam).toNat - n + a) : ℕ) : ℤ) := by
      omega
    have e2 : ip RD i lam - 1 + ((n - (C.dij i j - s 0 + a) : ℕ) : ℤ) =
        ((s 0 - 1 - (C.dij i j - (ip RD i lam).toNat - n + a) : ℕ) : ℤ) := by
      omega
    rw [e1, e2]
  rw [sconv]
  simp only [sconv_cLs_τQ RD k sc lam hij, smul_mul_assoc, Finset.sum_mul]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  rw [Finset.sum_congr rfl fun s hs => by rw [key s hs], hS, smul_zero]

theorem sconv_eq_add_last {A : Type*} [Ring A] (u w : ℕ → A) (n : ℕ) :
    sconv u w n = ∑ a ∈ Finset.range n, u a * w (n - a) + u n * w 0 := by
  rw [sconv, Finset.sum_range_succ, Nat.sub_self]

/-- **Bubble slides in all degrees for `i ≠ j`, general Cautis–Lauda scalars** (KL III,
Propositions 3.3–3.4, extended to fake bubbles): with
`τ = t_ij⁻¹ ∑_s c_s x_j^{s_1} t^{d_ij - s_0}` (`τQ`), the counterclockwise bubbles to the right of
an upward `j`-strand are `C_L τ` and the clockwise bubbles to its left are `τ W_R`. -/
theorem slidesQ (hij : i ≠ j) :
    (∀ α, cRs RD k sc lam i (up j) α =
        sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) α) ∧
      ∀ β, wLs RD k sc lam i (up j) β =
        sconv (τQ RD k sc lam i j) (wRs RD k sc lam i (up j)) β := by
  have hw := ip_wt_up_ne RD hij lam
  have A0 : cRs RD k sc lam i (up j) 0 =
      sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) 0 := by
    rw [sconv, Finset.sum_range_one, Nat.sub_self, cLs_zero, τQ_zero RD k sc lam hij, mul_one,
      cRs_zero]
  have B0 : wLs RD k sc lam i (up j) 0 =
      sconv (τQ RD k sc lam i j) (wRs RD k sc lam i (up j)) 0 := by
    rw [sconv, Finset.sum_range_one, Nat.sub_self, wRs_zero, τQ_zero RD k sc lam hij, mul_one,
      wLs_zero]
  have hG := sconv_cRs_wRs RD k sc lam i (up j)
  have hG' := sconv_cLs_wLs RD k sc lam i (up j)
  by_cases hA : ip RD i lam ≤ 0
  · have hA' : ∀ α, cRs RD k sc lam i (up j) α =
        sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) α := by
      intro α
      rcases α with _ | α
      · exact A0
      · exact slideAQ_real RD k sc lam hij _ (by push_cast; omega)
    exact ⟨hA', transfer_right _ _ _ _ _ hG hG' hA' (cLs_zero RD k sc lam i (up j))⟩
  by_cases hB : (C.dij i j : ℤ) ≤ ip RD i lam
  · have hB' : ∀ β, wLs RD k sc lam i (up j) β =
        sconv (τQ RD k sc lam i j) (wRs RD k sc lam i (up j)) β := by
      intro β
      rcases β with _ | β
      · exact B0
      · exact slideBQ_real RD k sc lam hij _ (by push_cast; omega)
    exact ⟨transfer_left _ _ _ _ _ hG hG' hB' (wRs_zero RD k sc lam i (up j)), hB'⟩
  -- the gap `0 < ⟨i, λ⟩ < d_ij` (Brundan–Ellis, proof of Proposition 7.3(iii))
  set M : ℕ := ((C.dij i j : ℤ) - ip RD i lam).toNat with hM
  have claim : ∀ n ≤ M, cRs RD k sc lam i (up j) n =
      sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · exact A0
    have e₁ := hG n
    have e₂ := mixedGrassQ RD k sc lam hij (by omega) n hn1 (by omega)
    rw [ite_eq_right (by omega)] at e₁
    rw [sconv_eq_add_last (cRs RD k sc lam i (up j)), wRs_zero, mul_one] at e₁
    rw [sconv_eq_add_last (sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j)), wRs_zero,
      mul_one] at e₂
    have : ∑ a ∈ Finset.range n, cRs RD k sc lam i (up j) a * wRs RD k sc lam i (up j) (n - a) =
        ∑ a ∈ Finset.range n, sconv (cLs RD k sc lam i (up j)) (τQ RD k sc lam i j) a *
          wRs RD k sc lam i (up j) (n - a) :=
      Finset.sum_congr rfl fun a ha => by
        rw [ih a (Finset.mem_range.1 ha) (by have := Finset.mem_range.1 ha; omega)]
    rw [this] at e₁
    exact add_left_cancel (e₁.trans e₂.symm)
  have hBlow := transfer_right_trunc _ _ _ _ _ hG hG' M claim (cLs_zero RD k sc lam i (up j))
  have hB' : ∀ β, wLs RD k sc lam i (up j) β =
      sconv (τQ RD k sc lam i j) (wRs RD k sc lam i (up j)) β := by
    intro β
    by_cases hβ : β ≤ M
    · exact hBlow β hβ
    · exact slideBQ_real RD k sc lam hij _ (by omega)
  exact ⟨transfer_left _ _ _ _ _ hG hG' hB' (wRs_zero RD k sc lam i (up j)), hB'⟩

end GenQ

end Categorification.KL3.Diagram.CLQ
