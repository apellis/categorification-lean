/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlidesAll
import Categorification.Diagrams.KL3.Rewriting

/-!
# Bubble slides in all degrees for an arbitrary Cartan datum

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Propositions 3.3 and 3.4 (TeX labels `prop_bubble_slide1`, `prop_bubble_slide2`).

KL III state the bubble slides only for `i = j`, `i · j = 0` and `i · j = -1`. For `i ≠ j` with
`i · j ≠ 0` and the KL II polynomial `Q_ij = u^{d_ij} + v^{d_ji}` the slides of real bubbles are
`bubble_slide_ccw_ne`, `bubble_slide_cw_ne` (the proof of KL III, Proposition 3.3). As in
`BubbleSlidesAll`, the slides in all degrees (fake bubbles included) are the generating function
identities `C_R = C_L τ` and `W_L = τ W_R` with `τ = 1 + x_j^{d_ji} t^{d_ij}` (`slides_gen`). If
`h = ⟨i, λ⟩ ≤ 0` or `h ≥ d_ij` one of the two families consists of real bubbles and the other
identity follows by inverting power series (`transfer_left`, `transfer_right`). For
`0 < h < d_ij` neither family is real; following J. Brundan, A. Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, proof of Proposition 7.3(iii) (TeX lines 9219–9420), the
missing low-degree identities come from the deformed braid relation (`dg_braidQ`, KL III
`eq_r3_hard-gen`) closed up on both sides of an upward `j`-strand: the two closures of the braid
diagrams contain a right curl, resp. a left curl with few dots, and vanish by the curl relations
of KL III Definition 3.1, while the closure of the correction term is
`∑_{r+s=d_ij-1} (ccw bubble, left) (cw bubble, right)` (`mixedGrass`).

## Main results

* `dg_braidQ`: the braid relation with correction on `E_c E_d E_c` (`c ≠ d`, `c · d ≠ 0`).
* `mixedGrass`: `∑_{s ≤ n} ccw_{n-s}(left of E_j) cw_s(right of E_j) = 0` for
  `1 ≤ n ≤ d_ij - ⟨i,λ⟩`, `0 < ⟨i,λ⟩`.
* `slides_gen`: the bubble slides in all degrees for `i ≠ j`, `i · j ≠ 0`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## The braid relation with correction on upward strands -/

section NcEval

variable {k} {A : Type*} [Ring A] [Algebra k A]

theorem ncEval_sum_aux {n : ℕ} (y : Fin n → A) {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin n) k) :
    KLR.ncEval y (∑ a ∈ s, p a) = ∑ a ∈ s, KLR.ncEval y (p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [KLR.ncEval]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ncEval_add_aux, ih]

theorem ncEval_X0_pow_mul_X2_pow (y : Fin 3 → A) (p q : ℕ) :
    KLR.ncEval y (MvPolynomial.X 0 ^ p * MvPolynomial.X 2 ^ q : MvPolynomial (Fin 3) k) =
      y 0 ^ p * y 2 ^ q := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
    ncEval_monomial_aux]
  simp [List.ofFn_succ, Finsupp.single_apply]

end NcEval

/-- **KL III `eq_r3_hard-gen`** (the case with correction term) for `c ≠ d`, `c · d ≠ 0`, with the
KL II polynomial `Q_cd = u^{d_cd} + v^{d_dc}`: on `E_c E_d E_c`,
`ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁ + ∑_{t < d_cd} x₀^t x₂^{d_cd - 1 - t}` (normal form, bottom to top). -/
theorem dg_braidQ (μ : X) (c d : I) (h : c ≠ d) (hcd : C.dot c d ≠ 0) :
    dg RD k μ [up c, up d, up c] [up c, up d, up c]
        [([], .cross true c d, [up c]), ([up d], .cross true c c, []),
          ([], .cross true d c, [up c])] =
      dg RD k μ [up c, up d, up c] [up c, up d, up c]
        [([up c], .cross true d c, []), ([], .cross true c c, [up d]),
          ([up c], .cross true c d, [])] +
      ∑ t ∈ Finset.range (C.dij c d),
        dg RD k μ [up c, up d, up c] [up c, up d, up c]
          (List.replicate t ([], .dot (up c), [up d, up c]) ++
            List.replicate (C.dij c d - 1 - t) ([up c, up d], .dot (up c), [])) := by
  have key := KLR.Diagram.braidQ_at (KLR.klQ2 k C) (u := []) (v := []) h
    (KLR.Diagram.braidL c d c) (KLR.Diagram.braidR c d c) (KLR.Diagram.E0 c d c)
    (KLR.Diagram.E1 c d c) (KLR.Diagram.E2 c d c) rfl rfl rfl rfl rfl
  have key' := congrArg (functorEndAlg k (upFunctor RD k μ) _) key
  rw [map_sub, AlgHom.map_ncEval] at key'
  simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    upFunctor_diag, upDiag_eq_dg] at key'
  rw [← sub_eq_iff_eq_add']
  refine Eq.trans ?_ (key'.trans ?_)
  · rfl
  rw [KLR.klQ2, ite_eq_right hcd, KLR.qbar_X_pow_add_X_pow, ncEval_sum_aux]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ncEval_X0_pow_mul_X2_pow]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    upFunctor_diag, upDiag_eq_dg]
  change (dgE RD k μ [up c, up d, up c] [([], .dot (up c), [up d, up c])]) ^ t *
      (dgE RD k μ [up c, up d, up c] [([up c, up d], .dot (up c), [])]) ^ (C.dij c d - 1 - t) = _
  rw [dgE_pow_single RD k μ _ _ (by schain), dgE_pow_single RD k μ _ _ (by schain), End.mul_def,
    dgE, dgE, dg_comp (by schain) (by schain)]
  exact dg_swap_dots RD k μ [] [up d] [] (up c) (up c) _ _

/-! ## Closing the braid relation around an upward strand -/

section Closure

variable (lam : X) (i j : I)

/-- The right curl on an upward `i`-strand in the region `λ` vanishes when `⟨i, λ⟩ ≥ 1` (KL III,
Definition 3.1, item iv), the sum being empty). -/
theorem dg_curlR_eq_zero (h1 : 1 ≤ ip RD i lam) :
    dg RD k lam [up i] [up i]
        [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] = 0 := by
  rw [dg_curlR, show (-ip RD i lam + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero]

/-- The top part of the closure of `ψ₀ψ₁ψ₀` (strands `i, j, i`) around an upward `j`-strand
contains a right curl in the region `λ`, hence vanishes for `⟨i, λ⟩ ≥ 1`. -/
theorem closeBL_tail (h1 : 1 ≤ ip RD i lam) :
    dg RD k lam [dn i, up i, up j] [up j]
      [([dn i, up i, up j], .cup (up i), []), ([dn i], .cross true i j, [up i, dn i]),
        ([dn i, up j], .cross true i i, [dn i]), ([dn i], .cross true j i, [up i, dn i]),
        ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])] = 0 := by
  dswap 0
  dswap 3
  rw [dg_stepL_at _ 1 [dn i, up j] [] (dg_curlR_eq_zero RD k lam i h1) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm), map_zero]

/-- The left curl with `N` dots on its loop (below the crossing) in the outer region `ν + i_X`
vanishes when `N + ⟨i, ν + i_X⟩ + 1 ≤ 0` (`ptrL_nhDotL_nhCross`: the sum is empty). -/
theorem dg_curlL_dots_eq_zero (ν : X) (N : ℕ) (hN : (N : ℤ) + ip RD i (wt RD ν [up i]) + 1 ≤ 0) :
    dg RD k ν [up i] [up i]
      ([([], .cup (dn i), [up i])] ++ List.replicate N ([dn i], .dot (up i), [up i]) ++
        [([dn i], .cross true i i, []), ([], .cap (up i), [up i])]) = 0 := by
  have e := ptrL_dg RD k ν i (List.replicate N ([], .dot (up i), [up i]) ++
    [([], .cross true i i, [])])
  rw [← dg_comp (t := [up i, up i]) (by schain) (by schain)] at e
  change ptrL RD k ν i (nhDotL RD k ν i N ≫ nhCross RD k ν i) = _ at e
  rw [ptrL_nhDotL_nhCross, show ((N : ℤ) + ip RD i (wt RD ν [up i]) + 1).toNat = 0 by omega,
    Finset.sum_range_zero] at e
  refine Eq.trans ?_ e.symm
  congr 1
  lnf

theorem ip_wt_up_up_dn (N : X) : ip RD i (wt RD N [up i, up j, dn i]) = ip RD i (wt RD N [up j]) := by
  simp [ip, wt, sh, sgn]
  ring

/-- The closure of `ψ₁ψ₀ψ₁` (strands `i, j, i`, `N` dots on the first strand below it) around an
upward `j`-strand contains a left curl with `N` dots in the region `λ + j_X`, hence vanishes for
`N + ⟨i, λ + j_X⟩ + 1 ≤ 0`. -/
theorem closeBR_eq_zero (N : ℕ) (hN : (N : ℤ) + ip RD i (wt RD lam [up j]) + 1 ≤ 0) :
    dg RD k lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), []), ([dn i, up i], .cross true j i, [dn i]),
          ([dn i], .cross true i i, [up j, dn i]), ([dn i, up i], .cross true i j, [dn i]),
          ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]) = 0 := by
  have e₁ := dg_interchange (RD := RD) (k := k) (μ := lam) (S := [up j]) (T := [up j]) []
    [([dn i], .cross true i i, [up j, dn i]), ([dn i, up i], .cross true i j, [dn i]),
      ([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]
    (s := []) (s' := [dn i, up i]) (t := [up j]) (t' := [up i, up j, dn i])
    (A := [([], .cup (dn i), [])] ++ List.replicate N ([dn i], .dot (up i), []))
    (B := [([up j], .cup (up i), []), ([], .cross true j i, [dn i])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil, List.map_replicate,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₁ ⊢
  rw [e₁]
  have e₂ := dg_interchange (RD := RD) (k := k) (μ := lam) (S := [up j]) (T := [up j])
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
  have hz := dg_curlL_dots_eq_zero RD k i (wt RD lam [up j, dn i]) N (by
    rw [show wt RD (wt RD lam [up j, dn i]) [up i] = wt RD lam [up i, up j, dn i] by
      simp, ip_wt_up_up_dn]; exact hN)
  rw [dg_stepL RD k lam [([up j], .cup (up i), []), ([], .cross true j i, [dn i])]
    [([], .cross true i j, [dn i]), ([up j], .cap (dn i), [])] [] [up j, dn i] hz
    (by schain) (by schain) (by lnf), map_zero]

/-- The closure of the correction term `x₀^t x₂^s` (with `N` further dots on the first strand)
around an upward `j`-strand: a counterclockwise bubble with `N + t` dots to the left of the strand
and a clockwise bubble with `s` dots to its right. -/
theorem closeCorr (N t s : ℕ) :
    dg RD k lam [up j] [up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
        [([dn i, up i, up j], .cup (up i), [])] ++
        List.replicate t ([dn i], .dot (up i), [up j, up i, dn i]) ++
        List.replicate s ([dn i, up i, up j], .dot (up i), [dn i]) ++
        [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])]) =
      bubLU RD k lam (up j) (ccwU RD k (wt RD lam [up j]) i ((N + t : ℕ) : ℤ)) ≫
        bubRU RD k lam (up j) (cwU RD k lam i (s : ℤ)) := by
  have e₁ := dg_interchange (RD := RD) (k := k) (μ := lam) (S := [up j]) (T := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]))
    (List.replicate s ([dn i, up i, up j], .dot (up i), [dn i]) ++
      [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])])
    (s := [dn i, up i]) (s' := [dn i, up i]) (t := [up j]) (t' := [up j, up i, dn i])
    (A := List.replicate t ([dn i], .dot (up i), []))
    (B := [([up j], .cup (up i), [])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil, List.map_replicate,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₁ ⊢
  rw [← e₁]
  have e₂ := dg_interchange (RD := RD) (k := k) (μ := lam) (S := [up j]) (T := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
      List.replicate t ([dn i], .dot (up i), [up j])) []
    (s := [dn i, up i]) (s' := []) (t := [up j]) (t' := [up j])
    (A := [([], .cap (up i), [])])
    (B := [([up j], .cup (up i), [])] ++ List.replicate s ([up j], .dot (up i), [dn i]) ++
      [([up j], .cap (dn i), [])]) (by schain) (by schain)
  simp only [whL, List.map_cons, List.map_nil, List.map_replicate, List.map_append,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at e₂ ⊢
  rw [← e₂, ccwU_of_nonneg, cwU_of_nonneg, bubLU, bubRU, plcL_dg, plcL_dg_nil]
  change _ = dg RD k lam [up j] [up j] _ ≫ dg RD k lam [up j] [up j] _
  rw [dg_comp (by unfold ccwLs; schain) (by unfold cwLs; schain)]
  symm
  unfold cwLs
  dstep ((ccwLs i (N + t)).map (whL [] [up j])) [] [up j] [] (dg_cw_dots RD k lam i s)
  simp only [ccwLs, whL, List.map_cons, List.map_nil, List.map_replicate, List.map_append,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.replicate_add]

/-- **The closed deformed braid relation** (J. Brundan, A. Ellis, arXiv:1701.04133v2, proof of
Proposition 7.3(iii), the display after TeX line 9234, for `t_ij = 1`, `s_ij^{pq} = 0`): for
`i ≠ j`, `i · j ≠ 0`, `⟨i, λ⟩ ≥ 1` and `N + ⟨i, λ + j_X⟩ + 1 ≤ 0`,
`∑_{t < d_ij} (ccw_{N+t} ⊗ E_j) … = 0`, i.e. with the counterclockwise bubble with `N + t` dots to
the left of the upward `j`-strand and the clockwise bubble with `d_ij - 1 - t` dots to its right.
Obtained by closing the relation `dg_braidQ` on the strands `i, j, i` around the `j`-strand
(`closeBL_tail`, `closeBR_eq_zero`, `closeCorr`). -/
theorem closeSum (hij : i ≠ j) (hdot : C.dot i j ≠ 0) (h1 : 1 ≤ ip RD i lam) (N : ℕ)
    (hN : (N : ℤ) + ip RD i (wt RD lam [up j]) + 1 ≤ 0) :
    ∑ t ∈ Finset.range (C.dij i j),
      bubLU RD k lam (up j) (ccwU RD k (wt RD lam [up j]) i ((N + t : ℕ) : ℤ)) ≫
        bubRU RD k lam (up j) (cwU RD k lam i ((C.dij i j - 1 - t : ℕ) : ℤ)) = 0 := by
  have hD1 : dg RD k lam [up j] [up j]
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
      ← dg_comp (t := [dn i, up i, up j]) (by schain) (by schain), closeBL_tail RD k lam i j h1,
      Limits.comp_zero]
  have key := dg_stepL RD k lam (s₀ := [up j]) (t₀ := [up j])
    ([([], .cup (dn i), [up j])] ++ List.replicate N ([dn i], .dot (up i), [up j]) ++
      [([dn i, up i, up j], .cup (up i), [])])
    [([dn i, up i, up j], .cap (dn i), []), ([], .cap (up i), [up j])] [dn i] [dn i]
    (dg_braidQ RD k (wt RD lam [dn i]) i j hij hdot) (by schain) (by schain) rfl
  rw [hD1, map_add, map_sum, ctxL_dg RD k lam (by schain) (by schain)] at key
  have hD2 := closeBR_eq_zero RD k lam i j N hN
  simp only [whL, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc] at key hD2
  rw [hD2, zero_add] at key
  refine Eq.trans ?_ key.symm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ctxL_dg RD k lam (by schain) (by schain), ← closeCorr RD k lam i j N t (C.dij i j - 1 - t)]
  simp only [whL, List.map_replicate, List.map_append,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

end Closure

/-! ## The mixed infinite Grassmannian relation in low degrees -/

section Mixed

variable (lam : X) (i j : I)

theorem dij_pos {i j : I} (hij : i ≠ j) (hdot : C.dot i j ≠ 0) : 0 < C.dij i j := by
  have h₁ := C.dij_mul hij
  rcases Nat.eq_zero_or_pos (C.dij i j) with h | h
  · rw [h] at h₁; simp at h₁; exact absurd h₁ hdot
  · exact h

theorem ip_wt_up_ne {i j : I} (hij : i ≠ j) (lam : X) :
    ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
  rw [ip_wt_up, A_eq_neg_dij hij]; ring

/-- **The mixed Grassmannian relation in low degrees** (Brundan–Ellis, arXiv:1701.04133v2, proof
of Proposition 7.3(iii)): for `i ≠ j`, `i · j ≠ 0`, `h = ⟨i, λ⟩ ≥ 1` and `1 ≤ n ≤ d_ij - h`,
`∑_{a ≤ n} ccw_{a+*}(left of E_j) · cw_{n-a+*}(right of E_j) = 0`. -/
theorem mixedGrass (hij : i ≠ j) (hdot : C.dot i j ≠ 0) (h1 : 1 ≤ ip RD i lam) (n : ℕ)
    (hn1 : 1 ≤ n) (hn : (n : ℤ) + ip RD i lam ≤ C.dij i j) :
    sconv (cLs RD k lam i (up j)) (wRs RD k lam i (up j)) n = 0 := by
  have hw := ip_wt_up_ne RD hij lam
  set d := C.dij i j with hd
  set h := ip RD i lam with hh
  have hS := closeSum RD k lam i j hij hdot h1 (n - 1) (by push_cast [Nat.cast_sub hn1]; omega)
  rw [← hd] at hS
  set m0 : ℕ := d - h.toNat - n with hm0
  have hm0' : (m0 : ℤ) = d - h - n := by omega
  have hsub : Finset.Ico m0 (m0 + (n + 1)) ⊆ Finset.range d := by
    intro t ht
    simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢
    omega
  have hz : ∀ t ∈ Finset.range d, t ∉ Finset.Ico m0 (m0 + (n + 1)) →
      bubLU RD k lam (up j) (ccwU RD k (wt RD lam [up j]) i ((n - 1 + t : ℕ) : ℤ)) ≫
        bubRU RD k lam (up j) (cwU RD k lam i ((d - 1 - t : ℕ) : ℤ)) = 0 := by
    intro t ht hnot
    simp only [Finset.mem_Ico, Finset.mem_range, not_and_or, not_le, not_lt] at ht hnot
    rcases hnot with h' | h'
    · rw [ccwU_eq_zero RD k _ i _ (by push_cast [Nat.cast_sub hn1]; omega), bubLU_zero,
        Limits.zero_comp]
    · have e : ((d - 1 - t : ℕ) : ℤ) = d - 1 - t := by omega
      rw [cwU_eq_zero RD k _ i _ (by rw [e]; omega), bubRU_zero, Limits.comp_zero]
  rw [← Finset.sum_subset hsub hz, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hS
  refine Eq.trans ?_ hS
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  rw [End.mul_def, cLs, wRs, bubLU_comm]
  have e₁ : ((d - 1 - (m0 + a) : ℕ) : ℤ) = d - 1 - m0 - a := by omega
  have e₂ : ((n - a : ℕ) : ℤ) = n - a := by omega
  have e₃ : ((n - 1 + (m0 + a) : ℕ) : ℤ) = n - 1 + m0 + a := by omega
  congr 3 <;> first | (rw [e₃]; omega) | (rw [e₁, e₂]; omega)

end Mixed

/-! ## Bubble slides in all degrees -/

section Conv

variable {A : Type*} [Ring A]

/-- Convolution with `1 + D t^d` (`d ≥ 1`) on the right. -/
theorem sconv_gen_right (u : ℕ → A) (d : ℕ) (hd : 0 < d) (D : A) (α : ℕ) :
    sconv u (fun e => if e = 0 then 1 else if e = d then D else 0) α =
      u α + (if d ≤ α then u (α - d) * D else 0) := by
  rw [sconv, Finset.sum_range_succ, Nat.sub_self, ite_eq_left rfl, mul_one, add_comm]
  congr 1
  by_cases h : d ≤ α
  · rw [ite_eq_left h, Finset.sum_eq_single (α - d)]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · intro b hb hb'
      have := Finset.mem_range.1 hb
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun b hb => ?_
    have := Finset.mem_range.1 hb
    rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]

/-- Convolution with `1 + D t^d` (`d ≥ 1`) on the left. -/
theorem sconv_gen_left (w : ℕ → A) (d : ℕ) (hd : 0 < d) (D : A) (β : ℕ) :
    sconv (fun e => if e = 0 then 1 else if e = d then D else 0) w β =
      w β + (if d ≤ β then D * w (β - d) else 0) := by
  rw [sconv, Finset.sum_range_succ', ite_eq_left rfl, one_mul, Nat.sub_zero, add_comm]
  congr 1
  by_cases h : d ≤ β
  · rw [ite_eq_left h, Finset.sum_eq_single (d - 1)]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), show β - (d - 1 + 1) = β - d by omega]
    · intro b hb hb'
      rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun b hb => ?_
    have := Finset.mem_range.1 hb
    rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]

/-- Truncated transfer: if `u w = 1`, `u' w' = 1`, `u'₀ = 1` and `u = u' τ` in degrees `≤ M`,
then `w' = τ w` in degrees `≤ M`. -/
theorem transfer_right_trunc (u w u' w' τ : ℕ → A)
    (hG : ∀ d, sconv u w d = if d = 0 then 1 else 0)
    (hG' : ∀ d, sconv u' w' d = if d = 0 then 1 else 0) (M : ℕ)
    (hA : ∀ α ≤ M, u α = sconv u' τ α) (hu' : u' 0 = 1) : ∀ β ≤ M, w' β = sconv τ w β := by
  intro β
  induction β using Nat.strong_induction_on with
  | _ β ih =>
  intro hβ
  have e₁ := hG' β
  have e₂ : sconv u' (sconv τ w) β = if β = 0 then 1 else 0 := by
    rw [← sconv_assoc, ← hG β]
    exact Finset.sum_congr rfl fun a ha => by
      rw [hA a (by have := Finset.mem_range.1 ha; omega)]
  rw [sconv, Finset.sum_range_succ', hu', one_mul, Nat.sub_zero] at e₁ e₂
  have : ∑ a ∈ Finset.range β, u' (a + 1) * w' (β - (a + 1)) =
      ∑ a ∈ Finset.range β, u' (a + 1) * sconv τ w (β - (a + 1)) :=
    Finset.sum_congr rfl fun a ha => by
      rw [ih (β - (a + 1)) (by have := Finset.mem_range.1 ha; omega) (by omega)]
  rw [this] at e₁
  exact add_left_cancel (e₁.trans e₂.symm)

end Conv

section Gen

variable (lam : X) (i j : I)

/-- The coefficients of `τ = 1 + x_j^{d_ji} t^{d_ij}` (dots on the strand `j`). -/
abbrev τgen (e : ℕ) : End ((pres RD k).obj (ob RD lam [up j])) :=
  if e = 0 then 1 else if e = C.dij i j then dotsU RD k lam (up j) (C.dij j i) else 0

variable {i j}

theorem lin_ccwReal_eq (ν : X) (i : I) (m : ℕ) :
    (pres RD k).lin (LinDiagram.of (ccwReal RD ν i m)) = ccwU RD k ν i (m : ℤ) := by
  rw [lin_ccwReal, ccwU_of_nonneg]

theorem lin_cwReal_eq (ν : X) (i : I) (m : ℕ) :
    (pres RD k).lin (LinDiagram.of (cwReal RD ν i m)) = cwU RD k ν i (m : ℤ) := by
  rw [lin_cwReal, cwU_of_nonneg]

theorem slideA_gen_real (hij : i ≠ j) (hdot : C.dot i j ≠ 0) (α : ℕ)
    (hα : 0 ≤ -ip RD i lam - 1 + α) :
    cRs RD k lam i (up j) α = sconv (cLs RD k lam i (up j)) (τgen RD k lam i j) α := by
  have hw := ip_wt_up_ne RD hij lam
  have hd := dij_pos hij hdot
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -ip RD i lam - 1 + α := ⟨_, Int.toNat_of_nonneg hα⟩
  have h := bubble_slide_ccw_ne RD k lam i j hij m
  rw [ite_eq_right hdot, lin_bubR_eq, lin_bubL_eq, lin_bubL_eq, lin_ccwReal_eq, lin_ccwReal_eq,
    lin_ccwReal_eq] at h
  rw [sconv_gen_right _ _ hd, cRs, ← hm, h, cLs]
  congr 1
  · congr 2; push_cast; omega
  · split_ifs with hα'
    · rw [End.mul_def, cLs, ← bubLU_comm]
      congr 3
      push_cast [Nat.cast_sub hα']; omega
    · rw [ccwU_eq_zero RD k _ i _ (by omega), bubLU_zero, Limits.zero_comp]

theorem slideB_gen_real (hij : i ≠ j) (hdot : C.dot i j ≠ 0) (β : ℕ)
    (hβ : 0 ≤ ip RD i (wt RD lam [up j]) - 1 + β) :
    wLs RD k lam i (up j) β = sconv (τgen RD k lam i j) (wRs RD k lam i (up j)) β := by
  have hw := ip_wt_up_ne RD hij lam
  have hd := dij_pos hij hdot
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = ip RD i (wt RD lam [up j]) - 1 + β :=
    ⟨_, Int.toNat_of_nonneg hβ⟩
  have h := bubble_slide_cw_ne RD k lam i j hij m
  rw [ite_eq_right hdot, lin_bubR_eq, lin_bubR_eq, lin_bubL_eq, lin_cwReal_eq, lin_cwReal_eq,
    lin_cwReal_eq] at h
  rw [sconv_gen_left _ _ hd, wLs, ← hm, h, wRs]
  congr 1
  · congr 2; push_cast; omega
  · split_ifs with hβ'
    · rw [End.mul_def, wRs]
      congr 3
      push_cast [Nat.cast_sub hβ']; omega
    · rw [cwU_eq_zero RD k _ i _ (by omega), bubRU_zero, Limits.zero_comp]

/-- **Bubble slides in all degrees for `i ≠ j`, `i · j ≠ 0`** (KL III, Propositions 3.3–3.4,
extended to an arbitrary Cartan datum and to fake bubbles): with `τ = 1 + x_j^{d_ji} t^{d_ij}`,
the counterclockwise bubbles to the right of an upward `j`-strand are `C_L τ` and the clockwise
bubbles to its left are `τ W_R`, as power series in the degree index. -/
theorem slides_gen (hij : i ≠ j) (hdot : C.dot i j ≠ 0) :
    (∀ α, cRs RD k lam i (up j) α = sconv (cLs RD k lam i (up j)) (τgen RD k lam i j) α) ∧
      ∀ β, wLs RD k lam i (up j) β = sconv (τgen RD k lam i j) (wRs RD k lam i (up j)) β := by
  have hw := ip_wt_up_ne RD hij lam
  have hd := dij_pos hij hdot
  have A0 : cRs RD k lam i (up j) 0 = sconv (cLs RD k lam i (up j)) (τgen RD k lam i j) 0 := by
    rw [sconv_gen_right _ _ hd, ite_eq_right (by omega), add_zero, cRs_zero, cLs_zero]
  have B0 : wLs RD k lam i (up j) 0 = sconv (τgen RD k lam i j) (wRs RD k lam i (up j)) 0 := by
    rw [sconv_gen_left _ _ hd, ite_eq_right (by omega), add_zero, wRs_zero, wLs_zero]
  have hG := sconv_cRs_wRs RD k lam i (up j)
  have hG' := sconv_cLs_wLs RD k lam i (up j)
  by_cases hA : ip RD i lam ≤ 0
  · have hA' : ∀ α, cRs RD k lam i (up j) α =
        sconv (cLs RD k lam i (up j)) (τgen RD k lam i j) α := by
      intro α
      rcases α with _ | α
      · exact A0
      · exact slideA_gen_real RD k lam hij hdot _ (by push_cast; omega)
    exact ⟨hA', transfer_right _ _ _ _ _ hG hG' hA' (cLs_zero RD k lam i (up j))⟩
  by_cases hB : (C.dij i j : ℤ) ≤ ip RD i lam
  · have hB' : ∀ β, wLs RD k lam i (up j) β =
        sconv (τgen RD k lam i j) (wRs RD k lam i (up j)) β := by
      intro β
      rcases β with _ | β
      · exact B0
      · exact slideB_gen_real RD k lam hij hdot _ (by push_cast; omega)
    exact ⟨transfer_left _ _ _ _ _ hG hG' hB' (wRs_zero RD k lam i (up j)), hB'⟩
  -- the gap `0 < ⟨i, λ⟩ < d_ij` (Brundan–Ellis, proof of Proposition 7.3(iii))
  set M : ℕ := ((C.dij i j : ℤ) - ip RD i lam).toNat with hM
  have claim : ∀ n ≤ M, cRs RD k lam i (up j) n =
      sconv (cLs RD k lam i (up j)) (τgen RD k lam i j) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · exact A0
    rw [sconv_gen_right _ _ hd, ite_eq_right (by omega), add_zero]
    have e₁ := hG n
    have e₂ := mixedGrass RD k lam i j hij hdot (by omega) n hn1 (by omega)
    rw [ite_eq_right (by omega)] at e₁
    rw [sconv, Finset.sum_range_succ, Nat.sub_self, wRs_zero, mul_one] at e₁ e₂
    have : ∑ a ∈ Finset.range n, cRs RD k lam i (up j) a * wRs RD k lam i (up j) (n - a) =
        ∑ a ∈ Finset.range n, cLs RD k lam i (up j) a * wRs RD k lam i (up j) (n - a) :=
      Finset.sum_congr rfl fun a ha => by
        have ha' := Finset.mem_range.1 ha
        rw [ih a ha' (by omega), sconv_gen_right _ _ hd, ite_eq_right (by omega), add_zero]
    rw [this] at e₁
    exact add_left_cancel (e₁.trans e₂.symm)
  have hBlow := transfer_right_trunc _ _ _ _ _ hG hG' M claim (cLs_zero RD k lam i (up j))
  have hB' : ∀ β, wLs RD k lam i (up j) β =
      sconv (τgen RD k lam i j) (wRs RD k lam i (up j)) β := by
    intro β
    by_cases hβ : β ≤ M
    · exact hBlow β hβ
    · exact slideB_gen_real RD k lam hij hdot _ (by omega)
  exact ⟨transfer_left _ _ _ _ _ hG hG' hB' (wRs_zero RD k lam i (up j)), hB'⟩

end Gen

end Categorification.KL3.Diagram
