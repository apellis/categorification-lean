/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Brundan

/-!
# One-sided mixed relations in `U_Q(g)` without the mixed relations

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Lemma 5.2 and its
proof. Brundan proves the relations (5.2), (5.3) by composing with the isomorphism built from the
sideways crossing `σ` and the `sl₂` decomposition; the computation itself does not use the inverse
of `σ`. Read in `presNM` (all relations of `U_Q(g)` except the mixed ones), it gives, for `i ≠ j`,
one of the two mixed relations `crossl j i ≫ crossr j i = t_{ij} · 1`, `crossr j i ≫ crossl j i =
t_{ij} · 1` at each weight, i.e. a one-sided inverse of the sideways crossing `crossl j i`.

## Main results

* `dgN_capTurn`: `⟨i, λ⟩ ≤ 0`, the cap `F_i E_i ⟶ 1` with the strand `j` passing both legs
  (crossing `σ` then `τ`) is `t_{ij}` times the cap;
* `dgN_downupEF_le`: `crossl j i ≫ crossr j i = t_{ij} · 1` on `E_j F_i 1_ν` for `⟨i, ν⟩ ≤ 2`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k] {S : CLScalars C k}

theorem wt_dn_up (ν : X) (i : I) : wt RD ν [dn i, up i] = ν := by
  simp only [wt_cons, wt_nil, sh, up, dn, sgn]; simp

theorem wt_up_dn (ν : X) (i : I) : wt RD ν [up i, dn i] = ν := by
  simp only [wt_cons, wt_nil, sh, up, dn, sgn]; simp

/-- Placing a normal-form diagram to the right of `u` and composing with a normal-form diagram. -/
theorem plcLC_dg_comp (P : Presentation.{w, max u v} (psig RD) k) (μ : X)
    (u s t t₀ : List (Letter I)) (A B : List (LayerData I)) (hA : SChain s A t)
    (hB : SChain (u ++ t ++ []) B t₀) :
    plcLC P μ u [] s t (dgC P μ s t A) ≫ dgC P μ (u ++ t ++ []) t₀ B =
      dgC P μ (u ++ s ++ []) t₀ (A.map (whL u []) ++ B) := by
  rw [plcLC_dg_nil]
  exact dgC_comp (hA.whisk u []) hB

/-- The strand `j` passing both legs of the cap `F_i E_i ⟶ 1` (left adjunction): the sideways
crossing `crossl j i` on the left leg, then the upward crossing `τ_{ji}` on the right leg. -/
def capTurnLs (i j : I) : List (LayerData I) :=
  (crosslL j i).map (whL [] [up i]) ++ [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]

variable (hr : ∀ c, S.r c = 1)
include hr

/-- **Brundan (5.2), `⟨i, λ⟩ ≤ 0`, composed with `σ`** (proof of Lemma 5.2): the strand `j`
passing both legs of the cap `F_i E_i ⟶ 1` equals `t_{ij}` times the cap, without using any
mixed relation. The components of this identity along the decomposition
`F_i E_i 1_λ ≅ E_i F_i 1_λ ⊕ 1_λ^{⊕(-⟨i,λ⟩)}` are `dgN_turn1`, `dgN_turn2`. -/
theorem dgN_capTurn {i j : I} (hij : i ≠ j) (lam : X) (h : ip RD i lam ≤ 0) :
    dgC (presNM RD k S) lam [up j, dn i, up i] [up j] (capTurnLs i j) =
      (S.t i j : k) • dgC (presNM RD k S) lam [up j, dn i, up i] [up j]
        [([up j], .cap (up i), [])] := by
  set D := dgC (presNM RD k S) lam [up j, dn i, up i] [up j] (capTurnLs i j) -
      (S.t i j : k) • dgC (presNM RD k S) lam [up j, dn i, up i] [up j]
        [([up j], .cap (up i), [])] with hD
  rw [← sub_eq_zero, ← hD]
  have hx0 : plcLC (presNM RD k S) lam [up j] [] [up i, dn i] [dn i, up i]
      (dgC (presNM RD k S) lam [up i, dn i] [dn i, up i] (crosslL i i)) ≫ D = 0 := by
    have e1 := plcLC_dg_comp (presNM RD k S) lam [up j] [up i, dn i] [dn i, up i] [up j]
      (crosslL i i) (capTurnLs i j) (by schain) (by schain)
    have e2 := plcLC_dg_comp (presNM RD k S) lam [up j] [up i, dn i] [dn i, up i] [up j]
      (crosslL i i) [([up j], .cap (up i), [])] (by schain) (by schain)
    rw [hD, Preadditive.comp_sub, Linear.comp_smul]
    erw [e1, e2]
    rw [sub_eq_zero]
    have := dgN_turn1 hr hij lam h
    simpa only [capTurnLs, curlALs, List.map_append, List.append_assoc, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, whL, List.append_nil] using this
  have hxm : ∀ m : ℕ, (m : ℤ) < -ip RD i lam →
      plcLC (presNM RD k S) lam [up j] [] [] [dn i, up i]
        (dgC (presNM RD k S) lam [] [dn i, up i] (cupDotFELs i m)) ≫ D = 0 := by
    intro m hm
    have e1 := plcLC_dg_comp (presNM RD k S) lam [up j] [] [dn i, up i] [up j]
      (cupDotFELs i m) (capTurnLs i j) (by schain) (by schain)
    have e2 := plcLC_dg_comp (presNM RD k S) lam [up j] [] [dn i, up i] [up j]
      (cupDotFELs i m) [([up j], .cap (up i), [])] (by schain) (by schain)
    rw [hD, Preadditive.comp_sub, Linear.comp_smul]
    erw [e1, e2]
    rw [sub_eq_zero]
    have := dgN_turn2 hr hij lam m hm
    simpa only [capTurnLs, cupDotFELs, List.map_append, List.append_assoc, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, whL, List.append_nil,
      List.map_replicate] using this
  have hw1 : wt RD (wt RD lam []) [up i, dn i] = wt RD (wt RD lam []) [dn i, up i] := by
    rw [wt_up_dn, wt_dn_up]
  have hw2 : wt RD (wt RD lam []) [] = wt RD (wt RD lam []) [dn i, up i] := by
    rw [wt_dn_up, wt_nil]
  have hw3 : wt RD (wt RD lam []) [dn i, up i] = wt RD (wt RD lam []) [] := hw2.symm
  calc D = plcLC (presNM RD k S) lam [up j] [] [dn i, up i] [dn i, up i] (𝟙 _) ≫ D := by
        rw [plcLC_id, Category.id_comp]
    _ = 0 := by
      rw [show (𝟙 ((presNM RD k S).obj (ob RD (wt RD lam []) [dn i, up i]))) =
        dgC (presNM RD k S) lam [dn i, up i] [dn i, up i] [] from (dgC_nil lam _).symm]
      rw [dgN_decompFE hr i lam, map_add, map_neg,
        Preadditive.add_comp, Preadditive.neg_comp, ← dgC_comp (t := [up i, dn i]) (by schain)
          (by schain)]
      have c1 := plcLC_comp (presNM RD k S) lam [up j] [] hw1 hw1.symm
        (dgC (presNM RD k S) lam [dn i, up i] [up i, dn i] (crossrL i i))
        (dgC (presNM RD k S) lam [up i, dn i] [dn i, up i] (crosslL i i))
      erw [← c1]
      rw [Category.assoc, hx0, Limits.comp_zero, neg_zero, zero_add, map_sum,
        Preadditive.sum_comp]
      refine Finset.sum_eq_zero fun f hf => ?_
      rw [map_sum, Preadditive.sum_comp]
      refine Finset.sum_eq_zero fun g _ => ?_
      have c2 := plcLC_comp (presNM RD k S) lam [up j] [] hw2 hw3
        (dgC (presNM RD k S) lam [dn i, up i] [] (dotCapFELs i (f - g)))
        (cwN S lam i (ip RD i lam - 1 + g) ≫
          dgC (presNM RD k S) lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - f)))
      have c3 := plcLC_comp (presNM RD k S) lam [up j] [] rfl hw3
        (cwN S lam i (ip RD i lam - 1 + g))
        (dgC (presNM RD k S) lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - f)))
      erw [← c2, ← c3]
      rw [Category.assoc, Category.assoc, hxm _ (by have := Finset.mem_range.1 hf; omega),
        Limits.comp_zero, Limits.comp_zero]


/-! ## The turn relations for `⟨i, λ⟩ ≥ d_{ij}`: the first relation -/

omit hr in
theorem dgC_comp_ctxLC {P : Presentation.{w, max u v} (psig RD) k} {μ : X}
    {s₁ s₀ t₀ : List (Letter I)} {L pre post : List (LayerData I)} {u v s t : List (Letter I)}
    (hL : SChain s₁ L s₀) (hpre : SChain s₀ pre (u ++ s ++ v))
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    dgC P μ s₁ s₀ L ≫ ctxLC P μ s₀ t₀ pre u v post s t f =
      ctxLC P μ s₁ t₀ (L ++ pre) u v post s t f := by
  simp only [ctxLC, LinearMap.coe_mk, AddHom.coe_mk, ← Category.assoc, dgC_comp hL hpre]

omit hr in
/-- A monomial of the correction term of `dgN_lurk` (labels `a = j`, `b = i`), with the cup
`1 ⟶ E_i F_i` attached at the bottom right: the clockwise bubble with the dots of the right
strand `i`, at the far right. -/
theorem dgN_lurkCup_mono (i j : I) (lam : X) (a b c : ℕ) :
    dgC (presNM RD k S) lam [up j] [up j, up i, dn i] [([up j], .cup (up i), [])] ≫
      ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
        [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
        [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
        (lurkY i j lam 0 ^ a * lurkY i j lam 1 ^ b * lurkY i j lam 2 ^ c) =
    dgC (presNM RD k S) lam [up j] [dn i, up i, up j]
      ([([], .cup (dn i), [up j])] ++ List.replicate b ([dn i, up i], .dot (up j), []) ++
        List.replicate a ([dn i], .dot (up i), [up j]) ++
        (cwUpLs i c).map (whL [dn i, up i, up j] [])) := by
  simp only [lurkY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [dgC_pow _ _ _ (by schain), dgC_pow _ _ _ (by schain), dgC_pow _ _ _ (by schain),
    dgC_mul3 _ _ _ _ _ (by schain) (by schain) (by schain), dgC_comp_ctxLC (by schain) (by schain),
    ctxLC_dg _ _ (by schain) (by schain)]
  -- swap the two cups
  rw [dgC_step_at _ 0 [] [] (dgC_swap (presNM RD k S) (wt RD lam []) [up j]
    [dn i, up i, up j, up i, dn i] [] [up j] [] (.cup (dn i)) (.cup (up i))).symm
    (by simp) (by simp only [Shape.dom, Shape.cod, Letter.dual_dn]; schain) (by simp [whL])]
  simp only [Shape.dom, Shape.cod, List.take_zero, List.length_cons, List.length_nil, zero_add,
    List.drop_succ_cons, List.drop_zero, List.nil_append, List.cons_append, Letter.dual_dn,
    List.singleton_append]
  have h1 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j])
    (T := [dn i, up i, up j])
    ([([], .cup (dn i), [up j]), ([dn i, up i, up j], .cup (up i), [])] ++
      List.replicate c ([dn i, up i, up j], .dot (up i), [dn i])) []
    (s := [dn i, up i, up j]) (s' := [dn i, up i, up j]) (t := [up i, dn i]) (t' := [])
    (A := List.replicate b ([dn i, up i], .dot (up j), []) ++
      List.replicate a ([dn i], .dot (up i), [up j]))
    (B := [([], .cap (dn i), [])]) (by schain) (by schain)
  have h2 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j])
    (T := [dn i, up i, up j])
    [([], .cup (dn i), [up j])] [] (s := [dn i, up i, up j]) (s' := [dn i, up i, up j])
    (t := []) (t' := [])
    (A := List.replicate b ([dn i, up i], .dot (up j), []) ++
      List.replicate a ([dn i], .dot (up i), [up j]))
    (B := cwUpLs i c) (by schain) (by unfold cwUpLs; schain)
  simp only [cwUpLs, List.map_append, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.append_assoc, List.nil_append, List.cons_append, List.append_nil] at h1 h2 ⊢
  rw [h1, ← h2]


/-- The correction term of `dgN_lurk` (labels `a = j`, `b = i`) with the cup `1 ⟶ E_i F_i`
attached at the bottom right, as a `k`-linear function of the polynomial. -/
def lurkCupF (i j : I) (lam : X) :
    MvPolynomial (Fin 3) k →ₗ[k] ((presNM RD k S).obj (ob RD lam [up j]) ⟶
      (presNM RD k S).obj (ob RD lam [dn i, up i, up j])) where
  toFun p := dgC (presNM RD k S) lam [up j] [up j, up i, dn i] [([up j], .cup (up i), [])] ≫
      ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
        [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
        [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
        (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up i, up j, up i])))
          (lurkY i j lam) p)
  map_add' p q := by rw [ncEvalB_add, map_add, Preadditive.comp_add]
  map_smul' c p := by
    rw [MvPolynomial.smul_eq_C_mul, ncEval_C_mul', ← Algebra.smul_def, map_smul, Linear.comp_smul]
    rfl

omit hr in
theorem lurkCupF_X3 (i j : I) (lam : X) (a b c : ℕ) (hc : (c : ℤ) ≤ ip RD i lam - 1) :
    lurkCupF (RD := RD) (S := S) i j lam
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c) =
      if (c : ℤ) = ip RD i lam - 1 then
        dgC (presNM RD k S) lam [up j] [dn i, up i, up j]
          ([([], .cup (dn i), [up j])] ++ List.replicate b ([dn i, up i], .dot (up j), []) ++
            List.replicate a ([dn i], .dot (up i), [up j]))
      else 0 := by
  show dgC _ _ _ _ _ ≫ ctxLC _ _ _ _ _ _ _ _ _ _ (KLR.ncEval (A := End ((presNM RD k S).obj
    (ob RD (wt RD lam [dn i]) [up i, up j, up i]))) (lurkY i j lam) _) = _
  rw [ncEval_X3, dgN_lurkCup_mono]
  split_ifs with h
  · have e : c = (ip RD i lam - 1).toNat := by omega
    subst e
    exact dgN_cwUpRight_one _ i _ (by omega) (by schain)
  · exact dgN_cwUpRight_zero _ i _ _ (by omega) (by schain)

omit hr in
/-- **The correction term of `dgN_lurk` with a cup at the bottom right**, in a region with
`⟨i, λ⟩ ≥ d_{ij}`: `t_{ij}` times the cup `1 ⟶ F_i E_i` if `⟨i, λ⟩ = d_{ij}` and `i · j ≠ 0`,
and `0` otherwise. -/
theorem dgN_lurkCup {i j : I} (hij : i ≠ j) (lam : X) (h : (C.dij i j : ℤ) ≤ ip RD i lam) :
    lurkCupF (RD := RD) (S := S) i j lam (KLR.qbar (qCL S i j)) =
      if ip RD i lam = C.dij i j ∧ C.dot i j ≠ 0 then
        (S.t i j : k) • dgC (presNM RD k S) lam [up j] [dn i, up i, up j] [([], .cup (dn i), [up j])]
      else 0 := by
  by_cases hd : C.dot i j = 0
  · rw [qCL_of_dot_eq_zero S hd, qbar_C, map_zero, ite_eq_right_iff.2 (fun h' => (h'.2 hd).elim)]
  have hdpos := C.dij_pos hij hd
  rw [qbar_qCL S hij hd, map_add, MvPolynomial.C_mul', map_smul]
  simp only [map_sum]
  have hX : ∀ l : ℕ × ℕ, (MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2 : MvPolynomial (Fin 3) k) =
      MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 1 ^ 0 * MvPolynomial.X 2 ^ l.2 := fun l => by ring
  have hmem : ∀ {n : ℕ} {l : ℕ × ℕ}, l ∈ Finset.HasAntidiagonal.antidiagonal n → l.1 + l.2 = n :=
    fun hl => Finset.HasAntidiagonal.mem_antidiagonal.1 hl
  have hs : (∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      lurkCupF (RD := RD) (S := S) i j lam
        (if C.dot i i * p + C.dot j j * q = -2 * C.dot i j then
          MvPolynomial.C (S.s i j p q) * MvPolynomial.X 1 ^ q *
            ∑ l ∈ Finset.HasAntidiagonal.antidiagonal (p - 1),
              MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2
        else 0)) = 0 := by
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have hp' := Finset.mem_range.1 hp
    have hq' := Finset.mem_range.1 hq
    split_ifs with hcond
    · have hp0 : p ≠ 0 := by
        rintro rfl
        have hm := C.dij_mul hij.symm
        rw [C.symm j i] at hm
        have hpos := C.dot_self_pos j
        have : C.dot j j * ((q : ℤ) - C.dij j i) = 0 := by push_cast at hcond; linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · omega
        · omega
      rw [mul_assoc, MvPolynomial.C_mul', Finset.mul_sum, map_smul, map_sum]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun l hl => ?_)
      have hl' := hmem hl
      rw [show (MvPolynomial.X 1 ^ q * (MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2) :
          MvPolynomial (Fin 3) k) = MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 1 ^ q *
            MvPolynomial.X 2 ^ l.2 by ring, lurkCupF_X3 i j lam _ _ _ (by omega),
        ite_eq_right (by omega)]
    · exact map_zero _
  rw [hs, add_zero]
  simp_rw [hX]
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [Finset.sum_eq_zero fun l hl => by
      rw [lurkCupF_X3 i j lam _ _ _ (by have := hmem hl; omega),
        ite_eq_right (by have := hmem hl; omega)],
      smul_zero, ite_eq_right (by omega)]
  · rw [ite_eq_left ⟨heq.symm, hd⟩, Finset.sum_eq_single (0, C.dij i j - 1)]
    · rw [lurkCupF_X3 i j lam _ _ _ (by simp only; omega), ite_eq_left (by simp only; omega)]
      simp
    · intro l hl hne
      have hl' := hmem hl
      rw [lurkCupF_X3 i j lam _ _ _ (by omega), ite_eq_right]
      intro h'
      exact hne (Prod.ext (by simp only at h' ⊢; omega) (by simp only at h' ⊢; omega))
    · intro h'
      exact (h' (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp))).elim

/-- **Brundan, proof of (5.3), first relation** (the analogue of the first relation of (5.4) for
`⟨i, λ⟩ ≥ d_{ij}`): the cup `1 ⟶ E_i F_i` crossed by the strand `j` (the upward crossing `τ_{ji}`,
then the sideways crossing `crossl j i`), followed by the sideways crossing `crossl i i`, is
`t_{ij}` times the curl `σ ∘ η'` to the left of the strand `j`. -/
theorem dgN_turn1E {i j : I} (hij : i ≠ j) (lam : X) (h : (C.dij i j : ℤ) ≤ ip RD i lam) :
    dgC (presNM RD k S) lam [up j] [dn i, up i, up j]
      ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++
        (crosslL j i).map (whL [up i] []) ++ (crosslL i i).map (whL [] [up j])) =
    (S.t i j : k) • dgC (presNM RD k S) lam [up j] [dn i, up i, up j]
      ((curlBLs i).map (whL [] [up j])) := by
  have hw : ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_iX_ne hij]; ring
  -- the right-hand side
  have hR : dgC (presNM RD k S) lam [up j] [dn i, up i, up j] ((curlBLs i).map (whL [] [up j])) =
      if ip RD i lam = C.dij i j then
        -dgC (presNM RD k S) lam [up j] [dn i, up i, up j] [([], .cup (dn i), [up j])] else 0 := by
    split_ifs with h0
    · have E : dgC (presNM RD k S) (wt RD lam [up j]) [] [dn i, up i] (curlBLs i) =
          -dgC (presNM RD k S) (wt RD lam [up j]) [] [dn i, up i] [([], .cup (dn i), [])] :=
        dgN_curlB_zero hr i (wt RD lam [up j]) (by rw [hw, h0]; ring)
      rw [dgC_stepL (presNM RD k S) lam [] [] [] [up j] E (by schain) (by schain) (by simp),
        map_neg, ctxLC_dg _ _ (by schain) (by schain)]
      simp [whL]
    · have E : dgC (presNM RD k S) (wt RD lam [up j]) [] [dn i, up i] (curlBLs i) = 0 :=
        dgN_curlB_pos hr i _ (by rw [hw]; omega)
      rw [dgC_stepL (presNM RD k S) lam [] [] [] [up j] E (by schain) (by schain) (by simp),
        map_zero]
  rw [hR]
  -- the left-hand side: pull the strand `j` through the crossing `ψ_{ii}`
  have e0 : ([([up j], .cup (up i), []), ([], .cross true j i, [dn i])] : List (LayerData I)) ++
      (crosslL j i).map (whL [up i] []) ++ (crosslL i i).map (whL [] [up j]) =
      [([up j], .cup (up i), [])] ++ ([([], .cross true j i, [dn i])] ++
        (crosslL j i).map (whL [up i] []) ++ (crosslL i i).map (whL [] [up j])) := by simp
  rw [e0, ← dgC_comp (t := [up j, up i, dn i]) (by schain) (by schain),
    eq_sub_of_add_eq (dgN_lurk hr j i hij.symm lam).symm, Preadditive.comp_sub,
    dgC_comp (by schain) (by schain)]
  have hcorr : dgC (presNM RD k S) lam [up j] [up j, up i, dn i] [([up j], .cup (up i), [])] ≫
      ctxLC (presNM RD k S) lam [up j, up i, dn i] [dn i, up i, up j]
        [([], .cup (dn i), [up j, up i, dn i])] [dn i] [dn i]
        [([dn i, up i, up j], .cap (dn i), [])] [up i, up j, up i] [up i, up j, up i]
        (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i]) [up i, up j, up i])))
          ![dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [up i, up j, up i]
              [([], .dot (up i), [up j, up i])],
            dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [up i, up j, up i]
              [([up i], .dot (up j), [up i])],
            dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up j, up i] [up i, up j, up i]
              [([up i, up j], .dot (up i), [])]]
          (KLR.qbar (qCL S i j))) =
      lurkCupF (RD := RD) (S := S) i j lam (KLR.qbar (qCL S i j)) := rfl
  rw [hcorr, dgN_lurkCup hij lam h]
  -- the main term: the curl `σ ∘ η'` at the bottom
  have hP : dgC (presNM RD k S) lam [up j] [dn i, up i, up j]
      ([([up j], .cup (up i), [])] ++ ((crosslL i i).map (whL [up j] []) ++
        (crosslL j i).map (whL [] [up i]) ++ [([dn i], .cross true j i, [])])) =
      if ip RD i lam = 0 then
        -((S.t i j : k) • dgC (presNM RD k S) lam [up j] [dn i, up i, up j]
          [([], .cup (dn i), [up j])])
      else 0 := by
    have e1 : ([([up j], .cup (up i), [])] : List (LayerData I)) ++
        ((crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
          [([dn i], .cross true j i, [])]) =
        (curlBLs i).map (whL [up j] []) ++ ((crosslL j i).map (whL [] [up i]) ++
          [([dn i], .cross true j i, [])]) := by simp [curlBLs, whL]
    rw [e1]
    split_ifs with h0
    · have hd0 : C.dij i j = 0 := by omega
      have hd : C.dot i j = 0 := (C.dij_eq_zero_iff hij).1 hd0
      have E : dgC (presNM RD k S) (wt RD lam []) [] [dn i, up i] (curlBLs i) =
          -dgC (presNM RD k S) (wt RD lam []) [] [dn i, up i] [([], .cup (dn i), [])] :=
        dgN_curlB_zero hr i lam h0
      rw [dgC_stepL (presNM RD k S) lam [] ((crosslL j i).map (whL [] [up i]) ++
          [([dn i], .cross true j i, [])]) [up j] [] E (by schain)
          (by simp only [crosslL]; schain) (by simp), map_neg,
        ctxLC_dg _ _ (by schain) (by simp only [crosslL]; schain)]
      congr 1
      have E2 : dgC (presNM RD k S) (wt RD lam []) [up j] [dn i, up j, up i]
          ([([up j], .cup (dn i), [])] ++ (crosslL j i).map (whL [] [up i])) =
          dgC (presNM RD k S) (wt RD lam []) [up j] [dn i, up j, up i]
            [([], .cup (dn i), [up j]), ([dn i], .cross true i j, [])] :=
        dgN_pitchCup (RD := RD) (S := S) i j lam
      rw [dgC_step (presNM RD k S) lam [] [([dn i], .cross true j i, [])] [] [] E2 (by schain)
        (by schain) (by simp [whL]) rfl]
      have E3 : dgC (presNM RD k S) (wt RD lam []) [up i, up j] [up i, up j]
          [([], .cross true i j, []), ([], .cross true j i, [])] =
          (S.t i j : k) • dgC (presNM RD k S) (wt RD lam []) [up i, up j] [up i, up j] [] :=
        dgN_sqNe_zero (RD := RD) hr (wt RD lam []) hij hd
      rw [dgC_stepL (presNM RD k S) lam [([], .cup (dn i), [up j])] [] [dn i] [] E3 (by schain)
        (by schain) (by simp [whL]), map_smul, ctxLC_dg _ _ (by schain) (by schain)]
      simp [whL]
    · have E : dgC (presNM RD k S) (wt RD lam []) [] [dn i, up i] (curlBLs i) = 0 :=
        dgN_curlB_pos hr i lam (by omega)
      rw [dgC_stepL (presNM RD k S) lam [] ((crosslL j i).map (whL [] [up i]) ++
          [([dn i], .cross true j i, [])]) [up j] [] E (by schain)
          (by simp only [crosslL]; schain) (by simp), map_zero]
  rw [hP]
  by_cases hd : C.dot i j = 0
  · have hd0 : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 hd
    rw [ite_eq_right (show ¬(ip RD i lam = C.dij i j ∧ C.dot i j ≠ 0) from fun h' => h'.2 hd), sub_zero]
    by_cases h0 : ip RD i lam = 0
    · rw [ite_eq_left h0, ite_eq_left (show ip RD i lam = C.dij i j by omega), smul_neg]
    · rw [ite_eq_right h0, ite_eq_right (show ¬ ip RD i lam = C.dij i j by omega), smul_zero]
  · have hdpos := C.dij_pos hij hd
    rw [ite_eq_right (show ¬ ip RD i lam = 0 by omega), zero_sub]
    by_cases h0 : ip RD i lam = C.dij i j
    · rw [ite_eq_left (show ip RD i lam = C.dij i j ∧ C.dot i j ≠ 0 from ⟨h0, hd⟩), ite_eq_left h0,
        smul_neg]
    · rw [ite_eq_right (show ¬(ip RD i lam = C.dij i j ∧ C.dot i j ≠ 0) from fun h' => h0 h'.1),
        ite_eq_right h0, neg_zero, smul_zero]


/-- The cup `1 ⟶ E_i F_i` crossed by the strand `j`: the upward crossing `τ_{ji}`, then the
sideways crossing `crossl j i`. -/
def cupTurnLs (i j : I) : List (LayerData I) :=
  [([up j], .cup (up i), []), ([], .cross true j i, [dn i])] ++ (crosslL j i).map (whL [up i] [])

omit hr in
/-- Composing a normal-form diagram with a diagram placed to the left of `v`. -/
theorem dgC_comp_plcLC (P : Presentation.{w, max u v} (psig RD) k) (μ : X)
    (v s t s₀ : List (Letter I)) (A B : List (LayerData I)) (hB : SChain s₀ B ([] ++ s ++ v))
    (hA : SChain s A t) :
    dgC P μ s₀ ([] ++ s ++ v) B ≫ plcLC P μ [] v s t (dgC P (wt RD μ v) s t A) =
      dgC P μ s₀ ([] ++ t ++ v) (B ++ A.map (whL [] v)) := by
  rw [plcLC_dg]
  exact dgC_comp hB (hA.whisk [] v)

/-- **Brundan (5.3), `⟨i, λ⟩ ≥ d_{ij}`, composed with `σ`** (proof of Lemma 5.2): the cup
`1 ⟶ E_i F_i` crossed by the strand `j` is `t_{ij}` times the cup to the left of the strand,
without using any mixed relation. The components of this identity along the decomposition
`E_i F_i 1_{λ+α_j} ≅ F_i E_i 1_{λ+α_j} ⊕ 1^{⊕(⟨i,λ⟩-d_{ij})}` are `dgN_turn1E`, `dgN_turn2E`. -/
theorem dgN_cupTurn {i j : I} (hij : i ≠ j) (lam : X) (h : (C.dij i j : ℤ) ≤ ip RD i lam) :
    dgC (presNM RD k S) lam [up j] [up i, dn i, up j] (cupTurnLs i j) =
      (S.t i j : k) • dgC (presNM RD k S) lam [up j] [up i, dn i, up j]
        [([], .cup (up i), [up j])] := by
  set D := dgC (presNM RD k S) lam [up j] [up i, dn i, up j] (cupTurnLs i j) -
      (S.t i j : k) • dgC (presNM RD k S) lam [up j] [up i, dn i, up j]
        [([], .cup (up i), [up j])] with hD
  rw [← sub_eq_zero, ← hD]
  have hw : ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_iX_ne hij]; ring
  have hy0 : D ≫ plcLC (presNM RD k S) lam [] [up j] [up i, dn i] [dn i, up i]
      (dgC (presNM RD k S) (wt RD lam [up j]) [up i, dn i] [dn i, up i] (crosslL i i)) = 0 := by
    have e1 := dgC_comp_plcLC (presNM RD k S) lam [up j] [up i, dn i] [dn i, up i] [up j]
      (crosslL i i) (cupTurnLs i j) (by unfold cupTurnLs; schain) (by schain)
    have e2 := dgC_comp_plcLC (presNM RD k S) lam [up j] [up i, dn i] [dn i, up i] [up j]
      (crosslL i i) [([], .cup (up i), [up j])] (by schain) (by schain)
    rw [hD, Preadditive.sub_comp, Linear.smul_comp]
    erw [e1, e2]
    rw [sub_eq_zero]
    have := dgN_turn1E hr hij lam h
    simpa only [cupTurnLs, curlBLs, List.map_append, List.append_assoc, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, whL, List.append_nil] using this
  have hym : ∀ m : ℕ, (m : ℤ) < ip RD i lam - C.dij i j →
      D ≫ plcLC (presNM RD k S) lam [] [up j] [up i, dn i] []
        (dgC (presNM RD k S) (wt RD lam [up j]) [up i, dn i] [] (dotCapEFLs i m)) = 0 := by
    intro m hm
    have e1 := dgC_comp_plcLC (presNM RD k S) lam [up j] [up i, dn i] [] [up j]
      (dotCapEFLs i m) (cupTurnLs i j) (by unfold cupTurnLs; schain)
      (by unfold dotCapEFLs; schain)
    have e2 := dgC_comp_plcLC (presNM RD k S) lam [up j] [up i, dn i] [] [up j]
      (dotCapEFLs i m) [([], .cup (up i), [up j])] (by schain) (by unfold dotCapEFLs; schain)
    rw [hD, Preadditive.sub_comp, Linear.smul_comp]
    erw [e1, e2]
    rw [sub_eq_zero]
    have := dgN_turn2E hr hij lam m hm
    simpa only [cupTurnLs, cwUpLs, dotCapEFLs, List.map_append, List.append_assoc, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, whL, List.append_nil,
      List.map_replicate] using this
  set ν := wt RD lam [up j]
  have hw1 : wt RD ν [dn i, up i] = wt RD ν [up i, dn i] := by rw [wt_up_dn, wt_dn_up]
  have hw2 : wt RD ν [] = wt RD ν [up i, dn i] := by rw [wt_up_dn, wt_nil]
  have hw3 : wt RD ν [up i, dn i] = wt RD ν [] := hw2.symm
  calc D = D ≫ plcLC (presNM RD k S) lam [] [up j] [up i, dn i] [up i, dn i] (𝟙 _) := by
        rw [plcLC_id]; exact (Category.comp_id D).symm
    _ = 0 := by
      rw [show (𝟙 ((presNM RD k S).obj (ob RD ν [up i, dn i]))) =
        dgC (presNM RD k S) ν [up i, dn i] [up i, dn i] [] from (dgC_nil ν _).symm]
      rw [dgN_decompEF hr i ν, map_add, map_neg, Preadditive.comp_add, Preadditive.comp_neg,
        ← dgC_comp (t := [dn i, up i]) (by schain) (by schain)]
      have c1 := plcLC_comp (presNM RD k S) lam [] [up j] hw1 hw1.symm
        (dgC (presNM RD k S) ν [up i, dn i] [dn i, up i] (crosslL i i))
        (dgC (presNM RD k S) ν [dn i, up i] [up i, dn i] (crossrL i i))
      erw [← c1]
      rw [← Category.assoc, hy0, Limits.zero_comp, neg_zero, zero_add, map_sum,
        Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun f hf => ?_
      rw [map_sum, Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun g hg => ?_
      have c2 := plcLC_comp (presNM RD k S) lam [] [up j] hw2 hw3
        (dgC (presNM RD k S) ν [up i, dn i] [] (dotCapEFLs i (f - g)))
        (ccwN S ν i (-ip RD i ν - 1 + g) ≫
          dgC (presNM RD k S) ν [] [up i, dn i] (cupDotEFLs i ((ip RD i ν).toNat - 1 - f)))
      erw [← c2]
      rw [← Category.assoc, hym _ (by
        have := Finset.mem_range.1 hf; have := Finset.mem_range.1 hg; rw [← hw]; omega),
        Limits.zero_comp]

/-- **The other mixed relation from Brundan's Lemma 5.2** (`⟨i, ν⟩ ≥ d_{ij}`, without any mixed
relation): `crossr j i ≫ crossl j i = t_{ij} · 1` on `F_i E_j 1_ν`; the sideways crossing
`crossl j i` has the right inverse `t_{ij}^{-1} crossr j i`. -/
theorem dgN_downupFE_ge {i j : I} (hij : i ≠ j) (ν : X) (h : (C.dij i j : ℤ) ≤ ip RD i ν) :
    dgC (presNM RD k S) ν [dn i, up j] [dn i, up j] (crossrL j i ++ crosslL j i) =
      (S.t i j : k) • dgC (presNM RD k S) ν [dn i, up j] [dn i, up j] [] := by
  have e1 : crossrL j i ++ crosslL j i =
      [] ++ ([([dn i, up j], .cup (up i), []), ([dn i], .cross true j i, [dn i])] : List (LayerData I)) ++
        ([([], .cap (up i), [])] : List (LayerData I)).map (whL [] [up j, dn i]) ++
        (crosslL j i).map (whL [] []) ++ [] := by
    simp [crossrL, whL]
  rw [e1, dgC_interchange (P := presNM RD k S) _ []
    (s := [dn i, up i]) (s' := []) (t := [up j, dn i]) (t' := [dn i, up j])
    (A := [([], .cap (up i), [])]) (B := crosslL j i) (by schain) (by schain)]
  rw [dgC_stepL (presNM RD k S) ν [] [([], .cap (up i), [dn i, up j])] [dn i] []
    (dgN_cupTurn hr hij ν h) (by schain) (by schain)
    (by simp [cupTurnLs, crosslL, whL]), map_smul]
  erw [ctxLC_dg _ _ (by schain) (by schain)]
  congr 1
  rw [dgC_step (presNM RD k S) ν [] [] [] [up j] (dgC_zigR' _ (presNM_zigzags RD k S) _ (up i))
    (by schain) (by schain) (by simp [whL]) rfl]
  simp [dgC_nil]

/-- **One mixed relation from Brundan's Lemma 5.2** (`⟨i, ν - α_i⟩ ≤ 0`, without any mixed
relation): `crossl j i ≫ crossr j i = t_{ij} · 1` on `E_j F_i 1_ν`; the sideways crossing
`crossl j i` has the left inverse `t_{ij}^{-1} crossr j i`. -/
theorem dgN_downupEF_le {i j : I} (hij : i ≠ j) (ν : X) (h : ip RD i (wt RD ν [dn i]) ≤ 0) :
    dgC (presNM RD k S) ν [up j, dn i] [up j, dn i] (crosslL j i ++ crossrL j i) =
      (S.t i j : k) • dgC (presNM RD k S) ν [up j, dn i] [up j, dn i] [] := by
  have e1 : crosslL j i ++ crossrL j i =
      [] ++ (crosslL j i).map (whL [] []) ++
        ([([], .cup (up i), [])] : List (LayerData I)).map (whL [dn i, up j] []) ++
        [([dn i], .cross true j i, [dn i]), ([], .cap (up i), [up j, dn i])] := by
    simp [crossrL, whL]
  rw [e1, dgC_interchange (P := presNM RD k S) [] _ (s := [up j, dn i]) (s' := [dn i, up j])
    (t := []) (t' := [up i, dn i]) (A := crosslL j i) (B := [([], .cup (up i), [])]) (by schain)
    (by schain)]
  rw [dgC_stepL (presNM RD k S) ν [([up j, dn i], .cup (up i), [])] [] [] [dn i]
    (dgN_capTurn hr hij (wt RD ν [dn i]) h) (by schain) (by schain)
    (by simp [capTurnLs, crosslL, whL]), map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  congr 1
  rw [dgC_step (presNM RD k S) ν [] [] [up j] [] (dgC_zigR' _ (presNM_zigzags RD k S) _ (up i))
    (by schain) (by schain) (by simp [whL]) rfl]
  simp [dgC_nil]

end Categorification.KL3.Diagram.CL
