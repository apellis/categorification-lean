/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.BrundanMixed

/-!
# The mixed relation in the intermediate weights

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, proof of Lemma 5.2,
the case `0 < ⟨h_i, λ⟩ < d_{ij}` (relation (5.5)): composed with the sideways crossing `σ`, the
relation (5.2) is proved directly, without the inverse of `σ`, in `U_Q(g)` without the mixed
relations (`presNM`). This completes `Categorification.Diagrams.CL.BrundanMixed`: at every weight
the sideways crossing `crossl j i` has a one-sided inverse.

## Main results

* `dgN_dotCurl`: the sideways crossing `crossr i i`, `c` dots, and the cap `E_i F_i ⟶ 1`, in a
  region with `⟨i, λ⟩ ≥ 1`: zero for `c < ⟨i, λ⟩`, minus the cap `F_i E_i ⟶ 1` for
  `c = ⟨i, λ⟩` (Brundan (3.6), (3.7), (4.4), (4.8));
* `dgN_capTurn_mid`, `dgN_downupEF_mid`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k] {S : CLScalars C k}

omit [AddCommGroup X] [AddCommGroup Y] in
theorem map_whL_nil (l : List (LayerData I)) : l.map (whL [] []) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- The sideways crossing `crossr i i : F_i E_i ⟶ E_i F_i`, `c` dots on the upward strand, then
the cap `E_i F_i ⟶ 1`. -/
def dotCurlLs (i : I) (c : ℕ) : List (LayerData I) :=
  crossrL i i ++ List.replicate c ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]

/-- `dotCurlLs` with the cap of `crossr i i` moved to the end. -/
def dotCurlNLs (i : I) (c : ℕ) : List (LayerData I) :=
  [([dn i, up i], .cup (up i), []), ([dn i], .cross true i i, [dn i])] ++
    List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
    [([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])]

theorem dgN_dotCurl_nf (lam : X) (i : I) (c : ℕ) :
    dgC (presNM RD k S) lam [dn i, up i] [] (dotCurlLs i c) =
      dgC (presNM RD k S) lam [dn i, up i] [] (dotCurlNLs i c) := by
  have h1 := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [dn i, up i]) (T := [])
    [([dn i, up i], .cup (up i), []), ([dn i], .cross true i i, [dn i])] []
    (s := [dn i, up i]) (s' := []) (t := [up i, dn i]) (t' := [])
    (A := [([], .cap (up i), [])])
    (B := List.replicate c ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])])
    (by schain) (by schain)
  simp only [dotCurlLs, dotCurlNLs, crossrL, List.map_append, List.map_replicate, List.map_cons,
    List.map_nil, whL, List.append_assoc, List.nil_append, List.cons_append,
    List.append_nil] at h1 ⊢
  exact h1

variable (hr : ∀ c, S.r c = 1)
include hr

theorem dgN_dotCurlN (lam : X) (i : I) (h1 : 1 ≤ ip RD i lam) :
    ∀ c : ℕ, (c : ℤ) ≤ ip RD i lam →
      dgC (presNM RD k S) lam [dn i, up i] [] (dotCurlNLs i c) =
        if (c : ℤ) = ip RD i lam then
          -dgC (presNM RD k S) lam [dn i, up i] [] [([], .cap (up i), [])]
        else 0
  | 0, _ => by
    rw [ite_eq_right (show ¬((0 : ℕ) : ℤ) = ip RD i lam by push_cast; omega)]
    have E : dgC (presNM RD k S) (wt RD lam []) [up i] [up i]
        [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] =
        0 := by
      have E' := dgN_curlR (RD := RD) (S := S) hr i lam
      rw [show (-ip RD i lam + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero] at E'
      exact E'
    exact dgC_eq_zero_at _ 0 [dn i] [] E (by simp [dotCurlNLs])
      (by simp only [dotCurlNLs]; dnorm; schain) (by simp [dotCurlNLs, whL])
  | c + 1, hc => by
    have ih := dgN_dotCurlN lam i h1 c (by push_cast at hc; omega)
    rw [ite_eq_right (show ¬((c : ℕ) : ℤ) = ip RD i lam by push_cast at hc ⊢; omega)] at ih
    have E : dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up i] [up i, up i]
        [([], .cross true i i, []), ([up i], .dot (up i), [])] =
        dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up i] [up i, up i]
          [([], .dot (up i), [up i]), ([], .cross true i i, [])] -
        dgC (presNM RD k S) (wt RD lam [dn i]) [up i, up i] [up i, up i] [] :=
      eq_sub_of_add_eq (dgC_slideREq (presNM_klr hr) _ i).symm
    have e0 : dotCurlNLs i (c + 1) =
        [([dn i, up i], .cup (up i), []), ([dn i], .cross true i i, [dn i]),
          ([dn i, up i], .dot (up i), [dn i])] ++
          List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
          [([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])] := by
      simp [dotCurlNLs, List.replicate_succ]
    rw [e0, dgC_stepL_at _ 1 [dn i] [dn i] E (by dnorm; schain) (by dnorm; schain) (by dnorm),
      map_sub, ctxLC_dg _ _ (by dnorm; schain) (by dnorm; schain),
      ctxLC_dg _ _ (by dnorm; schain) (by dnorm; schain)]
    dnorm
    -- the first term: the dot slides below the cup and the induction hypothesis applies
    have t1 : dgC (presNM RD k S) lam [dn i, up i] []
        (([dn i, up i], .cup (up i), []) :: ([dn i], .dot (up i), [up i, dn i]) ::
          ([dn i], .cross true i i, [dn i]) ::
          (List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
            [([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])])) = 0 := by
      dswapC 0
      have e1 : (([dn i], .dot (up i), []) :: ([dn i, up i], .cup (up i), []) ::
          ([dn i], .cross true i i, [dn i]) ::
          (List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
            [([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])]) : List (LayerData I)) =
          [([dn i], .dot (up i), [])] ++ dotCurlNLs i c := by
        simp [dotCurlNLs]
      rw [e1, ← dgC_comp (t := [dn i, up i]) (by schain)
        (by simp only [dotCurlNLs]; schain), ih, Limits.comp_zero]
    have t2e : (([dn i, up i], .cup (up i), []) ::
        (List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
          [([dn i, up i], .cap (dn i), []), ([], .cap (up i), [])]) : List (LayerData I)) =
        [] ++ (cwUpLs i c).map (whL [dn i, up i] []) ++ [([], .cap (up i), [])] := by
      simp [cwUpLs, whL, List.map_replicate]
    rw [t1, zero_sub, t2e]
    by_cases hb : (c : ℤ) = ip RD i lam - 1
    · rw [ite_eq_left (by push_cast; omega)]
      have E2 : dgC (presNM RD k S) (wt RD lam []) [] [] (cwUpLs i c) =
          dgC (presNM RD k S) (wt RD lam []) [] [] [] := by
        rw [show c = (ip RD i lam - 1).toNat by omega]
        exact (dgN_cwUp _ i _).trans (dgN_cwOne S _ i h1)
      rw [dgC_step (presNM RD k S) lam [] [([], .cap (up i), [])] [dn i, up i] [] E2
        (by schain) (by schain) rfl rfl]
      simp
    · rw [ite_eq_right (by push_cast; omega), neg_eq_zero]
      have E2 : dgC (presNM RD k S) (wt RD lam []) [] [] (cwUpLs i c) = 0 :=
        (dgN_cwUp _ i _).trans (dgN_cwNeg S _ i c (by rw [wt_nil]; push_cast at hc; omega))
      rw [dgC_stepL (presNM RD k S) lam [] [([], .cap (up i), [])] [dn i, up i] [] E2
        (by schain) (by schain) rfl, map_zero]

/-- **The dotted curl** (Brundan (3.6), (3.7) and (4.8), `⟨i, λ⟩ ≥ 1`): the sideways crossing
`crossr i i`, `c ≤ ⟨i, λ⟩` dots on the upward strand and the cap `E_i F_i ⟶ 1` give `0` for
`c < ⟨i, λ⟩` and minus the cap `F_i E_i ⟶ 1` for `c = ⟨i, λ⟩`. -/
theorem dgN_dotCurl (lam : X) (i : I) (h1 : 1 ≤ ip RD i lam) (c : ℕ) (hc : (c : ℤ) ≤ ip RD i lam) :
    dgC (presNM RD k S) lam [dn i, up i] [] (dotCurlLs i c) =
      if (c : ℤ) = ip RD i lam then
        -dgC (presNM RD k S) lam [dn i, up i] [] [([], .cap (up i), [])]
      else 0 := by
  rw [dgN_dotCurl_nf, dgN_dotCurlN hr lam i h1 c hc]

/-- The left-hand side of `dgN_turn1` in any region with `⟨i, λ⟩ < d_{ij}`: only the correction
term of `dgN_lurk` survives. -/
theorem dgN_crosslCapTurn {i j : I} (hij : i ≠ j) (lam : X) (h : ip RD i lam < C.dij i j) :
    dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
      ((crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
        [([dn i], .cross true j i, []), ([], .cap (up i), [up j])]) =
    lurkCapF (RD := RD) (S := S) i j lam (KLR.qbar (qCL S i j)) := by
  have hsplit : (crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
      [([dn i], .cross true j i, []), ([], .cap (up i), [up j])] =
      ((crosslL i i).map (whL [up j] []) ++ (crosslL j i).map (whL [] [up i]) ++
        [([dn i], .cross true j i, [])]) ++ [([], .cap (up i), [up j])] := by simp
  rw [hsplit, ← dgC_comp (t := [dn i, up i, up j]) (by dnorm; schain) (by schain),
    dgN_lurk hr j i hij.symm lam, Preadditive.add_comp, dgC_comp (by dnorm; schain) (by schain)]
  have hw : ip RD i (wt RD lam [up j]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_iX_ne hij]; ring
  have E : dgC (presNM RD k S) (wt RD lam [up j]) [up i, dn i] [] (curlALs i) = 0 :=
    dgN_curlA_neg hr i _ (by rw [hw]; omega)
  rw [dgC_eq_zero_at _ 4 [] [up j] E (by (try simp only [curlALs, crosslL]); dnorm; schain)
    (by (try simp only [curlALs, crosslL]); dnorm; schain) (by (try simp only [curlALs]); dnorm),
    zero_add]
  rfl

/-- A monomial of the correction term of `dgN_lurk`, capped by `F_i E_i ⟶ 1` and composed with
`crossr i i` at the bottom (Brundan, proof of (5.5)): only the term with `d_{ij} - ⟨i, λ⟩ - 1`
dots on the bubble and `⟨i, λ⟩` dots in the curl survives. -/
theorem dgN_crossrLurk_mono {i j : I} (hij : i ≠ j) (lam : X) (h1 : 1 ≤ ip RD i lam)
    (a b c : ℕ) (hac : ((a + c : ℕ) : ℤ) ≤ C.dij i j - 1) :
    dgC (presNM RD k S) lam [up j, dn i, up i] [up j]
      ((crossrL i i).map (whL [up j] []) ++ ((ccwLs i a).map (whL [] [up j, up i, dn i]) ++
        List.replicate c ([up j], .dot (up i), [dn i]) ++
        List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])])) =
    if (a : ℤ) = C.dij i j - ip RD i lam - 1 ∧ (c : ℤ) = ip RD i lam then
      -dgC (presNM RD k S) lam [up j, dn i, up i] [up j]
        ([([up j], .cap (up i), [])] ++ List.replicate b ([], .dot (up j), []))
    else 0 := by
  have h1' := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j, dn i, up i])
    (T := [up j]) []
    (List.replicate c ([up j], .dot (up i), [dn i]) ++
      List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])])
    (s := []) (s' := []) (t := [up j, dn i, up i]) (t' := [up j, up i, dn i])
    (A := ccwLs i a) (B := (crossrL i i).map (whL [up j] [])) (sChain_ccwLs i a)
    (by simp only [crossrL]; schain)
  have h2' := dgC_interchange (P := presNM RD k S) (μ := lam) (S := [up j, dn i, up i])
    (T := [up j])
    ((ccwLs i a).map (whL [] [up j, dn i, up i]) ++ (crossrL i i).map (whL [up j] []) ++
      List.replicate c ([up j], .dot (up i), [dn i])) []
    (s := [up j]) (s' := [up j]) (t := [up i, dn i]) (t' := [])
    (A := List.replicate b ([], .dot (up j), [])) (B := [([], .cap (dn i), [])])
    (by schain) (by schain)
  have eA : (crossrL i i).map (whL [up j] []) ++ ((ccwLs i a).map (whL [] [up j, up i, dn i]) ++
      List.replicate c ([up j], .dot (up i), [dn i]) ++
      List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])]) =
      [] ++ ((crossrL i i).map (whL [up j] [])).map (whL [] []) ++
        (ccwLs i a).map (whL [] [up j, up i, dn i]) ++
        (List.replicate c ([up j], .dot (up i), [dn i]) ++
          List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])]) := by
    simp [map_whL_nil]
  rw [eA, ← h1']
  have eB : [] ++ (ccwLs i a).map (whL [] [up j, dn i, up i]) ++
      ((crossrL i i).map (whL [up j] [])).map (whL [] []) ++
      (List.replicate c ([up j], .dot (up i), [dn i]) ++
        List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])]) =
      ((ccwLs i a).map (whL [] [up j, dn i, up i]) ++ (crossrL i i).map (whL [up j] []) ++
        List.replicate c ([up j], .dot (up i), [dn i])) ++
        (List.replicate b ([], .dot (up j), [])).map (whL [] [up i, dn i]) ++
        ([([], .cap (dn i), [])] : List (LayerData I)).map (whL [up j] []) ++ [] := by
    simp [map_whL_nil, whL, List.map_replicate]
  rw [eB, h2']
  have eC : ((ccwLs i a).map (whL [] [up j, dn i, up i]) ++ (crossrL i i).map (whL [up j] []) ++
        List.replicate c ([up j], .dot (up i), [dn i])) ++
        ([([], .cap (dn i), [])] : List (LayerData I)).map (whL [up j] []) ++
        (List.replicate b ([], .dot (up j), [])).map (whL [] []) ++ [] =
      (ccwLs i a).map (whL [] [up j, dn i, up i]) ++
        ((dotCurlLs i c).map (whL [up j] []) ++ List.replicate b ([], .dot (up j), [])) := by
    simp [map_whL_nil, whL, dotCurlLs, List.map_replicate]
  rw [eC]
  have hw : ip RD i (wt RD lam [up j, dn i, up i]) = ip RD i lam - C.dij i j := by
    simp only [wt_cons, wt_nil, ip_up, ip_dn, ip_iX_ne hij, ip_iX_self]; ring
  have hrest : SChain [up j, dn i, up i]
      ((dotCurlLs i c).map (whL [up j] []) ++ List.replicate b ([], .dot (up j), [])) [up j] := by
    simp only [dotCurlLs, crossrL]; schain
  by_cases hc : (c : ℤ) < ip RD i lam
  · rw [ite_eq_right (fun h' => by omega)]
    have E : dgC (presNM RD k S) (wt RD lam []) [dn i, up i] [] (dotCurlLs i c) = 0 :=
      (dgN_dotCurl hr lam i h1 c hc.le).trans (ite_eq_right (by omega))
    rw [dgC_stepL (presNM RD k S) lam ((ccwLs i a).map (whL [] [up j, dn i, up i]))
      (List.replicate b ([], .dot (up j), [])) [up j] [] E
      (by simpa using (sChain_ccwLs i a).whisk [] [up j, dn i, up i]) (by schain)
      (by simp), map_zero]
  · rw [not_lt] at hc
    by_cases ha : (a : ℤ) < C.dij i j - ip RD i lam - 1
    · rw [ite_eq_right (fun h' => by omega)]
      exact dgN_ccwLeft_zero _ i a _ (by rw [hw]; omega) hrest
    · have ha' : (a : ℤ) = C.dij i j - ip RD i lam - 1 := by push_cast at hac; omega
      have hc' : (c : ℤ) = ip RD i lam := by push_cast at hac; omega
      rw [ite_eq_left ⟨ha', hc'⟩, show a = (-ip RD i (wt RD lam [up j, dn i, up i]) - 1).toNat by
        rw [hw]; omega, dgN_ccwLeft_one _ i _ (by rw [hw]; omega) hrest]
      have E : dgC (presNM RD k S) (wt RD lam []) [dn i, up i] [] (dotCurlLs i c) =
          -dgC (presNM RD k S) (wt RD lam []) [dn i, up i] [] [([], .cap (up i), [])] := by
        exact (dgN_dotCurl hr lam i h1 c hc'.le).trans (ite_eq_left hc')
      rw [dgC_stepL (presNM RD k S) lam [] (List.replicate b ([], .dot (up j), [])) [up j] [] E
        (by schain) (by schain) (by simp), map_neg, ctxLC_dg _ _ (by schain) (by schain)]
      simp [whL]

/-- `crossr i i` composed with a monomial of the capped correction term of `dgN_lurk`. -/
theorem dgN_crossrLurkCapF_mono {i j : I} (hij : i ≠ j) (lam : X) (h1 : 1 ≤ ip RD i lam)
    (a b c : ℕ) (hac : ((a + c : ℕ) : ℤ) ≤ C.dij i j - 1) :
    plcLC (presNM RD k S) lam [up j] [] [dn i, up i] [up i, dn i]
        (dgC (presNM RD k S) lam [dn i, up i] [up i, dn i] (crossrL i i)) ≫
      lurkCapF (RD := RD) (S := S) i j lam
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c) =
    if (a : ℤ) = C.dij i j - ip RD i lam - 1 ∧ (c : ℤ) = ip RD i lam then
      -dgC (presNM RD k S) lam [up j, dn i, up i] [up j]
        ([([up j], .cap (up i), [])] ++ List.replicate b ([], .dot (up j), []))
    else 0 := by
  have hm : lurkCapF (RD := RD) (S := S) i j lam
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ c) =
      dgC (presNM RD k S) lam [up j, up i, dn i] [up j]
        ((ccwLs i a).map (whL [] [up j, up i, dn i]) ++
          List.replicate c ([up j], .dot (up i), [dn i]) ++
          List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])]) := by
    rw [← dgN_lurkCap_mono (RD := RD) (S := S) i j lam a b c]
    show ctxLC _ _ _ _ _ _ _ _ _ _ (KLR.ncEval (A := End ((presNM RD k S).obj (ob RD (wt RD lam [dn i])
      [up i, up j, up i]))) (lurkY i j lam) _) ≫ _ = _
    rw [ncEval_X3]
    rfl
  rw [hm]
  have e := plcLC_dg_comp (presNM RD k S) lam [up j] [dn i, up i] [up i, dn i] [up j]
    (crossrL i i) ((ccwLs i a).map (whL [] [up j, up i, dn i]) ++
          List.replicate c ([up j], .dot (up i), [dn i]) ++
          List.replicate b ([], .dot (up j), [up i, dn i]) ++ [([up j], .cap (dn i), [])])
    (by schain) (by simp only [ccwLs]; schain)
  erw [e]
  exact dgN_crossrLurk_mono hr hij lam h1 a b c hac

/-- **Brundan (5.5)** (`0 < ⟨i, λ⟩ < d_{ij}`, the relation (5.2) composed with `σ`): the strand
`j` passing both legs of the cap `F_i E_i ⟶ 1` is `t_{ij}` times the cap, without any mixed
relation. -/
theorem dgN_capTurn_mid {i j : I} (hij : i ≠ j) (lam : X) (h0 : 0 < ip RD i lam)
    (h1 : ip RD i lam < C.dij i j) :
    dgC (presNM RD k S) lam [up j, dn i, up i] [up j] (capTurnLs i j) =
      (S.t i j : k) • dgC (presNM RD k S) lam [up j, dn i, up i] [up j]
        [([up j], .cap (up i), [])] := by
  have hw1 : wt RD (wt RD lam []) [up i, dn i] = wt RD (wt RD lam []) [dn i, up i] := by
    rw [wt_up_dn, wt_dn_up]
  -- `1_{F_i E_i} = -crossr ∘ crossl` in a region with `⟨i, λ⟩ > 0`
  have hD : dgC (presNM RD k S) lam [up j, dn i, up i] [up j] (capTurnLs i j) =
      -(plcLC (presNM RD k S) lam [up j] [] [dn i, up i] [up i, dn i]
          (dgC (presNM RD k S) lam [dn i, up i] [up i, dn i] (crossrL i i)) ≫
        lurkCapF (RD := RD) (S := S) i j lam (KLR.qbar (qCL S i j))) := by
    calc dgC (presNM RD k S) lam [up j, dn i, up i] [up j] (capTurnLs i j) =
        plcLC (presNM RD k S) lam [up j] [] [dn i, up i] [dn i, up i] (𝟙 _) ≫
          dgC (presNM RD k S) lam [up j, dn i, up i] [up j] (capTurnLs i j) := by
          rw [plcLC_id]; exact (Category.id_comp _).symm
      _ = _ := by
        rw [show (𝟙 ((presNM RD k S).obj (ob RD (wt RD lam []) [dn i, up i]))) =
          dgC (presNM RD k S) lam [dn i, up i] [dn i, up i] [] from (dgC_nil lam _).symm]
        rw [dgN_decompFE hr i lam, show (-ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero,
          add_zero, map_neg, Preadditive.neg_comp, ← dgC_comp (t := [up i, dn i]) (by schain)
            (by schain)]
        have c1 := plcLC_comp (presNM RD k S) lam [up j] [] hw1 hw1.symm
          (dgC (presNM RD k S) lam [dn i, up i] [up i, dn i] (crossrL i i))
          (dgC (presNM RD k S) lam [up i, dn i] [dn i, up i] (crosslL i i))
        erw [← c1]
        rw [Category.assoc]
        congr 2
        have e := plcLC_dg_comp (presNM RD k S) lam [up j] [up i, dn i] [dn i, up i] [up j]
          (crosslL i i) (capTurnLs i j) (by schain) (by unfold capTurnLs; schain)
        erw [e]
        rw [← dgN_crosslCapTurn hr hij lam h1]
        simp only [capTurnLs, List.append_assoc]
        rfl
  rw [hD]
  have hd : C.dot i j ≠ 0 := fun h' => by
    have := (C.dij_eq_zero_iff hij).2 h'; omega
  have hdpos := C.dij_pos hij hd
  rw [qbar_qCL S hij hd, map_add, MvPolynomial.C_mul', map_smul]
  simp only [map_sum, Preadditive.comp_add, Linear.comp_smul, Preadditive.comp_sum]
  have hmem : ∀ {n : ℕ} {l : ℕ × ℕ}, l ∈ Finset.HasAntidiagonal.antidiagonal n → l.1 + l.2 = n :=
    fun hl => Finset.HasAntidiagonal.mem_antidiagonal.1 hl
  have hX : ∀ l : ℕ × ℕ, (MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2 : MvPolynomial (Fin 3) k) =
      MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 1 ^ 0 * MvPolynomial.X 2 ^ l.2 := fun l => by ring
  -- the `s`-terms vanish
  have hs : (∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      plcLC (presNM RD k S) lam [up j] [] [dn i, up i] [up i, dn i]
          (dgC (presNM RD k S) lam [dn i, up i] [up i, dn i] (crossrL i i)) ≫
        lurkCapF (RD := RD) (S := S) i j lam
        (if C.dot i i * p + C.dot j j * q = -2 * C.dot i j then
          MvPolynomial.C (S.s i j p q) * MvPolynomial.X 1 ^ q *
            ∑ l ∈ Finset.HasAntidiagonal.antidiagonal (p - 1),
              MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2
        else 0)) = 0 := by
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => ?_
    have hp' := Finset.mem_range.1 hp
    split_ifs
    · rw [mul_assoc, MvPolynomial.C_mul', Finset.mul_sum, map_smul, map_sum, Linear.comp_smul,
        Preadditive.comp_sum]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun l hl => ?_)
      have hl' := hmem hl
      rw [show (MvPolynomial.X 1 ^ q * (MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 2 ^ l.2) :
          MvPolynomial (Fin 3) k) = MvPolynomial.X 0 ^ l.1 * MvPolynomial.X 1 ^ q *
            MvPolynomial.X 2 ^ l.2 by ring,
        dgN_crossrLurkCapF_mono hr hij lam (by omega) _ _ _ (by push_cast; omega),
        ite_eq_right (fun h' => by omega)]
    · rw [map_zero, Limits.comp_zero]
  rw [hs, add_zero]
  simp_rw [hX]
  rw [Finset.sum_eq_single (C.dij i j - (ip RD i lam).toNat - 1, (ip RD i lam).toNat)]
  · rw [dgN_crossrLurkCapF_mono hr hij lam (by omega) _ _ _ (by push_cast; omega),
      ite_eq_left (by constructor <;> push_cast <;> omega)]
    simp
  · intro l hl hne
    have hl' := hmem hl
    rw [dgN_crossrLurkCapF_mono hr hij lam (by omega) _ _ _ (by push_cast; omega), ite_eq_right]
    intro h'
    exact hne (Prod.ext (by simp only at h' ⊢; omega) (by simp only at h' ⊢; omega))
  · intro h'
    exact (h' (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega))).elim

/-- **The mixed relation in the intermediate weights** (`0 < ⟨i, ν - α_i⟩ < d_{ij}`, Brundan
(5.5), without any mixed relation): `crossl j i ≫ crossr j i = t_{ij} · 1` on `E_j F_i 1_ν`. -/
theorem dgN_downupEF_mid {i j : I} (hij : i ≠ j) (ν : X) (h0 : 0 < ip RD i (wt RD ν [dn i]))
    (h1 : ip RD i (wt RD ν [dn i]) < C.dij i j) :
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
    (dgN_capTurn_mid hr hij (wt RD ν [dn i]) h0 h1) (by schain) (by schain)
    (by simp [capTurnLs, crosslL, whL]), map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  congr 1
  rw [dgC_step (presNM RD k S) ν [] [] [up j] [] (dgC_zigR' _ (presNM_zigzags RD k S) _ (up i))
    (by schain) (by schain) (by simp [whL]) rfl]
  simp [dgC_nil]

end Categorification.KL3.Diagram.CL
