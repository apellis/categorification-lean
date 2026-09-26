/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.MixedR3
import Categorification.Diagrams.KL3.Pitchfork
import Categorification.Diagrams.KL3.BubbleSlidesProp

/-!
# Reidemeister 3 with one downward strand, the case `i = j = k` (KL III Proposition 3.5)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.5 (TeX label `prop_other_triangle`), equation (3.23) (TeX label `eq_r3_extra`).
KL III refer to A. Lauda, *A categorification of quantum sl(2)*, arXiv:0803.3652v3, §5.4
(Proposition `prop_other_triangle` there). For `¬ (i = j = k)` see
`Categorification.Diagrams.KL3.MixedR3` (`prop35_a`).

Throughout, `n = ⟨i, λ⟩` with `λ` the rightmost region (`lam`), and `λ + i_X = wt RD lam [up i]`
is the region to the left of the rightmost strand; diagrams are in the normal form of
`Categorification.Diagrams.KL3.Basic`, read bottom to top.

## Reading of (3.23)

The left-hand side is `r3mixL i i i - r3mixR i i i` (the two sides of (3.22) with all labels
`i`), a 2-morphism `E_i F_i E_i 1_λ ⟶ E_i F_i E_i 1_λ`. Decoding the `xy-pic` source:

* a term of the first sum (`sigma1Term f₁ f₂ f₃ f₄`) is: the cap `E_i F_i ⟶ 1` on the left two
  strands with `f₃` dots, the counterclockwise bubble with label `-n-3+f₄` in the region
  `λ + i_X` to the left of the remaining strand, the cup `1 ⟶ E_i F_i` on the left with `f₁`
  dots, and `f₂` dots on the right strand;
* a term of the second sum (`sigma2Term g₁ g₂ g₃ g₄`) is: the cap `F_i E_i ⟶ 1` on the right two
  strands with `g₃` dots, the clockwise bubble with label `n-1+g₄` in the region `λ` to the right
  of the remaining strand, the cup `1 ⟶ F_i E_i` on the right with `g₁` dots, and `g₂` dots on
  the left strand.

The dots on cups and caps are drawn near their downward legs and are placed there (by (3.3) the
position of a dot on a cup or cap is immaterial). Bubbles with negative labels are fake bubbles
(`ccwU`, `cwU`).

## The range of the second sum (erratum)

As printed, the second sum runs over `g₁ + g₂ + g₃ + g₄ = ⟨i,λ⟩ - 2` and "is zero when
`⟨i,λ⟩ < 2`". This is incompatible with the grading: the left-hand side is homogeneous of
degree `-i·i` (the sideways crossings have degree `0`), while a term of the second sum has degree
`(i·i)(1 + n + g₁ + g₂ + g₃ + g₄)` (the cap and cup each have degree `(i·i/2)(1 + n)`), so the
sum must run over `g₁ + g₂ + g₃ + g₄ = -⟨i,λ⟩ - 2` and vanish for `⟨i,λ⟩ > -2`. This agrees with
Lauda's `sl(2)` statement (second sum `∑_{ℓ=0}^{-n-2}`). The first sum
(`f₁ + f₂ + f₃ + f₄ = ⟨i,λ⟩`, zero for `⟨i,λ⟩ < 0`) is as printed. We prove the repaired
statement (`prop35_b`).

## Proof

Rather than rotating the nilHecke Reidemeister 3 relation as in Lauda's sketch, we compose with
the decompositions `eq_ident_decomp` of `1_{F E}` and `1_{E F}`, as in KL III's proof of (3.22):

* `d1` (used for `n ≥ -1`): `L - R = -(ΣEF ⊗ 1) ∘ R + L ∘ (1 ⊗ ΣFE)`, from the outer mixed
  Reidemeister 3 move `dg_r3outR`; `d2` (used for `n ≤ -2`):
  `L - R = (1 ⊗ ΣFE) ∘ L - R ∘ (ΣEF ⊗ 1)`, from `dg_r3outL`. Here `ΣEF`, `ΣFE` (`sEF`, `sFE`) are
  the sums of cap–bubble–cup terms of `eq_ident_decomp`; `ΣFE = 0` for `n ≥ 0` and `ΣEF = 0` for
  `n ≤ -2`.
* `k1`: a cup `1 ⟶ E_i F_i` with `m ≤ n + 1` dots below `R` equals
  `-∑_{a<m}` (the cup with `a` dots) `x^{m-1-a}`: a pitchfork move (`dg_pf_cupUp`), the nilHecke
  relation `ψ x₁^m ψ = ∑ x₂^a x₁^{m-1-a} ψ`, the pitchfork back, `crossr ∘ crossl = -1` on `F E`
  (`n ≥ 0`), and the vanishing of dotted right curls on a cup (`dg_cupUp_crossl_eq_zero`,
  Lauda Proposition 5.4); `k2` is the mirror statement for a cup `1 ⟶ F_i E_i` below `L`
  (`n ≤ -q - 1`), and `k3` kills the only term of `L ∘ (1 ⊗ ΣFE)` for `n = -1`.
* `term1`–`term4` evaluate the four composites; `sum_reindex4` rewrites the resulting triple sums
  as sums over compositions `f₁ + f₂ + f₃ + f₄`.

## Main results

* `prop35_b`: **KL III (3.23)**, repaired as above.
* Auxiliary: `k1`, `k2`, `k3`, `d1`, `d2`, `dg_cupUp_crossl_eq_zero`, `dg_cupDn_crossr_eq_zero`,
  `dg_dotsL_comm`, `dg_dotsR_comm`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Placed nilHecke generators -/

section Placed

variable (lam : X) (i : I)

theorem plcL_nhDotR_dnR (b : ℕ) :
    plcL RD k lam [] [dn i] [up i, up i] [up i, up i] (nhDotR RD k (wt RD lam [dn i]) i b) =
      dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
        (List.replicate b ([up i], .dot (up i), [dn i])) := by
  simp only [nhDotR]; rw [plcL_dg]; lnf

theorem plcL_nhCross_dnR :
    plcL RD k lam [] [dn i] [up i, up i] [up i, up i] (nhCross RD k (wt RD lam [dn i]) i) =
      dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] := by
  simp only [nhCross]; rw [plcL_dg]; lnf

theorem plcL_nhDotL_dnL (b : ℕ) :
    plcL RD k lam [dn i] [] [up i, up i] [up i, up i] (nhDotL RD k lam i b) =
      dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
        (List.replicate b ([dn i], .dot (up i), [up i])) := by
  simp only [nhDotL]; rw [plcL_dg_nil]; lnf

theorem plcL_nhCross_dnL :
    plcL RD k lam [dn i] [] [up i, up i] [up i, up i] (nhCross RD k lam i) =
      dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] := by
  simp only [nhCross]; rw [plcL_dg_nil]; lnf

end Placed

/-! ## A cup of `1 ⟶ E_i F_i` below the right-hand side of (3.22) -/

section K1

variable (lam : X) (i : I)

/-- Dots on the leftmost strand commute with a diagram on the other strands (interchange law). -/
theorem dg_dotsL_comm {μ : X} (l : Letter I) {s t : List (Letter I)} {B : List (LayerData I)}
    (hB : SChain s B t) (m : ℕ) :
    dg RD k μ (l :: s) (l :: t) (List.replicate m ([], .dot l, s) ++ B.map (whL [l] [])) =
      dg RD k μ (l :: s) (l :: t) (B.map (whL [l] []) ++ List.replicate m ([], .dot l, t)) := by
  have h := dg_interchange (RD := RD) (k := k) (μ := μ) (S := l :: s) (T := l :: t) [] []
    (A := List.replicate m ([], .dot l, [])) (s := [l]) (s' := [l])
    (SChain.replicate m [] l []) hB
  simpa [whL, List.map_replicate] using h

/-- Dots on the rightmost strand commute with a diagram on the other strands. -/
theorem dg_dotsR_comm {μ : X} (l : Letter I) {s t : List (Letter I)} {A : List (LayerData I)}
    (hA : SChain s A t) (m : ℕ) :
    dg RD k μ (s ++ [l]) (t ++ [l]) (List.replicate m (s, .dot l, []) ++ A.map (whL [] [l])) =
      dg RD k μ (s ++ [l]) (t ++ [l]) (A.map (whL [] [l]) ++ List.replicate m (t, .dot l, [])) := by
  have h := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s ++ [l]) (T := t ++ [l]) [] []
    (B := List.replicate m ([], .dot l, [])) (t := [l]) (t' := [l]) hA
    (SChain.replicate m [] l [])
  simpa [whL, List.map_replicate] using h.symm

theorem k1_split (m : ℕ) :
    dg RD k lam [up i] [up i, dn i, up i]
        ([([], .cup (up i), [up i])] ++ List.replicate m ([up i], .dot (dn i), [up i]) ++
          r3mixR i i i) =
      dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate m ([up i], .dot (dn i), [up i])) ≫
        dg RD k lam [up i, dn i, up i] [up i, up i, dn i] ((crossrL i i).map (whL [up i] [])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
        dg RD k lam [up i, up i, dn i] [up i, dn i, up i] ((crosslL i i).map (whL [up i] [])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain),
    dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  congr 1

@[reassoc]
theorem k1a (m : ℕ) :
    dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate m ([up i], .dot (dn i), [up i])) =
      dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate m ([], .dot (up i), [dn i, up i])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  dstep [] [] [] [up i] (dg_dots_cupUp RD k i _ m)
  simp [whL]

@[reassoc]
theorem k1b (m : ℕ) :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate m ([], .dot (up i), [dn i, up i])) ≫
        dg RD k lam [up i, dn i, up i] [up i, up i, dn i] ((crossrL i i).map (whL [up i] [])) =
      dg RD k lam [up i, dn i, up i] [up i, up i, dn i] ((crossrL i i).map (whL [up i] [])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate m ([], .dot (up i), [up i, dn i])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_dotsL_comm RD k (up i) (B := crossrL i i) (by schain) m

@[reassoc]
theorem k1c :
    dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
        dg RD k lam [up i, dn i, up i] [up i, up i, dn i] ((crossrL i i).map (whL [up i] [])) =
      dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_pf_cupUp RD k i i lam

@[reassoc]
theorem k1d (m : ℕ) :
    dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate m ([], .dot (up i), [up i, dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] =
      ∑ a ∈ Finset.range m,
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
            (List.replicate a ([up i], .dot (up i), [dn i])) ≫
          dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
            (List.replicate (m - 1 - a) ([], .dot (up i), [up i, dn i])) ≫
          dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] := by
  rw [← plcL_nhCross_dnR, ← plcL_nhDotL RD k lam i m, plcL_comp RD k lam [] [dn i] rfl rfl,
    plcL_comp RD k lam [] [dn i] rfl rfl, nhCross_nhDotL_nhCross, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← plcL_comp RD k lam [] [dn i] rfl rfl, ← plcL_comp RD k lam [] [dn i] rfl rfl,
    plcL_nhDotR_dnR, plcL_nhDotL, plcL_nhCross_dnR]

@[reassoc]
theorem k1e (b : ℕ) :
    dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate b ([], .dot (up i), [up i, dn i])) =
      dotsU RD k lam (up i) b ≫
        dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] := by
  rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact (dg_dotsL_comm RD k (up i) (s := []) (B := [([], .cup (up i), [])]) (by schain) b).symm

@[reassoc]
theorem k1f (a : ℕ) :
    dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate a ([up i], .dot (up i), [dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] =
      dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
          dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
            (List.replicate a ([], .dot (up i), [up i, dn i])) -
        ∑ c ∈ Finset.range a,
          dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
              (List.replicate c ([up i], .dot (up i), [dn i])) ≫
            dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
              (List.replicate (a - 1 - c) ([], .dot (up i), [up i, dn i])) := by
  rw [← plcL_nhCross_dnR, ← plcL_nhDotL RD k lam i a, ← plcL_nhDotR_dnR,
    plcL_comp RD k lam [] [dn i] rfl rfl, plcL_comp RD k lam [] [dn i] rfl rfl,
    nhCross_nhDotL_pow, map_add, map_sum]
  have : ∑ c ∈ Finset.range a, plcL RD k lam [] [dn i] [up i, up i] [up i, up i]
      (nhDotR RD k (wt RD lam [dn i]) i c ≫ nhDotL RD k (wt RD lam [dn i]) i (a - 1 - c)) =
      ∑ c ∈ Finset.range a,
          dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
              (List.replicate c ([up i], .dot (up i), [dn i])) ≫
            dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
              (List.replicate (a - 1 - c) ([], .dot (up i), [up i, dn i])) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← plcL_comp RD k lam [] [dn i] rfl rfl, plcL_nhDotR_dnR, plcL_nhDotL]
  rw [this, add_sub_cancel_right]

@[reassoc]
theorem k1g (a : ℕ) :
    dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate a ([], .dot (up i), [up i, dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, dn i, up i] ((crosslL i i).map (whL [up i] [])) =
      dg RD k lam [up i, up i, dn i] [up i, dn i, up i] ((crosslL i i).map (whL [up i] [])) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate a ([], .dot (up i), [dn i, up i])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_dotsL_comm RD k (up i) (B := crosslL i i) (by schain) a

@[reassoc]
theorem k1h (hn : 0 ≤ ip RD i lam) :
    dg RD k lam [up i, dn i, up i] [up i, up i, dn i] ((crossrL i i).map (whL [up i] [])) ≫
        dg RD k lam [up i, up i, dn i] [up i, dn i, up i] ((crosslL i i).map (whL [up i] [])) =
      -𝟙 _ := by
  have hd := dg_decompFE RD k i lam
  have h0 : (-ip RD i lam).toNat = 0 := by omega
  rw [h0, Finset.sum_range_zero, add_zero] at hd
  have hd' : dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) =
      -dg RD k lam [dn i, up i] [dn i, up i] [] := by
    rw [hd, neg_neg]
  rw [dg_comp (by schain) (by schain), ← List.map_append]
  calc dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.map (whL [up i] []) (crossrL i i ++ crosslL i i))
      = plcL RD k lam [up i] [] [dn i, up i] [dn i, up i]
          (dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i)) :=
        (plcL_dg_nil RD k lam [up i] [dn i, up i] [dn i, up i] _).symm
    _ = -plcL RD k lam [up i] [] [dn i, up i] [dn i, up i]
          (dg RD k lam [dn i, up i] [dn i, up i] []) := by rw [hd', map_neg]
    _ = -𝟙 _ := by rw [plcL_dg_nil, List.map_nil, dg_nil]

@[reassoc]
theorem k1j (a b : ℕ) :
    dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate a ([up i], .dot (up i), [dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate b ([], .dot (up i), [up i, dn i])) =
      dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate b ([], .dot (up i), [up i, dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate a ([up i], .dot (up i), [dn i])) := by
  rw [← plcL_nhDotR_dnR, ← plcL_nhDotL RD k lam i b, plcL_comp RD k lam [] [dn i] rfl rfl,
    plcL_comp RD k lam [] [dn i] rfl rfl, nhDotR_nhDotL]

/-- The cup `1 ⟶ E_i F_i` with `c` dots on its upward leg, followed by `crossl` on its two legs,
vanishes for `c < ⟨i, λ⟩`: it is the cup `1 ⟶ F_i E_i` followed by a right curl with `c` dots
on its loop (Lauda, Proposition 5.4). -/
theorem dg_cupUp_crossl_eq_zero (c : ℕ) (hc : (c : ℤ) < ip RD i lam) :
    dg RD k lam [] [dn i, up i]
      ([([], .cup (up i), [])] ++ List.replicate c ([], .dot (up i), [dn i]) ++
        crosslL i i) = 0 := by
  have hP : plcL RD k lam [dn i] [] [up i] [up i]
      (ptrR RD k lam i (nhDotR RD k (wt RD lam [dn i]) i c ≫ nhCross RD k (wt RD lam [dn i]) i)) =
      dg RD k lam [dn i, up i] [dn i, up i]
        ([([dn i, up i], .cup (up i), [])] ++
          List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
          [([dn i], .cross true i i, [dn i]), ([dn i, up i], .cap (dn i), [])]) := by
    rw [nhDotR, nhCross, dg_comp (by schain) (by schain), ptrR_dg, plcL_dg_nil]
    congr 1
    lnf
  have hR : ptrR RD k lam i (nhDotR RD k (wt RD lam [dn i]) i c ≫
      nhCross RD k (wt RD lam [dn i]) i) = 0 := by
    rw [ptrR_nhDotR_nhCross]
    have h0 : ((c : ℤ) + -ip RD i lam + 1).toNat = 0 := by omega
    rw [h0, Finset.sum_range_zero, neg_zero]
  rw [hR, map_zero] at hP
  have e : dg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] ≫
      dg RD k lam [dn i, up i] [dn i, up i]
        ([([dn i, up i], .cup (up i), [])] ++
          List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
          [([dn i], .cross true i i, [dn i]), ([dn i, up i], .cap (dn i), [])]) =
      dg RD k lam [] [dn i, up i]
        ([([], .cup (dn i), [])] ++ ([([dn i, up i], .cup (up i), [])] ++
          List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
          [([dn i], .cross true i i, [dn i]), ([dn i, up i], .cap (dn i), [])])) :=
    dg_comp (by schain) (by schain)
  rw [← hP, Limits.comp_zero] at e
  simp only [crosslL]
  dstep [([], .cup (up i), [])] [([dn i], .cross true i i, [dn i]), ([dn i, up i], .cap (dn i), [])]
    [] [] (dg_swap_rep RD k lam [] [] [dn i] (.cup (dn i)) (.dot (up i)) rfl c)
  dstep [] (List.replicate c ([dn i, up i], .dot (up i), [dn i]) ++
      [([dn i], .cross true i i, [dn i]), ([dn i, up i], .cap (dn i), [])]) [] []
    (dg_swap' RD k lam [] [] [] (.cup (dn i)) (.cup (up i))).symm
  refine Eq.trans ?_ e.symm
  congr 1

/-- The cup `1 ⟶ E_i F_i` to the right of `E_i` with `c` dots on its upward leg, followed by
`crossl` on its legs, vanishes for `c < ⟨i, λ⟩`. -/
@[reassoc]
theorem k1i (c : ℕ) (hc : (c : ℤ) < ip RD i lam) :
    dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate c ([up i], .dot (up i), [dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, dn i, up i]
          ((crosslL i i).map (whL [up i] [])) = 0 := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  have := plcL_dg_nil RD k lam [up i] [] [dn i, up i]
    ([([], .cup (up i), [])] ++ List.replicate c ([], .dot (up i), [dn i]) ++ crosslL i i)
  rw [dg_cupUp_crossl_eq_zero RD k lam i c hc, map_zero] at this
  refine Eq.trans ?_ this.symm
  congr 1
  simp [whL, List.map_replicate]

theorem k1_term (a : ℕ) (hn : 0 ≤ ip RD i lam) (ha : (a : ℤ) ≤ ip RD i lam) :
    dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
          (List.replicate a ([up i], .dot (up i), [dn i])) ≫
        dg RD k lam [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
        dg RD k lam [up i, up i, dn i] [up i, dn i, up i] ((crosslL i i).map (whL [up i] [])) =
      -(dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
          dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
            (List.replicate a ([up i], .dot (dn i), [up i]))) := by
  rw [k1f_assoc, Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.sum_comp,
    Preadditive.comp_sum]
  have hc : ∀ c ∈ Finset.range a,
      dg RD k lam [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
        (dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
            (List.replicate c ([up i], .dot (up i), [dn i])) ≫
          dg RD k lam [up i, up i, dn i] [up i, up i, dn i]
            (List.replicate (a - 1 - c) ([], .dot (up i), [up i, dn i]))) ≫
          dg RD k lam [up i, up i, dn i] [up i, dn i, up i] ((crosslL i i).map (whL [up i] [])) =
        0 := by
    intro c hc
    have hc' := Finset.mem_range.1 hc
    simp only [Category.assoc]
    rw [k1g, k1i_assoc RD k lam i c (by omega), Limits.zero_comp]
  rw [Finset.sum_congr rfl hc, Finset.sum_const_zero, sub_zero]
  simp only [Category.assoc]
  rw [k1g, ← k1c_assoc, k1h_assoc RD k lam i hn, Preadditive.neg_comp, Category.id_comp,
    Preadditive.comp_neg, ← k1a]

/-- **Key lemma for `i = j = k`, `⟨i, λ⟩ ≥ m - 1`**: the cup `1 ⟶ E_i F_i` with `m` dots on its
downward leg, placed to the left of `E_i`, followed by the right-hand side of (3.22), equals
`-∑_{a<m}` (the same cup with `a` dots) `x^{m-1-a}` on `E_i`. -/
theorem k1 (m : ℕ) (hm : (m : ℤ) ≤ ip RD i lam + 1) :
    dg RD k lam [up i] [up i, dn i, up i]
        ([([], .cup (up i), [up i])] ++ List.replicate m ([up i], .dot (dn i), [up i]) ++
          r3mixR i i i) =
      -∑ a ∈ Finset.range m, dotsU RD k lam (up i) (m - 1 - a) ≫
        dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
          dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
            (List.replicate a ([up i], .dot (dn i), [up i])) := by
  rw [k1_split, k1a_assoc, k1b_assoc, k1c_assoc, k1d_assoc, Preadditive.sum_comp,
    Preadditive.comp_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  simp only [Category.assoc]
  rw [k1j_assoc, k1e_assoc, k1_term RD k lam i a (by omega) (by omega), Preadditive.comp_neg]

end K1

/-! ## A cup of `1 ⟶ F_i E_i` below the left-hand side of (3.22) -/

section K2

variable (lam : X) (i : I)

theorem k2_split (q : ℕ) :
    dg RD k lam [up i] [up i, dn i, up i]
        ([([up i], .cup (dn i), [])] ++ List.replicate q ([up i, dn i], .dot (up i), []) ++
          r3mixL i i i) =
      dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate q ([up i, dn i], .dot (up i), [])) ≫
        dg RD k lam [up i, dn i, up i] [dn i, up i, up i] ((crosslL i i).map (whL [] [up i])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
        dg RD k lam [dn i, up i, up i] [up i, dn i, up i] ((crossrL i i).map (whL [] [up i])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain),
    dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  congr 1

@[reassoc]
theorem k2b (q : ℕ) :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate q ([up i, dn i], .dot (up i), [])) ≫
        dg RD k lam [up i, dn i, up i] [dn i, up i, up i] ((crosslL i i).map (whL [] [up i])) =
      dg RD k lam [up i, dn i, up i] [dn i, up i, up i] ((crosslL i i).map (whL [] [up i])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate q ([dn i, up i], .dot (up i), [])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_dotsR_comm RD k (up i) (A := crosslL i i) (by schain) q

@[reassoc]
theorem k2c :
    dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
        dg RD k lam [up i, dn i, up i] [dn i, up i, up i] ((crosslL i i).map (whL [] [up i])) =
      dg RD k lam [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_pf_cupDn RD k i i lam

@[reassoc]
theorem k2d (q : ℕ) :
    dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate q ([dn i, up i], .dot (up i), [])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] =
      -∑ a ∈ Finset.range q,
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
            (List.replicate a ([dn i], .dot (up i), [up i])) ≫
          dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
            (List.replicate (q - 1 - a) ([dn i, up i], .dot (up i), [])) ≫
          dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] := by
  rw [← plcL_nhCross_dnL, ← plcL_nhDotR RD k lam i q, plcL_comp RD k lam [dn i] [] rfl rfl,
    plcL_comp RD k lam [dn i] [] rfl rfl, nhCross_nhDotR_nhCross, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← plcL_comp RD k lam [dn i] [] rfl rfl, ← plcL_comp RD k lam [dn i] [] rfl rfl,
    plcL_nhDotL_dnL, plcL_nhDotR, plcL_nhCross_dnL]

@[reassoc]
theorem k2e (b : ℕ) :
    dg RD k lam [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate b ([dn i, up i], .dot (up i), [])) =
      dotsU RD k lam (up i) b ≫
        dg RD k lam [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] := by
  rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact (dg_dotsR_comm RD k (up i) (s := []) (A := [([], .cup (dn i), [])]) (by schain) b).symm

@[reassoc]
theorem k2f (a : ℕ) :
    dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate a ([dn i], .dot (up i), [up i])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] =
      dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
          dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
            (List.replicate a ([dn i, up i], .dot (up i), [])) +
        ∑ c ∈ Finset.range a,
          dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
              (List.replicate c ([dn i], .dot (up i), [up i])) ≫
            dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
              (List.replicate (a - 1 - c) ([dn i, up i], .dot (up i), [])) := by
  rw [← plcL_nhCross_dnL, ← plcL_nhDotR RD k lam i a, ← plcL_nhDotL_dnL,
    plcL_comp RD k lam [dn i] [] rfl rfl, plcL_comp RD k lam [dn i] [] rfl rfl,
    nhCross_nhDotR, map_sub, map_sum]
  have : ∑ c ∈ Finset.range a, plcL RD k lam [dn i] [] [up i, up i] [up i, up i]
      (nhDotL RD k lam i c ≫ nhDotR RD k lam i (a - 1 - c)) =
      ∑ c ∈ Finset.range a,
          dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
              (List.replicate c ([dn i], .dot (up i), [up i])) ≫
            dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
              (List.replicate (a - 1 - c) ([dn i, up i], .dot (up i), [])) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← plcL_comp RD k lam [dn i] [] rfl rfl, plcL_nhDotL_dnL, plcL_nhDotR]
  rw [this, sub_add_cancel]

@[reassoc]
theorem k2g (a : ℕ) :
    dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate a ([dn i, up i], .dot (up i), [])) ≫
        dg RD k lam [dn i, up i, up i] [up i, dn i, up i] ((crossrL i i).map (whL [] [up i])) =
      dg RD k lam [dn i, up i, up i] [up i, dn i, up i] ((crossrL i i).map (whL [] [up i])) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate a ([up i, dn i], .dot (up i), [])) := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  exact dg_dotsR_comm RD k (up i) (A := crossrL i i) (by schain) a

@[reassoc]
theorem k2h (hn : ip RD i lam ≤ -2) :
    dg RD k lam [up i, dn i, up i] [dn i, up i, up i] ((crosslL i i).map (whL [] [up i])) ≫
        dg RD k lam [dn i, up i, up i] [up i, dn i, up i] ((crossrL i i).map (whL [] [up i])) =
      -𝟙 _ := by
  have hd := dg_decompEF RD k i (wt RD lam [up i])
  have h0 : (ip RD i (wt RD lam [up i])).toNat = 0 := by
    rw [ip_wt_up, A_self]; omega
  rw [h0, Finset.sum_range_zero, add_zero] at hd
  have hd' : dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) =
      -dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] [] := by
    rw [hd, neg_neg]
  rw [dg_comp (by schain) (by schain), ← List.map_append]
  calc dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.map (whL [] [up i]) (crosslL i i ++ crossrL i i))
      = plcL RD k lam [] [up i] [up i, dn i] [up i, dn i]
          (dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i)) :=
        (plcL_dg RD k lam [] [up i] [up i, dn i] [up i, dn i] _).symm
    _ = -plcL RD k lam [] [up i] [up i, dn i] [up i, dn i]
          (dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] []) := by rw [hd', map_neg]
    _ = -𝟙 _ := by rw [plcL_dg, List.map_nil, dg_nil]

@[reassoc]
theorem k2j (a b : ℕ) :
    dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate a ([dn i], .dot (up i), [up i])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate b ([dn i, up i], .dot (up i), [])) =
      dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate b ([dn i, up i], .dot (up i), [])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate a ([dn i], .dot (up i), [up i])) := by
  rw [← plcL_nhDotL_dnL, ← plcL_nhDotR RD k lam i b, plcL_comp RD k lam [dn i] [] rfl rfl,
    plcL_comp RD k lam [dn i] [] rfl rfl, nhDotR_nhDotL]

/-- The cup `1 ⟶ F_i E_i` with `c` dots on its upward leg, followed by `crossr` on its two legs,
vanishes for `c + ⟨i, λ'⟩ + 1 ≤ 0` (`λ'` its outer region): it is the cup `1 ⟶ E_i F_i` followed
by a left curl with `c` dots on its loop (Lauda, Proposition 5.4). -/
theorem dg_cupDn_crossr_eq_zero (ν : X) (c : ℕ) (hc : (c : ℤ) + ip RD i ν + 1 ≤ 0) :
    dg RD k ν [] [up i, dn i]
      ([([], .cup (dn i), [])] ++ List.replicate c ([dn i], .dot (up i), []) ++
        crossrL i i) = 0 := by
  have hP : plcL RD k ν [] [dn i] [up i] [up i]
      (ptrL RD k (wt RD ν [dn i]) i (nhDotL RD k (wt RD ν [dn i]) i c ≫
        nhCross RD k (wt RD ν [dn i]) i)) =
      dg RD k ν [up i, dn i] [up i, dn i]
        ([([], .cup (dn i), [up i, dn i])] ++
          List.replicate c ([dn i], .dot (up i), [up i, dn i]) ++
          [([dn i], .cross true i i, [dn i]), ([], .cap (up i), [up i, dn i])]) := by
    rw [nhDotL, nhCross, dg_comp (by schain) (by schain), ptrL_dg, plcL_dg]
    congr 1
    lnf
  have hR : ptrL RD k (wt RD ν [dn i]) i (nhDotL RD k (wt RD ν [dn i]) i c ≫
      nhCross RD k (wt RD ν [dn i]) i) = 0 := by
    rw [ptrL_nhDotL_nhCross]
    have e : wt RD (wt RD ν [dn i]) [up i] = ν := by simp
    have h0 : ((c : ℤ) + ip RD i (wt RD (wt RD ν [dn i]) [up i]) + 1).toNat = 0 := by
      rw [e]; omega
    rw [h0, Finset.sum_range_zero]
  rw [hR, map_zero] at hP
  have e : dg RD k ν [] [up i, dn i] [([], .cup (up i), [])] ≫
      dg RD k ν [up i, dn i] [up i, dn i]
        ([([], .cup (dn i), [up i, dn i])] ++
          List.replicate c ([dn i], .dot (up i), [up i, dn i]) ++
          [([dn i], .cross true i i, [dn i]), ([], .cap (up i), [up i, dn i])]) =
      dg RD k ν [] [up i, dn i]
        ([([], .cup (up i), [])] ++ ([([], .cup (dn i), [up i, dn i])] ++
          List.replicate c ([dn i], .dot (up i), [up i, dn i]) ++
          [([dn i], .cross true i i, [dn i]), ([], .cap (up i), [up i, dn i])])) :=
    dg_comp (by schain) (by schain)
  rw [← hP, Limits.comp_zero] at e
  simp only [crossrL]
  dstep [([], .cup (dn i), [])] [([dn i], .cross true i i, [dn i]), ([], .cap (up i), [up i, dn i])]
    [] [] (dg_swap_rep' RD k ν [dn i] [] [] (.cup (up i)) (.dot (up i)) rfl c)
  dstep [] (List.replicate c ([dn i], .dot (up i), [up i, dn i]) ++
      [([dn i], .cross true i i, [dn i]), ([], .cap (up i), [up i, dn i])]) [] []
    (dg_swap' RD k ν [] [] [] (.cup (dn i)) (.cup (up i)))
  refine Eq.trans ?_ e.symm
  congr 1

@[reassoc]
theorem k2i (c : ℕ) (hc : (c : ℤ) + ip RD i lam + 3 ≤ 0) :
    dg RD k lam [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate c ([dn i], .dot (up i), [up i])) ≫
        dg RD k lam [dn i, up i, up i] [up i, dn i, up i]
          ((crossrL i i).map (whL [] [up i])) = 0 := by
  rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  have := plcL_dg RD k lam [] [up i] [] [up i, dn i]
    ([([], .cup (dn i), [])] ++ List.replicate c ([dn i], .dot (up i), []) ++ crossrL i i)
  rw [dg_cupDn_crossr_eq_zero RD k i _ c (by rw [ip_wt_up, A_self]; omega), map_zero] at this
  refine Eq.trans ?_ this.symm
  congr 1
  simp [whL, List.map_replicate]

theorem k2_term (a : ℕ) (hn : ip RD i lam ≤ -2) (ha : (a : ℤ) + ip RD i lam + 2 ≤ 0) :
    dg RD k lam [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
          (List.replicate a ([dn i], .dot (up i), [up i])) ≫
        dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
        dg RD k lam [dn i, up i, up i] [up i, dn i, up i] ((crossrL i i).map (whL [] [up i])) =
      -(dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
          dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
            (List.replicate a ([up i, dn i], .dot (up i), []))) := by
  rw [k2f_assoc, Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum]
  have hc : ∀ c ∈ Finset.range a,
      dg RD k lam [up i] [dn i, up i, up i] [([], .cup (dn i), [up i])] ≫
        (dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
            (List.replicate c ([dn i], .dot (up i), [up i])) ≫
          dg RD k lam [dn i, up i, up i] [dn i, up i, up i]
            (List.replicate (a - 1 - c) ([dn i, up i], .dot (up i), []))) ≫
          dg RD k lam [dn i, up i, up i] [up i, dn i, up i] ((crossrL i i).map (whL [] [up i])) =
        0 := by
    intro c hc
    have hc' := Finset.mem_range.1 hc
    simp only [Category.assoc]
    rw [k2g, k2i_assoc RD k lam i c (by omega), Limits.zero_comp]
  rw [Finset.sum_congr rfl hc, Finset.sum_const_zero, add_zero]
  simp only [Category.assoc]
  rw [k2g, ← k2c_assoc, k2h_assoc RD k lam i hn, Preadditive.neg_comp, Category.id_comp,
    Preadditive.comp_neg]

/-- **Key lemma for `i = j = k`, `⟨i, λ⟩ ≤ -q - 1`**: the cup `1 ⟶ F_i E_i` with `q` dots on its
upward leg, placed to the right of `E_i`, followed by the left-hand side of (3.22), equals
`∑_{a<q} x^{q-1-a}` on `E_i` (the same cup with `a` dots). -/
theorem k2 (q : ℕ) (hq : (q : ℤ) + ip RD i lam + 1 ≤ 0) :
    dg RD k lam [up i] [up i, dn i, up i]
        ([([up i], .cup (dn i), [])] ++ List.replicate q ([up i, dn i], .dot (up i), []) ++
          r3mixL i i i) =
      ∑ a ∈ Finset.range q, dotsU RD k lam (up i) (q - 1 - a) ≫
        dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
          dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
            (List.replicate a ([up i, dn i], .dot (up i), [])) := by
  rw [k2_split, k2b_assoc, k2c_assoc, k2d_assoc, Preadditive.neg_comp, Preadditive.comp_neg,
    Preadditive.sum_comp, Preadditive.comp_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  simp only [Category.assoc]
  rw [k2j_assoc, k2e_assoc, k2_term RD k lam i a (by omega) (by omega), Preadditive.comp_neg,
    neg_neg]

/-- The cap `F_i E_i ⟶ 1` on the right two strands after the left-hand side of (3.22)
vanishes (a pitchfork move and `ψ² = 0`). -/
theorem k3 :
    dg RD k lam [up i, dn i, up i] [up i] (r3mixL i i i ++ [([up i], .cap (up i), [])]) = 0 := by
  have hX : dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
      dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] = 0 := by
    rw [← plcL_nhCross_dnL, plcL_comp RD k lam [dn i] [] rfl rfl, nhCross_nhCross, map_zero]
  have e₁ : r3mixL i i i ++ [([up i], .cap (up i), [])] =
      ((crosslL i i).map (whL [] [up i]) ++ [([dn i], .cross true i i, [])]) ++
        ((crossrL i i).map (whL [] [up i]) ++ [([up i], .cap (up i), [])]) := by
    simp [r3mixL, List.append_assoc]
  rw [e₁, ← dg_comp (t := [dn i, up i, up i]) (by schain) (by schain), dg_pf_capUp,
    ← dg_comp (t := [dn i, up i, up i]) (by schain) (by schain)]
  have e₂ : dg RD k lam [dn i, up i, up i] [up i]
      [([dn i], .cross true i i, []), ([], .cap (up i), [up i])] =
      dg RD k lam [dn i, up i, up i] [dn i, up i, up i] [([dn i], .cross true i i, [])] ≫
        dg RD k lam [dn i, up i, up i] [up i] [([], .cap (up i), [up i])] := by
    rw [dg_comp (by schain) (by schain)]; rfl
  rw [e₂]
  simp only [Category.assoc]
  rw [← Category.assoc (dg RD k lam [dn i, up i, up i] [dn i, up i, up i] _), hX,
    Limits.zero_comp, Limits.comp_zero]

end K2

/-! ## Composing (3.22) with the decompositions of `1_{E F}` and `1_{F E}` -/

section Derivations

variable (lam : X) (i : I)

/-- Placement of an endomorphism of `E_i F_i 1_{λ + i_X}` on the left two strands of
`E_i F_i E_i 1_λ`. -/
def plcEF : ((pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i]) ⟶
      (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i])) →ₗ[k]
    ((pres RD k).obj (ob RD lam [up i, dn i, up i]) ⟶
      (pres RD k).obj (ob RD lam [up i, dn i, up i])) :=
  plcL RD k lam [] [up i] [up i, dn i] [up i, dn i]

/-- Placement of an endomorphism of `F_i E_i 1_λ` on the right two strands of
`E_i F_i E_i 1_λ`. -/
def plcFE : ((pres RD k).obj (ob RD lam [dn i, up i]) ⟶
      (pres RD k).obj (ob RD lam [dn i, up i])) →ₗ[k]
    ((pres RD k).obj (ob RD lam [up i, dn i, up i]) ⟶
      (pres RD k).obj (ob RD lam [up i, dn i, up i])) :=
  plcL RD k lam [up i] [] [dn i, up i] [dn i, up i]

theorem plcEF_dg (A : List (LayerData I)) :
    plcEF RD k lam i (dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] A) =
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (A.map (whL [] [up i])) :=
  plcL_dg RD k lam [] [up i] [up i, dn i] [up i, dn i] A

theorem plcFE_dg (A : List (LayerData I)) :
    plcFE RD k lam i (dg RD k lam [dn i, up i] [dn i, up i] A) =
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (A.map (whL [up i] [])) :=
  plcL_dg_nil RD k lam [up i] [dn i, up i] [dn i, up i] A

theorem plcEF_id : plcEF RD k lam i (𝟙 _) = 𝟙 _ := by
  rw [← dg_nil, plcEF_dg, List.map_nil, dg_nil]

theorem plcFE_id : plcFE RD k lam i (𝟙 _) = 𝟙 _ := by
  rw [← dg_nil, plcFE_dg, List.map_nil, dg_nil]

theorem d1_aux :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) ≫
        plcFE RD k lam i (dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i)) =
      plcEF RD k lam i
          (dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i)) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) := by
  rw [plcFE_dg, plcEF_dg, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  simp only [r3mixL, r3mixR]
  dnorm
  dat 3 [] [] (dg_r3outR RD k i i i (by simp) _)

theorem d2_aux :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) ≫
        plcEF RD k lam i
          (dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i)) =
      plcFE RD k lam i (dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i)) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) := by
  rw [plcFE_dg, plcEF_dg, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
  simp only [r3mixL, r3mixR]
  dnorm
  dat 3 [] [] (dg_r3outL RD k i i i (by simp) _).symm

/-- **First derivation** (compose the left-hand side of (3.22) with the decomposition of
`1_{F E}` on the top right, then use the outer mixed Reidemeister 3 move and the decomposition
of `1_{E F}` on the bottom left). -/
theorem d1 {SEF : (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i]) ⟶
      (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i])}
    {SFE : (pres RD k).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k).obj (ob RD lam [dn i, up i])}
    (hEF : dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] [] =
      -dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) + SEF)
    (hFE : dg RD k lam [dn i, up i] [dn i, up i] [] =
      -dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) + SFE) :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) -
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) =
      -(plcEF RD k lam i SEF ≫ dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i)) +
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) ≫
          plcFE RD k lam i SFE := by
  have h1 : dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) =
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) ≫
        plcFE RD k lam i (dg RD k lam [dn i, up i] [dn i, up i] []) := by
    rw [dg_nil, plcFE_id, Category.comp_id]
  have h3 : dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) =
      SEF - 𝟙 _ := by
    rw [← dg_nil, hEF]; abel
  rw [hFE, map_add, map_neg, Preadditive.comp_add, Preadditive.comp_neg, d1_aux, h3, map_sub,
    Preadditive.sub_comp, plcEF_id, Category.id_comp] at h1
  conv_lhs => rw [h1]
  abel

/-- **Second derivation** (compose the right-hand side of (3.22) with the decomposition of
`1_{E F}` on the top left, then use the outer mixed Reidemeister 3 move and the decomposition
of `1_{F E}` on the bottom right). -/
theorem d2 {SEF : (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i]) ⟶
      (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i])}
    {SFE : (pres RD k).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k).obj (ob RD lam [dn i, up i])}
    (hEF : dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] [] =
      -dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) + SEF)
    (hFE : dg RD k lam [dn i, up i] [dn i, up i] [] =
      -dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) + SFE) :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) -
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) =
      plcFE RD k lam i SFE ≫ dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) -
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) ≫
          plcEF RD k lam i SEF := by
  have h1 : dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) =
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) ≫
        plcEF RD k lam i (dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] []) := by
    rw [dg_nil, plcEF_id, Category.comp_id]
  have h3 : dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) = SFE - 𝟙 _ := by
    rw [← dg_nil, hFE]; abel
  rw [hEF, map_add, map_neg, Preadditive.comp_add, Preadditive.comp_neg, d2_aux, h3, map_sub,
    Preadditive.sub_comp, plcFE_id, Category.id_comp] at h1
  conv_lhs => rw [h1]
  abel

end Derivations

/-! ## The terms of the decompositions -/

section Terms

variable (lam : X) (i : I)

theorem plcEF_term (P Q : List (LayerData I))
    (β : End ((pres RD k).obj (ob RD (wt RD lam [up i]) []))) :
    plcEF RD k lam i (dg RD k (wt RD lam [up i]) [up i, dn i] [] P ≫ β ≫
        dg RD k (wt RD lam [up i]) [] [up i, dn i] Q) =
      dg RD k lam [up i, dn i, up i] [up i] (P.map (whL [] [up i])) ≫
        bubLU RD k lam (up i) β ≫
          dg RD k lam [up i] [up i, dn i, up i] (Q.map (whL [] [up i])) := by
  have hw : wt RD (wt RD lam [up i]) [up i, dn i] = wt RD (wt RD lam [up i]) [] := by simp
  calc plcEF RD k lam i (dg RD k (wt RD lam [up i]) [up i, dn i] [] P ≫ β ≫
        dg RD k (wt RD lam [up i]) [] [up i, dn i] Q)
      = plcL RD k lam [] [up i] [up i, dn i] [] (dg RD k (wt RD lam [up i]) [up i, dn i] [] P) ≫
          plcL RD k lam [] [up i] [] [up i, dn i]
            (β ≫ dg RD k (wt RD lam [up i]) [] [up i, dn i] Q) :=
        (plcL_comp RD k lam [] [up i] hw.symm hw _ _).symm
    _ = plcL RD k lam [] [up i] [up i, dn i] [] (dg RD k (wt RD lam [up i]) [up i, dn i] [] P) ≫
          plcL RD k lam [] [up i] [] [] β ≫
            plcL RD k lam [] [up i] [] [up i, dn i]
              (dg RD k (wt RD lam [up i]) [] [up i, dn i] Q) := by
        rw [plcL_comp RD k lam [] [up i] rfl hw]
    _ = _ := by rw [plcL_dg, plcL_dg]; rfl

theorem plcFE_term (P Q : List (LayerData I)) (β : End ((pres RD k).obj (ob RD lam []))) :
    plcFE RD k lam i (dg RD k lam [dn i, up i] [] P ≫ β ≫ dg RD k lam [] [dn i, up i] Q) =
      dg RD k lam [up i, dn i, up i] [up i] (P.map (whL [up i] [])) ≫
        bubRU RD k lam (up i) β ≫
          dg RD k lam [up i] [up i, dn i, up i] (Q.map (whL [up i] [])) := by
  have hw : wt RD (wt RD lam []) [dn i, up i] = wt RD (wt RD lam []) [] := by simp
  calc plcFE RD k lam i (dg RD k lam [dn i, up i] [] P ≫ β ≫ dg RD k lam [] [dn i, up i] Q)
      = plcL RD k lam [up i] [] [dn i, up i] [] (dg RD k lam [dn i, up i] [] P) ≫
          plcL RD k lam [up i] [] [] [dn i, up i] (β ≫ dg RD k lam [] [dn i, up i] Q) :=
        (plcL_comp RD k lam [up i] [] hw.symm hw _ _).symm
    _ = plcL RD k lam [up i] [] [dn i, up i] [] (dg RD k lam [dn i, up i] [] P) ≫
          plcL RD k lam [up i] [] [] [] β ≫
            plcL RD k lam [up i] [] [] [dn i, up i] (dg RD k lam [] [dn i, up i] Q) := by
        rw [plcL_comp RD k lam [up i] [] rfl hw]
    _ = _ := by rw [plcL_dg_nil, plcL_dg_nil]; rfl

theorem conv1 (p b a : ℕ) (β : End ((pres RD k).obj (ob RD (wt RD lam [up i]) []))) :
    dg RD k lam [up i, dn i, up i] [up i] ((dotCapEFLs i p).map (whL [] [up i])) ≫
        bubLU RD k lam (up i) β ≫ dotsU RD k lam (up i) b ≫
          dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
            dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
              (List.replicate a ([up i], .dot (dn i), [up i])) =
      dg RD k lam [up i, dn i, up i] [up i]
          (List.replicate p ([up i], .dot (dn i), [up i]) ++ [([], .cap (dn i), [up i])]) ≫
        bubLU RD k lam (up i) β ≫
          dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
            dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
              (List.replicate a ([up i], .dot (dn i), [up i])) ≫
            dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
              (List.replicate b ([up i, dn i], .dot (up i), [])) := by
  have h₁ : dg RD k lam [up i, dn i, up i] [up i] ((dotCapEFLs i p).map (whL [] [up i])) =
      dg RD k lam [up i, dn i, up i] [up i]
        (List.replicate p ([up i], .dot (dn i), [up i]) ++ [([], .cap (dn i), [up i])]) := by
    simp only [dotCapEFLs]
    dstep [] [] [] [up i] (dg_dots_cap_dn RD k _ i p).symm
    simp [whL]
  have h₂ : dotsU RD k lam (up i) b ≫
      dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] =
      dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate b ([up i, dn i], .dot (up i), [])) := by
    rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact dg_dotsR_comm RD k (up i) (s := []) (A := [([], .cup (up i), [])]) (by schain) b
  have h₃ : dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate b ([up i, dn i], .dot (up i), [])) ≫
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate a ([up i], .dot (dn i), [up i])) =
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate a ([up i], .dot (dn i), [up i])) ≫
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate b ([up i, dn i], .dot (up i), [])) := by
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact dg_swap_dots RD k lam [up i] [] [] (dn i) (up i) b a
  rw [h₁, ← Category.assoc (dotsU RD k lam (up i) b), h₂, Category.assoc, h₃]

theorem conv2 (p b a : ℕ) (β : End ((pres RD k).obj (ob RD lam []))) :
    dg RD k lam [up i, dn i, up i] [up i] ((dotCapFELs i p).map (whL [up i] [])) ≫
        bubRU RD k lam (up i) β ≫ dotsU RD k lam (up i) b ≫
          dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
            dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
              (List.replicate a ([up i, dn i], .dot (up i), [])) =
      dg RD k lam [up i, dn i, up i] [up i]
          (List.replicate p ([up i], .dot (dn i), [up i]) ++ [([up i], .cap (up i), [])]) ≫
        bubRU RD k lam (up i) β ≫
          dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
            dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
              (List.replicate a ([up i], .dot (dn i), [up i])) ≫
            dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
              (List.replicate b ([], .dot (up i), [dn i, up i])) := by
  have h₁ : dg RD k lam [up i, dn i, up i] [up i] ((dotCapFELs i p).map (whL [up i] [])) =
      dg RD k lam [up i, dn i, up i] [up i]
        (List.replicate p ([up i], .dot (dn i), [up i]) ++ [([up i], .cap (up i), [])]) := by
    simp [dotCapFELs, whL, List.map_replicate]
  have h₂ : dotsU RD k lam (up i) b ≫
      dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] =
      dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate b ([], .dot (up i), [dn i, up i])) := by
    rw [dotsU, dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact dg_dotsL_comm RD k (up i) (s := []) (B := [([], .cup (dn i), [])]) (by schain) b
  have h₃ : dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate a ([up i, dn i], .dot (up i), [])) =
      dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate a ([up i], .dot (dn i), [up i])) := by
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    dstep [] [] [up i] [] (dg_dots_cupDn RD k i _ a)
    simp [whL]
  have h₄ : dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate b ([], .dot (up i), [dn i, up i])) ≫
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate a ([up i], .dot (dn i), [up i])) =
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate a ([up i], .dot (dn i), [up i])) ≫
      dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
        (List.replicate b ([], .dot (up i), [dn i, up i])) := by
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
    exact (dg_swap_dots RD k lam [] [] [up i] (up i) (dn i) a b).symm
  rw [h₁, h₃, ← Category.assoc (dotsU RD k lam (up i) b), h₂, Category.assoc, h₄]

end Terms

/-! ## Proposition 3.5, the case `i = j = k` -/

section Prop35b

variable (lam : X) (i : I)

/-- The sum in the decomposition of `1_{E_i F_i 1_{λ+i_X}}` (`dg_decompEF`). -/
def sEF : (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i]) ⟶
    (pres RD k).obj (ob RD (wt RD lam [up i]) [up i, dn i]) :=
  ∑ f ∈ Finset.range (ip RD i (wt RD lam [up i])).toNat, ∑ g ∈ Finset.range (f + 1),
    dg RD k (wt RD lam [up i]) [up i, dn i] [] (dotCapEFLs i (f - g)) ≫
      ccwU RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + g) ≫
        dg RD k (wt RD lam [up i]) [] [up i, dn i]
          (cupDotEFLs i ((ip RD i (wt RD lam [up i])).toNat - 1 - f))

/-- The sum in the decomposition of `1_{F_i E_i 1_λ}` (`dg_decompFE`). -/
def sFE : (pres RD k).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k).obj (ob RD lam [dn i, up i]) :=
  ∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
    dg RD k lam [dn i, up i] [] (dotCapFELs i (f - g)) ≫ cwU RD k lam i (ip RD i lam - 1 + g) ≫
      dg RD k lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - f))

theorem decompEF_sEF :
    dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] [] =
      -dg RD k (wt RD lam [up i]) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) +
        sEF RD k lam i :=
  dg_decompEF RD k i _

theorem decompFE_sFE :
    dg RD k lam [dn i, up i] [dn i, up i] [] =
      -dg RD k lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) + sFE RD k lam i :=
  dg_decompFE RD k i lam

/-- A term of the first sum of KL III (3.23) (`f₁ + f₂ + f₃ + f₄ = ⟨i, λ⟩`): the cap
`E_i F_i ⟶ 1` on the left two strands with `f₃` dots on its downward leg, the counterclockwise
bubble with label `-⟨i,λ⟩-3+f₄` in the region `λ + i_X` to the left of the remaining strand, the
cup `1 ⟶ E_i F_i` with `f₁` dots on its downward leg, and `f₂` dots on the right strand. -/
def sigma1Term (f₁ f₂ f₃ f₄ : ℕ) :
    (pres RD k).obj (ob RD lam [up i, dn i, up i]) ⟶
      (pres RD k).obj (ob RD lam [up i, dn i, up i]) :=
  dg RD k lam [up i, dn i, up i] [up i]
      (List.replicate f₃ ([up i], .dot (dn i), [up i]) ++ [([], .cap (dn i), [up i])]) ≫
    bubLU RD k lam (up i) (ccwU RD k (wt RD lam [up i]) i (-ip RD i lam - 3 + f₄)) ≫
      dg RD k lam [up i] [up i, dn i, up i] [([], .cup (up i), [up i])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate f₁ ([up i], .dot (dn i), [up i])) ≫
          dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
            (List.replicate f₂ ([up i, dn i], .dot (up i), []))

/-- A term of the second sum of KL III (3.23) (`g₁ + g₂ + g₃ + g₄ = -⟨i, λ⟩ - 2`, see the module
docstring): the cap `F_i E_i ⟶ 1` on the right two strands with `g₃` dots on its downward leg,
the clockwise bubble with label `⟨i,λ⟩-1+g₄` in the region `λ` to the right of the remaining
strand, the cup `1 ⟶ F_i E_i` with `g₁` dots on its downward leg, and `g₂` dots on the left
strand. -/
def sigma2Term (g₁ g₂ g₃ g₄ : ℕ) :
    (pres RD k).obj (ob RD lam [up i, dn i, up i]) ⟶
      (pres RD k).obj (ob RD lam [up i, dn i, up i]) :=
  dg RD k lam [up i, dn i, up i] [up i]
      (List.replicate g₃ ([up i], .dot (dn i), [up i]) ++ [([up i], .cap (up i), [])]) ≫
    bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + g₄)) ≫
      dg RD k lam [up i] [up i, dn i, up i] [([up i], .cup (dn i), [])] ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
          (List.replicate g₁ ([up i], .dot (dn i), [up i])) ≫
          dg RD k lam [up i, dn i, up i] [up i, dn i, up i]
            (List.replicate g₂ ([], .dot (up i), [dn i, up i]))

theorem ip_wt_up_self : ip RD i (wt RD lam [up i]) = ip RD i lam + 2 := by
  rw [ip_wt_up, A_self]; ring

theorem term1 (hn : -1 ≤ ip RD i lam) :
    -(plcEF RD k lam i (sEF RD k lam i) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i)) =
      ∑ f ∈ Finset.range (ip RD i (wt RD lam [up i])).toNat, ∑ g ∈ Finset.range (f + 1),
        ∑ a ∈ Finset.range ((ip RD i (wt RD lam [up i])).toNat - 1 - f),
          sigma1Term RD k lam i a ((ip RD i (wt RD lam [up i])).toNat - 1 - f - 1 - a)
            (f - g) g := by
  have hN := ip_wt_up_self RD lam i
  rw [sEF, map_sum, Preadditive.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [map_sum, Preadditive.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hf' := Finset.mem_range.1 hf
  have hq : (((ip RD i (wt RD lam [up i])).toNat - 1 - f : ℕ) : ℤ) ≤ ip RD i lam + 1 := by omega
  have hk := k1 RD k lam i _ hq
  rw [plcEF_term]
  simp only [Category.assoc]
  have hc : dg RD k lam [up i] [up i, dn i, up i]
      ((cupDotEFLs i ((ip RD i (wt RD lam [up i])).toNat - 1 - f)).map (whL [] [up i])) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) =
      dg RD k lam [up i] [up i, dn i, up i]
        ([([], .cup (up i), [up i])] ++
          List.replicate ((ip RD i (wt RD lam [up i])).toNat - 1 - f)
            ([up i], .dot (dn i), [up i]) ++
          r3mixR i i i) := by
    rw [dg_comp (by simp only [cupDotEFLs]; schain) (by simp only [r3mixR]; schain)]
    congr 1
    simp [cupDotEFLs, whL, List.map_replicate]
  rw [hc, hk, Preadditive.comp_neg, Preadditive.comp_neg, neg_neg, Preadditive.comp_sum,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conv1, sigma1Term,
    show -ip RD i (wt RD lam [up i]) - 1 + (g : ℤ) = -ip RD i lam - 3 + g by rw [hN]; ring]

theorem term2 (hn : -1 ≤ ip RD i lam) :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) ≫
      plcFE RD k lam i (sFE RD k lam i) = 0 := by
  rw [sFE, map_sum, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun f hf => ?_
  rw [map_sum, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hf' := Finset.mem_range.1 hf
  have hg' := Finset.mem_range.1 hg
  have hf0 : f = 0 := by omega
  have hg0 : g = 0 := by omega
  subst hf0 hg0
  rw [plcFE_term, ← Category.assoc, dg_comp (by simp only [r3mixL]; schain)
    (by simp only [dotCapFELs]; schain)]
  have := k3 RD k lam i
  simp only [dotCapFELs, Nat.sub_self, List.replicate_zero, List.nil_append, List.map_cons,
    List.map_nil, whL, List.append_nil] at this ⊢
  rw [this, Limits.zero_comp]

theorem term3 (hn : ip RD i lam ≤ -2) :
    plcFE RD k lam i (sFE RD k lam i) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) =
      ∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
        ∑ a ∈ Finset.range ((-ip RD i lam).toNat - 1 - f),
          sigma2Term RD k lam i a ((-ip RD i lam).toNat - 1 - f - 1 - a) (f - g) g := by
  rw [sFE, map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hf' := Finset.mem_range.1 hf
  have hq : (((-ip RD i lam).toNat - 1 - f : ℕ) : ℤ) + ip RD i lam + 1 ≤ 0 := by omega
  have hk := k2 RD k lam i _ hq
  rw [plcFE_term]
  simp only [Category.assoc]
  have hc : dg RD k lam [up i] [up i, dn i, up i]
      ((cupDotFELs i ((-ip RD i lam).toNat - 1 - f)).map (whL [up i] [])) ≫
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) =
      dg RD k lam [up i] [up i, dn i, up i]
        ([([up i], .cup (dn i), [])] ++
          List.replicate ((-ip RD i lam).toNat - 1 - f) ([up i, dn i], .dot (up i), []) ++
          r3mixL i i i) := by
    rw [dg_comp (by simp only [cupDotFELs]; schain) (by simp only [r3mixL]; schain)]
    congr 1
    simp [cupDotFELs, whL, List.map_replicate]
  rw [hc, hk, Preadditive.comp_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conv2, sigma2Term]

theorem term4 (hn : ip RD i lam ≤ -2) :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) ≫
      plcEF RD k lam i (sEF RD k lam i) = 0 := by
  have h0 : (ip RD i (wt RD lam [up i])).toNat = 0 := by
    rw [ip_wt_up_self]; omega
  rw [sEF, h0, Finset.sum_range_zero, map_zero, Limits.comp_zero]

/-- Reindexing a triple sum over `f ≤ m + 1`, `g ≤ f`, `a ≤ m - f` as a sum over the
compositions `f₁ + f₂ + f₃ + f₄ = m` (with `f₁ = a`, `f₂ = m - f - a`, `f₃ = f - g`, `f₄ = g`). -/
theorem sum_reindex4 {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → ℕ → ℕ → M) (m : ℕ) :
    ∑ f ∈ Finset.range (m + 2), ∑ g ∈ Finset.range (f + 1),
        ∑ a ∈ Finset.range (m + 2 - 1 - f), F a (m + 2 - 1 - f - 1 - a) (f - g) g =
      ∑ x ∈ Finset.antidiagonal m, ∑ z ∈ Finset.antidiagonal x.1,
        ∑ y ∈ Finset.antidiagonal x.2, F y.1 y.2 z.2 z.1 := by
  rw [Finset.sum_range_succ, show m + 2 - 1 - (m + 1) = 0 by omega]
  simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero, add_zero]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf' := Finset.mem_range.1 hf
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show m + 2 - 1 - f = (m - f).succ by omega]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only
  rw [show (m - f).succ - 1 - a = m - f - a by omega]

/-- **KL III Proposition 3.5, equation (3.23)** (label `eq_r3_extra`), case `i = j = k`, repaired
form (see the module docstring): with `n = ⟨i, λ⟩`,
`r3mixL i i i - r3mixR i i i = ∑_{f₁+f₂+f₃+f₄ = n} sigma1Term f₁ f₂ f₃ f₄ +
  ∑_{g₁+g₂+g₃+g₄ = -n-2} sigma2Term g₁ g₂ g₃ g₄`,
the first sum being zero if `n < 0` and the second if `n > -2`. The sums over compositions are
written as nested sums over antidiagonals. -/
theorem prop35_b :
    dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixL i i i) -
        dg RD k lam [up i, dn i, up i] [up i, dn i, up i] (r3mixR i i i) =
      (if 0 ≤ ip RD i lam then
        ∑ x ∈ Finset.antidiagonal (ip RD i lam).toNat, ∑ z ∈ Finset.antidiagonal x.1,
          ∑ y ∈ Finset.antidiagonal x.2, sigma1Term RD k lam i y.1 y.2 z.2 z.1
      else 0) +
      (if ip RD i lam ≤ -2 then
        ∑ x ∈ Finset.antidiagonal (-ip RD i lam - 2).toNat, ∑ z ∈ Finset.antidiagonal x.1,
          ∑ y ∈ Finset.antidiagonal x.2, sigma2Term RD k lam i y.1 y.2 z.2 z.1
      else 0) := by
  by_cases h : -1 ≤ ip RD i lam
  · rw [d1 RD k lam i (decompEF_sEF RD k lam i) (decompFE_sFE RD k lam i), term1 RD k lam i h,
      term2 RD k lam i h, add_zero, if_neg (show ¬ ip RD i lam ≤ -2 by omega), add_zero]
    by_cases h0 : 0 ≤ ip RD i lam
    · rw [if_pos h0]
      have hN : (ip RD i (wt RD lam [up i])).toNat = (ip RD i lam).toNat + 2 := by
        rw [ip_wt_up_self]; omega
      rw [hN]
      exact sum_reindex4 _ _
    · rw [if_neg h0]
      have hN : (ip RD i (wt RD lam [up i])).toNat = 1 := by
        rw [ip_wt_up_self]; omega
      rw [hN]
      simp
  · rw [d2 RD k lam i (decompEF_sEF RD k lam i) (decompFE_sFE RD k lam i),
      term3 RD k lam i (by omega),
      term4 RD k lam i (by omega), sub_zero, if_neg (show ¬ 0 ≤ ip RD i lam by omega),
      if_pos (show ip RD i lam ≤ -2 by omega), zero_add]
    have hN : (-ip RD i lam).toNat = (-ip RD i lam - 2).toNat + 2 := by omega
    rw [hN]
    exact sum_reindex4 _ _

end Prop35b

end Categorification.KL3.Diagram
