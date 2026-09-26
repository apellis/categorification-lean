/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Karoubi
import Categorification.Diagrams.KL3.MixedR3Sl2
import Categorification.Diagrams.KL3.BubbleSlidesAll
import Categorification.Diagrams.KL3.Grading

/-!
# Direct sum decompositions in `U̇` (KL III Propositions 3.25 and 3.26)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.5
(TeX label `subsec_dirsumdecs`), Proposition 3.25 (TeX label `pmii-isoms`) and
Proposition 3.26 (TeX label `pmij-isoms`), in the 2-category `U̇` of Definition 3.21
(`Categorification.Diagrams.KL3.Karoubi`).

## Conventions

`UKar RD k λ' λ` is the Hom category `U̇(λ, λ')` (library order: 1-morphisms go from the left
region `λ'` to the right region `λ`; see `Categorification.Diagrams.KL3.Basic`). For a signed
sequence `t` with rightmost region `μ` (and leftmost region `λ' = μ + t_X`, given by a proof
`h : wt RD μ t = λ'`), `nfObj RD k λ' μ t h s` is the object `E_t 1_μ {s}` of `U̇`. A
homogeneous 2-morphism of degree `s - s'` is a morphism `E_t 1_μ {s} ⟶ E_{t'} 1_μ {s'}`
(`GradedBicat.homOf`).

## Proposition 3.25

Let `n = ⟨i, μ⟩ ≥ 0`. KL III's maps are, with `N = n`,

* `α = (-crossl ; α_0, …, α_{n-1}) : E_i F_i 1_μ ⟶ F_i E_i 1_μ ⊕ ⨁_s 1_μ`, where
  `α_s = ∑_{g=0}^{s}` (the cap `E_i F_i ⟶ 1` with `s - g` dots on its upward strand)
  `· ccw_{-n-1+g}` (fake bubbles), and
* `α⁻¹ = (crossr, β_0, …, β_{n-1})` with `β_s` the cup `1 ⟶ E_i F_i` with `n - 1 - s` dots.

With the shifts `1_μ {d_i (n - 1 - 2s)}` (`s = 0, …, n - 1`, the multiset of shifts of
KL III (3.60)) all components have degree `0`. We check the four families of relations of
`SumDecomp`:

* `α α⁻¹ = 1` on `E F` is the relation `eq_ident_decomp` (`dg_decompEF`), reindexed;
* `crossr (-crossl) = 1` on `F E` is `dg_decompFE` (its sum is empty for `n ≥ 0`);
* `β_s crossl = 0`: a dotted cup followed by `crossl` is a right curl with fewer than `n` dots
  on its loop, which vanishes (`dg_cupUp_crossl_eq_zero`, Lauda Proposition 5.4);
* `β_s α_t = δ_{st}`: the composite is `∑_g cw_{n-1+(t-s)-g} ccw_{-n-1+g}`, which is the
  infinite Grassmannian relation in all degrees (`grassmannian_all`) and bubble positivity.

The remaining block `crossr α_s = 0` is then automatic (`SumDecomp.b0_a`): the endomorphism
`α⁻¹ α` of `F E ⊕ ⨁ 1` is an idempotent which differs from the identity only in that block.
The case `n ≤ 0` is the mirror statement, with `dg_decompFE`, `dg_cupDn_crossr_eq_zero` and
clockwise fake bubbles.

The contexts `i'`, `i''` of the printed statement are obtained by composing with the
1-morphisms `E_{i'}` and `E_{i''}` (`wLDot`, `wRDot`), which are additive functors.

## Main results

* `sumDecompEF`, `sumDecompFE`: the decomposition data (`SumDecomp`) of Proposition 3.25.
* `prop325EF`: **KL III Proposition 3.25, first case**: for `⟨i, μ⟩ ≥ 0`,
  `E_{+i-i} 1_μ ≅ E_{-i+i} 1_μ ⊕ ⨁_{s < ⟨i,μ⟩} 1_μ {d_i (⟨i,μ⟩ - 1 - 2s)}`.
* `prop325FE`: **second case**: for `⟨i, μ⟩ ≤ 0`,
  `E_{-i+i} 1_μ ≅ E_{+i-i} 1_μ ⊕ ⨁_{s < -⟨i,μ⟩} 1_μ {d_i (-⟨i,μ⟩ - 1 - 2s)}`.
* `prop325EF_whisker`, `prop325FE_whisker`: the same after composing with arbitrary
  1-morphisms on both sides (KL III's `i'`, `i''`).
* `prop326`, `prop326_whisker`: **KL III Proposition 3.26**: for `i ≠ j`,
  `E_{+i-j} 1_μ {s} ≅ E_{-j+i} 1_μ {s}` (the sideways crossings, `eq_downup_ij-gen`), in any
  context.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Objects and morphisms of `U̇` given by normal-form diagrams -/

/-- The Hom category `U̇(λ, λ')` of KL III Definition 3.21 (library order: from the left region
`λ'` to the right region `λ`). -/
abbrev UKar (lam' lam : X) : Type _ :=
  UDotHom (pres RD k) (deg RD) (wtObj RD k lam') (wtObj RD k lam)

/-- The 1-morphism `E_t 1_μ : μ → λ'` of `U` (library: from `λ'` to `μ`), for a signed sequence
`t` with rightmost region `μ` and leftmost region `λ' = μ + t_X`. -/
abbrev nfHom (lam' μ : X) (t : List (Letter I)) (h : wt RD μ t = lam') :
    Presentation.Bicat.Hom (wtObj RD k lam') (wtObj RD k μ) :=
  ⟨ob RD μ t, h, ob_wf RD μ t, ob_endR RD μ t⟩

/-- The object `E_t 1_μ {s}` of `U̇`. -/
abbrev nfObj (lam' μ : X) (t : List (Letter I)) (h : wt RD μ t = lam') (s : ℤ) :
    UKar RD k lam' μ :=
  objOf (nfHom RD k lam' μ t h) s

variable {RD k}

/-- Membership of a normal-form diagram in a homogeneous component. -/
theorem dg_mem_homDeg {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} {d : ℤ}
    (h : (ls.map fun x => sdeg RD (wt RD μ x.2.2) x.2.1).sum = d) :
    dg RD k μ s t ls ∈ (pres RD k).homDeg (deg RD) (ob RD μ s) (ob RD μ t) d := by
  by_cases hc : SChain s ls t
  · rw [dg_of hc]
    exact diag_mem_homDeg' (by rw [degree_mkD]; exact h)
  · rw [dg_of_not hc]
    exact Submodule.zero_mem _

theorem crosslL_mem (i j : I) (μ : X) :
    dg RD k μ [up i, dn j] [dn j, up i] (crosslL i j) ∈
      (pres RD k).homDeg (deg RD) (ob RD μ [up i, dn j]) (ob RD μ [dn j, up i]) 0 := by
  rw [dg_crossl]; exact diag_mem_homDeg' (degree_crossl i j μ)

theorem crossrL_mem (i j : I) (μ : X) :
    dg RD k μ [dn j, up i] [up i, dn j] (crossrL i j) ∈
      (pres RD k).homDeg (deg RD) (ob RD μ [dn j, up i]) (ob RD μ [up i, dn j]) 0 := by
  rw [dg_crossr]; exact diag_mem_homDeg' (degree_crossr i j μ)

theorem ccwU_mem (lam : X) (i : I) (m : ℤ) :
    ccwU RD k lam i m ∈ (pres RD k).homDeg (deg RD) (ob RD lam []) (ob RD lam [])
      (2 * di C i * (m + 1 + ip RD i lam)) :=
  lin_mem_homDeg (ccwL_mem (RD := RD) (k := k) lam i m)

theorem cwU_mem (lam : X) (i : I) (m : ℤ) :
    cwU RD k lam i m ∈ (pres RD k).homDeg (deg RD) (ob RD lam []) (ob RD lam [])
      (2 * di C i * (m + 1 - ip RD i lam)) :=
  lin_mem_homDeg (cwL_mem (RD := RD) (k := k) lam i m)

theorem dotCapEFLs_mem (lam : X) (i : I) (m : ℕ) :
    dg RD k lam [up i, dn i] [] (dotCapEFLs i m) ∈
      (pres RD k).homDeg (deg RD) (ob RD lam [up i, dn i]) (ob RD lam [])
        (m * C.dot i i + di C i * (1 - ip RD i lam)) := by
  rw [show dg RD k lam [up i, dn i] [] (dotCapEFLs i m) = (pres RD k).diag (dotCapEF RD lam i m)
    by rw [dg_of (by schain)]; rfl]
  exact diag_mem_homDeg' (degree_dotCapEF lam i m)

theorem cupDotEFLs_mem (lam : X) (i : I) (m : ℕ) :
    dg RD k lam [] [up i, dn i] (cupDotEFLs i m) ∈
      (pres RD k).homDeg (deg RD) (ob RD lam []) (ob RD lam [up i, dn i])
        (di C i * (1 - ip RD i lam) + m * C.dot i i) := by
  rw [show dg RD k lam [] [up i, dn i] (cupDotEFLs i m) = (pres RD k).diag (cupDotEF RD lam i m)
    by rw [dg_of (by schain)]; rfl]
  exact diag_mem_homDeg' (degree_cupDotEF lam i m)

theorem dotCapFELs_mem (lam : X) (i : I) (m : ℕ) :
    dg RD k lam [dn i, up i] [] (dotCapFELs i m) ∈
      (pres RD k).homDeg (deg RD) (ob RD lam [dn i, up i]) (ob RD lam [])
        (m * C.dot i i + di C i * (1 + ip RD i lam)) := by
  rw [show dg RD k lam [dn i, up i] [] (dotCapFELs i m) = (pres RD k).diag (dotCapFE RD lam i m)
    by rw [dg_of (by schain)]; rfl]
  exact diag_mem_homDeg' (degree_dotCapFE lam i m)

theorem cupDotFELs_mem (lam : X) (i : I) (m : ℕ) :
    dg RD k lam [] [dn i, up i] (cupDotFELs i m) ∈
      (pres RD k).homDeg (deg RD) (ob RD lam []) (ob RD lam [dn i, up i])
        (di C i * (1 + ip RD i lam) + m * C.dot i i) := by
  rw [show dg RD k lam [] [dn i, up i] (cupDotFELs i m) = (pres RD k).diag (cupDotFE RD lam i m)
    by rw [dg_of (by schain)]; rfl]
  exact diag_mem_homDeg' (degree_cupDotFE lam i m)

/-! ## Bubble sums -/

section BubbleSums

variable (ρ : X) (i : I)

/-- `∑_{g=0}^{T} cw_{n-1+e-g} ccw_{-n-1+g} = δ_{e,0}` for `e ≤ T` (`n = ⟨i, ρ⟩`): the infinite
Grassmannian relation in degree `e`, the terms with `g > e` vanishing by positivity. -/
theorem sum_cw_ccw (e : ℤ) (T : ℕ) (hT : e ≤ T) :
    ∑ g ∈ Finset.range (T + 1),
      cwU RD k ρ i (ip RD i ρ - 1 + (e - g)) ≫ ccwU RD k ρ i (-ip RD i ρ - 1 + g) =
      if e = 0 then 𝟙 _ else 0 := by
  by_cases he : 0 ≤ e
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have hsub : Finset.range (d + 1) ⊆ Finset.range (T + 1) :=
      Finset.range_subset.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · have := grassmannian_all RD k ρ i d
      simp only [Nat.cast_inj, Nat.cast_eq_zero]
      rw [← this]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [endEmpty_comm]
    · intro g _ hg
      rw [Finset.mem_range] at hg
      rw [cwU_eq_zero RD k ρ i _ (by omega), Limits.zero_comp]
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [cwU_eq_zero RD k ρ i _ (by omega), Limits.zero_comp]

/-- `∑_{g=0}^{T} ccw_{-n-1+e-g} cw_{n-1+g} = δ_{e,0}` for `e ≤ T`. -/
theorem sum_ccw_cw (e : ℤ) (T : ℕ) (hT : e ≤ T) :
    ∑ g ∈ Finset.range (T + 1),
      ccwU RD k ρ i (-ip RD i ρ - 1 + (e - g)) ≫ cwU RD k ρ i (ip RD i ρ - 1 + g) =
      if e = 0 then 𝟙 _ else 0 := by
  by_cases he : 0 ≤ e
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have hsub : Finset.range (d + 1) ⊆ Finset.range (T + 1) :=
      Finset.range_subset.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · have := grassmannian_all RD k ρ i d
      simp only [Nat.cast_inj, Nat.cast_eq_zero]
      rw [← this, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [Finset.mem_range] at hg
      congr 2
      · push_cast [Nat.cast_sub (show g ≤ d by omega)]; ring
      · push_cast [Nat.cast_sub (show g ≤ d by omega)]; ring
    · intro g _ hg
      rw [Finset.mem_range] at hg
      rw [ccwU_eq_zero RD k ρ i _ (by omega), Limits.zero_comp]
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [ccwU_eq_zero RD k ρ i _ (by omega), Limits.zero_comp]

end BubbleSums

/-! ## The components of the decompositions -/

section Components

variable (RD k) (i : I) (lam : X)

/-- KL III's `α_s : E_i F_i 1_λ ⟶ 1_λ` (proof of Proposition 3.25):
`∑_{g=0}^{s}` (cap with `s - g` dots) `ccw_{-n-1+g}`. -/
def alphaEF (s : ℕ) : (pres RD k).obj (ob RD lam [up i, dn i]) ⟶ (pres RD k).obj (ob RD lam []) :=
  ∑ g ∈ Finset.range (s + 1),
    dg RD k lam [up i, dn i] [] (dotCapEFLs i (s - g)) ≫ ccwU RD k lam i (-ip RD i lam - 1 + g)

/-- KL III's `s`-th component of `α⁻¹` on the summands `1_λ`: the cup `1_λ ⟶ E_i F_i` with
`n - 1 - s` dots. -/
def betaEF (s : ℕ) : (pres RD k).obj (ob RD lam []) ⟶ (pres RD k).obj (ob RD lam [up i, dn i]) :=
  dg RD k lam [] [up i, dn i] (cupDotEFLs i ((ip RD i lam).toNat - 1 - s))

/-- The mirror `α_s : F_i E_i 1_λ ⟶ 1_λ`: `∑_{g=0}^{s}` (cap with `s - g` dots)
`cw_{n-1+g}`. -/
def alphaFE (s : ℕ) : (pres RD k).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k).obj (ob RD lam []) :=
  ∑ g ∈ Finset.range (s + 1),
    dg RD k lam [dn i, up i] [] (dotCapFELs i (s - g)) ≫ cwU RD k lam i (ip RD i lam - 1 + g)

/-- The mirror `β_s`: the cup `1_λ ⟶ F_i E_i` with `-n - 1 - s` dots. -/
def betaFE (s : ℕ) : (pres RD k).obj (ob RD lam []) ⟶ (pres RD k).obj (ob RD lam [dn i, up i]) :=
  dg RD k lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - s))

variable {RD k}

theorem alphaEF_mem (s : ℕ) :
    alphaEF RD k i lam s ∈ (pres RD k).homDeg (deg RD) (ob RD lam [up i, dn i]) (ob RD lam [])
      (di C i * (2 * s + 1 - ip RD i lam)) := by
  refine Submodule.sum_mem _ fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  refine mem_homDeg_of_eq (comp_mem_homDeg (dotCapEFLs_mem lam i (s - g)) (ccwU_mem lam i _)) ?_
  rw [← two_mul_di C i]
  push_cast [Nat.cast_sub (show g ≤ s by omega)]
  ring

theorem betaEF_mem (s : ℕ) (hs : s < (ip RD i lam).toNat) :
    betaEF RD k i lam s ∈ (pres RD k).homDeg (deg RD) (ob RD lam []) (ob RD lam [up i, dn i])
      (di C i * (ip RD i lam - 1 - 2 * s)) := by
  refine mem_homDeg_of_eq (cupDotEFLs_mem lam i _) ?_
  have hc : (((ip RD i lam).toNat - 1 - s : ℕ) : ℤ) = ip RD i lam - 1 - s := by omega
  rw [hc, ← two_mul_di C i]
  ring

theorem alphaFE_mem (s : ℕ) :
    alphaFE RD k i lam s ∈ (pres RD k).homDeg (deg RD) (ob RD lam [dn i, up i]) (ob RD lam [])
      (di C i * (2 * s + 1 + ip RD i lam)) := by
  refine Submodule.sum_mem _ fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  refine mem_homDeg_of_eq (comp_mem_homDeg (dotCapFELs_mem lam i (s - g)) (cwU_mem lam i _)) ?_
  rw [← two_mul_di C i]
  push_cast [Nat.cast_sub (show g ≤ s by omega)]
  ring

theorem betaFE_mem (s : ℕ) (hs : s < (-ip RD i lam).toNat) :
    betaFE RD k i lam s ∈ (pres RD k).homDeg (deg RD) (ob RD lam []) (ob RD lam [dn i, up i])
      (di C i * (-ip RD i lam - 1 - 2 * s)) := by
  refine mem_homDeg_of_eq (cupDotFELs_mem lam i _) ?_
  have hc : (((-ip RD i lam).toNat - 1 - s : ℕ) : ℤ) = -ip RD i lam - 1 - s := by omega
  rw [hc, ← two_mul_di C i]
  ring

/-! ### The relations, case `⟨i, λ⟩ ≥ 0` -/

/-- `α α⁻¹ = 1` on `E_i F_i 1_λ`: the relation `eq_ident_decomp`. -/
theorem total_EF :
    (-dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i)) ≫
        dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) +
      ∑ s ∈ Finset.range (ip RD i lam).toNat, alphaEF RD k i lam s ≫ betaEF RD k i lam s =
      𝟙 _ := by
  have h := dg_decompEF RD k i lam
  rw [dg_nil] at h
  rw [h, Preadditive.neg_comp, dg_comp (by schain) (by schain)]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaEF, betaEF, Preadditive.sum_comp]
  simp only [Category.assoc]

/-- `(-crossl) crossr = 1` on `F_i E_i 1_λ` for `⟨i, λ⟩ ≥ 0`. -/
theorem b0a0_EF (hn : 0 ≤ ip RD i lam) :
    dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫
        (-dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i)) = 𝟙 _ := by
  have h := dg_decompFE RD k i lam
  rw [show (-ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero, add_zero, dg_nil] at h
  rw [Preadditive.comp_neg, dg_comp (by schain) (by schain), h]

/-- A cup with fewer than `n` dots followed by `crossl` vanishes. -/
theorem ba0_EF (s : ℕ) (hs : s < (ip RD i lam).toNat) :
    betaEF RD k i lam s ≫ (-dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i)) = 0 := by
  rw [Preadditive.comp_neg, betaEF, cupDotEFLs, dg_dots_cupUp, dg_comp (by schain) (by schain),
    dg_cupUp_crossl_eq_zero RD k lam i _ (by omega), neg_zero]

/-- `β_s α_t = δ_{st}`. -/
theorem ba_EF (s t : ℕ) (hs : s < (ip RD i lam).toNat) (ht : t < (ip RD i lam).toNat) :
    betaEF RD k i lam s ≫ alphaEF RD k i lam t = if s = t then 𝟙 _ else 0 := by
  rw [alphaEF, Preadditive.comp_sum]
  have hterm : ∀ g ∈ Finset.range (t + 1),
      betaEF RD k i lam s ≫ dg RD k lam [up i, dn i] [] (dotCapEFLs i (t - g)) ≫
          ccwU RD k lam i (-ip RD i lam - 1 + g) =
        cwU RD k lam i (ip RD i lam - 1 + (((t : ℤ) - s) - g)) ≫
          ccwU RD k lam i (-ip RD i lam - 1 + g) := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    rw [← Category.assoc, betaEF, dotCapEFLs, ← dg_dots_cap_dn, dg_comp (by schain) (by schain)]
    have e : ip RD i lam - 1 + (((t : ℤ) - s) - g) =
        (((ip RD i lam).toNat - 1 - s + (t - g) : ℕ) : ℤ) := by
      omega
    rw [e, cwU_of_nonneg, cwLs, cupDotEFLs, List.replicate_add]
    simp only [List.append_assoc]
  rw [Finset.sum_congr rfl hterm, sum_cw_ccw lam i _ t (by omega)]
  by_cases hst : s = t
  · subst hst; simp
  · rw [if_neg (by omega), if_neg hst]

/-! ### The relations, case `⟨i, λ⟩ ≤ 0` -/

/-- `α α⁻¹ = 1` on `F_i E_i 1_λ`: the relation `eq_ident_decomp`. -/
theorem total_FE :
    (-dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i)) ≫
        dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) +
      ∑ s ∈ Finset.range (-ip RD i lam).toNat, alphaFE RD k i lam s ≫ betaFE RD k i lam s =
      𝟙 _ := by
  have h := dg_decompFE RD k i lam
  rw [dg_nil] at h
  rw [h, Preadditive.neg_comp, dg_comp (by schain) (by schain)]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaFE, betaFE, Preadditive.sum_comp]
  simp only [Category.assoc]

/-- `(-crossr) crossl = 1` on `E_i F_i 1_λ` for `⟨i, λ⟩ ≤ 0`. -/
theorem b0a0_FE (hn : ip RD i lam ≤ 0) :
    dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫
        (-dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i)) = 𝟙 _ := by
  have h := dg_decompEF RD k i lam
  rw [show (ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero, add_zero, dg_nil] at h
  rw [Preadditive.comp_neg, dg_comp (by schain) (by schain), h]

/-- A cup `1 ⟶ F_i E_i` with fewer than `-n` dots followed by `crossr` vanishes. -/
theorem ba0_FE (s : ℕ) (hs : s < (-ip RD i lam).toNat) :
    betaFE RD k i lam s ≫ (-dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i)) = 0 := by
  rw [Preadditive.comp_neg, betaFE, cupDotFELs, dg_comp (by schain) (by schain),
    dg_cupDn_crossr_eq_zero RD k i lam _ (by omega), neg_zero]

/-- `β_s α_t = δ_{st}` (mirror case). -/
theorem ba_FE (s t : ℕ) (hs : s < (-ip RD i lam).toNat) (ht : t < (-ip RD i lam).toNat) :
    betaFE RD k i lam s ≫ alphaFE RD k i lam t = if s = t then 𝟙 _ else 0 := by
  rw [alphaFE, Preadditive.comp_sum]
  have hterm : ∀ g ∈ Finset.range (t + 1),
      betaFE RD k i lam s ≫ dg RD k lam [dn i, up i] [] (dotCapFELs i (t - g)) ≫
          cwU RD k lam i (ip RD i lam - 1 + g) =
        ccwU RD k lam i (-ip RD i lam - 1 + (((t : ℤ) - s) - g)) ≫
          cwU RD k lam i (ip RD i lam - 1 + g) := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    rw [← Category.assoc, betaFE, dotCapFELs, dg_dots_cap_up, dg_comp (by schain) (by schain)]
    have e : -ip RD i lam - 1 + (((t : ℤ) - s) - g) =
        (((-ip RD i lam).toNat - 1 - s + (t - g) : ℕ) : ℤ) := by
      omega
    rw [e, ccwU_of_nonneg, ccwLs, cupDotFELs, List.replicate_add]
    simp only [List.append_assoc]
  rw [Finset.sum_congr rfl hterm, sum_ccw_cw lam i _ t (by omega)]
  by_cases hst : s = t
  · subst hst; simp
  · rw [if_neg (by omega), if_neg hst]

end Components

/-! ## Proposition 3.25 in `U̇` -/

section Prop325

variable (RD k) (i : I) (lam : X)

theorem wt_up_dn : wt RD lam [up i, dn i] = lam := by
  simp [sh, add_neg_cancel_left]

theorem wt_dn_up : wt RD lam [dn i, up i] = lam := by
  simp [sh, neg_add_cancel_left]

/-- `E_{+i-i} 1_λ {s} = E_i F_i 1_λ {s}` in `U̇(λ, λ)`. -/
abbrev objEF (s : ℤ) : UKar RD k lam lam := nfObj RD k lam lam [up i, dn i] (wt_up_dn RD i lam) s

/-- `E_{-i+i} 1_λ {s} = F_i E_i 1_λ {s}` in `U̇(λ, λ)`. -/
abbrev objFE (s : ℤ) : UKar RD k lam lam := nfObj RD k lam lam [dn i, up i] (wt_dn_up RD i lam) s

/-- `1_λ {s}` in `U̇(λ, λ)`. -/
abbrev objOne (s : ℤ) : UKar RD k lam lam := nfObj RD k lam lam [] rfl s

/-- The decomposition data of KL III Proposition 3.25 for `⟨i, λ⟩ ≥ 0`. -/
def sumDecompEF (hn : 0 ≤ ip RD i lam) :
    SumDecomp (objEF RD k i lam 0) (objFE RD k i lam 0)
      (fun s : Fin (ip RD i lam).toNat => objOne RD k lam (di C i * (ip RD i lam - 1 - 2 * s))) where
  a0 := homOf (-dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i))
    (Submodule.neg_mem _ (mem_homDeg_of_eq (crosslL_mem i i lam) (by ring)))
  b0 := homOf (dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i))
    (mem_homDeg_of_eq (crossrL_mem i i lam) (by ring))
  a s := homOf (alphaEF RD k i lam s) (mem_homDeg_of_eq (alphaEF_mem i lam s) (by ring))
  b s := homOf (betaEF RD k i lam s) (mem_homDeg_of_eq (betaEF_mem i lam s s.2) (by ring))
  total := by
    simp only [homOf_comp]
    rw [sum_homOf, add_homOf]
    refine homOf_eq_id ?_ _
    rw [Fin.sum_univ_eq_sum_range (fun s => alphaEF RD k i lam s ≫ betaEF RD k i lam s)]
    exact total_EF i lam
  b0_a0 := by
    rw [homOf_comp]
    exact homOf_eq_id (b0a0_EF i lam hn) _
  b_a0 s := by
    rw [homOf_comp]
    exact homOf_eq_zero (ba0_EF i lam s s.2) _
  b_a_self s := by
    rw [homOf_comp]
    refine homOf_eq_id ?_ _
    rw [ba_EF i lam s s s.2 s.2, if_pos rfl]
  b_a_ne s t hst := by
    rw [homOf_comp]
    refine homOf_eq_zero ?_ _
    rw [ba_EF i lam s t s.2 t.2, if_neg (fun h => hst (Fin.ext h))]

/-- The decomposition data of KL III Proposition 3.25 for `⟨i, λ⟩ ≤ 0`. -/
def sumDecompFE (hn : ip RD i lam ≤ 0) :
    SumDecomp (objFE RD k i lam 0) (objEF RD k i lam 0)
      (fun s : Fin (-ip RD i lam).toNat =>
        objOne RD k lam (di C i * (-ip RD i lam - 1 - 2 * s))) where
  a0 := homOf (-dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i))
    (Submodule.neg_mem _ (mem_homDeg_of_eq (crossrL_mem i i lam) (by ring)))
  b0 := homOf (dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i))
    (mem_homDeg_of_eq (crosslL_mem i i lam) (by ring))
  a s := homOf (alphaFE RD k i lam s) (mem_homDeg_of_eq (alphaFE_mem i lam s) (by ring))
  b s := homOf (betaFE RD k i lam s) (mem_homDeg_of_eq (betaFE_mem i lam s s.2) (by ring))
  total := by
    simp only [homOf_comp]
    rw [sum_homOf, add_homOf]
    refine homOf_eq_id ?_ _
    rw [Fin.sum_univ_eq_sum_range (fun s => alphaFE RD k i lam s ≫ betaFE RD k i lam s)]
    exact total_FE i lam
  b0_a0 := by
    rw [homOf_comp]
    exact homOf_eq_id (b0a0_FE i lam hn) _
  b_a0 s := by
    rw [homOf_comp]
    exact homOf_eq_zero (ba0_FE i lam s s.2) _
  b_a_self s := by
    rw [homOf_comp]
    refine homOf_eq_id ?_ _
    rw [ba_FE i lam s s s.2 s.2, if_pos rfl]
  b_a_ne s t hst := by
    rw [homOf_comp]
    refine homOf_eq_zero ?_ _
    rw [ba_FE i lam s t s.2 t.2, if_neg (fun h => hst (Fin.ext h))]

/-- **KL III Proposition 3.25, first case** (`⟨i, λ⟩ ≥ 0`, empty contexts `i'`, `i''`): in `U̇`,
`E_{+i-i} 1_λ ≅ E_{-i+i} 1_λ ⊕ ⨁_{s=0}^{⟨i,λ⟩-1} 1_λ {d_i (⟨i,λ⟩ - 1 - 2s)}`, i.e.
`E_i F_i 1_λ ≅ F_i E_i 1_λ ⊕ 1_λ^{⊕[⟨i,λ⟩]_i}` with the shifts of KL III (3.60). -/
def prop325EF (hn : 0 ≤ ip RD i lam) :
    objEF RD k i lam 0 ≅ objFE RD k i lam 0 ⊞
      ⨁ (fun s : Fin (ip RD i lam).toNat => objOne RD k lam (di C i * (ip RD i lam - 1 - 2 * s))) :=
  (sumDecompEF RD k i lam hn).iso

/-- **KL III Proposition 3.25, second case** (`⟨i, λ⟩ ≤ 0`, empty contexts): in `U̇`,
`E_{-i+i} 1_λ ≅ E_{+i-i} 1_λ ⊕ ⨁_{s=0}^{-⟨i,λ⟩-1} 1_λ {d_i (-⟨i,λ⟩ - 1 - 2s)}`. -/
def prop325FE (hn : ip RD i lam ≤ 0) :
    objFE RD k i lam 0 ≅ objEF RD k i lam 0 ⊞
      ⨁ (fun s : Fin (-ip RD i lam).toNat =>
        objOne RD k lam (di C i * (-ip RD i lam - 1 - 2 * s))) :=
  (sumDecompFE RD k i lam hn).iso

variable {RD k}

/-- The composition with 1-morphisms `a` on the left and `b` on the right (KL III's contexts
`i'` and `i''`), as an additive functor `U̇(λ, λ) ⥤ U̇(ρ', ρ)`. -/
abbrev ctxDot {ρ' ρ : X} (a : Presentation.Bicat.Hom (wtObj RD k ρ') (wtObj RD k lam))
    (b : Presentation.Bicat.Hom (wtObj RD k lam) (wtObj RD k ρ)) :
    UKar RD k lam lam ⥤ UKar RD k ρ' ρ :=
  wLDot (deg RD) a ⋙ wRDot (deg RD) b

/-- **KL III Proposition 3.25, first case, with contexts**: for 1-morphisms `a = E_{i'}` and
`b = E_{i''}` (any 1-morphisms of `U`) and `⟨i, λ⟩ ≥ 0` (`λ = μ` of KL III, the region to the
right of the pair), `E_{i' +i -i i''} ≅ E_{i' -i +i i''} ⊕ E_{i' i''}^{⊕[⟨i,λ⟩]_i}`. -/
def prop325EF_whisker {ρ' ρ : X} (a : Presentation.Bicat.Hom (wtObj RD k ρ') (wtObj RD k lam))
    (b : Presentation.Bicat.Hom (wtObj RD k lam) (wtObj RD k ρ)) (hn : 0 ≤ ip RD i lam) :
    (ctxDot lam a b).obj (objEF RD k i lam 0) ≅ (ctxDot lam a b).obj (objFE RD k i lam 0) ⊞
      ⨁ (fun s : Fin (ip RD i lam).toNat =>
        (ctxDot lam a b).obj (objOne RD k lam (di C i * (ip RD i lam - 1 - 2 * s)))) :=
  ((sumDecompEF RD k i lam hn).map (ctxDot lam a b)).iso

/-- **KL III Proposition 3.25, second case, with contexts** (`⟨i, λ⟩ ≤ 0`). -/
def prop325FE_whisker {ρ' ρ : X} (a : Presentation.Bicat.Hom (wtObj RD k ρ') (wtObj RD k lam))
    (b : Presentation.Bicat.Hom (wtObj RD k lam) (wtObj RD k ρ)) (hn : ip RD i lam ≤ 0) :
    (ctxDot lam a b).obj (objFE RD k i lam 0) ≅ (ctxDot lam a b).obj (objEF RD k i lam 0) ⊞
      ⨁ (fun s : Fin (-ip RD i lam).toNat =>
        (ctxDot lam a b).obj (objOne RD k lam (di C i * (-ip RD i lam - 1 - 2 * s)))) :=
  ((sumDecompFE RD k i lam hn).map (ctxDot lam a b)).iso

end Prop325

/-! ## Proposition 3.26 in `U̇` -/

section Prop326

variable (RD k)

theorem wt_dn_up_eq (i j : I) (μ : X) : wt RD μ [dn j, up i] = wt RD μ [up i, dn j] := by
  simp only [wt_cons, wt_nil]; abel

/-- **KL III Proposition 3.26** (empty context): for `i ≠ j`, the sideways crossings give a
degree-zero isomorphism `E_{+i-j} 1_μ {s} ≅ E_{-j+i} 1_μ {s}` in `U̇` (`eq_downup_ij-gen`). -/
def prop326 (i j : I) (h : i ≠ j) (μ : X) (s : ℤ) :
    nfObj RD k (wt RD μ [up i, dn j]) μ [up i, dn j] rfl s ≅
      nfObj RD k (wt RD μ [up i, dn j]) μ [dn j, up i] (wt_dn_up_eq RD i j μ) s where
  hom := homOf (dg RD k μ [up i, dn j] [dn j, up i] (crosslL i j))
    (mem_homDeg_of_eq (crosslL_mem i j μ) (by ring))
  inv := homOf (dg RD k μ [dn j, up i] [up i, dn j] (crossrL i j))
    (mem_homDeg_of_eq (crossrL_mem i j μ) (by ring))
  hom_inv_id := by
    rw [homOf_comp]
    refine homOf_eq_id ?_ _
    rw [dg_crossl, dg_crossr]
    exact crossl_comp_crossr RD k i j h μ
  inv_hom_id := by
    rw [homOf_comp]
    refine homOf_eq_id ?_ _
    rw [dg_crossl, dg_crossr]
    exact crossr_comp_crossl RD k i j h μ

/-- **KL III Proposition 3.26 with contexts**: `E_{…+i-j…} 1_λ ≅ E_{…-j+i…} 1_λ` for `i ≠ j`,
for arbitrary 1-morphisms `a`, `b` composed on the left and on the right. -/
def prop326_whisker (i j : I) (h : i ≠ j) (μ : X) (s : ℤ) {ρ' ρ : X}
    (a : Presentation.Bicat.Hom (wtObj RD k ρ') (wtObj RD k (wt RD μ [up i, dn j])))
    (b : Presentation.Bicat.Hom (wtObj RD k μ) (wtObj RD k ρ)) :
    (wLDot (deg RD) a ⋙ wRDot (deg RD) b).obj
        (nfObj RD k (wt RD μ [up i, dn j]) μ [up i, dn j] rfl s) ≅
      (wLDot (deg RD) a ⋙ wRDot (deg RD) b).obj
        (nfObj RD k (wt RD μ [up i, dn j]) μ [dn j, up i] (wt_dn_up_eq RD i j μ) s) :=
  (wLDot (deg RD) a ⋙ wRDot (deg RD) b).mapIso (prop326 RD k i j h μ s)

end Prop326

end Categorification.KL3.Diagram
