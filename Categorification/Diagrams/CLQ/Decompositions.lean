/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.MixedR3Sl2
import Categorification.Diagrams.CLQ.MixedR3
import Categorification.Diagrams.CLQ.BubbleSlidesAll
import Categorification.Diagrams.CLQ.BubbleSlidesEq
import Categorification.Diagrams.KL3.Decompositions

/-!
# The `𝔰𝔩₂` decompositions in Cautis–Lauda's `U_Q(g)`

Cautis–Lauda, arXiv:1111.1431v3, Definition 1.1 (`r = 1`; `CLQ.pres RD k sc`): the relations
(1.14)–(1.15) that make the maps `E_i F_i 1_λ → F_i E_i 1_λ ⊕ 1_λ^{⊕⟨i,λ⟩}` (and the mirror maps)
invertible, in the form of Khovanov–Lauda, arXiv:0807.3250v1, Proposition 3.25. The components
are those of the KL III version (`KL3.Diagram.alphaEF`, `KL3.Diagram.betaEF`, ...), with the
relations of `U_Q(g)` in place of those of KL III: the decomposition relations
(`dg_decompEF`, `dg_decompFE`), the vanishing of right curls with few dots
(`dg_cupUp_crossl_eq_zero`, `dg_cupDn_crossr_eq_zero`) and the infinite Grassmannian relation
(`grassmannian_all`). Only the ungraded morphisms are used.

For `i ≠ j` the sideways crossings are inverse up to the unit `t_ij` of `sc`
(`crossl_comp_smul_crossr`, `smul_crossr_comp_crossl`).
-/

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Bubble sums -/

section BubbleSums

variable {RD k sc} (ρ : X) (i : I)

/-- `∑_{g=0}^{T} cw_{n-1+e-g} ccw_{-n-1+g} = δ_{e,0}` for `e ≤ T` (`n = ⟨i, ρ⟩`): the infinite
Grassmannian relation in degree `e`, the terms with `g > e` vanishing by positivity. -/
theorem sum_cw_ccw (e : ℤ) (T : ℕ) (hT : e ≤ T) :
    ∑ g ∈ Finset.range (T + 1),
      NF.cwU (pres RD k sc) ρ i (ip RD i ρ - 1 + (e - g)) ≫ NF.ccwU (pres RD k sc) ρ i (-ip RD i ρ - 1 + g) =
      if e = 0 then 𝟙 _ else 0 := by
  by_cases he : 0 ≤ e
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have hsub : Finset.range (d + 1) ⊆ Finset.range (T + 1) :=
      Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · have := grassmannian_all RD k sc ρ i d
      simp only [Nat.cast_eq_zero]
      rw [← this]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [endEmpty_comm]
    · intro g _ hg
      rw [Finset.mem_range] at hg
      rw [cwU_eq_zero RD k sc ρ i _ (by omega), Limits.zero_comp]
  · rw [ite_eq_right (by omega)]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [cwU_eq_zero RD k sc ρ i _ (by omega), Limits.zero_comp]

/-- `∑_{g=0}^{T} ccw_{-n-1+e-g} cw_{n-1+g} = δ_{e,0}` for `e ≤ T`. -/
theorem sum_ccw_cw (e : ℤ) (T : ℕ) (hT : e ≤ T) :
    ∑ g ∈ Finset.range (T + 1),
      NF.ccwU (pres RD k sc) ρ i (-ip RD i ρ - 1 + (e - g)) ≫ NF.cwU (pres RD k sc) ρ i (ip RD i ρ - 1 + g) =
      if e = 0 then 𝟙 _ else 0 := by
  by_cases he : 0 ≤ e
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have hsub : Finset.range (d + 1) ⊆ Finset.range (T + 1) :=
      Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · have := grassmannian_all RD k sc ρ i d
      simp only [Nat.cast_eq_zero]
      rw [← this, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [Finset.mem_range] at hg
      congr 2
      · push_cast [Nat.cast_sub (show g ≤ d by omega)]; ring
      · push_cast [Nat.cast_sub (show g ≤ d by omega)]; ring
    · intro g _ hg
      rw [Finset.mem_range] at hg
      rw [ccwU_eq_zero RD k sc ρ i _ (by omega), Limits.zero_comp]
  · rw [ite_eq_right (by omega)]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [ccwU_eq_zero RD k sc ρ i _ (by omega), Limits.zero_comp]

end BubbleSums

/-! ## The components of the decompositions -/

section Components

variable (i : I) (lam : X)

/-- KL III's `α_s : E_i F_i 1_λ ⟶ 1_λ` (proof of Proposition 3.25):
`∑_{g=0}^{s}` (cap with `s - g` dots) `ccw_{-n-1+g}`. -/
def alphaEF (s : ℕ) : (pres RD k sc).obj (ob RD lam [up i, dn i]) ⟶ (pres RD k sc).obj (ob RD lam []) :=
  ∑ g ∈ Finset.range (s + 1),
    NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i (s - g)) ≫ NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + g)

/-- KL III's `s`-th component of `α⁻¹` on the summands `1_λ`: the cup `1_λ ⟶ E_i F_i` with
`n - 1 - s` dots. -/
def betaEF (s : ℕ) : (pres RD k sc).obj (ob RD lam []) ⟶ (pres RD k sc).obj (ob RD lam [up i, dn i]) :=
  NF.dg (pres RD k sc) lam [] [up i, dn i] (cupDotEFLs i ((ip RD i lam).toNat - 1 - s))

/-- The mirror `α_s : F_i E_i 1_λ ⟶ 1_λ`: `∑_{g=0}^{s}` (cap with `s - g` dots)
`cw_{n-1+g}`. -/
def alphaFE (s : ℕ) : (pres RD k sc).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k sc).obj (ob RD lam []) :=
  ∑ g ∈ Finset.range (s + 1),
    NF.dg (pres RD k sc) lam [dn i, up i] [] (dotCapFELs i (s - g)) ≫ NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + g)

/-- The mirror `β_s`: the cup `1_λ ⟶ F_i E_i` with `-n - 1 - s` dots. -/
def betaFE (s : ℕ) : (pres RD k sc).obj (ob RD lam []) ⟶ (pres RD k sc).obj (ob RD lam [dn i, up i]) :=
  NF.dg (pres RD k sc) lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - s))

variable {RD k sc}

/-! ### The relations, case `⟨i, λ⟩ ≥ 0` -/

/-- `α α⁻¹ = 1` on `E_i F_i 1_λ`: the relation `eq_ident_decomp`. -/
theorem total_EF :
    (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i)) ≫
        NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i) +
      ∑ s ∈ Finset.range (ip RD i lam).toNat, alphaEF RD k sc i lam s ≫ betaEF RD k sc i lam s =
      𝟙 _ := by
  have h := dg_decompEF RD k sc i lam
  rw [NF.dg_nil] at h
  rw [h, Preadditive.neg_comp, NF.dg_comp (by schain) (by schain)]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaEF, betaEF, Preadditive.sum_comp]
  simp only [Category.assoc]

/-- `(-crossl) crossr = 1` on `F_i E_i 1_λ` for `⟨i, λ⟩ ≥ 0`. -/
theorem b0a0_EF (hn : 0 ≤ ip RD i lam) :
    NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i) ≫
        (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i)) = 𝟙 _ := by
  have h := dg_decompFE RD k sc i lam
  rw [show (-ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero, add_zero, NF.dg_nil] at h
  rw [Preadditive.comp_neg, NF.dg_comp (by schain) (by schain), h]

/-- A cup with fewer than `n` dots followed by `crossl` vanishes. -/
theorem ba0_EF (s : ℕ) (hs : s < (ip RD i lam).toNat) :
    betaEF RD k sc i lam s ≫ (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i)) = 0 := by
  rw [Preadditive.comp_neg, betaEF, cupDotEFLs, dg_dots_cupUp, NF.dg_comp (by schain) (by schain),
    dg_cupUp_crossl_eq_zero RD k sc lam i _ (by omega), neg_zero]

/-- `β_s α_t = δ_{st}`. -/
theorem ba_EF (s t : ℕ) (hs : s < (ip RD i lam).toNat) (ht : t < (ip RD i lam).toNat) :
    betaEF RD k sc i lam s ≫ alphaEF RD k sc i lam t = if s = t then 𝟙 _ else 0 := by
  rw [alphaEF, Preadditive.comp_sum]
  have hterm : ∀ g ∈ Finset.range (t + 1),
      betaEF RD k sc i lam s ≫ NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i (t - g)) ≫
          NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + g) =
        NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + (((t : ℤ) - s) - g)) ≫
          NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + g) := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    rw [← Category.assoc, betaEF, dotCapEFLs, ← dg_dots_cap_dn, NF.dg_comp (by schain) (by schain)]
    have e : ip RD i lam - 1 + (((t : ℤ) - s) - g) =
        (((ip RD i lam).toNat - 1 - s + (t - g) : ℕ) : ℤ) := by
      omega
    rw [e, NF.cwU_of_nonneg, cwLs, cupDotEFLs, List.replicate_add]
    simp only [List.append_assoc]
  rw [Finset.sum_congr rfl hterm, sum_cw_ccw lam i _ t (by omega)]
  by_cases hst : s = t
  · subst hst; simp
  · rw [ite_eq_right (by omega), ite_eq_right hst]

/-! ### The relations, case `⟨i, λ⟩ ≤ 0` -/

/-- `α α⁻¹ = 1` on `F_i E_i 1_λ`: the relation `eq_ident_decomp`. -/
theorem total_FE :
    (-NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i)) ≫
        NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i) +
      ∑ s ∈ Finset.range (-ip RD i lam).toNat, alphaFE RD k sc i lam s ≫ betaFE RD k sc i lam s =
      𝟙 _ := by
  have h := dg_decompFE RD k sc i lam
  rw [NF.dg_nil] at h
  rw [h, Preadditive.neg_comp, NF.dg_comp (by schain) (by schain)]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaFE, betaFE, Preadditive.sum_comp]
  simp only [Category.assoc]

/-- `(-crossr) crossl = 1` on `E_i F_i 1_λ` for `⟨i, λ⟩ ≤ 0`. -/
theorem b0a0_FE (hn : ip RD i lam ≤ 0) :
    NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i) ≫
        (-NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i)) = 𝟙 _ := by
  have h := dg_decompEF RD k sc i lam
  rw [show (ip RD i lam).toNat = 0 by omega, Finset.sum_range_zero, add_zero, NF.dg_nil] at h
  rw [Preadditive.comp_neg, NF.dg_comp (by schain) (by schain), h]

/-- A cup `1 ⟶ F_i E_i` with fewer than `-n` dots followed by `crossr` vanishes. -/
theorem ba0_FE (s : ℕ) (hs : s < (-ip RD i lam).toNat) :
    betaFE RD k sc i lam s ≫ (-NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i)) = 0 := by
  rw [Preadditive.comp_neg, betaFE, cupDotFELs, NF.dg_comp (by schain) (by schain),
    dg_cupDn_crossr_eq_zero RD k sc i lam _ (by omega), neg_zero]

/-- `β_s α_t = δ_{st}` (mirror case). -/
theorem ba_FE (s t : ℕ) (hs : s < (-ip RD i lam).toNat) (ht : t < (-ip RD i lam).toNat) :
    betaFE RD k sc i lam s ≫ alphaFE RD k sc i lam t = if s = t then 𝟙 _ else 0 := by
  rw [alphaFE, Preadditive.comp_sum]
  have hterm : ∀ g ∈ Finset.range (t + 1),
      betaFE RD k sc i lam s ≫ NF.dg (pres RD k sc) lam [dn i, up i] [] (dotCapFELs i (t - g)) ≫
          NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + g) =
        NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + (((t : ℤ) - s) - g)) ≫
          NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + g) := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    rw [← Category.assoc, betaFE, dotCapFELs, dg_dots_cap_up, NF.dg_comp (by schain) (by schain)]
    have e : -ip RD i lam - 1 + (((t : ℤ) - s) - g) =
        (((-ip RD i lam).toNat - 1 - s + (t - g) : ℕ) : ℤ) := by
      omega
    rw [e, NF.ccwU_of_nonneg, ccwLs, cupDotFELs, List.replicate_add]
    simp only [List.append_assoc]
  rw [Finset.sum_congr rfl hterm, sum_ccw_cw lam i _ t (by omega)]
  by_cases hst : s = t
  · subst hst; simp
  · rw [ite_eq_right (by omega), ite_eq_right hst]

end Components

/-! ## Sideways crossings for distinct colours -/

section Cross

/-- For `i ≠ j`, `crossl ≫ t_ji⁻¹ crossr = 1` on `E_i F_j 1_μ`. -/
theorem crossl_comp_smul_crossr (i j : I) (h : i ≠ j) (μ : X) :
    (pres RD k sc).diag (crossl RD i j μ) ≫
        ((((sc.t j i)⁻¹ : kˣ) : k) • (pres RD k sc).diag (crossr RD i j μ)) = 𝟙 _ := by
  rw [Linear.comp_smul, ← dg_crossl, ← dg_crossr, NF.dg_comp (by schain) (by schain),
    dg_downupEF RD k sc i j h μ, smul_smul, Units.inv_mul, one_smul, NF.dg_nil]

/-- For `i ≠ j`, `t_ji⁻¹ crossr ≫ crossl = 1` on `F_j E_i 1_μ`. -/
theorem smul_crossr_comp_crossl (i j : I) (h : i ≠ j) (μ : X) :
    ((((sc.t j i)⁻¹ : kˣ) : k) • (pres RD k sc).diag (crossr RD i j μ)) ≫
        (pres RD k sc).diag (crossl RD i j μ) = 𝟙 _ := by
  rw [Linear.smul_comp, ← dg_crossl, ← dg_crossr, NF.dg_comp (by schain) (by schain),
    dg_downupFE RD k sc j i h.symm μ, smul_smul, Units.inv_mul, one_smul, NF.dg_nil]

end Cross

end Categorification.KL3.Diagram.CLQ
