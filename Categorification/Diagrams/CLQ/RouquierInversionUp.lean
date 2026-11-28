/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.RouquierInversion
import Categorification.TwoRep.RouqDual

/-!
# Rouquier's invertibility conditions in `U_Q(g)` for the adjunction `E_i ⊣ F_i`

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1,
(1.6), (1.8), (1.9), for the downward strands `F_i` of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3,
Definition 1.1, `r = 1`; `CLQ.pres RD k sc`), with the cups and caps of the other adjunction
`E_i ⊣ F_i` (`biadjColour … .right`): its unit is the cup `1 → E_i F_i` (`cup (up i)`) and its
counit the cap `F_i E_i → 1` (`cap (up i)`). This is the adjunction by which the black action
of Webster, arXiv:1309.3796v3, §4.6, makes induction left adjoint to restriction
(`blackCompletedAdjunctionQ`), the black action being contravariant on 1-morphisms.

* `dg_sigmaUpLs`: the rightward crossing built from the downward crossing with these cups and
  caps (cup on the left, crossing, cap on the right) is Cautis–Lauda's sideways crossing
  `crossr_{ii}` (cyclicity, `t_{ii} = 1`).
* `sumInvTo_sigmaUp` (`⟨i, λ⟩ ≤ 0`): `(-crossr, capUp 0, …, capUp (-n - 1))`, where `capUp m` is
  the cap `F_i E_i → 1` with `m` dots on its downward strand, has an explicit inverse.
* `sumInvFrom_sigmaUp` (`⟨i, λ⟩ ≥ 0`): `(-crossr, cupUp 0, …, cupUp (n - 1))`, where `cupUp m`
  is the cup `1 → E_i F_i` with `m` dots on its downward strand, has an explicit inverse.

These come from the decompositions of Khovanov–Lauda, arXiv:0807.3250v1, Proposition 3.25
(`total_FE`, `ba_FE`, `total_EF`, ...), as in `RouquierInversion`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.TwoRep

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-- The layers of Brundan's rightward crossing (1.6) for the downward strands with the cups and
caps of `E_i ⊣ F_i`: the cup `1 → E_i F_i` on the left, the crossing of the two `F_i`, the cap
`F_i E_i → 1` on the right. -/
def sigmaUpLs (i : I) : List (LayerData I) :=
  [([], .cup (up i), [dn i, up i]), ([up i], .cross false i i, [up i]),
    ([up i, dn i], .cap (up i), [])]

variable (i : I) (lam : X)

/-- The cap `F_i E_i 1_λ → 1_λ` with `m` dots on its downward strand. -/
def capUp (m : ℕ) :
    (pres RD k sc).obj (ob RD lam [dn i, up i]) ⟶ (pres RD k sc).obj (ob RD lam []) :=
  NF.dg (pres RD k sc) lam [dn i, up i] [] (dotCapFELs i m)

/-- The cup `1_λ → E_i F_i 1_λ` with `m` dots on its downward strand. -/
def cupUp (m : ℕ) :
    (pres RD k sc).obj (ob RD lam []) ⟶ (pres RD k sc).obj (ob RD lam [up i, dn i]) :=
  NF.dg (pres RD k sc) lam [] [up i, dn i] (cupDotEFLs i m)

/-- **The rightward crossing for `E_i ⊣ F_i` is Cautis–Lauda's sideways crossing `crossr`**
(cyclicity of the crossing, `t_{ii} = 1`). -/
theorem dg_sigmaUpLs :
    NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (sigmaUpLs i) =
      NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i) := by
  rw [dg_crossrL_eq_smul_wls, show ((sc.t i i : kˣ) : k) = 1 by rw [sc.t_self]; rfl, one_smul]
  rfl

variable {RD k sc}

/-- A dotted cup `1 → F_i E_i` followed by a dotted cap `F_i E_i → 1` is a counter-clockwise
bubble. -/
theorem betaFE_comp_capUp (s m : ℕ) (hs : s < (-ip RD i lam).toNat) :
    betaFE RD k sc i lam s ≫ capUp RD k sc i lam m =
      NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + ((m : ℤ) - s)) := by
  rw [betaFE, capUp, dotCapFELs, dg_dots_cap_up, NF.dg_comp (by schain) (by schain)]
  have e : -ip RD i lam - 1 + ((m : ℤ) - s) = (((-ip RD i lam).toNat - 1 - s + m : ℕ) : ℤ) := by
    omega
  rw [e, NF.ccwU_of_nonneg, ccwLs, cupDotFELs, List.replicate_add]
  simp only [List.append_assoc]

/-- The infinite Grassmannian relation, indexed by the positions of a cap and a cup. -/
theorem sum_cw_ccw_shift (n s s' : ℕ) (hs' : s' < n) :
    ∑ t ∈ Finset.range n,
      NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ((t : ℤ) - s)) ≫
        NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + ((s' : ℤ) - t)) =
      if s = s' then 𝟙 _ else 0 := by
  have hsub : Finset.range (s' + 1) ⊆ Finset.range n := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub, ← Finset.sum_range_reflect]
  · have h := sum_cw_ccw (RD := RD) (k := k) (sc := sc) lam i ((s' : ℤ) - s) s' (by omega)
    refine (Finset.sum_congr rfl fun g hg => ?_).trans (h.trans ?_)
    · have hg' := Finset.mem_range.1 hg
      congr 2 <;> push_cast [Nat.cast_sub (show g ≤ s' by omega)] <;> ring
    · split_ifs <;> first | rfl | (exfalso; omega)
  · intro t _ ht
    rw [Finset.mem_range] at ht
    rw [ccwU_eq_zero RD k sc lam i _ (by omega), Limits.comp_zero]

/-! ## Rouquier's map for `⟨i, λ⟩ ≤ 0` -/

/-- Cautis–Lauda's explicit inverse of `(-crossr, α)` for `⟨i, λ⟩ ≤ 0`. -/
def sumInvToFECL (hn : ip RD i lam ≤ 0) :
    SumInvTo (-NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i))
      (alphaFE RD k sc i lam) (-ip RD i lam).toNat :=
  SumInvTo.ofEqs (NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i))
    (betaFE RD k sc i lam) (total_FE i lam) (b0a0_FE i lam hn) (fun s hs => ba0_FE i lam s hs)
    (fun s t hs ht => ba_FE i lam s t hs ht)

/-- **Brundan (1.8) in `U_Q(g)` for `E_i ⊣ F_i`**: for `n = ⟨i, λ⟩ ≤ 0`, Rouquier's map
`(σ, capUp 0, …, capUp (-n - 1)) : F_i E_i 1_λ → E_i F_i 1_λ ⊕ 1_λ^{⊕ -n}`, with `σ = -crossr`
(`dg_sigmaUpLs`), has an explicit inverse. -/
def sumInvTo_sigmaUp (hn : ip RD i lam ≤ 0) :
    SumInvTo (-NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (sigmaUpLs i))
      (capUp RD k sc i lam) (-ip RD i lam).toNat := by
  rw [dg_sigmaUpLs]
  refine (sumInvToFECL i lam hn).changeSummands (capUp RD k sc i lam)
    (fun s t => NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ((t : ℤ) - s))) ?_ ?_
  · intro t ht
    have hsub : Finset.range (t + 1) ⊆ Finset.range (-ip RD i lam).toNat :=
      Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub, ← Finset.sum_range_reflect, alphaFE]
    · refine Finset.sum_congr rfl fun g hg => ?_
      have hg' := Finset.mem_range.1 hg
      rw [capUp]
      congr 2
      push_cast [Nat.cast_sub (show g ≤ t by omega)]
      ring
    · intro s _ hs
      rw [Finset.mem_range] at hs
      rw [cwU_eq_zero RD k sc lam i _ (by omega), Limits.comp_zero]
  · intro s s' hs hs'
    change (∑ t ∈ Finset.range (-ip RD i lam).toNat, _ ≫ betaFE RD k sc i lam t) ≫ _ = _
    simp only [Preadditive.sum_comp, Category.assoc]
    rw [← sum_cw_ccw_shift (RD := RD) (k := k) (sc := sc) i lam _ s s' hs']
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [betaFE_comp_capUp i lam t s' (Finset.mem_range.1 ht)]

/-! ## Rouquier's map for `⟨i, λ⟩ ≥ 0` -/

/-- Cautis–Lauda's explicit inverse of `(crossr, β)` for `⟨i, λ⟩ ≥ 0`. -/
def sumInvFromEFCL (hn : 0 ≤ ip RD i lam) :
    SumInvFrom (NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i))
      (betaEF RD k sc i lam) (ip RD i lam).toNat :=
  SumInvFrom.ofEqs (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i))
    (alphaEF RD k sc i lam) (total_EF i lam) (b0a0_EF i lam hn)
    (fun s hs => ba0_EF i lam s hs) (fun s t hs ht => ba_EF i lam s t hs ht)

/-- **Brundan (1.9) in `U_Q(g)` for `E_i ⊣ F_i`**: for `n = ⟨i, λ⟩ ≥ 0`, Rouquier's map
`(σ, cupUp 0, …, cupUp (n - 1)) : F_i E_i 1_λ ⊕ 1_λ^{⊕ n} → E_i F_i 1_λ`, with `σ = -crossr`
(`dg_sigmaUpLs`), has an explicit inverse. -/
def sumInvFrom_sigmaUp (hn : 0 ≤ ip RD i lam) :
    SumInvFrom (-NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (sigmaUpLs i))
      (cupUp RD k sc i lam) (ip RD i lam).toNat := by
  rw [dg_sigmaUpLs]
  refine (sumInvFromEFCL i lam hn).neg.reindex (cupUp RD k sc i lam) fun m hm => ?_
  rw [cupUp, betaEF, show (ip RD i lam).toNat - 1 - ((ip RD i lam).toNat - 1 - m) = m by
    omega]

end Categorification.KL3.Diagram.CLQ
