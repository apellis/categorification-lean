/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Decompositions
import Categorification.Diagrams.CLQ.SpanningSetLocal
import Categorification.TwoRep.SumInvChange

/-!
# Rouquier's invertibility conditions in Cautis–Lauda's `U_Q(g)`

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1,
(1.6), (1.8), (1.9), for the downward strands `F_i` of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3,
Definition 1.1, `r = 1`; `CLQ.pres RD k sc`), with `F_i` in the role of Brundan's `E` and its right
adjoint `E_i` in the role of Brundan's `F`. The unit of `F_i ⊣ E_i` is the cup `1 → F_i E_i` and
its counit is the cap `E_i F_i → 1`; Brundan's upward crossing is minus the downward crossing,
`τ = -(cross false i i)`.

* `dg_sigmaLs`: Brundan's rightward crossing `σ` built from the downward crossing (cup on the
  right, crossing, cap on the left) is Cautis–Lauda's sideways crossing `crossl_{ii}`; this is the
  cyclicity of the crossing, `t_{ii} = 1`. With `τ = -(cross false i i)`, Brundan's `σ` is
  `-crossl_{ii}`.
* `sumInvTo_sigma` (Brundan (1.8), `⟨i, λ⟩ ≥ 0`): `(-crossl, capDn 0, …, capDn (n - 1))`
  has an explicit inverse, where `capDn m` is the cap `E_i F_i → 1` with `m` dots on its
  downward strand.
* `sumInvFrom_sigma` (Brundan (1.9), `⟨i, λ⟩ ≤ 0`): `(-crossl, cupDn 0, …, cupDn (-n - 1))`
  has an explicit inverse, where `cupDn m` is the cup `1 → F_i E_i` with `m` dots on its
  downward strand.

These come from Cautis–Lauda's decompositions (`total_EF`, `ba_EF`, ...; Khovanov–Lauda,
arXiv:0807.3250v1, Proposition 3.25), whose cap components carry fake bubbles: they are
unitriangular combinations of the plain dotted caps, inverted by the infinite Grassmannian
relation (`sum_ccw_cw`).
-/

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.TwoRep

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-- The layers of Brundan's rightward crossing (1.6) for the downward strands with the downward
crossing: the cup `1 → F_i E_i` on the right, the crossing of the two `F_i`, the cap
`E_i F_i → 1` on the left. -/
def sigmaLs (i : I) : List (LayerData I) :=
  [([up i, dn i], .cup (dn i), []), ([up i], .cross false i i, [up i]),
    ([], .cap (dn i), [dn i, up i])]

/-- The layers of the cap `E_i F_i → 1` with `m` dots on its downward strand. -/
def capDnLs (i : I) (m : ℕ) : List (LayerData I) :=
  List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]

/-- The layers of the cup `1 → F_i E_i` with `m` dots on its downward strand. -/
def cupDnLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), [])] ++ List.replicate m ([], .dot (dn i), [up i])

variable (i : I) (lam : X)

/-- The cap `E_i F_i 1_λ → 1_λ` with `m` dots on its downward strand. -/
def capDn (m : ℕ) :
    (pres RD k sc).obj (ob RD lam [up i, dn i]) ⟶ (pres RD k sc).obj (ob RD lam []) :=
  NF.dg (pres RD k sc) lam [up i, dn i] [] (capDnLs i m)

/-- The cup `1_λ → F_i E_i 1_λ` with `m` dots on its downward strand. -/
def cupDn (m : ℕ) :
    (pres RD k sc).obj (ob RD lam []) ⟶ (pres RD k sc).obj (ob RD lam [dn i, up i]) :=
  NF.dg (pres RD k sc) lam [] [dn i, up i] (cupDnLs i m)

/-- **Brundan's rightward crossing is Cautis–Lauda's sideways crossing** (cyclicity of the
crossing, `t_{ii} = 1`). -/
theorem dg_sigmaLs :
    NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (sigmaLs i) =
      NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i) := by
  rw [dg_crosslL_eq_smul_wls, show ((sc.t i i : kˣ) : k) = 1 by rw [sc.t_self]; rfl, one_smul]
  rfl

theorem capDn_eq (m : ℕ) :
    capDn RD k sc i lam m = NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i m) :=
  dg_dots_cap_dn RD k sc lam i m

theorem cupDn_eq (m : ℕ) :
    cupDn RD k sc i lam m = NF.dg (pres RD k sc) lam [] [dn i, up i] (cupDotFELs i m) :=
  (dg_dots_cupDn RD k sc i lam m).symm

variable {RD k sc}

/-- A dotted cup followed by a dotted cap is a clockwise bubble. -/
theorem betaEF_comp_dotCap (s m : ℕ) (hs : s < (ip RD i lam).toNat) :
    betaEF RD k sc i lam s ≫ NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i m) =
      NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ((m : ℤ) - s)) := by
  rw [betaEF, dotCapEFLs, ← dg_dots_cap_dn, NF.dg_comp (by schain) (by schain)]
  have e : ip RD i lam - 1 + ((m : ℤ) - s) = (((ip RD i lam).toNat - 1 - s + m : ℕ) : ℤ) := by
    omega
  rw [e, NF.cwU_of_nonneg, cwLs, cupDotEFLs, List.replicate_add]
  simp only [List.append_assoc]

/-- The infinite Grassmannian relation, indexed by the positions of a cup and a cap. -/
theorem sum_ccw_cw_shift (n s s' : ℕ) (hs' : s' < n) :
    ∑ t ∈ Finset.range n,
      NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + ((t : ℤ) - s)) ≫
        NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ((s' : ℤ) - t)) =
      if s = s' then 𝟙 _ else 0 := by
  have hsub : Finset.range (s' + 1) ⊆ Finset.range n := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub, ← Finset.sum_range_reflect]
  · have h := sum_ccw_cw (RD := RD) (k := k) (sc := sc) lam i ((s' : ℤ) - s) s' (by omega)
    refine (Finset.sum_congr rfl fun g hg => ?_).trans (h.trans ?_)
    · have hg' := Finset.mem_range.1 hg
      congr 2 <;> push_cast [Nat.cast_sub (show g ≤ s' by omega)] <;> ring
    · split_ifs <;> first | rfl | (exfalso; omega)
  · intro t _ ht
    rw [Finset.mem_range] at ht
    rw [cwU_eq_zero RD k sc lam i _ (by omega), Limits.comp_zero]

/-! ## Rouquier's map for `⟨i, λ⟩ ≥ 0` -/

/-- Cautis–Lauda's explicit inverse of `(-crossl, α)` for `⟨i, λ⟩ ≥ 0`. -/
def sumInvToCL (hn : 0 ≤ ip RD i lam) :
    SumInvTo (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i))
      (alphaEF RD k sc i lam) (ip RD i lam).toNat :=
  SumInvTo.ofEqs (NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i))
    (betaEF RD k sc i lam) (total_EF i lam) (b0a0_EF i lam hn) (fun s hs => ba0_EF i lam s hs)
    (fun s t hs ht => ba_EF i lam s t hs ht)

/-- **Brundan (1.8) in `U_Q(g)`**: for `n = ⟨i, λ⟩ ≥ 0`, Rouquier's map
`(σ, capDn 0, …, capDn (n - 1)) : E_i F_i 1_λ → F_i E_i 1_λ ⊕ 1_λ^{⊕ n}`, with `σ = -crossl`
(`dg_sigmaLs`), has an explicit inverse. -/
def sumInvTo_sigma (hn : 0 ≤ ip RD i lam) :
    SumInvTo (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (sigmaLs i))
      (capDn RD k sc i lam) (ip RD i lam).toNat := by
  rw [dg_sigmaLs]
  refine (sumInvToCL i lam hn).changeSummands (capDn RD k sc i lam)
    (fun s t => NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + ((t : ℤ) - s))) ?_ ?_
  · intro t ht
    have hsub : Finset.range (t + 1) ⊆ Finset.range (ip RD i lam).toNat :=
      Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub, ← Finset.sum_range_reflect, alphaEF]
    · refine Finset.sum_congr rfl fun g hg => ?_
      have hg' := Finset.mem_range.1 hg
      rw [capDn_eq]
      congr 2
      push_cast [Nat.cast_sub (show g ≤ t by omega)]
      ring
    · intro s _ hs
      rw [Finset.mem_range] at hs
      rw [ccwU_eq_zero RD k sc lam i _ (by omega), Limits.comp_zero]
  · intro s s' hs hs'
    change (∑ t ∈ Finset.range (ip RD i lam).toNat, _ ≫ betaEF RD k sc i lam t) ≫ _ = _
    simp only [Preadditive.sum_comp, Category.assoc]
    rw [capDn_eq, ← sum_ccw_cw_shift (RD := RD) (k := k) (sc := sc) i lam _ s s' hs']
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [betaEF_comp_dotCap i lam t s' (Finset.mem_range.1 ht)]

/-! ## Rouquier's map for `⟨i, λ⟩ ≤ 0` -/

/-- Cautis–Lauda's explicit inverse of `(-crossl, β)` for `⟨i, λ⟩ ≤ 0`. -/
def sumInvFromCL (hn : ip RD i lam ≤ 0) :
    SumInvFrom (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i))
      (betaFE RD k sc i lam) (-ip RD i lam).toNat :=
  SumInvFrom.ofEqs (NF.dg (pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i))
    (alphaFE RD k sc i lam)
    (by rw [← total_FE i lam, Preadditive.comp_neg, Preadditive.neg_comp])
    (by rw [Preadditive.neg_comp, ← Preadditive.comp_neg]; exact b0a0_FE i lam hn)
    (fun s hs => by
      have h := ba0_FE (RD := RD) (k := k) (sc := sc) i lam s hs
      rw [Preadditive.comp_neg, neg_eq_zero] at h
      exact h)
    (fun s t hs ht => ba_FE i lam s t hs ht)

/-- **Brundan (1.9) in `U_Q(g)`**: for `n = ⟨i, λ⟩ ≤ 0`, Rouquier's map
`(σ, cupDn 0, …, cupDn (-n - 1)) : E_i F_i 1_λ ⊕ 1_λ^{⊕ -n} → F_i E_i 1_λ`, with `σ = -crossl`
(`dg_sigmaLs`), has an explicit inverse. -/
def sumInvFrom_sigma (hn : ip RD i lam ≤ 0) :
    SumInvFrom (-NF.dg (pres RD k sc) lam [up i, dn i] [dn i, up i] (sigmaLs i))
      (cupDn RD k sc i lam) (-ip RD i lam).toNat := by
  rw [dg_sigmaLs]
  refine (sumInvFromCL i lam hn).reindex (cupDn RD k sc i lam) fun m hm => ?_
  rw [cupDn_eq, betaFE, show (-ip RD i lam).toNat - 1 - ((-ip RD i lam).toNat - 1 - m) = m by
    omega]

end Categorification.KL3.Diagram.CLQ
