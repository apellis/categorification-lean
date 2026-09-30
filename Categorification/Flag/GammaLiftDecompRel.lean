/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftSidewaysR
import Categorification.Flag.GammaLiftBubbleRel
import Categorification.Diagrams.CL.Specialize

/-!
# `Γ_N` respects the decompositions of `1_{E F 1_λ}` and `1_{F E 1_λ}`

KL III, arXiv:0807.3250v1, Definition 3.1, label `eq_ident_decomp`
(`Categorification.KL3.Diagram.Rel.decompEF`, `decompFE`), in Cautis–Lauda's normalization
(arXiv:1111.1431v3, `eq_ident_decomp-nleqz` and the displays for `n > 0`, `n = 0`):
`1 + r_i^{-2} · (double sideways crossing) - ∑ … = 0`, with `r_i = 1` for `CL.Sln.slnScalars`.

Each theorem is the hypothesis `hP` of `Categorification.Flag.gamma_respects` for the relation
index `.inr (.decompEF i λ)`, resp. `.inr (.decompFE i λ)`, of
`CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)`.

`Γ_N` of the sideways crossings is `crosslW`, `crossrW` (`evalB_crossl_eq`, `evalB_crossr_eq`),
`Γ_N` of the terms of the double sum is `dcW`, `dcWFE` (cup and cap with dots,
`evalB_cupDotEF`, `evalB_dotCapEF`, …, and the real or fake bubble, `evalB_ccwL`, `evalB_cwL`),
and the path-model theorems `decompEF_W`, `decompFE_W` (`Categorification.Diagrams.KL3.
GammaFlagDecomp`) give the relation. When the 1-morphism through which the double crossing
factors is zero in the path model, the double crossing is `0` and `decompEF_W_top`,
`decompFE_W_top` apply.
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

local notation "PCL" => CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)

theorem BHom.finset_sum_apply' {A : Type u} [CommRing A] {M M' : BRing A K} {ι : Type*}
    (S : Finset ι) (φ : ι → BHom M M') (z : M.T) : (∑ a ∈ S, φ a) z = ∑ a ∈ S, φ a z := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BHom.add_apply, ih]

/-- `Γ_N` of a term of the sum in the decomposition of `1_{E_i F_i 1_λ}`. -/
theorem evalB_decompEF_term (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N lam ((ob RD lam [up i, dn i]).word ++ v))
    (a c : ℕ) (mm : ℤ) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (dotCapEF RD lam i c) ≫ ccwL RD K lam i mm ≫
        LinDiagram.of (cupDotEF RD lam i a)) =
      dcW K i ha.tail.step (gammaR K N lam v ha.tail.tail) a c
        (ccwLH (compOf N lam) i mm) := by
  have h0 : WOK N lam ((ob RD lam []).word ++ v) := ha.tail.tail
  rw [evalB_comp dnScal lam v ha h0 hb, evalB_comp dnScal lam v h0 h0 hb, evalB_dotCapEF,
    evalB_ccwL, evalB_cupDotEF]
  rfl

/-- `Γ_N` of a term of the sum in the decomposition of `1_{F_i E_i 1_λ}`. -/
theorem evalB_decompFE_term (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N lam ((ob RD lam [dn i, up i]).word ++ v))
    (a c : ℕ) (mm : ℤ) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (dotCapFE RD lam i c) ≫ cwL RD K lam i mm ≫
        LinDiagram.of (cupDotFE RD lam i a)) =
      dcWFE K i ha.tail.step (gammaR K N lam v ha.tail.tail) a c
        (cwLH (compOf N lam) i mm) := by
  have h0 : WOK N lam ((ob RD lam []).word ++ v) := ha.tail.tail
  rw [evalB_comp dnScal lam v ha h0 hb, evalB_comp dnScal lam v h0 h0 hb, evalB_dotCapFE,
    evalB_cwL, evalB_cupDotFE]
  rfl

set_option maxHeartbeats 4000000 in
/-- **`Γ_N` respects the decomposition of `1_{E_i F_i 1_λ}`** of `U_Q(sl_n)` (KL III
Definition 3.1 `eq_ident_decomp`; CL `eq_ident_decomp-*` with `r_i = 1`). -/
theorem evalB_presCL_decompEF (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.decompEF i lam))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.decompEF i lam))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.decompEF i lam))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.decompEF i lam))) = 0 := by
  have hs' : s = lam := hs.trans (sh_up_dn i lam)
  revert ha hb
  rw [hs']
  intro ha₀ hb₀
  have ha : WOK N lam ((ob RD lam [up i, dn i]).word ++ v) := ha₀
  have hb : WOK N lam ((ob RD lam [up i, dn i]).word ++ v) := hb₀
  show evalB K N dnScal (a := ob RD lam [up i, dn i]) (b := ob RD lam [up i, dn i]) lam v ha hb
    (LinDiagram.of (𝟙 (ob RD lam [up i, dn i])) +
    ((((CL.Sln.slnScalars K m).r i)⁻¹ : Kˣ) : K) ^ 2 •
      LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam) - decompEFSum RD K i lam) = 0
  have hn : ip RD i lam = nH (compOf N lam) i := ip_eq_nH ha.tail.tail.realized i
  rw [CL.Sln.slnScalars_r, inv_one, Units.val_one, one_pow, one_smul, LinDiagram.of_comp,
    map_sub, map_add, evalB_of_id_bub, sub_eq_zero]
  have hsum : evalB K N dnScal lam v ha hb (decompEFSum RD K i lam) =
      ∑ f ∈ Finset.range (nH (compOf N lam) i).toNat, ∑ g ∈ Finset.range (f + 1),
        dcW K i ha.tail.step (gammaR K N lam v ha.tail.tail) ((nH (compOf N lam) i).toNat - 1 - f)
          (f - g) (ccwLH (compOf N lam) i (-nH (compOf N lam) i - 1 + g)) := by
    unfold decompEFSum
    rw [map_sum, hn]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => evalB_decompEF_term dnScal i lam v ha hb _ _ _
  rw [hsum]
  by_cases hr : Realized N (sh RD (up i) + lam)
  · have hm : WOK N lam ((ob RD lam [dn i, up i]).word ++ v) :=
      ⟨ha.1, sh_dn_up i lam, hr, rfl, ha.tail.tail⟩
    rw [evalB_comp dnScal lam v ha hm hb, evalB_crossl_eq, evalB_crossr_eq]
    refine BHom.ext fun z => ?_
    rw [BHom.finset_sum_apply']
    simp only [BHom.finset_sum_apply']
    have key := decompEF_W (K := K) i
      (ha.tail.step : StepR (false, i) (compOf N lam) (compOf N (sh RD (dn i) + lam)))
      (hm.tail.step : StepR (true, i) (compOf N lam) (compOf N (sh RD (up i) + lam)))
      (gammaR K N lam v ha.tail.tail) z
    rw [BHom.add_apply, BHom.id_apply, BHom.comp_apply, add_comm z]
    exact eq_neg_add_iff_add_eq.mp key
  · have h0 : compOf N lam i.succ = 0 := compOf_succ_eq_zero ha.tail.tail.realized i hr
    have hm : ¬ WOK N lam ((ob RD lam [dn i, up i]).word ++ v) := fun hm => hr hm.2.2.1
    rw [evalB_comp_zero dnScal lam v ha hm hb, add_zero]
    refine BHom.ext fun z => ?_
    rw [BHom.finset_sum_apply']
    simp only [BHom.finset_sum_apply']
    exact decompEF_W_top (K := K) i
      (ha.tail.step : StepR (false, i) (compOf N lam) (compOf N (sh RD (dn i) + lam)))
      (gammaR K N lam v ha.tail.tail) h0 z

set_option maxHeartbeats 4000000 in
/-- **`Γ_N` respects the decomposition of `1_{F_i E_i 1_λ}`** of `U_Q(sl_n)` (KL III
Definition 3.1 `eq_ident_decomp`; CL `eq_ident_decomp-*` with `r_i = 1`). -/
theorem evalB_presCL_decompFE (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.decompFE i lam))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.decompFE i lam))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.decompFE i lam))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.decompFE i lam))) = 0 := by
  have hs' : s = lam := hs.trans (sh_dn_up i lam)
  revert ha hb
  rw [hs']
  intro ha₀ hb₀
  have ha : WOK N lam ((ob RD lam [dn i, up i]).word ++ v) := ha₀
  have hb : WOK N lam ((ob RD lam [dn i, up i]).word ++ v) := hb₀
  show evalB K N dnScal (a := ob RD lam [dn i, up i]) (b := ob RD lam [dn i, up i]) lam v ha hb
    (LinDiagram.of (𝟙 (ob RD lam [dn i, up i])) +
    ((((CL.Sln.slnScalars K m).r i)⁻¹ : Kˣ) : K) ^ 2 •
      LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam) - decompFESum RD K i lam) = 0
  have hn : ip RD i lam = nH (compOf N lam) i := ip_eq_nH ha.tail.tail.realized i
  rw [CL.Sln.slnScalars_r, inv_one, Units.val_one, one_pow, one_smul, LinDiagram.of_comp,
    map_sub, map_add, evalB_of_id_bub, sub_eq_zero]
  have hsum : evalB K N dnScal lam v ha hb (decompFESum RD K i lam) =
      ∑ f ∈ Finset.range (-nH (compOf N lam) i).toNat, ∑ g ∈ Finset.range (f + 1),
        dcWFE K i ha.tail.step (gammaR K N lam v ha.tail.tail)
          ((-nH (compOf N lam) i).toNat - 1 - f) (f - g)
          (cwLH (compOf N lam) i (nH (compOf N lam) i - 1 + g)) := by
    unfold decompFESum
    rw [map_sum, hn]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => evalB_decompFE_term dnScal i lam v ha hb _ _ _
  rw [hsum]
  by_cases hr : Realized N (sh RD (dn i) + lam)
  · have hm : WOK N lam ((ob RD lam [up i, dn i]).word ++ v) :=
      ⟨ha.1, sh_up_dn i lam, hr, rfl, ha.tail.tail⟩
    rw [evalB_comp dnScal lam v ha hm hb, evalB_crossr_eq, evalB_crossl_eq]
    refine BHom.ext fun z => ?_
    rw [BHom.finset_sum_apply']
    simp only [BHom.finset_sum_apply']
    have key := decompFE_W (K := K) i
      (hm.tail.step : StepR (false, i) (compOf N lam) (compOf N (sh RD (dn i) + lam)))
      (ha.tail.step : StepR (true, i) (compOf N lam) (compOf N (sh RD (up i) + lam)))
      (gammaR K N lam v ha.tail.tail) z
    rw [BHom.add_apply, BHom.id_apply, BHom.comp_apply, add_comm z]
    exact eq_neg_add_iff_add_eq.mp key
  · have h0 : compOf N lam i.castSucc = 0 := compOf_castSucc_eq_zero ha.tail.tail.realized i hr
    have hm : ¬ WOK N lam ((ob RD lam [up i, dn i]).word ++ v) := fun hm => hr hm.2.2.1
    rw [evalB_comp_zero dnScal lam v ha hm hb, add_zero]
    refine BHom.ext fun z => ?_
    rw [BHom.finset_sum_apply']
    simp only [BHom.finset_sum_apply']
    exact decompFE_W_top (K := K) i
      (ha.tail.step : StepR (true, i) (compOf N lam) (compOf N (sh RD (up i) + lam)))
      (gammaR K N lam v ha.tail.tail) h0 z

end Categorification.Flag

end
