/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftCyc
import Categorification.Flag.GammaLiftSidewaysR

/-!
# `Γ_N` respects the mixed relations `downupEF`, `downupFE`

Cautis–Lauda arXiv:1111.1431v3, §2 (`sec:mixedrels`, p. 8), for `i ≠ j` and the `sl_n` scalars:
`crossl i j ≫ crossr i j = t_{ji} · 1` on `E_i F_j 1_μ` (`downupEF i j`) and
`crossr j i ≫ crossl j i = t_{ij} · 1` on `F_i E_j 1_μ` (`downupFE i j`).

On the path model (`Categorification.Flag.downupEF_W`, `downupFE_W`) both composites are `-1` if
`i = j + 1` resp. `j = i + 1`, and `1` otherwise, which is `t_{ji}` resp. `t_{ij}`
(`t_{ij} = i - j` for adjacent colours). The intermediate 1-morphism `F_j E_i 1_μ` resp.
`E_j F_i 1_μ` is nonzero as soon as the source is (`wok_mid_EF`, `wok_mid_FE`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### The intermediate objects -/

/-- If `E_i F_j 1_μ` is nonzero (`i ≠ j`), so is `F_j E_i 1_μ`. -/
theorem wok_mid_EF {i j : Fin m} (hij : i ≠ j) {μ s : Wt m} {v : List (psig RD).Colour}
    (ha : WOK N s ((ob RD μ [up i, dn j]).word ++ v)) :
    WOK N s ((ob RD μ [dn j, up i]).word ++ v) := by
  have hF : StepR (false, j) (compOf N μ) (compOf N (wt RD μ [dn j])) := ha.tail.step
  have hE : StepR (true, i) (compOf N (wt RD μ [dn j])) (compOf N s) := ha.step
  obtain ⟨hF1, -⟩ := hF
  obtain ⟨-, hE2⟩ := hE
  have hμ : Realized N μ := ha.2.2.2.2.realized
  have hpos : 0 < compOf N μ i.succ := by
    rw [← hF1, Signed.raise_val]
    have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
    split_ifs <;> omega
  have hr : Realized N (wt RD μ [up i]) :=
    (realized_of_stepR_up hμ i (⟨rfl, hpos⟩ : StepR (true, i) (compOf N μ) _)).1
  refine ⟨ha.1, ?_, hr, rfl, ha.2.2.2.2⟩
  rw [← ha.2.1]
  show sh RD (dn j) + (sh RD (up i) + μ) = sh RD (up i) + (sh RD (dn j) + μ)
  exact add_left_comm _ _ _

/-- If `F_i E_j 1_μ` is nonzero (`i ≠ j`), so is `E_j F_i 1_μ`. -/
theorem wok_mid_FE {i j : Fin m} (hij : i ≠ j) {μ s : Wt m} {v : List (psig RD).Colour}
    (ha : WOK N s ((ob RD μ [dn i, up j]).word ++ v)) :
    WOK N s ((ob RD μ [up j, dn i]).word ++ v) := by
  have hE : StepR (true, j) (compOf N μ) (compOf N (wt RD μ [up j])) := ha.tail.step
  have hF : StepR (false, i) (compOf N (wt RD μ [up j])) (compOf N s) := ha.step
  obtain ⟨hE1, -⟩ := hE
  obtain ⟨hF1, -⟩ := hF
  have hμ : Realized N μ := ha.2.2.2.2.realized
  set r := compOf N μ with hrdef
  have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective _ h)
  have hii : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ i).ne
  have hpos : 1 ≤ r i.castSucc := by
    have h1 := congrFun hE1 i.castSucc
    have h2 := congrFun hF1 i.castSucc
    rw [Signed.raise_val, if_neg hne] at h1
    rw [Signed.raise_val, if_pos rfl] at h2
    split_ifs at h1 with h3 <;> omega
  let d : Comp m := fun k => if k = i.castSucc then r k - 1 else if k = i.succ then r k + 1 else r k
  have hd : StepR (true, i) d r := by
    refine ⟨funext fun k => ?_, ?_⟩
    · simp only [Signed.raise_val, d]
      by_cases h1 : k = i.castSucc
      · subst h1; simp only [if_true]; omega
      · by_cases h2 : k = i.succ
        · subst h2; simp only [if_neg hii.symm, if_true]; omega
        · simp only [if_neg h1, if_neg h2]
    · simp only [d, if_neg hii.symm, if_true]; omega
  have hr : Realized N (wt RD μ [dn i]) :=
    (realized_of_stepR_up' hμ i hd (wt RD μ [dn i]) (sh_up_dn_cancel i μ)).1
  refine ⟨ha.1, ?_, hr, rfl, ha.2.2.2.2⟩
  rw [← ha.2.1]
  show sh RD (up j) + (sh RD (dn i) + μ) = sh RD (dn i) + (sh RD (up j) + μ)
  exact add_left_comm _ _ _

/-! ### The scalars -/

/-- `t_{ji}` as the sign of `downupEF_W`. -/
theorem slnT_eq_sign (i j : Fin m) :
    (((CL.Sln.slnScalars K m).t j i : Kˣ) : K) = if i.castSucc = j.succ then -1 else 1 := by
  rw [CL.Sln.slnScalars_t]
  by_cases hadj : (slCartan m).dot j i = -1
  · rw [CL.Sln.slnT_of_adj K hadj]
    rcases (slCartan_dot_eq_neg_one_iff j i).1 hadj with h' | h'
    · have e := Signed.castSucc_eq_succ_iff.1 h'
      have hn : ¬ i.castSucc = j.succ := by
        intro h
        have := Signed.castSucc_eq_succ_iff.1 h
        omega
      rw [if_neg hn, e]
      push_cast
      ring
    · have e := Signed.castSucc_eq_succ_iff.1 h'
      rw [if_pos h', e]
      push_cast
      ring
  · rw [CL.Sln.slnT_of_not_adj K hadj, Units.val_one, if_neg]
    intro h
    exact hadj ((slCartan_dot_eq_neg_one_iff j i).2 (Or.inr h))

/-! ### The relations -/

local notation "PCL" => CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)

theorem BHom.sub_smul_id_of_sign {A : Type u} [CommRing A] (M : BRing A K) (P : Prop)
    [Decidable P] :
    (if P then -BHom.id M else BHom.id M) - (if P then (-1 : K) else 1) • BHom.id M = 0 := by
  split_ifs
  · rw [neg_smul, one_smul, sub_neg_eq_add, neg_add_cancel]
  · rw [one_smul, sub_self]

/-- **`Γ_N` respects `downupEF i j`** (`i ≠ j`): `crossl i j ≫ crossr i j = t_{ji} · 1` on
`E_i F_j 1_μ`. -/
theorem evalB_presCL_downupEF (i j : Fin m) (h : i ≠ j) (μ s : Wt m)
    (_hs : s = ((PCL).dom (.inr (.downupEF i j h μ))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.downupEF i j h μ))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.downupEF i j h μ))).word ++ v)) :
    evalB K N (gammaDn K m) s v ha hb ((PCL).rel (.inr (.downupEF i j h μ))) = 0 := by
  have ha₀ : WOK N s ((ob RD μ [up i, dn j]).word ++ v) := ha
  have hb₀ : WOK N s ((ob RD μ [up i, dn j]).word ++ v) := hb
  have hm := wok_mid_EF h ha₀
  show evalB K N (gammaDn K m) s v ha₀ hb₀ (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) -
    (((CL.Sln.slnScalars K m).t j i : Kˣ) : K) • LinDiagram.of (𝟙 _)) = 0
  rw [map_sub, map_smul, LinDiagram.of_comp, evalB_comp (gammaDn K m) s v ha₀ hm hb₀,
    evalB_crossl_eq (gammaDn K m) i j μ s v ha₀ hm,
    evalB_crossr_eq (gammaDn K m) i j μ s v hm hb₀, evalB_id,
    downupEF_W i j ha₀.step ha₀.tail.step hm.step hm.tail.step _ h, slnT_eq_sign]
  exact BHom.sub_smul_id_of_sign _ _

/-- **`Γ_N` respects `downupFE i j`** (`i ≠ j`): `crossr j i ≫ crossl j i = t_{ij} · 1` on
`F_i E_j 1_μ`. -/
theorem evalB_presCL_downupFE (i j : Fin m) (h : i ≠ j) (μ s : Wt m)
    (_hs : s = ((PCL).dom (.inr (.downupFE i j h μ))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.downupFE i j h μ))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.downupFE i j h μ))).word ++ v)) :
    evalB K N (gammaDn K m) s v ha hb ((PCL).rel (.inr (.downupFE i j h μ))) = 0 := by
  have ha₀ : WOK N s ((ob RD μ [dn i, up j]).word ++ v) := ha
  have hb₀ : WOK N s ((ob RD μ [dn i, up j]).word ++ v) := hb
  have hm := wok_mid_FE h ha₀
  show evalB K N (gammaDn K m) s v ha₀ hb₀ (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
    (((CL.Sln.slnScalars K m).t i j : Kˣ) : K) • LinDiagram.of (𝟙 _)) = 0
  rw [map_sub, map_smul, LinDiagram.of_comp, evalB_comp (gammaDn K m) s v ha₀ hm hb₀,
    evalB_crossr_eq (gammaDn K m) j i μ s v ha₀ hm,
    evalB_crossl_eq (gammaDn K m) j i μ s v hm hb₀, evalB_id,
    downupFE_W j i hm.step hm.tail.step ha₀.step ha₀.tail.step _ (Ne.symm h), slnT_eq_sign]
  exact BHom.sub_smul_id_of_sign _ _

end Categorification.Flag

end
