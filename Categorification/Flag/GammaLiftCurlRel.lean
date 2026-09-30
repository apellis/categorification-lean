/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftCurl

/-!
# `Γ_N` respects the curl relations of Cautis–Lauda's `U_Q(sl_n)`

KL III, arXiv:0807.3250v1, Definition 3.1 iv) (first display: the curl relations,
`Categorification.KL3.Diagram.Rel.curlR`, `curlL`), in Cautis–Lauda's normalization
(arXiv:1111.1431v3, `eq_reduction-ngeqz`, `eq_reduction-nleqz`): `curl = r_i · (KL III's
right-hand side)`, with `r_i = 1` for the scalars `CL.Sln.slnScalars`.

Each theorem is the hypothesis `hP` of `Categorification.Flag.gamma_respects` for the relation
index `.inr (.curlR i λ)`, resp. `.inr (.curlL i μ)`, of
`CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)`.

When the region inside the curl is realized, the chain map of the curl is `curlRW`, resp.
`curlLW` (`evalB_curlR_eq`, `evalB_curlL_eq`), and the path-model theorems `curlRW_eq_curlRHS`,
`curlLW_eq_curlLHS` identify it with `Γ_N` of the right-hand side (`evalB_curlRHS`,
`evalB_curlLHS`, via `Γ_N` of real and fake bubbles). Otherwise the curl is `0` and so is the
right-hand side, since the dot of `E_i` is a root of the total Chern class of the neighbouring
block (`curlR_rhs_degenerate`, `curlL_rhs_degenerate`).
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

/-- **`Γ_N` respects the right curl relation** of `U_Q(sl_n)` (KL III Definition 3.1 iv);
CL `eq_reduction-*` with `r_i = 1`). -/
theorem evalB_presCL_curlR (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.curlR i lam))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.curlR i lam))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.curlR i lam))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.curlR i lam))) = 0 := by
  subst hs
  show evalB K N dnScal _ v ha hb (LinDiagram.of (curlR RD i lam) -
    (((CL.Sln.slnScalars K m).r i : Kˣ) : K) • curlRHS RD K i lam) = 0
  rw [CL.Sln.slnScalars_r, Units.val_one, one_smul, map_sub, sub_eq_zero]
  erw [evalB_curlRHS dnScal i lam _ v ha hb]
  obtain ⟨x, rfl⟩ : ∃ x, lam = sh RD (up i) + x := ⟨_, (sh_up_dn i lam).symm⟩
  by_cases hx : Realized N x
  · have hm : WOK N (sh RD (up i) + (sh RD (up i) + x))
        ([⟨up i, sh RD (up i) + x⟩, ⟨up i, x⟩, ⟨dn i, sh RD (up i) + x⟩] ++ v) :=
      ⟨ha.1, ha.2.1, ha.2.2.realized, rfl, hx, sh_dn_up i x, ha.2.2⟩
    erw [evalB_curlR_eq dnScal i x v ha hb hm, curlRW_eq_curlRHS]
    rfl
  · have h0 : compOf N (sh RD (up i) + x) i.castSucc = 0 :=
      compOf_castSucc_eq_zero ha.tail.realized i fun h => hx (h.congr (sh_dn_up i x))
    erw [evalB_curlR_zero dnScal i x v ha hb hx, curlR_rhs_degenerate i ha.step h0, neg_zero,
      BHom.mulB_zero']

/-- **`Γ_N` respects the left curl relation** of `U_Q(sl_n)` (KL III Definition 3.1 iv);
CL `eq_reduction-*` with `r_i = 1`). -/
theorem evalB_presCL_curlL (dnScal : Fin m → Fin m → K) (i : Fin m) (μ : Wt m) (s : Wt m)
    (hs : s = ((PCL).dom (.inr (.curlL i μ))).start) (v : List (psig RD).Colour)
    (ha : WOK N s (((PCL).dom (.inr (.curlL i μ))).word ++ v))
    (hb : WOK N s (((PCL).cod (.inr (.curlL i μ))).word ++ v)) :
    evalB K N dnScal s v ha hb ((PCL).rel (.inr (.curlL i μ))) = 0 := by
  subst hs
  show evalB K N dnScal _ v ha hb (LinDiagram.of (curlL RD i μ) -
    (((CL.Sln.slnScalars K m).r i : Kˣ) : K) • curlLHS RD K i μ) = 0
  rw [CL.Sln.slnScalars_r, Units.val_one, one_smul, map_sub, sub_eq_zero]
  erw [evalB_curlLHS dnScal i μ _ rfl v ha hb]
  by_cases hc : Realized N (sh RD (up i) + (sh RD (up i) + μ))
  · have hm : WOK N (sh RD (up i) + μ)
        ([⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩, ⟨up i, sh RD (up i) + μ⟩, ⟨up i, μ⟩] ++ v) :=
      ⟨ha.1, sh_dn_up i _, hc, rfl, ha⟩
    erw [evalB_curlL_eq dnScal i μ v ha hb hm, curlLW_eq_curlLHS]
    rfl
  · have h0 : compOf N (sh RD (up i) + μ) i.succ = 0 :=
      compOf_succ_eq_zero ha.realized i hc
    erw [evalB_curlL_zero dnScal i μ v ha hb hc, curlL_rhs_degenerate i ha.step h0,
      BHom.mulB_zero']

end Categorification.Flag

end
