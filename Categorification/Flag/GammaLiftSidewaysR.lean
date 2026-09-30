/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftSideways

/-!
# `Γ_N` of the sideways crossing `crossr`

KL III, arXiv:0807.3250v1, §3.1.1 (the sideways crossings, defined by `eq_crossr-gen`;
`Categorification.KL3.Diagram.crossr`) and §6.

`evalB_crossr_eq`: `Γ_N` of `crossr i j : F_j E_i 1_μ → E_i F_j 1_μ`, whiskered by any `v` on the
right, from the region making its source valid, is `crossrW`
(`Categorification.Flag.GammaSideways`). With `μ` written `j_X + x`, the chain on canonical layer
data (`chainBD_crossr_canon`, where the regions differing from the canonical ones are variables)
reduces to `crossrW` by substitution; `crossrW_trS_start`, `crossrW_trS_end` record its
naturality in the regions of its boundary.
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### `crossr` -/

/-- `crossrW` is natural in the region to the right of `F_j` at the bottom. -/
theorem crossrW_trS_start (i j : Fin m) (S a b R : Wt m) (e : a = b) (w : List (WCol m))
    {q' : Comp m} (hFa : StepR (false, j) (compOf N a) (compOf N S))
    (hFb : StepR (false, j) (compOf N b) (compOf N S))
    (hp : WOK N a (⟨up i, R⟩ :: w)) (hp' : WOK N b (⟨up i, R⟩ :: w))
    (hEi' : StepR (true, i) q' (compOf N S)) (hFj' : StepR (false, j) (compOf N R) q') :
    (crossrW K i j hFb hp'.step hEi' hFj' (gammaR K N R w hp'.tail)).comp
        (trS (false, j) S a b e (⟨up i, R⟩ :: w) hFa hFb hp hp') =
      crossrW K i j hFa hp.step hEi' hFj' (gammaR K N R w hp.tail) := by
  subst e
  exact BHom.ext fun _ => rfl

/-- `crossrW` is natural in the region to the right of `E_i` at the top. -/
theorem crossrW_trS_end (i j : Fin m) (S a b R : Wt m) (e : a = b) (w : List (WCol m))
    {q : Comp m} (hFj : StepR (false, j) q (compOf N S)) (hEi : StepR (true, i) (compOf N R) q)
    (hEa : StepR (true, i) (compOf N a) (compOf N S))
    (hEb : StepR (true, i) (compOf N b) (compOf N S))
    (hp : WOK N a (⟨dn j, R⟩ :: w)) (hp' : WOK N b (⟨dn j, R⟩ :: w)) :
    (trS (K := K) (true, i) S a b e (⟨dn j, R⟩ :: w) hEa hEb hp hp').comp
        (crossrW K i j hFj hEi hEa hp.step (gammaR K N R w hp.tail)) =
      crossrW K i j hFj hEi hEb hp'.step (gammaR K N R w hp'.tail) := by
  subst e
  exact BHom.ext fun _ => rfl

set_option maxHeartbeats 4000000 in
/-- The chain of `crossr` on canonical layer data, with the regions that differ from the
canonical ones as variables. -/
theorem chainBD_crossr_canon (dnScal : Fin m → Fin m → K) (i j : Fin m) (x s a b : Wt m)
    (v : List (psig RD).Colour) (es : sh RD (up i) + x = s)
    (ea : sh RD (up j) + (sh RD (up i) + x) = a) (eb : x = b)
    (h : ChainW ([⟨dn j, a⟩, ⟨up i, sh RD (up j) + x⟩] ++ v)
      [([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩, ⟨up i, sh RD (up j) + x⟩], .cup ⟨up j, x⟩, v),
        ([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩], .gen (.cross true i j x),
          ⟨dn j, sh RD (up j) + x⟩ :: v),
        ([], .cap ⟨up j, sh RD (up i) + x⟩, [⟨up i, x⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v)]
      ([⟨up i, b⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v))
    (ha : WOK N s ([⟨dn j, a⟩, ⟨up i, sh RD (up j) + x⟩] ++ v))
    (hb : WOK N s ([⟨up i, b⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v)) :
    chainBD K N dnScal s _ _ _ h ha hb =
      crossrW K i j ha.step ha.tail.step hb.step hb.tail.step
        (gammaR K N (sh RD (up j) + x) v ha.tail.tail) := by
  subst es ea eb
  have hL1 : WOK N (sh RD (up i) + x) ([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩,
      ⟨up i, sh RD (up j) + x⟩, ⟨up j, x⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v) :=
    ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.realized, rfl, hb.2.2⟩
  have hL2 : WOK N (sh RD (up i) + x) ([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩,
      ⟨up j, sh RD (up i) + x⟩, ⟨up i, x⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v) :=
    ⟨ha.1, ha.2.1, ha.2.2.1, rfl, ha.1, rfl, hb.2.2⟩
  rw [chainBD_three dnScal _ _ _ _ _ _ h ha hb ha hL1 hL1 hL2 hL2 hb]
  simp only [genScal, BHom.csmul_one, trW_self, BHom.id_comp']
  simp only [layerMap, genMap, cupMap, crossMap, capMap, trS_self'', BHom.whiskerLeft_id,
    BHom.id_comp', BHom.comp_id'']
  erw [BHom.whiskerLeft_id, BHom.comp_id'']
  rfl

set_option maxHeartbeats 4000000 in
/-- **`Γ_N` of the sideways crossing `crossr i j : F_j E_i 1_μ → E_i F_j 1_μ`** (KL III
`eq_crossr-gen`), whiskered by `v`, from any region `s` making the source valid: `crossrW`
(`Categorification.Flag.GammaSideways`). -/
theorem evalB_crossr_eq (dnScal : Fin m → Fin m → K) (i j : Fin m) (μ : Wt m) (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s ((ob RD μ [dn j, up i]).word ++ v))
    (hb : WOK N s ((ob RD μ [up i, dn j]).word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (crossr RD i j μ)) =
      crossrW K i j ha.step ha.tail.step hb.step hb.tail.step (gammaR K N μ v ha.tail.tail) := by
  obtain ⟨x, rfl⟩ : ∃ x, μ = sh RD (up j) + x := ⟨_, (sh_up_dn j μ).symm⟩
  rw [evalB_of]
  have el : (Diagram.layers (crossr RD i j (sh RD (up j) + x))).map (dataV v) =
      [([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩, ⟨up i, sh RD (up j) + x⟩], .cup ⟨up j, x⟩, v),
        ([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩], .gen (.cross true i j x),
          ⟨dn j, sh RD (up j) + x⟩ :: v),
        ([], .cap ⟨up j, sh RD (up i) + x⟩, [⟨up i, x⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v)] := by
    simp only [crossr, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, Shape.dom, List.nil_append, List.append_nil, List.cons_append,
      Letter.dual_mk, Bool.not_true]
    have e1 : sh RD (false, j) + (sh RD (up j) + x) = x := sh_dn_up j x
    rw [e1, add_left_comm (sh RD (up i)) (sh RD (up j)) x]
  have h₂ : ChainW ((ob RD (sh RD (up j) + x) [dn j, up i]).word ++ v)
      [([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩, ⟨up i, sh RD (up j) + x⟩], .cup ⟨up j, x⟩, v),
        ([⟨dn j, sh RD (up j) + (sh RD (up i) + x)⟩], .gen (.cross true i j x),
          ⟨dn j, sh RD (up j) + x⟩ :: v),
        ([], .cap ⟨up j, sh RD (up i) + x⟩, [⟨up i, x⟩, ⟨dn j, sh RD (up j) + x⟩] ++ v)]
      ((ob RD (sh RD (up j) + x) [up i, dn j]).word ++ v) :=
    el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal s rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  have es : sh RD (up i) + x = s := by
    refine Eq.trans ?_ ha.2.1
    show _ = sh RD (dn j) + (sh RD (up i) + (sh RD (up j) + x))
    rw [sh_up_eq, sh_up_eq, sh_dn_eq]
    abel
  exact chainBD_crossr_canon dnScal i j x s _ _ v es (add_left_comm _ _ _) (sh_dn_up j x).symm
    h₂ ha hb

end Categorification.Flag

end
