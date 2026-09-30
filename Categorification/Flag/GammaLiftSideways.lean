/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftBubble

/-!
# `Γ_N` of the sideways crossing `crossl`

KL III, arXiv:0807.3250v1, §3.1.1 (the sideways crossings, defined by `eq_crossl-gen`;
`Categorification.KL3.Diagram.crossl`) and §6.

`evalB_crossl_eq`: `Γ_N` of `crossl i j : E_i F_j 1_μ → F_j E_i 1_μ`, whiskered by any `v` on the
right, from the (unique) region making its source valid, is `crosslW`
(`Categorification.Flag.GammaSideways`). The relabellings of regions in the chain of layers are
absorbed by the cup (`trS_trans'`), the cap (`trS_capMap_false`) and the crossing
(`trS_crossU_out`).
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Relabelling regions through crossings and caps -/

/-- An upward crossing absorbs a relabelling of its middle output region. -/
theorem trS_crossU_out (c d : Fin m) (s ν a b : Wt m) (e : a = b) (right : List (WCol m))
    {r₁ : Comp m} (h₁ : StepR (true, c) r₁ (compOf N s)) (h₂ : StepR (true, d) (compOf N ν) r₁)
    (h₁' : StepR (true, d) (compOf N a) (compOf N s))
    (h₁'' : StepR (true, d) (compOf N b) (compOf N s))
    (hp : WOK N a (⟨up c, ν⟩ :: right)) (hp' : WOK N b (⟨up c, ν⟩ :: right)) :
    (trS (K := K) (true, d) s a b e (⟨up c, ν⟩ :: right) h₁' h₁'' hp hp').comp
        (locTwo (crossU K c d h₁ h₂ h₁' hp.step) (gammaR K N ν right hp.tail)) =
      locTwo (crossU K c d h₁ h₂ h₁'' hp'.step) (gammaR K N ν right hp'.tail) := by
  subst e
  exact BHom.ext fun _ => rfl

/-- The cap `E_j F_j → 1` in the region to the right of a strand `E_i` is natural in that region. -/
theorem trS_capMap_false (i j : Fin m) (L a b μ : Wt m) (e : a = b) (v : List (WCol m))
    (hE : StepR (true, i) (compOf N a) (compOf N L))
    (hE' : StepR (true, i) (compOf N b) (compOf N L))
    (hd : WOK N a (⟨up j, sh RD (dn j) + μ⟩ :: ⟨dn j, μ⟩ :: v)) (hc : WOK N a v)
    (hd' : WOK N b (⟨up j, sh RD (dn j) + μ⟩ :: ⟨dn j, μ⟩ :: v)) (hc' : WOK N b v) :
    (trS (K := K) (true, i) L a b e v hE hE' hc hc').comp
        (BHom.whiskerLeft (stepB K (true, i) (compOf N a) (compOf N L) hE)
          (capMap K N false j μ a v hd hc)) =
      (BHom.whiskerLeft (stepB K (true, i) (compOf N b) (compOf N L) hE')
          (capMap K N false j μ b v hd' hc')).comp
        (trS (true, i) L a b e (⟨up j, sh RD (dn j) + μ⟩ :: ⟨dn j, μ⟩ :: v) hE hE' hd hd') := by
  subst e
  exact BHom.ext fun _ => rfl

theorem sh_swap_cancel (i j : Fin m) (μ : Wt m) :
    sh RD (up j) + (sh RD (up i) + (sh RD (dn j) + μ)) = sh RD (up i) + μ := by
  rw [sh_up_eq, sh_up_eq, sh_dn_eq]
  abel

/-! ### `crossl` -/

set_option maxHeartbeats 20000000 in
theorem evalB_crossl_aux (dnScal : Fin m → Fin m → K) (i j : Fin m) (μ : Wt m)
    (v : List (psig RD).Colour)
    (ha : WOK N (sh RD (up i) + (sh RD (dn j) + μ)) ([⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v))
    (hb : WOK N (sh RD (up i) + (sh RD (dn j) + μ)) ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, μ⟩] ++ v)) :
    evalB K N dnScal (a := ob RD μ [up i, dn j]) (b := ob RD μ [dn j, up i]) _ v ha hb
        (LinDiagram.of (crossl RD i j μ)) =
      crosslW K i j ha.step ha.tail.step hb.step hb.tail.step (gammaR K N μ v ha.tail.tail) := by
  rw [evalB_of]
  have el : (Diagram.layers (crossl RD i j μ)).map (dataV v) =
      [([], .cup ⟨dn j, sh RD (up i) + μ⟩, [⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v),
        ([⟨dn j, sh RD (up i) + μ⟩], .gen (.cross true j i (sh RD (dn j) + μ)), ⟨dn j, μ⟩ :: v),
        ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, sh RD (up j) + (sh RD (dn j) + μ)⟩], .cap ⟨dn j, μ⟩,
          v)] := by
    simp only [crossl, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, Shape.dom, List.nil_append, List.append_nil, List.cons_append,
      Letter.dual_mk, Bool.not_false]
    rw [sh_swap_cancel, sh_up_dn]
  have h₂ : ChainW ([⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v)
      [([], .cup ⟨dn j, sh RD (up i) + μ⟩, [⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v),
        ([⟨dn j, sh RD (up i) + μ⟩], .gen (.cross true j i (sh RD (dn j) + μ)), ⟨dn j, μ⟩ :: v),
        ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, sh RD (up j) + (sh RD (dn j) + μ)⟩], .cap ⟨dn j, μ⟩,
          v)] ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, μ⟩] ++ v) := by
    have := el ▸ chainW_of_chain v (Diagram.chain (crossl RD i j μ))
    exact this
  have eq' : sh RD (dn j) + (sh RD (up i) + μ) = sh RD (up i) + (sh RD (dn j) + μ) :=
    add_left_comm _ _ _
  have hL1 : WOK N (sh RD (up i) + (sh RD (dn j) + μ))
      ([⟨dn j, sh RD (up i) + μ⟩, ⟨up j, sh RD (dn j) + (sh RD (up i) + μ)⟩,
        ⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v) :=
    ⟨ha.1, eq', hb.2.2.1, sh_up_dn j _, ha.1.congr eq'.symm, eq'.symm, ha.2.2⟩
  have hL2 : WOK N (sh RD (up i) + (sh RD (dn j) + μ))
      ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, sh RD (up j) + (sh RD (dn j) + μ)⟩,
        ⟨up j, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v) :=
    ⟨ha.1, eq', hb.2.2.1, by rw [sh_up_dn], hb.2.2.2.2.realized.congr (sh_up_dn j μ).symm, rfl,
      ha.2.2⟩
  have hL3 : WOK N (sh RD (up i) + (sh RD (dn j) + μ))
      ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, sh RD (up j) + (sh RD (dn j) + μ)⟩] ++ v) :=
    ⟨ha.1, eq', hb.2.2.1, by rw [sh_up_dn], wok_congr_region (sh_up_dn j μ).symm hb.2.2.2.2⟩
  have hd₂ : WOK N (sh RD (up i) + (sh RD (dn j) + μ))
      ([⟨dn j, sh RD (up i) + μ⟩, ⟨up j, sh RD (up i) + (sh RD (dn j) + μ)⟩,
        ⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v) :=
    ⟨ha.1, eq', hb.2.2.1, sh_swap_cancel i j μ, ha⟩
  show chainBD K N dnScal _ ([⟨up i, sh RD (dn j) + μ⟩, ⟨dn j, μ⟩] ++ v) _
    ([⟨dn j, sh RD (up i) + μ⟩, ⟨up i, μ⟩] ++ v) _ ha hb = _
  rw [chainBD_congr dnScal _ rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  rw [chainBD_three dnScal _ _ _ _ _ _ h₂ ha hb ha hL1 hd₂ hL2 hL2 hL3]
  simp only [genScal, BHom.csmul_one]
  dsimp only [wt_cons, wt_nil, wd_cons, wd_nil, Letter.dual_mk, bnot_false_rfl, bnot_true_rfl,
    list_nil_append_rfl, list_cons_append_rfl, List.nil_append, List.cons_append,
    gcod_cap_rfl, gdom_cap_rfl, gcod_cup_rfl, gdom_cup_rfl, gdom_cross_rfl, gcod_cross_rfl]
  rw [trW_self _ _ hL2 hL2, trW_self _ _ ha ha]
  erw [BHom.comp_id'', BHom.id_comp']
  erw [trW_cons' _ ⟨dn j, sh RD (up i) + μ⟩, trW_head, trW_cons' _ ⟨dn j, sh RD (up i) + μ⟩,
    trW_head]
  simp only [layerMap, genMap, cupMap, crossMap]
  simp only [← BHom.comp_assoc]
  simp only [← BHom.whiskerLeft_comp]
  simp only [BHom.comp_assoc]
  have hdμ : WOK N μ (⟨up j, sh RD (dn j) + μ⟩ :: ⟨dn j, μ⟩ :: v) :=
    ⟨hb.2.2.2.2.realized, sh_up_dn j μ, ha.2.2.1, rfl, hb.2.2.2.2⟩
  dsimp only [Letter.dual, dn, up, bnot_false_rfl, wt_cons, wt_nil,
    list_nil_append_rfl, list_cons_append_rfl, gcod_cap_rfl]
  erw [trS_trans' (K := K) (N := N) (up j) (sh RD (up i) + μ)
    (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (dn j) + (sh RD (up i) + μ))
    (sh RD (up i) + (sh RD (dn j) + μ)) _ _
    (⟨up i, sh RD (dn j) + μ⟩ :: ⟨dn j, μ⟩ :: v)]
  rw [trS_self'', BHom.comp_id'', ← BHom.comp_assoc,
    trS_capMap_false (hd' := hdμ), BHom.comp_assoc, trS_crossU_out, capMap_false_self,
    crosslW, BHom.whiskerLeft_comp, BHom.comp_assoc]
  rfl

/-- **`Γ_N` of the sideways crossing `crossl i j : E_i F_j 1_μ → F_j E_i 1_μ`** (KL III
`eq_crossl-gen`), whiskered by `v`, from any region `s` making the source valid: `crosslW`
(`Categorification.Flag.GammaSideways`). -/
theorem evalB_crossl_eq (dnScal : Fin m → Fin m → K) (i j : Fin m) (μ : Wt m) (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s ((ob RD μ [up i, dn j]).word ++ v))
    (hb : WOK N s ((ob RD μ [dn j, up i]).word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (crossl RD i j μ)) =
      crosslW K i j ha.step ha.tail.step hb.step hb.tail.step (gammaR K N μ v ha.tail.tail) := by
  have e : sh RD (up i) + (sh RD (dn j) + μ) = s := ha.2.1
  subst e
  exact evalB_crossl_aux dnScal i j μ v ha hb

end Categorification.Flag

end
