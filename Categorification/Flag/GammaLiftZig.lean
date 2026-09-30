/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftDots

/-!
# `Γ_N` respects the zigzag relations

KL III, arXiv:0807.3250v1, Definition 3.1, eqs. (3.1), (3.2) (biadjointness; Cautis–Lauda
arXiv:1111.1431v3, Definition 1.1 (1), `eq_biadjoint1`, `eq_biadjoint2`). In the presentations
`Categorification.KL3.Diagram.pres` and `CL.presCL` these are the relations of the pivotal base
(`StringDiagrams.Presentation.pivotal`): for every colour `c`, the left zigzag
`Pivotal.zigL c = (cup_c ⊗ 1_c) ≫ (1_c ⊗ cap_c)` on `c` and the right zigzag
`Pivotal.zigR c = (1_{c*} ⊗ cup_c) ≫ (cap_c ⊗ 1_{c*})` on the dual colour `c*` are identities.

For `c = E_i` (resp. `F_i`) the left zigzag is `Γ_N`'s identity (3.2) on `E` (resp. (3.1) on `F`),
`zigzag_E'` (resp. `zigzag_F`), and the right zigzag is (3.2) on `F` (resp. (3.1) on `E`),
`zigzag_F'` (resp. `zigzag_E`) (`Categorification.Flag.GammaCups`).

* `evalB_zigL`, `evalB_zigR`: the bimodule evaluations of `zigL c - 1` and `zigR c - 1`, whiskered
  on the right by any word, vanish.
-/

-- Preserve elaboration of semireducible diagram and bimodule transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-- The colour duality of `psig` (the duality of the pivotal extension). -/
abbrev psigDual (m : ℕ) : (sig0 (slRootDatum m)).ColourDuality := (inv (slRootDatum m)).toColourDuality

set_option maxHeartbeats 1000000 in
/-- The canonical chain of the left zigzag of the colour `⟨(b, i), r⟩`. -/
theorem canon_zigL (dnScal : Fin m → Fin m → K) (b : Bool) (i : Fin m) (r : Wt m)
    (v : List (psig RD).Colour)
    (h : ChainW (⟨(b, i), r⟩ :: v)
      [([], .cup ⟨(b, i), r⟩, ⟨(b, i), r⟩ :: v), ([⟨(b, i), r⟩], .cap ⟨(b, i), r⟩, v)]
      (⟨(b, i), r⟩ :: v))
    (ha : WOK N (sh RD (b, i) + r) (⟨(b, i), r⟩ :: v)) :
    chainBD K N dnScal (sh RD (b, i) + r) _ _ _ h ha ha = BHom.id _ := by
  have hmid : WOK N (sh RD (b, i) + r)
      ([] ++ gcod (.cup ⟨(b, i), r⟩ : (psig RD).Gen) ++ ⟨(b, i), r⟩ :: v) :=
    ⟨ha.1, rfl, ha.2.2.realized, sh_cancel b i r, ha⟩
  simp only [chainBD]
  split_ifs with h1 h2
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    cases b
    · simp only [layerMap, genMap, capMap, cupMap, trS_self', BHom.whiskerLeft_id,
        BHom.id_comp']
      erw [BHom.whiskerLeft_id, BHom.comp_id']
      exact zigzag_F (K := K) i (s := compOf N (sh RD (false, i) + r)) (s' := compOf N r)
        (ha.step : StepR (true, i) (compOf N (sh RD (false, i) + r)) (compOf N r)) ha.step
        (gammaR K N r v ha.2.2)
    · simp only [layerMap, genMap, capMap, cupMap, trS_self', BHom.whiskerLeft_id,
        BHom.id_comp']
      erw [BHom.whiskerLeft_id, BHom.comp_id']
      exact zigzag_E' (K := K) i (s := compOf N r) (s' := compOf N (sh RD (true, i) + r))
        ha.step (ha.step : StepR (false, i) (compOf N (sh RD (true, i) + r)) (compOf N r))
        (gammaR K N r v ha.2.2)
  all_goals first
    | exact absurd hmid ‹_›
    | exact absurd ha ‹_›

set_option maxHeartbeats 1000000 in
/-- The canonical chain of the right zigzag of the colour `⟨(b, i), r⟩`. -/
theorem canon_zigR (dnScal : Fin m → Fin m → K) (b : Bool) (i : Fin m) (r : Wt m)
    (v : List (psig RD).Colour)
    (h : ChainW (⟨(!b, i), sh RD (b, i) + r⟩ :: v)
      [([⟨(!b, i), sh RD (b, i) + r⟩], .cup ⟨(b, i), r⟩, v),
       ([], .cap ⟨(b, i), r⟩, ⟨(!b, i), sh RD (b, i) + r⟩ :: v)]
      (⟨(!b, i), sh RD (b, i) + r⟩ :: v))
    (ha : WOK N r (⟨(!b, i), sh RD (b, i) + r⟩ :: v)) :
    chainBD K N dnScal r _ _ _ h ha ha = BHom.id _ := by
  have hmid : WOK N r
      ([⟨(!b, i), sh RD (b, i) + r⟩] ++ gcod (.cup ⟨(b, i), r⟩ : (psig RD).Gen) ++ v) :=
    ⟨ha.1, ha.2.1, ha.2.2.realized, rfl, ha⟩
  simp only [chainBD]
  split_ifs with h1 h2
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    cases b
    · simp only [layerMap, genMap, capMap, cupMap, trS_self', BHom.whiskerLeft_id,
        BHom.id_comp']
      erw [BHom.whiskerLeft_id, BHom.comp_id']
      exact zigzag_E (K := K) i (s := compOf N (sh RD (false, i) + r)) (s' := compOf N r)
        (ha.step : StepR (true, i) (compOf N (sh RD (false, i) + r)) (compOf N r))
        (h1.2.2.step : StepR (false, i) (compOf N r) (compOf N (sh RD (false, i) + r)))
        (gammaR K N (sh RD (false, i) + r) v ha.2.2)
    · simp only [layerMap, genMap, capMap, cupMap, trS_self', BHom.whiskerLeft_id,
        BHom.id_comp']
      erw [BHom.whiskerLeft_id, BHom.comp_id']
      exact zigzag_F' (K := K) i (s := compOf N r) (s' := compOf N (sh RD (true, i) + r))
        (h1.2.2.step : StepR (true, i) (compOf N r) (compOf N (sh RD (true, i) + r)))
        (ha.step : StepR (false, i) (compOf N (sh RD (true, i) + r)) (compOf N r))
        (gammaR K N (sh RD (true, i) + r) v ha.2.2)
  all_goals first
    | exact absurd hmid ‹_›
    | exact absurd ha ‹_›

theorem evalB_id (dnScal : Fin m → Fin m → K) (a : Obj (psig RD)) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s (a.word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (𝟙 a)) = BHom.id _ := by
  rw [evalB_of]
  rfl

/-- **`Γ_N` respects the left zigzag relation** of every colour. -/
theorem evalB_zigL (dnScal : Fin m → Fin m → K) (c : (psig RD).Colour) (s : Wt m)
    (hs : s = (Pivotal.colourObj (psigDual m) c).start) (v : List (psig RD).Colour)
    (ha : WOK N s ((Pivotal.colourObj (psigDual m) c).word ++ v))
    (hb : WOK N s ((Pivotal.colourObj (psigDual m) c).word ++ v)) :
    evalB K N dnScal s v ha hb
      (LinDiagram.of (Pivotal.zigL (psigDual m) c) - LinDiagram.of (𝟙 _)) = 0 := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  have hs' : s = sh RD (b, i) + r := hs
  subst hs'
  rw [map_sub, evalB_id, sub_eq_zero]
  rw [evalB_of]
  have el : (Diagram.layers (Pivotal.zigL (psigDual m) ⟨(b, i), r⟩)).map (dataV v) =
      ([([], .cup ⟨(b, i), r⟩, ⟨(b, i), r⟩ :: v), ([⟨(b, i), r⟩], .cap ⟨(b, i), r⟩, v)] : List (LData m)) := by
    simp only [Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD, Pivotal.capD,
      Diagram.layers_layer, List.map_cons, List.map_nil, dataV, Layer.wr, Layer.wl,
      List.nil_append, List.cons_append]
  rw [chainBD_congr dnScal _ rfl rfl el _ (by exact ⟨rfl, rfl, rfl⟩) ha ha hb hb,
    trW_self, BHom.id_comp', BHom.comp_id']
  exact canon_zigL dnScal b i r v _ ha

/-- **`Γ_N` respects the right zigzag relation** of every colour. -/
theorem evalB_zigR (dnScal : Fin m → Fin m → K) (c : (psig RD).Colour) (s : Wt m)
    (hs : s = (Pivotal.dualObj (psigDual m) c).start) (v : List (psig RD).Colour)
    (ha : WOK N s ((Pivotal.dualObj (psigDual m) c).word ++ v))
    (hb : WOK N s ((Pivotal.dualObj (psigDual m) c).word ++ v)) :
    evalB K N dnScal s v ha hb
      (LinDiagram.of (Pivotal.zigR (psigDual m) c) - LinDiagram.of (𝟙 _)) = 0 := by
  obtain ⟨⟨b, i⟩, r⟩ := c
  have hs' : r = s := hs.symm
  subst hs'
  rw [map_sub, evalB_id, sub_eq_zero]
  rw [evalB_of]
  have el : (Diagram.layers (Pivotal.zigR (psigDual m) ⟨(b, i), r⟩)).map (dataV v) =
      ([([⟨(!b, i), sh RD (b, i) + r⟩], .cup ⟨(b, i), r⟩, v),
      ([], .cap ⟨(b, i), r⟩, ⟨(!b, i), sh RD (b, i) + r⟩ :: v)] : List (LData m)) := by
    simp only [Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD,
      Diagram.layers_layer, List.map_cons, List.map_nil, dataV, Layer.wr, Layer.wl,
      List.nil_append, List.cons_append]
    rfl
  rw [chainBD_congr dnScal _ rfl rfl el _ (by exact ⟨rfl, rfl, rfl⟩) ha ha hb hb,
    trW_self, BHom.id_comp', BHom.comp_id']
  exact canon_zigR dnScal b i r v _ ha

end Categorification.Flag

end
