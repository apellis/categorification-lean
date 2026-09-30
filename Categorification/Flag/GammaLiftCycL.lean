/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftCyc

/-!
# `Γ_N` respects the relation `cycCrossL`

Cautis–Lauda arXiv:1111.1431v3, §2 (`eq_almost_cyclic`, p. 6), the relation
`cycCrossL j i μ : t_{ji}^{-1} · rotCrossL j i - downCross j i = 0` of `CL.presCL` for the `sl_n`
scalars. The left rotation is evaluated on canonical data (`canon_rotCrossL`), in which three
relabellings of inner regions remain; they are absorbed by the crossing and the two caps that
consume the relabelled strands (`trW_absorb_cross2`, `trW_absorb_capEF3`, `trW_absorb_capEF2`). On
the path model the left rotation is (6.9) (`rotCrossLW_eq_crossDn`, `rotCrossLW_same_eq`).
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Relabellings absorbed by a crossing or a cap -/

theorem trW_absorb_cross2 (a b : Fin m) (l₁ l₂ : SLetter m) {s a₁ a₂ x x' y : Wt m}
    (rest : List (WCol m)) (hx : x = x')
    (e : ((⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up a, x⟩ :: ⟨up b, y⟩ :: rest : List (WCol m)) =
      ⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up a, x'⟩ :: ⟨up b, y⟩ :: rest))
    (h : WOK N s (⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up a, x⟩ :: ⟨up b, y⟩ :: rest))
    (h' : WOK N s (⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up a, x'⟩ :: ⟨up b, y⟩ :: rest))
    {r₁' : Comp m} (h₁' : StepR (true, b) r₁' (compOf N a₂)) (h₂' : StepR (true, a) (compOf N y) r₁')
    (hr : WOK N y rest) :
    (BHom.whiskerLeft (stepB K l₁ (compOf N a₁) (compOf N s) h'.step)
      (BHom.whiskerLeft (stepB K l₂ (compOf N a₂) (compOf N a₁) h'.tail.step)
        (locTwo (crossU K a b (h'.tail.tail.step : StepR (true, a) (compOf N x') (compOf N a₂))
          (h'.tail.tail.tail.step : StepR (true, b) (compOf N y) (compOf N x')) h₁' h₂')
          (gammaR K N y rest hr)))).comp (trW s e h h') =
    BHom.whiskerLeft (stepB K l₁ (compOf N a₁) (compOf N s) h.step)
      (BHom.whiskerLeft (stepB K l₂ (compOf N a₂) (compOf N a₁) h.tail.step)
        (locTwo (crossU K a b (h.tail.tail.step : StepR (true, a) (compOf N x) (compOf N a₂))
          (h.tail.tail.tail.step : StepR (true, b) (compOf N y) (compOf N x)) h₁' h₂')
          (gammaR K N y rest hr))) := by
  subst hx
  rw [trW_self]
  rfl

theorem trW_absorb_capEF3 (b : Fin m) (l₁ l₂ l₃ : SLetter m) {s a₁ a₂ c x x' : Wt m}
    (rest : List (WCol m)) (hx : x = x')
    (e : ((⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨l₃, c⟩ :: ⟨up b, x⟩ :: ⟨dn b, c⟩ :: rest : List (WCol m)) =
      ⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨l₃, c⟩ :: ⟨up b, x'⟩ :: ⟨dn b, c⟩ :: rest))
    (h : WOK N s (⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨l₃, c⟩ :: ⟨up b, x⟩ :: ⟨dn b, c⟩ :: rest))
    (h' : WOK N s (⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨l₃, c⟩ :: ⟨up b, x'⟩ :: ⟨dn b, c⟩ :: rest))
    (hr : WOK N c rest) :
    (BHom.whiskerLeft (stepB K l₁ (compOf N a₁) (compOf N s) h'.step)
      (BHom.whiskerLeft (stepB K l₂ (compOf N a₂) (compOf N a₁) h'.tail.step)
        (BHom.whiskerLeft (stepB K l₃ (compOf N c) (compOf N a₂) h'.tail.tail.step)
          (capEFW K b (h'.tail.tail.tail.step : StepR (true, b) (compOf N x') (compOf N c))
            (h'.tail.tail.tail.step : StepR (false, b) (compOf N c) (compOf N x'))
            (gammaR K N c rest hr))))).comp (trW s e h h') =
    BHom.whiskerLeft (stepB K l₁ (compOf N a₁) (compOf N s) h.step)
      (BHom.whiskerLeft (stepB K l₂ (compOf N a₂) (compOf N a₁) h.tail.step)
        (BHom.whiskerLeft (stepB K l₃ (compOf N c) (compOf N a₂) h.tail.tail.step)
          (capEFW K b (h.tail.tail.tail.step : StepR (true, b) (compOf N x) (compOf N c))
            (h.tail.tail.tail.step : StepR (false, b) (compOf N c) (compOf N x))
            (gammaR K N c rest hr)))) := by
  subst hx
  rw [trW_self]
  rfl

theorem trW_absorb_capEF2 (b : Fin m) (l₁ l₂ : SLetter m) {s a₁ a₂ x x' : Wt m}
    (rest : List (WCol m)) (hx : x = x')
    (e : ((⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up b, x⟩ :: ⟨dn b, a₂⟩ :: rest : List (WCol m)) =
      ⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up b, x'⟩ :: ⟨dn b, a₂⟩ :: rest))
    (h : WOK N s (⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up b, x⟩ :: ⟨dn b, a₂⟩ :: rest))
    (h' : WOK N s (⟨l₁, a₁⟩ :: ⟨l₂, a₂⟩ :: ⟨up b, x'⟩ :: ⟨dn b, a₂⟩ :: rest))
    (hr : WOK N a₂ rest) :
    (BHom.whiskerLeft (stepB K l₁ (compOf N a₁) (compOf N s) h'.step)
      (BHom.whiskerLeft (stepB K l₂ (compOf N a₂) (compOf N a₁) h'.tail.step)
        (capEFW K b (h'.tail.tail.step : StepR (true, b) (compOf N x') (compOf N a₂))
          (h'.tail.tail.step : StepR (false, b) (compOf N a₂) (compOf N x'))
          (gammaR K N a₂ rest hr)))).comp (trW s e h h') =
    BHom.whiskerLeft (stepB K l₁ (compOf N a₁) (compOf N s) h.step)
      (BHom.whiskerLeft (stepB K l₂ (compOf N a₂) (compOf N a₁) h.tail.step)
        (capEFW K b (h.tail.tail.step : StepR (true, b) (compOf N x) (compOf N a₂))
          (h.tail.tail.step : StepR (false, b) (compOf N a₂) (compOf N x))
          (gammaR K N a₂ rest hr))) := by
  subst hx
  rw [trW_self]
  rfl
set_option maxHeartbeats 5000000 in
/-- **The left rotation of the upward crossing** on canonical layer data (regions written from the
region `q` on the right of the two strands): the path-model map `rotCrossLW` (KL III
`eq_cyclic_cross-gen`, right-hand picture). -/
theorem canon_rotCrossL (dnScal : Fin m → Fin m → K) (i j : Fin m) (q : Wt m)
    (v : List (psig RD).Colour)
    (h : ChainW (⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v)
      [([], .cup ⟨dn i, (sh RD (dn j) + q)⟩, ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + q)⟩], .cup ⟨dn j, q⟩, ⟨up i, (sh RD (dn i) + (sh RD (dn j) + q))⟩ :: ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + q)⟩, ⟨dn j, q⟩], .gen (.cross true j i (sh RD (dn i) + (sh RD (dn j) + q))), ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + q)⟩, ⟨dn j, q⟩, ⟨up i, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩], .cap ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩, ⟨dn i, q⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + q)⟩, ⟨dn j, q⟩], .cap ⟨dn i, q⟩, v)]
      (⟨dn i, (sh RD (dn j) + q)⟩ :: ⟨dn j, q⟩ :: v))
    (ha : WOK N (sh RD (dn i) + (sh RD (dn j) + q)) (⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v))
    (hb : WOK N (sh RD (dn i) + (sh RD (dn j) + q)) (⟨dn i, (sh RD (dn j) + q)⟩ :: ⟨dn j, q⟩ :: v)) :
    chainBD K N dnScal _ _ _ _ h ha hb = rotCrossLW K i j ha.step ha.tail.step hb.step
      hb.tail.step (gammaR K N _ v ha.tail.tail) := by
  have eA : sh RD (up i) + (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q))) = q := by
    simp only [sh_dn']; abel
  have w₁ : WOK N (sh RD (dn i) + (sh RD (dn j) + q)) (⟨dn i, (sh RD (dn j) + q)⟩ :: ⟨up i, (sh RD (dn i) + (sh RD (dn j) + q))⟩ :: ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v) :=
    ⟨ha.1, rfl, hb.2.2.1, sh_up_dn_cancel i _, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
  have w₂ : WOK N (sh RD (dn i) + (sh RD (dn j) + q)) (⟨dn i, (sh RD (dn j) + q)⟩ :: ⟨dn j, q⟩ :: ⟨up j, (sh RD (dn j) + q)⟩ :: ⟨up i, (sh RD (dn i) + (sh RD (dn j) + q))⟩ ::
      ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v) :=
    ⟨ha.1, rfl, hb.2.2.1, rfl, hb.2.2.2.2.realized, sh_up_dn_cancel j q, hb.2.2.1,
      sh_up_dn_cancel i _, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
  have w₃ : WOK N (sh RD (dn i) + (sh RD (dn j) + q)) (⟨dn i, (sh RD (dn j) + q)⟩ :: ⟨dn j, q⟩ :: ⟨up i, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨up j, (sh RD (dn i) + (sh RD (dn j) + q))⟩ ::
      ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v) :=
    ⟨ha.1, rfl, hb.2.2.1, rfl, hb.2.2.2.2.realized, eA, ha.2.2.1, rfl, ha.1, ha.2.1, ha.2.2.1,
      ha.2.2.2.1, ha.2.2.2.2⟩
  have w₄ : WOK N (sh RD (dn i) + (sh RD (dn j) + q)) (⟨dn i, (sh RD (dn j) + q)⟩ :: ⟨dn j, q⟩ :: ⟨up i, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v) :=
    ⟨ha.1, rfl, hb.2.2.1, rfl, hb.2.2.2.2.realized, eA, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
  simp only [chainBD]
  split_ifs with h1 h2 h3 h4 h5
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, crossMap]
    rw [cupMap_false_canon, cupMap_false_canon, capMap_false_canon, capMap_false_canon]
    rw [trW_absorb_capEF2 i (dn i) (dn j) v (x := (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))) (x' := sh RD (dn i) + q)
      (by simp only [sh_dn']; abel) _ h4]
    rw [trW_absorb_capEF3 j (dn i) (dn j) (up i) (⟨dn i, q⟩ :: v) (a₁ := (sh RD (dn j) + q)) (a₂ := q)
      (c := (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))) (x := (sh RD (dn i) + (sh RD (dn j) + q))) (x' := sh RD (dn j) + (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))) (sh_cancel true j _).symm _ h3]
    rw [trW_absorb_cross2 j i (dn i) (dn j) (⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + q)))⟩ :: ⟨dn i, q⟩ :: v) (a₁ := (sh RD (dn j) + q))
      (a₂ := q) (y := (sh RD (dn i) + (sh RD (dn j) + q))) (x := (sh RD (dn j) + q)) (x' := sh RD (up i) + (sh RD (dn i) + (sh RD (dn j) + q))) (sh_up_dn_cancel i _).symm _ h2]
    rfl
  all_goals first
    | exact absurd w₁ ‹_›
    | exact absurd w₂ ‹_›
    | exact absurd w₃ ‹_›
    | exact absurd w₄ ‹_›
    | exact absurd hb ‹_›

/-! ### The relation -/

set_option maxHeartbeats 2000000 in
/-- **`Γ_N` respects `cycCrossL j i μ`** (Cautis–Lauda `eq_almost_cyclic`, `sl_n` scalars):
`t_{ji}^{-1} · Γ(rotCrossL j i) = Γ(downCross j i)`, where `Γ(downCross j i) = t_{ji}^{-1} · (6.9)`. -/
theorem evalB_cycCrossL (j i : Fin m) (μ s : Wt m) (hs : s = (ob RD μ [dn j, dn i]).start)
    (v : List (psig RD).Colour) (ha : WOK N s ((ob RD μ [dn j, dn i]).word ++ v))
    (hb : WOK N s ((ob RD μ [dn i, dn j]).word ++ v)) :
    evalB K N (gammaDn K m) s v ha hb
      ((((((CL.Sln.slnScalars K m).t j i)⁻¹ : Kˣ) : K) • LinDiagram.of (rotCrossL RD j i μ) -
        LinDiagram.of (downCross RD j i μ))) = 0 := by
  have hs' : s = (sh RD (dn i) + (sh RD (dn j) + μ)) := by
    rw [hs]
    exact add_left_comm _ _ _
  subst hs'
  rw [map_sub, map_smul, evalB_downCross (gammaDn K m) j i _ _ v ha hb, evalB_of]
  have e₁ : (ob RD μ [dn j, dn i]).word ++ v =
      (⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v : List (WCol m)) := by
    simp only [ob_word, wd, wt, List.cons_append, List.nil_append, sh_dn', sh_up']
    abel_nf
  have e₂ : (ob RD μ [dn i, dn j]).word ++ v =
      (⟨dn i, (sh RD (dn j) + μ)⟩ :: ⟨dn j, μ⟩ :: v : List (WCol m)) := rfl
  have ha' := e₁ ▸ ha
  have hb' := e₂ ▸ hb
  have el : (Diagram.layers (rotCrossL RD j i μ)).map (dataV v) =
      ([([], .cup ⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩], .cup ⟨dn j, μ⟩, ⟨up i, (sh RD (dn i) + (sh RD (dn j) + μ))⟩ :: ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩], .gen (.cross true j i (sh RD (dn i) + (sh RD (dn j) + μ))), ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩, ⟨up i, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩], .cap ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩, ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩], .cap ⟨dn i, μ⟩, v)] : List (LData m)) := by
    simp only [rotCrossL, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, Shape.dom, List.nil_append, List.cons_append, List.append_nil,
      Letter.dual_mk]
    simp only [Bool.not_false, sh_dn', sh_up']
    abel_nf
  have hch : ChainW (⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v)
      [([], .cup ⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩], .cup ⟨dn j, μ⟩, ⟨up i, (sh RD (dn i) + (sh RD (dn j) + μ))⟩ :: ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩], .gen (.cross true j i (sh RD (dn i) + (sh RD (dn j) + μ))), ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩ :: ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩, ⟨up i, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩], .cap ⟨dn j, (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ)))⟩, ⟨dn i, μ⟩ :: v),
       ([⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩], .cap ⟨dn i, μ⟩, v)] (⟨dn i, (sh RD (dn j) + μ)⟩ :: ⟨dn j, μ⟩ :: v) := by
    rw [← el, ← e₁, ← e₂]
    exact chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr (gammaDn K m) _ e₁ e₂ el _ hch ha ha' hb hb', canon_rotCrossL]
  have hA : (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + μ))) = wt RD μ [dn i] := by
    simp only [wt_cons, wt_nil, sh_dn']; abel
  have hrel := crossDn_relabel (K := K) (N := N) j i v hA (rfl : μ = wt RD μ []) (rfl : (sh RD (dn j) + μ) = _)
    e₁ e₂.symm ha' ha hb' hb
  by_cases hij : i = j
  · subst hij
    rw [rotCrossLW_same_eq]
    erw [hrel]
    exact sub_self _
  · rw [rotCrossLW_eq_crossDn i j _ _ _ _ _ hij]
    erw [hrel]
    exact sub_self _

end Categorification.Flag

end
