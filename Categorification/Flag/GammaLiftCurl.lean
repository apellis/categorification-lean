/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftBubble
import Categorification.Diagrams.CL.Specialize

/-!
# `Γ_N` of the curls and of the right-hand sides of the curl relations

KL III, arXiv:0807.3250v1, Definition 3.1 iv) (first display; `Categorification.KL3.Diagram.
curlR`, `curlL`, `curlRHS`, `curlLHS`) and Proposition 6.3.

* `evalB_curlR_eq`, `evalB_curlL_eq`: when the region inside the curl is realized, `Γ_N` of the
  curl is `curlRW`, `curlLW` (`Categorification.Flag.GammaCurl`); `evalB_curlR_zero`,
  `evalB_curlL_zero`: otherwise it is `0`. For `curlR` the outer region is written `i_X + x`, so
  that the layer data are canonical; the one remaining relabelling of a region is absorbed by the
  cap (`capEFW_trS`).
* `evalB_curlRHS`, `evalB_curlLHS`: `Γ_N` of the right-hand sides, with the real or fake bubbles
  acting by `cwLH`, `ccwLH`.
* `curlR_rhs_degenerate`, `curlL_rhs_degenerate`: in the degenerate regions the right-hand sides
  vanish (`Eright_charpoly`, `ell_zero`).
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Relabelling the region inside a cap -/

/-- The cap `E_i F_i → 1` absorbs a relabelling of the region between its strands. -/
theorem capEFW_trS (i : Fin m) (L a b : Wt m) (e : a = b) (v : List (WCol m))
    (hE : StepR (true, i) (compOf N a) (compOf N L))
    (hE' : StepR (true, i) (compOf N b) (compOf N L))
    (hp : WOK N a (⟨dn i, L⟩ :: v)) (hp' : WOK N b (⟨dn i, L⟩ :: v)) :
    (capEFW K i hE' hp'.step (gammaR K N L v hp'.tail)).comp
        (trS (true, i) L a b e (⟨dn i, L⟩ :: v) hE hE' hp hp') =
      capEFW K i hE hp.step (gammaR K N L v hp.tail) := by
  subst e
  rfl

/-- The cap `F_i E_i → 1` absorbs a relabelling of the region between its strands. -/
theorem capFEW_trS (i : Fin m) (L a b : Wt m) (e : a = b) (v : List (WCol m))
    (hF : StepR (false, i) (compOf N a) (compOf N L))
    (hF' : StepR (false, i) (compOf N b) (compOf N L))
    (hp : WOK N a (⟨up i, L⟩ :: v)) (hp' : WOK N b (⟨up i, L⟩ :: v)) :
    (capFEW K i hp'.step hF' (gammaR K N L v hp'.tail)).comp
        (trS (false, i) L a b e (⟨up i, L⟩ :: v) hF hF' hp hp') =
      capFEW K i hp.step hF (gammaR K N L v hp.tail) := by
  subst e
  rfl

/-! ### The right curl -/

set_option maxHeartbeats 4000000 in
/-- **`Γ_N` of the right curl** (`curlR i λ`, KL III Definition 3.1 iv)), with the outer region
written `λ = i_X + x`, whenever the region `x` inside the curl is realized: `curlRW`. -/
theorem evalB_curlR_eq (dnScal : Fin m → Fin m → K) (i : Fin m) (x : Wt m)
    (v : List (psig RD).Colour)
    (ha hb : WOK N (sh RD (up i) + (sh RD (up i) + x))
      ((ob RD (sh RD (up i) + x) [up i]).word ++ v))
    (hm : WOK N (sh RD (up i) + (sh RD (up i) + x))
      ([⟨up i, sh RD (up i) + x⟩, ⟨up i, x⟩, ⟨dn i, sh RD (up i) + x⟩] ++ v)) :
    evalB K N dnScal _ v ha hb (LinDiagram.of (curlR RD i (sh RD (up i) + x))) =
      curlRW K i ha.step hm.tail.step (gammaR K N (sh RD (up i) + x) v ha.tail) := by
  rw [evalB_of]
  have el : (Diagram.layers (curlR RD i (sh RD (up i) + x))).map (dataV v) =
      [([⟨up i, sh RD (up i) + x⟩], .cup ⟨up i, x⟩, v),
        ([], .gen (.cross true i i x), ⟨dn i, sh RD (up i) + x⟩ :: v),
        ([⟨up i, sh RD (up i) + x⟩], .cap ⟨dn i, sh RD (up i) + x⟩, v)] := by
    simp only [curlR, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, Shape.dom, List.nil_append, List.append_nil, List.cons_append,
      Letter.dual_mk, Bool.not_true, Bool.not_false]
    rw [sh_dn_up]
  have h₂ : ChainW ((ob RD (sh RD (up i) + x) [up i]).word ++ v)
      [([⟨up i, sh RD (up i) + x⟩], .cup ⟨up i, x⟩, v),
        ([], .gen (.cross true i i x), ⟨dn i, sh RD (up i) + x⟩ :: v),
        ([⟨up i, sh RD (up i) + x⟩], .cap ⟨dn i, sh RD (up i) + x⟩, v)]
      ((ob RD (sh RD (up i) + x) [up i]).word ++ v) :=
    el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal _ rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  simp only [chainBD]
  split_ifs with h1 h2 h3
  · simp only [show genScal K dnScal (PivotalGen.cap ⟨dn i, sh RD (up i) + x⟩ : (psig RD).Gen) = 1
        from rfl, show genScal K dnScal (PivotalGen.gen (Gen0.cross true i i x) : (psig RD).Gen) = 1
        from rfl, show genScal K dnScal (PivotalGen.cup ⟨up i, x⟩ : (psig RD).Gen) = 1 from rfl,
      BHom.csmul_one]
    erw [trW_self _ _ h3 hb, trW_self _ _ h1]
    simp only [BHom.id_comp', BHom.comp_id'']
    erw [trW_cons' _ ⟨up i, sh RD (up i) + x⟩, trW_head]
    simp only [layerMap, genMap, cupMap, crossMap, capMap, trS_self'']
    erw [BHom.whiskerLeft_id, BHom.whiskerLeft_id]
    erw [BHom.comp_id'', BHom.comp_id'']
    rw [← BHom.whiskerLeft_comp]
    erw [capEFW_trS]
    rw [curlRW, BHom.comp_assoc]
    rfl
  all_goals first
    | exact absurd hm ‹_›
    | exact absurd hb ‹_›

/-- **`Γ_N` of the right curl when the region inside the curl is not realized**: `0`. -/
theorem evalB_curlR_zero (dnScal : Fin m → Fin m → K) (i : Fin m) (x : Wt m)
    (v : List (psig RD).Colour)
    (ha hb : WOK N (sh RD (up i) + (sh RD (up i) + x))
      ((ob RD (sh RD (up i) + x) [up i]).word ++ v))
    (hx : ¬ Realized N x) :
    evalB K N dnScal _ v ha hb (LinDiagram.of (curlR RD i (sh RD (up i) + x))) = 0 := by
  rw [evalB_of]
  refine chainBD_eq_zero_of_first dnScal _ _ _ _ _ ha hb
    (dataV v (lay RD (sh RD (up i) + x) [up i] (.cup (up i)) []))
    [dataV v (lay RD (sh RD (up i) + x) [] (.cross true i i) [dn i]),
      dataV v (lay RD (sh RD (up i) + x) [up i] (.cap (dn i)) [])] rfl ?_
  intro h1
  exact hx (Realized.congr h1.2.2.2.2.1 (sh_dn_up i x))

/-- **`Γ_N` of the right-hand side `curlRHS` of the right curl relation**:
`-∑_{f=0}^{-n} (ξ^{-n-f} on E_i) · Γ_N(cwL (n - 1 + f))`, the bubbles acting in the region `λ`. -/
theorem evalB_curlRHS (dnScal : Fin m → Fin m → K) (i : Fin m) (lam : Wt m) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD lam [up i]).word ++ v)) :
    evalB K N dnScal s v ha hb (curlRHS RD K i lam) =
      BHom.mulB (-∑ f ∈ Finset.range (-nH (compOf N lam) i + 1).toNat,
        BRing.tmul (stepB K (true, i) (compOf N lam) (compOf N s) ha.step)
          (gammaR K N lam v ha.tail)
          (eXi K i (compOf N lam) ha.step.2 ^ (-nH (compOf N lam) i - f).toNat)
          ((gammaR K N lam v ha.tail).left
            (cwLH (compOf N lam) i (nH (compOf N lam) i - 1 + f)))) := by
  have hn : ip RD i lam = nH (compOf N lam) i := ip_eq_nH ha.tail.realized i
  unfold curlRHS
  rw [map_neg, map_sum, mulB_neg', mulB_sum', hn]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [evalB_comp dnScal s v ha ha hb, evalB_bubR_up, evalB_cwL]
  erw [evalB_dots_first_bub]
  rw [BHom.whiskerLeft_mulB, BHom.mulB_comp_mulB]
  erw [BRing.tmul_mul_tmul, one_mul, mul_one]
  rfl

/-- **`Γ_N` of the right-hand side `curlLHS` of the left curl relation**:
`∑_{g=0}^{n} Γ_N(ccwL (-n - 1 + g)) · (ξ^{n-g} on E_i)`, the bubbles acting in the region
`λ = μ + i_X` to the left of `E_i`. -/
theorem evalB_curlLHS (dnScal : Fin m → Fin m → K) (i : Fin m) (μ : Wt m) (s : Wt m)
    (hs : s = sh RD (up i) + μ)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD μ [up i]).word ++ v)) :
    evalB K N dnScal s v ha hb (curlLHS RD K i μ) =
      BHom.mulB (∑ g ∈ Finset.range (nH (compOf N s) i + 1).toNat,
        BRing.tmul (stepB K (true, i) (compOf N μ) (compOf N s) ha.step) (gammaR K N μ v ha.tail)
          ((stepB K (true, i) (compOf N μ) (compOf N s) ha.step).left
            (ccwLH (compOf N s) i (-nH (compOf N s) i - 1 + g)) *
            xiStep K (true, i) (compOf N μ) (compOf N s) ha.step ^ (nH (compOf N s) i - g).toNat)
          1) := by
  subst hs
  have hn := ip_eq_nH ha.realized i
  unfold curlLHS
  rw [map_sum, mulB_sum']
  simp only [wt_cons, wt_nil]
  rw [hn]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [evalB_comp dnScal _ v ha ha hb, evalB_bubL_up]
  erw [evalB_ccwL]
  erw [evalB_dots_first_bub]
  rw [BHom.mulB_comp_mulB]
  congr 1
  show BRing.tmul _ _ _ 1 * BRing.tmul _ _ _ 1 = _
  rw [BRing.tmul_mul_tmul, one_mul, mul_comm]
  rfl

/-! ### The left curl -/

set_option maxHeartbeats 4000000 in
/-- **`Γ_N` of the left curl** (`curlL i μ`, KL III Definition 3.1 iv)) whenever the region
`c = μ + 2 i_X` inside the curl is realized: `curlLW`. -/
theorem evalB_curlL_eq (dnScal : Fin m → Fin m → K) (i : Fin m) (μ : Wt m)
    (v : List (psig RD).Colour)
    (ha hb : WOK N (sh RD (up i) + μ) ((ob RD μ [up i]).word ++ v))
    (hm : WOK N (sh RD (up i) + μ)
      ([⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩, ⟨up i, sh RD (up i) + μ⟩, ⟨up i, μ⟩] ++ v)) :
    evalB K N dnScal _ v ha hb (LinDiagram.of (curlL RD i μ)) =
      curlLW K i ha.step hm.tail.step (gammaR K N μ v ha.tail) := by
  rw [evalB_of]
  have hL1 : WOK N (sh RD (up i) + μ) (⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩ ::
      ⟨up i, sh RD (dn i) + (sh RD (up i) + (sh RD (up i) + μ))⟩ :: ⟨up i, μ⟩ :: v) :=
    ⟨hm.1, hm.2.1, hm.2.2.1, sh_up_dn i _, Realized.congr hm.1 (sh_dn_up i _).symm,
      (sh_dn_up i _).symm, hm.2.2.2.2.2.2⟩
  have el : (Diagram.layers (curlL RD i μ)).map (dataV v) =
      [([], .cup ⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩, ⟨up i, μ⟩ :: v),
        ([⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩], .gen (.cross true i i μ), v),
        ([], .cap ⟨up i, sh RD (up i) + μ⟩, ⟨up i, μ⟩ :: v)] := by
    simp only [curlL, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, Shape.dom, List.nil_append, List.append_nil, List.cons_append,
      Letter.dual_mk, Bool.not_true, Bool.not_false]
  have h₂ : ChainW ((ob RD μ [up i]).word ++ v)
      [([], .cup ⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩, ⟨up i, μ⟩ :: v),
        ([⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩], .gen (.cross true i i μ), v),
        ([], .cap ⟨up i, sh RD (up i) + μ⟩, ⟨up i, μ⟩ :: v)]
      ((ob RD μ [up i]).word ++ v) :=
    el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal _ rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  simp only [chainBD]
  split_ifs with h1 h2 h3
  · simp only [show genScal K dnScal (PivotalGen.cap ⟨up i, sh RD (up i) + μ⟩ : (psig RD).Gen) = 1
        from rfl, show genScal K dnScal (PivotalGen.gen (Gen0.cross true i i μ) : (psig RD).Gen) = 1
        from rfl, show genScal K dnScal (PivotalGen.cup ⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩ :
        (psig RD).Gen) = 1 from rfl, BHom.csmul_one]
    erw [trW_self _ _ h3 hb, trW_self _ _ h2]
    simp only [BHom.id_comp', BHom.comp_id'']
    erw [trW_cons' _ ⟨dn i, sh RD (up i) + (sh RD (up i) + μ)⟩, trW_head]
    simp only [layerMap, genMap, cupMap, crossMap]
    rw [capMap_true_self]
    dsimp only [wt_cons, wt_nil, wd_cons, wd_nil, Letter.dual_mk, bnot_false_rfl, bnot_true_rfl,
      list_nil_append_rfl, list_cons_append_rfl, List.nil_append, List.cons_append,
      gcod_cap_rfl, gdom_cap_rfl, gcod_cup_rfl, gdom_cup_rfl, gdom_cross_rfl, gcod_cross_rfl,
      ob_word, ob_start]
    rewrite [BHom.comp_id'', BHom.comp_assoc, BHom.comp_assoc,
      ← BHom.comp_assoc (BHom.whiskerLeft _ (trS _ _ _ _ _ _ _ _ _ _)), ← BHom.whiskerLeft_comp,
      trS_trans', trS_self'', BHom.whiskerLeft_id, BHom.id_comp', curlLW]
    rfl
  all_goals first
    | exact absurd hL1 ‹_›
    | exact absurd hm ‹_›
    | exact absurd hb ‹_›

/-- **`Γ_N` of the left curl when the region inside the curl is not realized**: `0`. -/
theorem evalB_curlL_zero (dnScal : Fin m → Fin m → K) (i : Fin m) (μ : Wt m)
    (v : List (psig RD).Colour)
    (ha hb : WOK N (sh RD (up i) + μ) ((ob RD μ [up i]).word ++ v))
    (hc : ¬ Realized N (sh RD (up i) + (sh RD (up i) + μ))) :
    evalB K N dnScal _ v ha hb (LinDiagram.of (curlL RD i μ)) = 0 := by
  rw [evalB_of]
  refine chainBD_eq_zero_of_first dnScal _ _ _ _ _ ha hb
    (dataV v (lay RD μ [] (.cup (dn i)) [up i]))
    [dataV v (lay RD μ [dn i] (.cross true i i) []),
      dataV v (lay RD μ [] (.cap (up i)) [up i])] rfl ?_
  intro h1
  exact hc h1.2.2.1

/-! ### Degenerate regions: the dot is a root of a total Chern class -/

/-- If block `i` of the region `k` to the right of `E_i` is empty, the right-hand side of the
right curl relation vanishes (`Eright_charpoly`). -/
theorem curlR_rhs_degenerate (i : Fin m) {k t : Comp m} (h : StepR (true, i) k t)
    (h0 : k i.castSucc = 0) {E' : Type u} [CommRing E'] (Y : BRing (H K k) E') :
    ∑ f ∈ Finset.range (-nH k i + 1).toNat, BRing.tmul (stepB K (true, i) k t h) Y
      (eXi K i k h.2 ^ (-nH k i - f).toNat) (Y.left (cwLH k i (nH k i - 1 + f))) = 0 := by
  have hn : nH k i = (k i.castSucc : ℤ) - k i.succ := rfl
  have hc := Eright_charpoly (K := K) i h
  rw [show (-nH k i + 1).toNat = k i.succ + 1 by omega]
  have e : ∀ f ∈ Finset.range (k i.succ + 1), BRing.tmul (stepB K (true, i) k t h) Y
      (eXi K i k h.2 ^ (-nH k i - f).toNat) (Y.left (cwLH k i (nH k i - 1 + f))) =
      BRing.tmul (stepB K (true, i) k t h) Y ((-1) ^ f * ((stepB K (true, i) k t h).right
        (x K k i.succ f) * xiStep K (true, i) k t h ^ (k i.succ - f))) 1 := by
    intro f hf
    have hf' := Finset.mem_range.1 hf
    rw [cwLH_eq, ite_eq_left (by omega), show (nH k i - 1 + (f : ℤ) + 1 - nH k i).toNat = f by omega,
      PsiH_of_castSucc_zero _ _ h0, show (-nH k i - f).toNat = k i.succ - f by omega,
      ← mul_one (Y.left _), ← BRing.tmul_balance, map_mul, map_pow, map_neg, map_one]
    congr 1
    rw [show xiStep K (true, i) k t h = (eXi K i k h.2 : (stepB K (true, i) k t h).T) from rfl]
    ring
  rw [Finset.sum_congr rfl e, ← BRing.sum_tmul, hc, BRing.zero_tmul]

/-- If block `i + 1` of the region `k` to the left of `E_i` is empty, the right-hand side of the
left curl relation vanishes (`Eleft_charpoly`). -/
theorem curlL_rhs_degenerate (i : Fin m) {t k : Comp m} (h : StepR (true, i) t k)
    (h0 : k i.succ = 0) {E' : Type u} [CommRing E'] (Y : BRing (H K t) E') :
    ∑ g ∈ Finset.range (nH k i + 1).toNat, BRing.tmul (stepB K (true, i) t k h) Y
      ((stepB K (true, i) t k h).left (ccwLH k i (-nH k i - 1 + g)) *
        xiStep K (true, i) t k h ^ (nH k i - g).toNat) 1 = 0 := by
  rw [← BRing.sum_tmul, ell_zero (K := K) i (h : StepR (false, i) k t) h0, BRing.zero_tmul]

end Categorification.Flag

end
