/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftKLR
import Categorification.Flag.GammaCyclicSameL
import Categorification.Flag.GammaErratumCheck

/-!
# `Γ_N` respects the `Q`-cyclicity of crossings

Cautis–Lauda arXiv:1111.1431v3, §2 (`eq_almost_cyclic`, p. 6): the relations
`cycCrossR j i μ : t_{ij}^{-1} · rotCrossR j i - downCross j i = 0` and
`cycCrossL j i μ : t_{ji}^{-1} · rotCrossL j i - downCross j i = 0` of `CL.presCL`
(`CL.relationCL`), for the `sl_n` scalars `CL.Sln.slnScalars` (`t_{ij} = i - j` for adjacent
`i, j`, `1` otherwise). The downward crossing `downCross j i` is sent to `t_{ji}^{-1}` times KL III's
(6.9) (`crossDn`), i.e. the generator scalars are `gammaDn i j = t_{ij}^{-1}`
(`Categorification.Flag.genScal`).

On the path model the left rotation of the upward crossing is (6.9) for all `i, j`, the right
rotation is (6.9) for `i · j ≠ -1` and `-(6.9)` for `i · j = -1`
(`Categorification.Flag.rotCrossLW_eq_crossDn`, `rotCrossRW_eq_crossDn`, `rotCrossRW_same_eq`,
`rotCrossLW_same_eq`); since `t_{ij} = -t_{ji}` for adjacent colours, both relations hold.

The five layers of each rotation are evaluated on *canonical* layer data (all regions written
from the leftmost region `s`), in which every identification of regions is trivial except one
relabelling of an inner region, absorbed by the adjacent cap or crossing (`trW_absorb_capFE`, …);
the canonical data differ from the normal-form data of the relation only by relabellings of the
two boundary objects, which are absorbed by the downward crossing (`crossDn_relabel`).
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Cups and caps in canonical position -/

theorem cupMap_true_canon (i : Fin m) (r : Wt m) (right : List (WCol m))
    (hd : WOK N (sh RD (up i) + r) right)
    (hc : WOK N (sh RD (up i) + r) (⟨up i, r⟩ :: ⟨dn i, sh RD (up i) + r⟩ :: right)) :
    cupMap K N true i r (sh RD (up i) + r) right hd hc =
      cupEFW K i hc.step (hc.step : StepR (false, i) (compOf N (sh RD (up i) + r)) (compOf N r))
        (gammaR K N _ right hd) := by
  simp only [cupMap, trS_self']
  erw [BHom.whiskerLeft_id, BHom.id_comp']

theorem capMap_true_canon (i : Fin m) (r : Wt m) (right : List (WCol m))
    (hd : WOK N r (⟨dn i, sh RD (up i) + r⟩ :: ⟨up i, r⟩ :: right)) (hc : WOK N r right) :
    capMap K N true i r r right hd hc =
      capFEW K i (hd.step : StepR (true, i) (compOf N r) (compOf N (sh RD (up i) + r))) hd.step
        (gammaR K N r right hc) := by
  simp only [capMap, trS_self']
  erw [BHom.whiskerLeft_id, BHom.comp_id']

theorem cupMap_false_canon (i : Fin m) (r : Wt m) (right : List (WCol m))
    (hd : WOK N (sh RD (dn i) + r) right)
    (hc : WOK N (sh RD (dn i) + r) (⟨dn i, r⟩ :: ⟨up i, sh RD (dn i) + r⟩ :: right)) :
    cupMap K N false i r (sh RD (dn i) + r) right hd hc =
      cupFEW K i (hc.step : StepR (true, i) (compOf N (sh RD (dn i) + r)) (compOf N r)) hc.step
        (gammaR K N _ right hd) := by
  simp only [cupMap, trS_self']
  erw [BHom.whiskerLeft_id, BHom.id_comp']

theorem capMap_false_canon (i : Fin m) (r : Wt m) (right : List (WCol m))
    (hd : WOK N r (⟨up i, sh RD (dn i) + r⟩ :: ⟨dn i, r⟩ :: right)) (hc : WOK N r right) :
    capMap K N false i r r right hd hc =
      capEFW K i hd.step (hd.step : StepR (false, i) (compOf N r) (compOf N (sh RD (dn i) + r)))
        (gammaR K N r right hc) := by
  simp only [capMap, trS_self']
  erw [BHom.whiskerLeft_id, BHom.comp_id']

/-- A relabelling of the region between the two strands of a cap `F_i E_i → 1` (with one strand
on the left) is absorbed by the cap. -/
theorem trW_absorb_capFE (i : Fin m) (l : SLetter m) {s A X X' : Wt m} (rest : List (WCol m))
    (hX : X = X')
    (e : ((⟨l, A⟩ :: ⟨dn i, X⟩ :: ⟨up i, A⟩ :: rest : List (WCol m)) =
      ⟨l, A⟩ :: ⟨dn i, X'⟩ :: ⟨up i, A⟩ :: rest))
    (h : WOK N s (⟨l, A⟩ :: ⟨dn i, X⟩ :: ⟨up i, A⟩ :: rest))
    (h' : WOK N s (⟨l, A⟩ :: ⟨dn i, X'⟩ :: ⟨up i, A⟩ :: rest)) (hr : WOK N A rest) :
    (BHom.whiskerLeft (stepB K l (compOf N A) (compOf N s) h'.step)
      (capFEW K i (h'.tail.step : StepR (true, i) (compOf N A) (compOf N X')) h'.tail.step
        (gammaR K N A rest hr))).comp (trW s e h h') =
    BHom.whiskerLeft (stepB K l (compOf N A) (compOf N s) h.step)
      (capFEW K i (h.tail.step : StepR (true, i) (compOf N A) (compOf N X)) h.tail.step
        (gammaR K N A rest hr)) := by
  subst hX
  rw [trW_self]
  rfl

/-! ### The right rotation on canonical data -/

set_option maxHeartbeats 1000000 in
/-- **The right rotation of the upward crossing** on canonical layer data from the region `s`:
the path-model map `rotCrossRW` (KL III `eq_cyclic_cross-gen`, left-hand picture). -/
theorem canon_rotCrossR (dnScal : Fin m → Fin m → K) (i j : Fin m) (s : Wt m)
    (v : List (psig RD).Colour)
    (h : ChainW (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ :: v)
      [([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩],
         .cup ⟨up j, sh RD (up i) + s⟩, v),
       ([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩,
          ⟨up j, sh RD (up i) + s⟩],
         .cup ⟨up i, s⟩, ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([⟨dn j, sh RD (up j) + s⟩, ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩],
         .gen (.cross true j i s),
         ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([⟨dn j, sh RD (up j) + s⟩], .cap ⟨up i, sh RD (up j) + s⟩,
         ⟨up j, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v),
       ([], .cap ⟨up j, s⟩,
         ⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v)]
      (⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v))
    (ha : WOK N s (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ :: v))
    (hb : WOK N s (⟨dn i, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v)) :
    chainBD K N dnScal s _ _ _ h ha hb = rotCrossRW K i j ha.step ha.tail.step hb.step
      hb.tail.step (gammaR K N _ v ha.tail.tail) := by
  have w₁ : WOK N s (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ ::
      ⟨up j, sh RD (up i) + s⟩ :: ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v) :=
    ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.realized, rfl, hb.2.2.1, hb.2.2.2.1,
      ha.2.2.2.2⟩
  have w₂ : WOK N s (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ ::
      ⟨up j, sh RD (up i) + s⟩ :: ⟨up i, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ ::
      ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v) :=
    ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.realized, rfl, hb.2.2.1, rfl, ha.1, hb.2.1,
      hb.2.2.1, hb.2.2.2.1, ha.2.2.2.2⟩
  have w₃ : WOK N s (⟨dn j, sh RD (up j) + s⟩ :: ⟨dn i, sh RD (up j) + (sh RD (up i) + s)⟩ ::
      ⟨up i, sh RD (up j) + s⟩ :: ⟨up j, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ ::
      ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v) :=
    ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.realized, add_left_comm _ _ _, ha.2.2.1, rfl,
      ha.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ha.2.2.2.2⟩
  have w₄ : WOK N s (⟨dn j, sh RD (up j) + s⟩ :: ⟨up j, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ ::
      ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v) :=
    ⟨ha.1, ha.2.1, ha.2.2.1, rfl, ha.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ha.2.2.2.2⟩
  simp only [chainBD]
  split_ifs with h1 h2 h3 h4 h5
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, crossMap]
    rw [cupMap_true_canon, cupMap_true_canon, capMap_true_canon, capMap_true_canon]
    rw [trW_absorb_capFE i (dn j) (⟨up j, s⟩ :: ⟨dn i, sh RD (up i) + s⟩ ::
      ⟨dn j, sh RD (up j) + (sh RD (up i) + s)⟩ :: v) (add_left_comm _ _ _) _ h3]
    rfl
  all_goals first
    | exact absurd w₁ ‹_›
    | exact absurd w₂ ‹_›
    | exact absurd w₃ ‹_›
    | exact absurd w₄ ‹_›
    | exact absurd hb ‹_›

/-! ### The downward crossing -/

variable (K m) in
/-- **The scalars of the downward crossings**: `downCross j i ↦ t_{ji}^{-1} · (6.9)` for the `sl_n`
scalars `t` of `CL.Sln.slnScalars`. -/
def gammaDn (a b : Fin m) : K := (((CL.Sln.slnScalars K m).t a b)⁻¹ : Kˣ)

theorem evalB_downCross (dnScal : Fin m → Fin m → K) (j i : Fin m) (μ s : Wt m)
    (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ [dn j, dn i]).word ++ v))
    (hb : WOK N s ((ob RD μ [dn i, dn j]).word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (downCross RD j i μ)) =
      dnScal j i • locTwo (crossDn K j i ha.step ha.tail.step hb.step hb.tail.step)
        (gammaR K N _ v ha.tail.tail) := by
  rw [evalB_of]
  show chainBD K N dnScal s _ ([([], .gen (.cross false j i μ), v)] : List (LData m)) _ _ ha hb = _
  simp only [chainBD]
  split_ifs with h
  · simp only [trW_self, BHom.id_comp', BHom.comp_id']
    rfl
  · exact absurd hb h

/-- Relabelling the regions of the two boundary objects of the downward crossing. -/
theorem crossDn_relabel (j i : Fin m) {s A A' X X' B B' : Wt m} (v : List (WCol m))
    (hA : A = A') (hX : X = X') (hB : B = B')
    (e₁ : (⟨dn j, A'⟩ :: ⟨dn i, X'⟩ :: v : List (WCol m)) = ⟨dn j, A⟩ :: ⟨dn i, X⟩ :: v)
    (e₂ : (⟨dn i, B⟩ :: ⟨dn j, X⟩ :: v : List (WCol m)) = ⟨dn i, B'⟩ :: ⟨dn j, X'⟩ :: v)
    (ha : WOK N s (⟨dn j, A⟩ :: ⟨dn i, X⟩ :: v)) (ha' : WOK N s (⟨dn j, A'⟩ :: ⟨dn i, X'⟩ :: v))
    (hb : WOK N s (⟨dn i, B⟩ :: ⟨dn j, X⟩ :: v)) (hb' : WOK N s (⟨dn i, B'⟩ :: ⟨dn j, X'⟩ :: v)) :
    (trW s e₂ hb hb').comp ((locTwo (crossDn K j i ha.step ha.tail.step hb.step hb.tail.step)
        (gammaR K N X v ha.tail.tail)).comp (trW s e₁ ha' ha)) =
      locTwo (crossDn K j i ha'.step ha'.tail.step hb'.step hb'.tail.step)
        (gammaR K N X' v ha'.tail.tail) := by
  subst hA hX hB
  rw [trW_self, trW_self]
  rfl

theorem BHom.neg_comp' {A B : Type u} [CommRing A] [CommRing B] {M M' M'' : BRing A B}
    (φ : BHom M' M'') (ψ : BHom M M') : (-φ).comp ψ = -(φ.comp ψ) :=
  BHom.ext fun _ => rfl

theorem BHom.comp_neg' {A B : Type u} [CommRing A] [CommRing B] {M M' M'' : BRing A B}
    (φ : BHom M' M'') (ψ : BHom M M') : φ.comp (-ψ) = -(φ.comp ψ) :=
  BHom.ext fun x => φ.map_neg (ψ x)

theorem sh_dn' (i : Fin m) : sh RD (dn i) = -sh RD (up i) := sh_dual RD (up i)

theorem sh_up_dn_cancel (i : Fin m) (x : Wt m) : sh RD (up i) + (sh RD (dn i) + x) = x :=
  sh_cancel false i x

/-- The scalars of the two rotations agree: `t_{ij}^{-1} (±1) = t_{ji}^{-1}`. -/
theorem slnT_inv_adj {i j : Fin m} (hadj : (slCartan m).dot i j = -1) :
    -(((CL.Sln.slnScalars K m).t i j)⁻¹ : Kˣ) = ((((CL.Sln.slnScalars K m).t j i)⁻¹ : Kˣ) : K) := by
  have hadj' : (slCartan m).dot j i = -1 := by rwa [(slCartan m).symm]
  rw [CL.Sln.slnScalars_t, CL.Sln.slnScalars_t, CL.Sln.slnT_inv, CL.Sln.slnT_inv,
    CL.Sln.slnT_of_adj K hadj, CL.Sln.slnT_of_adj K hadj']
  push_cast
  ring

theorem slnT_inv_not_adj {i j : Fin m} (hadj : ¬ (slCartan m).dot i j = -1) :
    ((((CL.Sln.slnScalars K m).t i j)⁻¹ : Kˣ) : K) = ((((CL.Sln.slnScalars K m).t j i)⁻¹ : Kˣ) : K) := by
  have hadj' : ¬ (slCartan m).dot j i = -1 := by rwa [(slCartan m).symm]
  rw [CL.Sln.slnScalars_t, CL.Sln.slnScalars_t, CL.Sln.slnT_of_not_adj K hadj,
    CL.Sln.slnT_of_not_adj K hadj']

end Categorification.Flag

end
