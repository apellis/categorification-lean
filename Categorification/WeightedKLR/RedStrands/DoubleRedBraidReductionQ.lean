/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidReduction
import Categorification.WeightedKLR.RedStrands.DoubleBlackBraidClosureQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffixQ
import Categorification.WeightedKLR.RedStrands.DoubleDiagramRewriting
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidClosure
import Categorification.WeightedKLR.RedStrands.DoubleRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedUp

/-!
# Moving the closures of the red braid off the red strand

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and the proof of
Theorem 4.25. In either three-crossing braid closure, one pair of red/down
crossings can be replaced by the red/up crossings using the red cup and cap
mates. The inverse red/up crossings then cancel, leaving the closed black
crossing on a single side of red.

This is the version of `DoubleRedBraidReduction` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)

section Mates

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Pm" => addRedCapRelations RD Λ (addRedCupRelations RD Λ P)
local notation "Pu" => addRedUpRelations RD Λ k (Pm)
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pu)

section Braid

variable (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ)
  (R : List (DoubleStrand I ℓ))

local notation "eS" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "fS" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "rS" => (Sum.inr r : DoubleStrand I ℓ)
local notation "cupE" => (Move.black (ℓ := ℓ) (KL3.Diagram.Shape.cup (true, i)))
local notation "cupF" => (Move.black (ℓ := ℓ) (KL3.Diagram.Shape.cup (false, i)))
local notation "capE" => (Move.black (ℓ := ℓ) (KL3.Diagram.Shape.cap (false, i)))
local notation "capF" => (Move.black (ℓ := ℓ) (KL3.Diagram.Shape.cap (true, i)))
local notation "crossFF" => (Move.black (ℓ := ℓ) (KL3.Diagram.Shape.cross false i i))
local notation "crossER" => (Move.blackRed (true, i) r)
local notation "crossRE" => (Move.redBlack r (true, i))
local notation "crossFR" => (Move.blackRed (false, i) r)
local notation "crossRF" => (Move.redBlack r (false, i))
local notation "Dg" => signedDg RD Λ (Pd) μ (L ++ [rS] ++ R) (L ++ [rS] ++ R)

private def cappedBraidLeftLayers : List (SignedLayer I ℓ) :=
  [(L, cupE, rS :: R), (L ++ [eS, fS, rS], cupF, R),
    (L ++ [eS], crossFR, fS :: eS :: R), (L ++ [eS, rS], crossFF, eS :: R),
    (L ++ [eS], crossRF, fS :: eS :: R), (L, capE, rS :: fS :: eS :: R),
    (L ++ [rS], capF, R)]

private def cappedBraidRightLayers : List (SignedLayer I ℓ) :=
  [(L, cupE, rS :: R), (L ++ [eS, fS, rS], cupF, R),
    (L ++ [eS, fS], crossRF, eS :: R), (L ++ [eS], crossFF, rS :: eS :: R),
    (L ++ [eS, fS], crossFR, eS :: R), (L, capE, rS :: fS :: eS :: R),
    (L ++ [rS], capF, R)]

private def closedBlackRightLayers : List (SignedLayer I ℓ) :=
  [(L ++ [rS], cupE, R), (L ++ [rS, eS, fS], cupF, R), (L ++ [rS, eS], crossFF, eS :: R),
    (L ++ [rS], capE, fS :: eS :: R), (L ++ [rS], capF, R)]

private def closedBlackLeftLayers : List (SignedLayer I ℓ) :=
  [(L, cupE, rS :: R), (L ++ [eS, fS], cupF, rS :: R), (L ++ [eS], crossFF, eS :: rS :: R),
    (L, capE, fS :: eS :: rS :: R), (L, capF, rS :: R)]

private theorem signedDg_cappedBraidLeft :
    Dg (cappedBraidLeftLayers L i r R) = Dg (closedBlackRightLayers L i r R) := by
  unfold cappedBraidLeftLayers closedBlackRightLayers
  signed_step 1 with (signedDg_swap RD Λ (Pd) μ (L ++ [eS]) [] R crossFR cupF rfl rfl).symm
  signed_step 0 with (signedDg_cup_mate RD Λ Q exponents P μ L R (true, i) r)
  signed_step 4 with (signedDg_cap_mate RD Λ Q exponents P μ L (fS :: eS :: R) (false, i) r)
  signed_step 1 with (signedDg_swap RD Λ (Pd) μ L [fS] R crossRE cupF rfl rfl)
  signed_step 2 with (signedDg_swap RD Λ (Pd) μ L [] (eS :: R) crossRE crossFF rfl rfl)
  signed_step 3 with (signedDg_up_cancel_right RD Λ Q exponents P μ L (fS :: fS :: eS :: R) i r)

private theorem signedDg_cappedBraidRight :
    Dg (cappedBraidRightLayers L i r R) = Dg (closedBlackLeftLayers L i r R) := by
  unfold cappedBraidRightLayers closedBlackLeftLayers
  signed_step 1 with (signedDg_cup_mate RD Λ Q exponents P μ (L ++ [eS, fS]) R (false, i) r).symm
  signed_step 4 with (signedDg_swap RD Λ (Pd) μ L [] (eS :: R) capE crossFR rfl rfl).symm
  signed_step 5 with (signedDg_cap_mate RD Λ Q exponents P μ L R (true, i) r).symm
  signed_step 2 with (signedDg_swap RD Λ (Pd) μ (L ++ [eS]) [] R crossFF crossER rfl rfl).symm
  signed_step 3 with (signedDg_swap RD Λ (Pd) μ L [fS] R capE crossER rfl rfl).symm
  signed_step 4 with (signedDg_up_cancel_left RD Λ Q exponents P μ (L ++ [fS]) R i r)

open KLR.Diagram in
private theorem map_redBraid_layer (a b : List (I ⊕ Fin ℓ)) (g : Gen (I ⊕ Fin ℓ))
    {d : Move I ℓ} (hd : downMove g = some d) :
    let Qₐ := affineCoverQ Q exponents
    let F := downPresentedFunctor RD Λ Qₐ (Pu) μ (L ++ [eS]) (eS :: R)
    (F).map ((pres k Qₐ).diag
      (dl a g b (a := ob (a ++ g.dom ++ b)) (b := ob (a ++ g.cod ++ b)) rfl rfl)) =
      (Pd).diag (downLayerDiagram RD Λ μ (L ++ [eS]) (eS :: R) (lay a g b) hd) := by
  exact downPresentedFunctor_layer RD Λ (affineCoverQ Q exponents) (Pu) μ (L ++ [eS])
    (eS :: R) (lay a g b) (lay_valid a g b) rfl rfl hd

local notation "dL" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "P₀" => KLR.Diagram.pres k (affineCoverQ Q exponents)
local notation "F" => downPresentedFunctor RD Λ (affineCoverQ Q exponents) (Pu) μ (L ++ [eS]) (eS :: R)
local notation "close" => closeRedBraid RD Λ μ L i r R Q exponents (Pu)

private theorem closeRedBraid_left_layers :
    (close) ((P₀).diag (KLR.Diagram.braidL dL rL dL)) = Dg (cappedBraidLeftLayers L i r R) := by
  change (Pd).diag (redBraidClosureCups RD Λ μ L i r R) ≫
    (F).map ((P₀).diag (KLR.Diagram.braidL dL rL dL)) ≫
    (Pd).diag (redBraidClosureCaps RD Λ μ L i r R) = _
  rw [show (P₀).diag (KLR.Diagram.braidL dL rL dL) =
    (P₀).diag (KLR.Diagram.XL dL rL dL) ≫ (P₀).diag (KLR.Diagram.XR rL dL dL) ≫
    (P₀).diag (KLR.Diagram.XL rL dL dL) by simp only [Presentation.diag_comp],
    Functor.map_comp, Functor.map_comp]
  change (Pd).diag _ ≫ ((F).map ((P₀).diag (KLR.Diagram.dl [] (.cross dL rL) [dL] rfl rfl)) ≫
    (F).map ((P₀).diag (KLR.Diagram.dl [rL] (.cross dL dL) [] rfl rfl)) ≫
    (F).map ((P₀).diag (KLR.Diagram.dl [] (.cross rL dL) [dL] rfl rfl))) ≫ (Pd).diag _ = _
  rw [map_redBraid_layer RD Λ Q exponents P μ L i R [] [dL] (.cross dL rL) (d := crossFR) rfl,
    map_redBraid_layer RD Λ Q exponents P μ L i R [rL] [] (.cross dL dL) (d := crossFF) rfl,
    map_redBraid_layer RD Λ Q exponents P μ L i R [] [dL] (.cross rL dL) (d := crossRF) rfl]
  simp only [← Presentation.diag_comp]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pd) μ (by
    simp [signedChain, cappedBraidLeftLayers, Move.bottom, Move.top, List.append_assoc])
  simp [signedLayers, cappedBraidLeftLayers, redBraidClosureCups, redBraidClosureCaps,
    Diagram.layers_comp, Diagram.layers_cast, moveDiagram, List.append_assoc, DoubleStrand.down]

private theorem closeRedBraid_right_layers :
    (close) ((P₀).diag (KLR.Diagram.braidR dL rL dL)) = Dg (cappedBraidRightLayers L i r R) := by
  change (Pd).diag (redBraidClosureCups RD Λ μ L i r R) ≫
    (F).map ((P₀).diag (KLR.Diagram.braidR dL rL dL)) ≫
    (Pd).diag (redBraidClosureCaps RD Λ μ L i r R) = _
  rw [show (P₀).diag (KLR.Diagram.braidR dL rL dL) =
    (P₀).diag (KLR.Diagram.XR dL rL dL) ≫ (P₀).diag (KLR.Diagram.XL dL dL rL) ≫
    (P₀).diag (KLR.Diagram.XR dL dL rL) by simp only [Presentation.diag_comp],
    Functor.map_comp, Functor.map_comp]
  change (Pd).diag _ ≫ ((F).map ((P₀).diag (KLR.Diagram.dl [dL] (.cross rL dL) [] rfl rfl)) ≫
    (F).map ((P₀).diag (KLR.Diagram.dl [] (.cross dL dL) [rL] rfl rfl)) ≫
    (F).map ((P₀).diag (KLR.Diagram.dl [dL] (.cross dL rL) [] rfl rfl))) ≫ (Pd).diag _ = _
  rw [map_redBraid_layer RD Λ Q exponents P μ L i R [dL] [] (.cross rL dL) (d := crossRF) rfl,
    map_redBraid_layer RD Λ Q exponents P μ L i R [] [rL] (.cross dL dL) (d := crossFF) rfl,
    map_redBraid_layer RD Λ Q exponents P μ L i R [dL] [] (.cross dL rL) (d := crossFR) rfl]
  simp only [← Presentation.diag_comp]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pd) μ (by
    simp [signedChain, cappedBraidRightLayers, Move.bottom, Move.top, List.append_assoc])
  simp [signedLayers, cappedBraidRightLayers, redBraidClosureCups, redBraidClosureCaps,
    Diagram.layers_comp, Diagram.layers_cast, moveDiagram, List.append_assoc, DoubleStrand.down]

end Braid

end Mates

section Vanishing

open KL3.Diagram

variable [DecidableEq I] (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))

local notation "Pb" => addBlackKLRelationsQ RD Λ sc P
local notation "Pcup" => addRedCupRelations RD Λ (Pb)
local notation "Pcap" => addRedCapRelations RD Λ (Pcup)
local notation "Pup" => addRedUpRelations RD Λ k (Pcap)
local notation "Pdown" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pup)
local notation "rS" => (Sum.inr r : DoubleStrand I ℓ)
local notation "dL" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "P₀" => KLR.Diagram.pres k (affineCoverQ Q exponents)
local notation "close" => closeRedBraid RD Λ μ L i r R Q exponents (Pup)

/-- The reflected black cup–crossing–cap diagram in its physical order. -/
private def blackClosureContext (u v : List (DoubleStrand I ℓ)) (i : I) : List (SignedLayer I ℓ) :=
  (blackBraidClosureLayers i).map fun (p, g, q) => (u ++ blackWord q, .black (Sig.shape g), blackWord p ++ v)

omit [DecidableEq I] in
private theorem signedDg_blackClosure_eq_zeroQ (u v : List (DoubleStrand I ℓ))
    (h : NF.dg (CLQ.pres RD k sc) (endWeight RD Λ μ u) [] [] (blackBraidClosureLayers i) = 0) :
    signedDg RD Λ (Pdown) μ (u ++ v) (u ++ v) (blackClosureContext u v i) = 0 := by
  let η := endWeight RD Λ μ u
  have hs : SChain [] (blackBraidClosureLayers i) [] := by unfold blackBraidClosureLayers; schain
  let d := mkD RD η (blackBraidClosureLayers i) hs
  have he : (CLQ.pres RD k sc).lin (LinDiagram.of d) = (CLQ.pres RD k sc).lin 0 := by
    rw [Presentation.lin_of, Presentation.lin_zero]
    exact (NF.dg_of hs).symm.trans h
  have hh := blackContext_lin_eq_of_KL_eq_suffixQ RD Λ sc μ u v [] P (LinDiagram.of d) 0 he
  rw [blackLinear_of, map_zero] at hh
  have hh' : (Pdown).lin (LinDiagram.of (blackDiagram RD Λ μ u v d)) = (Pdown).lin 0 := by
    apply lin_eq_addRels (Pup)
    apply lin_eq_addRels (Pcap)
    apply lin_eq_addRels (Pcup)
    exact lin_eq_addRels (Pb) hh
  let e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ (u ++ v) := by simp [blackWord]
  let f := Diagram.cast (blackDiagram RD Λ μ u v d) e e
  rw [signedDg_eq_diag_of_layers RD Λ (Pdown) μ
    (by simp [signedChain, blackClosureContext, blackBraidClosureLayers, blackWord, Sig.shape,
      Move.bottom, Move.top, List.append_assoc])
    f (by
      unfold f d
      rw [Diagram.layers_cast, layers_blackDiagram_mkD]
      rfl)]
  change (Pdown).lin (LinDiagram.of f) = 0
  rw [show LinDiagram.of f = LinDiagram.cast (LinDiagram.of (blackDiagram RD Λ μ u v d)) e e
    from (LinDiagram.cast_of ..).symm, Presentation.lin_cast, hh', Presentation.lin_zero]
  simp

/-- The closure of the downward braid starting with the left crossing
vanishes when the right coroot coordinate is positive. The red cup and
cap mates move the closed crossing to that side. -/
theorem closeRedBraid_left_eq_zero_of_posQ
    (h : 1 ≤ ip RD i (endWeight RD Λ μ (L ++ [rS]))) :
    (close) ((P₀).diag (KLR.Diagram.braidL dL rL dL)) = 0 := by
  rw [closeRedBraid_left_layers, signedDg_cappedBraidLeft]
  have hzero := signedDg_blackClosure_eq_zeroQ RD Λ sc Q exponents P μ i (L ++ [rS]) R
    (CLQ.dg_blackBraidClosure_posQ RD k sc _ i h)
  simpa [blackClosureContext, blackBraidClosureLayers, closedBlackRightLayers,
    blackWord, Sig.shape, List.append_assoc] using hzero

/-- The closure of the downward braid starting with the right crossing
vanishes when the left coroot coordinate is negative. The red cup and
cap mates move the closed crossing to that side. -/
theorem closeRedBraid_right_eq_zero_of_negQ
    (h : ip RD i (endWeight RD Λ μ L) ≤ -1) :
    (close) ((P₀).diag (KLR.Diagram.braidR dL rL dL)) = 0 := by
  rw [closeRedBraid_right_layers, signedDg_cappedBraidRight]
  have hzero := signedDg_blackClosure_eq_zeroQ RD Λ sc Q exponents P μ i L (rS :: R)
    (CLQ.dg_blackBraidClosure_negQ RD k sc _ i h)
  have hword : L ++ (rS :: R) = L ++ [rS] ++ R := (List.append_assoc L [rS] R).symm
  let vanishes (w : List (DoubleStrand I ℓ)) : Prop :=
    signedDg RD Λ (Pdown) μ w w (closedBlackLeftLayers L i r R) = 0
  apply (congrArg vanishes hword).mp
  simpa [vanishes, blackClosureContext, blackBraidClosureLayers, closedBlackLeftLayers,
    blackWord, Sig.shape, up, dn] using hzero

/-- In the sign-changing chamber of Webster, arXiv:1309.3796v2, §4.5,
the capped divided difference of the downward black–red–black braid
vanishes. -/
theorem closeRedBraid_correction_eq_zeroQ
    (hneg : ip RD i (endWeight RD Λ μ L) ≤ -1)
    (hpos : 1 ≤ ip RD i (endWeight RD Λ μ (L ++ [rS]))) :
    (∑ j ∈ Finset.range (exponents r i),
      (close) (End.of ((P₀).diag (KLR.Diagram.E0 dL rL dL)) ^ j *
        End.of ((P₀).diag (KLR.Diagram.E2 dL rL dL)) ^ (exponents r i - 1 - j))) = 0 := by
  have h := closeRedBraid_sub RD Λ μ L i r R Q exponents (Pup)
  dsimp only at h
  rw [closeRedBraid_left_eq_zero_of_posQ RD Λ sc Q exponents P μ L i r R hpos,
    closeRedBraid_right_eq_zero_of_negQ RD Λ sc Q exponents P μ L i r R hneg, sub_self] at h
  exact h.symm

end Vanishing

end Categorification.Stendhal.DoubleDiagram
