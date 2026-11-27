/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoublePointedBlackClosureQ
import Categorification.WeightedKLR.RedStrands.DoublePointedRedBraidQ

/-!
# Transport of marked cups in the capped red braid

Webster, arXiv:1309.3796v2, Definition 4.24 and (4.4). Marks on the
outer upward strand commute with the moves on the other strands. When
the marked cup changes sides, use the red/up dot slide.

This is the version of `DoubleMarkedRedTransport` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))

local notation "Pr" => addRedUpSlideRelations RD Λ P
local notation "Pb" => addBlackKLRelationsQ RD Λ sc (Pr)
local notation "Pcup" => addRedCupRelations RD Λ (Pb)
local notation "Pcap" => addRedCapRelations RD Λ (Pcup)
local notation "Pup" => addRedUpRelations RD Λ k (Pcap)
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pup)

local notation "upS" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "dnS" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "rdS" => (Sum.inr r : DoubleStrand I ℓ)
local notation "cupL" => (Move.black (ℓ := ℓ) (Shape.cup (true, i)))
local notation "cupR" => (Move.black (ℓ := ℓ) (Shape.cup (false, i)))
local notation "capL" => (Move.black (ℓ := ℓ) (Shape.cap (false, i)))
local notation "capR" => (Move.black (ℓ := ℓ) (Shape.cap (true, i)))
local notation "dotU" => (Move.black (ℓ := ℓ) (Shape.dot (true, i)))
local notation "crossFF" => (Move.black (ℓ := ℓ) (Shape.cross false i i))
local notation "crossER" => (Move.blackRed (true, i) r)
local notation "crossRE" => (Move.redBlack r (true, i))
local notation "crossFR" => (Move.blackRed (false, i) r)
local notation "crossRF" => (Move.redBlack r (false, i))
local notation "start" => (L ++ [rdS] ++ R)
local notation "openLeft" => (L ++ [upS, dnS, rdS] ++ R)
local notation "openRight" => (L ++ [rdS, upS, dnS] ++ R)
local notation "Dg" => signedDg RD Λ (Pd) μ

/-- The undotted part above the marked first cup when the braid starts at the right. -/
private def rightTail : List (SignedLayer I ℓ) :=
  [(L ++ [upS, dnS, rdS], cupR, R),
    (L ++ [upS, dnS], crossRF, upS :: R), (L ++ [upS], crossFF, rdS :: upS :: R),
    (L ++ [upS, dnS], crossFR, upS :: R), (L, capL, rdS :: dnS :: upS :: R),
    (L ++ [rdS], capR, R)]

private def rightTailClosed : List (SignedLayer I ℓ) :=
  [(L ++ [upS, dnS], cupR, rdS :: R), (L ++ [upS], crossFF, upS :: rdS :: R),
    (L, capL, dnS :: upS :: rdS :: R), (L, capR, rdS :: R)]

private theorem right_tail_transportQ :
    Dg openLeft start (rightTail L i r R) = Dg openLeft start (rightTailClosed L i r R) := by
  unfold rightTail rightTailClosed
  signed_step 0 with (signedDg_cup_mate RD Λ Q exponents (Pb) μ (L ++ [upS, dnS]) R (false, i) r).symm
  signed_step 3 with (signedDg_swap RD Λ (Pd) μ L [] (upS :: R) capL crossFR rfl rfl).symm
  signed_step 4 with (signedDg_cap_mate RD Λ Q exponents (Pb) μ L R (true, i) r).symm
  signed_step 1 with (signedDg_swap RD Λ (Pd) μ (L ++ [upS]) [] R crossFF crossER rfl rfl).symm
  signed_step 2 with (signedDg_swap RD Λ (Pd) μ L [dnS] R capL crossER rfl rfl).symm
  signed_step 3 with (signedDg_up_cancel_left RD Λ Q exponents (Pb) μ (L ++ [dnS]) R i r)

private def leftTail : List (SignedLayer I ℓ) :=
  [(L, crossRE, dnS :: R), (L ++ [upS, rdS, dnS], cupR, R),
    (L ++ [upS, rdS], crossFF, upS :: R), (L ++ [upS], crossRF, dnS :: upS :: R),
    (L, capL, rdS :: dnS :: upS :: R), (L ++ [rdS], capR, R)]

private def leftTailClosed : List (SignedLayer I ℓ) :=
  [(L ++ [rdS, upS, dnS], cupR, R), (L ++ [rdS, upS], crossFF, upS :: R),
    (L ++ [rdS], capL, dnS :: upS :: R), (L ++ [rdS], capR, R)]

private theorem left_tail_transportQ :
    Dg openRight start (leftTail L i r R) = Dg openRight start (leftTailClosed L i r R) := by
  unfold leftTail leftTailClosed
  signed_step 3 with (signedDg_cap_mate RD Λ Q exponents (Pb) μ L (dnS :: upS :: R) (false, i) r)
  signed_step 0 with (signedDg_swap RD Λ (Pd) μ L [dnS] R crossRE cupR rfl rfl)
  signed_step 1 with (signedDg_swap RD Λ (Pd) μ L [] (upS :: R) crossRE crossFF rfl rfl)
  signed_step 2 with (signedDg_up_cancel_right RD Λ Q exponents (Pb) μ L (dnS :: dnS :: upS :: R) i r)


private theorem signedDg_congr_wordQ {s t s' t' : List (DoubleStrand I ℓ)}
    {a b : List (SignedLayer I ℓ)} (hs : s = s') (ht : t = t')
    (h : Dg s t a = Dg s t b) : Dg s' t' a = Dg s' t' b := by
  subst s' t'
  exact h

private theorem upDots_past_rightQ (M V : List (DoubleStrand I ℓ)) (g : Move I ℓ) (N : ℕ) :
    let a := L ++ [upS] ++ M ++ g.bottom ++ V
    let b := L ++ [upS] ++ M ++ g.top ++ V
    let move : SignedLayer I ℓ := (L ++ [upS] ++ M, g, V)
    let x : SignedLayer I ℓ := (L, dotU, M ++ g.bottom ++ V)
    let y : SignedLayer I ℓ := (L, dotU, M ++ g.top ++ V)
    Dg a b ([move] ++ List.replicate N y) = Dg a b (List.replicate N x ++ [move]) := by
  dsimp only
  apply signedDg_markedMoveQ RD Λ μ (Pd)
  · simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  · simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  · simp [signedChain]
  exact (signedDg_swap RD Λ (Pd) μ L M V dotU g rfl rfl).symm

private theorem upDots_past_redQ (V : List (DoubleStrand I ℓ)) (N : ℕ) :
    Dg (L ++ [rdS, upS] ++ V) (L ++ [upS, rdS] ++ V)
      ([(L, crossRE, V)] ++ List.replicate N (L, dotU, rdS :: V)) =
    Dg (L ++ [rdS, upS] ++ V) (L ++ [upS, rdS] ++ V)
      (List.replicate N (L ++ [rdS], dotU, V) ++ [(L, crossRE, V)]) := by
  apply signedDg_markedMoveQ RD Λ μ (Pd)
  · simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  · simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  · simp [signedChain, Move.bottom, Move.top]
  let dot := KLR.Diagram.Gen.dot i
  have he := (redUp_slide RD Λ P μ L r dot V).symm
  have h : (Pd).diag (redUpSlide RD Λ μ L r dot V true) =
      (Pd).diag (redUpSlide RD Λ μ L r dot V false) :=
    diag_eq_addRels (Pup) (diag_eq_addRels (Pcap) (diag_eq_addRels (Pcup)
      (diag_eq_addRels (Pb) (diag_eq_addRels (Pr) he))))
  have h₁ := signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (ls := [(L, crossRE, V), (L, dotU, rdS :: V)])
    (by simp [dot, upBlackWord, signedChain,
      Move.bottom, Move.top, List.append_assoc])
    (redUpSlide RD Λ μ L r dot V true) (by
      simp [redUpSlide, redThroughUpWord, upBlackWord, upBlackMoveDiagram, UpBlackMove.shape,
        dot, Diagram.layers_comp, Diagram.layers_cast, moveDiagram, signedLayers])
  have h₂ := signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (ls := [(L ++ [rdS], dotU, V), (L, crossRE, V)])
    (by simp [dot, upBlackWord, signedChain,
      Move.bottom, Move.top, List.append_assoc])
    (redUpSlide RD Λ μ L r dot V false) (by
      simp [redUpSlide, redThroughUpWord, upBlackWord, upBlackMoveDiagram, UpBlackMove.shape,
        dot, Diagram.layers_comp, Diagram.layers_cast, moveDiagram, signedLayers])
  exact signedDg_congr_wordQ RD Λ sc Q exponents P μ
    (by simp [dot, upBlackWord, List.append_assoc])
    (by simp [dot, upBlackWord, List.append_assoc]) (h₁.trans (h.trans h₂.symm))


private def firstCup : SignedLayer I ℓ := (L, cupL, rdS :: R)
private def movedFirstCup : SignedLayer I ℓ := (L ++ [rdS], cupL, R)
private def markLeft (N : ℕ) : List (SignedLayer I ℓ) :=
  List.replicate N (L, dotU, dnS :: rdS :: R)
private def markRight (N : ℕ) : List (SignedLayer I ℓ) :=
  List.replicate N (L ++ [rdS], dotU, dnS :: R)

private theorem firstCup_mark_chain (N : ℕ) :
    signedChain start ([firstCup L i r R] ++ markLeft L i r R N) openLeft := by
  have hc : signedChain start [firstCup L i r R] openLeft := by
    simp [firstCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  exact hc.append (markedReplicate_chain (by
    simp [signedChain, Move.bottom, Move.top, List.append_assoc]) N)

private theorem movedCup_mark_chain (N : ℕ) :
    signedChain start ([movedFirstCup L i r R] ++ markRight L i r R N) openRight := by
  have hc : signedChain start [movedFirstCup L i r R] openRight := by
    simp [movedFirstCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  exact hc.append (markedReplicate_chain (by
    simp [signedChain, Move.bottom, Move.top, List.append_assoc]) N)

/-- With the dots between the two cups, the right-initiated braid closes
on the left. The mark is untouched by the red/up cancellation. -/
theorem signedMarkedRightTailQ (N : ℕ) :
    Dg start start ([firstCup L i r R] ++ markLeft L i r R N ++ rightTail L i r R) =
    Dg start start ([firstCup L i r R] ++ markLeft L i r R N ++ rightTailClosed L i r R) := by
  rw [← signedDg_comp RD Λ (Pd) μ (firstCup_mark_chain L i r R N)
    (by simp [rightTail, signedChain, Move.bottom, Move.top, List.append_assoc]),
    ← signedDg_comp RD Λ (Pd) μ (firstCup_mark_chain L i r R N)
    (by simp [rightTailClosed, signedChain, Move.bottom, Move.top, List.append_assoc]),
    right_tail_transportQ]

/-- Above the cup moved to the right of red, the left-initiated braid
reduces to the black closure. -/
theorem signedMarkedLeftTailQ (N : ℕ) :
    Dg start start ([movedFirstCup L i r R] ++ markRight L i r R N ++ leftTail L i r R) =
    Dg start start ([movedFirstCup L i r R] ++ markRight L i r R N ++ leftTailClosed L i r R) := by
  rw [← signedDg_comp RD Λ (Pd) μ (movedCup_mark_chain L i r R N)
    (by simp [leftTail, signedChain, Move.bottom, Move.top, List.append_assoc]),
    ← signedDg_comp RD Λ (Pd) μ (movedCup_mark_chain L i r R N)
    (by simp [leftTailClosed, signedChain, Move.bottom, Move.top, List.append_assoc]),
    left_tail_transportQ]


local notation "dotD" => (Move.black (ℓ := ℓ) (Shape.dot (false, i)))

private theorem markedCup_cycleQ (N : ℕ) :
    Dg start openLeft ([firstCup L i r R] ++
      List.replicate N (L ++ [upS], dotD, rdS :: R)) =
    Dg start openLeft ([firstCup L i r R] ++ markLeft L i r R N) := by
  let η := endWeight RD Λ μ L
  let a : List (LayerData I) :=
    [([], .cup (dn i), [])] ++ List.replicate N ([], .dot (dn i), [up i])
  let b : List (LayerData I) :=
    [([], .cup (dn i), [])] ++ List.replicate N ([dn i], .dot (up i), [])
  have ha : SChain [] a [dn i, up i] := by unfold a; schain
  have hb : SChain [] b [dn i, up i] := by unfold b; schain
  let f := mkD RD η a ha
  let g := mkD RD η b hb
  have hKL : (CLQ.pres RD k sc).lin (LinDiagram.of f) = (CLQ.pres RD k sc).lin (LinDiagram.of g) := by
    rw [Presentation.lin_of, Presentation.lin_of, ← NF.dg_of ha, ← NF.dg_of hb]
    exact (CLQ.dg_dots_cupDn RD k sc i η N).symm
  let τ := endWeight RD Λ μ (L ++ blackWord [])
  have hτ : endWeight RD Λ μ (L ++ blackWord [dn i, up i]) = τ := by
    simp [τ, endWeight_append, endWeight_blackWord, KL3.Diagram.wt, KL3.Diagram.sh]
  have hPb : ∀ j : (CLQ.pres RD k sc).Rel, (Pb).lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel j)) = 0 :=
    fun j => (Pb).lin_rel_self (.inr j)
  have hc := congrArg (blackRectangleHomQ RD Λ sc μ L (rdS :: R) [] (Pb) hPb [dn i, up i] rfl hτ) hKL
  rw [blackRectangleHom_linQ, blackRectangleHom_linQ] at hc
  have hp : (Pd).lin (blackLinear RD Λ k μ L (rdS :: R) (LinDiagram.of f)) =
      (Pd).lin (blackLinear RD Λ k μ L (rdS :: R) (LinDiagram.of g)) :=
    lin_eq_addRels (Pup) (lin_eq_addRels (Pcap)
      (lin_eq_addRels (Pcup) (lin_eq_addRels (Pb) hc)))
  have e₀ : obj RD Λ μ (L ++ blackWord [] ++ rdS :: R) = obj RD Λ μ start := by
    simp [blackWord, List.append_assoc]
  have e₁ : obj RD Λ μ (L ++ blackWord [dn i, up i] ++ rdS :: R) = obj RD Λ μ openLeft := by
    simp [blackWord, List.append_assoc]
  let f' := Diagram.cast (blackDiagram RD Λ μ L (rdS :: R) f) e₀ e₁
  let g' := Diagram.cast (blackDiagram RD Λ μ L (rdS :: R) g) e₀ e₁
  have hfirst : signedChain start [firstCup L i r R] openLeft := by
    simp [firstCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hmark : signedChain openLeft
      (List.replicate N (L ++ [upS], dotD, rdS :: R)) openLeft :=
    markedReplicate_chain (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) N
  rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ (hfirst.append hmark) f' (by
      dsimp only [f', f]
      rw [Diagram.layers_cast, layers_blackDiagram_mkD]
      simp [signedLayers, a, firstCup, Sig.shape, blackWord]),
    signedDg_eq_diag_of_layers RD Λ (Pd) μ (firstCup_mark_chain L i r R N) g' (by
      dsimp only [g', g]
      rw [Diagram.layers_cast, layers_blackDiagram_mkD]
      simp [signedLayers, b, markLeft, firstCup, Sig.shape, blackWord])]
  change (Pd).lin (LinDiagram.of f') = (Pd).lin (LinDiagram.of g')
  dsimp only [f', g']
  rw [← LinDiagram.cast_of, ← LinDiagram.cast_of, Presentation.lin_cast, Presentation.lin_cast]
  exact congrArg ((Pd).castHom e₀ e₁) (by simpa only [blackLinear_of] using hp)


private theorem rightMarkedTail_eq_blackQ (N : ℕ) :
    Dg start start ([firstCup L i r R] ++ markLeft L i r R N ++ rightTailClosed L i r R) =
    Dg start start (signedPointedBlackClosureLayers L (rdS :: R) i N) := by
  let y := L ++ [upS, dnS, dnS, upS] ++ (rdS :: R)
  let cup : SignedLayer I ℓ := (L ++ [upS, dnS], cupR, (rdS :: R))
  let dot : SignedLayer I ℓ := (L, dotU, dnS :: dnS :: upS :: (rdS :: R))
  let caps : List (SignedLayer I ℓ) :=
    [(L ++ [upS], crossFF, upS :: (rdS :: R)),
     (L, capL, dnS :: upS :: (rdS :: R)), (L, capR, (rdS :: R))]
  have h : Dg openLeft y (markLeft L i r R N ++ [cup]) =
      Dg openLeft y ([cup] ++ List.replicate N dot) := by
    have h₀ := (upDots_past_rightQ RD Λ sc Q exponents P μ L i [dnS] (rdS :: R) cupR N).symm
    have h₁ := signedDg_congr_wordQ RD Λ sc Q exponents P μ
      (s' := openLeft) (t' := y)
      (by simp [Move.bottom, List.append_assoc])
      (by simp [y, Move.top, List.append_assoc]) h₀
    simpa [cup, dot, markLeft, Move.bottom, Move.top, List.append_assoc] using h₁
  have hc : signedChain openLeft [cup] y := by
    simp [cup, y, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hbefore : signedChain openLeft (markLeft L i r R N) openLeft :=
    markedReplicate_chain (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hafter : signedChain y (List.replicate N dot) y :=
    markedReplicate_chain (by simp [y, dot, signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hh := signedDg_replace RD Λ (Pd) μ [firstCup L i r R] _ _ caps
    (s := start) (t := start)
    (by simp [firstCup, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [y, caps, signedChain, Move.bottom, Move.top, List.append_assoc])
    (hbefore.append hc) (hc.append hafter) h
  simpa [rightTailClosed, signedPointedBlackClosureLayers, pointedBlackClosureLayers,
    blackWord, Sig.shape, firstCup, markLeft, List.append_assoc, List.map_replicate,
    cup, caps, dot] using hh

private theorem leftMarkedTail_eq_blackQ (N : ℕ) :
    Dg start start ([movedFirstCup L i r R] ++ markRight L i r R N ++ leftTailClosed L i r R) =
    Dg start start (signedPointedBlackClosureLayers (L ++ [rdS]) R i N) := by

  let y := (L ++ [rdS]) ++ [upS, dnS, dnS, upS] ++ R
  let cup : SignedLayer I ℓ := ((L ++ [rdS]) ++ [upS, dnS], cupR, R)
  let dot : SignedLayer I ℓ := ((L ++ [rdS]), dotU, dnS :: dnS :: upS :: R)
  let caps : List (SignedLayer I ℓ) :=
    [((L ++ [rdS]) ++ [upS], crossFF, upS :: R),
     ((L ++ [rdS]), capL, dnS :: upS :: R), ((L ++ [rdS]), capR, R)]
  have h : Dg openRight y (markRight L i r R N ++ [cup]) =
      Dg openRight y ([cup] ++ List.replicate N dot) := by
    have h₀ := (upDots_past_rightQ RD Λ sc Q exponents P μ (L ++ [rdS]) i [dnS] R cupR N).symm
    have h₁ := signedDg_congr_wordQ RD Λ sc Q exponents P μ
      (s' := openRight) (t' := y)
      (by simp [Move.bottom, List.append_assoc])
      (by simp [y, Move.top, List.append_assoc]) h₀
    simpa [cup, dot, markRight, Move.bottom, Move.top, List.append_assoc] using h₁
  have hc : signedChain openRight [cup] y := by
    simp [cup, y, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hbefore : signedChain openRight (markRight L i r R N) openRight :=
    markedReplicate_chain (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hafter : signedChain y (List.replicate N dot) y :=
    markedReplicate_chain (by simp [y, dot, signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hh := signedDg_replace RD Λ (Pd) μ [movedFirstCup L i r R] _ _ caps
    (s := start) (t := start)
    (by simp [movedFirstCup, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [y, caps, signedChain, Move.bottom, Move.top, List.append_assoc])
    (hbefore.append hc) (hc.append hafter) h
  simpa [leftTailClosed, signedPointedBlackClosureLayers, pointedBlackClosureLayers,
    blackWord, Sig.shape, movedFirstCup, markRight, List.append_assoc, List.map_replicate,
    cup, caps, dot] using hh


local notation "sourceA" => (L ++ [upS] ++ [dnS, rdS, dnS] ++ (upS :: R))
local notation "Qₐ" => affineCoverQ Q exponents
local notation "P₀" => KLR.Diagram.pres k Qₐ
local notation "F" => downPresentedFunctor RD Λ Qₐ (Pup) μ (L ++ [upS]) (upS :: R)
local notation "dLabel" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "rLabel" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "sourceObj" => (KLR.Diagram.ob [dLabel, rLabel, dLabel])

private def secondCup : SignedLayer I ℓ := (L ++ [upS, dnS, rdS], cupR, R)
private def closedCaps : List (SignedLayer I ℓ) :=
  [(L, capL, rdS :: dnS :: upS :: R), (L ++ [rdS], capR, R)]

private def braidLayers (left : Bool) : List (SignedLayer I ℓ) :=
  if left then
    [(L ++ [upS], crossFR, dnS :: upS :: R), (L ++ [upS, rdS], crossFF, upS :: R),
      (L ++ [upS], crossRF, dnS :: upS :: R)]
  else
    [(L ++ [upS, dnS], crossRF, upS :: R), (L ++ [upS], crossFF, rdS :: upS :: R),
      (L ++ [upS, dnS], crossFR, upS :: R)]

private abbrev braidSource (left : Bool) : End sourceObj :=
  if left then KLR.Diagram.braidL dLabel rLabel dLabel else KLR.Diagram.braidR dLabel rLabel dLabel

open KLR.Diagram in
private theorem markedMap_layerQ (a b : List (I ⊕ Fin ℓ)) (g : Gen (I ⊕ Fin ℓ))
    {d : Move I ℓ} (hd : downMove g = some d) :
    (F).map ((P₀).diag
      (dl a g b (a := ob (a ++ g.dom ++ b)) (b := ob (a ++ g.cod ++ b)) rfl rfl)) =
      (Pd).diag (downLayerDiagram RD Λ μ (L ++ [upS]) (upS :: R) (lay a g b) hd) :=
  downPresentedFunctor_layer RD Λ Qₐ (Pup) μ (L ++ [upS])
    (upS :: R) (lay a g b) (lay_valid a g b) rfl rfl hd

open KLR.Diagram in
private theorem markedMap_braidQ (left : Bool) :
    (F).map ((P₀).diag (braidSource i r left)) =
      Dg sourceA sourceA (braidLayers L i r R left) := by
  cases left
  · change (F).map ((P₀).diag (XR dLabel rLabel dLabel ≫ XL dLabel dLabel rLabel ≫
      XR dLabel dLabel rLabel)) = _
    rw [Presentation.diag_comp, Presentation.diag_comp, Functor.map_comp, Functor.map_comp]
    change (F).map ((P₀).diag (dl [dLabel] (.cross rLabel dLabel) [] rfl rfl)) ≫
      (F).map ((P₀).diag (dl [] (.cross dLabel dLabel) [rLabel] rfl rfl)) ≫
      (F).map ((P₀).diag (dl [dLabel] (.cross dLabel rLabel) [] rfl rfl)) = _
    rw [markedMap_layerQ RD Λ sc Q exponents P μ L i R [dLabel] [] (.cross rLabel dLabel) (d := crossRF) rfl,
      markedMap_layerQ RD Λ sc Q exponents P μ L i R [] [rLabel] (.cross dLabel dLabel) (d := crossFF) rfl,
      markedMap_layerQ RD Λ sc Q exponents P μ L i R [dLabel] [] (.cross dLabel rLabel) (d := crossFR) rfl]
    simp only [← Presentation.diag_comp]
    symm
    apply signedDg_eq_diag_of_layers RD Λ (Pd) μ
      (by simp [braidLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    simp [signedLayers, braidLayers, Diagram.layers_comp, downLayerDiagram, moveDiagram, List.append_assoc,
      DoubleStrand.down, KLR.Diagram.lay]
  · change (F).map ((P₀).diag (XL dLabel rLabel dLabel ≫ XR rLabel dLabel dLabel ≫
      XL rLabel dLabel dLabel)) = _
    rw [Presentation.diag_comp, Presentation.diag_comp, Functor.map_comp, Functor.map_comp]
    change (F).map ((P₀).diag (dl [] (.cross dLabel rLabel) [dLabel] rfl rfl)) ≫
      (F).map ((P₀).diag (dl [rLabel] (.cross dLabel dLabel) [] rfl rfl)) ≫
      (F).map ((P₀).diag (dl [] (.cross rLabel dLabel) [dLabel] rfl rfl)) = _
    rw [markedMap_layerQ RD Λ sc Q exponents P μ L i R [] [dLabel] (.cross dLabel rLabel) (d := crossFR) rfl,
      markedMap_layerQ RD Λ sc Q exponents P μ L i R [rLabel] [] (.cross dLabel dLabel) (d := crossFF) rfl,
      markedMap_layerQ RD Λ sc Q exponents P μ L i R [] [dLabel] (.cross rLabel dLabel) (d := crossRF) rfl]
    simp only [← Presentation.diag_comp]
    symm
    apply signedDg_eq_diag_of_layers RD Λ (Pd) μ
      (by simp [braidLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    simp [signedLayers, braidLayers, Diagram.layers_comp, downLayerDiagram, moveDiagram, List.append_assoc,
      DoubleStrand.down, KLR.Diagram.lay]

private theorem markedPointedBraid_layersQ (left : Bool) (N : ℕ) :
    closePointedRedBraidQ RD Λ sc μ L i r R Q exponents (Pr) N ((P₀).diag (braidSource i r left)) =
    Dg start start ([firstCup L i r R, secondCup L i r R] ++
      downRedBraidDotLayers L i r R N 0 ++ braidLayers L i r R left ++ closedCaps L i r R) := by
  change (Pd).diag (redBraidClosureCups RD Λ μ L i r R) ≫
    (F).map ((End.of ((P₀).diag (KLR.Diagram.E0 dLabel rLabel dLabel)) ^ N : End _) ≫
      (P₀).diag (braidSource i r left)) ≫ (Pd).diag (redBraidClosureCaps RD Λ μ L i r R) = _
  rw [Functor.map_comp, markedMap_braidQ]
  have hd := downRedBraidDotMonomial_layersQ RD Λ μ L i r R Q exponents (Pup) N 0
  rw [pow_zero, mul_one] at hd
  rw [hd]
  have hpre : signedChain start [firstCup L i r R, secondCup L i r R] sourceA := by
    simp [firstCup, secondCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hpost : signedChain sourceA (closedCaps L i r R) start := by
    simp [closedCaps, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hdots : signedChain sourceA (downRedBraidDotLayers L i r R N 0) sourceA :=
    downRedBraidDotLayers_chainQ L i r R N 0
  have hbraid : signedChain sourceA (braidLayers L i r R left) sourceA := by
    cases left <;> simp [braidLayers, signedChain, Move.bottom, Move.top, List.append_assoc]
  rw [← signedDg_eq_diag_of_layers RD Λ (Pd) μ hpre (redBraidClosureCups RD Λ μ L i r R)
      (by simp [signedLayers, firstCup, secondCup, redBraidClosureCups, Diagram.layers_comp,
        Diagram.layers_cast, moveDiagram]),
    ← signedDg_eq_diag_of_layers RD Λ (Pd) μ hpost (redBraidClosureCaps RD Λ μ L i r R)
      (by simp [signedLayers, closedCaps, redBraidClosureCaps, Diagram.layers_comp,
        Diagram.layers_cast, moveDiagram]),
    ← Category.assoc, ← Category.assoc,
    signedDg_comp RD Λ (Pd) μ hpre hdots, signedDg_comp RD Λ (Pd) μ (hpre.append hdots) hbraid,
    signedDg_comp RD Λ (Pd) μ ((hpre.append hdots).append hbraid) hpost]


private theorem dnDots_past_secondCupQ (N : ℕ) :
    Dg openLeft sourceA ([secondCup L i r R] ++
      List.replicate N (L ++ [upS], dotD, rdS :: dnS :: upS :: R)) =
    Dg openLeft sourceA (List.replicate N (L ++ [upS], dotD, rdS :: R) ++ [secondCup L i r R]) := by
  apply signedDg_markedMoveQ RD Λ μ (Pd)
  · simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  · simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  · simp [secondCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  simpa [secondCup, Move.bottom, Move.top, List.append_assoc] using
    (signedDg_swap RD Λ (Pd) μ (L ++ [upS]) [rdS] R dotD cupR
      (s := openLeft) (t := sourceA) (by simp [Move.bottom, List.append_assoc])
      (by simp [Move.top, List.append_assoc])).symm

private theorem markedPointedBraid_markQ (left : Bool) (N : ℕ) :
    closePointedRedBraidQ RD Λ sc μ L i r R Q exponents (Pr) N ((P₀).diag (braidSource i r left)) =
    Dg start start ([firstCup L i r R] ++ markLeft L i r R N ++
      [secondCup L i r R] ++ braidLayers L i r R left ++ closedCaps L i r R) := by
  rw [markedPointedBraid_layersQ]
  let downL : SignedLayer I ℓ := (L ++ [upS], dotD, rdS :: R)
  let downBoth : SignedLayer I ℓ := (L ++ [upS], dotD, rdS :: dnS :: upS :: R)
  have hLayer : downRedBraidDotLayers L i r R N 0 = List.replicate N downBoth := rfl
  rw [hLayer]
  have h1 : signedChain start [firstCup L i r R] openLeft := by
    simp [firstCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  have h2 : signedChain openLeft [secondCup L i r R] sourceA := by
    simp [secondCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  have h3 : signedChain sourceA (braidLayers L i r R left ++ closedCaps L i r R) start := by
    cases left <;> simp [braidLayers, closedCaps, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hdownL : signedChain openLeft (List.replicate N downL) openLeft :=
    markedReplicate_chain (by simp [downL, signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hdownBoth : signedChain sourceA (List.replicate N downBoth) sourceA :=
    markedReplicate_chain (by simp [downBoth, signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hswap := signedDg_replace RD Λ (Pd) μ _ _ _ _ h1 h3
    (h2.append hdownBoth) (hdownL.append h2) (dnDots_past_secondCupQ RD Λ sc Q exponents P μ L i r R N)
  have hcycle := signedDg_replace RD Λ (Pd) μ [] _ _
    ([secondCup L i r R] ++ (braidLayers L i r R left ++ closedCaps L i r R)) rfl
    (h2.append h3) (h1.append hdownL) (firstCup_mark_chain L i r R N)
    (markedCup_cycleQ RD Λ sc Q exponents P μ L i r R N)
  exact (by simpa [List.append_assoc] using hswap :
    Dg _ _ _ = Dg start start ([firstCup L i r R] ++ (List.replicate N downL ++
      ([secondCup L i r R] ++ (braidLayers L i r R left ++ closedCaps L i r R))))).trans
    (by simpa [List.append_assoc] using hcycle)

variable [DecidableEq I]

/-- The pointed right-initiated braid closes entirely on the negative side. -/
theorem closePointedRedBraid_right_eq_zeroQ (N : ℕ)
    (hneg : (N : ℤ) + 1 ≤ -ip RD i (endWeight RD Λ μ L)) :
    closePointedRedBraidQ RD Λ sc μ L i r R Q exponents (Pr) N
      ((P₀).diag (KLR.Diagram.braidR dLabel rLabel dLabel)) = 0 := by
  change closePointedRedBraidQ RD Λ sc μ L i r R Q exponents (Pr) N
      ((P₀).diag (braidSource i r false)) = 0
  rw [markedPointedBraid_markQ]
  have h : [secondCup L i r R] ++ braidLayers L i r R false ++ closedCaps L i r R = rightTail L i r R := rfl
  simp only [List.append_assoc, h]
  rw [← List.append_assoc, signedMarkedRightTailQ, rightMarkedTail_eq_blackQ]
  have hz := signedPointedBlackClosure_eq_zeroQ RD Λ sc μ i Q exponents (Pr) L (rdS :: R) N
    (CLQ.dg_pointedBlackClosure_negQ RD k sc _ i N hneg)
  have hword : L ++ rdS :: R = start := by simp [List.append_assoc]
  revert hz
  generalize L ++ rdS :: R = s at hword
  subst s
  exact id


omit [DecidableEq I] in
private theorem markedLeftBraid_after_cupQ (N : ℕ) :
    Dg start start ([firstCup L i r R] ++ markLeft L i r R N ++
      [secondCup L i r R] ++ braidLayers L i r R true ++ closedCaps L i r R) =
    Dg start start ([movedFirstCup L i r R] ++ markRight L i r R N ++ leftTail L i r R) := by
  let a := openLeft
  let b := L ++ [upS, rdS, dnS] ++ R
  let c := L ++ [upS, rdS, dnS, dnS, upS] ++ R
  let swapFirst : SignedLayer I ℓ := (L ++ [upS], crossFR, R)
  let secondCup' : SignedLayer I ℓ := (L ++ [upS, rdS, dnS], cupR, R)
  let dotB : SignedLayer I ℓ := (L, dotU, rdS :: dnS :: R)
  let rest : List (SignedLayer I ℓ) :=
    [(L ++ [upS, rdS], crossFF, upS :: R), (L ++ [upS], crossRF, dnS :: upS :: R)] ++
      closedCaps L i r R
  have hrest : signedChain c rest start := by
    simp [c, rest, closedCaps, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hcup' : signedChain b [secondCup'] c := by
    simp [b, c, secondCup', signedChain, Move.bottom, Move.top, List.append_assoc]
  have hdotB : signedChain b (List.replicate N dotB) b :=
    markedReplicate_chain (by simp [b, dotB, signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hdotA : signedChain a (markLeft L i r R N) a :=
    markedReplicate_chain (by simp [a, signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hd := signedDg_swap RD Λ (Pd) μ (L ++ [upS]) [] R crossFR cupR
    (s := a) (t := c) (by simp [a, Move.bottom, List.append_assoc])
    (by simp [c, Move.top, List.append_assoc])
  have hswap := signedDg_replace RD Λ (Pd) μ
    ([firstCup L i r R] ++ markLeft L i r R N) _ _ rest
    (firstCup_mark_chain L i r R N) hrest
    (by simp [c, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [c, signedChain, Move.bottom, Move.top, List.append_assoc]) hd.symm
  have hmove : Dg a b (markLeft L i r R N ++ [swapFirst]) =
      Dg a b ([swapFirst] ++ List.replicate N dotB) := by
    have hh := (upDots_past_rightQ RD Λ sc Q exponents P μ L i [] R crossFR N).symm
    have hh' := signedDg_congr_wordQ RD Λ sc Q exponents P μ (s' := a) (t' := b)
      (by simp [a, Move.bottom, List.append_assoc])
      (by simp [b, Move.top, List.append_assoc]) hh
    simpa [markLeft, swapFirst, dotB, Move.bottom, Move.top] using hh'
  have hcross : signedChain a [swapFirst] b := by
    simp [a, b, swapFirst, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hfirst : signedChain start [firstCup L i r R] a := by
    simp [a, firstCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hkeep := signedDg_replace RD Λ (Pd) μ [firstCup L i r R] _ _ ([secondCup'] ++ rest)
    hfirst (hcup'.append hrest) (hdotA.append hcross) (hcross.append hdotB) hmove
  have hmate0 : Dg start b [firstCup L i r R, swapFirst] =
      Dg start b [movedFirstCup L i r R, (L, crossRE, dnS :: R)] :=
    signedDg_cup_mate RD Λ Q exponents (Pb) μ L R (true, i) r
  have hmate := signedDg_replace RD Λ (Pd) μ [] _ _
    (List.replicate N dotB ++ ([secondCup'] ++ rest)) rfl
    (hdotB.append (hcup'.append hrest))
    (by simp [b, firstCup, swapFirst, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [b, movedFirstCup, signedChain, Move.bottom, Move.top, List.append_assoc]) hmate0
  have hrightCup : signedChain start [movedFirstCup L i r R] openRight := by
    simp [movedFirstCup, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hred : signedChain openRight [(L, crossRE, dnS :: R)] b := by
    simp [b, signedChain, Move.bottom, Move.top, List.append_assoc]
  have hrightDots : signedChain openRight (markRight L i r R N) openRight :=
    markedReplicate_chain (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) N
  have hslide : Dg openRight b ([(L, crossRE, dnS :: R)] ++ List.replicate N dotB) =
      Dg openRight b (markRight L i r R N ++ [(L, crossRE, dnS :: R)]) := by
    exact signedDg_congr_wordQ RD Λ sc Q exponents P μ
      (by simp [List.append_assoc]) (by simp [b, List.append_assoc])
      (upDots_past_redQ RD Λ sc Q exponents P μ L i r (dnS :: R) N)
  have hmarked := signedDg_replace RD Λ (Pd) μ [movedFirstCup L i r R] _ _ ([secondCup'] ++ rest)
    hrightCup (hcup'.append hrest) (hred.append hdotB) (hrightDots.append hred)
    hslide
  exact (by simpa [a, c, swapFirst, secondCup', secondCup, rest, braidLayers, Move.bottom, Move.top,
    List.append_assoc] using hswap :
    Dg start start _ = Dg start start ([firstCup L i r R] ++
      (markLeft L i r R N ++ ([swapFirst] ++ ([secondCup'] ++ rest))))).trans
    ((by simpa [List.append_assoc] using hkeep :
      Dg start start _ = Dg start start ([firstCup L i r R] ++
        ([swapFirst] ++ (List.replicate N dotB ++ ([secondCup'] ++ rest))))).trans
    ((by simpa [firstCup, movedFirstCup, swapFirst, List.append_assoc] using hmate :
      Dg start start _ = Dg start start ([movedFirstCup L i r R] ++
        ([(L, crossRE, dnS :: R)] ++ (List.replicate N dotB ++ ([secondCup'] ++ rest))))).trans
    (by simpa [leftTail, rest, closedCaps, secondCup', markRight, dotB, List.append_assoc] using hmarked)))

/-- The pointed left-initiated braid closes entirely on the positive side. -/
theorem closePointedRedBraid_left_eq_zeroQ (N : ℕ)
    (hpos : 1 ≤ ip RD i (endWeight RD Λ μ (L ++ [rdS]))) :
    closePointedRedBraidQ RD Λ sc μ L i r R Q exponents (Pr) N
      ((P₀).diag (KLR.Diagram.braidL dLabel rLabel dLabel)) = 0 := by
  change closePointedRedBraidQ RD Λ sc μ L i r R Q exponents (Pr) N
      ((P₀).diag (braidSource i r true)) = 0
  rw [markedPointedBraid_markQ, markedLeftBraid_after_cupQ, signedMarkedLeftTailQ, leftMarkedTail_eq_blackQ]
  have hz := signedPointedBlackClosure_eq_zeroQ RD Λ sc μ i Q exponents (Pr) (L ++ [rdS]) R N
    (CLQ.dg_pointedBlackClosure_posQ RD k sc _ i N hpos)
  exact hz

local notation "nL" => (ip RD i (endWeight RD Λ μ L))
local notation "nR" => (ip RD i (endWeight RD Λ μ (L ++ [rdS])))

/-- The higher mixed bubble coefficient vanishes when both closed
pointed braid branches have vanishing black curls. -/
theorem pointedRedBraid_convolution_zeroQ (N : ℕ) (hN : (N : ℤ) + 1 ≤ -nL)
    (hpos : 1 ≤ nR) (hδ : nR = nL + (exponents r i : ℤ)) :
    sconv
      (fun a => End.of ((Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R ((-nL - 1).toNat + a))))
      (fun b => End.of ((Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R ((nR - 1).toNat + b)))) (N + 1) = 0 := by
  have h := pointedRedBraid_sub_eq_convolutionQ RD Λ sc μ L i r R Q exponents (Pr)
    N (by omega) (by omega) hpos hδ
  rw [closePointedRedBraid_left_eq_zeroQ RD Λ sc Q exponents P μ L i r R N hpos,
    closePointedRedBraid_right_eq_zeroQ RD Λ sc Q exponents P μ L i r R N hN, sub_self] at h
  exact h.symm

end Categorification.Stendhal.DoubleDiagram
