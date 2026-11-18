/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidReduction
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.WeightedKLR.RedStrands.DoubleClockwiseRedBubble
import Categorification.WeightedKLR.RedStrands.DoubleRedBubble

/-!
# Bubbles in the closed black–red–black braid

Webster, arXiv:1309.3796v2, Definitions 4.5 and 4.24. In the closure
of the divided difference, the two blocks of dots lie on disjoint
black loops. Interchange separates the loops. The clockwise bubble
is put in its standard dot convention by KL III, arXiv:0807.3250v1,
Definition 3.1(i), equation (3.3).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (μ : X)

section Interchange

variable (A : Presentation.{w, max u v} (signature RD Λ) k)

private theorem replicate_chain {s : List (DoubleStrand I ℓ)} {g : SignedLayer I ℓ}
    (hg : signedChain s [g] s) (n : ℕ) : signedChain s (List.replicate n g) s := by
  induction n with
  | zero => rfl
  | succ n ih => exact hg.append ih

private theorem signedDg_power {s : List (DoubleStrand I ℓ)} {g : SignedLayer I ℓ}
    (hg : signedChain s [g] s) (n : ℕ) :
    (End.of (signedDg RD Λ A μ s s [g]) ^ n : End (A.obj (obj RD Λ μ s))) =
      signedDg RD Λ A μ s s (List.replicate n g) := by
  induction n with
  | zero => exact (signedDg_nil RD Λ A μ s).symm
  | succ n ih =>
    rw [pow_succ, End.mul_def]
    change signedDg RD Λ A μ s s [g] ≫ (End.of (signedDg RD Λ A μ s s [g]) ^ n : End _) = _
    rw [ih, signedDg_comp RD Λ A μ hg (replicate_chain hg n)]
    rfl

private theorem signedDg_swap_rep (a m b : List (DoubleStrand I ℓ))
    (g h : Move I ℓ) (hh : h.bottom = h.top) (n : ℕ) :
    signedDg RD Λ A μ (a ++ g.bottom ++ m ++ h.bottom ++ b)
        (a ++ g.top ++ m ++ h.top ++ b)
        (List.replicate n (a ++ g.bottom ++ m, h, b) ++ [(a, g, m ++ h.top ++ b)]) =
      signedDg RD Λ A μ (a ++ g.bottom ++ m ++ h.bottom ++ b)
        (a ++ g.top ++ m ++ h.top ++ b)
        ([(a, g, m ++ h.bottom ++ b)] ++ List.replicate n (a ++ g.top ++ m, h, b)) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    let x : SignedLayer I ℓ := (a ++ g.bottom ++ m, h, b)
    let y : SignedLayer I ℓ := (a ++ g.top ++ m, h, b)
    have hpre : signedChain (a ++ g.bottom ++ m ++ h.bottom ++ b) [x]
        (a ++ g.bottom ++ m ++ h.bottom ++ b) := by simp [x, signedChain, hh]
    have hpost : signedChain (a ++ g.top ++ m ++ h.top ++ b) (List.replicate n y)
        (a ++ g.top ++ m ++ h.top ++ b) := replicate_chain (by simp [y, signedChain, hh]) _
    simp only [List.replicate_succ, List.cons_append]
    calc
      _ = signedDg RD Λ A μ _ _
          ([x] ++ ([(a, g, m ++ h.bottom ++ b)] ++ List.replicate n y)) :=
        by
          simpa only [x, y, List.append_nil, List.singleton_append] using signedDg_replace RD Λ A μ [x] _ _ [] hpre rfl
            ((replicate_chain hpre n).append (by simp [signedChain, hh, List.append_assoc]))
            ((by simp [signedChain, hh, List.append_assoc] : signedChain _ [_] _).append hpost) ih
      _ = _ := by
        have hs := (signedDg_swap RD Λ A μ a m b g h rfl rfl).symm
        have he := signedDg_replace RD Λ A μ [] _ _ (List.replicate n y) rfl hpost
          (by simp [signedChain, hh, List.append_assoc])
          (by simp [signedChain, hh, List.append_assoc]) hs
        simpa [x, y, hh, List.append_assoc] using he

private theorem signedDg_swap_rep' (a m b : List (DoubleStrand I ℓ))
    (g h : Move I ℓ) (hh : h.bottom = h.top) (n : ℕ) :
    signedDg RD Λ A μ (a ++ h.bottom ++ m ++ g.bottom ++ b)
        (a ++ h.top ++ m ++ g.top ++ b)
        (List.replicate n (a, h, m ++ g.bottom ++ b) ++ [(a ++ h.top ++ m, g, b)]) =
      signedDg RD Λ A μ (a ++ h.bottom ++ m ++ g.bottom ++ b)
        (a ++ h.top ++ m ++ g.top ++ b)
        ([(a ++ h.bottom ++ m, g, b)] ++ List.replicate n (a, h, m ++ g.top ++ b)) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    let x : SignedLayer I ℓ := (a, h, m ++ g.bottom ++ b)
    let y : SignedLayer I ℓ := (a, h, m ++ g.top ++ b)
    have hpre : signedChain (a ++ h.bottom ++ m ++ g.bottom ++ b) [x]
        (a ++ h.bottom ++ m ++ g.bottom ++ b) := by simp [x, signedChain, hh, List.append_assoc]
    have hpost : signedChain (a ++ h.top ++ m ++ g.top ++ b) (List.replicate n y)
        (a ++ h.top ++ m ++ g.top ++ b) :=
      replicate_chain (by simp [y, signedChain, hh, List.append_assoc]) _
    simp only [List.replicate_succ, List.cons_append]
    calc
      _ = signedDg RD Λ A μ _ _
          ([x] ++ ([(a ++ h.bottom ++ m, g, b)] ++ List.replicate n y)) :=
        by
          simpa only [x, y, List.append_nil, List.singleton_append] using signedDg_replace RD Λ A μ [x] _ _ [] hpre rfl
            ((replicate_chain hpre n).append (by simp [signedChain, hh, List.append_assoc]))
            ((by simp [signedChain, hh, List.append_assoc] : signedChain _ [_] _).append hpost) ih
      _ = _ := by
        have hs := signedDg_swap RD Λ A μ a m b h g rfl rfl
        have he := signedDg_replace RD Λ A μ [] _ _ (List.replicate n y) rfl hpost
          (by simp [signedChain, hh, List.append_assoc])
          (by simp [signedChain, hh, List.append_assoc]) hs
        simpa [x, y, hh, List.append_assoc] using he

end Interchange

section Loops

variable (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))

local notation "uS" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "dS" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "rS" => (Sum.inr r : DoubleStrand I ℓ)
local notation "cupL" => (Move.black (ℓ := ℓ) (Shape.cup (true, i)))
local notation "cupR" => (Move.black (ℓ := ℓ) (Shape.cup (false, i)))
local notation "capL" => (Move.black (ℓ := ℓ) (Shape.cap (false, i)))
local notation "capR" => (Move.black (ℓ := ℓ) (Shape.cap (true, i)))
local notation "dotD" => (Move.black (ℓ := ℓ) (Shape.dot (false, i)))

local notation "initial" => (L ++ [rS] ++ R)
local notation "openedL" => (L ++ [uS, dS, rS] ++ R)
local notation "openedR" => (L ++ [rS, dS, uS] ++ R)
local notation "openedBoth" => ((L ++ [uS]) ++ [dS, rS, dS] ++ (uS :: R))

private def leftCup (w : List (DoubleStrand I ℓ)) : SignedLayer I ℓ :=
  (L, cupL, rS :: w ++ R)

private def leftDot (w : List (DoubleStrand I ℓ)) : SignedLayer I ℓ :=
  (L ++ [uS], dotD, rS :: w ++ R)

private def leftCap (w : List (DoubleStrand I ℓ)) : SignedLayer I ℓ :=
  (L, capL, rS :: w ++ R)

private def rightCup (w : List (DoubleStrand I ℓ)) : SignedLayer I ℓ :=
  (L ++ w ++ [rS], cupR, R)

private def rightDot (w : List (DoubleStrand I ℓ)) : SignedLayer I ℓ :=
  (L ++ w ++ [rS], dotD, uS :: R)

private def rightCap (w : List (DoubleStrand I ℓ)) : SignedLayer I ℓ :=
  (L ++ w ++ [rS], capR, R)

local notation "lc" => leftCup L i r R
local notation "ld" => leftDot L i r R
local notation "la" => leftCap L i r R
local notation "rc" => rightCup L i r R
local notation "rdot" => rightDot L i r R
local notation "ra" => rightCap L i r R
local notation "lw" => [uS, dS]
local notation "rwrd" => [dS, uS]

variable (A : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Dg" => signedDg RD Λ A μ initial initial

private theorem separateClosedLoops (a b : ℕ) :
    Dg ([lc [], rc lw] ++ List.replicate b (rdot lw) ++ List.replicate a (ld rwrd) ++
      [la rwrd, ra []]) =
      Dg ([rc []] ++ List.replicate b (rdot []) ++ [ra [], lc []] ++
        List.replicate a (ld []) ++ [la []]) := by
  have hl {w : List (DoubleStrand I ℓ)} :
      signedChain (L ++ [uS, dS, rS] ++ w ++ R) [ld w]
        (L ++ [uS, dS, rS] ++ w ++ R) := by
    simp [leftDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  have hr {w : List (DoubleStrand I ℓ)} :
      signedChain (L ++ w ++ [rS, dS, uS] ++ R) [rdot w]
        (L ++ w ++ [rS, dS, uS] ++ R) := by
    simp [rightDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  have hlOne : signedChain openedL [ld []] openedL := by simpa using (hl (w := []))
  have hrOne : signedChain openedR [rdot []] openedR := by simpa using (hr (w := []))
  have hlBoth : signedChain openedBoth [ld rwrd] openedBoth := by
    simpa [List.append_assoc] using (hl (w := rwrd))
  have hrBoth : signedChain openedBoth [rdot lw] openedBoth := by
    simpa [List.append_assoc] using (hr (w := lw))
  have hrl : signedChain openedBoth [la rwrd, ra []] initial := by
    simp [leftCap, rightCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  have hswapCup := signedDg_swap RD Λ A μ L [rS] R cupL cupR
    (s := initial) (t := openedBoth)
    (by simp [Move.bottom, List.append_assoc])
    (by simp [Move.top, List.append_assoc])
  have hcup := signedDg_replace RD Λ A μ [] _ _
    (List.replicate b (rdot lw) ++ List.replicate a (ld rwrd) ++ [la rwrd, ra []])
    rfl (((replicate_chain hrBoth b).append (replicate_chain hlBoth a)).append hrl)
    (by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])
    (by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]) hswapCup
  have hleftPast := (signedDg_swap_rep RD Λ μ A L [rS] (uS :: R) cupL dotD rfl b).symm
  rw [show L ++ (cupL).bottom ++ [rS] ++ (dotD).bottom ++ uS :: R = openedR by
    simp [Move.bottom, Shape.dom, List.append_assoc],
    show L ++ (cupL).top ++ [rS] ++ (dotD).top ++ uS :: R = openedBoth by
      simp [Move.top, Shape.cod, Letter.dual, List.append_assoc]] at hleftPast
  have hrc : signedChain initial [rc []] openedR := by
    simp [rightCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  have hleftPast' : signedDg RD Λ A μ openedR openedBoth
      ([lc rwrd] ++ List.replicate b (rdot lw)) =
      signedDg RD Λ A μ openedR openedBoth ([].append (List.replicate b (rdot [])) ++ [lc rwrd]) := by
    simpa [leftCup, rightDot, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] using hleftPast
  have hmoveCup := signedDg_replace RD Λ A μ [rc []] _ _
    (List.replicate a (ld rwrd) ++ [la rwrd, ra []])
    hrc ((replicate_chain hlBoth a).append hrl)
    ((by simp [leftCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] :
      signedChain openedR [lc rwrd] openedBoth).append (replicate_chain hrBoth b))
    ((replicate_chain hrOne b).append (by
      simp [leftCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])) hleftPast'
  have hswapCap := signedDg_swap RD Λ A μ L [rS] R capL capR
    (s := openedBoth) (t := initial)
    (by simp [Move.bottom, List.append_assoc])
    (by simp [Move.top, List.append_assoc])
  have hcBoth : signedChain
      initial ([rc []] ++ List.replicate b (rdot []) ++ [lc rwrd]) openedBoth :=
    ((by simp [rightCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] :
      signedChain initial [rc []] openedR).append (replicate_chain hrOne b)).append
      (by simp [leftCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])
  have hcap := signedDg_replace RD Λ A μ (s := initial) (t := initial)
    (([rc []] ++ List.replicate b (rdot []) ++ [lc rwrd]) ++ List.replicate a (ld rwrd)) _ _ []
    (hcBoth.append (replicate_chain hlBoth a)) rfl
    (by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])
    (by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]) hswapCap
  have hrightPast := signedDg_swap_rep' RD Λ μ A (L ++ [uS]) [rS] R capR dotD rfl a
  rw [show (L ++ [uS]) ++ (dotD).bottom ++ [rS] ++ (capR).bottom ++ R = openedBoth by
    simp [Move.bottom, Shape.dom, Letter.dual, List.append_assoc],
    show (L ++ [uS]) ++ (dotD).top ++ [rS] ++ (capR).top ++ R = openedL by
      simp [Move.top, Shape.cod, List.append_assoc]] at hrightPast
  have hrightPast' : signedDg RD Λ A μ openedBoth openedL
      (List.replicate a (ld rwrd) ++ [ra lw]) =
      signedDg RD Λ A μ openedBoth openedL ([ra lw] ++ List.replicate a (ld [])) := by
    simpa [leftDot, rightCap, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] using hrightPast
  have hmoveCap := signedDg_replace RD Λ A μ (s := initial) (t := initial)
    ([rc []] ++ List.replicate b (rdot []) ++ [lc rwrd]) _ _ [la []]
    hcBoth (by simp [leftCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])
    ((replicate_chain hlBoth a).append (by simp [rightCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]))
    ((by simp [rightCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] :
      signedChain openedBoth [ra lw] openedL).append (replicate_chain hlOne a)) hrightPast'
  have hswapPair := signedDg_swap RD Λ A μ L [rS] R cupL capR
    (s := openedR) (t := openedL)
    (by simp [Move.bottom, List.append_assoc])
    (by simp [Move.top, List.append_assoc])
  have hpair := signedDg_replace RD Λ A μ (s := initial) (t := initial)
    ([rc []] ++ List.replicate b (rdot [])) _ _ (List.replicate a (ld []) ++ [la []])
    ((by simp [rightCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] :
      signedChain initial [rc []] openedR).append (replicate_chain hrOne b))
    ((replicate_chain hlOne a).append (by simp [leftCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]))
    (by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])
    (by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]) hswapPair
  exact (by simpa [leftCup, rightCup, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] using hcup :
    Dg _ = Dg ([rc [], lc rwrd] ++ List.replicate b (rdot lw) ++ List.replicate a (ld rwrd) ++
      [la rwrd, ra []])).trans
    ((by simpa [List.append_assoc] using hmoveCup :
      Dg _ = Dg ([rc []] ++ List.replicate b (rdot []) ++ [lc rwrd] ++
        List.replicate a (ld rwrd) ++ [la rwrd, ra []])).trans
    ((by simpa [leftCap, rightCap, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] using hcap :
      Dg _ = Dg ([rc []] ++ List.replicate b (rdot []) ++ [lc rwrd] ++
        List.replicate a (ld rwrd) ++ [ra lw, la []])).trans
    ((by simpa [List.append_assoc] using hmoveCap :
      Dg _ = Dg ([rc []] ++ List.replicate b (rdot []) ++ [lc rwrd, ra lw] ++
        List.replicate a (ld []) ++ [la []])).trans
    (by simpa [leftCup, rightCup, rightCap, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc] using hpair))))

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Qₐ" => affineCoverQ Q exponents
local notation "F" => downPresentedFunctor RD Λ Qₐ P μ (L ++ [uS]) (uS :: R)
local notation "P₀" => KLR.Diagram.pres k Qₐ
local notation "Pdown" => addDownRelations RD Λ Qₐ P
local notation "dL" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "ob0" => (KLR.Diagram.ob [dL, rL, dL])
local notation "caps" => redBraidClosureCaps RD Λ μ L i r R
local notation "cups" => redBraidClosureCups RD Λ μ L i r R

open KLR.Diagram in
private theorem map_dot0 :
    (F).map ((P₀).diag (E0 dL rL dL)) =
      signedDg RD Λ (Pdown) μ openedBoth openedBoth [ld rwrd] := by
  rw [show (F).map ((P₀).diag (E0 dL rL dL)) =
      (Pdown).diag (downLayerDiagram RD Λ μ (L ++ [uS]) (uS :: R)
        (lay [] (.dot dL) [rL, dL]) (g := dotD) rfl) from
    downPresentedFunctor_layer RD Λ Qₐ P μ (L ++ [uS]) (uS :: R)
      (lay [] (.dot dL) [rL, dL]) (lay_valid ..) rfl rfl rfl]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pdown) μ
    (by simp [leftDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc])
  simp [signedLayers, leftDot, downLayerDiagram, moveDiagram, KLR.Diagram.lay, DoubleStrand.down]

open KLR.Diagram in
private theorem map_dot2 :
    (F).map ((P₀).diag (E2 dL rL dL)) =
      signedDg RD Λ (Pdown) μ openedBoth openedBoth [rdot lw] := by
  rw [show (F).map ((P₀).diag (E2 dL rL dL)) =
      (Pdown).diag (downLayerDiagram RD Λ μ (L ++ [uS]) (uS :: R)
        (lay [dL, rL] (.dot dL) []) (g := dotD) rfl) from
    downPresentedFunctor_layer RD Λ Qₐ P μ (L ++ [uS]) (uS :: R)
      (lay [dL, rL] (.dot dL) []) (lay_valid ..) rfl rfl rfl]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pdown) μ
    (by simp [rightDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc])
  simp [signedLayers, rightDot, downLayerDiagram, Diagram.layers_cast, moveDiagram, List.append_assoc,
    KLR.Diagram.lay, DoubleStrand.down]

/-- The physical layers of the monomial E₀ᵃ E₂ᵇ between two upward black
spectators. Reading bottom to top puts the right dots first. -/
def downRedBraidDotLayers (a b : ℕ) : List (SignedLayer I ℓ) :=
  List.replicate b (L ++ [uS, dS] ++ [rS], dotD, uS :: R) ++
    List.replicate a (L ++ [uS], dotD, rS :: dS :: uS :: R)

/-- Both dot blocks preserve the same physical boundary. -/
theorem downRedBraidDotLayers_chain (a b : ℕ) :
    signedChain openedBoth (downRedBraidDotLayers L i r R a b) openedBoth := by
  apply signedChain.append
  · apply replicate_chain
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  · apply replicate_chain
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]

/-- The affine-cover dot monomial maps to its two physical downward-dot blocks. -/
theorem downRedBraidDotMonomial_layers (a b : ℕ) :
    (F).map (End.of ((P₀).diag (KLR.Diagram.E0 dL rL dL)) ^ a *
      End.of ((P₀).diag (KLR.Diagram.E2 dL rL dL)) ^ b) =
    signedDg RD Λ (Pdown) μ openedBoth openedBoth (downRedBraidDotLayers L i r R a b) := by
  change ((F).mapEnd (X := (P₀).obj ob0))
    (End.of ((P₀).diag (KLR.Diagram.E0 dL rL dL)) ^ a *
      End.of ((P₀).diag (KLR.Diagram.E2 dL rL dL)) ^ b) = _
  rw [map_mul, map_pow, map_pow]
  change End.of ((F).map ((P₀).diag (KLR.Diagram.E0 dL rL dL))) ^ a *
    End.of ((F).map ((P₀).diag (KLR.Diagram.E2 dL rL dL))) ^ b = _
  rw [map_dot0, map_dot2, signedDg_power _ _ _ _ (by
    simp [leftDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]),
    signedDg_power _ _ _ _ (by simp [rightDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]),
    End.mul_def]
  exact signedDg_comp RD Λ (Pdown) μ
    (replicate_chain (s := openedBoth) (g := rdot lw)
      (by simp [rightDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]) b)
    (replicate_chain (s := openedBoth) (g := ld rwrd)
      (by simp [leftDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]) a)

private theorem closedDotMonomial_layers (a b : ℕ) :
    closeRedBraid RD Λ μ L i r R Q exponents P
      (End.of ((P₀).diag (KLR.Diagram.E0 dL rL dL)) ^ a *
        End.of ((P₀).diag (KLR.Diagram.E2 dL rL dL)) ^ b) =
      signedDg RD Λ (Pdown) μ initial initial ([lc [], rc lw] ++ List.replicate b (rdot lw) ++ List.replicate a (ld rwrd) ++
        [la rwrd, ra []]) := by
  change (Pdown).diag cups ≫
    (F).map (End.of ((P₀).diag (KLR.Diagram.E0 dL rL dL)) ^ a *
      End.of ((P₀).diag (KLR.Diagram.E2 dL rL dL)) ^ b) ≫ (Pdown).diag caps = _
  rw [downRedBraidDotMonomial_layers]
  have hcup : signedChain initial [lc [], rc lw] openedBoth := by
    simp [leftCup, rightCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  have hcap : signedChain openedBoth [la rwrd, ra []] initial := by
    simp [leftCap, rightCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  rw [← signedDg_eq_diag_of_layers RD Λ (Pdown) μ hcup cups (by
    simp [signedLayers, leftCup, rightCup, redBraidClosureCups, Diagram.layers_comp,
      Diagram.layers_cast, moveDiagram, List.append_assoc]),
    ← signedDg_eq_diag_of_layers RD Λ (Pdown) μ hcap caps (by
      simp [signedLayers, leftCap, rightCap, redBraidClosureCaps, Diagram.layers_comp,
        Diagram.layers_cast, moveDiagram])]
  have hd := downRedBraidDotLayers_chain L i r R a b
  rw [← Category.assoc, signedDg_comp RD Λ (Pdown) μ hcup hd,
    signedDg_comp RD Λ (Pdown) μ (hcup.append hd) hcap]
  simp only [downRedBraidDotLayers, leftDot, rightDot, List.append_assoc, List.cons_append,
    List.nil_append]

private def cwOppositeLayers (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), [])] ++ List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]

private theorem cwOpposite_chain (i : I) (m : ℕ) : SChain [] (cwOppositeLayers i m) [] := by
  unfold cwOppositeLayers
  schain

private theorem dg_cwOpposite [DecidableEq I] (η : X) (i : I) (m : ℕ) :
    dg RD k η [] [] (cwOppositeLayers i m) = dg RD k η [] [] (ccwLs i m) := by
  obtain ⟨ν, rfl⟩ : ∃ ν : X, η = -ν := ⟨-η, (neg_neg η).symm⟩
  let alt : List (LayerData I) :=
    [([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i]) ++
      [([], .cap (dn i), [])]
  have h : dg RD k ν [] [] (cwLs i m) = dg RD k ν [] [] alt := dg_cw_dots RD k ν i m
  have ho := congrArg (omegaU RD k).map h
  rw [omegaU_dg_nil ν (cwLs i m) (sChain_cwLs i m),
    omegaU_dg_nil ν alt (by dsimp only [alt]; schain)] at ho
  have hsgn₀ : Sig.sgnS (cwLs i m) = 1 := by
    simp [Sig.sgnS, Sig.sgnSh, cwLs]
  have hsgn₁ : Sig.sgnS alt = 1 := by
    simp [Sig.sgnS, Sig.sgnSh, alt]
  rw [hsgn₀, hsgn₁, Int.cast_one, one_smul, one_smul] at ho
  have he₀ : Omega.wls (cwLs i m) = ccwLs i m := by
    simp [Omega.wls, Omega.ld, Omega.shape, cwLs, ccwLs]
  have he₁ : Omega.wls alt = cwOppositeLayers i m := by
    simp [Omega.wls, Omega.ld, Omega.shape, alt, cwOppositeLayers]
  change dg RD k (-ν) [] [] (Omega.wls (cwLs i m)) = dg RD k (-ν) [] [] (Omega.wls alt) at ho
  rw [he₀, he₁] at ho
  exact ho.symm

private theorem leftLoop_chain (a : ℕ) :
    signedChain initial ([lc []] ++ List.replicate a (ld []) ++ [la []]) initial := by
  have hc : signedChain initial [lc []] openedL := by
    simp [leftCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  have hd : signedChain openedL [ld []] openedL := by
    simp [leftDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  exact (hc.append (replicate_chain hd a)).append (by
    simp [leftCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])

private theorem rightLoop_chain (b : ℕ) :
    signedChain initial ([rc []] ++ List.replicate b (rdot []) ++ [ra []]) initial := by
  have hc : signedChain initial [rc []] openedR := by
    simp [rightCup, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  have hd : signedChain openedR [rdot []] openedR := by
    simp [rightDot, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  exact (hc.append (replicate_chain hd b)).append (by
    simp [rightCap, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc])

private theorem rightLoop_eq_real (b : ℕ) :
    signedDg RD Λ A μ initial initial ([rc []] ++ List.replicate b (rdot []) ++ [ra []]) =
      A.diag (ccwBubbleAfterRed RD Λ μ L i r R b) := by
  apply signedDg_eq_diag_of_layers RD Λ A μ (rightLoop_chain L i r R b)
  rw [ccwBubbleAfterRed, Diagram.layers_cast]
  change Diagram.layers (blackDiagram RD Λ μ (L ++ [rS]) R
      (BubbleOrientation.counterclockwise.beforeReflection RD (endWeight RD Λ μ (L ++ [rS])) i b)) = _
  rw [realBubble_layers]
  simp [signedLayers, rightCup, rightDot, rightCap, BubbleOrientation.cupLetter]

variable [DecidableEq I]
local notation "Pb" => addBlackKLRelations RD Λ P
local notation "Pcup" => addRedCupRelations RD Λ (Pb)
local notation "Pcap" => addRedCapRelations RD Λ (Pcup)
local notation "Pup" => addRedUpRelations RD Λ k (Pcap)
local notation "Pd" => addDownRelations RD Λ Qₐ (Pup)

private theorem leftLoop_eq_real (a : ℕ) :
    signedDg RD Λ (Pd) μ initial initial ([lc []] ++ List.replicate a (ld []) ++ [la []]) =
      (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R a) := by
  let ν := endWeight RD Λ μ L
  let d := mkD RD ν (cwOppositeLayers i a) (cwOpposite_chain i a)
  have he : (pres RD k).lin (LinDiagram.of d) =
      (pres RD k).lin (LinDiagram.of (ccwReal RD ν i a)) := by
    rw [lin_ccwReal, Presentation.lin_of, ← dg_of (cwOpposite_chain i a)]
    exact dg_cwOpposite RD (k := k) ν i a
  have hb := blackContext_lin_eq_of_KL_eq_suffix RD Λ μ L (rS :: R) [] P
    (LinDiagram.of d) (LinDiagram.of (ccwReal RD ν i a)) he
  have hh : (Pd).lin (blackLinear RD Λ k μ L (rS :: R) (LinDiagram.of d)) =
      (Pd).lin (blackLinear RD Λ k μ L (rS :: R) (LinDiagram.of (ccwReal RD ν i a))) :=
    lin_eq_addRels (Pup) (lin_eq_addRels (Pcap)
      (lin_eq_addRels (Pcup) (lin_eq_addRels (Pb) hb)))
  let e : obj RD Λ μ (L ++ blackWord [] ++ rS :: R) = obj RD Λ μ initial := by
    simp [blackWord, List.append_assoc]
  let f := Diagram.cast (blackDiagram RD Λ μ L (rS :: R) d) e e
  rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ (leftLoop_chain L i r R a) f (by
    dsimp only [f, d]
    rw [Diagram.layers_cast, layers_blackDiagram_mkD]
    simp [cwOppositeLayers, signedLayers, leftCup, leftDot, leftCap, blackWord, Sig.shape])]
  unfold cwBubbleBeforeRed
  change (Pd).lin (LinDiagram.of f) =
    (Pd).lin (LinDiagram.of (Diagram.cast
      (blackDiagram RD Λ μ L (rS :: R) (ccwReal RD ν i a)) e e))
  dsimp only [f]
  rw [← LinDiagram.cast_of, ← LinDiagram.cast_of, Presentation.lin_cast, Presentation.lin_cast]
  exact congrArg ((Pd).castHom e e) (by simpa only [blackLinear_of] using hh)

/-- The capped divided-difference monomial is the product of the physical
clockwise bubble before red and the counterclockwise bubble after red.
The dot powers are read in the bottom-to-top order of the closure. -/
theorem closedDotMonomial_eq_bubbles (a b : ℕ) :
    closeRedBraid RD Λ μ L i r R Q exponents (Pup)
      (End.of ((P₀).diag (KLR.Diagram.E0 dL rL dL)) ^ a *
        End.of ((P₀).diag (KLR.Diagram.E2 dL rL dL)) ^ b) =
      (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R b) ≫
        (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R a) := by
  rw [closedDotMonomial_layers, separateClosedLoops]
  have h := signedDg_comp RD Λ (Pd) μ (rightLoop_chain L i r R b) (leftLoop_chain L i r R a)
  rw [← rightLoop_eq_real, ← leftLoop_eq_real]
  simpa [List.append_assoc] using h.symm

local notation "nL" => (ip RD i (endWeight RD Λ μ L))
local notation "nR" => (ip RD i (endWeight RD Λ μ (L ++ [rS])))
local notation "dotCountL" => (Int.toNat (-nL - 1))
local notation "dotCountR" => (Int.toNat (nR - 1))
local notation "BObj" => (Presentation.obj (Pd) (obj RD Λ μ initial))

private def reflectedBubble (u v : List (DoubleStrand I ℓ))
    (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ initial) :
    LEnd RD k (ob RD (endWeight RD Λ μ u) []) →ₗ[k] End BObj :=
  ((Pd).castLinearEquiv e e).toLinearMap.comp ((Pd).linFunctor.mapLinearMap k ∘ₗ
    blackLinear RD Λ k μ u v)

omit [DecidableEq I] in
private theorem reflectedBubble_preserves (u v : List (DoubleStrand I ℓ))
    (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ initial)
    (f g : LEnd RD k (ob RD (endWeight RD Λ μ u) []))
    (h : (pres RD k).lin f = (pres RD k).lin g) :
    reflectedBubble RD Λ μ L r R Q exponents P u v e f =
      reflectedBubble RD Λ μ L r R Q exponents P u v e g := by
  have hkl := blackContext_lin_eq_of_KL_eq_suffix RD Λ μ u v [] P f g h
  have hq : (Pd).lin (blackLinear RD Λ k μ u v f) = (Pd).lin (blackLinear RD Λ k μ u v g) :=
    lin_eq_addRels (Pup) (lin_eq_addRels (Pcap)
      (lin_eq_addRels (Pcup) (lin_eq_addRels (Pb) hkl)))
  exact congrArg ((Pd).castHom e e) hq

omit [DecidableEq I] in
private theorem reflectedBubble_one (u v : List (DoubleStrand I ℓ))
    (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ initial) :
    reflectedBubble RD Λ μ L r R Q exponents P u v e 1 = 1 := by
  change (Pd).castHom e e ((Pd).lin (blackLinear RD Λ k μ u v (LinDiagram.of (𝟙 _)))) = 𝟙 _
  rw [blackLinear_of, blackDiagram_id, Presentation.lin_of, Presentation.diag_id, Presentation.castHom_id]

omit [DecidableEq I] in
private theorem beforeEq : obj RD Λ μ (L ++ blackWord [] ++ rS :: R) = obj RD Λ μ initial := by
  simp [blackWord, List.append_assoc]

omit [DecidableEq I] in
private theorem afterEq : obj RD Λ μ ((L ++ [rS]) ++ blackWord [] ++ R) = obj RD Λ μ initial := by
  simp [blackWord]

local notation "beforeMap" => reflectedBubble RD Λ μ L r R Q exponents P L (rS :: R) (beforeEq RD Λ μ L r R)
local notation "afterMap" => reflectedBubble RD Λ μ L r R Q exponents P (L ++ [rS]) R (afterEq RD Λ μ L r R)

omit [DecidableEq I] in
private theorem beforeMap_real (a : ℕ) :
    (beforeMap) (LinDiagram.of (ccwReal RD (endWeight RD Λ μ L) i a)) =
      (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R a) := by
  change (Pd).castHom (beforeEq RD Λ μ L r R) (beforeEq RD Λ μ L r R)
    ((Pd).lin (blackLinear RD Λ k μ L (rS :: R) (LinDiagram.of _))) = _
  rw [blackLinear_of, Presentation.castHom_lin, LinDiagram.cast_of]
  rfl

omit [DecidableEq I] in
private theorem afterMap_real (b : ℕ) :
    (afterMap) (LinDiagram.of (cwReal RD (endWeight RD Λ μ (L ++ [rS])) i b)) =
      (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R b) := by
  change (Pd).castHom (afterEq RD Λ μ L r R) (afterEq RD Λ μ L r R)
    ((Pd).lin (blackLinear RD Λ k μ (L ++ [rS]) R (LinDiagram.of _))) = _
  rw [blackLinear_of, Presentation.castHom_lin, LinDiagram.cast_of]
  rfl

/-- The degree-one mixed bubble convolution in the strict sign-changing region.
The red coroot pairing determines the degree-zero dot counts of both real bubbles. -/
theorem closedRedBraid_degreeOne (hneg : nL ≤ -1) (hpos : 1 ≤ nR)
    (hδ : nR = nL + (exponents r i : ℤ)) :
    (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R (dotCountR + 1)) +
      (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R (dotCountL + 1)) = 0 := by
  let w : ℕ → End BObj := fun a => (Pd).diag (cwBubbleBeforeRed RD Λ μ L i r R a)
  let c : ℕ → End BObj := fun b => (Pd).diag (ccwBubbleAfterRed RD Λ μ L i r R b)
  have hw' (a : ℕ) (ha : a < dotCountL) : w a = 0 := by
    rw [show w a = (Pd).diag _ from rfl, ← beforeMap_real]
    have h : (pres RD k).lin (LinDiagram.of (ccwReal RD (endWeight RD Λ μ L) i a)) =
        (pres RD k).lin 0 := by
      rw [lin_ccwReal, Presentation.lin_zero]
      exact dg_ccwNeg RD k _ _ _ (by omega)
    exact (reflectedBubble_preserves RD Λ μ L r R Q exponents P L (rS :: R)
      (beforeEq RD Λ μ L r R) _ 0 h).trans (map_zero _)
  have hc' (b : ℕ) (hb : b < dotCountR) : c b = 0 := by
    rw [show c b = (Pd).diag _ from rfl, ← afterMap_real]
    have h : (pres RD k).lin (LinDiagram.of (cwReal RD (endWeight RD Λ μ (L ++ [rS])) i b)) =
        (pres RD k).lin 0 := by
      rw [lin_cwReal, Presentation.lin_zero]
      exact dg_cwNeg RD k _ _ _ (by omega)
    exact (reflectedBubble_preserves RD Λ μ L r R Q exponents P (L ++ [rS]) R
      (afterEq RD Λ μ L r R) _ 0 h).trans (map_zero _)
  have hw₀ : w dotCountL = 1 := by
    rw [show w dotCountL = (Pd).diag _ from rfl, ← beforeMap_real]
    have h : (pres RD k).lin (LinDiagram.of (ccwReal RD (endWeight RD Λ μ L) i dotCountL)) =
        (pres RD k).lin (LinDiagram.of (𝟙 _)) := by
      rw [lin_ccwReal, dg_ccwOne RD k _ _ hneg, dg_nil, Presentation.lin_of, Presentation.diag_id]
    exact (reflectedBubble_preserves RD Λ μ L r R Q exponents P L (rS :: R)
      (beforeEq RD Λ μ L r R) _ 1 h).trans (reflectedBubble_one RD Λ μ L r R Q exponents P _ _ _)
  have hc₀ : c dotCountR = 1 := by
    rw [show c dotCountR = (Pd).diag _ from rfl, ← afterMap_real]
    have h : (pres RD k).lin (LinDiagram.of (cwReal RD (endWeight RD Λ μ (L ++ [rS])) i dotCountR)) =
        (pres RD k).lin (LinDiagram.of (𝟙 _)) := by
      rw [lin_cwReal, dg_cwOne RD k _ _ hpos, dg_nil, Presentation.lin_of, Presentation.diag_id]
    exact (reflectedBubble_preserves RD Λ μ L r R Q exponents P (L ++ [rS]) R
      (afterEq RD Λ μ L r R) _ 1 h).trans (reflectedBubble_one RD Λ μ L r R Q exponents P _ _ _)
  have hsum : ∑ a ∈ Finset.range (exponents r i), w a * c (exponents r i - 1 - a) = 0 := by
    have h := closeRedBraid_correction_eq_zero RD Λ Q exponents P μ L i r R hneg hpos
    simp only [closedDotMonomial_eq_bubbles] at h
    exact h
  rw [show exponents r i = dotCountL + dotCountR + 2 by omega,
    show dotCountL + dotCountR + 2 - 1 = dotCountL + dotCountR + 1 by omega] at hsum
  have hh := closedRedBraidCorrection_eq_sconv w c dotCountL dotCountR 0 (Nat.zero_le _) hw' hc'
  simp only [Nat.zero_add] at hh
  rw [hh] at hsum
  have hdegree : w dotCountL * c (dotCountR + 1) + w (dotCountL + 1) * c dotCountR = 0 := by
    simpa only [sconv, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.sub_zero, Nat.sub_self, Nat.add_zero] using hsum
  rw [hw₀, hc₀, one_mul, mul_one] at hdegree
  exact hdegree

/-- The bubble before red, indexed by its normalized degree. Real and fake
bubbles use the same index according to KL III's inverse-series convention. -/
def normalizedBubbleBeforeRed (s : BubbleOrientation) (d : ℕ) : End BObj :=
  (beforeMap) (s.beforeReflectionExtended RD k (endWeight RD Λ μ L) i
    (s.degreeZeroDots nL + d))

/-- The bubble after red, indexed by its normalized degree. -/
def normalizedBubbleAfterRed (s : BubbleOrientation) (d : ℕ) : End BObj :=
  (afterMap) (s.beforeReflectionExtended RD k (endWeight RD Λ μ (L ++ [rS])) i
    (s.degreeZeroDots nR + d))

private theorem grassInv_one {D : Type*} [Ring D] (c : ℕ → D) : grassInv c 1 = -c 1 := by
  have h := grassInv_succ c 0
  change grassInv c 1 = -∑ a : Fin 1, c (a.val + 1) * grassInv c (0 - a.val) at h
  rw [h, Fintype.sum_unique]
  change -(c 1 * grassInv c 0) = -c 1
  rw [grassInv_zero, mul_one]

/-- The degree-one bubble slides across red in both orientations when the
left coroot is negative and the right coroot is positive. This is the first
coefficient where the dot-shift slides for real bubbles do not apply. -/
theorem normalizedBubble_degreeOne (hneg : nL ≤ -1) (hpos : 1 ≤ nR)
    (hδ : nR = nL + (exponents r i : ℤ)) :
    normalizedBubbleBeforeRed RD Λ μ L i r R Q exponents P .clockwise 1 =
      normalizedBubbleAfterRed RD Λ μ L i r R Q exponents P .clockwise 1 ∧
    normalizedBubbleBeforeRed RD Λ μ L i r R Q exponents P .counterclockwise 1 =
      normalizedBubbleAfterRed RD Λ μ L i r R Q exponents P .counterclockwise 1 := by
  have hL : (-nL - 1 + 1).toNat = dotCountL + 1 := by omega
  have hR : (nR - 1 + 1).toNat = dotCountR + 1 := by omega
  have hfL : cwL RD k (endWeight RD Λ μ L) i nL =
      -LinDiagram.of (ccwReal RD (endWeight RD Λ μ L) i (dotCountL + 1)) := by
    rw [cwL, ite_eq_right (by omega), show nL + 1 - nL = 1 by omega,
      ite_eq_left (by decide : 0 ≤ (1 : ℤ))]
    change grassInv _ 1 = _
    rw [grassInv_one, ccwR]
    change -(if 0 ≤ -nL - 1 + 1 then LinDiagram.of
      (ccwReal RD (endWeight RD Λ μ L) i ((-nL - 1 + 1).toNat)) else 0) = _
    rw [ite_eq_left (by omega), hL]
  have hfR : ccwL RD k (endWeight RD Λ μ (L ++ [rS])) i (-nR) =
      -LinDiagram.of (cwReal RD (endWeight RD Λ μ (L ++ [rS])) i (dotCountR + 1)) := by
    rw [ccwL, ite_eq_right (by omega), show -nR + 1 + nR = 1 by omega,
      ite_eq_left (by decide : 0 ≤ (1 : ℤ))]
    change grassInv _ 1 = _
    rw [grassInv_one, cwR]
    change -(if 0 ≤ nR - 1 + 1 then LinDiagram.of
      (cwReal RD (endWeight RD Λ μ (L ++ [rS])) i ((nR - 1 + 1).toNat)) else 0) = _
    rw [ite_eq_left (by omega), hR]
  have h := closedRedBraid_degreeOne RD Λ μ L i r R Q exponents P hneg hpos hδ
  constructor
  · unfold normalizedBubbleBeforeRed normalizedBubbleAfterRed
    change (beforeMap) (ccwL RD k _ i (-nL - 1 + 1)) =
      (afterMap) (ccwL RD k _ i (-nR - 1 + 1))
    rw [show -nR - 1 + 1 = -nR by omega, hfR, map_neg, afterMap_real,
      ccwL, ite_eq_left (by omega), hL, beforeMap_real]
    exact eq_neg_of_add_eq_zero_right h
  · unfold normalizedBubbleBeforeRed normalizedBubbleAfterRed
    change (beforeMap) (cwL RD k _ i (nL - 1 + 1)) =
      (afterMap) (cwL RD k _ i (nR - 1 + 1))
    rw [show nL - 1 + 1 = nL by omega, hfL, map_neg, beforeMap_real,
      cwL, ite_eq_left (by omega), hR, afterMap_real]
    exact neg_eq_of_add_eq_zero_left h

end Loops

end Categorification.Stendhal.DoubleDiagram
