/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDot
import Categorification.WeightedKLR.RedStrands.DoubleBlackAdjunction
import Categorification.WeightedKLR.RedStrands.DoubleBubbleRelations

/-!
# A creating cup at the endpoint of a signed cap sweep

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28 and §2.2, Definition 2.4.
When a cup supplies the stationary cap leg and the outside-left surviving
strand, interchange moves the whole intervening sweep below the cup. The
remaining biadjunction triangle straightens and transfers its dots to the
survivor. When the cup supplies both cap endpoints, the swept word is empty
and the composite is the real bubble in its specified physical region.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L U : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))

local notation "A" => addBlackAdjunctionRelations RD Λ P
local notation "bl(" l ")" => (Sum.inl l : DoubleStrand I ℓ)
local notation "D" => signedDg RD Λ A μ
local notation "start" => L ++ U ++ [bl(l)] ++ R
local notation "stop" => L ++ [bl(l)] ++ U ++ R
local notation "mid" => (L ++ [bl(l)]) ++ [bl(l.dual)] ++ U ++ [bl(l)] ++ R
local notation "cup" => (L, Move.black (Shape.cup l), U ++ [bl(l)] ++ R)
local notation "blk" => signedCapBlock (L ++ [bl(l)]) U l R
local notation "sw" => sweepBlackLeft L U l R
local notation "dot" => (L, Move.black (Shape.dot l), U ++ R)

private theorem cup_chain : signedChain start [cup] mid := by
  simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]

private theorem block_chain (d : ℕ) : signedChain mid (blk d) stop :=
  signedCapBlock_chain _ U l R d

private theorem cup_block_zero :
    D start mid [cup] ≫ D mid stop (blk 0) = D start stop sw := by
  let top := (L ++ [bl(l),bl(l.dual),bl(l)]) ++ U ++ R
  let cap : SignedLayer I ℓ := (L ++ [bl(l)], .black (.cap l), U ++ R)
  let cup' : SignedLayer I ℓ := (L, .black (.cup l), bl(l) :: (U ++ R))
  let sw' := sweepBlackLeft ((L ++ [bl(l)]) ++ [bl(l.dual)]) U l R
  have hc : signedChain ([] : List (DoubleStrand I ℓ)) [([], .black (.cup l), [])]
      [bl(l),bl(l.dual)] := by simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod]
  have hs := sweepBlackLeft_chain ([] : List (DoubleStrand I ℓ)) U l []
  have eqv := signedDg_interchange RD Λ A μ L R hc hs
  have e₁ : L ++ [] ++ ([] ++ U ++ [bl(l)] ++ []) ++ R = start := by simp [List.append_assoc]
  have e₂ : L ++ [bl(l),bl(l.dual)] ++ ([] ++ [bl(l)] ++ U ++ []) ++ R = top := by
    simp [top,List.append_assoc]
  rw [e₁,e₂] at eqv
  have swap : D start top ([cup] ++ sw') = D start top (sw ++ [cup']) := by
    simp only [sweepBlackLeft_whisk] at eqv
    simpa only [signedWhisk, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
      List.append_assoc, List.cons_append, sw', cup'] using eqv
  have hcap : signedChain top [cap] stop := by
    simp [top,cap,signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod,List.append_assoc]
  have hcup : signedChain stop [cup'] top := by
    simp [top,cup',signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod,List.append_assoc]
  have hsw : signedChain mid sw' top := by
    simpa only [top, sw', List.append_assoc,List.cons_append,List.nil_append] using
      sweepBlackLeft_chain ((L ++ [bl(l)]) ++ [bl(l.dual)]) U l R
  have h₁ := (cup_chain L U l R).append hsw
  have h₂ := (sweepBlackLeft_chain L U l R).append hcup
  have exch := congrArg (fun f => f ≫ D top stop [cap]) swap
  rw [signedDg_comp RD Λ A μ h₁ hcap, signedDg_comp RD Λ A μ h₂ hcap] at exch
  have snake : D stop stop ([cup'] ++ [cap]) = 𝟙 _ := by
    let b := blackSnakeLeft RD Λ μ L l (U ++ R)
    have h : L ++ [bl(l)] ++ (U ++ R) = stop := by simp [List.append_assoc]
    rw [← h]
    exact (signedDg_eq_diag_of_layers RD Λ A μ (by simpa only [h] using hcup.append hcap)
      b (by simp [b,cup',cap,blackSnakeLeft,signedLayers,moveDiagram])).trans
      (blackSnakeLeft_eq RD Λ μ L l (U ++ R) P)
  rw [signedDg_comp RD Λ A μ (cup_chain L U l R) (block_chain L U l R 0)]
  change D start stop ([cup] ++ (sw' ++ [] ++ [cap])) = _
  rw [List.append_nil, ← List.append_assoc, exch, List.append_assoc sw [cup'] [cap],
    ← signedDg_comp RD Λ A μ (sweepBlackLeft_chain L U l R) (hcup.append hcap), snake,
    Category.comp_id]


local notation "middleDot" => (L ++ [bl(l)], Move.black (Shape.dot l.dual), U ++ [bl(l)] ++ R)
local notation "outerDot" => (L, Move.black (Shape.dot l), bl(l.dual) :: (U ++ [bl(l)] ++ R))

private theorem middleDot_chain : signedChain mid [middleDot] mid := by
  simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]

private theorem outerDot_chain : signedChain mid [outerDot] mid := by
  simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]

private theorem survivorDot_chain : signedChain stop [dot] stop := by
  simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]

private theorem cup_dot_outer :
    D start mid [cup] ≫ D mid mid [middleDot] = D start mid [cup] ≫ D mid mid [outerDot] := by
  rw [signedDg_comp RD Λ A μ (cup_chain L U l R) (middleDot_chain L U l R),
    signedDg_comp RD Λ A μ (cup_chain L U l R) (outerDot_chain L U l R)]
  let T := U ++ [bl(l)] ++ R
  have e₁ : L ++ T = start := by simp [T,List.append_assoc]
  have e₂ : L ++ [bl(l),bl(l.dual)] ++ T = mid := by simp [T,List.append_assoc]
  rw [← e₁,← e₂]
  apply Eq.trans (signedDg_eq_diag_of_layers RD Λ A μ
    (by simpa only [e₁,e₂] using (cup_chain L U l R).append (middleDot_chain L U l R))
    (blackCupDotRight RD Λ μ L l T) (by simp [blackCupDotRight, blackCup, blackPairDotRight,
      signedLayers, moveDiagram, T]))
  apply (blackCup_dot_slide RD Λ μ L l T P).symm.trans
  exact (signedDg_eq_diag_of_layers RD Λ A μ
    (by simpa only [e₁,e₂] using (cup_chain L U l R).append (outerDot_chain L U l R))
    (blackCupDotLeft RD Λ μ L l T) (by simp [blackCupDotLeft, blackCup, blackPairDotLeft,
      signedLayers, moveDiagram,T])).symm

private theorem survivor_dot_block (d : ℕ) :
    D mid mid [outerDot] ≫ D mid stop (blk d) = D mid stop (blk d) ≫ D stop stop [dot] := by
  rw [signedDg_comp RD Λ A μ (outerDot_chain L U l R) (block_chain L U l R d),
    signedDg_comp RD Λ A μ (block_chain L U l R d) (survivorDot_chain L U l R)]
  have hd : signedChain (ℓ := ℓ) [bl(l)] [([], .black (.dot l), [])] [bl(l)] := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod]
  have ex := signedDg_interchange RD Λ A μ L R hd (signedCapBlock_chain [] U l [] d)
  have e₁ : L ++ [bl(l)] ++ ([] ++ [bl(l.dual)] ++ U ++ [bl(l)] ++ []) ++ R = mid := by
    simp [List.append_assoc]
  have e₂ : L ++ [bl(l)] ++ ([] ++ U ++ []) ++ R = stop := by simp [List.append_assoc]
  rw [e₁,e₂] at ex
  simp only [signedCapBlock_whisk] at ex
  simpa only [signedWhisk, List.map_cons, List.map_nil, List.append_nil, List.nil_append,
    List.cons_append, List.append_assoc] using ex

private theorem cupLeft_power (d : ℕ) :
    D start stop (cup :: blk d) = D start stop sw ≫ (End.of (D stop stop [dot]) ^ d) := by
  have aux (n : ℕ) : D start mid [cup] ≫ D mid stop (blk n) =
      D start stop sw ≫ (End.of (D stop stop [dot]) ^ n) := by
    induction n with
    | zero => simpa using cup_block_zero RD Λ P μ L U l R
    | succ n ih =>
      have inc : D mid mid [middleDot] ≫ D mid stop (blk n) = D mid stop (blk (n+1)) := by
        rw [signedDg_comp RD Λ A μ (middleDot_chain L U l R) (block_chain L U l R n)]
        exact signedCapBlock_dotLeft RD Λ A μ (L ++ [bl(l)]) U l R n
      rw [← inc, ← Category.assoc, cup_dot_outer RD Λ P μ L U l R, Category.assoc,
        survivor_dot_block RD Λ P μ L U l R n, ← Category.assoc, ih, pow_succ']
      exact Category.assoc ..
  exact (signedDg_comp RD Λ A μ (cup_chain L U l R) (block_chain L U l R d)).symm.trans (aux d)


private theorem dots_chain (n : ℕ) : signedChain stop (List.replicate n dot) stop := by
  induction n with
  | zero => rfl
  | succ n ih => exact (survivorDot_chain L U l R).append ih

private theorem dots_power (n : ℕ) :
    End.of (D stop stop [dot]) ^ n = D stop stop (List.replicate n dot) := by
  induction n with
  | zero => exact (signedDg_nil RD Λ A μ stop).symm
  | succ n ih =>
    rw [pow_succ]
    change D stop stop [dot] ≫ (End.of (D stop stop [dot]) ^ n) = _
    rw [ih]
    exact signedDg_comp RD Λ A μ (survivorDot_chain L U l R) (dots_chain L U l R n)

/-- The preceding cup which supplies the outer-left survivor and the stationary cap
leg straightens over any signed word. All dots appear on the surviving strand, and
the right leg's sweep gives the remaining crossings. This is the left triangle in
the cap induction for Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. -/
theorem signedCapBlock_cupLeft (d : ℕ) :
    D start stop (cup :: blk d) = D start stop (sw ++ List.replicate d dot) := by
  rw [cupLeft_power RD Λ P μ L U l R d, dots_power RD Λ P μ L U l R d]
  exact signedDg_comp RD Λ A μ (sweepBlackLeft_chain L U l R) (dots_chain L U l R d)

/-- If both endpoints of the swept cap are created by the preceding cup, the
composite is the indicated real bubble with its dots on the physical left leg,
in any exterior word. Its left region is the weight at the end of the prefix
in Webster, arXiv:1309.3796v2, §2.2, (2.2a), and §4.5, Lemma 4.28. -/
theorem signedCapBlock_cupBubble {w : List (DoubleStrand I ℓ)} (h : L ++ R = w)
    (s : BubbleOrientation) (i : I) (d : ℕ) :
    signedDg RD Λ P μ w w
      ((L, .black (.cup (s.cupLetter i)), R) :: signedCapBlock L [] (s.cupLetter i).dual R d) =
    P.diag (Diagram.cast (blackDiagram RD Λ μ L R
      (s.beforeReflection RD (endWeight RD Λ μ L) i d))
      (by simp [blackWord,h]) (by simp [blackWord,h])) := by
  subst w
  apply signedDg_eq_diag_of_layers
  · have hc : signedChain (L ++ R) [(L, .black (.cup (s.cupLetter i)), R)]
        (L ++ [bl((s.cupLetter i).dual.dual)] ++ [] ++ [bl((s.cupLetter i).dual)] ++ R) := by
      simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
    simpa only [List.append_nil, List.singleton_append] using hc.append (signedCapBlock_chain L [] (s.cupLetter i).dual R d)
  · simp [Diagram.layers_cast, realBubble_layers, signedLayers, signedCapBlock, capLegDots,
      sweepBlackLeft]

end Categorification.Stendhal.DoubleDiagram
