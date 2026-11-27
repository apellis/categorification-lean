/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPhysicalSpanQ
import Categorification.Diagrams.KL3.SpanningSetBlock
import Categorification.Diagrams.CLQ.SpanningSetBlock

/-!
# Black local cup reductions for the signed sweep

The curl, cusp, and Reidemeister II following a cup in KL III,
arXiv:0807.3250v1, proof of Proposition 3.11, decrease the crossing
count. The black rectangle in physical order gives these bounds with
arbitrary signed spectators for Webster v2, §4.5, Lemma 4.28.

This is the version of `DoubleSignedCupCurl` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe w u v
variable {I : Type u} {ℓ : ℕ}
local notation "B" => DoubleStrand I ℓ
local notation "bl(" l ")" => (Sum.inl l : B)
variable (L R : List (DoubleStrand I ℓ))

private theorem physicalBlackLayers_append (A D : List (LayerData I)) :
    physicalBlackLayers L R (A ++ D) = physicalBlackLayers L R A ++ physicalBlackLayers L R D := List.map_append

private theorem physicalBlackLayers_whL (a b : List (Letter I)) (A : List (LayerData I)) :
    physicalBlackLayers L R (A.map (whL a b)) = physicalBlackLayers (L ++ a.map Sum.inl) (b.map Sum.inl ++ R) A := by
  simp only [physicalBlackLayers,List.map_map]
  apply List.map_congr_left
  rintro ⟨u,g,v⟩ _
  simp [whL,List.append_assoc]

private theorem physicalBlackLayers_xLay (i j : Letter I) :
    physicalBlackLayers L R (xLay i j) = crossBlackLeft L (bl(i)) j R := by
  obtain ⟨_ | _,u⟩ := i <;> obtain ⟨_ | _,v⟩ := j <;>
    simp [physicalBlackLayers,xLay,crosslL,crossrL,crossBlackLeft,upwardMateLayers]

variable {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (P : Presentation.{w,max u v} (signature RD Λ) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
  (μ : X)

local notation "D" => signedDg RD Λ P μ
local notation "F" => signedCrossingSpan RD Λ P μ

private theorem mem_reindex {a b a' b' : List B} (ha : a=a') (hb : b=b')
    {ls : List (SignedLayer I ℓ)} {n : ℕ} (h : D a b ls ∈ F a b n) : D a' b' ls ∈ F a' b' n := by
  cases ha; cases hb; exact h

include hP

private theorem physicalBoundQ {s t : List (Letter I)} (A : List (LayerData I)) (h : SChain s A t)
    {n : ℕ} (hf : ∀ ν, NF.dg (CLQ.pres RD k sc) ν s t A ∈ CLQ.LeL RD k sc ν s t n) :
    D (L ++ s.map Sum.inl ++ R) (L ++ t.map Sum.inl ++ R) (physicalBlackLayers L R A) ∈
      F (L ++ s.map Sum.inl ++ R) (L ++ t.map Sum.inl ++ R) n := by
  let ν := -endWeight RD Λ μ L - RD.wX s
  exact physicalBlack_mem_signedCrossingSpanQ RD sc Λ P hP μ L R A h
    (ν := ν) (by rw [wt_eq_add_wX]; dsimp only [ν]; abel) (hf ν)

/-- A cup with its two output strands crossed has a crossing-free expansion,
including when its signed exterior contains red strands. -/
theorem signedCupCurl_blackQ (l : Letter I) :
    D (L ++ R) (L ++ [bl(l.dual),bl(l)] ++ R)
      ([(L,.black (.cup l),R)] ++ crossBlackLeft L (bl(l)) l.dual R) ∈
      F (L ++ R) (L ++ [bl(l.dual),bl(l)] ++ R) 0 := by
  let A := [([],Shape.cup l,[])] ++ xLay l l.dual
  have ha : SChain [] A [l.dual,l] := (show SChain [] [([], .cup l, [])] [l,l.dual] from ⟨rfl,rfl⟩).append
    (sChain_xLay l l.dual)
  have H := physicalBoundQ L R RD Λ sc P hP μ A ha (fun ν => CLQ.cupCurl (RD := RD) (k := k) ν l)
  have H := mem_reindex RD Λ P μ (a' := L ++ R) (b' := L ++ [bl(l.dual),bl(l)] ++ R)
    (by simp) rfl H
  have e : physicalBlackLayers L R A =
      [(L,.black (.cup l),R)] ++ crossBlackLeft L (bl(l)) l.dual R := by
    dsimp only [A]
    rw [physicalBlackLayers_append,physicalBlackLayers_xLay]
    simp [physicalBlackLayers]
  exact e ▸ H

/-- A through-strand that sweeps left across both legs of a cup gives terms
with at most one crossing. This is the local interior-cup bound of KL III,
arXiv:0807.3250v1, proof of Proposition 3.11, in physical order. -/
theorem signedCupTwoLegs_blackQ (x l : Letter I) :
    D (L ++ [bl(l)] ++ R) (L ++ [bl(l),bl(x),bl(x.dual)] ++ R)
      ([(L,.black (.cup x),bl(l) :: R)] ++ crossBlackLeft (L ++ [bl(x)]) (bl(x.dual)) l R ++
        crossBlackLeft L (bl(x)) l (bl(x.dual) :: R)) ∈
      F (L ++ [bl(l)] ++ R) (L ++ [bl(l),bl(x),bl(x.dual)] ++ R) 1 := by
  classical
  let A := [([],Shape.cup x,[l])] ++ (xLay x.dual l).map (whL [x] []) ++ (xLay x l).map (whL [] [x.dual])
  have ha : SChain [l] A [l,x,x.dual] :=
    ((show SChain [l] [([], .cup x, [l])] [x,x.dual,l] from ⟨rfl,rfl⟩).append
      (by simpa using (sChain_xLay x.dual l).whisk [x] [])).append
      (by simpa using (sChain_xLay x l).whisk [] [x.dual])
  have H := physicalBoundQ L R RD Λ sc P hP μ A ha (fun ν => CLQ.cupPF2 (RD := RD) (k := k) ν x l)
  have H := mem_reindex RD Λ P μ (a' := L ++ [bl(l)] ++ R) (b' := L ++ [bl(l),bl(x),bl(x.dual)] ++ R)
    rfl rfl H
  have e : physicalBlackLayers L R A = [(L,.black (.cup x),bl(l) :: R)] ++
      crossBlackLeft (L ++ [bl(x)]) (bl(x.dual)) l R ++ crossBlackLeft L (bl(x)) l (bl(x.dual) :: R) := by
    dsimp only [A]
    rw [physicalBlackLayers_append,physicalBlackLayers_append,
      physicalBlackLayers_whL,physicalBlackLayers_whL,physicalBlackLayers_xLay,physicalBlackLayers_xLay]
    simp [physicalBlackLayers]
  exact e ▸ H

/-- Creating the stationary cap endpoint together with the first interior black
strand forms a dotted curl on one surviving strand. With no other interior
strands its expansion has crossing degree zero. -/
theorem signedCapBlock_firstCup_singleQ (l : Letter I) (d : ℕ) :
    D (L ++ [bl(l)] ++ R) (L ++ [bl(l)] ++ R)
      ((L,.black (.cup l.dual),bl(l) :: R) :: signedCapBlock L [bl(l)] l R d) ∈
      F (L ++ [bl(l)] ++ R) (L ++ [bl(l)] ++ R) 0 := by
  classical
  let A := [([],Shape.cup l.dual,[l])] ++ capBlk [l] l d
  have ha : SChain [l] A [l] :=
    (show SChain [l] [([], .cup l.dual, [l])] ([l.dual] ++ [l] ++ [l]) by
      simp [SChain,Shape.cod]).append (sChain_capBlk [l] l d)
  have H := physicalBoundQ L R RD Λ sc P hP μ A ha (fun ν => CLQ.capBlk_cupAs (RD := RD) (k := k) ν [] l d)
  have H := mem_reindex RD Λ P μ (a' := L ++ [bl(l)] ++ R) (b' := L ++ [bl(l)] ++ R) rfl rfl H
  obtain ⟨_ | _,i⟩ := l <;>
    simpa [A,capBlk,lmLc,xLay,whL,physicalBlackLayers,List.map_replicate,signedCapBlock,
      capLegDots,sweepBlackLeft,crossBlackLeft,Letter.dual,List.append_assoc] using H

end Categorification.Stendhal.DoubleDiagram
