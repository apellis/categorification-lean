/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotSweep

/-! # A dot between the stationary and swept cap legs

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28, using KL III
Proposition 3.11. A dot in the interior passes through one potentially
intersecting crossing, between two disjoint stages of the sweep.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "A" => signedCapKLPresentation RD Λ P Q exponents t
local notation "B" => DoubleStrand I ℓ
local notation "bx" => (Sum.inl (α := Letter I) (β := Fin ℓ))

private theorem whisk_capSweepDot (L R p q : List B) (s : Letter I) :
    signedWhisk L R (capSweepDot p s q) = capSweepDot (L ++ p) s (q ++ R) := rfl

/-- A dot on an interior black strand passes above the cap. The nilHecke
correction loses the crossing between this strand and the moving leg. -/
theorem signedCapBlock_dotInside (μ : X) (L U V : List B) (s l : Letter I) (R : List B) (d : ℕ) :
    signedDg RD Λ (A) μ (L ++ [bx l.dual] ++ (U ++ [bx s] ++ V) ++ [bx l] ++ R)
        (L ++ (U ++ [bx s] ++ V) ++ R)
      (capSweepDot (L ++ [bx l.dual] ++ U) s (V ++ [bx l] ++ R) ++ signedCapBlock L (U ++ [bx s] ++ V) l R d) -
    signedDg RD Λ (A) μ (L ++ [bx l.dual] ++ (U ++ [bx s] ++ V) ++ [bx l] ++ R)
        (L ++ (U ++ [bx s] ++ V) ++ R)
      (signedCapBlock L (U ++ [bx s] ++ V) l R d ++ capSweepDot (L ++ U) s (V ++ R)) ∈
    signedCrossingSpan RD Λ (A) μ (L ++ [bx l.dual] ++ (U ++ [bx s] ++ V) ++ [bx l] ++ R)
      (L ++ (U ++ [bx s] ++ V) ++ R) (U.length + V.length) := by
  let p := L ++ [bx l.dual] ++ U
  let a := p ++ [bx s] ++ V ++ [bx l] ++ R
  let b := p ++ [bx s,bx l] ++ V ++ R
  let c := p ++ [bx l,bx s] ++ V ++ R
  let e := (L ++ U) ++ [bx s] ++ V ++ R
  let X₀ := capSweepDot p s (V ++ [bx l] ++ R)
  let Y₀ := capSweepDot p s (bx l :: (V ++ R))
  let Z₀ := capSweepDot (p ++ [bx l]) s (V ++ R)
  let W₀ := capSweepDot (L ++ U) s (V ++ R)
  let F := sweepBlackLeft (p ++ [bx s]) V l R
  let G := crossBlackLeft p (bx s) l (V ++ R)
  let H := signedCapBlock L U l (bx s :: (V ++ R)) d
  have hX : signedChain a X₀ a := by simpa [a,X₀,List.append_assoc] using capSweepDot_chain p s (V ++ [bx l] ++ R)
  have hY : signedChain b Y₀ b := by simpa [b,Y₀,List.append_assoc] using capSweepDot_chain p s (bx l :: (V ++ R))
  have hZ : signedChain c Z₀ c := by simpa [c,Z₀,List.append_assoc] using capSweepDot_chain (p ++ [bx l]) s (V ++ R)
  have hW : signedChain e W₀ e := by simpa [e,W₀,List.append_assoc] using capSweepDot_chain (L ++ U) s (V ++ R)
  have hF : signedChain a F b := by simpa [a,b,F,List.append_assoc] using sweepBlackLeft_chain (p ++ [bx s]) V l R
  have hG : signedChain b G c := by simpa [b,c,G,List.append_assoc] using crossBlackLeft_chain p (bx s) l (V ++ R)
  have hH : signedChain c H e := by
    simpa [c,e,p,H,List.append_assoc] using signedCapBlock_chain L U l (bx s :: (V ++ R)) d
  have eqF : signedDg RD Λ (A) μ a b (X₀ ++ F) = signedDg RD Λ (A) μ a b (F ++ Y₀) := by
    apply capDot_eq_congr RD Λ (A) μ (signedDg_interchange RD Λ (A) μ p R
      (capSweepDot_chain ([] : List B) s []) (sweepBlackLeft_chain ([] : List B) V l [])) <;>
      simp [a,b,X₀,Y₀,F,whisk_capSweepDot,sweepBlackLeft_whisk,List.append_assoc]
  have eqG : signedDg RD Λ (A) μ b c (Y₀ ++ G) - signedDg RD Λ (A) μ b c (G ++ Z₀) ∈
      signedCrossingSpan RD Λ (A) μ b c 0 := by
    apply capDot_bound_congr RD Λ (A) μ (capSweepDot_cross_black RD Λ (A) μ p (V ++ R)
      (signedCapKL_reflectedBlack RD Λ P Q exponents t) s l false) <;>
      simp [b,c,Y₀,Z₀,G,List.append_assoc]
  have eqH : signedDg RD Λ (A) μ c e (Z₀ ++ H) = signedDg RD Λ (A) μ c e (H ++ W₀) := by
    apply capDot_eq_congr RD Λ (A) μ (signedCapBlock_disjointRight RD Λ (A) μ L U l (V ++ R)
      (capSweepDot_chain ([] : List B) s []) d) <;>
      simp [c,e,p,Z₀,W₀,H,whisk_capSweepDot,List.append_assoc]
  have h := dotThroughMiddle RD Λ (A) μ hX hY hZ hW hF hG hH eqF eqG eqH
  have blk : signedCapBlock L (U ++ [bx s] ++ V) l R d = F ++ G ++ H := by
    rw [List.append_assoc, signedCapBlock_append]
    simp [F,G,H,p,sweepBlackLeft,List.append_assoc]
  exact capDot_bound_congr RD Λ (A) μ h (by simp [a,p,List.append_assoc]) (by simp [e,List.append_assoc])
    (by rw [blk]; simp [X₀,p,List.append_assoc])
    (by rw [blk])
    (by rw [show signedCrossings F = V.length from sweepBlackLeft_crossings ..,
      show signedCrossings H = U.length from signedCapBlock_crossings .., Nat.add_comm])

end Categorification.Stendhal.DoubleDiagram
