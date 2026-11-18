/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave
import Categorification.WeightedKLR.RedStrands.DoubleRedCup
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedPitchfork

/-!
# The upward red triple point in a signed cap sweep

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24, (4.4c), and Lemma 4.28.
The red/upward triple point commutes exactly for both placements of red
in the crossed pair, including the case of equal black colours.
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
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i j : I) (R : List (DoubleStrand I ℓ))

local notation "Pm" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
  (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))
local notation "Pp" => addMixedCupPitchforkRelations RD Λ (Pm) t
local notation "Pf" => addBlackAdjunctionRelations RD Λ (Pp)
local notation "Pc" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pf)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "e" => (Sum.inl (true,i) : DoubleStrand I ℓ)
local notation "f" => (Sum.inl (true,j) : DoubleStrand I ℓ)

private theorem liftBraid (x y : DoubleStrand I ℓ) (h : CanCross x y)
    (he : signedDg RD Λ (Pm) μ (L ++ [x,y,f] ++ R) (L ++ [f,y,x] ++ R)
          (signedCapBraidLeft L x y (true,j) R) =
        signedDg RD Λ (Pm) μ (L ++ [x,y,f] ++ R) (L ++ [f,y,x] ++ R)
          (signedCapBraidRight L x y (true,j) R)) :
    signedDg RD Λ (Pc) μ (L ++ [x,y,f] ++ R) (L ++ [f,y,x] ++ R)
        (signedCapBraidLeft L x y (true,j) R) -
      signedDg RD Λ (Pc) μ (L ++ [x,y,f] ++ R) (L ++ [f,y,x] ++ R)
        (signedCapBraidRight L x y (true,j) R) ∈
      signedCrossingSpan RD Λ (Pc) μ (L ++ [x,y,f] ++ R) (L ++ [f,y,x] ++ R) 2 := by
  have h₁ := signedCapBraidLeft_chain L h (true,j) R
  have h₂ := signedCapBraidRight_chain L h (true,j) R
  rw [signedDg_of RD Λ (Pm) μ h₁, signedDg_of RD Λ (Pm) μ h₂] at he
  rw [signedDg_of RD Λ (Pc) μ h₁, signedDg_of RD Λ (Pc) μ h₂,
    show (Pc).diag _ = (Pc).diag _ from diag_eq_addRels (Pf) (diag_eq_addRels (Pp) (diag_eq_addRels (Pm) he)),
    sub_self]
  exact Submodule.zero_mem _

/-- If red starts to the left of the two upward strands, (4.4c) solves the
required cap-sweep braid step exactly. -/
theorem signedCapBraid_redBlack_up :
    signedDg RD Λ (Pc) μ (L ++ [red,e,f] ++ R) (L ++ [f,e,red] ++ R)
        (signedCapBraidLeft L red e (true,j) R) -
      signedDg RD Λ (Pc) μ (L ++ [red,e,f] ++ R) (L ++ [f,e,red] ++ R)
        (signedCapBraidRight L red e (true,j) R) ∈
      signedCrossingSpan RD Λ (Pc) μ (L ++ [red,e,f] ++ R) (L ++ [f,e,red] ++ R) 2 := by
  exact liftBraid RD Λ P Q exponents t μ L j R red e trivial (upRedLeft RD Λ P μ L r i j R)

/-- If red starts between the upward strands, the middle red triple-point
identity solves the required cap-sweep braid step exactly. -/
theorem signedCapBraid_blackRed_up :
    signedDg RD Λ (Pc) μ (L ++ [e,red,f] ++ R) (L ++ [f,red,e] ++ R)
        (signedCapBraidLeft L e red (true,j) R) -
      signedDg RD Λ (Pc) μ (L ++ [e,red,f] ++ R) (L ++ [f,red,e] ++ R)
        (signedCapBraidRight L e red (true,j) R) ∈
      signedCrossingSpan RD Λ (Pc) μ (L ++ [e,red,f] ++ R) (L ++ [f,red,e] ++ R) 2 := by
  exact liftBraid RD Λ P Q exponents t μ L j R e red trivial (upRedMiddle RD Λ P μ L r i j R)

end Categorification.Stendhal.DoubleDiagram
