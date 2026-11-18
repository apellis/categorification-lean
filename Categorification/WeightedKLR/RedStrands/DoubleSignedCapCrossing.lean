/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCrossFirst
import Categorification.WeightedKLR.RedStrands.DoubleRedCapPitchfork

/-!
# The stationary-end crossing positions in the common signed presentation

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. The two positions at the
stationary end of the cap block use a zero-crossing pitchfork correction.
The red pitchfork is exact; the black one uses reflected KL III relations.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (t : I → I → k)

local notation "B" => DoubleStrand I ℓ
local notation "bl(" z ")" => (Sum.inl z : B)
local notation "capP" => signedCapKLPresentation RD Λ P Q exponents t
local notation "D" => signedDg RD Λ (capP) μ
local notation "F" => signedCrossingSpan RD Λ (capP) μ

/-- The dotted cap pitchfork has crossing bound zero for every signed
through-strand. -/
theorem signedCapKL_capPitch (L : List B) (x : B) (l : Letter I) (R : List B) (d : ℕ) :
    let a := L ++ [bl(l.dual),x,bl(l)] ++ R
    let b := L ++ [x] ++ R
    (D) a b (signedCapPitchLeft L x l R d) - (D) a b (signedCapPitchRight L x l R d) ∈
      (F) a b 0 := by
  cases x with
  | inl m =>
    exact signedCapPitch_black RD Λ (capP) μ L l R d
      (signedCapKL_reflectedBlack RD Λ P Q exponents t) m
  | inr r =>
    dsimp only
    rw [signedCapPitch_red RD Λ P μ L l R d Q exponents t r, sub_self]
    exact Submodule.zero_mem _

/-- A preceding crossing entering at the left extends the intervening word,
with a strictly smaller crossing correction. -/
theorem signedCapKL_capBlock_enterLeft (L U R : List B) (x : B) (l : Letter I) (d : ℕ) :
    let a := L ++ [bl(l.dual),x] ++ U ++ [bl(l)] ++ R
    let b := L ++ [x] ++ (U ++ R)
    (D) a b (signedCrossLayers L bl(l.dual) x (U ++ [bl(l)] ++ R) ++
        signedCapBlock (L ++ [x]) U l R d) -
      (D) a b (signedCapBlock L (x :: U) l R d) ∈ (F) a b U.length :=
  signedCapBlock_enterLeft_of_pitch RD Λ (capP) μ L U R x l d
    (signedCapKL_capPitch RD Λ P μ Q exponents t L x l (U ++ R) d)

/-- A preceding crossing of the stationary leg with the first interior
strand is a strictly lower term. -/
theorem signedCapKL_capBlock_crossFirst (L U R : List B) (x : B) (l : Letter I) (d : ℕ) :
    let a := L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R
    let b := L ++ [x] ++ (U ++ R)
    (D) a b (signedCrossLayers L x bl(l.dual) (U ++ [bl(l)] ++ R) ++
        signedCapBlock L (x :: U) l R d) ∈ (F) a b (U.length + 1) := by
  apply signedCapBlock_crossFirst_of_pitch RD Λ (capP) μ L U R x l d
    (signedCapKL_capPitch RD Λ P μ Q exponents t L x l (U ++ R) d)
  have hc : CanCross x bl(l.dual) := by cases x <;> trivial
  have h := signedCapKL_bigon RD Λ P μ L (U ++ [bl(l)] ++ R) Q exponents t x bl(l.dual) hc
  dsimp only at h ⊢
  rw [show L ++ [x,bl(l.dual)] ++ (U ++ [bl(l)] ++ R) = L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R by
    simp [List.append_assoc]] at h
  exact h

end Categorification.Stendhal.DoubleDiagram
