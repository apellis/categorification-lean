/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCrossFirst
import Categorification.WeightedKLR.RedStrands.DoubleRedCapPitchforkQ
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapPitchforkQ
import Categorification.WeightedKLR.RedStrands.DoubleSignedCrossingBigonQ
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCrossFirstUnits

/-!
# The stationary-end crossing positions in the common signed presentation

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. The two positions at the
stationary end of the cap block use a zero-crossing pitchfork correction.
The red pitchfork is exact; the black one uses reflected KL III relations.

This is the version of `DoubleSignedCapCrossing` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (t : I → I → k)

local notation "B" => DoubleStrand I ℓ
local notation "bl(" z ")" => (Sum.inl z : B)
local notation "capP" => signedCapKLPresentationQ RD Λ sc P Q exponents t
local notation "D" => signedDg RD Λ (capP) μ
local notation "F" => signedCrossingSpan RD Λ (capP) μ

/-- The dotted cap pitchfork has crossing bound zero, up to a unit, for every signed
through-strand. -/
theorem signedCapKL_capPitchQ (L : List B) (x : B) (l : Letter I) (R : List B) (d : ℕ) :
    let a := L ++ [bl(l.dual),x,bl(l)] ++ R
    let b := L ++ [x] ++ R
    ∃ c : kˣ, (D) a b (signedCapPitchLeft L x l R d) - (c : k) • (D) a b (signedCapPitchRight L x l R d) ∈
      (F) a b 0 := by
  cases x with
  | inl m =>
    exact signedCapPitch_blackQ RD Λ sc (capP) μ L l R d
      (signedCapKL_reflectedBlackQ RD Λ sc P Q exponents t) m
  | inr r =>
    refine ⟨1, ?_⟩
    rw [signedCapPitch_redQ RD Λ sc P μ L l R d Q exponents t r, Units.val_one, one_smul, sub_self]
    exact Submodule.zero_mem _

/-- A preceding crossing entering at the left extends the intervening word,
with a strictly smaller crossing correction. -/
theorem signedCapKL_capBlock_enterLeftQ (L U R : List B) (x : B) (l : Letter I) (d : ℕ) :
    let a := L ++ [bl(l.dual),x] ++ U ++ [bl(l)] ++ R
    let b := L ++ [x] ++ (U ++ R)
    ∃ c : kˣ, (D) a b (signedCrossLayers L bl(l.dual) x (U ++ [bl(l)] ++ R) ++
        signedCapBlock (L ++ [x]) U l R d) -
      (c : k) • (D) a b (signedCapBlock L (x :: U) l R d) ∈ (F) a b U.length := by
  obtain ⟨c, hc⟩ := signedCapKL_capPitchQ RD Λ sc P μ Q exponents t L x l (U ++ R) d
  exact ⟨c, signedCapBlock_enterLeft_of_pitch_smul RD Λ (capP) μ L U R x l d c hc⟩

/-- A preceding crossing of the stationary leg with the first interior
strand is a strictly lower term. -/
theorem signedCapKL_capBlock_crossFirstQ (L U R : List B) (x : B) (l : Letter I) (d : ℕ) :
    let a := L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R
    let b := L ++ [x] ++ (U ++ R)
    (D) a b (signedCrossLayers L x bl(l.dual) (U ++ [bl(l)] ++ R) ++
        signedCapBlock L (x :: U) l R d) ∈ (F) a b (U.length + 1) := by
  obtain ⟨c, hc⟩ := signedCapKL_capPitchQ RD Λ sc P μ Q exponents t L x l (U ++ R) d
  apply signedCapBlock_crossFirst_of_pitch_smul RD Λ (capP) μ L U R x l d c hc
  have hc : CanCross x bl(l.dual) := by cases x <;> trivial
  have h := signedCapKL_bigonQ RD Λ sc P μ L (U ++ [bl(l)] ++ R) Q exponents t x bl(l.dual) hc
  dsimp only at h ⊢
  rw [show L ++ [x,bl(l.dual)] ++ (U ++ [bl(l)] ++ R) = L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R by
    simp [List.append_assoc]] at h
  exact h

end Categorification.Stendhal.DoubleDiagram
