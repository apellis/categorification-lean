/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotSweep
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBare

/-! # Dots on the swept cap leg

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28, using KL III
Proposition 3.11. At the end of the signed sweep, cyclicity transfers the
dot from the moving leg to the decoration on the bare cap.
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
variable (μ : X)
local notation "D" => signedDg RD Λ (A) μ

/-- A moving-leg dot directly below a bare cap adds exactly one decoration. -/
theorem signedCapBlock_dotRight_nil (L : List B) (l : Letter I) (R : List B) (d : ℕ) :
    D (L ++ [bx l.dual,bx l] ++ R) (L ++ R) (capSweepDot (L ++ [bx l.dual]) l R ++ signedCapBlock L [] l R d) =
      D (L ++ [bx l.dual,bx l] ++ R) (L ++ R) (signedCapBlock L [] l R (d+1)) := by
  let S := L ++ [bx l.dual,bx l] ++ R
  let X₀ := capSweepDot (L ++ [bx l.dual]) l R
  have hd : signedChain S X₀ S := by
    simpa [S,X₀,List.append_assoc] using capSweepDot_chain (L ++ [bx l.dual]) l R
  have cap (d : ℕ) : signedChain S (signedCapBlock L [] l R d) (L ++ R) := by
    simpa [S,List.append_assoc] using signedCapBlock_chain L ([] : List B) l R d
  have eqv := signedCapDotRight_eq RD Λ (A) (signedCapKL_reflectedBlack RD Λ P Q exponents t) μ L l R
  have moved := signedDg_replace RD Λ (A) μ X₀ _ _ [] hd (show signedChain (L ++ R) [] (L ++ R) from rfl)
    (cap d) (signedCapDotRight_chain L l R d) (eqv d).symm
  simp only [List.append_nil] at moved
  refine moved.trans ?_
  exact (show X₀ ++ signedCapDotRight L l R d = signedCapDotRight L l R (d+1) from by
    simp [X₀,capSweepDot,signedCapDotRight,List.replicate_succ]).symm ▸ eqv (d+1)

/-- A dot on the moving cap leg adds a decoration modulo strictly fewer
crossings when the interior is nonempty. The empty-interior equality is
`signedCapBlock_dotRight_nil`. -/
theorem signedCapBlock_dotRight (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    D (L ++ [bx l.dual] ++ U ++ [bx l] ++ R) (L ++ U ++ R)
      (capSweepDot (L ++ [bx l.dual] ++ U) l R ++ signedCapBlock L U l R d) -
    D (L ++ [bx l.dual] ++ U ++ [bx l] ++ R) (L ++ U ++ R) (signedCapBlock L U l R (d+1)) ∈
    signedCrossingSpan RD Λ (A) μ (L ++ [bx l.dual] ++ U ++ [bx l] ++ R) (L ++ U ++ R) (U.length-1) := by
  by_cases hn : U = []
  · subst U
    have eqv := signedCapBlock_dotRight_nil RD Λ P Q exponents t μ L l R d
    have h : D (L ++ [bx l.dual] ++ [] ++ [bx l] ++ R) (L ++ [] ++ R)
        (capSweepDot (L ++ [bx l.dual] ++ []) l R ++ signedCapBlock L [] l R d) =
        D (L ++ [bx l.dual] ++ [] ++ [bx l] ++ R) (L ++ [] ++ R) (signedCapBlock L [] l R (d+1)) := by
      apply capDot_eq_congr RD Λ (A) μ eqv <;> simp [List.append_assoc]
    rw [h,sub_self]
    exact Submodule.zero_mem _
  let S := L ++ [bx l.dual] ++ U ++ [bx l] ++ R
  let M := L ++ [bx l.dual,bx l] ++ (U ++ R)
  let T := L ++ (U ++ R)
  let F := sweepBlackLeft (L ++ [bx l.dual]) U l R
  let H (n : ℕ) := signedCapBlock L [] l (U ++ R) n
  let X₀ := capSweepDot (L ++ [bx l.dual] ++ U) l R
  let X₁ := capSweepDot (L ++ [bx l.dual]) l (U ++ R)
  have h₀ : signedChain S X₀ S := capSweepDot_chain _ _ _
  have h₁ : signedChain M X₁ M := by
    simpa [M,X₁,List.append_assoc] using capSweepDot_chain (L ++ [bx l.dual]) l (U ++ R)
  have hf : signedChain S F M := by
    simpa [S,M,F,List.append_assoc] using sweepBlackLeft_chain (L ++ [bx l.dual]) U l R
  have hh (n : ℕ) : signedChain M (H n) T := by
    simpa [M,H,T,List.append_assoc] using signedCapBlock_chain L ([] : List B) l (U ++ R) n
  have ex : D S M (X₀ ++ F) - D S M (F ++ X₁) ∈ signedCrossingSpan RD Λ (A) μ S M (U.length-1) := by
    apply capDot_bound_congr RD Λ (A) μ (capSweepDot_sweep RD Λ P Q exponents t μ (L ++ [bx l.dual]) U l R hn) <;>
      simp [S,M,F,X₀,X₁,List.append_assoc]
  have h := signedDg_replace_span RD Λ (A) μ (pre := []) (show signedChain S [] S from rfl)
    (h₀.append hf) (hf.append h₁) (hh d) ex
  have eqv := signedCapBlock_dotRight_nil RD Λ P Q exponents t μ L l (U ++ R) d
  have moved := signedDg_replace RD Λ (A) μ F _ _ [] hf (show signedChain T [] T from rfl)
    (h₁.append (hh d)) (hh (d+1)) eqv
  simp only [List.append_nil] at moved
  have hc : signedCrossings (H d) = 0 := signedCapBlock_crossings ..
  simp only [show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl,
    Nat.zero_add,hc,Nat.add_zero,List.nil_append,List.append_assoc] at h
  rw [moved] at h
  have blk (n : ℕ) : signedCapBlock L U l R n = F ++ H n := by
    simp [F,H,signedCapBlock,capLegDots,sweepBlackLeft,List.append_assoc]
  apply capDot_bound_congr RD Λ (A) μ h <;> simp [S,T,X₀,blk,List.append_assoc]

end Categorification.Stendhal.DoubleDiagram
