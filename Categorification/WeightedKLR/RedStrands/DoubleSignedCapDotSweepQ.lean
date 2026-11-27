/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotSweep
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDotCrossQ

/-! # Dot transport along a signed cap sweep

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28. The dot on a swept
leg crosses each strand in turn. Every correction loses at least one crossing.

This is the version of `DoubleSignedCapDotSweep` in which the black strands carry the relations of
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
local notation "B" => DoubleStrand I ℓ

section Passage
variable (μ : X)
local notation "D" => signedDg RD Λ P μ
local notation "fil" => signedCrossingSpan RD Λ P μ

private theorem dot_difference_trans {M : Type*} [AddCommGroup M] [Module k M]
    {S : Submodule k M} {f g h : M} (h₁ : f-g ∈ S) (h₂ : g-h ∈ S) : f-h ∈ S := by
  simpa using S.add_mem h₁ h₂

/-- Concatenate two dot slides whose local errors have one fewer crossing. -/
private theorem dotThroughPair {a b c : List B} {X Y Z F G : List (SignedLayer I ℓ)}
    (hX : signedChain a X a) (hY : signedChain b Y b) (hZ : signedChain c Z c)
    (hF : signedChain a F b) (hG : signedChain b G c) {nF nG n : ℕ}
    (eF : D a b (X ++ F) - D a b (F ++ Y) ∈ fil a b nF)
    (eG : D b c (Y ++ G) - D b c (G ++ Z) ∈ fil b c nG)
    (wF : nF + signedCrossings G = n) (wG : signedCrossings F + nG = n) :
    D a c (X ++ F ++ G) - D a c (F ++ G ++ Z) ∈ fil a c n := by
  have e₁ := signedDg_replace_span RD Λ P μ (pre := []) (show signedChain a [] a from rfl)
    (hX.append hF) (hF.append hY) hG eF
  have e₂ := signedDg_replace_span RD Λ P μ hF (hY.append hG) (hG.append hZ)
    (post := []) (show signedChain c [] c from rfl) eG
  simp only [show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl,
    Nat.zero_add, Nat.add_zero, wF, wG, List.nil_append, List.append_nil, List.append_assoc] at e₁ e₂ ⊢
  exact dot_difference_trans e₁ e₂

end Passage

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "A" => signedCapKLPresentationQ RD Λ sc P Q exponents t

/-- On a nonempty signed word, sliding the moving dot through the sweep replaces
at least one crossing by a crossing-free correction. -/
theorem capSweepDot_sweepQ (μ : X) (L U : List B) (l : Letter I) (R : List B) (hU : U ≠ []) :
    signedDg RD Λ (A) μ (L ++ U ++ [.inl l] ++ R) (L ++ [.inl l] ++ U ++ R)
      (capSweepDot (L ++ U) l R ++ sweepBlackLeft L U l R) -
    signedDg RD Λ (A) μ (L ++ U ++ [.inl l] ++ R) (L ++ [.inl l] ++ U ++ R)
      (sweepBlackLeft L U l R ++ capSweepDot L l (U ++ R)) ∈
    signedCrossingSpan RD Λ (A) μ (L ++ U ++ [.inl l] ++ R) (L ++ [.inl l] ++ U ++ R) (U.length-1) := by
  induction U generalizing L with
  | nil => exact (hU rfl).elim
  | cons x U ih =>
    by_cases hn : U = []
    · subst U
      apply capDot_bound_congr RD Λ (A) μ (capSweepDot_cross_movingQ RD Λ sc P μ L R Q exponents t x l) <;>
        simp [sweepBlackLeft,List.append_assoc]
    · let S := L ++ [x] ++ U ++ [.inl l] ++ R
      let M := L ++ [x,.inl l] ++ U ++ R
      let T := L ++ [.inl l,x] ++ U ++ R
      let f := sweepBlackLeft (L ++ [x]) U l R
      let g := crossBlackLeft L x l (U ++ R)
      let x₀ := capSweepDot ((L ++ [x]) ++ U) l R
      let x₁ := capSweepDot (L ++ [x]) l (U ++ R)
      let x₂ := capSweepDot L l (x :: (U ++ R))
      have h₀ : signedChain S x₀ S := capSweepDot_chain _ _ _
      have h₁ : signedChain M x₁ M := by
        simpa only [M,x₁,List.append_assoc,List.cons_append,List.nil_append] using
          capSweepDot_chain (L ++ [x]) l (U ++ R)
      have h₂ : signedChain T x₂ T := by
        simpa only [T,x₂,List.append_assoc,List.cons_append,List.nil_append] using
          capSweepDot_chain L l (x :: (U ++ R))
      have hf : signedChain S f M := by
        simpa only [S,M,f,List.append_assoc,List.cons_append,List.nil_append] using sweepBlackLeft_chain (L ++ [x]) U l R
      have hg : signedChain M g T := by
        simpa only [M,T,g,List.append_assoc,List.cons_append,List.nil_append] using crossBlackLeft_chain L x l (U ++ R)
      have e₀ : signedDg RD Λ (A) μ S M (x₀ ++ f) - signedDg RD Λ (A) μ S M (f ++ x₁) ∈
          signedCrossingSpan RD Λ (A) μ S M (U.length-1) := by
        apply capDot_bound_congr RD Λ (A) μ (ih (L ++ [x]) hn) <;> simp [S,M,f,x₀,x₁,List.append_assoc]
      have e₁ : signedDg RD Λ (A) μ M T (x₁ ++ g) - signedDg RD Λ (A) μ M T (g ++ x₂) ∈
          signedCrossingSpan RD Λ (A) μ M T 0 := by
        apply capDot_bound_congr RD Λ (A) μ (capSweepDot_cross_movingQ RD Λ sc P μ L (U ++ R) Q exponents t x l) <;>
          simp [M,T,g,x₁,x₂,List.append_assoc]
      have h := dotThroughPair RD Λ (A) μ h₀ h₁ h₂ hf hg e₀ e₁ (n := U.length)
        (by rw [show signedCrossings g = 1 from crossBlackLeft_crossings ..]; have := List.length_pos_iff.mpr hn; omega)
        (by rw [show signedCrossings f = U.length from sweepBlackLeft_crossings .., Nat.add_zero])
      apply capDot_bound_congr RD Λ (A) μ h <;> simp [S,T,x₀,x₂,f,g,sweepBlackLeft,List.append_assoc]

end Categorification.Stendhal.DoubleDiagram
