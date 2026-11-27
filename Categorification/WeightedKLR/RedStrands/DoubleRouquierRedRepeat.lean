/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRed
import Categorification.WeightedKLR.RedStrands.DoubleDownRedRed

/-!
# Downward relations with two red strands in a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25. The red labels `Fin ℓ` of the double
signature index the tensor factors of `λ = (λ₁, …, λ_ℓ)`, so a 1-morphism of `𝒯` that meets
the red line `r` twice does not occur in the target of the representation: a representation
in which red lines act by `I^λ` kills the words with a red label twice (`RepeatedRedZero`).

The downward KLR relations of `addDownRelations` with at least two red strands then hold in
the double model: those in which two red strands of distinct colours cross translate to zero
as diagrams (`DoubleDownRedRed`), and the others end at a word with a red label twice
(`admissibleMap_downRelation_of_two_red`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

variable {I : Type u} [DecidableEq I] {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))

omit [DecidableEq I] in
theorem colours_map_snd (μ : X) (w : List (DoubleStrand I ℓ)) :
    (colours RD Λ μ w).map Prod.snd = w := by
  induction w generalizing μ with
  | nil => rfl
  | cons a w ih => simp [colours, ih]

/-- **Words with a red label twice vanish**: the identity of the image of every word in which
some red label occurs at least twice is zero. -/
def RepeatedRedZero : Prop :=
  ∀ (x y : X) (w : List (DoubleStrand I ℓ))
    (h₁ : (signature RD Λ).ok x (colours RD Λ x w))
    (h₂ : (signature RD Λ).endR x (colours RD Λ x w) = y) (s : Fin ℓ),
    2 ≤ w.countP (· = .inr s) → 𝟙 ((doubleModel S red).word x (colours RD Λ x w) y h₁ h₂) = 0

variable {S red}

omit [AdditiveWhiskering B] in
/-- A linear diagram ending at a downward word with a red label twice has image zero. -/
theorem admissibleMap_down_eq_zero_of_repeated (hrep : RepeatedRedZero S red)
    (G : GenImg (doubleModel S red)) (m : X) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    {x y : X} (ha : Cond x y (downContextObj RD Λ m [] [] a))
    (hb : Cond x y (downContextObj RD Λ m [] [] b))
    (f : LinDiagram k (downContextObj RD Λ m [] [] a) (downContextObj RD Λ m [] [] b))
    (s : Fin ℓ) (h : 2 ≤ b.word.countP (· = .inr s)) :
    admissibleMap G ha hb f = 0 := by
  obtain rfl : m = x := ha.2.2
  have hc : 2 ≤ ([] ++ b.word.map DoubleStrand.down ++ []).countP
      (· = (.inr s : DoubleStrand I ℓ)) := by
    rw [List.nil_append, List.append_nil, List.countP_map]
    refine le_trans h (le_of_eq (List.countP_congr fun c _ => ?_))
    rcases c with c | c <;> simp [DoubleStrand.down]
  rw [← Category.comp_id (admissibleMap G ha hb f)]
  erw [hrep m y _ hb.1 hb.2.1 s hc, Limits.comp_zero]

omit [AdditiveWhiskering B] in
/-- **The downward relations with at least two red strands.** If the words with a red label
twice vanish and the polynomials of two red colours have no constant term, every downward KLR
relation with at least two red strands has image zero. -/
theorem admissibleMap_downRelation_of_two_red (hrep : RepeatedRedZero S red)
    (G : GenImg (doubleModel S red)) (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hQ : ∀ s t : Fin ℓ, MvPolynomial.constantCoeff (Q (.inr s) (.inr t)) = 0) (m : X)
    (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) (hr : 2 ≤ r.dom.word.countP (fun c => c.isRight))
    {x y : X} (ha : Cond x y (downContextObj RD Λ m [] [] r.dom))
    (hb : Cond x y (downContextObj RD Λ m [] [] r.cod)) :
    admissibleMap G ha hb (downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q r)) = 0 := by
  have zero : downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q r) = 0 →
      admissibleMap G ha hb (downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q r)) = 0 :=
    fun h => by rw [h, map_zero]
  have rep : ∀ s : Fin ℓ, 2 ≤ r.cod.word.countP (· = .inr s) →
      admissibleMap G ha hb (downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q r)) = 0 :=
    fun s h => admissibleMap_down_eq_zero_of_repeated hrep G m ha hb _ s h
  cases r with
  | sqEq c =>
    rcases c with c | s
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact rep s (by simp [KLR.Diagram.Rel.cod])
  | sqNe c d h =>
    rcases c with c | s <;> rcases d with d | t
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact zero (downLinear_relation_sqNe_red RD Λ k m [] [] Q s t h (hQ s t))
  | slideLEq c =>
    rcases c with c | s
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact rep s (by simp [KLR.Diagram.Rel.cod])
  | slideLNe c d h =>
    rcases c with c | s <;> rcases d with d | t
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact zero (downLinear_relation_slideLNe_red RD Λ k m [] [] Q s t h)
  | slideREq c =>
    rcases c with c | s
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact rep s (by simp [KLR.Diagram.Rel.cod])
  | slideRNe c d h =>
    rcases c with c | s <;> rcases d with d | t
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact zero (downLinear_relation_slideRNe_red RD Λ k m [] [] Q s t h)
  | braid c d e h =>
    rcases c with c | s <;> rcases d with d | t <;> rcases e with e | t'
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact zero (downLinear_relation_braid_red₂₃ RD Λ k m [] [] Q _ t t' h)
    · simp [KLR.Diagram.Rel.dom] at hr
    · exact zero (downLinear_relation_braid_red₁₃ RD Λ k m [] [] Q s t' _ h)
    · exact zero (downLinear_relation_braid_red₁₂ RD Λ k m [] [] Q s t _ h)
    · exact zero (downLinear_relation_braid_red₁₂ RD Λ k m [] [] Q s t _ h)
  | braidQ c d h =>
    rcases c with c | s
    · rcases d with d | t
      · simp [KLR.Diagram.Rel.dom] at hr
      · simp [KLR.Diagram.Rel.dom] at hr
    · exact rep s (by simp [KLR.Diagram.Rel.cod])

end Categorification.Stendhal.DoubleDiagram
