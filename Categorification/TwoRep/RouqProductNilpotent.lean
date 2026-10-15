/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqProduct

/-!
# Nilpotent dots in the product of two Rouquier families

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. The representations `X^{μ₊, μ₋}` are realized as
`RouqFamily.homProduct W T`, and the action of `g` on them uses power series in the dots. Those
series are finite when the dots are nilpotent on each 1-morphism. If the dots of `W` and `T`
are nilpotent on each 1-morphism, so are those of `homProduct W T`
(`RouqFamily.homProduct_dot_nilpotent`). The dots of `homProduct W T` are images of the dots of
`W` and `T` under postcomposition functors, transported along equalities of weights.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u u₁

namespace RouqFamily

open Yoneda QuantumGroup UDot

variable (k : Type w') [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type u₁} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₁ : WeightDatum C₁ X₁ Y₁} {RD₂ : WeightDatum C₂ X₂ Y₂}
  (W : RouqFamily (B := B) RD₁) (T : RouqFamily (B := B) RD₂)

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem yMap₂_zero (y : B) {a b : B} {f : a ⟶ b} : yMap₂ k y (0 : f ⟶ f) = 0 :=
  (yFun k y a b).map_zero _ _

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem powComp_endCast {x z z' : X₁ × X₂} (e : z = z')
    {f : homObj k W T x ⟶ homObj k W T z} (d : f ⟶ f) (n : ℕ) :
    powComp (endCast e d) n = endCast e (powComp d n) := by
  subst e
  rfl

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem endCast_zero {x z z' : X₁ × X₂} (e : z = z') {f : homObj k W T x ⟶ homObj k W T z} :
    endCast e (0 : f ⟶ f) = 0 := by
  subst e
  rfl

/-- **The dots of `homProduct W T` are nilpotent** on each 1-morphism when those of `W` and `T`
are. -/
theorem homProduct_dot_nilpotent
    (hW : ∀ (i : I₁) {x y : X₁} (h : x + RD₁.iX i = y), ∃ N : ℕ, powComp (W.dot i h) N = 0)
    (hT : ∀ (i : I₂) {x y : X₂} (h : x + RD₂.iX i = y), ∃ N : ℕ, powComp (T.dot i h) N = 0) :
    ∀ (c : I₁ ⊕ I₂) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX c = y),
      ∃ N : ℕ, powComp ((homProduct k W T).dot c h) N = 0
  | .inl i, x, y, h => by
    obtain ⟨N, hN⟩ := hW i (fst_step (RD₂ := RD₂) (y := y) i h)
    refine ⟨N, ?_⟩
    change powComp (endCast (snd_eq i h)
      ((leftFamily k W T x.2).dot i (fst_step (RD₂ := RD₂) (y := y) i h))) N = 0
    erw [powComp_endCast]
    change endCast (snd_eq i h) (powComp (yMap₂ k (T.obj (-x.2))
      (W.dot i (fst_step (RD₂ := RD₂) (y := y) i h))) N) = 0
    rw [← yMap₂_powComp, hN, yMap₂_zero, endCast_zero]
  | .inr i, x, y, h => by
    obtain ⟨N, hN⟩ := hT i (neg_reg i (snd_step (RD₁ := RD₁) (y := y) i h))
    refine ⟨N, ?_⟩
    change powComp (endCast (fst_eq i h)
      ((rightFamily k W T x.1).dot i (snd_step (RD₁ := RD₁) (y := y) i h))) N = 0
    erw [powComp_endCast]
    change endCast (fst_eq i h) (powComp (yMap₂ k (HOp.mk (W.obj x.1))
      (T.reverse.dot i (snd_step (RD₁ := RD₁) (y := y) i h))) N) = 0
    erw [← yMap₂_powComp]
    change endCast (fst_eq i h) (yMap₂ k (HOp.mk (W.obj x.1))
      (show T.E i (neg_reg i (snd_step (RD₁ := RD₁) (y := y) i h)) ⟶ _ from
        powComp (T.dot i (neg_reg i (snd_step (RD₁ := RD₁) (y := y) i h))) N)) = 0
    rw [hN]
    erw [yMap₂_zero]
    rw [endCast_zero]

end RouqFamily

end Categorification.TwoRep
