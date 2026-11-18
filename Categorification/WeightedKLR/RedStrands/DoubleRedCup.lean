/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedCap
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations
import Categorification.WeightedKLR.RedStrands.AffineCover
import Categorification.KLR.BaseChange

/-!
# Red crossings, cups, and downward bigons

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.24 and the proof of Theorem 4.25. The cup equation is the
unit form of the red-crossing mate in that proof. The downward red/black
bigons are the images of the ordinary Stendhal relation (4.2).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)

/-- Create a black pair on the left, then cross its right end past the red strand. -/
def redCupLeft (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ [.inr r] ++ v) ⟶ obj RD Λ μ (u ++ [.inl l, .inr r, .inl l.dual] ++ v) :=
  let d := moveDiagram RD Λ μ u (.black (.cup l)) (.inr r :: v)
  let e := moveDiagram RD Λ μ (u ++ [.inl l]) (.blackRed l.dual r) v
  let mid := obj RD Λ μ (u ++ [.inl l, .inl l.dual, .inr r] ++ v)
  Diagram.cast (b' := mid) d (by simp [List.append_assoc, Move.bottom])
    (by simp [mid, List.append_assoc, Move.top]) ≫
  Diagram.cast e (by simp [mid, List.append_assoc, Move.bottom])
    (by simp [List.append_assoc, Move.top])

/-- Create a black pair on the right, then cross its left end past the red strand. -/
def redCupRight (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ)) :
    obj RD Λ μ (u ++ [.inr r] ++ v) ⟶ obj RD Λ μ (u ++ [.inl l, .inr r, .inl l.dual] ++ v) :=
  let d := moveDiagram RD Λ μ (u ++ [.inr r]) (.black (.cup l)) v
  let e := moveDiagram RD Λ μ u (.redBlack r l) (.inl l.dual :: v)
  let mid := obj RD Λ μ (u ++ [.inr r, .inl l, .inl l.dual] ++ v)
  Diagram.cast (b' := mid) d (by simp [Move.bottom])
    (by simp [mid, List.append_assoc, Move.top]) ≫
  Diagram.cast e (by simp [mid, List.append_assoc, Move.bottom])
    (by simp [List.append_assoc, Move.top])

variable {k : Type w} [CommRing k]

/-- Adjoin the unit form of the red/cup mate equations from the proof of Webster's
Theorem 4.25. Both orientations use the same formula. -/
def addRedCupRelations (P : Presentation.{w, max u v₁} (signature RD Λ) k) :
    Presentation.{w, max u v₁} (signature RD Λ) k :=
  P.addRels (RedCapRelation X I ℓ)
    (fun a => obj RD Λ a.leftWeight (a.left ++ [.inr a.red] ++ a.right))
    (fun a => obj RD Λ a.leftWeight (a.left ++ [.inl a.black, .inr a.red, .inl a.black.dual] ++ a.right))
    (fun a => LinDiagram.of (redCupLeft RD Λ a.leftWeight a.left a.black a.red a.right) -
      LinDiagram.of (redCupRight RD Λ a.leftWeight a.left a.black a.red a.right))

/-- The straddled form of the red/cup mate equation in the presented category. -/
theorem redCup_slide (P : Presentation.{w, max u v₁} (signature RD Λ) k)
    (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ)) :
    (addRedCupRelations RD Λ P).diag (redCupLeft RD Λ μ u l r v) =
      (addRedCupRelations RD Λ P).diag (redCupRight RD Λ μ u l r v) :=
  (addRedCupRelations RD Λ P).diag_eq_of_rel (.inr ⟨μ, u, l, r, v⟩) rfl

section Bigons

open KLR.Diagram
open scoped Matrix

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v₁} (signature RD Λ) k)

local notation "R" => affineCoverQ Q exponents
local notation "P₀" => KLR.Diagram.pres k R
local notation "P₁" => addDownRelations RD Λ R P

/-- A dot on the black strand of a red/black pair with red on the left. -/
def redDownDotRedLeft (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) : End (obj RD Λ μ (u ++ [.inr r, .inl (false, i)] ++ v)) :=
  Diagram.cast (moveDiagram RD Λ μ (u ++ [.inr r]) (.black (.dot (false, i))) v)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

/-- A dot on the black strand of a black/red pair with black on the left. -/
def redDownDotBlackLeft (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) : End (obj RD Λ μ (u ++ [.inl (false, i), .inr r] ++ v)) :=
  Diagram.cast (moveDiagram RD Λ μ u (.black (.dot (false, i))) (.inr r :: v))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private theorem ncEval_two_X_pow {A : Type*} [Ring A] [Algebra k A]
    (a : Fin 2 → A) (j : Fin 2) (n : ℕ) :
    KLR.ncEval a (MvPolynomial.X j ^ n : MvPolynomial (Fin 2) k) = a j ^ n := by
  rw [MvPolynomial.X_pow_eq_monomial, KLR.ncEval_monomial, map_one, one_mul]
  fin_cases j <;> simp [List.ofFn_succ, Finsupp.single_apply]

private theorem klr_bigon_power (c d : I ⊕ Fin ℓ) (h : c ≠ d) (j : Fin 2) (n : ℕ)
    (hp : R c d = MvPolynomial.X j ^ n) :
    (P₀).diag (X2 c d ≫ X2 d c) = End.of ((P₀).diag (![D0 c d, D1 c d] j)) ^ n := by
  let z : End (Free.of k (ob [c, d])) := LinDiagram.of (X2 c d ≫ X2 d c)
  let ys : Fin 2 → End (Free.of k (ob [c, d])) := fun t => LinDiagram.of (![D0 c d, D1 c d] t)
  have hrel := (P₀).lin_rel_self (.sqNe c d h)
  change (P₀).lin (z - KLR.ncEval ys (R c d)) = 0 at hrel
  rw [Presentation.lin_sub, sub_eq_zero, hp, ncEval_two_X_pow] at hrel
  refine hrel.trans ?_
  exact map_pow ((P₀).linAlgHom _) _ _

private theorem diag_translate_layer (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (sig (I ⊕ Fin ℓ))) (hv : L.Valid)
    {a b : Obj (sig (I ⊕ Fin ℓ))} (ha : L.dom = a) (hb : L.cod = b)
    {g : Move I ℓ} (hg : downMove L.gen = some g)
    (f : downContextObj RD Λ μ u v a ⟶ downContextObj RD Λ μ u v b)
    (hf : Diagram.layers f = [layer RD Λ μ (u ++ L.left.map DoubleStrand.down)
      g (L.right.map DoubleStrand.down ++ v)]) :
    (downPresentedFunctor RD Λ R P μ u v).map ((P₀).diag (Diagram.layer L hv ha hb)) =
      (P₁).diag f := by
  rw [downPresentedFunctor_layer RD Λ R P μ u v L hv ha hb hg]
  apply (P₁).diag_eq_of_layers_eq
  rw [Diagram.layers_cast, layers_downLayerDiagram, hf]

private theorem redDown_map_cross_redLeft (μ : X) (u v : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (i : I) :
    (downPresentedFunctor RD Λ R P μ u v).map ((P₀).diag (X2 (.inr r) (.inl i))) =
      (P₁).diag (moveDiagram RD Λ μ u (.redBlack r (false, i)) v) := by
  apply diag_translate_layer RD Λ Q exponents P μ u v _ _ _ _ rfl
  change [_] = [_]
  simp

private theorem redDown_map_cross_blackLeft (μ : X) (u v : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (i : I) :
    (downPresentedFunctor RD Λ R P μ u v).map ((P₀).diag (X2 (.inl i) (.inr r))) =
      (P₁).diag (moveDiagram RD Λ μ u (.blackRed (false, i) r) v) := by
  apply diag_translate_layer RD Λ Q exponents P μ u v _ _ _ _ rfl
  change [_] = [_]
  simp

private theorem redDown_map_dot_redLeft (μ : X) (u v : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (i : I) :
    (downPresentedFunctor RD Λ R P μ u v).map ((P₀).diag (D1 (.inr r) (.inl i))) =
      (P₁).diag (redDownDotRedLeft RD Λ μ u r i v) := by
  apply diag_translate_layer RD Λ Q exponents P μ u v _ _ _ _ rfl
  change [_] = [_]
  simp [DoubleStrand.down]

private theorem redDown_map_dot_blackLeft (μ : X) (u v : List (DoubleStrand I ℓ))
    (r : Fin ℓ) (i : I) :
    (downPresentedFunctor RD Λ R P μ u v).map ((P₀).diag (D0 (.inl i) (.inr r))) =
      (P₁).diag (redDownDotBlackLeft RD Λ μ u r i v) := by
  apply diag_translate_layer RD Λ Q exponents P μ u v _ _ _ _ rfl
  change [_] = [_]
  simp [DoubleStrand.down]

/-- Webster's downward red/black bigon (4.2) with the red strand initially on the left. -/
theorem redDown_bigon_redLeft (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) :
    (P₁).diag (moveDiagram RD Λ μ u (.redBlack r (false, i)) v ≫
      moveDiagram RD Λ μ u (.blackRed (false, i) r) v) =
      End.of ((P₁).diag (redDownDotRedLeft RD Λ μ u r i v)) ^ exponents r i := by
  let F := downPresentedFunctor RD Λ R P μ u v
  have h := congrArg (F.mapEnd (X := (P₀).obj (ob [.inr r, .inl i])))
    (klr_bigon_power Q exponents (.inr r) (.inl i) Sum.inr_ne_inl 1 (exponents r i) rfl)
  rw [map_pow] at h
  simpa only [F, Functor.mapEnd_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    Presentation.diag_comp, Functor.map_comp, redDown_map_cross_redLeft,
    redDown_map_cross_blackLeft, redDown_map_dot_redLeft] using h

/-- Webster's downward black/red bigon (4.2) with the black strand initially on the left. -/
theorem redDown_bigon_blackLeft (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) :
    (P₁).diag (moveDiagram RD Λ μ u (.blackRed (false, i) r) v ≫
      moveDiagram RD Λ μ u (.redBlack r (false, i)) v) =
      End.of ((P₁).diag (redDownDotBlackLeft RD Λ μ u r i v)) ^ exponents r i := by
  let F := downPresentedFunctor RD Λ R P μ u v
  have h := congrArg (F.mapEnd (X := (P₀).obj (ob [.inl i, .inr r])))
    (klr_bigon_power Q exponents (.inl i) (.inr r) Sum.inl_ne_inr 0 (exponents r i) rfl)
  rw [map_pow] at h
  simpa only [F, Functor.mapEnd_apply, Matrix.cons_val_zero, Presentation.diag_comp,
    Functor.map_comp, redDown_map_cross_redLeft, redDown_map_cross_blackLeft,
    redDown_map_dot_blackLeft] using h

/-- A downward black dot slides through the crossing that moves it to the left of red. -/
theorem redDown_dot_slide_redLeft (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) :
    (P₁).diag (moveDiagram RD Λ μ u (.redBlack r (false, i)) v) ≫
      (P₁).diag (redDownDotBlackLeft RD Λ μ u r i v) =
    (P₁).diag (redDownDotRedLeft RD Λ μ u r i v) ≫
      (P₁).diag (moveDiagram RD Λ μ u (.redBlack r (false, i)) v) := by
  let red : I ⊕ Fin ℓ := .inr r
  let black : I ⊕ Fin ℓ := .inl i
  have h := (P₀).lin_rel_self (.slideLNe red black Sum.inr_ne_inl)
  change (P₀).lin (LinDiagram.of (X2 red black ≫ D0 black red) -
    LinDiagram.of (D1 red black ≫ X2 red black)) = 0 at h
  rw [Presentation.lin_sub, sub_eq_zero, Presentation.lin_of, Presentation.lin_of] at h
  simpa only [red, black, Presentation.diag_comp, Functor.map_comp, redDown_map_cross_redLeft,
    redDown_map_dot_blackLeft, redDown_map_dot_redLeft] using
    congrArg (downPresentedFunctor RD Λ R P μ u v).map h

/-- A downward black dot slides through the crossing that moves it to the right of red. -/
theorem redDown_dot_slide_blackLeft (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I)
    (v : List (DoubleStrand I ℓ)) :
    (P₁).diag (moveDiagram RD Λ μ u (.blackRed (false, i) r) v) ≫
      (P₁).diag (redDownDotRedLeft RD Λ μ u r i v) =
    (P₁).diag (redDownDotBlackLeft RD Λ μ u r i v) ≫
      (P₁).diag (moveDiagram RD Λ μ u (.blackRed (false, i) r) v) := by
  let red : I ⊕ Fin ℓ := .inr r
  let black : I ⊕ Fin ℓ := .inl i
  have h := (P₀).lin_rel_self (.slideRNe black red Sum.inl_ne_inr)
  change (P₀).lin (LinDiagram.of (D0 black red ≫ X2 black red) -
    LinDiagram.of (X2 black red ≫ D1 red black)) = 0 at h
  rw [Presentation.lin_sub, sub_eq_zero, Presentation.lin_of, Presentation.lin_of] at h
  simpa only [red, black, Presentation.diag_comp, Functor.map_comp, redDown_map_cross_blackLeft,
    redDown_map_dot_blackLeft, redDown_map_dot_redLeft] using
    congrArg (downPresentedFunctor RD Λ R P μ u v).map h.symm

end Bigons

end Categorification.Stendhal.DoubleDiagram
