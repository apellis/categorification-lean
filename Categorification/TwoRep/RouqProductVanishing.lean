/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqProduct

/-!
# Colours acting by zero in the product of two Rouquier families

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. In `RouqFamily.homProduct W T`:

* a colour of `W` acts by postcomposition with the 1-morphisms of `W`;
* a colour of `T` acts by precomposition with the 1-morphisms of `T`.

So the colour acts by zero wherever the corresponding 1-morphisms of `W` or `T` are zero
(`RouqFamily.homProduct_isZero_inl`, `RouqFamily.homProduct_isZero_inr`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

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

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem isZero_tgtCast {x z z' : X₁ × X₂} (e : z = z') {f : homObj k W T x ⟶ homObj k W T z}
    (hf : IsZero f) : IsZero (tgtCast e f) := by
  subst e
  exact hf

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem isZero_srcCast {x z z' : X₁ × X₂} (e : z = z') {f : homObj k W T z ⟶ homObj k W T x}
    (hf : IsZero f) : IsZero (srcCast e f) := by
  subst e
  exact hf

theorem isZero_yMap {B' : Type*} [Bicategory.{w, v} B'] [∀ a b : B', Preadditive (a ⟶ b)]
    [∀ a b : B', Linear k (a ⟶ b)] [AdditiveWhiskering B']
    [∀ (a b c : B') (f : b ⟶ c), (postcomp a f).Linear k] (y : B') {a b : B'} {f : a ⟶ b}
    (hf : IsZero f) : IsZero (yMap k y f) :=
  (yFun k y a b).map_isZero hf

/-- **A colour of `W` acts by zero on `homProduct W T`** where its 1-morphisms in `W` vanish. -/
theorem homProduct_isZero_inl (i : I₁) {x y : X₁ × X₂}
    (h : x + (RD₁.prod RD₂).iX (.inl i) = y)
    (hE : IsZero (W.E i (fst_step (RD₂ := RD₂) (y := y) i h)))
    (hF : IsZero (W.F i (fst_step (RD₂ := RD₂) (y := y) i h))) :
    IsZero ((homProduct k W T).E (.inl i) h) ∧ IsZero ((homProduct k W T).F (.inl i) h) :=
  ⟨isZero_tgtCast k W T _ (isZero_yMap k _ hE), isZero_srcCast k W T _ (isZero_yMap k _ hF)⟩

/-- **A colour of `T` acts by zero on `homProduct W T`** where its 1-morphisms in `T` (at the
negated weights) vanish. -/
theorem homProduct_isZero_inr (i : I₂) {x y : X₁ × X₂}
    (h : x + (RD₁.prod RD₂).iX (.inr i) = y)
    (hE : IsZero (T.E i (neg_reg i (snd_step (RD₁ := RD₁) (y := y) i h))))
    (hF : IsZero (T.F i (neg_reg i (snd_step (RD₁ := RD₁) (y := y) i h)))) :
    IsZero ((homProduct k W T).E (.inr i) h) ∧ IsZero ((homProduct k W T).F (.inr i) h) :=
  ⟨isZero_tgtCast k W T _ (isZero_yMap k (B' := HOp B) _ hE),
    isZero_srcCast k W T _ (isZero_yMap k (B' := HOp B) _ hF)⟩

end RouqFamily

end Categorification.TwoRep
