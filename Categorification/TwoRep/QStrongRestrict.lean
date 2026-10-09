/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.QStrong

/-!
# Restricting a `Q`-strong 2-representation to an `α_i`-string

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3: §3 works with `g = sl₂`; a `Q`-strong 2-representation of `g` (Definition 1.2)
restricts, along the `α_i`-string through a weight `λ₀`, to one of `sl₂`. This file collects the
bookkeeping for that restriction (made in `Categorification.TwoRep.QStrongString`): the transport
lemmas `shCast_comp_shCast` etc. for the degrees of shifted 2-morphisms, and the weights along a
string (`QStrong.string_add`, `QStrong.pair_string`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open QuantumGroup QuantumGroup.UDot

universe w v u

section Cast

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

omit [Preadditive C] in
theorem shCast_rfl {X Y : C} {a : ℤ} (f : ShiftedHom X Y a) (h : a = a) : shCast f h = f := rfl

omit [Preadditive C] in
theorem shCast_shCast {X Y : C} {a b c : ℤ} (f : ShiftedHom X Y a) (h : a = b) (h' : b = c) :
    shCast (shCast f h) h' = shCast f (h.trans h') := by
  subst h h'; rfl

theorem shCast_zero {X Y : C} {a b : ℤ} (h : a = b) : shCast (0 : ShiftedHom X Y a) h = 0 := by
  subst h; rfl

theorem shCast_sub {X Y : C} {a b : ℤ} (f g : ShiftedHom X Y a) (h : a = b) :
    shCast (f - g) h = shCast f h - shCast g h := by
  subst h; rfl

omit [Preadditive C] in
/-- Composition of transported shifted morphisms is the transport of the composition. -/
theorem shCast_comp_shCast {X Y Z : C} {a a' b b' c c' : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (ea : a = a') (eb : b = b') (h : b' + a' = c') (h₀ : b + a = c)
    (ec : c = c') : (shCast f ea).comp (shCast g eb) h = shCast (f.comp g h₀) ec := by
  subst ea eb ec; rfl

omit [Preadditive C] in
theorem comp_shCast {X Y Z : C} {a b b' c c' : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (eb : b = b') (h : b' + a = c') (h₀ : b + a = c) (ec : c = c') :
    f.comp (shCast g eb) h = shCast (f.comp g h₀) ec := by
  subst eb ec; rfl

omit [Preadditive C] in
theorem shCast_comp {X Y Z : C} {a a' b c c' : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (ea : a = a') (h : b + a' = c') (h₀ : b + a = c) (ec : c = c') :
    (shCast f ea).comp g h = shCast (f.comp g h₀) ec := by
  subst ea ec; rfl

omit [Preadditive C] in
/-- Changing the degree bookkeeping of a composition. -/
theorem comp_eq_shCast {X Y Z : C} {a b c c' : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c') (h₀ : b + a = c) (ec : c = c') :
    f.comp g h = shCast (f.comp g h₀) ec := by
  subst ec; rfl

end Cast

section Whisker

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

theorem shWhiskerLeft_shCast {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {n n' : ℤ}
    (η : ShiftedHom g h n) (e : n = n') :
    shWhiskerLeft f (shCast η e) = shCast (shWhiskerLeft f η) e := by
  subst e; rfl

theorem shWhiskerRight_shCast {a b c : B} {f g : a ⟶ b} {n n' : ℤ} (η : ShiftedHom f g n)
    (e : n = n') (h : b ⟶ c) :
    shWhiskerRight (shCast η e) h = shCast (shWhiskerRight η h) e := by
  subst e; rfl

end Whisker

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable (i : I) (l₀ : X)

theorem string_add (r : ℤ) : l₀ + r • RD.iX i + RD.iX i = l₀ + (r + 1) • RD.iX i := by
  rw [add_smul, one_smul, add_assoc]

theorem pair_string (r : ℤ) :
    RD.pair (RD.iY i) (l₀ + r • RD.iX i) = RD.pair (RD.iY i) l₀ + 2 * r := by
  rw [map_add, map_zsmul, RD.pair_iY_iX_self, smul_eq_mul]; ring

end QStrong

end Categorification.TwoRep
