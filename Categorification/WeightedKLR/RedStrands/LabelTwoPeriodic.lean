/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The periodic middle-algebra resolution for the label-two unknot

The algebra calculation in Webster, arXiv:1309.3796v2, §8.2, proof preceding
Proposition 8.4. The two iterated dual number generators represent the two
square-zero variables. The alternating multiplication maps have kernel equal
to the image of the other map over any commutative ground ring.
-/

namespace Categorification.Webster.LabelTwo

open TrivSqZeroExt
open scoped DualNumber

variable {k : Type*} [CommRing k]

abbrev Middle (k : Type*) := DualNumber (DualNumber k)

def y₁ : Middle k := inl ε
def y₂ : Middle k := ε

private def mulMap {R : Type*} [CommRing R] (a : R) : R →ₗ[R] R where
  toFun x := a*x
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := mul_left_comm _ _ _

def plus : Middle k →ₗ[Middle k] Middle k := mulMap (R := Middle k) (y₁ + y₂)
def minus : Middle k →ₗ[Middle k] Middle k := mulMap (R := Middle k) (y₁ - y₂)

theorem plus_coordinates (a b c d : k) :
    plus (⟨⟨a,b⟩,⟨c,d⟩⟩ : Middle k) = ⟨⟨0,a⟩,⟨a,c+b⟩⟩ := by
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · change (0+0)*a = 0
    simp
  · change (0+0)*b+(1+0)*a = a
    simp
  · change (0+0)*c+(0+1)*a = a
    simp
  · change ((0+0)*d+(1+0)*c)+((0+1)*b+(0+0)*a) = c+b
    simp

private theorem minus_coordinates (a b c d : k) :
    minus (⟨⟨a,b⟩,⟨c,d⟩⟩ : Middle k) = ⟨⟨0,a⟩,⟨-a,c-b⟩⟩ := by
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · change (0-0)*a = 0
    simp
  · change (0-0)*b+(1-0)*a = a
    simp
  · change (0-0)*c+(0-1)*a = -a
    simp
  · change ((0-0)*d+(1-0)*c)+((0-1)*b+(0-0)*a) = c-b
    simp [sub_eq_add_neg]

theorem ker_plus : LinearMap.ker (plus (k := k)) = LinearMap.range minus := by
  ext x
  change _ = 0 ↔ _
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  constructor
  · intro hx
    rw [plus_coordinates] at hx
    have ha : a=0 := congrArg (fun z : Middle k => z.fst.snd) hx
    have hc : c+b=0 := congrArg (fun z : Middle k => z.snd.snd) hx
    have hc' : c = -b := eq_neg_of_add_eq_zero_left hc
    subst a
    subst c
    exact ⟨⟨⟨b,0⟩,⟨d,0⟩⟩, by rw [minus_coordinates,sub_zero]⟩
  · rintro ⟨⟨⟨e,f⟩,⟨g,h⟩⟩,hx⟩
    rw [← hx,minus_coordinates,plus_coordinates]
    simp
    rfl

theorem ker_minus : LinearMap.ker (minus (k := k)) = LinearMap.range plus := by
  ext x
  change _ = 0 ↔ _
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  constructor
  · intro hx
    rw [minus_coordinates] at hx
    have ha : a=0 := congrArg (fun z : Middle k => z.fst.snd) hx
    have hc : c-b=0 := congrArg (fun z : Middle k => z.snd.snd) hx
    have hc' : c = b := sub_eq_zero.mp hc
    subst a
    subst c
    exact ⟨⟨⟨b,0⟩,⟨d,0⟩⟩, by rw [plus_coordinates,add_zero]⟩
  · rintro ⟨⟨⟨e,f⟩,⟨g,h⟩⟩,hx⟩
    rw [← hx,plus_coordinates,minus_coordinates]
    simp
    rfl

end Categorification.Webster.LabelTwo
