/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.QStrongRestrict
import Categorification.TwoRep.Regrade

/-!
# The restriction of a `Q`-strong 2-representation to an `α_i`-string

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3: a `Q`-strong 2-representation of `g` (Definition 1.2) restricts, along the
`α_i`-string through a weight `λ₀`, to one of `sl₂`, "by rescaling degrees" when
`d_i = (α_i, α_i)/2 ≠ 1` (§2.6.1 and the first paragraph of §5): the dots have degree
`(α_i, α_i) = 2 d_i` and the units of the adjunctions are shifted by multiples of `d_i`.

Here the rescaling is made on the side of the 2-representation: the restriction is a strong
2-representation of `sl₂` (`StrongSl2`) on `Regrade B (d_i)`, the bicategory `B` with the grading
shift `⟨n⟩` replaced by `⟨d_i n⟩` (`Categorification.TwoRep.Regrade`).

* `QStrong.toStrongSl2 S i λ₀ : StrongSl2 k (Regrade B (d_i))`: object `r` is `obj (λ₀ + r α_i)`,
  of weight `⟨i, λ₀⟩ + 2r`; `E r`, `F r` are `E_i`, `F_i` there; the dot and the crossing are those
  of the KLR action (of degrees `2` and `-2` in `Regrade B (d_i)`, i.e. `±(α_i, α_i)` in `B`);
  `r_i` is `S.rQ i`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open QuantumGroup QuantumGroup.UDot

universe w v u

theorem qsum_one {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ] [HasZeroObject C]
    [HasBinaryBiproducts C] (n : ℕ) (X : C) :
    qsum 1 n X = lsum ((List.range n).map fun j : ℕ => X⟦(n : ℤ) - 1 - 2 * (j : ℤ)⟧) := by
  simp only [qsum, one_mul]

theorem shCast_mk₀ {C : Type*} [Category C] [HasShift C ℤ] {X Y : C} {m m' : ℤ} (hm : m = 0)
    (f : X ⟶ Y) (e : m = m') :
    shCast (ShiftedHom.mk₀ m hm f) e = ShiftedHom.mk₀ m' (e ▸ hm) f := by
  subst e; rfl

theorem shCast_congr {C : Type*} [Category C] [HasShift C ℤ] {X Y : C} {a b : ℤ}
    {f g : ShiftedHom X Y a} (h : f = g) (e e' : a = b) : shCast f e = shCast g e' := by
  subst h; rfl

theorem braid_shCast {C : Type*} [Category C] [HasShift C ℤ] {W : C} {m m' p p' q q' : ℤ}
    (A T : ShiftedHom W W m) (e : m = m') (h₁ : m + m = p) (h₂ : m + p = q) (h₁' : m' + m' = p')
    (h₂' : m' + p' = q') (hb : (A.comp T h₁).comp A h₂ = (T.comp A h₁).comp T h₂) :
    ((shCast A e).comp (shCast T e) h₁').comp (shCast A e) h₂' =
      ((shCast T e).comp (shCast A e) h₁').comp (shCast T e) h₂' := by
  subst e
  obtain rfl : p = p' := h₁.symm.trans h₁'
  obtain rfl : q = q' := h₂.symm.trans h₂'
  exact hb

theorem dot_eq_di {I : Type*} (C : CartanDatum I) (i : I) : C.dot i i = di C i * 2 := by
  rw [← two_mul_di]; ring

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

/-- Transport of an adjunction `E ⊣ F⟨n⟩` along an equality of degrees. -/
def shiftAdj {a b : B} {E : a ⟶ b} {F : b ⟶ a} {n n' : ℤ} (e : n = n') (adj : E ⊣ F⟦n⟧) :
    E ⊣ F⟦n'⟧ :=
  e ▸ adj

namespace QStrong

variable (S : QStrong B C RD k Q) (i : I) (l₀ : X)

open Regrade in
/-- **The restriction of a `Q`-strong 2-representation to the `α_i`-string through `λ₀`**: a
strong 2-representation of `sl₂` in the sense of `StrongSl2`, on `B` with its grading rescaled by
`d_i` (`Regrade B (d_i)`, so that the shift `⟨n⟩` there is `⟨d_i n⟩` in `B`; CL §2.6.1, §5). -/
def toStrongSl2 : StrongSl2 k (Regrade B (di C i)) where
  n₀ := RD.pair (RD.iY i) l₀
  obj r := Regrade.of (di C i) (S.obj (l₀ + r • RD.iX i))
  E r := Regrade.up (di C i) (S.E i (string_add i l₀ r))
  F r := Regrade.up (di C i) (S.F i (string_add i l₀ r))
  adj r := (shiftAdj (B := B) (n' := di C i * (RD.pair (RD.iY i) l₀ + 2 * r + 1))
    (by rw [pair_string]) (S.adj i (string_add i l₀ r)) :)
  exists_leftAdj r := by
    obtain ⟨L, ⟨h⟩⟩ := S.exists_leftAdj i (string_add i l₀ r)
    exact ⟨L, ⟨h⟩⟩
  integrable := S.integrable i l₀
  hom_neg r l hl := S.hom_neg _ (di C i * l) (mul_neg_of_pos_of_neg (di_pos C i) hl)
  hom_zero r := S.hom_zero _
  EF r h := by
    have h' : 0 ≤ RD.pair (RD.iY i) (l₀ + (r + 1) • RD.iX i) := by rw [pair_string]; exact h
    obtain ⟨e⟩ := S.EF i (string_add i l₀ r) (string_add i l₀ (r + 1)) h'
    rw [pair_string] at e
    rw [qsum_one]
    exact ⟨e⟩
  FE r h := by
    have h' : RD.pair (RD.iY i) (l₀ + (r + 1) • RD.iX i) ≤ 0 := by rw [pair_string]; exact h
    obtain ⟨e⟩ := S.FE i (string_add i l₀ r) (string_add i l₀ (r + 1)) h'
    rw [pair_string] at e
    rw [qsum_one]
    exact ⟨e⟩
  rQ := S.rQ i
  dot r := ofB (di C i) (shCast (S.dot i (string_add i l₀ r)) (dot_eq_di C i))
  cross r := ofB (di C i) (shCast (S.cross i i (string_add i l₀ r) (string_add i l₀ (r + 1))
    (string_add i l₀ r) (string_add i l₀ (r + 1))) (by rw [dot_eq_di]; ring))
  cross_sq r := by
    apply toB_inj
    rw [toB_comp, toB_ofB]
    erw [shCast_comp_shCast _ _ _ _ _
      (by ring : -C.dot i i + -C.dot i i = -2 * C.dot i i) (by rw [dot_eq_di]; ring),
      S.klr.cross_sq_self, shCast_zero]
    rfl
  dot_slide_left r := by
    apply toB_inj
    rw [toB_sub, toB_comp, toB_comp, toB_shWhiskerLeft, toB_shWhiskerRight, toB_mk₀, toB_ofB,
      toB_ofB, toB_ofB]
    erw [shWhiskerLeft_shCast, shWhiskerRight_shCast,
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + C.dot i i = 0) (by ring),
      shCast_comp_shCast _ _ _ _ _ (by ring : C.dot i i + -C.dot i i = 0) (by ring),
      ← shCast_sub, ← S.klr.dot_slide_self_left i, shCast_mk₀]
    rfl
  dot_slide_right r := by
    apply toB_inj
    rw [toB_sub, toB_comp, toB_comp, toB_shWhiskerLeft, toB_shWhiskerRight, toB_mk₀, toB_ofB,
      toB_ofB, toB_ofB]
    erw [shWhiskerLeft_shCast, shWhiskerRight_shCast,
      shCast_comp_shCast _ _ _ _ _ (by ring : C.dot i i + -C.dot i i = 0) (by ring),
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + C.dot i i = 0) (by ring),
      ← shCast_sub, ← S.klr.dot_slide_self_right i, shCast_mk₀]
    rfl
  braid r := by
    have hb := S.klr.braid i i i (fun h => absurd h.2 (not_lt.2 (C.dot_self_pos i).le))
      (string_add i l₀ r) (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1))
      (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1))
      (string_add i l₀ r) (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1))
      (string_add i l₀ (r + 1 + 1)) (string_add i l₀ r) (string_add i l₀ (r + 1))
      (string_add i l₀ (r + 1))
    simp only [KLRGens.braidLRL, KLRGens.braidRLR, KLRGens.crossL, KLRGens.crossR] at hb
    intro τ₁ τ₂
    have hτ : -C.dot i i = di C i * -2 := by rw [dot_eq_di]; ring
    have e₁ : toB (di C i) τ₁ = shCast (shWhiskerLeft (S.E i (string_add i l₀ r))
        (S.cross i i (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1))
          (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1)))) hτ := by
      simp only [τ₁]
      rw [toB_shWhiskerLeft, toB_ofB]
      erw [shWhiskerLeft_shCast]
      rfl
    have e₂ : toB (di C i) τ₂ = shCast ((ShiftedHom.mk₀ (0 : ℤ) rfl (α_ _ _ _).inv).comp
        ((shWhiskerRight (S.cross i i (string_add i l₀ r) (string_add i l₀ (r + 1))
          (string_add i l₀ r) (string_add i l₀ (r + 1))) (S.E i (string_add i l₀ (r + 1 + 1)))).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ _ _ _).hom)
          (by ring : (0 : ℤ) + -C.dot i i = -C.dot i i))
        (by ring : -C.dot i i + (0 : ℤ) = -C.dot i i)) hτ := by
      simp only [τ₂]
      rw [toB_comp, toB_comp, toB_mk₀, toB_mk₀, toB_shWhiskerRight, toB_ofB]
      erw [shWhiskerRight_shCast, ← shCast_mk₀ (m := 0) rfl _ (by ring : (0 : ℤ) = di C i * 0),
        ← shCast_mk₀ (m := 0) rfl _ (by ring : (0 : ℤ) = di C i * 0),
        shCast_comp_shCast _ _ _ _ _ (by ring : (0 : ℤ) + -C.dot i i = -C.dot i i)
          (by have := dot_eq_di C i; omega),
        shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + (0 : ℤ) = -C.dot i i)
          (by have := dot_eq_di C i; omega)]
      rfl
    clear_value τ₁ τ₂
    apply toB_inj
    rw [toB_comp, toB_comp, toB_comp, toB_comp, e₁, e₂]
    exact braid_shCast _ _ hτ (by ring) (by ring) _ _ hb

end QStrong

end Categorification.TwoRep
