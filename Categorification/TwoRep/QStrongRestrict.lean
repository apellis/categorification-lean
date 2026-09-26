/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.QStrong

/-!
# Restricting a `Q`-strong 2-representation to an `α_i`-string

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3: §3 works with `g = sl₂`; a `Q`-strong 2-representation of `g` (Definition 1.2)
restricts, along the `α_i`-string through a weight `λ₀`, to one of `sl₂`. Here this is made precise
for a simply-laced vertex (`(α_i, α_i) = 2`, so `d_i = 1`); CL's reduction of general `d_i` to this
case "by rescaling degrees" (§5, first paragraph) is not formalized.

* `QStrong.toStrongSl2 S i hi l₀ : StrongSl2 k B`: object `r` is `obj (λ₀ + r α_i)`, of weight
  `⟨i, λ₀⟩ + 2r`; `E r`, `F r` are `E_i`, `F_i` there; the dot and the crossing are those of the KLR
  action, with degrees `(α_i, α_i) = 2` and `-(α_i, α_i) = -2`; `r_i` is `S.rQ i`.

The degree bookkeeping uses the transport lemmas `shCast_comp_shCast` etc. for shifted
2-morphisms.
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

variable (S : QStrong B C RD k Q) (i : I) (hi : C.dot i i = 2) (l₀ : X)

theorem string_add (r : ℤ) : l₀ + r • RD.iX i + RD.iX i = l₀ + (r + 1) • RD.iX i := by
  rw [add_smul, one_smul, add_assoc]

theorem pair_string (r : ℤ) :
    RD.pair (RD.iY i) (l₀ + r • RD.iX i) = RD.pair (RD.iY i) l₀ + 2 * r := by
  rw [map_add, map_zsmul, RD.pair_iY_iX_self, smul_eq_mul]; ring

include hi in
theorem di_eq_one : di C i = 1 := by
  unfold di; rw [hi]; rfl

/-- **The restriction of a `Q`-strong 2-representation to the `α_i`-string through `λ₀`**, for a
vertex with `(α_i, α_i) = 2`: a strong 2-representation of `sl₂` in the sense of `StrongSl2`. -/
def toStrongSl2 : StrongSl2 k B where
  n₀ := RD.pair (RD.iY i) l₀
  obj r := S.obj (l₀ + r • RD.iX i)
  E r := S.E i (string_add i l₀ r)
  F r := S.F i (string_add i l₀ r)
  adj r := by
    have e : di C i * (RD.pair (RD.iY i) (l₀ + r • RD.iX i) + 1) =
        RD.pair (RD.iY i) l₀ + 2 * r + 1 := by
      rw [di_eq_one i hi, pair_string, one_mul]
    exact e ▸ S.adj i (string_add i l₀ r)
  exists_leftAdj r := S.exists_leftAdj i _
  integrable := S.integrable i l₀
  hom_neg r := S.hom_neg _
  hom_zero r := S.hom_zero _
  EF r h := by
    have h' : 0 ≤ RD.pair (RD.iY i) (l₀ + (r + 1) • RD.iX i) := by rw [pair_string]; exact h
    have := S.EF i (string_add i l₀ r) (string_add i l₀ (r + 1)) h'
    rwa [di_eq_one i hi, pair_string] at this
  FE r h := by
    have h' : RD.pair (RD.iY i) (l₀ + (r + 1) • RD.iX i) ≤ 0 := by rw [pair_string]; exact h
    have := S.FE i (string_add i l₀ r) (string_add i l₀ (r + 1)) h'
    rwa [di_eq_one i hi, pair_string] at this
  rQ := S.rQ i
  dot r := shCast (S.dot i (string_add i l₀ r)) hi
  cross r := shCast (S.cross i i (string_add i l₀ r) (string_add i l₀ (r + 1))
    (string_add i l₀ r) (string_add i l₀ (r + 1))) (by rw [hi])
  cross_sq r := by
    rw [shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + -C.dot i i = -2 * C.dot i i)
      (by rw [hi]; norm_num), S.klr.cross_sq_self, shCast_zero]
  dot_slide_left r := by
    rw [shWhiskerLeft_shCast, shWhiskerRight_shCast,
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + C.dot i i = 0) rfl,
      shCast_comp_shCast _ _ _ _ _ (by ring : C.dot i i + -C.dot i i = 0) rfl, shCast_rfl,
      shCast_rfl]
    exact S.klr.dot_slide_self_left i _ _
  dot_slide_right r := by
    rw [shWhiskerLeft_shCast, shWhiskerRight_shCast,
      shCast_comp_shCast _ _ _ _ _ (by ring : C.dot i i + -C.dot i i = 0) rfl,
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + C.dot i i = 0) rfl, shCast_rfl,
      shCast_rfl]
    exact S.klr.dot_slide_self_right i _ _
  braid r := by
    have hb := S.klr.braid i i i (fun h => by have := h.2; omega)
      (string_add i l₀ r) (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1))
      (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1))
      (string_add i l₀ r) (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1))
      (string_add i l₀ (r + 1 + 1)) (string_add i l₀ r) (string_add i l₀ (r + 1))
      (string_add i l₀ (r + 1))
    simp only [KLRGens.braidLRL, KLRGens.braidRLR, KLRGens.crossL, KLRGens.crossR] at hb
    intro τ₁ τ₂
    have hτ : -C.dot i i = -2 := by rw [hi]
    have e₁ : τ₁ = shCast (shWhiskerLeft (S.E i (string_add i l₀ r))
        (S.cross i i (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1))
          (string_add i l₀ (r + 1)) (string_add i l₀ (r + 1 + 1)))) hτ :=
      shWhiskerLeft_shCast _ _ _
    have e₂ : τ₂ = shCast ((ShiftedHom.mk₀ (0 : ℤ) rfl (α_ _ _ _).inv).comp
        ((shWhiskerRight (S.cross i i (string_add i l₀ r) (string_add i l₀ (r + 1))
          (string_add i l₀ r) (string_add i l₀ (r + 1))) (S.E i (string_add i l₀ (r + 1 + 1)))).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ _ _ _).hom)
          (by ring : (0 : ℤ) + -C.dot i i = -C.dot i i))
        (by ring : -C.dot i i + (0 : ℤ) = -C.dot i i)) hτ := by
      change (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ _ _ _).inv).comp
        ((shWhiskerRight (shCast _ hτ) _).comp _ _) _ = _
      rw [shWhiskerRight_shCast, shCast_comp _ _ _ _ (by ring : (0 : ℤ) + -C.dot i i = -C.dot i i)
        hτ, comp_shCast _ _ _ _ (by ring : -C.dot i i + (0 : ℤ) = -C.dot i i) hτ]
    rw [e₁, e₂, shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + -C.dot i i =
        -(C.dot i i + C.dot i i)) (by rw [hi]; norm_num),
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + -(C.dot i i + C.dot i i) =
        -(C.dot i i + C.dot i i + C.dot i i)) (by rw [hi]; norm_num),
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + -C.dot i i =
        -(C.dot i i + C.dot i i)) (by rw [hi]; norm_num),
      shCast_comp_shCast _ _ _ _ _ (by ring : -C.dot i i + -(C.dot i i + C.dot i i) =
        -(C.dot i i + C.dot i i + C.dot i i)) (by rw [hi]; norm_num)]
    congr 1

end QStrong

end Categorification.TwoRep
