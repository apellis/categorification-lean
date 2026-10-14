/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.KLR.CyclotomicAction.Square
import Categorification.TwoRep.AdditiveCat

/-!
# Cyclotomic restriction and the induction–restriction adjunction

For `{i} + β = δ`, cyclotomic restriction `E_i^Λ : R^Λ(δ)-mod → R^Λ(β)-mod` is restriction
along the last-strand inclusion `R^Λ(β) → R^Λ(δ)`, i.e. truncation by its idempotent
(Kang–Kashiwara, arXiv:1102.4677v4, §4.2), and `indResAdj : F_i^Λ ⊣ E_i^Λ` is the
induction–restriction adjunction. The target multiset `δ` is a variable tied to `β` only by
the proof `h`, as for `ind`.

`blockCat`, `indA`, `resA`, `adjA`, `dotA`, `sameCrossA` bundle these functors and the
generating transformations as 1- and 2-cells of `TwoRep.AdditiveCat`; these are the block
cells from which the weight-indexed cyclotomic Rouquier family is assembled (KL III Thm. 1.2).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory

universe u v w

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

/-- Cyclotomic restriction `R^Λ(δ)-mod → R^Λ(β)-mod`, `{i} + β = δ`. -/
abbrev res (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    ModuleCat.{max (max u v) w} (CycKLR k Q a δ) ⥤
      ModuleCat.{max (max u v) w} (CycKLR k Q a β) :=
  InductionAlong.resFunctor.{max u v, w} (lastEmb Q a i h)

/-- **Cyclotomic induction is left adjoint to cyclotomic restriction.** -/
def indResAdj (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    ind.{u, v, w} Q a i h ⊣ res Q a i h :=
  InductionAlong.adjunction.{max u v, w} (lastEmb Q a i h)

instance ind_additive (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (ind.{u, v, w} Q a i h).Additive :=
  inferInstanceAs (InductionAlong.functor.{max u v, w} (lastEmb Q a i h)).Additive

instance res_additive (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (res.{u, v, w} Q a i h).Additive :=
  inferInstanceAs (InductionAlong.resFunctor.{max u v, w} (lastEmb Q a i h)).Additive

/-- The block category `R^Λ(β)-mod`, as an object of `TwoRep.AdditiveCat`. -/
abbrev blockCat (β : Multiset I) : TwoRep.AdditiveCat :=
  TwoRep.AdditiveCat.of (ModuleCat.{max (max u v) w} (CycKLR k Q a β))

/-- Induction as a 1-cell of `TwoRep.AdditiveCat`. -/
def indA (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    blockCat.{u, v, w} Q a β ⟶ blockCat Q a δ :=
  @AdditiveFunctor.of _ _ _ _ _ _ (ind.{u, v, w} Q a i h) (ind_additive Q a i h)

/-- Restriction as a 1-cell of `TwoRep.AdditiveCat`. -/
def resA (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    blockCat.{u, v, w} Q a δ ⟶ blockCat Q a β :=
  @AdditiveFunctor.of _ _ _ _ _ _ (res.{u, v, w} Q a i h) (res_additive Q a i h)

/-- The induction–restriction adjunction in `TwoRep.AdditiveCat`. -/
def adjA (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    Bicategory.Adjunction (indA.{u, v, w} Q a i h) (resA Q a i h) :=
  TwoRep.AdditiveCat.ofAdjunction (indResAdj.{u, v, w} Q a i h)

/-- The dot as a 2-cell of `TwoRep.AdditiveCat`. -/
def dotA (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    indA.{u, v, w} Q a i h ⟶ indA Q a i h :=
  ObjectProperty.homMk (dot.{u, v, w} Q a i h)

/-- The same-colour crossing `-ψ` as a 2-cell of `TwoRep.AdditiveCat`. -/
def sameCrossA (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ) :
    indA.{u, v, w} Q a i h₁ ≫ indA Q a i h₂ ⟶ indA Q a i h₁ ≫ indA Q a i h₂ :=
  ObjectProperty.homMk (sameCross.{u, v, w} Q a i h₁ h₂)

@[simp] theorem indA_obj (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (indA.{u, v, w} Q a i h).obj = ind Q a i h := rfl

@[simp] theorem resA_obj (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (resA.{u, v, w} Q a i h).obj = res Q a i h := rfl

@[simp] theorem dotA_hom (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (dotA.{u, v, w} Q a i h).hom = dot Q a i h := rfl

@[simp] theorem sameCrossA_hom (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β)
    (h₂ : {i} + β = δ) : (sameCrossA.{u, v, w} Q a i h₁ h₂).hom = sameCross Q a i h₁ h₂ := rfl

end

end Categorification.KLR.CyclotomicAction
