/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong
import Categorification.KLR.CyclotomicAction.Block
import Categorification.KLR.CyclotomicAbsentColour

/-!
# Cyclotomic induction, its dots and its crossings

Kang–Kashiwara (arXiv:1102.4677v4, §4.2) define `F_i^Λ M = R^Λ(β + α_i) e(β, i) ⊗_{R^Λ(β)} M`.
Here this is induction along the nonunital map `lastEmb i h : R^Λ(β) → R^Λ(δ)`, for a
proof `h : {i} + β = δ`:

* `ind i h = InductionAlong.functor (lastEmb i h)`.
* `dot i h : ind i h ⟶ ind i h` : right multiplication by the dot on the last strand.
* `cross i j h₁ h₂ h₃ h₄ : ind j h₁ ⋙ ind i h₂ ⟶ ind i h₃ ⋙ ind j h₄` : after identifying
  both composites with induction along the composite inclusions (`InductionAlong.compIso`),
  right multiplication by the crossing `ψ_{card γ}` of the two new strands.

The weight of the target is the multiset `δ` in all four functors; it is a variable, and
the intermediate weights `β`, `β'` are tied to it only by the proofs `h₁, …, h₄`. Both
composites are therefore functors between literally the same categories
`ModuleCat R^Λ(γ) ⥤ ModuleCat R^Λ(δ)`, and every natural transformation built from
elements of `R^Λ(δ)` is compared with others inside the one ring `R^Λ(δ)`.

Elements of `R^Λ(δ)` give natural transformations by `InductionAlong.natTrans`; the
intertwining conditions come from `KLRAlgebra.IsLeftBlock` through `intertwines_mk`.
Everything is ungraded, over any commutative ring, for any `Q` and any cyclotomic
polynomials `a`.
-/

namespace Categorification.KLR.CyclotomicAction

open KLRAlgebra CategoryTheory

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

noncomputable section

/-- Transport of the cyclotomic quotient along an equality of multisets. -/
def castCyc {β δ : Multiset I} (h : β = δ) : CycKLR k Q a β ≃ₐ[k] CycKLR k Q a δ := by
  subst h
  exact AlgEquiv.refl

theorem castCyc_mk {β δ : Multiset I} (h : β = δ) (r : KLRAlgebra k Q β) :
    castCyc Q a h (CycKLR.mk k Q a β r) = CycKLR.mk k Q a δ (castKLR Q h r) := by
  subst h
  rfl

/-- The last-strand inclusion `R^Λ(β) → R^Λ(δ)` for `{i} + β = δ`; its unit image is the
idempotent `e(β, i)`. -/
def lastEmb (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    CycKLR k Q a β →ₙ+* CycKLR k Q a δ where
  toFun r := castCyc Q a h (KLRAlgebra.AbsentColour.cyclotomicLast Q i a β r)
  map_mul' r r' := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' r r' := by rw [map_add, map_add]

theorem lastEmb_mk (i : I) {β δ : Multiset I} (h : {i} + β = δ) (r : KLRAlgebra k Q β) :
    lastEmb Q a i h (CycKLR.mk k Q a β r) = CycKLR.mk k Q a δ (lastIncl Q i h r) := by
  change castCyc Q a h (KLRAlgebra.AbsentColour.cyclotomicLast Q i a β _) = _
  rw [KLRAlgebra.AbsentColour.cyclotomicLast_mk, castCyc_mk]
  rfl

variable {Q a}

/-- Intertwiners of KLR algebras descend to the cyclotomic quotients. -/
theorem intertwines_mk {γ δ : Multiset I} {F G : CycKLR k Q a γ →ₙ+* CycKLR k Q a δ}
    {f g : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ}
    (hF : ∀ r, F (CycKLR.mk k Q a γ r) = CycKLR.mk k Q a δ (f r))
    (hG : ∀ r, G (CycKLR.mk k Q a γ r) = CycKLR.mk k Q a δ (g r)) {c : KLRAlgebra k Q δ}
    (h : ∀ r, f r * c = c * g r) :
    InductionAlong.Intertwines F G (CycKLR.mk k Q a δ c) := fun r => by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  rw [hF, hG, ← map_mul, ← map_mul, h]

theorem lastEmb_comp_mk (i j : I) {γ β δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) (r : KLRAlgebra k Q γ) :
    ((lastEmb Q a i h₂).comp (lastEmb Q a j h₁)) (CycKLR.mk k Q a γ r) =
      CycKLR.mk k Q a δ (((lastIncl Q i h₂).comp (lastIncl Q j h₁)) r) := by
  rw [NonUnitalRingHom.comp_apply, lastEmb_mk, lastEmb_mk]
  rfl

/-! ### The functors and the generating natural transformations -/

variable (Q a)

/-- Cyclotomic induction `F_i^Λ : R^Λ(β)-mod → R^Λ(δ)-mod`, `{i} + β = δ`. -/
abbrev ind (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    ModuleCat.{max (max u v) w} (CycKLR k Q a β) ⥤
      ModuleCat.{max (max u v) w} (CycKLR k Q a δ) :=
  InductionAlong.functor.{max u v, w} (lastEmb Q a i h)

/-- The dot on the last strand. -/
def dotElt (i : I) {β δ : Multiset I} (h : {i} + β = δ) : CycKLR k Q a δ :=
  CycKLR.mk k Q a δ (x ⟨Multiset.card β, by rw [card_lastIncl i h]; omega⟩)

theorem intertwines_dotElt (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    InductionAlong.Intertwines (lastEmb Q a i h) (lastEmb Q a i h) (dotElt Q a i h) :=
  intertwines_mk (lastEmb_mk Q a i h) (lastEmb_mk Q a i h)
    ((isLeftBlock_lastIncl i h).intertwines_dot _ le_rfl)

/-- **The dot** `x : F_i ⟶ F_i`, right multiplication by the last dot. -/
def dot (i : I) {β δ : Multiset I} (h : {i} + β = δ) : ind.{u, v, w} Q a i h ⟶ ind Q a i h :=
  InductionAlong.natTrans (intertwines_dotElt Q a i h)

section Cross

variable (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ)
  (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ)

/-- The two-strand inclusion `R(γ) → R(δ)` adding strands `j` then `i`. -/
noncomputable abbrev doubleIncl : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ :=
  (lastIncl Q i h₂).comp (lastIncl Q j h₁)

omit [DecidableEq I] in
theorem card_double {i j : I} {γ β δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ) :
    Multiset.card δ = Multiset.card γ + 2 := by
  rw [card_lastIncl i h₂, card_lastIncl j h₁]

omit [DecidableEq I] in
theorem card_mid {j : I} {γ β : Multiset I} (h₁ : {j} + γ = β) :
    Multiset.card β - Multiset.card γ = 1 := by
  rw [← h₁, Multiset.card_add, Multiset.card_singleton]; omega

theorem isLeftBlock_double :
    IsLeftBlock (doubleIncl (Q := Q) i j h₁ h₂) (fun n => if n = 0 then j else i) :=
  ((isLeftBlock_lastIncl j h₁).comp (isLeftBlock_lastIncl i h₂)).congr_word fun n _ => by
    simp only [card_mid h₁, Nat.lt_one_iff]

/-- The crossing of the two new strands intertwines the two two-strand inclusions. -/
theorem double_cross (r : KLRAlgebra k Q γ) :
    doubleIncl (Q := Q) i j h₁ h₂ r * ψ (Multiset.card γ) =
      ψ (Multiset.card γ) * doubleIncl (Q := Q) j i h₃ h₄ r := by
  have hδ := card_double h₁ h₂
  have h := (isLeftBlock_double Q i j h₁ h₂).intertwines_cross (q := 0)
    ((isLeftBlock_double Q j i h₃ h₄).congr_word fun n hn => by
      rcases n with _ | _ | n
      · simp [IsLeftBlock.swapAt]
      · simp [IsLeftBlock.swapAt]
      · omega) (by omega) r
  simpa using h

/-- The crossing element of `R^Λ(δ)`. -/
def crossElt : CycKLR k Q a δ := CycKLR.mk k Q a δ (ψ (Multiset.card γ))

theorem intertwines_crossElt :
    InductionAlong.Intertwines ((lastEmb Q a i h₂).comp (lastEmb Q a j h₁))
      ((lastEmb Q a j h₄).comp (lastEmb Q a i h₃)) (crossElt Q a (γ := γ) (δ := δ)) :=
  intertwines_mk (lastEmb_comp_mk i j h₁ h₂) (lastEmb_comp_mk j i h₃ h₄)
    (double_cross Q i j h₁ h₂ h₃ h₄)

/-- **The crossing** `ψ : F_i F_j ⟶ F_j F_i` (the functor `ind j h₁ ⋙ ind i h₂` applies
`F_j` first): conjugate of right multiplication by `ψ_{card γ}`. -/
def cross : ind.{u, v, w} Q a j h₁ ⋙ ind Q a i h₂ ⟶ ind Q a i h₃ ⋙ ind Q a j h₄ :=
  (InductionAlong.compIso _ _).hom ≫
    InductionAlong.natTrans (intertwines_crossElt Q a i j h₁ h₂ h₃ h₄) ≫
      (InductionAlong.compIso _ _).inv

end Cross

end

end Categorification.KLR.CyclotomicAction
