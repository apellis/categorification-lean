/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqThreeStrand

/-!
# The braid relation with distinct outer colours for black induction

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Khovanov–Lauda I, §2.1 (the braid relation with distinct outer labels); Brundan,
arXiv:1501.00350v1, Definition 1.1, (1.4) for outer labels `i ≠ c` (the shape of
`TwoRep.RouqUpKLR.braid`).

Every crossing on restrictions is right multiplication by a projected affine crossing
(`resCrossOfEq_val`). Through the three last-strand inclusions of the affine cover the six
whiskered crossings of the braid relation are products of `ψ`'s with units of two-strand
inclusions; moving these units across the crossings (`CyclotomicAction.double_cross`) leaves
the KLR braid identity `CyclotomicAction.braid_identity` on the affine cover with outer labels
`i ≠ c` (`KLRAlgebra.unit_mul_braid_cut`). The signs agree on both sides since the same three
pairs of colours cross. This gives

* the braid relation on restrictions between arbitrary contents, for any middle colour `j`
  (equal to `i`, to `c`, or distinct from both): `resCrossOfEq_braid_three`;
* its mate on inductions: `indCrossOfEq_braid_three`.

The hypotheses are `KLRSymm Q` and `i ≠ c`; no route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open CyclotomicAction

universe u v

variable {J : Type u} [DecidableEq J] {k : Type v} [CommRing k]
  {Q : J → J → MvPolynomial (Fin 2) k}

/-- Moving idempotents to the left across three factors. -/
theorem unit_mul_absorb_three {R : Type*} [Ring R] {U₀ U₁ U₂ U₃ a b c D₁ D₂ D₃ : R}
    (h₁ : U₀ * a = a * U₁) (h₁' : U₁ * D₁ = U₁) (h₂ : U₁ * b = b * U₂) (h₂' : U₂ * D₂ = U₂)
    (h₃ : U₂ * c = c * U₃) (h₃' : U₃ * D₃ = U₃) :
    U₀ * (a * D₁) * (b * D₂) * (c * D₃) = U₀ * (a * (b * c)) := by
  have e1 : U₀ * (a * D₁) = a * U₁ := by rw [← mul_assoc, h₁, mul_assoc, h₁']
  have e2 : U₁ * (b * D₂) = b * U₂ := by rw [← mul_assoc, h₂, mul_assoc, h₂']
  have e3 : U₂ * (c * D₃) = c * U₃ := by rw [← mul_assoc, h₃, mul_assoc, h₃']
  have f : U₀ * (a * (b * c)) = a * (b * (c * U₃)) := by
    rw [← mul_assoc, h₁, mul_assoc, ← mul_assoc U₁, h₂, mul_assoc, h₃]
  rw [f, e1, mul_assoc a, e2, mul_assoc, mul_assoc b, e3]

/-- **The braid identity with distinct outer labels, cut by two-strand units**: the products
of crossings of the three whiskered crossings of both sides of the braid relation agree after
the unit of the source block. -/
theorem unit_mul_braid_cut (i j c : J) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset J} (e1 : {c} + l = w₁) (e2 : {j} + w₁ = w₂)
    (e3 : {i} + w₂ = m) (e4 : {i} + w₁ = w₃) (e5 : {j} + w₃ = m)
    (e6 : {i} + l = w₄) (e7 : {c} + w₄ = w₃) (e8 : {j} + w₄ = w₅)
    (e9 : {c} + w₅ = m) (e10 : {j} + l = w₆) (e11 : {c} + w₆ = w₂)
    (e12 : {i} + w₆ = w₅) :
    tripleIncl Q i j c e6 e8 e9 1 *
        (ψ (Multiset.card w₄) * lastIncl Q j e5 (lastIncl Q c e7 1)) *
        lastIncl Q j e5 (ψ (Multiset.card l) * lastIncl Q i e4 (lastIncl Q c e1 1)) *
        (ψ (Multiset.card w₁) * lastIncl Q i e3 (lastIncl Q j e2 1)) =
      tripleIncl Q i j c e6 e8 e9 1 *
        lastIncl Q c e9 (ψ (Multiset.card l) * lastIncl Q i e12 (lastIncl Q j e10 1)) *
        (ψ (Multiset.card w₆) * lastIncl Q i e3 (lastIncl Q c e11 1)) *
        lastIncl Q i e3 (ψ (Multiset.card l) * lastIncl Q j e2 (lastIncl Q c e1 1)) := by
  have idem : ∀ {β β' : Multiset J} (x y z : J) (g₁ : {x} + l = β) (g₂ : {y} + β = β')
      (g₃ : {z} + β' = m),
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) *
        lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) =
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) := fun x y z g₁ g₂ g₃ => by
    rw [← map_mul, ← map_mul, ← map_mul, mul_one]
  have top : ∀ {β β' : Multiset J} (x y z : J) (g₁ : {x} + l = β) (g₂ : {y} + β = β')
      (g₃ : {z} + β' = m),
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) *
        lastIncl Q z g₃ (lastIncl Q y g₂ 1) =
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) := fun x y z g₁ g₂ g₃ => by
    rw [← map_mul, ← map_mul, mul_one]
  have l1 : lastIncl Q c e9 (lastIncl Q j e8 (lastIncl Q i e6 1)) * ψ (Multiset.card w₄) =
      ψ (Multiset.card w₄) * lastIncl Q j e5 (lastIncl Q c e7 (lastIncl Q i e6 1)) :=
    double_cross Q c j e8 e9 e7 e5 (lastIncl Q i e6 1)
  have l2 : lastIncl Q j e5 (lastIncl Q c e7 (lastIncl Q i e6 1)) *
      lastIncl Q j e5 (ψ (Multiset.card l)) =
      lastIncl Q j e5 (ψ (Multiset.card l)) * lastIncl Q j e5 (lastIncl Q i e4 (lastIncl Q c e1
          1)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (double_cross Q c i e6 e7 e1 e4 1)
  have l3 : lastIncl Q j e5 (lastIncl Q i e4 (lastIncl Q c e1 1)) * ψ (Multiset.card w₁) =
      ψ (Multiset.card w₁) * lastIncl Q i e3 (lastIncl Q j e2 (lastIncl Q c e1 1)) :=
    double_cross Q j i e4 e5 e2 e3 (lastIncl Q c e1 1)
  have r1 : lastIncl Q c e9 (lastIncl Q j e8 (lastIncl Q i e6 1)) *
      lastIncl Q c e9 (ψ (Multiset.card l)) =
      lastIncl Q c e9 (ψ (Multiset.card l)) *
        lastIncl Q c e9 (lastIncl Q i e12 (lastIncl Q j e10 1)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (double_cross Q j i e6 e8 e10 e12 1)
  have r2 : lastIncl Q c e9 (lastIncl Q i e12 (lastIncl Q j e10 1)) * ψ (Multiset.card w₆) =
      ψ (Multiset.card w₆) * lastIncl Q i e3 (lastIncl Q c e11 (lastIncl Q j e10 1)) :=
    double_cross Q c i e12 e9 e11 e3 (lastIncl Q j e10 1)
  have r3 : lastIncl Q i e3 (lastIncl Q c e11 (lastIncl Q j e10 1)) *
      lastIncl Q i e3 (ψ (Multiset.card l)) =
      lastIncl Q i e3 (ψ (Multiset.card l)) *
        lastIncl Q i e3 (lastIncl Q j e2 (lastIncl Q c e1 1)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (double_cross Q c j e10 e11 e1 e2 1)
  have lhs := unit_mul_absorb_three l1 (top i c j e6 e7 e5) l2 (idem c i j e1 e4 e5) l3
    (top c j i e1 e2 e3)
  have rhs := unit_mul_absorb_three r1 (idem j i c e10 e12 e9) r2 (top j c i e10 e11 e3) r3
    (idem c j i e1 e2 e3)
  rw [map_mul (lastIncl Q j e5), map_mul (lastIncl Q c e9), map_mul (lastIncl Q i e3)]
  refine lhs.trans (Eq.trans ?_ rhs.symm)
  rw [card_lastIncl i e6, card_lastIncl c e1, card_lastIncl j e10]
  exact braid_identity c j i hb.symm e6 e8 e9 e7 e5 e1 e4 e2 e3 e10 e12 e11

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR KLRAlgebra
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

local notation "S" => affineCoverQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ
local notation "π" => affineTensorProjection (Q := Q) Λ

omit [Field k] in
/-- Three actions agree on a fixed vector once their products agree after the fixing element. -/
theorem smul_three_eq_of_fix {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    {u z₁ z₂ z₃ y₁ y₂ y₃ : R} {n : N} (hn : u • n = n)
    (h : z₃ * z₂ * z₁ * u = y₃ * y₂ * y₁ * u) : z₃ • z₂ • z₁ • n = y₃ • y₂ • y₁ • n := by
  rw [← hn]
  simp only [smul_smul, mul_assoc] at h ⊢
  rw [h]

/-- **The braid relation with distinct outer colours on restrictions** between arbitrary
contents (KL I, §2.1; Brundan, arXiv:1501.00350v1, (1.4) with `i ≠ c`), for every middle
colour `j`: the mate form of `TwoRep.RouqUpKLR.braid`. -/
theorem resCrossOfEq_braid_three (hsym : KLRSymm Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : ({c} : Multiset I) + l = w₁)
    (e2 : ({j} : Multiset I) + w₁ = w₂) (e3 : ({i} : Multiset I) + w₂ = m)
    (e4 : ({i} : Multiset I) + w₁ = w₃) (e5 : ({j} : Multiset I) + w₃ = m)
    (e6 : ({i} : Multiset I) + l = w₄) (e7 : ({c} : Multiset I) + w₄ = w₃)
    (e8 : ({j} : Multiset I) + w₄ = w₅) (e9 : ({c} : Multiset I) + w₅ = m)
    (e10 : ({j} : Multiset I) + l = w₆) (e11 : ({c} : Multiset I) + w₆ = w₂)
    (e12 : ({i} : Multiset I) + w₆ = w₅) :
    Functor.whiskerRight (resCrossOfEq Λ hsym j c e7 e5 e8 e9) (blackEOfEq Q Λ i e6) ≫
        Functor.whiskerLeft (blackEOfEq Q Λ j e5) (resCrossOfEq Λ hsym i c e1 e4 e6 e7) ≫
          Functor.whiskerRight (resCrossOfEq Λ hsym i j e2 e3 e4 e5) (blackEOfEq Q Λ c e1) =
      Functor.whiskerLeft (blackEOfEq Q Λ c e9) (resCrossOfEq Λ hsym i j e10 e12 e6 e8) ≫
        Functor.whiskerRight (resCrossOfEq Λ hsym i c e11 e3 e12 e9) (blackEOfEq Q Λ j e10) ≫
          Functor.whiskerLeft (blackEOfEq Q Λ i e3) (resCrossOfEq Λ hsym j c e1 e2 e10 e11) := by
  refine NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun w =>
    Res.ext (Res.ext (Res.ext ?_))))
  have v1 := whiskerRight_resCrossOfEq_val Λ hsym j c i e7 e5 e8 e9 e6 M w
  have v2 := whiskerLeft_resCrossOfEq_val Λ hsym i c j e1 e4 e6 e7 e5 M
    (((Functor.whiskerRight (resCrossOfEq Λ hsym j c e7 e5 e8 e9)
      (blackEOfEq Q Λ i e6)).app M).hom w)
  have v3 := whiskerRight_resCrossOfEq_val Λ hsym i j c e2 e3 e4 e5 e1 M
    (((Functor.whiskerLeft (blackEOfEq Q Λ j e5) (resCrossOfEq Λ hsym i c e1 e4 e6 e7)).app
      M).hom (((Functor.whiskerRight (resCrossOfEq Λ hsym j c e7 e5 e8 e9)
        (blackEOfEq Q Λ i e6)).app M).hom w))
  have u1 := whiskerLeft_resCrossOfEq_val Λ hsym i j c e10 e12 e6 e8 e9 M w
  have u2 := whiskerRight_resCrossOfEq_val Λ hsym i c j e11 e3 e12 e9 e10 M
    (((Functor.whiskerLeft (blackEOfEq Q Λ c e9) (resCrossOfEq Λ hsym i j e10 e12 e6 e8)).app
      M).hom w)
  have u3 := whiskerLeft_resCrossOfEq_val Λ hsym j c i e1 e2 e10 e11 e3 M
    (((Functor.whiskerRight (resCrossOfEq Λ hsym i c e11 e3 e12 e9)
      (blackEOfEq Q Λ j e10)).app M).hom
      (((Functor.whiskerLeft (blackEOfEq Q Λ c e9) (resCrossOfEq Λ hsym i j e10 e12 e6 e8)).app
        M).hom w))
  refine (v3.trans ((congrArg (_ • ·) v2).trans (congrArg (_ • ·) (congrArg (_ • ·) v1)))).trans
    (Eq.trans ?_ (u3.trans ((congrArg (_ • ·) u2).trans
      (congrArg (_ • ·) (congrArg (_ • ·) u1)))).symm)
  refine smul_three_eq_of_fix (res_three_val_fix Λ i j c e6 e8 e9 M w) ?_
  simp only [← op_mul, ← map_mul, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hs : resCrossSign k i j * resCrossSign k i c * resCrossSign k j c =
      resCrossSign k j c * resCrossSign k i c * resCrossSign k i j := by ring
  rw [hs]
  congr 3
  have key := unit_mul_braid_cut (Q := S) (Sum.inl i) (Sum.inl j) (Sum.inl c)
    (Sum.inl_injective.ne hb) (stendhalWeight_cons_eq c e1) (stendhalWeight_cons_eq j e2)
    (stendhalWeight_cons_eq i e3) (stendhalWeight_cons_eq i e4) (stendhalWeight_cons_eq j e5)
    (stendhalWeight_cons_eq i e6) (stendhalWeight_cons_eq c e7) (stendhalWeight_cons_eq j e8)
    (stendhalWeight_cons_eq c e9) (stendhalWeight_cons_eq j e10) (stendhalWeight_cons_eq c e11)
    (stendhalWeight_cons_eq i e12)
  simp only [crossCoverElem, map_mul, mul_assoc] at key ⊢
  exact key

/-! ### Mates on inductions -/

omit [Field k] in
theorem adjunction_comp_assoc {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : B ⥤ C} {G₂ : C ⥤ B} {F₃ : C ⥤ D}
    {G₃ : D ⥤ C} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃) :
    (a₁.comp a₂).comp a₃ = a₁.comp (a₂.comp a₃) := by
  ext X
  simp [Adjunction.comp_unit_app]

omit [Field k] in
/-- Mates of a composite of three transformations. -/
theorem conjugateEquiv_symm_comp_three {A B : Type*} [Category A] [Category B]
    {L₀ L₁ L₂ L₃ : A ⥤ B} {R₀ R₁ R₂ R₃ : B ⥤ A} (A₀ : L₀ ⊣ R₀) (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂)
    (A₃ : L₃ ⊣ R₃) (ρ₁ : R₁ ⟶ R₀) (ρ₂ : R₂ ⟶ R₁) (ρ₃ : R₃ ⟶ R₂) :
    (conjugateEquiv A₁ A₀).symm ρ₁ ≫ (conjugateEquiv A₂ A₁).symm ρ₂ ≫
        (conjugateEquiv A₃ A₂).symm ρ₃ =
      (conjugateEquiv A₃ A₀).symm (ρ₃ ≫ ρ₂ ≫ ρ₁) := by
  rw [conjugateEquiv_symm_comp, conjugateEquiv_symm_comp, Category.assoc]

/-- An induction crossing whiskered on the left is the mate of the restriction crossing
whiskered on the right. -/
theorem whiskerLeft_indCrossOfEq (hsym : KLRSymm Q) (a b x : I) {ν μ β₁ β₂ δ : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (e : ({x} : Multiset I) + ν = μ) :
    Functor.whiskerLeft (blackFOfEq Q Λ x e) (indCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄) =
      (conjugateEquiv ((blackAdjOfEq Q Λ x e).comp
          ((blackAdjOfEq Q Λ a h₃).comp (blackAdjOfEq Q Λ b h₄)))
        ((blackAdjOfEq Q Λ x e).comp ((blackAdjOfEq Q Λ b h₁).comp (blackAdjOfEq Q Λ a h₂)))).symm
        (Functor.whiskerRight (resCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄) (blackEOfEq Q Λ x e)) := by
  rw [Equiv.eq_symm_apply, indCrossOfEq, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]

/-- An induction crossing whiskered on the right is the mate of the restriction crossing
whiskered on the left. -/
theorem whiskerRight_indCrossOfEq (hsym : KLRSymm Q) (a b x : I) {μ β₁ β₂ δ m : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (e : ({x} : Multiset I) + δ = m) :
    Functor.whiskerRight (indCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄) (blackFOfEq Q Λ x e) =
      (conjugateEquiv ((blackAdjOfEq Q Λ a h₃).comp
          ((blackAdjOfEq Q Λ b h₄).comp (blackAdjOfEq Q Λ x e)))
        ((blackAdjOfEq Q Λ b h₁).comp ((blackAdjOfEq Q Λ a h₂).comp (blackAdjOfEq Q Λ x e)))).symm
        (Functor.whiskerLeft (blackEOfEq Q Λ x e) (resCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄)) := by
  have h := conjugateEquiv_whiskerRight ((blackAdjOfEq Q Λ a h₃).comp (blackAdjOfEq Q Λ b h₄))
    ((blackAdjOfEq Q Λ b h₁).comp (blackAdjOfEq Q Λ a h₂)) (blackAdjOfEq Q Λ x e)
    (indCrossOfEq Λ hsym a b h₁ h₂ h₃ h₄)
  rw [adjunction_comp_assoc, adjunction_comp_assoc] at h
  exact (Equiv.eq_symm_apply _).mpr (h.trans (by rw [indCrossOfEq, Equiv.apply_symm_apply]))

/-- **The braid relation with distinct outer colours on black inductions** between arbitrary
contents (KL I, §2.1; Brundan, arXiv:1501.00350v1, (1.4) with `i ≠ c`, the block form of
`TwoRep.RouqUpKLR.braid`), the mate of `resCrossOfEq_braid_three`. -/
theorem indCrossOfEq_braid_three (hsym : KLRSymm Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : ({c} : Multiset I) + l = w₁)
    (e2 : ({j} : Multiset I) + w₁ = w₂) (e3 : ({i} : Multiset I) + w₂ = m)
    (e4 : ({i} : Multiset I) + w₁ = w₃) (e5 : ({j} : Multiset I) + w₃ = m)
    (e6 : ({i} : Multiset I) + l = w₄) (e7 : ({c} : Multiset I) + w₄ = w₃)
    (e8 : ({j} : Multiset I) + w₄ = w₅) (e9 : ({c} : Multiset I) + w₅ = m)
    (e10 : ({j} : Multiset I) + l = w₆) (e11 : ({c} : Multiset I) + w₆ = w₂)
    (e12 : ({i} : Multiset I) + w₆ = w₅) :
    Functor.whiskerLeft (blackFOfEq Q Λ c e1) (indCrossOfEq Λ hsym i j e2 e3 e4 e5) ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym i c e1 e4 e6 e7) (blackFOfEq Q Λ j e5) ≫
          Functor.whiskerLeft (blackFOfEq Q Λ i e6) (indCrossOfEq Λ hsym j c e7 e5 e8 e9) =
      Functor.whiskerRight (indCrossOfEq Λ hsym j c e1 e2 e10 e11) (blackFOfEq Q Λ i e3) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ j e10) (indCrossOfEq Λ hsym i c e11 e3 e12 e9) ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i j e10 e12 e6 e8) (blackFOfEq Q Λ c e9) := by
  rw [whiskerLeft_indCrossOfEq, whiskerRight_indCrossOfEq, whiskerLeft_indCrossOfEq,
    whiskerRight_indCrossOfEq, whiskerLeft_indCrossOfEq, whiskerRight_indCrossOfEq]
  refine (conjugateEquiv_symm_comp_three _ _ _ _ _ _ _).trans (Eq.trans ?_
    (conjugateEquiv_symm_comp_three _ _ _ _ _ _ _).symm)
  refine congrArg _ ?_
  simpa only [Category.assoc] using resCrossOfEq_braid_three Λ hsym i j c hb e1 e2 e3 e4 e5 e6 e7
    e8 e9 e10 e11 e12

end Categorification.Stendhal
