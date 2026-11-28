/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleRouqMixedInversion
import Categorification.WeightedKLR.RedStrands.BlackRouqPresCL

/-!
# The upward KLR relations for Webster's action on `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
in Brundan's form (arXiv:1501.00350v1, Definition 1.1, (1.2)–(1.4), and Theorem 1.2), for
the Rouquier family `blackModuleRouqFamily` on the weight spaces of all right `T^λ`-modules (the
abelian counterpart of `blackRouqFamily`).

* `blackModuleRouqFamily_upKLR`: the upward KLR relations for distinct colours, Brundan
  (1.2)–(1.4), with the polynomials `Q` of the family: the mixed square and dot slides
  (`blackModCross_mixed_square`, `_slide_left`, `_slide_right`) and the two braid relations
  (`blackModCross_braid`, `blackModCross_braidQ`). They are the module relations
  `indCrossOfEq_mixed_square`, `indCrossOfEq_mixed_slide_left`, `indCrossOfEq_mixed_slide_right`,
  `indCrossOfEq_braid_three` and `indCrossOfEq_braidQ`, assembled over blocks.
* `blackModuleRouqFamily_brundanUpKLR`: the same relations with Brundan's polynomials of the
  Kang–Kashiwara scalars `rouquierScalars` of `Q`.
* `blackModPresCL`: Cautis–Lauda's normalized presentation `presCL` with these scalars acts on
  the weight spaces of right `T^λ`-modules (Brundan, Theorem 1.2), with the mixed inversion
  `blackModuleRouqFamily_mixedInversion`.

The hypotheses are those of `blackModuleRouqFamily`; no route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory MulOpposite InductionAlong
  QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram
  KL3.Diagram NatTrans

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w u₁

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}

set_option hygiene false in
local notation "D" β => ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ

/-! ### Block relations with associators -/

section Blocks

variable {Q}

/-- `indCrossOfEq_braid_three` with the associators of functor composition. -/
theorem indCrossOfEq_braid_three_assoc (hsym : KLRSymm Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : ({c} : Multiset I) + l = w₁)
    (e2 : ({j} : Multiset I) + w₁ = w₂) (e3 : ({i} : Multiset I) + w₂ = m)
    (e4 : ({i} : Multiset I) + w₁ = w₃) (e5 : ({j} : Multiset I) + w₃ = m)
    (e6 : ({i} : Multiset I) + l = w₄) (e7 : ({c} : Multiset I) + w₄ = w₃)
    (e8 : ({j} : Multiset I) + w₄ = w₅) (e9 : ({c} : Multiset I) + w₅ = m)
    (e10 : ({j} : Multiset I) + l = w₆) (e11 : ({c} : Multiset I) + w₆ = w₂)
    (e12 : ({i} : Multiset I) + w₆ = w₅) :
    Functor.whiskerLeft (blackFOfEq Q Λ c e1) (indCrossOfEq Λ hsym i j e2 e3 e4 e5) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i c e1 e4 e6 e7) (blackFOfEq Q Λ j e5) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i e6) (indCrossOfEq Λ hsym j c e7 e5 e8 e9) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym j c e1 e2 e10 e11) (blackFOfEq Q Λ i e3) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ j e10) (indCrossOfEq Λ hsym i c e11 e3 e12 e9) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i j e10 e12 e6 e8) (blackFOfEq Q Λ c e9) ≫
          (Functor.associator _ _ _).hom) := by
  refine NatTrans.ext (funext fun X => ?_)
  have hX := congrArg (fun η => NatTrans.app η X)
    (indCrossOfEq_braid_three Λ hsym i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id] using hX

/-- `indCrossOfEq_braidQ` with the associators of functor composition. -/
theorem indCrossOfEq_braidQ_assoc (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {l b c d e f : Multiset I} (h₁ : ({i} : Multiset I) + l = b)
    (h₂ : ({j} : Multiset I) + b = c) (h₃ : ({i} : Multiset I) + c = f)
    (h₄ : ({i} : Multiset I) + b = d) (h₅ : ({j} : Multiset I) + d = f)
    (h₆ : ({j} : Multiset I) + l = e) (h₇ : ({i} : Multiset I) + e = c) :
    (Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i j h₂ h₃ h₄ h₅) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₄ h₁ h₄) (blackFOfEq Q Λ j h₅) ≫
        (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym j i h₄ h₅ h₂ h₃)) -
    (((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym j i h₁ h₂ h₆ h₇) (blackFOfEq Q Λ i h₃) ≫
        (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft (blackFOfEq Q Λ j h₆) (indCrossOfEq Λ hsym i i h₇ h₃ h₇ h₃) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym i j h₆ h₇ h₁ h₂) (blackFOfEq Q Λ i h₃) ≫
        (Functor.associator _ _ _).hom)) =
      KLR.ncEval (A := End (blackFOfEq Q Λ i h₁ ⋙ blackFOfEq Q Λ j h₂ ⋙ blackFOfEq Q Λ i h₃))
        ![Functor.whiskerLeft (blackFOfEq Q Λ i h₁)
            (Functor.whiskerLeft (blackFOfEq Q Λ j h₂) (indDotOfEq Q Λ i h₃)),
          Functor.whiskerLeft (blackFOfEq Q Λ i h₁)
            (Functor.whiskerRight (indDotOfEq Q Λ j h₂) (blackFOfEq Q Λ i h₃)),
          Functor.whiskerRight (indDotOfEq Q Λ i h₁)
            (blackFOfEq Q Λ j h₂ ⋙ blackFOfEq Q Λ i h₃)] (KLR.qbar (Q i j)) := by
  refine Eq.trans ?_ (indCrossOfEq_braidQ Λ hsym i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇)
  refine NatTrans.ext (funext fun X => ?_)
  simp only [NatTrans.app_sub, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id]

end Blocks
variable {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y)
  (Λ₀ : X)

/-! ### The mixed square and dot slides on weight spaces -/

/-- **The mixed quadratic relation on weight spaces** (Brundan, arXiv:1501.00350v1, (1.3), the
shape of `TwoRep.RouqUpKLR.square`). -/
theorem blackModCross_mixed_square (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j) {x y z t : X}
    (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ ≫
        blackModCross Q Λ RD Λ₀ hsym j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (blackModE Q Λ RD Λ₀ j h₁ ≫ blackModE Q Λ RD Λ₀ i h₂))
        ![blackModE Q Λ RD Λ₀ j h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂,
          blackModDot Q Λ RD Λ₀ j h₁ ▷ blackModE Q Λ RD Λ₀ i h₂] (Q i j) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
    (moduleFBlock Q Λ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ₀ j h₄ (blockSucc RD Λ₀ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  have hR := ncEval_compat (blackModE Q Λ RD Λ₀ j h₁ ≫ blackModE Q Λ RD Λ₀ i h₂)
    (blackFOfEq Q Λ j (blockSucc_eq RD Λ₀ j hb) ⋙
      blackFOfEq Q Λ i (blockSucc_eq RD Λ₀ i hd)) (fun M => M γ)
    (Pi.eval _ δ) (fun M => gen₂ (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂)
      (moduleFBlock Q Λ RD Λ₀ j h₁) (moduleFBlock Q Λ RD Λ₀ i h₂) M γ hb hd)
    ![blackModE Q Λ RD Λ₀ j h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂,
      blackModDot Q Λ RD Λ₀ j h₁ ▷ blackModE Q Λ RD Λ₀ i h₂]
    ![Functor.whiskerLeft (blackFOfEq Q Λ j (blockSucc_eq RD Λ₀ j hb))
        (indDotOfEq Q Λ i (blockSucc_eq RD Λ₀ i hd)),
      Functor.whiskerRight (indDotOfEq Q Λ j (blockSucc_eq RD Λ₀ j hb))
        (blackFOfEq Q Λ i (blockSucc_eq RD Λ₀ i hd))]
    (fun c M => by
      fin_cases c
      · exact gen₂_whiskerLeft_blackModDot Q Λ RD Λ₀ i j h₁ h₂ M γ hb hd
      · exact gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ i j h₁ h₂ M γ hb hd) (Q i j) M
  refine Eq.trans ?_ hR.symm
  rw [← indCrossOfEq_mixed_square Λ hsym hij (blockSucc_eq RD Λ₀ j hb)
    (blockSucc_eq RD Λ₀ i hd) (blockSucc_eq RD Λ₀ i (rfl : blockSucc RD Λ₀ i h₃ γ = _))
    (blockSucc_eq RD Λ₀ j e₁)]
  change gen₂ _ _ _ _ M γ hb hd ≫ ((blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄).hom.app M δ ≫
    (blackModCross Q Λ RD Λ₀ hsym j i h₃ h₄ h₁ h₂).hom.app M δ) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (gen₂_blackModCross Q Λ RD Λ₀ hsym j i h₃ h₄ h₁ h₂ M γ rfl e₁ hb hd)).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The left dot slide for distinct colours on weight spaces** (Brundan, arXiv:1501.00350v1,
(1.2), the shape of `TwoRep.RouqUpKLR.slide_left`). -/
theorem blackModCross_mixed_slide_left (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    blackModE Q Λ RD Λ₀ j h₁ ◁ blackModDot Q Λ RD Λ₀ i h₂ ≫
        blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ =
      blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ ≫
        blackModDot Q Λ RD Λ₀ i h₃ ▷ blackModE Q Λ RD Λ₀ j h₄ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
    (moduleFBlock Q Λ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ₀ j h₄ (blockSucc RD Λ₀ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  refine (gen_comp_comp (gen₂_whiskerLeft_blackModDot Q Λ RD Λ₀ i j h₁ h₂ M γ hb hd)
    (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans
    (Eq.trans ?_ (gen_comp_comp
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)
      (gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ j i h₃ h₄ M γ rfl e₁)).symm)
  rw [← NatTrans.comp_app, ← NatTrans.comp_app,
    indCrossOfEq_mixed_slide_left Λ hsym hij]

/-- **The right dot slide for distinct colours on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.2), the shape of `TwoRep.RouqUpKLR.slide_right`). -/
theorem blackModCross_mixed_slide_right (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    blackModDot Q Λ RD Λ₀ j h₁ ▷ blackModE Q Λ RD Λ₀ i h₂ ≫
        blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ =
      blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ ≫
        blackModE Q Λ RD Λ₀ i h₃ ◁ blackModDot Q Λ RD Λ₀ j h₄ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ₀ j h₁) (blockSucc RD Λ₀ i h₂) (moduleFBlock Q Λ RD Λ₀ j h₁)
    (moduleFBlock Q Λ RD Λ₀ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ₀ j h₄ (blockSucc RD Λ₀ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ₀ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  refine (gen_comp_comp (gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ i j h₁ h₂ M γ hb hd)
    (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans
    (Eq.trans ?_ (gen_comp_comp
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)
      (gen₂_whiskerLeft_blackModDot Q Λ RD Λ₀ j i h₃ h₄ M γ rfl e₁)).symm)
  rw [← NatTrans.comp_app, ← NatTrans.comp_app,
    indCrossOfEq_mixed_slide_right Λ hsym hij]

/-! ### The braid relations on weight spaces -/

/-- **The braid relation with distinct outer colours on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.4) with `i ≠ c`): the field `braid` of `TwoRep.RouqUpKLR` for the
Rouquier generators `blackModuleRouqData` on categories of `T^λ`-modules. -/
theorem blackModCross_braid (hsym : KLRSymm Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅) :
    (blackModE Q Λ RD Λ₀ c e1) ◁ blackModCross Q Λ RD Λ₀ hsym i j e2 e3 e4 e5 ≫
        ((α_ (blackModE Q Λ RD Λ₀ c e1) (blackModE Q Λ RD Λ₀ i e4) (blackModE Q Λ RD Λ₀ j
            e5)).inv ≫ blackModCross Q Λ RD Λ₀ hsym i c e1 e4 e6 e7 ▷ (blackModE Q Λ RD Λ₀ j
                e5) ≫ (α_ (blackModE Q Λ RD Λ₀ i e6) (blackModE Q Λ RD Λ₀ c e7) (blackModE Q Λ
                    RD Λ₀ j e5)).hom) ≫
        (blackModE Q Λ RD Λ₀ i e6) ◁ blackModCross Q Λ RD Λ₀ hsym j c e7 e5 e8 e9 =
      ((α_ (blackModE Q Λ RD Λ₀ c e1) (blackModE Q Λ RD Λ₀ j e2) (blackModE Q Λ RD Λ₀ i
          e3)).inv ≫ blackModCross Q Λ RD Λ₀ hsym j c e1 e2 e10 e11 ▷ (blackModE Q Λ RD Λ₀ i
              e3) ≫ (α_ (blackModE Q Λ RD Λ₀ j e10) (blackModE Q Λ RD Λ₀ c e11) (blackModE Q Λ
                  RD Λ₀ i e3)).hom) ≫
        (blackModE Q Λ RD Λ₀ j e10) ◁ blackModCross Q Λ RD Λ₀ hsym i c e11 e3 e12 e9 ≫
        ((α_ (blackModE Q Λ RD Λ₀ j e10) (blackModE Q Λ RD Λ₀ i e12) (blackModE Q Λ RD Λ₀ c
            e9)).inv ≫ blackModCross Q Λ RD Λ₀ hsym i j e10 e12 e6 e8 ▷ (blackModE Q Λ RD Λ₀ c
                e9) ≫ (α_ (blackModE Q Λ RD Λ₀ i e6) (blackModE Q Λ RD Λ₀ j e8) (blackModE Q Λ
                    RD Λ₀ c e9)).hom) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ j e2) (blockSucc RD Λ₀ i e3)
    (moduleFBlock Q Λ RD Λ₀ c e1) (moduleFBlock Q Λ RD Λ₀ j e2)
    (moduleFBlock Q Λ RD Λ₀ i e3) fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have k1 : blockSucc RD Λ₀ j e5 (blockSucc RD Λ₀ i e4 (blockSucc RD Λ₀ c e1 γ)) =
      blockSucc RD Λ₀ i e3 (blockSucc RD Λ₀ j e2 (blockSucc RD Λ₀ c e1 γ)) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have k2 : blockSucc RD Λ₀ c e7 (blockSucc RD Λ₀ i e6 γ) =
      blockSucc RD Λ₀ i e4 (blockSucc RD Λ₀ c e1 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have k3 : blockSucc RD Λ₀ c e9 (blockSucc RD Λ₀ j e8 (blockSucc RD Λ₀ i e6 γ)) =
      blockSucc RD Λ₀ i e3 (blockSucc RD Λ₀ j e2 (blockSucc RD Λ₀ c e1 γ)) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have r1 : blockSucc RD Λ₀ c e11 (blockSucc RD Λ₀ j e10 γ) =
      blockSucc RD Λ₀ j e2 (blockSucc RD Λ₀ c e1 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have r2 : blockSucc RD Λ₀ i e12 (blockSucc RD Λ₀ j e10 γ) =
      blockSucc RD Λ₀ j e8 (blockSucc RD Λ₀ i e6 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have s1 := gen₃_whiskerLeft (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ j e2)
      (blockSucc RD Λ₀ i e3) (moduleFBlock Q Λ RD Λ₀ c e1) (moduleFBlock Q Λ RD Λ₀ j e2)
      (moduleFBlock Q Λ RD Λ₀ i e3)
      (s₂' := blockSucc RD Λ₀ i e4) (s₃' := blockSucc RD Λ₀ j e5)
      (L₂' := moduleFBlock Q Λ RD Λ₀ i e4) (L₃' := moduleFBlock Q Λ RD Λ₀ j e5)
      (blackModCross Q Λ RD Λ₀ hsym i j e2 e3 e4 e5).hom M γ rfl rfl rfl rfl k1 _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i j e2 e3 e4 e5 _ _ rfl rfl rfl k1)
  have s3 := gen₃_whiskerRight (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ i e4)
      (blockSucc RD Λ₀ j e5) (moduleFBlock Q Λ RD Λ₀ c e1) (moduleFBlock Q Λ RD Λ₀ i e4)
      (moduleFBlock Q Λ RD Λ₀ j e5)
      (s₁' := blockSucc RD Λ₀ i e6) (s₂' := blockSucc RD Λ₀ c e7)
      (L₁' := moduleFBlock Q Λ RD Λ₀ i e6) (L₂' := moduleFBlock Q Λ RD Λ₀ c e7)
      (blackModCross Q Λ RD Λ₀ hsym i c e1 e4 e6 e7).hom M γ rfl rfl rfl k2 k1 _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i c e1 e4 e6 e7 M γ rfl rfl rfl k2)
  have s5 := gen₃_whiskerLeft (blockSucc RD Λ₀ i e6) (blockSucc RD Λ₀ c e7)
      (blockSucc RD Λ₀ j e5) (moduleFBlock Q Λ RD Λ₀ i e6) (moduleFBlock Q Λ RD Λ₀ c e7)
      (moduleFBlock Q Λ RD Λ₀ j e5)
      (s₂' := blockSucc RD Λ₀ j e8) (s₃' := blockSucc RD Λ₀ c e9)
      (L₂' := moduleFBlock Q Λ RD Λ₀ j e8) (L₃' := moduleFBlock Q Λ RD Λ₀ c e9)
      (blackModCross Q Λ RD Λ₀ hsym j c e7 e5 e8 e9).hom M γ rfl k2 k1 rfl k3 _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym j c e7 e5 e8 e9 _ _ k2 k1 rfl k3)
  have t2 := gen₃_whiskerRight (blockSucc RD Λ₀ c e1) (blockSucc RD Λ₀ j e2)
      (blockSucc RD Λ₀ i e3) (moduleFBlock Q Λ RD Λ₀ c e1) (moduleFBlock Q Λ RD Λ₀ j e2)
      (moduleFBlock Q Λ RD Λ₀ i e3)
      (s₁' := blockSucc RD Λ₀ j e10) (s₂' := blockSucc RD Λ₀ c e11)
      (L₁' := moduleFBlock Q Λ RD Λ₀ j e10) (L₂' := moduleFBlock Q Λ RD Λ₀ c e11)
      (blackModCross Q Λ RD Λ₀ hsym j c e1 e2 e10 e11).hom M γ rfl rfl rfl r1 rfl _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym j c e1 e2 e10 e11 M γ rfl rfl rfl r1)
  have t4 := gen₃_whiskerLeft (blockSucc RD Λ₀ j e10) (blockSucc RD Λ₀ c e11)
      (blockSucc RD Λ₀ i e3) (moduleFBlock Q Λ RD Λ₀ j e10) (moduleFBlock Q Λ RD Λ₀ c e11)
      (moduleFBlock Q Λ RD Λ₀ i e3)
      (s₂' := blockSucc RD Λ₀ i e12) (s₃' := blockSucc RD Λ₀ c e9)
      (L₂' := moduleFBlock Q Λ RD Λ₀ i e12) (L₃' := moduleFBlock Q Λ RD Λ₀ c e9)
      (blackModCross Q Λ RD Λ₀ hsym i c e11 e3 e12 e9).hom M γ rfl r1 rfl r2 k3 _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i c e11 e3 e12 e9 _ _ r1 rfl r2 k3)
  have t6 := gen₃_whiskerRight (blockSucc RD Λ₀ j e10) (blockSucc RD Λ₀ i e12)
      (blockSucc RD Λ₀ c e9) (moduleFBlock Q Λ RD Λ₀ j e10) (moduleFBlock Q Λ RD Λ₀ i e12)
      (moduleFBlock Q Λ RD Λ₀ c e9)
      (s₁' := blockSucc RD Λ₀ i e6) (s₂' := blockSucc RD Λ₀ j e8)
      (L₁' := moduleFBlock Q Λ RD Λ₀ i e6) (L₂' := moduleFBlock Q Λ RD Λ₀ j e8)
      (blackModCross Q Λ RD Λ₀ hsym i j e10 e12 e6 e8).hom M γ rfl r2 rfl rfl k3 _
      (gen₂_blackModCross Q Λ RD Λ₀ hsym i j e10 e12 e6 e8 M γ rfl r2 rfl rfl)
  refine (gen_chain_left s1 (gen_assoc _) s3 (gen_assoc _) s5).trans
    (Eq.trans ?_ (gen_chain_right (gen_assoc _) t2 (gen_assoc _) t4 (gen_assoc _) t6
      (gen_assoc _)).symm)
  exact congrArg (· ≫ _) (congrArg (fun η => NatTrans.app η (M γ))
    (indCrossOfEq_braid_three_assoc Λ hsym i j c hb _ _ _ _ _ _ _ _ _ _ _ _))

section BraidQ

variable (hsym : KLRSymm Q)

local notation "𝔼" => blackModE Q Λ RD Λ₀
local notation "𝔻" => blackModDot Q Λ RD Λ₀
local notation "𝕏" => blackModCross Q Λ RD Λ₀ hsym
local notation "𝔽" => blackFOfEq Q Λ
local notation "𝕕" => indDotOfEq Q Λ
local notation "𝕏'" => indCrossOfEq Λ hsym
local notation "𝔾" => moduleFBlock Q Λ RD Λ₀
local notation "𝕤" => blockSucc_step RD Λ₀
local notation "𝕓" => blockSucc RD Λ₀



/-- **Endomorphisms of `E_i E_j E_k` compatible with the generators at a block `γ`**: pairs of an
endomorphism of the composite on weight spaces and of the composite of black inductions
starting at `γ`, intertwined by the generators `gen₃`. -/
def blackModTripleCompat (i j l : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX l = w₃) (γ : WeightBlocks RD Λ₀ w₀) :
    Subalgebra k (End (𝔼 i h₁ ≫
        (𝔼 j h₂ ≫ 𝔼 l h₃)) ×
      End (𝔽 i (𝕤 i h₁ γ) ⋙
        𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _))) :=
  compatSubalgebra _ _ (fun M => M γ)
    (Pi.eval _ (𝕓 l h₃ (𝕓 j h₂ (𝕓 i h₁ γ))))
    (fun M => gen₃ (𝕓 i h₁) (𝕓 j h₂) (𝕓 l h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 l h₃) M γ rfl rfl rfl)

/-- The dots of `E_i E_j E_k` on weight spaces and on blocks are compatible, hence so are their
polynomial evaluations. -/
theorem blackModDots_ncEval_mem (i j l : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX l = w₃) (γ : WeightBlocks RD Λ₀ w₀)
    (p : MvPolynomial (Fin 3) k) :
    (KLR.ncEval (A := End (𝔼 i h₁ ≫
        (𝔼 j h₂ ≫ 𝔼 l h₃)))
      ![𝔼 i h₁ ◁ (𝔼 j h₂ ◁ 𝔻 l h₃),
        𝔼 i h₁ ◁ (𝔻 j h₂ ▷ 𝔼 l h₃),
        𝔻 i h₁ ▷ (𝔼 j h₂ ≫ 𝔼 l h₃)] p,
      KLR.ncEval (A := End (𝔽 i (𝕤 i h₁ γ) ⋙
          𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _)))
        ![Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ))
            (Functor.whiskerLeft (𝔽 j (𝕤 j h₂ _))
              (𝕕 l (𝕤 l h₃ _))),
          Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ))
            (Functor.whiskerRight (𝕕 j (𝕤 j h₂ _))
              (𝔽 l (𝕤 l h₃ _))),
          Functor.whiskerRight (𝕕 i (𝕤 i h₁ γ))
            (𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _))]
        p) ∈ blackModTripleCompat Q Λ RD Λ₀ i j l h₁ h₂ h₃ γ := by
  intro M
  refine ncEval_compat (𝔼 i h₁ ≫
      (𝔼 j h₂ ≫ 𝔼 l h₃))
    (𝔽 i (𝕤 i h₁ γ) ⋙
      𝔽 j (𝕤 j h₂ _) ⋙ 𝔽 l (𝕤 l h₃ _))
    (fun M => M γ)
    (Pi.eval _ (𝕓 l h₃ (𝕓 j h₂ (𝕓 i h₁ γ))))
    (fun M => gen₃ (𝕓 i h₁) (𝕓 j h₂) (𝕓 l h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 l h₃) M γ rfl rfl rfl)
    _ _ ?_ p M
  intro c M'
  fin_cases c
  · have d := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 j h₂)
      (𝕓 l h₃) (𝔾 i h₁) (𝔾 j h₂)
      (𝔾 l h₃) (s₂' := 𝕓 j h₂) (s₃' := 𝕓 l h₃)
      (L₂' := 𝔾 j h₂) (L₃' := 𝔾 l h₃)
      (𝔼 j h₂ ◁ 𝔻 l h₃).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_whiskerLeft_blackModDot Q Λ RD Λ₀ l j h₂ h₃ _ _ rfl rfl)
    exact d
  · have d := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 j h₂)
      (𝕓 l h₃) (𝔾 i h₁) (𝔾 j h₂)
      (𝔾 l h₃) (s₂' := 𝕓 j h₂) (s₃' := 𝕓 l h₃)
      (L₂' := 𝔾 j h₂) (L₃' := 𝔾 l h₃)
      (𝔻 j h₂ ▷ 𝔼 l h₃).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ l j h₂ h₃ _ _ rfl rfl)
    exact d
  · have d := gen₃_whiskerRight (𝕓 i h₁) (𝕓 j h₂)
      (𝕓 l h₃) (𝔾 i h₁) (𝔾 j h₂)
      (𝔾 l h₃) (s₁' := 𝕓 i h₁) (s₂' := 𝕓 j h₂)
      (L₁' := 𝔾 i h₁) (L₂' := 𝔾 j h₂)
      (𝔻 i h₁ ▷ 𝔼 j h₂).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_blackModDot_whiskerRight Q Λ RD Λ₀ j i h₁ h₂ M' γ rfl rfl)
    exact d

/-- The first composite of the braid relation with outer labels `i, i` on weight spaces is
compatible with its blockwise counterpart. -/
theorem blackModBraidLeft_mem (i j : I) {w₀ w₁ w₂ w₃ w₅ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅) (h₄ : w₁ + RD.iX i = w₃)
    (h₅ : w₃ + RD.iX j = w₅) (γ : WeightBlocks RD Λ₀ w₀) :
    (𝔼 i h₁ ◁ 𝕏 i j h₂ h₃ h₄ h₅ ≫
        ((α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).inv ≫
          𝕏 i i h₁ h₄ h₁ h₄ ▷ 𝔼 j h₅ ≫
          (α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).hom) ≫
        𝔼 i h₁ ◁ 𝕏 j i h₄ h₅ h₂ h₃,
      Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ)) (𝕏' i j (𝕤 j h₂ _) (𝕤 i h₃ _) (𝕤 i h₄ _)
          (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)))) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (𝕏' i i (𝕤 i h₁ γ) (𝕤 i h₄ _) (𝕤 i h₁ γ) (𝕤 i h₄ _))
            (𝔽 j (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)))) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (𝔽 i (𝕤 i h₁ γ)) (𝕏' j i (𝕤 i h₄ _)
          (blockSucc_eq RD Λ₀ j (blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)))
          (𝕤 j h₂ _) (𝕤 i h₃ _))) ∈
      blackModTripleCompat Q Λ RD Λ₀ i j i h₁ h₂ h₃ γ := by
  intro M
  have q1 := blockSucc_comm RD Λ₀ j i h₄ h₅ h₂ h₃ (𝕓 i h₁ γ)
  have u1 := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 j h₂) (𝕓 i h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 i h₃)
      (s₂' := 𝕓 i h₄) (s₃' := 𝕓 j h₅) (L₂' := 𝔾 i h₄)
      (L₃' := 𝔾 j h₅) (𝕏 i j h₂ h₃ h₄ h₅).hom M γ
      rfl rfl rfl rfl q1 _ (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₂ h₃ h₄ h₅ _ _ rfl rfl rfl q1)
  have u3 := gen₃_whiskerRight (𝕓 i h₁) (𝕓 i h₄) (𝕓 j h₅)
      (𝔾 i h₁) (𝔾 i h₄) (𝔾 j h₅)
      (s₁' := 𝕓 i h₁) (s₂' := 𝕓 i h₄) (L₁' := 𝔾 i h₁)
      (L₂' := 𝔾 i h₄) (𝕏 i i h₁ h₄ h₁ h₄).hom M γ
      rfl rfl rfl rfl q1 _ (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₁ h₄ h₁ h₄ M γ rfl rfl rfl rfl)
  have u5 := gen₃_whiskerLeft (𝕓 i h₁) (𝕓 i h₄) (𝕓 j h₅)
      (𝔾 i h₁) (𝔾 i h₄) (𝔾 j h₅)
      (s₂' := 𝕓 j h₂) (s₃' := 𝕓 i h₃) (L₂' := 𝔾 j h₂)
      (L₃' := 𝔾 i h₃) (𝕏 j i h₄ h₅ h₂ h₃).hom M γ
      rfl rfl q1 rfl rfl _ (gen₂_blackModCross Q Λ RD Λ₀ hsym j i h₄ h₅ h₂ h₃ _ _ rfl q1 rfl rfl)
  exact gen_chain_left u1 (gen_assoc _) u3 (gen_assoc _) u5

/-- The second composite of the braid relation with outer labels `i, i` on weight spaces is
compatible with its blockwise counterpart. -/
theorem blackModBraidRight_mem (i j : I) {w₀ w₁ w₂ w₄ w₅ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅) (h₆ : w₀ + RD.iX j = w₄)
    (h₇ : w₄ + RD.iX i = w₂) (γ : WeightBlocks RD Λ₀ w₀) :
    (((α_ (𝔼 i h₁) (𝔼 j h₂)
          (𝔼 i h₃)).inv ≫
        𝕏 j i h₁ h₂ h₆ h₇ ▷ 𝔼 i h₃ ≫
        (α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).hom) ≫
        𝔼 j h₆ ◁ 𝕏 i i h₇ h₃ h₇ h₃ ≫
        ((α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).inv ≫
          𝕏 i j h₆ h₇ h₁ h₂ ▷ 𝔼 i h₃ ≫
          (α_ (𝔼 i h₁) (𝔼 j h₂) (𝔼 i h₃)).hom),
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (𝕏' j i (𝕤 i h₁ γ) (𝕤 j h₂ _) (𝕤 j h₆ γ)
            (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ))) (𝔽 i (𝕤 i h₃ _)) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (𝔽 j (𝕤 j h₆ γ))
          (𝕏' i i (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ)) (𝕤 i h₃ _)
            (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ)) (𝕤 i h₃ _)) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (𝕏' i j (𝕤 j h₆ γ)
            (blockSucc_eq RD Λ₀ i (blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ)) (𝕤 i h₁ γ)
            (𝕤 j h₂ _)) (𝔽 i (𝕤 i h₃ _)) ≫
          (Functor.associator _ _ _).hom)) ∈
      blackModTripleCompat Q Λ RD Λ₀ i j i h₁ h₂ h₃ γ := by
  intro M
  have q2 := blockSucc_comm RD Λ₀ i j h₆ h₇ h₁ h₂ γ
  have v2 := gen₃_whiskerRight (𝕓 i h₁) (𝕓 j h₂) (𝕓 i h₃)
      (𝔾 i h₁) (𝔾 j h₂) (𝔾 i h₃)
      (s₁' := 𝕓 j h₆) (s₂' := 𝕓 i h₇) (L₁' := 𝔾 j h₆)
      (L₂' := 𝔾 i h₇) (𝕏 j i h₁ h₂ h₆ h₇).hom M γ
      rfl rfl rfl q2 rfl _ (gen₂_blackModCross Q Λ RD Λ₀ hsym j i h₁ h₂ h₆ h₇ M γ rfl rfl rfl q2)
  have v4 := gen₃_whiskerLeft (𝕓 j h₆) (𝕓 i h₇) (𝕓 i h₃)
      (𝔾 j h₆) (𝔾 i h₇) (𝔾 i h₃)
      (s₂' := 𝕓 i h₇) (s₃' := 𝕓 i h₃) (L₂' := 𝔾 i h₇)
      (L₃' := 𝔾 i h₃) (𝕏 i i h₇ h₃ h₇ h₃).hom M γ
      rfl q2 rfl q2 rfl _ (gen₂_blackModCross Q Λ RD Λ₀ hsym i i h₇ h₃ h₇ h₃ _ _ q2 rfl q2 rfl)
  have v6 := gen₃_whiskerRight (𝕓 j h₆) (𝕓 i h₇) (𝕓 i h₃)
      (𝔾 j h₆) (𝔾 i h₇) (𝔾 i h₃)
      (s₁' := 𝕓 i h₁) (s₂' := 𝕓 j h₂) (L₁' := 𝔾 i h₁)
      (L₂' := 𝔾 j h₂) (𝕏 i j h₆ h₇ h₁ h₂).hom M γ
      rfl q2 rfl rfl rfl _ (gen₂_blackModCross Q Λ RD Λ₀ hsym i j h₆ h₇ h₁ h₂ M γ rfl q2 rfl rfl)
  exact gen_chain_right (gen_assoc _) v2 (gen_assoc _) v4 (gen_assoc _) v6 (gen_assoc _)

/-- **The braid relation with equal outer labels on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.4) for outer labels `i, i` and middle label `j ≠ i`): the field `braidQ`
of `TwoRep.RouqUpKLR` for the Rouquier generators `blackModuleRouqData` on categories of
`T^λ`-modules. The difference of the two composites of crossings on `E_i E_j E_i` is `Q̄_ij`
evaluated at the three dots. -/
theorem blackModCross_braidQ (i j : I) (hij : i ≠ j) {w₀ w₁ w₂ w₃ w₄ w₅ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅)
    (h₄ : w₁ + RD.iX i = w₃) (h₅ : w₃ + RD.iX j = w₅)
    (h₆ : w₀ + RD.iX j = w₄) (h₇ : w₄ + RD.iX i = w₂) :
    (𝔼 i h₁ ◁ 𝕏 i j h₂ h₃ h₄ h₅ ≫
      ((α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).inv ≫
        𝕏 i i h₁ h₄ h₁ h₄ ▷ 𝔼 j h₅ ≫
        (α_ (𝔼 i h₁) (𝔼 i h₄) (𝔼 j h₅)).hom) ≫
      𝔼 i h₁ ◁ 𝕏 j i h₄ h₅ h₂ h₃) -
    (((α_ (𝔼 i h₁) (𝔼 j h₂) (𝔼 i h₃)).inv ≫
      𝕏 j i h₁ h₂ h₆ h₇ ▷ 𝔼 i h₃ ≫
      (α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).hom) ≫
      𝔼 j h₆ ◁ 𝕏 i i h₇ h₃ h₇ h₃ ≫
      ((α_ (𝔼 j h₆) (𝔼 i h₇) (𝔼 i h₃)).inv ≫
        𝕏 i j h₆ h₇ h₁ h₂ ▷ 𝔼 i h₃ ≫
        (α_ (𝔼 i h₁) (𝔼 j h₂) (𝔼 i h₃)).hom)) =
      KLR.ncEval (A := End (𝔼 i h₁ ≫
          (𝔼 j h₂ ≫ 𝔼 i h₃)))
        ![𝔼 i h₁ ◁ (𝔼 j h₂ ◁ 𝔻 i h₃),
          𝔼 i h₁ ◁ (𝔻 j h₂ ▷ 𝔼 i h₃),
          𝔻 i h₁ ▷ (𝔼 j h₂ ≫ 𝔼 i h₃)]
        (KLR.qbar (Q i j)) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (𝕓 i h₁) (𝕓 j h₂) (𝕓 i h₃)
    (𝔾 i h₁) (𝔾 j h₂) (𝔾 i h₃)
    fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have hS := Subalgebra.sub_mem _ (blackModBraidLeft_mem Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₄ h₅ γ)
    (blackModBraidRight_mem Q Λ RD Λ₀ hsym i j h₁ h₂ h₃ h₆ h₇ γ)
  rw [Prod.mk_sub_mk, indCrossOfEq_braidQ_assoc Λ hsym i j hij] at hS
  exact (hS M).trans
    (blackModDots_ncEval_mem Q Λ RD Λ₀ i j i h₁ h₂ h₃ γ (KLR.qbar (Q i j)) M).symm


end BraidQ

/-! ### The family -/

section Family

variable {Q Λ RD Λ₀} {hQ : IsRouquierQ C Q} {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom) (hsym : KLRSymm Q)
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))


/-- **The upward KLR relations for distinct colours on Webster's action on `T^λ`-modules**
(Brundan, arXiv:1501.00350v1, Definition 1.1, (1.2)–(1.4); Webster, arXiv:1309.3796v3,
Theorem 4.31), with the polynomials `Q` of the family. -/
theorem blackModuleRouqFamily_upKLR :
    RouqUpKLR (blackModuleRouqFamily hP hwf hsym hΛ₀) Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    blackModCross_mixed_square Q Λ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄
  slide_left i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    blackModCross_mixed_slide_left Q Λ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄
  slide_right i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    blackModCross_mixed_slide_right Q Λ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄
  braid i j c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
    blackModCross_braid Q Λ RD Λ₀ hsym i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ :=
    blackModCross_braidQ Q Λ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇

/-- **Brundan's upward relations for Webster's action on `T^λ`-modules**, with the
Kang–Kashiwara scalars of `Q` (Brundan, arXiv:1501.00350v1, Definition 1.1; Webster,
arXiv:1309.3796v3, Theorem 4.31). -/
theorem blackModuleRouqFamily_brundanUpKLR :
    BrundanUpKLR (blackModuleRouqFamily hP hwf hsym hΛ₀) (rouquierScalars hQ hsym) :=
  (blackModuleRouqFamily_upKLR hP hwf hsym hΛ₀).of_eq fun _ _ h =>
    eq_brundanQ C hsym _
      (fun i j hij p q hlt => coeff_eq_zero_of_lt_of_hom C (hQ.homogeneous i j hij) p q hlt) h

/-- **Cautis–Lauda's normalized `U_Q(g)` acts on Webster's categories of `T^λ`-modules**
(Brundan, arXiv:1501.00350v1, Theorem 1.2; Webster, arXiv:1309.3796v3, Theorem 4.31): the
presentation `presCL` with the Kang–Kashiwara scalars of the Rouquier family `Q` acts on the
weight spaces of the categories of right `T^λ`-modules, with `E_i`, `F_i` acting by
restriction and induction. -/
def blackModPresCL : Pseudofunctor (RevBicat (CL.presCL RD k (rouquierScalars hQ hsym)).Bicat)
    (LinearCat k) :=
  (blackModuleRouqFamily hP hwf hsym hΛ₀).presCLPseudofunctor (rouquierScalars hQ hsym)
    (blackModuleRouqFamily_brundanUpKLR hP hwf hsym hΛ₀)
    (blackModuleRouqFamily_mixedInversion hP hwf hsym hΛ₀) (fun _ => rfl)
    (kkScalars_s_eq_zero C hsym _ hQ.homogeneous)

end Family

end Categorification.Stendhal
