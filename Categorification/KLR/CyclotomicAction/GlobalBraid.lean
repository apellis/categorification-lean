/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Braid
import Categorification.KLR.CyclotomicAction.GlobalCross
import Categorification.TwoRep.BlockSumTriple

/-!
# The braid relations of the weight-indexed cyclotomic Rouquier family

The braid relations (KL I §2.1; Brundan, arXiv:1501.00350v1, (1.4)) for the crossings
`globalCross` of the cyclotomic Rouquier family on weight spaces (KL III Thm. 1.2):

* `globalCross_braid`: outer labels `i ≠ c` and any middle label `j`, in the shape of
  `TwoRep.RouqUpKLR.braid`;
* `globalCross_sameBraid`: three strands of the same colour, in the shape of
  `TwoRep.RouqFamily.braid`.

Each is checked on the generators of a composite of three block sums (`TwoRep.gen₃_ext`), where
it is the corresponding relation for cyclotomic induction functors with the signed crossings
`signedCross` (`signedCross_braid`, `signedCross_sameBraid`; the crossing of two strands of the
same colour is `-ψ`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep QuantumGroup

universe u v w u₁

noncomputable section


variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

theorem signedCross_same (i : I) {γ β β' δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ)
    (h₃ : {i} + γ = β') (h₄ : {i} + β' = δ) :
    signedCross.{u, v, w} Q a i i h₁ h₂ h₃ h₄ = -cross Q a i i h₁ h₂ h₃ h₄ := by
  simp [signedCross]

/-- The braid relation with distinct outer labels for the signed crossings. -/
theorem signedCross_braid (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : {c} + l = w₁) (e2 : {j} + w₁ = w₂)
    (e3 : {i} + w₂ = m) (e4 : {i} + w₁ = w₃) (e5 : {j} + w₃ = m)
    (e6 : {i} + l = w₄) (e7 : {c} + w₄ = w₃) (e8 : {j} + w₄ = w₅)
    (e9 : {c} + w₅ = m) (e10 : {j} + l = w₆) (e11 : {c} + w₆ = w₂)
    (e12 : {i} + w₆ = w₅) :
    Functor.whiskerLeft (ind.{u, v, w} Q a c e1) (signedCross Q a i j e2 e3 e4 e5) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (signedCross Q a i c e1 e4 e6 e7) (ind Q a j e5) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i e6) (signedCross Q a j c e7 e5 e8 e9) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (signedCross Q a j c e1 e2 e10 e11) (ind Q a i e3) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a j e10) (signedCross Q a i c e11 e3 e12 e9) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (signedCross Q a i j e10 e12 e6 e8) (ind Q a c e9) ≫
          (Functor.associator _ _ _).hom) := by
  have B := braid Q a i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  rw [signedCross_of_ne Q a hb, signedCross_of_ne Q a hb]
  by_cases hij : i = j
  · subst hij
    rw [signedCross_of_ne Q a hb, signedCross_of_ne Q a hb, signedCross_same, signedCross_same]
    ext x
    have Bx := congrArg (fun η => NatTrans.app η x) B
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.app_neg, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg] at Bx ⊢
    rw [Bx]
  by_cases hjc : j = c
  · subst hjc
    rw [signedCross_of_ne Q a hij, signedCross_same, signedCross_same,
      signedCross_of_ne Q a hij]
    ext x
    have Bx := congrArg (fun η => NatTrans.app η x) B
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.app_neg, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg] at Bx ⊢
    rw [Bx]
  rw [signedCross_of_ne Q a hij, signedCross_of_ne Q a hjc, signedCross_of_ne Q a hjc,
    signedCross_of_ne Q a hij]
  exact B

/-- The braid relation for three strands of the same colour, for the signed crossings. -/
theorem signedCross_sameBraid (i : I) {γ β β₁ δ : Multiset I} (h₁ : {i} + γ = β)
    (h₂ : {i} + β = β₁) (h₃ : {i} + β₁ = δ) :
    Functor.whiskerLeft (ind.{u, v, w} Q a i h₁) (signedCross Q a i i h₂ h₃ h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (signedCross Q a i i h₁ h₂ h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i h₁) (signedCross Q a i i h₂ h₃ h₂ h₃) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (signedCross Q a i i h₁ h₂ h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i h₁) (signedCross Q a i i h₂ h₃ h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (signedCross Q a i i h₁ h₂ h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) := by
  rw [signedCross_self, signedCross_self]
  exact sameCross_braid Q a i h₁ h₂ h₃

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)

/-- The associator of `LinearCat k` on generators. -/
theorem gen_assoc {𝒟 : Type*} [Category 𝒟] {P G : 𝒟} (g : P ⟶ G) : g ≫ 𝟙 G = 𝟙 P ≫ g :=
  (Category.comp_id g).trans (Category.id_comp g).symm

/-- **The braid relation with distinct outer labels on weight spaces** (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.4), the shape of `TwoRep.RouqUpKLR.braid`). -/
theorem globalCross_braid (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅) :
    globalE.{u, v, w} Q a RD Λ c e1 ◁ globalCross Q a RD Λ i j e2 e3 e4 e5 ≫
        ((α_ (globalE Q a RD Λ c e1) (globalE Q a RD Λ i e4) (globalE Q a RD Λ j e5)).inv ≫
          globalCross Q a RD Λ i c e1 e4 e6 e7 ▷ globalE Q a RD Λ j e5 ≫
          (α_ (globalE Q a RD Λ i e6) (globalE Q a RD Λ c e7) (globalE Q a RD Λ j e5)).hom) ≫
        globalE Q a RD Λ i e6 ◁ globalCross Q a RD Λ j c e7 e5 e8 e9 =
      ((α_ (globalE Q a RD Λ c e1) (globalE Q a RD Λ j e2) (globalE Q a RD Λ i e3)).inv ≫
          globalCross Q a RD Λ j c e1 e2 e10 e11 ▷ globalE Q a RD Λ i e3 ≫
          (α_ (globalE Q a RD Λ j e10) (globalE Q a RD Λ c e11) (globalE Q a RD Λ i e3)).hom) ≫
        globalE Q a RD Λ j e10 ◁ globalCross Q a RD Λ i c e11 e3 e12 e9 ≫
        ((α_ (globalE Q a RD Λ j e10) (globalE Q a RD Λ i e12) (globalE Q a RD Λ c e9)).inv ≫
          globalCross Q a RD Λ i j e10 e12 e6 e8 ▷ globalE Q a RD Λ c e9 ≫
          (α_ (globalE Q a RD Λ i e6) (globalE Q a RD Λ j e8) (globalE Q a RD Λ c e9)).hom) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ c e1) (blockSucc RD Λ j e2) (blockSucc RD Λ i e3)
    (indBlock Q a RD Λ c e1) (indBlock Q a RD Λ j e2) (indBlock Q a RD Λ i e3)
    fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have k1 : blockSucc RD Λ j e5 (blockSucc RD Λ i e4 (blockSucc RD Λ c e1 γ)) =
      blockSucc RD Λ i e3 (blockSucc RD Λ j e2 (blockSucc RD Λ c e1 γ)) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have k2 : blockSucc RD Λ c e7 (blockSucc RD Λ i e6 γ) =
      blockSucc RD Λ i e4 (blockSucc RD Λ c e1 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have k3 : blockSucc RD Λ c e9 (blockSucc RD Λ j e8 (blockSucc RD Λ i e6 γ)) =
      blockSucc RD Λ i e3 (blockSucc RD Λ j e2 (blockSucc RD Λ c e1 γ)) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have r1 : blockSucc RD Λ c e11 (blockSucc RD Λ j e10 γ) =
      blockSucc RD Λ j e2 (blockSucc RD Λ c e1 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have r2 : blockSucc RD Λ i e12 (blockSucc RD Λ j e10 γ) =
      blockSucc RD Λ j e8 (blockSucc RD Λ i e6 γ) :=
    Subtype.ext (by simp only [blockSucc_val]; abel)
  have s1 := gen₃_whiskerLeft (blockSucc RD Λ c e1) (blockSucc RD Λ j e2) (blockSucc RD Λ i e3)
      (indBlock Q a RD Λ c e1) (indBlock Q a RD Λ j e2) (indBlock Q a RD Λ i e3)
      (s₂' := blockSucc RD Λ i e4) (s₃' := blockSucc RD Λ j e5) (L₂' := indBlock Q a RD Λ i e4)
      (L₃' := indBlock Q a RD Λ j e5)
      (globalCross Q a RD Λ i j e2 e3 e4 e5).hom M γ rfl rfl rfl rfl k1 _
      (gen₂_globalCross Q a RD Λ i j e2 e3 e4 e5 _ _ rfl rfl rfl k1)
  have s3 := gen₃_whiskerRight (blockSucc RD Λ c e1) (blockSucc RD Λ i e4) (blockSucc RD Λ j e5)
      (indBlock Q a RD Λ c e1) (indBlock Q a RD Λ i e4) (indBlock Q a RD Λ j e5)
      (s₁' := blockSucc RD Λ i e6) (s₂' := blockSucc RD Λ c e7) (L₁' := indBlock Q a RD Λ i e6)
      (L₂' := indBlock Q a RD Λ c e7)
      (globalCross Q a RD Λ i c e1 e4 e6 e7).hom M γ rfl rfl rfl k2 k1 _
      (gen₂_globalCross Q a RD Λ i c e1 e4 e6 e7 M γ rfl rfl rfl k2)
  have s5 := gen₃_whiskerLeft (blockSucc RD Λ i e6) (blockSucc RD Λ c e7) (blockSucc RD Λ j e5)
      (indBlock Q a RD Λ i e6) (indBlock Q a RD Λ c e7) (indBlock Q a RD Λ j e5)
      (s₂' := blockSucc RD Λ j e8) (s₃' := blockSucc RD Λ c e9) (L₂' := indBlock Q a RD Λ j e8)
      (L₃' := indBlock Q a RD Λ c e9)
      (globalCross Q a RD Λ j c e7 e5 e8 e9).hom M γ rfl k2 k1 rfl k3 _
      (gen₂_globalCross Q a RD Λ j c e7 e5 e8 e9 _ _ k2 k1 rfl k3)
  have t2 := gen₃_whiskerRight (blockSucc RD Λ c e1) (blockSucc RD Λ j e2) (blockSucc RD Λ i e3)
      (indBlock Q a RD Λ c e1) (indBlock Q a RD Λ j e2) (indBlock Q a RD Λ i e3)
      (s₁' := blockSucc RD Λ j e10) (s₂' := blockSucc RD Λ c e11) (L₁' := indBlock Q a RD Λ j e10)
      (L₂' := indBlock Q a RD Λ c e11)
      (globalCross Q a RD Λ j c e1 e2 e10 e11).hom M γ rfl rfl rfl r1 rfl _
      (gen₂_globalCross Q a RD Λ j c e1 e2 e10 e11 M γ rfl rfl rfl r1)
  have t4 := gen₃_whiskerLeft (blockSucc RD Λ j e10) (blockSucc RD Λ c e11) (blockSucc RD Λ i e3)
      (indBlock Q a RD Λ j e10) (indBlock Q a RD Λ c e11) (indBlock Q a RD Λ i e3)
      (s₂' := blockSucc RD Λ i e12) (s₃' := blockSucc RD Λ c e9) (L₂' := indBlock Q a RD Λ i e12)
      (L₃' := indBlock Q a RD Λ c e9)
      (globalCross Q a RD Λ i c e11 e3 e12 e9).hom M γ rfl r1 rfl r2 k3 _
      (gen₂_globalCross Q a RD Λ i c e11 e3 e12 e9 _ _ r1 rfl r2 k3)
  have t6 := gen₃_whiskerRight (blockSucc RD Λ j e10) (blockSucc RD Λ i e12) (blockSucc RD Λ c e9)
      (indBlock Q a RD Λ j e10) (indBlock Q a RD Λ i e12) (indBlock Q a RD Λ c e9)
      (s₁' := blockSucc RD Λ i e6) (s₂' := blockSucc RD Λ j e8) (L₁' := indBlock Q a RD Λ i e6)
      (L₂' := indBlock Q a RD Λ j e8)
      (globalCross Q a RD Λ i j e10 e12 e6 e8).hom M γ rfl r2 rfl rfl k3 _
      (gen₂_globalCross Q a RD Λ i j e10 e12 e6 e8 M γ rfl r2 rfl rfl)
  refine (gen_chain_left s1 (gen_assoc _) s3 (gen_assoc _) s5).trans
    (Eq.trans ?_ (gen_chain_right (gen_assoc _) t2 (gen_assoc _) t4 (gen_assoc _) t6
      (gen_assoc _)).symm)
  exact congrArg (· ≫ _) (congrArg (fun η => NatTrans.app η (M γ))
    (signedCross_braid Q a i j c hb _ _ _ _ _ _ _ _ _ _ _ _))

/-- **The braid relation for three strands of the same colour on weight spaces** (Brundan,
arXiv:1501.00350v1, (1.4) for equal labels, the shape of `TwoRep.RouqFamily.braid`). -/
theorem globalCross_sameBraid (i : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX i = w₂) (h₃ : w₂ + RD.iX i = w₃) :
    globalE.{u, v, w} Q a RD Λ i h₁ ◁ globalCross Q a RD Λ i i h₂ h₃ h₂ h₃ ≫
      ((α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₂) (globalE Q a RD Λ i h₃)).inv ≫
        globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ ▷ globalE Q a RD Λ i h₃ ≫
        (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₂) (globalE Q a RD Λ i h₃)).hom) ≫
      globalE Q a RD Λ i h₁ ◁ globalCross Q a RD Λ i i h₂ h₃ h₂ h₃ =
    ((α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₂) (globalE Q a RD Λ i h₃)).inv ≫
      globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ ▷ globalE Q a RD Λ i h₃ ≫
      (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₂) (globalE Q a RD Λ i h₃)).hom) ≫
      globalE Q a RD Λ i h₁ ◁ globalCross Q a RD Λ i i h₂ h₃ h₂ h₃ ≫
    ((α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₂) (globalE Q a RD Λ i h₃)).inv ≫
      globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ ▷ globalE Q a RD Λ i h₃ ≫
      (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₂) (globalE Q a RD Λ i h₃)).hom) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (blockSucc RD Λ i h₃)
    (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ i h₂) (indBlock Q a RD Λ i h₃)
    fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have s1 := gen₃_whiskerLeft (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (blockSucc RD Λ i h₃)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ i h₂) (indBlock Q a RD Λ i h₃)
      (s₂' := blockSucc RD Λ i h₂) (s₃' := blockSucc RD Λ i h₃) (L₂' := indBlock Q a RD Λ i h₂)
      (L₃' := indBlock Q a RD Λ i h₃)
      (globalCross Q a RD Λ i i h₂ h₃ h₂ h₃).hom M γ rfl rfl rfl rfl rfl _
      (gen₂_globalCross Q a RD Λ i i h₂ h₃ h₂ h₃ _ _ rfl rfl rfl rfl)
  have s2 := gen₃_whiskerRight (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (blockSucc RD Λ i h₃)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ i h₂) (indBlock Q a RD Λ i h₃)
      (s₁' := blockSucc RD Λ i h₁) (s₂' := blockSucc RD Λ i h₂) (L₁' := indBlock Q a RD Λ i h₁)
      (L₂' := indBlock Q a RD Λ i h₂)
      (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂).hom M γ rfl rfl rfl rfl rfl _
      (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
  refine (gen_chain_left s1 (gen_assoc _) s2 (gen_assoc _) s1).trans
    (Eq.trans ?_ (gen_chain_right (gen_assoc _) s2 (gen_assoc _) s1 (gen_assoc _) s2
      (gen_assoc _)).symm)
  exact congrArg (· ≫ _) (congrArg (fun η => NatTrans.app η (M γ))
    (signedCross_sameBraid Q a i _ _ _))

end

end Categorification.KLR.CyclotomicAction
