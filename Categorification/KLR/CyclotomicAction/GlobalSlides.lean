/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalBraidQ

/-!
# The nil-Hecke dot slides on weight spaces

The dot slides for two strands of the same colour (Brundan, arXiv:1501.00350v1, (1.2) for equal
labels, the `slide_left` and `slide_right` fields of `TwoRep.RouqLoc`) for the crossings
`globalCross i i` of the cyclotomic Rouquier family on weight spaces (KL III Thm. 1.2):
`globalCross_slide_left_self`, `globalCross_slide_right_self`.

For a block `γ`, `pairCompat` is the subalgebra of pairs of endomorphisms of `E_i E_j` on weight
spaces and of the composite of two cyclotomic induction functors at `γ` that are intertwined by
the generators `gen₂`. Both sides of each slide lie in it with their blockwise counterparts, and
the relations follow from the blockwise ones (`sameCross_slide_left`, `sameCross_slide_right`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)

/-- **Endomorphisms of `E_j E_i` compatible with the generators at a block `γ`**: pairs of an
endomorphism of the composite on weight spaces and of the composite of cyclotomic induction
functors starting at `γ`, intertwined by the generators `gen₂`. -/
def pairCompat (i j : I) {w₀ w₁ w₂ : X} (h₁ : w₀ + RD.iX j = w₁) (h₂ : w₁ + RD.iX i = w₂)
    (γ : WeightBlocks RD Λ w₀) :
    Subalgebra k (End (globalE.{u, v, w} Q a RD Λ j h₁ ≫ globalE Q a RD Λ i h₂) ×
      End (ind.{u, v, w} Q a j (blockSucc_step RD Λ j h₁ γ) ⋙
        ind Q a i (blockSucc_step RD Λ i h₂ _))) :=
  compatSubalgebra _ _ (fun M => M γ)
    (Pi.eval _ (blockSucc RD Λ i h₂ (blockSucc RD Λ j h₁ γ)))
    (fun M => gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
      (indBlock Q a RD Λ i h₂) M γ rfl rfl)

theorem whiskerLeft_globalDot_comp_globalCross_mem (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) (γ : WeightBlocks RD Λ w₀) :
    (globalE.{u, v, w} Q a RD Λ i h₁ ◁ globalDot Q a RD Λ i h₂ ≫
        globalCross Q a RD Λ i i h₁ h₂ h₁ h₂,
      Functor.whiskerLeft (ind Q a i (blockSucc_step RD Λ i h₁ γ))
          (dot Q a i (blockSucc_step RD Λ i h₂ _)) ≫
        signedCross Q a i i (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _)
          (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _)) ∈
      pairCompat Q a RD Λ i i h₁ h₂ γ := fun M =>
  gen_comp_comp (gen₂_whiskerLeft_globalDot Q a RD Λ i i h₁ h₂ M γ rfl rfl)
    (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)

theorem globalCross_comp_globalDot_whiskerRight_mem (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) (γ : WeightBlocks RD Λ w₀) :
    (globalCross.{u, v, w} Q a RD Λ i i h₁ h₂ h₁ h₂ ≫
        globalDot Q a RD Λ i h₁ ▷ globalE Q a RD Λ i h₂,
      signedCross Q a i i (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _)
          (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _) ≫
        Functor.whiskerRight (dot Q a i (blockSucc_step RD Λ i h₁ γ))
          (ind Q a i (blockSucc_step RD Λ i h₂ _))) ∈
      pairCompat Q a RD Λ i i h₁ h₂ γ := fun M =>
  gen_comp_comp (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
    (gen₂_globalDot_whiskerRight Q a RD Λ i i h₁ h₂ M γ rfl rfl)

theorem globalCross_comp_whiskerLeft_globalDot_mem (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) (γ : WeightBlocks RD Λ w₀) :
    (globalCross.{u, v, w} Q a RD Λ i i h₁ h₂ h₁ h₂ ≫
        globalE Q a RD Λ i h₁ ◁ globalDot Q a RD Λ i h₂,
      signedCross Q a i i (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _)
          (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _) ≫
        Functor.whiskerLeft (ind Q a i (blockSucc_step RD Λ i h₁ γ))
          (dot Q a i (blockSucc_step RD Λ i h₂ _))) ∈
      pairCompat Q a RD Λ i i h₁ h₂ γ := fun M =>
  gen_comp_comp (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)
    (gen₂_whiskerLeft_globalDot Q a RD Λ i i h₁ h₂ M γ rfl rfl)

theorem globalDot_whiskerRight_comp_globalCross_mem (i : I) {w₀ w₁ w₂ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX i = w₂) (γ : WeightBlocks RD Λ w₀) :
    (globalDot.{u, v, w} Q a RD Λ i h₁ ▷ globalE Q a RD Λ i h₂ ≫
        globalCross Q a RD Λ i i h₁ h₂ h₁ h₂,
      Functor.whiskerRight (dot Q a i (blockSucc_step RD Λ i h₁ γ))
          (ind Q a i (blockSucc_step RD Λ i h₂ _)) ≫
        signedCross Q a i i (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _)
          (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ i h₂ _)) ∈
      pairCompat Q a RD Λ i i h₁ h₂ γ := fun M =>
  gen_comp_comp (gen₂_globalDot_whiskerRight Q a RD Λ i i h₁ h₂ M γ rfl rfl)
    (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ rfl rfl rfl rfl)

/-- **The nil-Hecke left dot slide on weight spaces** (Brundan, arXiv:1501.00350v1, (1.2) for
equal labels, the shape of `TwoRep.RouqLoc.slide_left`). -/
theorem globalCross_slide_left_self (i : I) {w₀ w₁ w₂ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX i = w₂) :
    globalE.{u, v, w} Q a RD Λ i h₁ ◁ globalDot Q a RD Λ i h₂ ≫
        globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ -
      globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ ≫ globalDot Q a RD Λ i h₁ ▷ globalE Q a RD Λ i h₂ =
      𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₁)
    (indBlock Q a RD Λ i h₂) fun γ β δ hb hd => ?_
  subst hb hd
  have hS := Subalgebra.sub_mem _ (whiskerLeft_globalDot_comp_globalCross_mem Q a RD Λ i h₁ h₂ γ)
    (globalCross_comp_globalDot_whiskerRight_mem Q a RD Λ i h₁ h₂ γ)
  rw [Prod.mk_sub_mk, signedCross_self, sameCross_slide_left] at hS
  exact (hS M).trans ((pairCompat Q a RD Λ i i h₁ h₂ γ).one_mem M).symm

/-- **The nil-Hecke right dot slide on weight spaces** (Brundan, arXiv:1501.00350v1, (1.2) for
equal labels, the shape of `TwoRep.RouqLoc.slide_right`). -/
theorem globalCross_slide_right_self (i : I) {w₀ w₁ w₂ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX i = w₂) :
    globalCross.{u, v, w} Q a RD Λ i i h₁ h₂ h₁ h₂ ≫
        globalE Q a RD Λ i h₁ ◁ globalDot Q a RD Λ i h₂ -
      globalDot Q a RD Λ i h₁ ▷ globalE Q a RD Λ i h₂ ≫ globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ =
      𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₁)
    (indBlock Q a RD Λ i h₂) fun γ β δ hb hd => ?_
  subst hb hd
  have hS := Subalgebra.sub_mem _ (globalCross_comp_whiskerLeft_globalDot_mem Q a RD Λ i h₁ h₂ γ)
    (globalDot_whiskerRight_comp_globalCross_mem Q a RD Λ i h₁ h₂ γ)
  rw [Prod.mk_sub_mk, signedCross_self, sameCross_slide_right] at hS
  exact (hS M).trans ((pairCompat Q a RD Λ i i h₁ h₂ γ).one_mem M).symm

end

end Categorification.KLR.CyclotomicAction
