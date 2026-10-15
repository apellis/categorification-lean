/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalBraid

/-!
# The braid relation with equal outer labels on weight spaces

The braid relation for outer labels `i, i` and middle label `j ≠ i` (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.4)) for the crossings `globalCross` of the cyclotomic Rouquier family on
weight spaces (KL III Thm. 1.2), in the shape of `TwoRep.RouqUpKLR.braidQ`: the difference of
the two composites of crossings `E_i E_j E_i ⟶ E_i E_j E_i` is `Q̄_ij` evaluated at the three
dots (`globalCross_braidQ`).

For a block `γ`, the pairs of endomorphisms of `E_i E_j E_i` on weight spaces and of the
composite of three cyclotomic induction functors at `γ` that are intertwined by the generators
form a `k`-subalgebra (`tripleCompat`, an instance of `TwoRep.compatSubalgebra`). The two
composites of crossings, and the polynomial in the dots, lie in it together with their blockwise
counterparts (`braidLeft_mem`, `braidRight_mem`, `ncEval_dots_mem`); the relation then follows
from the blockwise relation `braidQ`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

/-- The first composite of the braid relation with outer labels `i, i`, for signed crossings:
`(1 ψ_ij)(ψ_ii 1)(1 ψ_ji)` read on `F_i F_j F_i`. -/
def braidLeft (i j : I) {γ β β₁ β₂ δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {j} + β = β₁)
    (h₃ : {i} + β₁ = δ) (h₄ : {i} + β = β₂) (h₅ : {j} + β₂ = δ) :
    ind.{u, v, w} Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃ ⟶
      ind Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃ :=
  Functor.whiskerLeft (ind Q a i h₁) (signedCross Q a i j h₂ h₃ h₄ h₅) ≫
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (signedCross Q a i i h₁ h₄ h₁ h₄) (ind Q a j h₅) ≫
      (Functor.associator _ _ _).hom) ≫
    Functor.whiskerLeft (ind Q a i h₁) (signedCross Q a j i h₄ h₅ h₂ h₃)

/-- The second composite of the braid relation with outer labels `i, i`, for signed crossings:
`(ψ_ji 1)(1 ψ_ii)(ψ_ij 1)` read on `F_i F_j F_i`. -/
def braidRight (i j : I) {γ β β₁ β₃ δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {j} + β = β₁)
    (h₃ : {i} + β₁ = δ) (h₆ : {j} + γ = β₃) (h₇ : {i} + β₃ = β₁) :
    ind.{u, v, w} Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃ ⟶
      ind Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃ :=
  ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (signedCross Q a j i h₁ h₂ h₆ h₇) (ind Q a i h₃) ≫
      (Functor.associator _ _ _).hom) ≫
    Functor.whiskerLeft (ind Q a j h₆) (signedCross Q a i i h₇ h₃ h₇ h₃) ≫
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (signedCross Q a i j h₆ h₇ h₁ h₂) (ind Q a i h₃) ≫
      (Functor.associator _ _ _).hom)

/-- The braid relation with equal outer labels on blocks, for the signed crossings. -/
theorem braidLeft_sub_braidRight (i j : I) (hij : i ≠ j) {γ β β₁ β₂ β₃ δ : Multiset I}
    (h₁ : {i} + γ = β) (h₂ : {j} + β = β₁) (h₃ : {i} + β₁ = δ) (h₄ : {i} + β = β₂)
    (h₅ : {j} + β₂ = δ) (h₆ : {j} + γ = β₃) (h₇ : {i} + β₃ = β₁) :
    braidLeft.{u, v, w} Q a i j h₁ h₂ h₃ h₄ h₅ - braidRight Q a i j h₁ h₂ h₃ h₆ h₇ =
      KLR.ncEval (A := End (ind.{u, v, w} Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃))
        ![Functor.whiskerLeft (ind Q a i h₁) (Functor.whiskerLeft (ind Q a j h₂) (dot Q a i h₃)),
          Functor.whiskerLeft (ind Q a i h₁) (Functor.whiskerRight (dot Q a j h₂) (ind Q a i h₃)),
          Functor.whiskerRight (dot Q a i h₁) (ind Q a j h₂ ⋙ ind Q a i h₃)]
        (KLR.qbar (Q i j)) := by
  rw [braidLeft, braidRight, signedCross_of_ne Q a hij, signedCross_of_ne Q a hij,
    signedCross_of_ne Q a (Ne.symm hij), signedCross_of_ne Q a (Ne.symm hij), signedCross_self,
    signedCross_self]
  exact braidQ Q a i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)

omit [DecidableEq I] in
/-- The multiset identity of appending a strand to a block. -/
theorem blockSucc_step (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ x) :
    {i} + β.1 = (blockSucc RD Λ i h β).1 :=
  rfl

/-- **Endomorphisms of `E_i E_j E_k` compatible with the generators at a block `γ`**: pairs of an
endomorphism of the composite on weight spaces and of the composite of cyclotomic induction
functors starting at `γ`, intertwined by the generators `gen₃`. -/
def tripleCompat (i j l : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX l = w₃) (γ : WeightBlocks RD Λ w₀) :
    Subalgebra k (End (globalE.{u, v, w} Q a RD Λ i h₁ ≫
        (globalE Q a RD Λ j h₂ ≫ globalE Q a RD Λ l h₃)) ×
      End (ind.{u, v, w} Q a i (blockSucc_step RD Λ i h₁ γ) ⋙
        ind Q a j (blockSucc_step RD Λ j h₂ _) ⋙ ind Q a l (blockSucc_step RD Λ l h₃ _))) :=
  compatSubalgebra _ _ (fun M => M γ)
    (Pi.eval _ (blockSucc RD Λ l h₃ (blockSucc RD Λ j h₂ (blockSucc RD Λ i h₁ γ))))
    (fun M => gen₃ (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂) (blockSucc RD Λ l h₃)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂) (indBlock Q a RD Λ l h₃) M γ rfl rfl rfl)

/-- The dots of `E_i E_j E_k` on weight spaces and on blocks are compatible, hence so are their
polynomial evaluations. -/
theorem ncEval_dots_mem (i j l : I) {w₀ w₁ w₂ w₃ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX l = w₃) (γ : WeightBlocks RD Λ w₀)
    (p : MvPolynomial (Fin 3) k) :
    (KLR.ncEval (A := End (globalE.{u, v, w} Q a RD Λ i h₁ ≫
        (globalE Q a RD Λ j h₂ ≫ globalE Q a RD Λ l h₃)))
      ![globalE Q a RD Λ i h₁ ◁ (globalE Q a RD Λ j h₂ ◁ globalDot Q a RD Λ l h₃),
        globalE Q a RD Λ i h₁ ◁ (globalDot Q a RD Λ j h₂ ▷ globalE Q a RD Λ l h₃),
        globalDot Q a RD Λ i h₁ ▷ (globalE Q a RD Λ j h₂ ≫ globalE Q a RD Λ l h₃)] p,
      KLR.ncEval (A := End (ind.{u, v, w} Q a i (blockSucc_step RD Λ i h₁ γ) ⋙
          ind Q a j (blockSucc_step RD Λ j h₂ _) ⋙ ind Q a l (blockSucc_step RD Λ l h₃ _)))
        ![Functor.whiskerLeft (ind Q a i (blockSucc_step RD Λ i h₁ γ))
            (Functor.whiskerLeft (ind Q a j (blockSucc_step RD Λ j h₂ _))
              (dot Q a l (blockSucc_step RD Λ l h₃ _))),
          Functor.whiskerLeft (ind Q a i (blockSucc_step RD Λ i h₁ γ))
            (Functor.whiskerRight (dot Q a j (blockSucc_step RD Λ j h₂ _))
              (ind Q a l (blockSucc_step RD Λ l h₃ _))),
          Functor.whiskerRight (dot Q a i (blockSucc_step RD Λ i h₁ γ))
            (ind Q a j (blockSucc_step RD Λ j h₂ _) ⋙ ind Q a l (blockSucc_step RD Λ l h₃ _))]
        p) ∈ tripleCompat Q a RD Λ i j l h₁ h₂ h₃ γ := by
  intro M
  refine ncEval_compat (globalE.{u, v, w} Q a RD Λ i h₁ ≫
      (globalE Q a RD Λ j h₂ ≫ globalE Q a RD Λ l h₃))
    (ind.{u, v, w} Q a i (blockSucc_step RD Λ i h₁ γ) ⋙
      ind Q a j (blockSucc_step RD Λ j h₂ _) ⋙ ind Q a l (blockSucc_step RD Λ l h₃ _))
    (fun M => M γ)
    (Pi.eval _ (blockSucc RD Λ l h₃ (blockSucc RD Λ j h₂ (blockSucc RD Λ i h₁ γ))))
    (fun M => gen₃ (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂) (blockSucc RD Λ l h₃)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂) (indBlock Q a RD Λ l h₃) M γ rfl rfl rfl)
    _ _ ?_ p M
  intro c M'
  fin_cases c
  · have d := gen₃_whiskerLeft (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂)
      (blockSucc RD Λ l h₃) (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂)
      (indBlock Q a RD Λ l h₃) (s₂' := blockSucc RD Λ j h₂) (s₃' := blockSucc RD Λ l h₃)
      (L₂' := indBlock Q a RD Λ j h₂) (L₃' := indBlock Q a RD Λ l h₃)
      (globalE Q a RD Λ j h₂ ◁ globalDot Q a RD Λ l h₃).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_whiskerLeft_globalDot Q a RD Λ l j h₂ h₃ _ _ rfl rfl)
    exact d
  · have d := gen₃_whiskerLeft (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂)
      (blockSucc RD Λ l h₃) (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂)
      (indBlock Q a RD Λ l h₃) (s₂' := blockSucc RD Λ j h₂) (s₃' := blockSucc RD Λ l h₃)
      (L₂' := indBlock Q a RD Λ j h₂) (L₃' := indBlock Q a RD Λ l h₃)
      (globalDot Q a RD Λ j h₂ ▷ globalE Q a RD Λ l h₃).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_globalDot_whiskerRight Q a RD Λ l j h₂ h₃ _ _ rfl rfl)
    exact d
  · have d := gen₃_whiskerRight (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂)
      (blockSucc RD Λ l h₃) (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂)
      (indBlock Q a RD Λ l h₃) (s₁' := blockSucc RD Λ i h₁) (s₂' := blockSucc RD Λ j h₂)
      (L₁' := indBlock Q a RD Λ i h₁) (L₂' := indBlock Q a RD Λ j h₂)
      (globalDot Q a RD Λ i h₁ ▷ globalE Q a RD Λ j h₂).hom M' γ rfl rfl rfl rfl rfl _
      (gen₂_globalDot_whiskerRight Q a RD Λ j i h₁ h₂ M' γ rfl rfl)
    exact d

/-- The first composite of the braid relation with outer labels `i, i` on weight spaces is
compatible with its blockwise counterpart. -/
theorem braidLeft_mem (i j : I) {w₀ w₁ w₂ w₃ w₅ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅) (h₄ : w₁ + RD.iX i = w₃)
    (h₅ : w₃ + RD.iX j = w₅) (γ : WeightBlocks RD Λ w₀) :
    (globalE.{u, v, w} Q a RD Λ i h₁ ◁ globalCross Q a RD Λ i j h₂ h₃ h₄ h₅ ≫
        ((α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₄) (globalE Q a RD Λ j h₅)).inv ≫
          globalCross Q a RD Λ i i h₁ h₄ h₁ h₄ ▷ globalE Q a RD Λ j h₅ ≫
          (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₄) (globalE Q a RD Λ j h₅)).hom) ≫
        globalE Q a RD Λ i h₁ ◁ globalCross Q a RD Λ j i h₄ h₅ h₂ h₃,
      braidLeft Q a i j (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ j h₂ _)
        (blockSucc_step RD Λ i h₃ _) (blockSucc_step RD Λ i h₄ _)
        (blockSucc_eq RD Λ j (blockSucc_comm RD Λ j i h₄ h₅ h₂ h₃ (blockSucc RD Λ i h₁ γ)))) ∈
      tripleCompat Q a RD Λ i j i h₁ h₂ h₃ γ := by
  intro M
  have q1 := blockSucc_comm RD Λ j i h₄ h₅ h₂ h₃ (blockSucc RD Λ i h₁ γ)
  have u1 := gen₃_whiskerLeft (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂) (blockSucc RD Λ i h₃)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂) (indBlock Q a RD Λ i h₃)
      (s₂' := blockSucc RD Λ i h₄) (s₃' := blockSucc RD Λ j h₅) (L₂' := indBlock Q a RD Λ i h₄)
      (L₃' := indBlock Q a RD Λ j h₅) (globalCross Q a RD Λ i j h₂ h₃ h₄ h₅).hom M γ
      rfl rfl rfl rfl q1 _ (gen₂_globalCross Q a RD Λ i j h₂ h₃ h₄ h₅ _ _ rfl rfl rfl q1)
  have u3 := gen₃_whiskerRight (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₄) (blockSucc RD Λ j h₅)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ i h₄) (indBlock Q a RD Λ j h₅)
      (s₁' := blockSucc RD Λ i h₁) (s₂' := blockSucc RD Λ i h₄) (L₁' := indBlock Q a RD Λ i h₁)
      (L₂' := indBlock Q a RD Λ i h₄) (globalCross Q a RD Λ i i h₁ h₄ h₁ h₄).hom M γ
      rfl rfl rfl rfl q1 _ (gen₂_globalCross Q a RD Λ i i h₁ h₄ h₁ h₄ M γ rfl rfl rfl rfl)
  have u5 := gen₃_whiskerLeft (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₄) (blockSucc RD Λ j h₅)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ i h₄) (indBlock Q a RD Λ j h₅)
      (s₂' := blockSucc RD Λ j h₂) (s₃' := blockSucc RD Λ i h₃) (L₂' := indBlock Q a RD Λ j h₂)
      (L₃' := indBlock Q a RD Λ i h₃) (globalCross Q a RD Λ j i h₄ h₅ h₂ h₃).hom M γ
      rfl rfl q1 rfl rfl _ (gen₂_globalCross Q a RD Λ j i h₄ h₅ h₂ h₃ _ _ rfl q1 rfl rfl)
  exact gen_chain_left u1 (gen_assoc _) u3 (gen_assoc _) u5

/-- The second composite of the braid relation with outer labels `i, i` on weight spaces is
compatible with its blockwise counterpart. -/
theorem braidRight_mem (i j : I) {w₀ w₁ w₂ w₄ w₅ : X} (h₁ : w₀ + RD.iX i = w₁)
    (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅) (h₆ : w₀ + RD.iX j = w₄)
    (h₇ : w₄ + RD.iX i = w₂) (γ : WeightBlocks RD Λ w₀) :
    (((α_ (globalE.{u, v, w} Q a RD Λ i h₁) (globalE Q a RD Λ j h₂)
          (globalE Q a RD Λ i h₃)).inv ≫
        globalCross Q a RD Λ j i h₁ h₂ h₆ h₇ ▷ globalE Q a RD Λ i h₃ ≫
        (α_ (globalE Q a RD Λ j h₆) (globalE Q a RD Λ i h₇) (globalE Q a RD Λ i h₃)).hom) ≫
        globalE Q a RD Λ j h₆ ◁ globalCross Q a RD Λ i i h₇ h₃ h₇ h₃ ≫
        ((α_ (globalE Q a RD Λ j h₆) (globalE Q a RD Λ i h₇) (globalE Q a RD Λ i h₃)).inv ≫
          globalCross Q a RD Λ i j h₆ h₇ h₁ h₂ ▷ globalE Q a RD Λ i h₃ ≫
          (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ j h₂) (globalE Q a RD Λ i h₃)).hom),
      braidRight Q a i j (blockSucc_step RD Λ i h₁ γ) (blockSucc_step RD Λ j h₂ _)
        (blockSucc_step RD Λ i h₃ _) (blockSucc_step RD Λ j h₆ γ)
        (blockSucc_eq RD Λ i (blockSucc_comm RD Λ i j h₆ h₇ h₁ h₂ γ))) ∈
      tripleCompat Q a RD Λ i j i h₁ h₂ h₃ γ := by
  intro M
  have q2 := blockSucc_comm RD Λ i j h₆ h₇ h₁ h₂ γ
  have v2 := gen₃_whiskerRight (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂) (blockSucc RD Λ i h₃)
      (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂) (indBlock Q a RD Λ i h₃)
      (s₁' := blockSucc RD Λ j h₆) (s₂' := blockSucc RD Λ i h₇) (L₁' := indBlock Q a RD Λ j h₆)
      (L₂' := indBlock Q a RD Λ i h₇) (globalCross Q a RD Λ j i h₁ h₂ h₆ h₇).hom M γ
      rfl rfl rfl q2 rfl _ (gen₂_globalCross Q a RD Λ j i h₁ h₂ h₆ h₇ M γ rfl rfl rfl q2)
  have v4 := gen₃_whiskerLeft (blockSucc RD Λ j h₆) (blockSucc RD Λ i h₇) (blockSucc RD Λ i h₃)
      (indBlock Q a RD Λ j h₆) (indBlock Q a RD Λ i h₇) (indBlock Q a RD Λ i h₃)
      (s₂' := blockSucc RD Λ i h₇) (s₃' := blockSucc RD Λ i h₃) (L₂' := indBlock Q a RD Λ i h₇)
      (L₃' := indBlock Q a RD Λ i h₃) (globalCross Q a RD Λ i i h₇ h₃ h₇ h₃).hom M γ
      rfl q2 rfl q2 rfl _ (gen₂_globalCross Q a RD Λ i i h₇ h₃ h₇ h₃ _ _ q2 rfl q2 rfl)
  have v6 := gen₃_whiskerRight (blockSucc RD Λ j h₆) (blockSucc RD Λ i h₇) (blockSucc RD Λ i h₃)
      (indBlock Q a RD Λ j h₆) (indBlock Q a RD Λ i h₇) (indBlock Q a RD Λ i h₃)
      (s₁' := blockSucc RD Λ i h₁) (s₂' := blockSucc RD Λ j h₂) (L₁' := indBlock Q a RD Λ i h₁)
      (L₂' := indBlock Q a RD Λ j h₂) (globalCross Q a RD Λ i j h₆ h₇ h₁ h₂).hom M γ
      rfl q2 rfl rfl rfl _ (gen₂_globalCross Q a RD Λ i j h₆ h₇ h₁ h₂ M γ rfl q2 rfl rfl)
  exact gen_chain_right (gen_assoc _) v2 (gen_assoc _) v4 (gen_assoc _) v6 (gen_assoc _)

/-- **The braid relation with equal outer labels on weight spaces** (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.4) for outer labels `i, i` and middle label `j ≠ i`, the shape of
`TwoRep.RouqUpKLR.braidQ`): the difference of the two composites of crossings on
`E_i E_j E_i` is `Q̄_ij` evaluated at the three dots. -/
theorem globalCross_braidQ (i j : I) (hij : i ≠ j) {w₀ w₁ w₂ w₃ w₄ w₅ : X}
    (h₁ : w₀ + RD.iX i = w₁) (h₂ : w₁ + RD.iX j = w₂) (h₃ : w₂ + RD.iX i = w₅)
    (h₄ : w₁ + RD.iX i = w₃) (h₅ : w₃ + RD.iX j = w₅)
    (h₆ : w₀ + RD.iX j = w₄) (h₇ : w₄ + RD.iX i = w₂) :
    (globalE.{u, v, w} Q a RD Λ i h₁ ◁ globalCross Q a RD Λ i j h₂ h₃ h₄ h₅ ≫
      ((α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₄) (globalE Q a RD Λ j h₅)).inv ≫
        globalCross Q a RD Λ i i h₁ h₄ h₁ h₄ ▷ globalE Q a RD Λ j h₅ ≫
        (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ i h₄) (globalE Q a RD Λ j h₅)).hom) ≫
      globalE Q a RD Λ i h₁ ◁ globalCross Q a RD Λ j i h₄ h₅ h₂ h₃) -
    (((α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ j h₂) (globalE Q a RD Λ i h₃)).inv ≫
      globalCross Q a RD Λ j i h₁ h₂ h₆ h₇ ▷ globalE Q a RD Λ i h₃ ≫
      (α_ (globalE Q a RD Λ j h₆) (globalE Q a RD Λ i h₇) (globalE Q a RD Λ i h₃)).hom) ≫
      globalE Q a RD Λ j h₆ ◁ globalCross Q a RD Λ i i h₇ h₃ h₇ h₃ ≫
      ((α_ (globalE Q a RD Λ j h₆) (globalE Q a RD Λ i h₇) (globalE Q a RD Λ i h₃)).inv ≫
        globalCross Q a RD Λ i j h₆ h₇ h₁ h₂ ▷ globalE Q a RD Λ i h₃ ≫
        (α_ (globalE Q a RD Λ i h₁) (globalE Q a RD Λ j h₂) (globalE Q a RD Λ i h₃)).hom)) =
      KLR.ncEval (A := End (globalE.{u, v, w} Q a RD Λ i h₁ ≫
          (globalE Q a RD Λ j h₂ ≫ globalE Q a RD Λ i h₃)))
        ![globalE Q a RD Λ i h₁ ◁ (globalE Q a RD Λ j h₂ ◁ globalDot Q a RD Λ i h₃),
          globalE Q a RD Λ i h₁ ◁ (globalDot Q a RD Λ j h₂ ▷ globalE Q a RD Λ i h₃),
          globalDot Q a RD Λ i h₁ ▷ (globalE Q a RD Λ j h₂ ≫ globalE Q a RD Λ i h₃)]
        (KLR.qbar (Q i j)) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₃_ext (blockSucc RD Λ i h₁) (blockSucc RD Λ j h₂) (blockSucc RD Λ i h₃)
    (indBlock Q a RD Λ i h₁) (indBlock Q a RD Λ j h₂) (indBlock Q a RD Λ i h₃)
    fun γ β δ μ hβ hδ hμ => ?_
  subst hβ hδ hμ
  have hS := Subalgebra.sub_mem _ (braidLeft_mem Q a RD Λ i j h₁ h₂ h₃ h₄ h₅ γ)
    (braidRight_mem Q a RD Λ i j h₁ h₂ h₃ h₆ h₇ γ)
  rw [Prod.mk_sub_mk, braidLeft_sub_braidRight Q a i j hij] at hS
  exact (hS M).trans (ncEval_dots_mem Q a RD Λ i j i h₁ h₂ h₃ γ (KLR.qbar (Q i j)) M).symm

end

end Categorification.KLR.CyclotomicAction
