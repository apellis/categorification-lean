/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Global
import Categorification.KLR.CyclotomicAction.Slides
import Categorification.TwoRep.BlockSumGen

/-!
# The crossings of the weight-indexed cyclotomic Rouquier family

On blocks, the crossing `F_j F_i ⟶ F_i F_j` of cyclotomic induction functors is `ψ` for distinct
colours (`cross`) and `-ψ` for equal colours (`sameCross`); `signedCross` packages both. For
weights `x + j_X = y`, `y + i_X = t`, `x + i_X = z`, `z + j_X = t`, `globalCross i j` is the
transformation `globalE j ≫ globalE i ⟶ globalE i ≫ globalE j` of functors between weight spaces
that is `signedCross` on each block (`gen₂_globalCross`). These are the crossings of the
cyclotomic Rouquier family of KL III Thm. 1.2 (Kang–Kashiwara, arXiv:1102.4677v4, §4.2).

Relations (KL I §2.1; Brundan, arXiv:1501.00350v1, (1.2), (1.3)), in the shapes of
`TwoRep.RouqUpKLR` and `TwoRep.RouqFamily`:

* `globalCross_square`: for `i ≠ j`, `globalCross i j ≫ globalCross j i = Q_ij(dots)`, assuming
  `KLRSymm Q` as in Kang–Kashiwara §3;
* `globalCross_slide_left`, `globalCross_slide_right`: dot slides for `i ≠ j`;
* `globalCross_sq`: the square of the same-colour crossing is zero.

Each is checked on the generators of a composite of block sums, where it is the corresponding
relation for cyclotomic induction functors; polynomial evaluations in the dots pass to blocks by
`TwoRep.ncEval_compat`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

/-- The crossing of cyclotomic induction functors on blocks: `ψ` for distinct colours and
`-ψ` (`sameCross`) for equal colours. -/
def signedCross (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ)
    (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    ind.{u, v, w} Q a j h₁ ⋙ ind Q a i h₂ ⟶ ind Q a i h₃ ⋙ ind Q a j h₄ :=
  if i = j then -cross Q a i j h₁ h₂ h₃ h₄ else cross Q a i j h₁ h₂ h₃ h₄

theorem signedCross_of_ne {i j : I} (hij : i ≠ j) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    signedCross.{u, v, w} Q a i j h₁ h₂ h₃ h₄ = cross Q a i j h₁ h₂ h₃ h₄ := by
  simp [signedCross, hij]

theorem signedCross_self (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ) :
    signedCross.{u, v, w} Q a i i h₁ h₂ h₁ h₂ = sameCross Q a i h₁ h₂ := by
  simp [signedCross, sameCross]

/-- Two successive transformations on a generator. -/
theorem gen_comp_comp {𝒟 : Type*} [Category 𝒟] {P P' P'' G G' G'' : 𝒟} {g : P ⟶ G}
    {g' : P' ⟶ G'} {g'' : P'' ⟶ G''} {f₁ : G ⟶ G'} {f₂ : G' ⟶ G''} {a₁ : P ⟶ P'}
    {a₂ : P' ⟶ P''} (h₁ : g ≫ f₁ = a₁ ≫ g') (h₂ : g' ≫ f₂ = a₂ ≫ g'') :
    g ≫ f₁ ≫ f₂ = (a₁ ≫ a₂) ≫ g'' := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)

omit [DecidableEq I] in
theorem blockSucc_comm (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t)
    (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t) (γ : WeightBlocks RD Λ x) :
    blockSucc RD Λ i h₂ (blockSucc RD Λ j h₁ γ) = blockSucc RD Λ j h₄ (blockSucc RD Λ i h₃ γ) :=
  Subtype.ext (add_left_comm _ _ _)

/-- **The crossing on weight spaces** `globalE j ≫ globalE i ⟶ globalE i ≫ globalE j`. -/
def globalCross (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t)
    (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t) :
    globalE.{u, v, w} Q a RD Λ j h₁ ≫ globalE Q a RD Λ i h₂ ⟶
      globalE Q a RD Λ i h₃ ≫ globalE Q a RD Λ j h₄ :=
  ObjectProperty.homMk (blockCross (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂)
    (indBlock Q a RD Λ j h₁) (indBlock Q a RD Λ i h₂) (blockSucc RD Λ i h₃)
    (blockSucc RD Λ j h₄) (indBlock Q a RD Λ i h₃) (indBlock Q a RD Λ j h₄)
    (blockSucc_comm RD Λ i j h₁ h₂ h₃ h₄) fun _ _ _ _ hb hd hb' hd' =>
      signedCross Q a i j (blockSucc_eq RD Λ j hb) (blockSucc_eq RD Λ i hd)
        (blockSucc_eq RD Λ i hb') (blockSucc_eq RD Λ j hd'))

/-- `globalCross` on the generators of `globalE j ≫ globalE i`, for any intermediate blocks. -/
theorem gen₂_globalCross (i j : I) {x y z t : X} (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t)
    (h₃ : x + RD.iX i = z) (h₄ : z + RD.iX j = t) (M : ∀ γ : WeightBlocks RD Λ x,
      ModuleCat.{max (max u v) w} (CycKLR k Q a γ.1)) (γ : WeightBlocks RD Λ x)
    {β : WeightBlocks RD Λ y} {β' : WeightBlocks RD Λ z} {δ : WeightBlocks RD Λ t}
    (hb : blockSucc RD Λ j h₁ γ = β) (hd : blockSucc RD Λ i h₂ β = δ)
    (hb' : blockSucc RD Λ i h₃ γ = β') (hd' : blockSucc RD Λ j h₄ β' = δ) :
    gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
        (indBlock Q a RD Λ i h₂) M γ hb hd ≫
        (globalCross.{u, v, w} Q a RD Λ i j h₁ h₂ h₃ h₄).hom.app M δ =
      (signedCross Q a i j (blockSucc_eq RD Λ j hb) (blockSucc_eq RD Λ i hd)
          (blockSucc_eq RD Λ i hb') (blockSucc_eq RD Λ j hd')).app (M γ) ≫
        gen₂ (blockSucc RD Λ i h₃) (blockSucc RD Λ j h₄) (indBlock Q a RD Λ i h₃)
          (indBlock Q a RD Λ j h₄) M γ hb' hd' :=
  gen₂_blockCross _ _ _ _ _ _ _ _ _ _ M γ hb hd hb' hd'

/-- `globalE j ◁ globalDot i` on generators. -/
theorem gen₂_whiskerLeft_globalDot (i j : I) {x y t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t) (M : ∀ γ : WeightBlocks RD Λ x,
      ModuleCat.{max (max u v) w} (CycKLR k Q a γ.1)) (γ : WeightBlocks RD Λ x)
    {β : WeightBlocks RD Λ y} {δ : WeightBlocks RD Λ t}
    (hb : blockSucc RD Λ j h₁ γ = β) (hd : blockSucc RD Λ i h₂ β = δ) :
    gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
        (indBlock Q a RD Λ i h₂) M γ hb hd ≫
        (globalE.{u, v, w} Q a RD Λ j h₁ ◁ globalDot Q a RD Λ i h₂).hom.app M δ =
      (Functor.whiskerLeft (ind Q a j (blockSucc_eq RD Λ j hb))
          (dot Q a i (blockSucc_eq RD Λ i hd))).app (M γ) ≫
        gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
          (indBlock Q a RD Λ i h₂) M γ hb hd :=
  gen₂_whiskerLeft (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
    (fun _ _ hβ => dot Q a i (blockSucc_eq RD Λ i hβ)) M γ hb hd

/-- `globalDot j ▷ globalE i` on generators. -/
theorem gen₂_globalDot_whiskerRight (i j : I) {x y t : X} (h₁ : x + RD.iX j = y)
    (h₂ : y + RD.iX i = t) (M : ∀ γ : WeightBlocks RD Λ x,
      ModuleCat.{max (max u v) w} (CycKLR k Q a γ.1)) (γ : WeightBlocks RD Λ x)
    {β : WeightBlocks RD Λ y} {δ : WeightBlocks RD Λ t}
    (hb : blockSucc RD Λ j h₁ γ = β) (hd : blockSucc RD Λ i h₂ β = δ) :
    gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
        (indBlock Q a RD Λ i h₂) M γ hb hd ≫
        (globalDot.{u, v, w} Q a RD Λ j h₁ ▷ globalE Q a RD Λ i h₂).hom.app M δ =
      (Functor.whiskerRight (dot Q a j (blockSucc_eq RD Λ j hb))
          (ind Q a i (blockSucc_eq RD Λ i hd))).app (M γ) ≫
        gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
          (indBlock Q a RD Λ i h₂) M γ hb hd :=
  gen₂_whiskerRight (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₂)
    (fun _ _ hβ => dot Q a j (blockSucc_eq RD Λ j hβ)) M γ hb hd

/-- **The quadratic KLR relation for distinct colours on weight spaces** (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.3), the shape of `TwoRep.RouqUpKLR.square`). Hypothesis: `KLRSymm Q`. -/
theorem globalCross_square (hQ : KLRSymm Q) (i j : I) (hij : i ≠ j) {x y z t : X}
    (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    globalCross.{u, v, w} Q a RD Λ i j h₁ h₂ h₃ h₄ ≫ globalCross Q a RD Λ j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (globalE.{u, v, w} Q a RD Λ j h₁ ≫ globalE Q a RD Λ i h₂))
        ![globalE Q a RD Λ j h₁ ◁ globalDot Q a RD Λ i h₂,
          globalDot Q a RD Λ j h₁ ▷ globalE Q a RD Λ i h₂] (Q i j) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
    (indBlock Q a RD Λ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ j h₄ (blockSucc RD Λ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  have hR := ncEval_compat (globalE.{u, v, w} Q a RD Λ j h₁ ≫ globalE Q a RD Λ i h₂)
    (ind Q a j (blockSucc_eq RD Λ j hb) ⋙ ind Q a i (blockSucc_eq RD Λ i hd)) (fun M => M γ)
    (Pi.eval _ δ) (fun M => gen₂ (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂)
      (indBlock Q a RD Λ j h₁) (indBlock Q a RD Λ i h₂) M γ hb hd)
    ![globalE Q a RD Λ j h₁ ◁ globalDot Q a RD Λ i h₂,
      globalDot Q a RD Λ j h₁ ▷ globalE Q a RD Λ i h₂]
    ![Functor.whiskerLeft (ind Q a j (blockSucc_eq RD Λ j hb))
        (dot Q a i (blockSucc_eq RD Λ i hd)),
      Functor.whiskerRight (dot Q a j (blockSucc_eq RD Λ j hb))
        (ind Q a i (blockSucc_eq RD Λ i hd))]
    (fun c M => by
      fin_cases c
      · exact gen₂_whiskerLeft_globalDot Q a RD Λ i j h₁ h₂ M γ hb hd
      · exact gen₂_globalDot_whiskerRight Q a RD Λ i j h₁ h₂ M γ hb hd) (Q i j) M
  refine Eq.trans ?_ hR.symm
  rw [← square Q a hQ i j hij (blockSucc_eq RD Λ j hb) (blockSucc_eq RD Λ i hd)
    (blockSucc_eq RD Λ i (rfl : blockSucc RD Λ i h₃ γ = _)) (blockSucc_eq RD Λ j e₁)]
  change gen₂ _ _ _ _ M γ hb hd ≫ ((globalCross Q a RD Λ i j h₁ h₂ h₃ h₄).hom.app M δ ≫
    (globalCross Q a RD Λ j i h₃ h₄ h₁ h₂).hom.app M δ) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (gen₂_globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (gen₂_globalCross Q a RD Λ j i h₃ h₄ h₁ h₂ M γ rfl e₁ hb hd)).trans ?_
  rw [signedCross_of_ne Q a hij, signedCross_of_ne Q a (Ne.symm hij)]
  exact (Category.assoc _ _ _).symm

/-- **Dot slides for distinct colours on weight spaces** (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.2), the shape of `TwoRep.RouqUpKLR.slide_left`). -/
theorem globalCross_slide_left (i j : I) (hij : i ≠ j) {x y z t : X}
    (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    globalE.{u, v, w} Q a RD Λ j h₁ ◁ globalDot Q a RD Λ i h₂ ≫
        globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ =
      globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ ≫ globalDot Q a RD Λ i h₃ ▷ globalE Q a RD Λ j h₄ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
    (indBlock Q a RD Λ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ j h₄ (blockSucc RD Λ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  refine (gen_comp_comp (gen₂_whiskerLeft_globalDot Q a RD Λ i j h₁ h₂ M γ hb hd)
    (gen₂_globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans
    (Eq.trans ?_ (gen_comp_comp (gen₂_globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)
      (gen₂_globalDot_whiskerRight Q a RD Λ j i h₃ h₄ M γ rfl e₁)).symm)
  rw [signedCross_of_ne Q a hij, ← NatTrans.comp_app, ← NatTrans.comp_app,
    slide_left Q a i j hij]

/-- **Dot slides for distinct colours on weight spaces** (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.2), the shape of `TwoRep.RouqUpKLR.slide_right`). -/
theorem globalCross_slide_right (i j : I) (hij : i ≠ j) {x y z t : X}
    (h₁ : x + RD.iX j = y) (h₂ : y + RD.iX i = t) (h₃ : x + RD.iX i = z)
    (h₄ : z + RD.iX j = t) :
    globalDot.{u, v, w} Q a RD Λ j h₁ ▷ globalE Q a RD Λ i h₂ ≫
        globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ =
      globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ ≫ globalE Q a RD Λ i h₃ ◁ globalDot Q a RD Λ j h₄ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ j h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ j h₁)
    (indBlock Q a RD Λ i h₂) fun γ β δ hb hd => ?_
  have e₁ : blockSucc RD Λ j h₄ (blockSucc RD Λ i h₃ γ) = δ :=
    (blockSucc_comm RD Λ i j h₁ h₂ h₃ h₄ γ).symm.trans (by rw [hb, hd])
  refine (gen_comp_comp (gen₂_globalDot_whiskerRight Q a RD Λ i j h₁ h₂ M γ hb hd)
    (gen₂_globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)).trans
    (Eq.trans ?_ (gen_comp_comp (gen₂_globalCross Q a RD Λ i j h₁ h₂ h₃ h₄ M γ hb hd rfl e₁)
      (gen₂_whiskerLeft_globalDot Q a RD Λ j i h₃ h₄ M γ rfl e₁)).symm)
  rw [signedCross_of_ne Q a hij, ← NatTrans.comp_app, ← NatTrans.comp_app,
    slide_right Q a i j hij]

/-- **The nil-Hecke quadratic relation on weight spaces** (Brundan, arXiv:1501.00350v1, (1.3)
for equal labels, the shape of `TwoRep.RouqFamily.square`). -/
theorem globalCross_sq (i : I) {x y t : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = t) :
    globalCross.{u, v, w} Q a RD Λ i i h₁ h₂ h₁ h₂ ≫ globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ = 0 := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun M => ?_)
  refine gen₂_ext (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₁)
    (indBlock Q a RD Λ i h₂) fun γ β δ hb hd => ?_
  refine (gen_comp_comp (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ hb hd hb hd)
    (gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂ M γ hb hd hb hd)).trans ?_
  rw [signedCross_self, ← NatTrans.comp_app, sameCross_sq, NatTrans.app_zero]
  exact Limits.zero_comp.trans Limits.comp_zero.symm

end

end Categorification.KLR.CyclotomicAction
