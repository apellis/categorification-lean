/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqKaroubiQ
import Categorification.TwoRep.CatPowComp

/-!
# The dot and crossing 2-morphisms of the completed black action, componentwise

Brundan, arXiv:1501.00350v1, (1.6), for the black action of Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) on the additive idempotent
completions of the violating quotients (Webster, arXiv:1309.3796v3, §4.5–4.6).

* `ofTrQ`: a diagram between the boundary words of two 1-morphisms, as a 2-morphism, with
  `homTrQ (ofTrQ D) = D`. This gives the dot `dnDotCellQ` on a downward strand and the
  crossing `dnCrossCellQ` of two downward strands, the inputs `x` and `τ` of
  `blackCompletedSigmaSumInvToQ`.
* `toNatTrans_blackCompletedCrossQ`: the image of the crossing, framed by `map_comp`, is the
  completion of `crossNatQ`.
* `toNatTrans_blackCompletedDotQ`: the image of the dot is the completion of the black-action
  dot.
* `blackCompletedSigma_app`: the rightward crossing of the image adjunctions at an object is
  `η₂ ≫ E₂ (τ) ≫ E₂ (F₂ ε₁)` with `τ` the completed `crossNatQ`, the form of the hypothesis
  of `MatEnd.sigma_generator`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep
  Idempotents

universe u v w

section Cells

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}

/-- A diagram between the boundary words of two 1-morphisms of the Khovanov–Lauda bicategory,
as a 2-morphism. -/
def ofTrQ {l m : (CLQ.pres RD k sc).Bicat} {f g : l ⟶ m}
    (D : (CLQ.pres RD k sc).obj (ob RD m.region (homLettersQ f)) ⟶
      (CLQ.pres RD k sc).obj (ob RD m.region (homLettersQ g))) : f ⟶ g :=
  Presentation.Bicat.homOf (eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ f)) ≫ D ≫
    eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ g)).symm)

theorem homTrQ_ofTrQ {l m : (CLQ.pres RD k sc).Bicat} {f g : l ⟶ m}
    (D : (CLQ.pres RD k sc).obj (ob RD m.region (homLettersQ f)) ⟶
      (CLQ.pres RD k sc).obj (ob RD m.region (homLettersQ g))) :
    homTrQ (ofTrQ D) = D := by
  simp only [homTrQ, ofTrQ, Presentation.Bicat.homOf]
  simp

variable (k sc) (i : I)

/-- The dot on a downward strand `F_i`, as a 2-morphism of the 1-cell dual. -/
def dnDotCellQ {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    downStrandRevQ k sc i h ⟶ downStrandRevQ k sc i h :=
  ofTrQ (f := downStrandHomQ (k := k) (sc := sc) i h) (dnDotQ (sc := sc) i μ)

theorem homTrQ_dnDotCellQ {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    homTrQ (dnDotCellQ k sc i h) = dnDotQ (sc := sc) i μ :=
  homTrQ_ofTrQ _

/-- The crossing of two downward strands `F_i`, as a 2-morphism of the 1-cell dual. -/
def dnCrossCellQ {μ ν ν₂ : X} (h₁ : wt RD μ [(false, i)] = ν) (h₂ : wt RD ν [(false, i)] = ν₂) :
    downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ ⟶
      downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ :=
  ofTrQ (f := downStrandHomQ (k := k) (sc := sc) i h₂ ≫ downStrandHomQ (k := k) (sc := sc) i h₁)
    (dnCrossQ (sc := sc) i μ)

theorem homTrQ_dnCrossCellQ {μ ν ν₂ : X} (h₁ : wt RD μ [(false, i)] = ν)
    (h₂ : wt RD ν [(false, i)] = ν₂) :
    homTrQ (dnCrossCellQ k sc i h₁ h₂) = dnCrossQ (sc := sc) i μ :=
  homTrQ_ofTrQ _

end Cells

section Action

/-- Minus a composite `a ≫ R.map t ≫ c` is `a ≫ R.map t' ≫ c` when `t' = -t` and `R` is
additive. -/
theorem neg_comp_map_comp {A B : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
    (R : A ⥤ B) [hR : R.Additive] {W : B} {Y₁ Y₂ : A} {V : B} (a : W ⟶ R.obj Y₁)
    (c : R.obj Y₂ ⟶ V) (t : Y₁ ⟶ Y₂) {t₀ t' : Y₁ ⟶ Y₂} (h₀ : t₀ = t) (ht : t' = -t₀) :
    -(a ≫ R.map t ≫ c) = a ≫ R.map t' ≫ c := by
  rw [ht, h₀, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)
  (i : I)

/-- **The image of the dot is the completed black-action dot.** -/
theorem toNatTrans_blackCompletedDotQ {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    ((blackActionCompletedQ sc P hP).map₂ (dnDotCellQ k sc i h)).toNatTrans =
      completionMap₂ (blackMapQ P hP h h (dnDotQ (sc := sc) i μ)) :=
  congrArg (fun t => completionMap₂ (blackMapQ P hP h h t)) (homTrQ_dnDotCellQ k sc i h)

/-- **The image of the crossing is the completed black-action crossing**: framed by `map_comp`,
the image of `dnCrossCellQ` is the completion of `crossNatQ`. -/
theorem toNatTrans_blackCompletedCrossQ (ν : Multiset I) :
    (eqToHom ((blackActionCompletedQ sc P hP).map_comp
        (downStrandRevQ k sc i (wt_downRightWeight (Λ := Λ) i ν))
        (downStrandRevQ k sc i (wt_downRightWeight (Λ := Λ) i ({i} + ν)))).symm ≫
      (blackActionCompletedQ sc P hP).map₂ (dnCrossCellQ k sc i _ _) ≫
      eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _)).toNatTrans =
    completionMap₂ (crossNatQ P hP i ν) := by
  rw [Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.Hom₂.eqToHom_toNatTrans]
  change eqToHom _ ≫ completionMap₂ (blackMapQ P hP (homWtQ _) (homWtQ _)
    (homTrQ (dnCrossCellQ k sc i (wt_downRightWeight (Λ := Λ) i ν)
      (wt_downRightWeight (Λ := Λ) i ({i} + ν))))) ≫ eqToHom _ = _
  rw [homTrQ_dnCrossCellQ, crossNatQ, completionMap₂_comp, completionMap₂_comp,
    completionMap₂_eqToHom, completionMap₂_eqToHom]

variable {μ ν ν₂ : X} (h₁ : wt RD μ [(false, i)] = ν) (h₁' : wt RD ν [(true, i)] = μ)
  (h₂ : wt RD ν [(false, i)] = ν₂) (h₂' : wt RD ν₂ [(true, i)] = ν)

/-- The completion of `-τ₀` at an object is minus the image of `τ`, when the image of `τ` framed
by `map_comp` is the completion of `τ₀`. -/
theorem completionMap₂_neg_app_of (τ : downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ ⟶
      downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂)
    (τ₀ : blackAct P [(false, i)] h₁ ⋙ blackAct P [(false, i)] h₂ ⟶
      blackAct P [(false, i)] h₁ ⋙ blackAct P [(false, i)] h₂)
    (hτ₀ : (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _)).toNatTrans = completionMap₂ τ₀)
    (W : Karoubi (Mat_ (ViolatingCategory P μ))) :
    (completionMap₂ (-τ₀)).app W = -(show (completionMap (blackAct P [(false, i)] h₂)).obj
      ((completionMap (blackAct P [(false, i)] h₁)).obj W) ⟶
    (completionMap (blackAct P [(false, i)] h₂)).obj
      ((completionMap (blackAct P [(false, i)] h₁)).obj W) from
  (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _)).toNatTrans.app W) := by
  rw [completionMap₂_neg, NatTrans.app_neg]
  dsimp only
  exact congrArg Neg.neg (congrArg (fun φ => NatTrans.app φ W) hτ₀).symm

/-- **The rightward crossing of the image adjunctions at an object** (Brundan, (1.6)): if the
image of `τ`, framed by `map_comp`, is the completion of `τ₀`, then minus the rightward crossing
built from the image of `E_i ⊣ F_i` and of `τ` is, at `Z`, `η₂ ≫ E₂ (τ₀') ≫ E₂ (F₂ ε₁)` with
`τ₀'` the completion of `-τ₀`. -/
theorem blackCompletedSigma_app
    (τ : downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ ⟶
      downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂)
    (τ₀ : blackAct P [(false, i)] h₁ ⋙ blackAct P [(false, i)] h₂ ⟶
      blackAct P [(false, i)] h₁ ⋙ blackAct P [(false, i)] h₂)
    (hτ₀ : (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _)).toNatTrans = completionMap₂ τ₀)
    (Z : Karoubi (Mat_ (ViolatingCategory P ν))) :
    (-(show completionMap (blackAct P [(true, i)] h₁') ⋙
          completionMap (blackAct P [(false, i)] h₁) ⟶
        completionMap (blackAct P [(false, i)] h₂) ⋙ completionMap (blackAct P [(true, i)] h₂')
        from (RightwardCrossing.sigma
      (E₁ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₁))
      (E₂ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₂))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
      (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
      ).toNatTrans)).app Z =
    (blackCompletedAdjunctionQ P hP i h₂ h₂').unit.app
        ((completionMap (blackAct P [(false, i)] h₁)).obj
          ((completionMap (blackAct P [(true, i)] h₁')).obj Z)) ≫
      (completionMap (blackAct P [(true, i)] h₂')).map
        ((completionMap₂ (-τ₀)).app ((completionMap (blackAct P [(true, i)] h₁')).obj Z)) ≫
      (completionMap (blackAct P [(true, i)] h₂')).map
        ((completionMap (blackAct P [(false, i)] h₂)).map
          ((blackCompletedAdjunctionQ P hP i h₁ h₁').counit.app Z)) := by
  rw [NatTrans.app_neg]
  dsimp only
  have e := Cat.sigma_toNatTrans_app
    ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
    (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
      (blackActionCompletedQ sc P hP).map₂ τ ≫
      eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
    ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit Z
  rw [e]
  refine Eq.trans ?_ (neg_comp_map_comp (completionMap (blackAct P [(true, i)] h₂')) _ _ _ rfl
    (completionMap₂_neg_app_of P hP i h₁ h₂ τ τ₀ hτ₀ _))
  rfl

end Action

end Categorification.Stendhal.DoubleDiagram
