/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqCrossingQ
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecompQ
import Categorification.Diagrams.KLR.MatEndModuleSumInv
import Categorification.Diagrams.KLR.MatEndNatEmbSigma

/-!
# Brundan's inversion relations on modules over the all-down matrix ring

Brundan, arXiv:1501.00350v1, (1.8) and (1.9), for Webster's functors `Fᵢ ⊣ Eᵢ` (induction and
restriction along the matrix map of a downward black strand) on all right modules over the
all-down matrix ring (Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31), at the black action of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`).

The explicit inverses of the completed black action (`blackCompletedSigmaSumInvToQ`,
`blackCompletedSigmaSumInvFromQ`) pass to modules through `MatEnd.resIndSumInvTo` and
`MatEnd.resIndSumInvFrom`:

* `blackMatrixSumInvToQ` (`⟨i, λ⟩ ≤ 0`): an explicit inverse of the rightward crossing
  `z ⊗ m ↦ φ(z) c φ(1) ⊗ m` together with the dotted counits `z ⊗ m ↦ z d^m m`;
* `blackMatrixSumInvFromQ` (`0 ≤ ⟨i, λ⟩`): the same with the dotted units `m ↦ φ(1) d^m ⊗ m`.

Here `λ` is the right weight of content `i + ν`, `c` is the diagonal matrix of minus the
black-action crossing of the two new downward strands (`crossNatQ`) and `d` that of the
black-action dot on the new strand.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Idempotents Bicategory QuantumGroup QuantumGroup.UDot
  StringDiagrams   KLR TwoRep CyclotomicAction KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance] HomTensor.bimodule
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

universe w u v

section Generic

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)
  (i : I) {μ ν ν₂ : X} (h₁ : wt RD μ [(false, i)] = ν) (h₁' : wt RD ν [(true, i)] = μ)
  (h₂ : wt RD ν [(false, i)] = ν₂) (h₂' : wt RD ν₂ [(true, i)] = ν)

/-- Minus the rightward crossing of the image of `E_i ⊣ F_i` in the completed black action,
built from the crossing `dnCrossCellQ` of two downward strands (the first component of
`blackCompletedSigmaSumInvToQ`). -/
abbrev blackCompletedNegSigmaQ :
    completionMap (blackAct P [(true, i)] h₁') ⋙ completionMap (blackAct P [(false, i)] h₁) ⟶
      completionMap (blackAct P [(false, i)] h₂) ⋙ completionMap (blackAct P [(true, i)] h₂') :=
  -(show completionMap (blackAct P [(true, i)] h₁') ⋙
        completionMap (blackAct P [(false, i)] h₁) ⟶
      completionMap (blackAct P [(false, i)] h₂) ⋙ completionMap (blackAct P [(true, i)] h₂')
      from (RightwardCrossing.sigma
    (E₁ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₁))
    (E₂ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₂))
    ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
    (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
      (blackActionCompletedQ sc P hP).map₂ (dnCrossCellQ k sc i h₁ h₂) ≫
      eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
    ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
    ).toNatTrans)

variable {ι₀ ι₁ ι₂ : Type u} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] {X₀ : ι₀ → ViolatingCategory P μ}
  {X₁ : ι₁ → ViolatingCategory P ν} {X₂ : ι₂ → ViolatingCategory P ν₂}
  {e₁ : ι₀ → ι₁} {e₂ : ι₁ → ι₂} (he₁ : Function.Injective e₁)
  (hX₁ : ∀ s, (blackAct P [(false, i)] h₁).obj (X₀ s) = X₁ (e₁ s))
  (he₂ : Function.Injective e₂)
  (hX₂ : ∀ s, (blackAct P [(false, i)] h₂).obj (X₁ s) = X₂ (e₂ s))
  (τ₀ : blackAct P [(false, i)] h₁ ⋙ blackAct P [(false, i)] h₂ ⟶
    blackAct P [(false, i)] h₁ ⋙ blackAct P [(false, i)] h₂)
  (hτ₀ : (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
      (blackActionCompletedQ sc P hP).map₂ (dnCrossCellQ k sc i h₁ h₂) ≫
      eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _)).toNatTrans = completionMap₂ τ₀)

include hτ₀ in
/-- The generator condition of `MatEnd.resIndModuleEquiv_sigmaLin` for the completed rightward
crossing, with crossing element the diagonal matrix of `-τ₀`. -/
theorem blackCompletedNegSigmaQ_generator :
    (blackCompletedAdjunctionQ P hP i h₂ h₂').homEquiv _ _
        (KLR.Diagram.MatEnd.karoubiSect _ hX₂) ≫
      (completionMap (blackAct P [(true, i)] h₂')).map
        (KLR.Diagram.MatEnd.karoubiCorner _ he₂ hX₂
        (sigmaElt (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁) (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)
          (op (KLR.Diagram.MatEnd.natEmb _ (KLR.Diagram.MatEnd.compEq _ _ hX₁ hX₂) (-τ₀)))
          (unitGen (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁)))) =
    (KLR.Diagram.MatEnd.karoubiGen _ he₁ hX₁ ≫
        (completionMap (blackAct P [(false, i)] h₁)).map
          ((blackCompletedAdjunctionQ P hP i h₁ h₁').homEquiv _ _
            (KLR.Diagram.MatEnd.karoubiSect _ hX₁))) ≫
      (blackCompletedNegSigmaQ P hP i h₁ h₁' h₂ h₂').app
        ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₁)) :=
  KLR.Diagram.MatEnd.sigma_generator _ _ he₁ hX₁ he₂ hX₂ (-τ₀)
    (blackCompletedAdjunctionQ P hP i h₁ h₁') (blackCompletedAdjunctionQ P hP i h₂ h₂')
    (blackCompletedNegSigmaQ P hP i h₁ h₁' h₂ h₂')
    (blackCompletedSigma_app P hP i h₁ h₁' h₂ h₂' (dnCrossCellQ k sc i h₁ h₂) τ₀ hτ₀ _)

/-- **The dotted cap of the image adjunction** is the whiskered power of the completed
black-action dot followed by the counit of `blackCompletedAdjunctionQ`. -/
theorem blackCompletedDottedCapQ_eq (m : ℕ) :
    (show completionMap (blackAct P [(true, i)] h₁') ⋙
          completionMap (blackAct P [(false, i)] h₁) ⟶ 𝟭 _ from
        ((blackActionCompletedQ sc P hP).map _ ◁
          powComp ((blackActionCompletedQ sc P hP).map₂ (dnDotCellQ k sc i h₁)) m ≫
        ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
        ).toNatTrans) =
      Functor.whiskerLeft (completionMap (blackAct P [(true, i)] h₁'))
        ((show End (completionMap (blackAct P [(false, i)] h₁)) from
          completionMap₂ (blackMapQ P hP h₁ h₁ (dnDotQ (sc := sc) i μ))) ^ m) ≫
        (blackCompletedAdjunctionQ P hP i h₁ h₁').counit := by
  dsimp only
  refine (Cat.dottedCap_toNatTrans _ _ m).trans ?_
  rw [toNatTrans_blackCompletedDotQ]
  rfl

include hτ₀ in
/-- **Brundan (1.8) on modules over the matrix ring, from the completed black action**
(`⟨i, ν⟩ ≤ 0`): the rightward crossing `z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m`, with `c` the diagonal
matrix of `-τ₀`, together with the dotted counits `z ⊗ m ↦ z d^m m`, with `d` the diagonal
matrix of the black-action dot, has an explicit inverse on every module. -/
def blackFamilySumInvToQ (M : ModuleCat.{max u v w} (KLR.Diagram.MatEnd X₁)ᵐᵒᵖ)
    {J : Type*} [Fintype J]
    (π : J → ((completionMap (blackAct P [(true, i)] h₁')).obj
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₁)) ⟶
        (toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₀)))
    (ι' : J → ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₀) ⟶
      (completionMap (blackAct P [(true, i)] h₁')).obj
        ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₁))))
    (hπ : ∑ j, π j ≫ ι' j = 𝟙 _) (hn : ip RD i ν ≤ 0) :
    SumInvTo
      (X := ModuleCat.of _ (Ind (Res (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁) M)
        (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁)))
      (Y := ModuleCat.of _ (Res (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)
        (Ind M (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)))) (Z := M)
      (ModuleCat.ofHom (sigmaLin (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁)
        (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)
        (KLR.Diagram.MatEnd.natEmb_comp_commute _ _ he₁ hX₁ he₂ hX₂ (-τ₀)) M))
      (fun m => ModuleCat.ofHom (counitMap (φ := KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁) M ∘ₗ
        (natMap (KLR.Diagram.MatEnd.intertwines_natEmb _ he₁ hX₁
          (blackMapQ P hP h₁ h₁ (dnDotQ (sc := sc) i μ))) ^ m : Module.End _ _)))
      (-ip RD i ν).toNat :=
  KLR.Diagram.MatEnd.resIndSumInvTo _ _ he₁ hX₁ he₂ hX₂
    (blackCompletedAdjunctionQ P hP i h₂ h₂')
    (KLR.Diagram.MatEnd.natEmb_comp_commute _ _ he₁ hX₁ he₂ hX₂ (-τ₀))
    (blackCompletedAdjunctionQ P hP i h₁ h₁') (blackCompletedNegSigmaQ P hP i h₁ h₁' h₂ h₂')
    (blackCompletedNegSigmaQ_generator P hP i h₁ h₁' h₂ h₂' he₁ hX₁ he₂ hX₂ τ₀ hτ₀)
    (KLR.Diagram.MatEnd.intertwines_natEmb _ he₁ hX₁ _)
    (KLR.Diagram.MatEnd.karoubiCorner_cornerMul_natEmb _ he₁ hX₁ _) M π ι' hπ
    ((blackCompletedSigmaSumInvToQ P hP i h₁ h₁' h₂ h₂' (dnDotCellQ k sc i h₁)
      (homTrQ_dnDotCellQ k sc i h₁) (dnCrossCellQ k sc i h₁ h₂) (homTrQ_dnCrossCellQ k sc i h₁ h₂)
      hn).congr rfl (funext fun m => blackCompletedDottedCapQ_eq P hP i h₁ h₁' m) rfl)

/-- **The dotted cup of the image adjunction** is the unit of `blackCompletedAdjunctionQ`
followed by the whiskered power of the completed black-action dot. -/
theorem blackCompletedDottedCupQ_eq (m : ℕ) :
    (show 𝟭 _ ⟶ completionMap (blackAct P [(false, i)] h₂) ⋙
          completionMap (blackAct P [(true, i)] h₂') from
        (((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit ≫
          powComp ((blackActionCompletedQ sc P hP).map₂ (dnDotCellQ k sc i h₂)) m ▷
            (blackActionCompletedQ sc P hP).map _).toNatTrans) =
      (blackCompletedAdjunctionQ P hP i h₂ h₂').unit ≫
        Functor.whiskerRight ((show End (completionMap (blackAct P [(false, i)] h₂)) from
          completionMap₂ (blackMapQ P hP h₂ h₂ (dnDotQ (sc := sc) i ν))) ^ m)
          (completionMap (blackAct P [(true, i)] h₂')) := by
  dsimp only
  refine (Cat.dottedCup_toNatTrans _ _ m).trans ?_
  rw [toNatTrans_blackCompletedDotQ]
  rfl

include hτ₀ in
/-- **Brundan (1.9) on modules over the matrix ring, from the completed black action**
(`0 ≤ ⟨i, ν⟩`): the rightward crossing `z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m`, with `c` the diagonal
matrix of `-τ₀`, together with the dotted units `m ↦ φ₂(1) d^m ⊗ m`, with `d` the diagonal
matrix of the black-action dot on the second strand, has an explicit inverse on every module. -/
def blackFamilySumInvFromQ (M : ModuleCat.{max u v w} (KLR.Diagram.MatEnd X₁)ᵐᵒᵖ)
    {J : Type*} [Fintype J]
    (π : J → ((completionMap (blackAct P [(true, i)] h₁')).obj
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₁)) ⟶
        (toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₀)))
    (ι' : J → ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₀) ⟶
      (completionMap (blackAct P [(true, i)] h₁')).obj
        ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₁))))
    (hπ : ∑ j, π j ≫ ι' j = 𝟙 _) (hn : 0 ≤ ip RD i ν) :
    SumInvFrom
      (X := ModuleCat.of _ (Res (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)
        (Ind M (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂))))
      (Y := ModuleCat.of _ (Ind (Res (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁) M)
        (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁))) (Z := M)
      (ModuleCat.ofHom (sigmaLin (KLR.Diagram.MatEnd.mapEmbOp _ he₁ hX₁)
        (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)
        (KLR.Diagram.MatEnd.natEmb_comp_commute _ _ he₁ hX₁ he₂ hX₂ (-τ₀)) M))
      (fun m => ModuleCat.ofHom (Res.map (natMap (KLR.Diagram.MatEnd.intertwines_natEmb _ he₂ hX₂
          (blackMapQ P hP h₂ h₂ (dnDotQ (sc := sc) i ν))) ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂) M))
      (ip RD i ν).toNat :=
  KLR.Diagram.MatEnd.resIndSumInvFrom _ _ he₁ hX₁ he₂ hX₂
    (blackCompletedAdjunctionQ P hP i h₂ h₂')
    (KLR.Diagram.MatEnd.natEmb_comp_commute _ _ he₁ hX₁ he₂ hX₂ (-τ₀))
    (blackCompletedAdjunctionQ P hP i h₁ h₁') (blackCompletedNegSigmaQ P hP i h₁ h₁' h₂ h₂')
    (blackCompletedNegSigmaQ_generator P hP i h₁ h₁' h₂ h₂' he₁ hX₁ he₂ hX₂ τ₀ hτ₀) M π ι' hπ
    (KLR.Diagram.MatEnd.intertwines_natEmb _ he₂ hX₂ _)
    (KLR.Diagram.MatEnd.karoubiCorner_cornerMul_natEmb _ he₂ hX₂ _)
    ((blackCompletedSigmaSumInvFromQ P hP i h₁ h₁' h₂ h₂' (dnDotCellQ k sc i h₂)
      (homTrQ_dnDotCellQ k sc i h₂) (dnCrossCellQ k sc i h₁ h₂) (homTrQ_dnCrossCellQ k sc i h₁ h₂)
      hn).congr rfl (funext fun m => blackCompletedDottedCupQ_eq P hP i h₂ h₂' m) rfl)

end Generic

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

variable (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
  (addRedUpRelations RD (Subtype.val ∘ Λ) k (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)).lin
    (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)

/-- The crossing element on the twice-extended all-down matrix ring: the diagonal matrix of
minus the black-action crossing of the two new downward strands. -/
abbrev blackMatrixCrossQ : (downwardMatrix (Q) ({i} + ({i} + ν)))ᵐᵒᵖ :=
  op (KLR.Diagram.MatEnd.natEmb (blackAct (Q) [(false, i)] (wt_downRightWeight (Λ := Λ) i ν) ⋙
      blackAct (Q) [(false, i)] (wt_downRightWeight (Λ := Λ) i ({i} + ν)))
    (KLR.Diagram.MatEnd.compEq _ _ (blackAct_downObj (Q) i) (blackAct_downObj (Q) i))
    (-crossNatQ (Q) hP i ν))

theorem blackMatrixCrossQ_commute (a : (downwardMatrix (Q) ν)ᵐᵒᵖ) :
    blackMatrixCrossQ P t i ν hP * blackMatrixOp P t i ({i} + ν) (blackMatrixOp P t i ν a) =
      blackMatrixOp P t i ({i} + ν) (blackMatrixOp P t i ν a) * blackMatrixCrossQ P t i ν hP :=
  KLR.Diagram.MatEnd.natEmb_comp_commute _ _ (appendDown_injective i) (blackAct_downObj (Q) i)
    (appendDown_injective i) (blackAct_downObj (Q) i) (-crossNatQ (Q) hP i ν) a

/-- The dot element on the extended all-down matrix ring: the diagonal matrix of the
black-action dot on the new downward strand. -/
abbrev blackMatrixDotQ : (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ :=
  op (KLR.Diagram.MatEnd.natEmb (blackAct (Q) [(false, i)] (wt_downRightWeight (Λ := Λ) i ν))
    (blackAct_downObj (Q) i)
    (blackMapQ (Q) hP (wt_downRightWeight (Λ := Λ) i ν) (wt_downRightWeight (Λ := Λ) i ν)
      (dnDotQ (sc := sc) i _)))

theorem blackMatrixDotQ_intertwines :
    Intertwines (blackMatrixOp P t i ν) (blackMatrixOp P t i ν) (blackMatrixDotQ P t i ν hP) :=
  KLR.Diagram.MatEnd.intertwines_natEmb _ (appendDown_injective i) (blackAct_downObj (Q) i) _

/-- **Brundan (1.8) for Webster's functors on modules over the all-down matrix ring**
(`⟨i, λ⟩ ≤ 0`, with `λ` the right weight of content `i + ν`): the rightward crossing
`z ⊗ m ↦ φ(z) c φ(1) ⊗ m` (`c = blackMatrixCrossQ`) together with the dotted counits
`z ⊗ m ↦ z d^m m` (`d = blackMatrixDotQ`) has an explicit inverse on every module. -/
def blackMatrixSumInvToQ (M : ModuleCat.{max u v w} (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ)
    (hn : ip RD i (downRightWeight RD Λ ({i} + ν)) ≤ 0) :=
  blackFamilySumInvToQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν)
    (wt_downRightWeight i ({i} + ν)) (wt_upDownRightWeight i ({i} + ν))
    (appendDown_injective i) (blackAct_downObj (Q) i) (appendDown_injective i)
    (blackAct_downObj (Q) i) (crossNatQ (Q) hP i ν) (toNatTrans_blackCompletedCrossQ (Q) hP i ν) M
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec hn

/-- **Brundan (1.9) for Webster's functors on modules over the all-down matrix ring**
(`0 ≤ ⟨i, λ⟩`, with `λ` the right weight of content `i + ν`): the rightward crossing together
with the dotted units `m ↦ φ(1) d^m ⊗ m` (`d` the black-action dot on the new strand of content
`i + (i + ν)`) has an explicit inverse on every module. -/
def blackMatrixSumInvFromQ (M : ModuleCat.{max u v w} (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ)
    (hn : 0 ≤ ip RD i (downRightWeight RD Λ ({i} + ν))) :=
  blackFamilySumInvFromQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν)
    (wt_downRightWeight i ({i} + ν)) (wt_upDownRightWeight i ({i} + ν))
    (appendDown_injective i) (blackAct_downObj (Q) i) (appendDown_injective i)
    (blackAct_downObj (Q) i) (crossNatQ (Q) hP i ν) (toNatTrans_blackCompletedCrossQ (Q) hP i ν) M
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec hn

end Block

end Categorification.Stendhal.DoubleDiagram
