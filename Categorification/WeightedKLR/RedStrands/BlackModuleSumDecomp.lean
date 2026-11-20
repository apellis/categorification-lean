/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTensor
import Categorification.Diagrams.KLR.MatEndModuleDecomp

/-!
# The commutation relation of `Eᵢ` and `Fᵢ` on all modules

The commutation relation of the categorical action (Webster, arXiv:1309.3796v3, Thm 4.31) on
modules, an input of the proof of Proposition 5.5 there (the filtrations of `Eᵢ` and `Fᵢ` of a
standardization), which is not formalized in this file. On the all-down matrix ring of
content `i + ν`, with `λ` its right weight and `n = ⟨i, λ⟩`, Webster's functors `Eᵢ Fᵢ` (restriction after induction along the matrix map of `Fᵢ`) and `Fᵢ Eᵢ`
(induction after restriction) satisfy, for every right module `M`,

* `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` when `n ≥ 0` (`blackModuleEFEquiv`),
* `Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` when `n ≤ 0` (`blackModuleFEEquiv`),

as modules over the all-down matrix ring. Both functors are module functors of words of the
black action (`blackResIndModule`, `blackIndResModule`), whose decompositions
(`blackModuleSumDecompEF`, `blackModuleSumDecompFE`) give these isomorphisms
(`KLR.Diagram.MatEnd.resIndEquivIndResProd`, `KLR.Diagram.MatEnd.indResEquivResIndProd`).
They hold for all modules, not only for projective ones.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance] HomTensor.bimodule

namespace DoubleDiagram

universe w u v

theorem completionMap_eq_id {A : Type*} [Category A] [Preadditive A] (F : A ⥤ A) [F.Additive]
    (h : F = 𝟭 A) : completionMap F = 𝟭 _ := by
  subst h
  rfl

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- **`Eᵢ Fᵢ` against `Fᵢ Eᵢ` on all modules** (Webster, arXiv:1309.3796v3, input of the proof
of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`,
with `λ` the right weight of content `i + ν`, `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for every right
module `M` over the all-down matrix ring of content `i + ν`. -/
def blackModuleEFEquiv (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M]
    (hn : 0 ≤ ip RD i (downRightWeight RD Λ ({i} + ν))) :=
  KLR.Diagram.MatEnd.resIndEquivIndResProd
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ({i} + ν))) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i ({i} + ν))
      (wt_upDownRightWeight i ({i} + ν)))
    (completionIso (blackActAppend (Q) [up i] [dn i] (wt_downRightWeight i ({i} + ν))
      (wt_upDownRightWeight i ({i} + ν)) (wt_up_dn RD i _)))
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ν)) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec
    (completionIso (blackActAppend (Q) [dn i] [up i] (wt_upDownRightWeight i ν)
      (wt_downRightWeight i ν) (wt_dn_up RD i _)))
    (completionMap_eq_id _ (blackAct_nil (Q) _)) M
    (letI := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := {i} + ν))) M
    blackModuleSumDecompEF (Q) hP i (downRightWeight RD Λ ({i} + ν))
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := {i} + ν)))) M hn)

/-- **`Fᵢ Eᵢ` against `Eᵢ Fᵢ` on all modules** (Webster, arXiv:1309.3796v3, input of the proof
of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`,
with `λ` the right weight of content `i + ν`, `Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` for every right
module `M` over the all-down matrix ring of content `i + ν`. -/
def blackModuleFEEquiv (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M]
    (hn : ip RD i (downRightWeight RD Λ ({i} + ν)) ≤ 0) :=
  KLR.Diagram.MatEnd.indResEquivResIndProd
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ({i} + ν))) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i ({i} + ν))
      (wt_upDownRightWeight i ({i} + ν)))
    (completionIso (blackActAppend (Q) [up i] [dn i] (wt_downRightWeight i ({i} + ν))
      (wt_upDownRightWeight i ({i} + ν)) (wt_up_dn RD i _)))
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ν)) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec
    (completionIso (blackActAppend (Q) [dn i] [up i] (wt_upDownRightWeight i ν)
      (wt_downRightWeight i ν) (wt_dn_up RD i _)))
    (completionMap_eq_id _ (blackAct_nil (Q) _)) M
    (letI := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := {i} + ν))) M
    blackModuleSumDecompFE (Q) hP i (downRightWeight RD Λ ({i} + ν))
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := {i} + ν)))) M hn)

end Block

end DoubleDiagram

end Categorification.Stendhal
