/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTensor
import Categorification.WeightedKLR.RedStrands.DoubleBlackRestrictionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleCommutationQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionCompQ
import Categorification.Diagrams.KLR.MatEndModuleComp

/-!
# Webster's `Eᵢ Fᵢ` on all modules as a module functor of the black action

Webster, arXiv:1309.3796v3, §4.6 and the proof of Proposition 5.5. Over the all-down matrix
ring of content `ν`, Webster's functor `Eᵢ Fᵢ` (induction along the matrix map of `Fᵢ`, then
restriction along it) on a right module `N` is the module functor of the word `Eᵢ Fᵢ` of the
black action: `Res (Ind N) ≅ (⊕ O_ν ⟶ Eᵢ Fᵢ ⊕ O_ν) ⊗ N` (`blackResIndModuleQ`). It is
semilinear for the all-down matrix ring by `MatEnd.resIndModuleEquivOfIso_smul`. Dually, induction
after restriction on the block of content `i + ν` is the module functor of the word `Fᵢ Eᵢ`
(`blackIndResModuleQ`); this uses that `Eᵢ` of the all-down sum of content `i + ν` is generated
by the all-down sum of content `ν` (`blackUp_downSum_generated`). Both hold for every module,
not only for projective ones.

This is the version of `BlackModuleTensor` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
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

section Generic

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

end Generic

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)
local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)


local notation "Eu" => blackAct (Q) [(true, i)] (wt_upDownRightWeight i ν)

/-- **Webster's `Fᵢ Eᵢ` as a module functor** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): induction after restriction along the matrix map of `Fᵢ` is the module
functor of the word `Fᵢ Eᵢ` of the black action. -/
def blackIndResModuleQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M] :
    letI := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOpY (downObj (Q) (ν := {i} + ν))) M
    Ind (Res (blackMatrixOp P t i ν) M) (blackMatrixOp P t i ν) ≃ₗ[ℤ]
      BalancedTensor ℤ
        (End ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := {i} + ν)))))ᵐᵒᵖ
        (End ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := {i} + ν)))))ᵐᵒᵖ
        ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := {i} + ν))) ⟶
          (completionMap (blackAct (Q) [dn i, up i] (wt_dn_up RD i _))).obj
            ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := {i} + ν))))) M :=
  KLR.Diagram.MatEnd.indResModuleEquivOfIso F (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunctionQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν)) M
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec
    (completionIso (blackActAppend (Q) [dn i] [up i] (wt_upDownRightWeight i ν)
      (wt_downRightWeight i ν) (wt_dn_up RD i _)))

/-- **Webster's `Eᵢ Fᵢ` as a module functor** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): restriction after induction along the matrix map of `Fᵢ` is the module
functor of the word `Eᵢ Fᵢ` of the black action. -/
def blackResIndModuleQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    (N : Type (max u v w)) [AddCommGroup N] [Module (downwardMatrix (Q) ν)ᵐᵒᵖ N] :
    letI : Module (End ((toKaroubi _).obj (downSum (Q) ν)))ᵐᵒᵖ N := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := ν))) N
    Res (blackMatrixOp P t i ν) (Ind N (blackMatrixOp P t i ν)) ≃ₗ[ℤ]
      HomTensor.tensorObj ((toKaroubi _).obj (downSum (Q) ν))
        ((toKaroubi _).obj (downSum (Q) ν)) N
        (completionMap (blackAct (Q) [up i, dn i] (wt_up_dn RD i _))) :=
  KLR.Diagram.MatEnd.resIndModuleEquivOfIso F (appendDown_injective i)
    (blackAct_downObj (Q) i) N
    (blackCompletedAdjunctionQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (completionIso (blackActAppend (Q) [up i] [dn i] (wt_downRightWeight i ν)
      (wt_upDownRightWeight i ν) (wt_up_dn RD i _)))

end Block

end DoubleDiagram

end Categorification.Stendhal
