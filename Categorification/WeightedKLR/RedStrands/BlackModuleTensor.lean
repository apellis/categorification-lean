/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackRestriction
import Categorification.WeightedKLR.RedStrands.BlackModuleCommutation
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionComp
import Categorification.Diagrams.KLR.MatEndModuleComp

/-!
# Webster's `Eᵢ Fᵢ` on all modules as a module functor of the black action

Webster, arXiv:1309.3796v3, §4.6 and the proof of Proposition 5.5. Over the all-down matrix
ring of content `ν`, Webster's functor `Eᵢ Fᵢ` (induction along the matrix map of `Fᵢ`, then
restriction along it) on a right module `N` is the module functor of the word `Eᵢ Fᵢ` of the
black action: `Res (Ind N) ≅ (⊕ O_ν ⟶ Eᵢ Fᵢ ⊕ O_ν) ⊗ N` (`blackResIndModule`). It is
semilinear for the all-down matrix ring by `MatEnd.resIndModuleEquivOfIso_smul`. This holds for
every module `N`, not only for projective ones.
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
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

instance completionMap_blackAct_comp_additive {μ ν₁ ν₂ : X} (s t : List (Letter I))
    (ht : wt RD μ t = ν₁) (hs : wt RD ν₁ s = ν₂) :
    (completionMap (blackAct P t ht ⋙ blackAct P s hs)).Additive := by
  unfold completionMap
  infer_instance

end Generic

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)
local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)


/-- **Webster's `Eᵢ Fᵢ` as a module functor** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): restriction after induction along the matrix map of `Fᵢ` is the module
functor of the word `Eᵢ Fᵢ` of the black action. -/
def blackResIndModule (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (N : Type (max u v w)) [AddCommGroup N] [Module (downwardMatrix (Q) ν)ᵐᵒᵖ N] :
    letI : Module (End ((toKaroubi _).obj (downSum (Q) ν)))ᵐᵒᵖ N := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := ν))) N
    Res (blackMatrixOp P t i ν) (Ind N (blackMatrixOp P t i ν)) ≃ₗ[ℤ]
      HomTensor.tensorObj ((toKaroubi _).obj (downSum (Q) ν))
        ((toKaroubi _).obj (downSum (Q) ν)) N
        (completionMap (blackAct (Q) [up i, dn i] (wt_up_dn RD i _))) :=
  KLR.Diagram.MatEnd.resIndModuleEquivOfIso F (appendDown_injective i)
    (blackAct_downObj (Q) i) N
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (completionIso (blackActAppend (Q) [up i] [dn i] (wt_downRightWeight i ν)
      (wt_upDownRightWeight i ν) (wt_up_dn RD i _)))

end Block

end DoubleDiagram

end Categorification.Stendhal
