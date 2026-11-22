/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTensor
import Categorification.Diagrams.KLR.MatEndModuleAdjunction

/-!
# `Eᵢ` is left adjoint to `Fᵢ` on all modules

Webster, arXiv:1309.3796v3, Theorem 4.31: the functors `Fᵢ` and `Eᵢ` on right
`T^λ`-modules are biadjoint (up to grading shift, which is invisible on ungraded modules).
Induction is always left adjoint to restriction (`blackAdjunction`); this file proves the other
adjunction `Eᵢ ⊣ Fᵢ` for the all-down matrix rings of the categorical action.

* `blackCompletedAdjunctionOp`: in the completed black action, the downward black strand of
  colour `i` is right adjoint to the upward one: the image of the other half of the
  biadjunction of the Khovanov–Lauda 2-category (compare `blackCompletedAdjunction`).
* `blackResIndHomEquiv`: for right modules `M` over the all-down matrix ring of content
  `i + ν` and `N` over that of content `ν`,
  `Hom(Res M, N) ≃ Hom(M, Ind N)`, restriction and induction along the matrix map of `Fᵢ`.
  It combines the module functors of `MatEndModuleFunctor` with `HomTensor.homEquiv`; the
  finiteness input is that `Eᵢ` of the all-down sum of content `i + ν` is a summand of copies
  of the all-down sum of content `ν` (`blackUp_downSum_generated`).

This adjunction is the input that Chuang–Rouquier's theory of `sl₂`-categorifications
(arXiv:math/0407205, §5, in particular Proposition 5.20) needs beyond `Fᵢ ⊣ Eᵢ`; Webster uses
it in §5 (Propositions 5.11–5.18).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong
  MulOpposite

open scoped Classical

namespace DoubleDiagram

universe w u v

section Adjunction

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (pres RD k).Rel,
      P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

/-- **The downward black strand is right adjoint to the upward one** in the completed black
action: the image of the second half of the biadjunction of the Khovanov–Lauda 2-category. -/
def blackCompletedAdjunctionOp (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) :
    completionMap (blackAct P [(true, i)] h') ⊣ completionMap (blackAct P [(false, i)] h) :=
  Adjunction.ofCat ((blackActionCompleted P hP).mapAdjunction
    (RevBicat.adjunction ((biadjColour RD k (downStrandHom (k := k) i h) ⟨dn i, μ⟩ rfl).left)))

end Adjunction

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)
local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)

/-- **`Eᵢ ⊣ Fᵢ` on all modules** (Webster, arXiv:1309.3796v3, Theorem 4.31): restriction
along the matrix map of `Fᵢ` is left adjoint to induction along it,
`Hom(Res M, N) ≃ Hom(M, Ind N)`. -/
def blackResIndHomEquiv (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M]
    (N : Type (max u v w)) [AddCommGroup N] [Module (downwardMatrix (Q) ν)ᵐᵒᵖ N] :
    (Res (blackMatrixOp P t i ν) M →ₗ[(downwardMatrix (Q) ν)ᵐᵒᵖ] N) ≃
      (M →ₗ[(downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ] Ind N (blackMatrixOp P t i ν)) :=
  KLR.Diagram.MatEnd.resIndHomEquiv F (appendDown_injective i) (blackAct_downObj (Q) i)
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackCompletedAdjunctionOp (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν))
    (blackUp_downSum_generated P t i ν).choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t i ν).choose_spec.choose_spec.choose_spec M N

end Block

end DoubleDiagram

end Categorification.Stendhal
