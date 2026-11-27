/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleCross
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecompQ
import Categorification.Diagrams.KLR.MatEndModuleCross

/-!
# The commutation of `Eⱼ` and `Fᵢ` on all modules, for `i ≠ j`

The relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of the categorical action (Webster, arXiv:1309.3796v3,
Theorem 4.31) on modules, an input of the proof of Proposition 5.5 there. For a right module `M`
over the all-down matrix ring of content `j + ρ`, Webster's `Eⱼ Fᵢ M` (restriction along the
matrix map of `Fⱼ` out of content `i + ρ`, after induction along the matrix map of `Fᵢ`) and
`Fᵢ Eⱼ M` (induction along `Fᵢ` out of content `ρ`, after restriction along `Fⱼ`) are
isomorphic as modules over the all-down matrix ring of content `i + ρ`
(`blackModuleCrossEquivQ`).

The two contents `j + (i + ρ)` and `i + (j + ρ)` of the middle term are equal but not
definitionally, so the all-down loadings of the first are transported to the second
(`downIdxCast`, `blackAct_downObj_cast`).

This is the version of `BlackModuleCross` in which the black strands carry the relations of
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

section Cast

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}

variable {k : Type*} [CommRing k] (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)

end Cast

section Cross

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)
  (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)

/-- `blackCrossIsoQ` with the target weight given by an equality. -/
def blackCrossIsoOfEqQ (i j : I) (h : i ≠ j) {μ ν : X} (h₁ : wt RD μ [up i, dn j] = ν)
    (h₂ : wt RD μ [dn j, up i] = ν) :
    blackAct P [up i, dn j] h₁ ≅ blackAct P [dn j, up i] h₂ := by
  subst h₁
  exact blackCrossIsoQ P hP i j h μ

end Cross

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i j : I) (ρ : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- The isomorphism `Fᵢ ⋙ Eⱼ ≅ Eⱼ ⋙ Fᵢ` of completed black actions, out of the all-down
weight of content `j + ρ` (`blackCrossIsoQ` composed with the composition isomorphisms). -/
def blackCrossCompletionIsoQ (hji : j ≠ i) (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0) :
    completionMap (blackAct (Q) [dn i] (wt_downRightWeight (Λ := Λ) i ({j} + ρ)) ⋙
        blackAct (Q) [up j] (cross_wt_up (Λ := Λ) i j ρ)) ≅
      completionMap (blackAct (Q) [up j] (wt_upDownRightWeight (Λ := Λ) j ρ) ⋙
        blackAct (Q) [dn i] (wt_downRightWeight (Λ := Λ) i ρ)) :=
  let e₁ := completionIso (blackActAppend (Q) [up j] [dn i]
    (wt_downRightWeight (Λ := Λ) i ({j} + ρ)) (cross_wt_up (Λ := Λ) i j ρ)
    (cross_wt_up_dn (Λ := Λ) i j ρ))
  let e₂ := completionIso (blackCrossIsoOfEqQ (Q) hP j i hji (cross_wt_up_dn (Λ := Λ) i j ρ)
    (cross_wt_dn_up (Λ := Λ) i j ρ))
  let e₃ := completionIso (blackActAppend (Q) [dn i] [up j] (wt_upDownRightWeight (Λ := Λ) j ρ)
    (wt_downRightWeight (Λ := Λ) i ρ) (cross_wt_dn_up (Λ := Λ) i j ρ))
  e₁.symm ≪≫ e₂ ≪≫ e₃

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on all modules**, `i ≠ j` (Webster, arXiv:1309.3796v3,
Theorem 4.31, input of the proof of Proposition 5.5): for every right module `M` over the
all-down matrix ring of content `j + ρ`, `Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` as modules over the all-down
matrix ring of content `i + ρ`. -/
def blackModuleCrossEquivQ (hji : j ≠ i) (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) ({j} + ρ))ᵐᵒᵖ M] :=
  KLR.Diagram.MatEnd.resIndEquivIndResCross (X := downObj (Q) (ν := {j} + ρ))
    (X' := downObj (Q) (ν := {i} + ρ)) (Y := downObj (Q) (ν := {i} + ({j} + ρ)))
    (Z := downObj (Q) (ν := ρ)) (e₁' := fun s => downIdxCast (cross_content i j ρ) (appendDown j s))
    M
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ({j} + ρ))) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackAct (Q) [(false, j)] (cross_wt_down (Λ := Λ) i j ρ))
    ((downIdxCast_injective (cross_content i j ρ)).comp (appendDown_injective j))
    (blackAct_downObj_cast (Q) j (cross_content i j ρ) (cross_wt_down (Λ := Λ) i j ρ))
    (blackCompletedAdjunctionQ (Q) hP j (cross_wt_down (Λ := Λ) i j ρ) (cross_wt_up (Λ := Λ) i j ρ))
    (blackAct (Q) [(false, j)] (wt_downRightWeight j ρ)) (appendDown_injective j)
    (blackAct_downObj (Q) j)
    (blackCompletedAdjunctionQ (Q) hP j (wt_downRightWeight j ρ) (wt_upDownRightWeight j ρ))
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ρ)) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackUp_downSum_generated P t j ρ).choose_spec.choose
    (blackUp_downSum_generated P t j ρ).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t j ρ).choose_spec.choose_spec.choose_spec
    (blackCrossCompletionIsoQ P t i j ρ hji hP)

end Block

end DoubleDiagram

end Categorification.Stendhal
