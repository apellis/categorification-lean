/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecomp
import Categorification.Diagrams.KLR.MatEndModuleCross

/-!
# The commutation of `Eⱼ` and `Fᵢ` on all modules, for `i ≠ j`

The relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of the categorical action (Webster, arXiv:1309.3796v3,
Theorem 4.31) on modules, an input of the proof of Proposition 5.5 there. For a right module `M`
over the all-down matrix ring of content `j + ρ`, Webster's `Eⱼ Fᵢ M` (restriction along the
matrix map of `Fⱼ` out of content `i + ρ`, after induction along the matrix map of `Fᵢ`) and
`Fᵢ Eⱼ M` (induction along `Fᵢ` out of content `ρ`, after restriction along `Fⱼ`) are
isomorphic as modules over the all-down matrix ring of content `i + ρ`
(`blackModuleCrossEquiv`).

The two contents `j + (i + ρ)` and `i + (j + ρ)` of the middle term are equal but not
definitionally, so the all-down loadings of the first are transported to the second
(`downIdxCast`, `blackAct_downObj_cast`).
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

/-- Transport of an all-down loading along an equality of contents. -/
def downIdxCast {ν ν' : Multiset I} (h : ν = ν')
    (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    {s : Seq (stendhalWeight ℓ ν') // IsRedOrdered s} :=
  h ▸ s

theorem downIdxCast_injective {ν ν' : Multiset I} (h : ν = ν') :
    Function.Injective (downIdxCast (ℓ := ℓ) h) := by
  subst h
  exact fun _ _ e => e

variable {k : Type*} [CommRing k] (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)

/-- `blackAct_downObj` with the content of the target transported along an equality. -/
theorem blackAct_downObj_cast (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν')
    (hw : wt RD (downRightWeight RD Λ μ) [(false, j)] = downRightWeight RD Λ ν')
    (s : {s : Seq (stendhalWeight ℓ μ) // IsRedOrdered s}) :
    (blackAct P [(false, j)] hw).obj (downObj P s) =
      downObj P (downIdxCast hc (appendDown j s)) := by
  subst hc
  exact blackAct_downObj P j s

end Cast

section Cross

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)
  (hP : ∀ r : (pres RD k).Rel,
    P.lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)

/-- `blackCrossIso` with the target weight given by an equality. -/
def blackCrossIsoOfEq (i j : I) (h : i ≠ j) {μ ν : X} (h₁ : wt RD μ [up i, dn j] = ν)
    (h₂ : wt RD μ [dn j, up i] = ν) :
    blackAct P [up i, dn j] h₁ ≅ blackAct P [dn j, up i] h₂ := by
  subst h₁
  exact blackCrossIso P hP i j h μ

end Cross

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i j : I) (ρ : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- The two contents of the middle term. -/
theorem cross_content : ({j} + ({i} + ρ) : Multiset I) = {i} + ({j} + ρ) :=
  add_left_comm _ _ _

theorem cross_wt_down :
    wt RD (downRightWeight RD Λ ({i} + ρ)) [(false, j)] =
      downRightWeight RD Λ ({i} + ({j} + ρ)) :=
  (wt_downRightWeight j ({i} + ρ)).trans
    (congrArg (downRightWeight RD Λ) (cross_content i j ρ))

theorem cross_wt_up :
    wt RD (downRightWeight RD Λ ({i} + ({j} + ρ))) [(true, j)] =
      downRightWeight RD Λ ({i} + ρ) :=
  (congrArg (fun ν => wt RD (downRightWeight RD Λ ν) [(true, j)])
    (cross_content i j ρ).symm).trans (wt_upDownRightWeight j ({i} + ρ))

theorem cross_wt_up_dn :
    wt RD (downRightWeight RD Λ ({j} + ρ)) [up j, dn i] = downRightWeight RD Λ ({i} + ρ) :=
  (wt_append RD _ [up j] [dn i]).trans
    ((congrArg (fun μ => wt RD μ [up j]) (wt_downRightWeight i ({j} + ρ))).trans
      (cross_wt_up i j ρ))

theorem cross_wt_dn_up :
    wt RD (downRightWeight RD Λ ({j} + ρ)) [dn i, up j] = downRightWeight RD Λ ({i} + ρ) :=
  (wt_append RD _ [dn i] [up j]).trans
    ((congrArg (fun μ => wt RD μ [dn i]) (wt_upDownRightWeight j ρ)).trans
      (wt_downRightWeight i ρ))

/-- The isomorphism `Fᵢ ⋙ Eⱼ ≅ Eⱼ ⋙ Fᵢ` of completed black actions, out of the all-down
weight of content `j + ρ` (`blackCrossIso` composed with the composition isomorphisms). -/
def blackCrossCompletionIso (hji : j ≠ i) (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0) :
    completionMap (blackAct (Q) [dn i] (wt_downRightWeight (Λ := Λ) i ({j} + ρ)) ⋙
        blackAct (Q) [up j] (cross_wt_up (Λ := Λ) i j ρ)) ≅
      completionMap (blackAct (Q) [up j] (wt_upDownRightWeight (Λ := Λ) j ρ) ⋙
        blackAct (Q) [dn i] (wt_downRightWeight (Λ := Λ) i ρ)) :=
  let e₁ := completionIso (blackActAppend (Q) [up j] [dn i]
    (wt_downRightWeight (Λ := Λ) i ({j} + ρ)) (cross_wt_up (Λ := Λ) i j ρ)
    (cross_wt_up_dn (Λ := Λ) i j ρ))
  let e₂ := completionIso (blackCrossIsoOfEq (Q) hP j i hji (cross_wt_up_dn (Λ := Λ) i j ρ)
    (cross_wt_dn_up (Λ := Λ) i j ρ))
  let e₃ := completionIso (blackActAppend (Q) [dn i] [up j] (wt_upDownRightWeight (Λ := Λ) j ρ)
    (wt_downRightWeight (Λ := Λ) i ρ) (cross_wt_dn_up (Λ := Λ) i j ρ))
  e₁.symm ≪≫ e₂ ≪≫ e₃

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on all modules**, `i ≠ j` (Webster, arXiv:1309.3796v3,
Theorem 4.31, input of the proof of Proposition 5.5): for every right module `M` over the
all-down matrix ring of content `j + ρ`, `Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` as modules over the all-down
matrix ring of content `i + ρ`. -/
def blackModuleCrossEquiv (hji : j ≠ i) (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
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
    (blackCompletedAdjunction (Q) hP j (cross_wt_down (Λ := Λ) i j ρ) (cross_wt_up (Λ := Λ) i j ρ))
    (blackAct (Q) [(false, j)] (wt_downRightWeight j ρ)) (appendDown_injective j)
    (blackAct_downObj (Q) j)
    (blackCompletedAdjunction (Q) hP j (wt_downRightWeight j ρ) (wt_upDownRightWeight j ρ))
    (blackAct (Q) [(false, i)] (wt_downRightWeight i ρ)) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackUp_downSum_generated P t j ρ).choose_spec.choose
    (blackUp_downSum_generated P t j ρ).choose_spec.choose_spec.choose
    (blackUp_downSum_generated P t j ρ).choose_spec.choose_spec.choose_spec
    (blackCrossCompletionIso P t i j ρ hji hP)

end Block

end DoubleDiagram

end Categorification.Stendhal
