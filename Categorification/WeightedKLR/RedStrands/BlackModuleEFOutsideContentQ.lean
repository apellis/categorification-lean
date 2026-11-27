/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContent
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecompQ
import Categorification.WeightedKLR.RedStrands.MatEndResIndPi

/-!
# `Eᵢ Fᵢ` on modules of content not containing `i`

Webster, arXiv:1309.3796v3, the commutation relation of Theorem 4.31 on modules, an input of
the proof of Proposition 5.5. On the all-down matrix ring of a content `μ` with `i ∉ μ`, the
functor `Eᵢ` vanishes: every object of `Eᵢ (⊕ O_μ)` has signed content `μ - i`, which has a
negative coefficient at `i`, so its identity factors through no all-down boundary and is zero
(Webster, §4.5, proof of Theorem 4.29; `isZero_blackUp_downSum`). The weight `λ` of content `μ`
then has `n = ⟨i, λ⟩ ≥ 0` (`ip_nonneg_of_notMem`), and the commutation relation
`Eᵢ Fᵢ 1_λ ≅ Fᵢ Eᵢ 1_λ ⊕ 1_λ^{⊕ n}` of Webster's Theorem 4.31 gives, for every right module `M`,
`Eᵢ Fᵢ M ≅ M^{⊕ n}` as modules over the all-down matrix ring
(`blackModuleEFEquivOfNotMemQ`), naturally in `M` (`blackModuleEFEquivOfNotMem_mapQ`).

This is the version of `BlackModuleEFOutsideContent` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits QuantumGroup
  QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram
  InductionAlong MulOpposite

open scoped Classical

attribute [local instance] HomTensor.bimodule

namespace DoubleDiagram

universe w u v

section Content

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

variable (i : I) (μ : Multiset I)

/-- **`Eᵢ Fᵢ` outside the content on all modules** (Webster, arXiv:1309.3796v3, Theorem 4.31
and input of the proof of Proposition 5.5): for `i ∉ μ`, with `λ` the weight of content `μ` and
`n = ⟨i, λ⟩ ≥ 0`, `Eᵢ Fᵢ M ≅ M^{⊕ n}` for every right module `M` over the all-down matrix ring
of content `μ`. -/
def blackModuleEFEquivOfNotMemQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) μ)ᵐᵒᵖ M]
    (hi : i ∉ μ) :=
  KLR.Diagram.MatEnd.resIndEquivPiOfSubsingleton
    (blackAct (Q) [(false, i)] (wt_downRightWeight i μ)) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunctionQ (Q) hP i (wt_downRightWeight i μ) (wt_upDownRightWeight i μ))
    (completionIso (blackActAppend (Q) [up i] [dn i] (wt_downRightWeight i μ)
      (wt_upDownRightWeight i μ) (wt_up_dn RD i _)))
    (subsingleton_hom_blackDnUp_downSum P t i μ hi)
    (completionMap_eq_id _ (blackAct_nil (Q) _)) M
    (letI := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := μ))) M
    blackModuleSumDecompEFQ (Q) hP i (downRightWeight RD Λ μ)
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := μ)))) M
      (ip_nonneg_of_notMem i μ hi))

/-- `blackModuleEFEquivOfNotMemQ` is natural in the module: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem blackModuleEFEquivOfNotMem_mapQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    {M M₂ : Type (max u v w)} [AddCommGroup M] [Module (downwardMatrix (Q) μ)ᵐᵒᵖ M]
    [AddCommGroup M₂] [Module (downwardMatrix (Q) μ)ᵐᵒᵖ M₂]
    (f : M →ₗ[(downwardMatrix (Q) μ)ᵐᵒᵖ] M₂) (hi : i ∉ μ)
    (x : Res (blackMatrixOp P t i μ) (Ind M (blackMatrixOp P t i μ))) :
    blackModuleEFEquivOfNotMemQ P t i μ hP M₂ hi
        (Res.map (φ := blackMatrixOp P t i μ) (Ind.map (φ := blackMatrixOp P t i μ) f) x) =
      fun s => f (blackModuleEFEquivOfNotMemQ P t i μ hP M hi x s) := by
  delta blackModuleEFEquivOfNotMemQ blackModuleSumDecompEFQ
  apply KLR.Diagram.MatEnd.resIndEquivPiOfSubsingleton_map

end Content

end DoubleDiagram

end Categorification.Stendhal
