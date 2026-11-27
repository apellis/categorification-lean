/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleNaturality
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecompQ
import Categorification.Diagrams.KLR.MatEndModuleDecompNaturality

/-!
# Naturality of the commutation of `Eᵢ` and `Fᵢ` on modules

The isomorphisms `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` (`blackModuleEFEquivQ`) and
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` (`blackModuleFEEquivQ`) of the all-down matrix ring
(Webster, arXiv:1309.3796v3, Thm 4.31 on modules) are natural in the module `M`
(`blackModuleEFEquiv_mapQ`, `blackModuleFEEquiv_mapQ`). This is what makes them compatible with
a further action commuting with the algebra, as used for the tensor factors in the proof of
Proposition 5.5 there.

This is the version of `BlackModuleNaturality` in which the black strands carry the relations of
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

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- `blackModuleEFEquivQ` is natural in the module: it carries `Eᵢ Fᵢ f` to
`Fᵢ Eᵢ f × f^n`. -/
theorem blackModuleEFEquiv_mapQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    {M M₂ : Type (max u v w)} [AddCommGroup M]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M] [AddCommGroup M₂]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M₂]
    (f : M →ₗ[(downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ] M₂)
    (hn : 0 ≤ ip RD i (downRightWeight RD Λ ({i} + ν)))
    (x : Res (blackOuterHom P t i ν) (Ind M (blackOuterHom P t i ν))) :
    blackModuleEFEquivQ P t i ν hP M₂ hn
        (Res.map (φ := blackOuterHom P t i ν) (Ind.map (φ := blackOuterHom P t i ν) f) x) =
      (Ind.map (φ := blackInnerHom P t i ν) (Res.map (φ := blackInnerHom P t i ν) f)
          (blackModuleEFEquivQ P t i ν hP M hn x).1,
        fun s => f ((blackModuleEFEquivQ P t i ν hP M hn x).2 s)) := by
  delta blackModuleEFEquivQ blackModuleSumDecompEFQ
  apply KLR.Diagram.MatEnd.resIndEquivIndResProd_map

/-- `blackModuleFEEquivQ` is natural in the module: it carries `Fᵢ Eᵢ f` to
`Eᵢ Fᵢ f × f^{-n}`. -/
theorem blackModuleFEEquiv_mapQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    {M M₂ : Type (max u v w)} [AddCommGroup M]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M] [AddCommGroup M₂]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M₂]
    (f : M →ₗ[(downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ] M₂)
    (hn : ip RD i (downRightWeight RD Λ ({i} + ν)) ≤ 0)
    (x : Ind (Res (blackInnerHom P t i ν) M) (blackInnerHom P t i ν)) :
    blackModuleFEEquivQ P t i ν hP M₂ hn
        (Ind.map (φ := blackInnerHom P t i ν) (Res.map (φ := blackInnerHom P t i ν) f) x) =
      (Res.map (φ := blackOuterHom P t i ν) (Ind.map (φ := blackOuterHom P t i ν) f)
          (blackModuleFEEquivQ P t i ν hP M hn x).1,
        fun s => f ((blackModuleFEEquivQ P t i ν hP M hn x).2 s)) := by
  delta blackModuleFEEquivQ blackModuleSumDecompFEQ
  convert KLR.Diagram.MatEnd.indResEquivResIndProd_map _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ x
    using 1

end Block

end DoubleDiagram

end Categorification.Stendhal
