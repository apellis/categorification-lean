/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecomp
import Categorification.Diagrams.KLR.MatEndModuleDecompNaturality

/-!
# Naturality of the commutation of `Eᵢ` and `Fᵢ` on modules

The isomorphisms `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` (`blackModuleEFEquiv`) and
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` (`blackModuleFEEquiv`) of the all-down matrix ring
(Webster, arXiv:1309.3796v3, Thm 4.31 on modules) are natural in the module `M`
(`blackModuleEFEquiv_map`, `blackModuleFEEquiv_map`). This is what makes them compatible with
a further action commuting with the algebra, as used for the tensor factors in the proof of
Proposition 5.5 there.
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
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- The ring map of `Fᵢ` on all-down matrix rings, from content `i + ν` to content `i + i + ν`
(the matrix map of the first factor of `blackModuleEFEquiv`). -/
abbrev blackOuterHom :=
  KLR.Diagram.MatEnd.mapEmbOp (blackAct (Q) [(false, i)] (wt_downRightWeight i ({i} + ν)))
    (appendDown_injective i) (blackAct_downObj (Q) i)

/-- The ring map of `Fᵢ` on all-down matrix rings, from content `ν` to content `i + ν`. -/
abbrev blackInnerHom :=
  KLR.Diagram.MatEnd.mapEmbOp (blackAct (Q) [(false, i)] (wt_downRightWeight i ν))
    (appendDown_injective i) (blackAct_downObj (Q) i)

/-- `blackModuleEFEquiv` is natural in the module: it carries `Eᵢ Fᵢ f` to
`Fᵢ Eᵢ f × f^n`. -/
theorem blackModuleEFEquiv_map (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    {M M₂ : Type (max u v w)} [AddCommGroup M]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M] [AddCommGroup M₂]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M₂]
    (f : M →ₗ[(downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ] M₂)
    (hn : 0 ≤ ip RD i (downRightWeight RD Λ ({i} + ν)))
    (x : Res (blackOuterHom P t i ν) (Ind M (blackOuterHom P t i ν))) :
    blackModuleEFEquiv P t i ν hP M₂ hn
        (Res.map (φ := blackOuterHom P t i ν) (Ind.map (φ := blackOuterHom P t i ν) f) x) =
      (Ind.map (φ := blackInnerHom P t i ν) (Res.map (φ := blackInnerHom P t i ν) f)
          (blackModuleEFEquiv P t i ν hP M hn x).1,
        fun s => f ((blackModuleEFEquiv P t i ν hP M hn x).2 s)) := by
  delta blackModuleEFEquiv blackModuleSumDecompEF
  apply KLR.Diagram.MatEnd.resIndEquivIndResProd_map

/-- `blackModuleFEEquiv` is natural in the module: it carries `Fᵢ Eᵢ f` to
`Eᵢ Fᵢ f × f^{-n}`. -/
theorem blackModuleFEEquiv_map (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    {M M₂ : Type (max u v w)} [AddCommGroup M]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M] [AddCommGroup M₂]
    [Module (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ M₂]
    (f : M →ₗ[(downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ] M₂)
    (hn : ip RD i (downRightWeight RD Λ ({i} + ν)) ≤ 0)
    (x : Ind (Res (blackInnerHom P t i ν) M) (blackInnerHom P t i ν)) :
    blackModuleFEEquiv P t i ν hP M₂ hn
        (Ind.map (φ := blackInnerHom P t i ν) (Res.map (φ := blackInnerHom P t i ν) f) x) =
      (Res.map (φ := blackOuterHom P t i ν) (Ind.map (φ := blackOuterHom P t i ν) f)
          (blackModuleFEEquiv P t i ν hP M hn x).1,
        fun s => f ((blackModuleFEEquiv P t i ν hP M hn x).2 s)) := by
  delta blackModuleFEEquiv blackModuleSumDecompFE
  convert KLR.Diagram.MatEnd.indResEquivResIndProd_map _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ x
    using 1

end Block

end DoubleDiagram

end Categorification.Stendhal
