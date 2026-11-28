/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMatrixSumInvQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContent
import Categorification.Diagrams.KLR.MatEndModuleSumInvZero

/-!
# Brundan's relation (1.9) outside the content, on the all-down matrix ring

Brundan, arXiv:1501.00350v1, (1.9), for Webster's functors `Fᵢ ⊣ Eᵢ` on right modules over the
all-down matrix ring of a content `μ` with `i ∉ μ` (Webster, arXiv:1309.3796v3, §4.6,
Theorem 4.31), at the black action of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3,
Definition 1.1, `r = 1`; `CLQ.pres RD k sc`). There `Eᵢ` of the all-down sum vanishes
(`isZero_blackUp_downSum`), so the source of the rightward crossing vanishes, and the explicit
inverse of the completed black action (`blackCompletedSigmaSumInvFromQ`) says that the dotted
units identify `M^{⊕ n}` with `Eᵢ Fᵢ M`, for `n = ⟨i, λ⟩ ≥ 0` with `λ` the weight of content
`μ`:

* `blackFamilySumInvFromOfIsZeroQ`: the statement for general families, given the vanishing;
* `blackMatrixSumInvFromOfNotMemQ`: the statement on the all-down matrix ring of `μ`, `i ∉ μ`.

This is the boundary case of the local Rouquier data (compare `GlobalLoc.locNegBoundary` for
the cyclotomic KLR algebras).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits Bicategory QuantumGroup
  QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction KL3.Diagram InductionAlong
  MulOpposite

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
  {ι₁ ι₂ : Type u} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {X₁ : ι₁ → ViolatingCategory P ν} {X₂ : ι₂ → ViolatingCategory P ν₂}
  {e₂ : ι₁ → ι₂} (he₂ : Function.Injective e₂)
  (hX₂ : ∀ s, (blackAct P [(false, i)] h₂).obj (X₁ s) = X₂ (e₂ s))

/-- **Brundan (1.9) on modules, for families on which `Eᵢ` vanishes**: if the completed `Eᵢ`
vanishes on the sum of `X₁`, then the dotted units `m ↦ φ(1) d^m ⊗ m` (`d` the black-action
dot on the new strand) identify `M^{⊕ n}` with `Res (Ind M)`, `n = ⟨i, ν⟩ ≥ 0`, for every
module `M` over the matrix ring of `X₁`. -/
def blackFamilySumInvFromOfIsZeroQ (M : ModuleCat.{max u v w} (KLR.Diagram.MatEnd X₁)ᵐᵒᵖ)
    (hG : IsZero ((completionMap (blackAct P [(true, i)] h₁')).obj
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum X₁))))
    (hn : 0 ≤ ip RD i ν) :
    SumInvFrom
      (X := ModuleCat.of _ (Res (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂)
        (Ind M (KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂))))
      (Y := ModuleCat.of _ PUnit) (Z := M) 0
      (fun m => ModuleCat.ofHom (Res.map (natMap (KLR.Diagram.MatEnd.intertwines_natEmb _ he₂ hX₂
          (blackMapQ P hP h₂ h₂ (dnDotQ (sc := sc) i ν))) ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := KLR.Diagram.MatEnd.mapEmbOp _ he₂ hX₂) M))
      (ip RD i ν).toNat :=
  KLR.Diagram.MatEnd.resIndSumInvFromOfIsZero _ he₂ hX₂
    (blackCompletedAdjunctionQ P hP i h₂ h₂') (blackCompletedNegSigmaQ P hP i h₁ h₁' h₂ h₂')
    ((completionMap (blackAct P [(false, i)] h₁)).map_isZero hG)
    (KLR.Diagram.MatEnd.intertwines_natEmb _ he₂ hX₂ _)
    (KLR.Diagram.MatEnd.karoubiCorner_cornerMul_natEmb _ he₂ hX₂ _) M
    ((blackCompletedSigmaSumInvFromQ P hP i h₁ h₁' h₂ h₂' (dnDotCellQ k sc i h₂)
      (homTrQ_dnDotCellQ k sc i h₂) (dnCrossCellQ k sc i h₁ h₂) (homTrQ_dnCrossCellQ k sc i h₁ h₂)
      hn).congr rfl (funext fun m => blackCompletedDottedCupQ_eq P hP i h₂ h₂' m) rfl)

end Generic

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (μ : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

variable (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
  (addRedUpRelations RD (Subtype.val ∘ Λ) k (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)).lin
    (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)

/-- **Brundan (1.9) outside the content, on modules over the all-down matrix ring**
(Webster, arXiv:1309.3796v3, Theorem 4.31): for `i ∉ μ`, with `λ` the weight of content `μ`
and `n = ⟨i, λ⟩ ≥ 0`, the dotted units `m ↦ φ(1) d^m ⊗ m` (`d` the black-action dot on the new
strand) identify `M^{⊕ n}` with `Eᵢ Fᵢ M` for every module `M`. -/
def blackMatrixSumInvFromOfNotMemQ (M : ModuleCat.{max u v w} (downwardMatrix (Q) μ)ᵐᵒᵖ)
    (hi : i ∉ μ) :=
  blackFamilySumInvFromOfIsZeroQ (Q) hP i
    ((wt_append RD (downRightWeight RD Λ μ) [dn i] [up i]).symm.trans
      (wt_dn_up RD i (downRightWeight RD Λ μ))) rfl
    (wt_downRightWeight i μ) (wt_upDownRightWeight i μ)
    (appendDown_injective i) (blackAct_downObj (Q) i) M
    (isZero_blackUp_downSum P t i μ hi) (ip_nonneg_of_notMem i μ hi)

end Block

end Categorification.Stendhal.DoubleDiagram
