/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackInduction
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.DoubleCLMorita
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackComparison
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.Algebra.HomTensorInd
import Categorification.Algebra.InductionAlongTensor

/-!
# `Fᵢ` on the categorical side is Webster's `Fᵢ` on modules

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31 and the paragraph after it. Under the Morita equivalence of
Theorem 4.30, an object `M` of the completed block of `DT^λ` corresponds to the right
`T^λ_ν`-module `Hom(⊕ O_ν, M)`, where `⊕ O_ν` is the sum of the all-down boundaries. The
categorical action of `Fᵢ` (appending a downward black strand of colour `i`) corresponds to
Webster's `Fᵢ`, the induction `N ↦ N ⊗_{T^λ_ν} e' T^λ_{ν+i}` along `appendBlackOp`:
`Hom(⊕ O_{ν+i}, Fᵢ M)` is the induction of `Hom(⊕ O_ν, M)`
(`DoubleDiagram.blackHomInd`, at the matrix ring of the all-down block, and
`clBlackHomIndQ`, at `T^λ` through the repaired Lemma 4.29). Both isomorphisms are semilinear
for the actions of the target rings.

This is the version of `DoubleBlackInduction` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong
  MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace DoubleDiagram

universe w u v

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)
local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)
local notation "Vc" => ViolatingCategory (Q) (downRightWeight RD Λ ν)

end Block

end DoubleDiagram

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ
local notation "T" => TensorProductAlgebra k (clDownwardQ KL) Λ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapPresentationOf (RDc) (redWeight (cyclotomicCoverWeightDatum Λ C)) (CLQ.pres (RDc) k KL) P (clDownwardQ KL) Λ fun i j => (CL.CLScalars.t KL i j : k))
local notation "PD" => addRedUpRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k
  (addMixedBlackRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k
    (CL.CLScalars.t KL) (Pin))
local notation "Vc" => ViolatingCategory (PD)
  (downRightWeight (RDc) (coordinateRedWeights Λ C) ν)
local notation "F" => blackAct (PD) [(false, i)] (wt_downRightWeight i ν)

/-- The repaired Lemma 4.29 on opposite rings. -/
abbrev clOpEquivQ (ν : Multiset I) : (T ν)ᵐᵒᵖ ≃+* (downwardMatrix (PD) ν)ᵐᵒᵖ :=
  RingEquiv.op (ordinaryToDownwardMatrixEquivQ (ν := ν) hP hwf).toRingEquiv

/-- The right `T^λ_ν`-module `Hom(⊕ O_ν, M)` of the Morita equivalence (Webster,
arXiv:1309.3796v3, Theorem 4.30): `T^λ_ν` acts through the repaired Lemma 4.29. -/
abbrev clHomModuleQ (M : Karoubi (Mat_ (Vc))) :
    Module (T ν)ᵐᵒᵖ ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) :=
  HomTensor.homModule _ ((clOpEquivQ hP hwf ν).trans
    (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (PD) (ν := ν)))) M

/-- `T^λ_ν` acts on `Hom(⊕ O_ν, M)` through the matrix ring. -/
theorem clHomModule_smulQ (M : Karoubi (Mat_ (Vc))) (z : (T ν)ᵐᵒᵖ)
    (f : (toKaroubi _).obj (downSum (PD) ν) ⟶ M) :
    (clHomModuleQ hP hwf ν M).smul z f =
      (downHomModule (Pin) (CL.CLScalars.t KL) ν M).smul (clOpEquivQ hP hwf ν z) f :=
  rfl

theorem clOpEquiv_appendBlackQ (z : (T ν)ᵐᵒᵖ) :
    blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν (clOpEquivQ hP hwf ν z) =
      clOpEquivQ hP hwf ({i} + ν) (appendBlackOp (clDownwardQ KL) Λ i ν z) := by
  rw [blackMatrixOp_apply]
  exact congrArg op (ordinaryToDownwardMatrix_appendBlack _ _ Λ (CL.CLScalars.t KL) i ν z.unop).symm

/-- `Hom(⊕ O_ν, M)` over `T^λ_ν` and over the all-down matrix ring, with the inductions along
`appendBlackOp` and along the matrix map of `Fᵢ` identified by the repaired Lemma 4.29. -/
def clIndTransportQ (M : Karoubi (Mat_ (Vc))) :
    letI := clHomModuleQ hP hwf ν M
    letI := downHomModule (Pin) (CL.CLScalars.t KL) ν M
    Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (clDownwardQ KL) Λ i ν) ≃+
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν) :=
  letI := clHomModuleQ hP hwf ν M
  letI := downHomModule (Pin) (CL.CLScalars.t KL) ν M
  Ind.transport (φ := appendBlackOp (clDownwardQ KL) Λ i ν)
    (φ' := blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν) (clOpEquivQ hP hwf ν)
    (clOpEquivQ hP hwf ({i} + ν)) (clOpEquiv_appendBlackQ hP hwf i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) ν) ⟶ M)) (clHomModule_smulQ hP hwf ν M)

theorem clIndTransport_smulQ (M : Karoubi (Mat_ (Vc))) (b : (T ({i} + ν))ᵐᵒᵖ)
    (x : letI := clHomModuleQ hP hwf ν M
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (clDownwardQ KL) Λ i ν)) :
    letI := clHomModuleQ hP hwf ν M
    letI := downHomModule (Pin) (CL.CLScalars.t KL) ν M
    clIndTransportQ hP hwf i ν M (b • x) =
      clOpEquivQ hP hwf ({i} + ν) b • clIndTransportQ hP hwf i ν M x := by
  let _ := clHomModuleQ hP hwf ν M
  let _ := downHomModule (Pin) (CL.CLScalars.t KL) ν M
  have key := Ind.transport_smul (φ := appendBlackOp (clDownwardQ KL) Λ i ν)
    (φ' := blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν) (clOpEquivQ hP hwf ν)
    (clOpEquivQ hP hwf ({i} + ν)) (clOpEquiv_appendBlackQ hP hwf i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) ν) ⟶ M)) (clHomModule_smulQ hP hwf ν M)
    b x
  exact key

/-- **Webster's `Fᵢ` is the categorical `Fᵢ`** (Webster, arXiv:1309.3796v3, §4.6,
paragraph after Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30), at the standard
Khovanov–Lauda parameters over a field: for `M` in the completed block of content `ν`,
Webster's `Fᵢ` applied to the right `T^λ_ν`-module `Hom(⊕ O_ν, M)` is
`Hom(⊕ O_{ν+i}, Fᵢ M)`, semilinearly for `T^λ_{ν+i}` (`clBlackHomInd_smulQ`). -/
def clBlackHomIndQ (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν) :
    letI := clHomModuleQ hP hwf ν M
    Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (clDownwardQ KL) Λ i ν) ≃+
      ((toKaroubi _).obj (downSum (PD) ({i} + ν)) ⟶ (completionMap F).obj M) :=
  letI := clHomModuleQ hP hwf ν M
  letI := downHomModule (Pin) (CL.CLScalars.t KL) ν M
  (clIndTransportQ hP hwf i ν M).trans (blackHomInd (Pin) (CL.CLScalars.t KL) i ν M hM)

theorem clBlackHomInd_smulQ (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν) (b : (T ({i} + ν))ᵐᵒᵖ)
    (x : letI := clHomModuleQ hP hwf ν M
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (clDownwardQ KL) Λ i ν)) :
    clBlackHomIndQ hP hwf i ν M hM (b • x) =
      (KLR.Diagram.MatEnd.karoubiMatrixOpY (downObj (PD) (ν := {i} + ν))
        (clOpEquivQ hP hwf ({i} + ν) b)).unop ≫ clBlackHomIndQ hP hwf i ν M hM x :=
  letI := clHomModuleQ hP hwf ν M
  letI := downHomModule (Pin) (CL.CLScalars.t KL) ν M
  (congrArg (blackHomInd (Pin) (CL.CLScalars.t KL) i ν M hM) (clIndTransport_smulQ hP hwf i ν M b x)).trans
    (blackHomInd_smul (Pin) (CL.CLScalars.t KL) i ν M hM _ _)

end CL

end Categorification.Stendhal
