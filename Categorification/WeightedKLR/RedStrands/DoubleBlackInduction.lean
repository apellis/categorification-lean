/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLMorita
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackComparison
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.Algebra.HomTensorInd
import Categorification.Algebra.InductionAlongTensor

/-!
# `Fᵢ` on the categorical side is Webster's `Fᵢ` on modules

Webster, arXiv:1309.3796v3, §5, Proposition 5.3 and §4.6. Under the Morita equivalence of
Theorem 4.30, an object `M` of the completed block of `DT^λ` corresponds to the right
`T^λ_ν`-module `Hom(⊕ O_ν, M)`, where `⊕ O_ν` is the sum of the all-down boundaries. The
categorical action of `Fᵢ` (appending a downward black strand of colour `i`) corresponds to
Webster's `Fᵢ`, the induction `N ↦ N ⊗_{T^λ_ν} e' T^λ_{ν+i}` along `appendBlackOp`:
`Hom(⊕ O_{ν+i}, Fᵢ M)` is the induction of `Hom(⊕ O_ν, M)`
(`DoubleDiagram.blackHomInd`, at the matrix ring of the all-down block, and
`clBlackHomInd`, at `T^λ` through the repaired Lemma 4.29). Both isomorphisms are semilinear
for the actions of the target rings.
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

/-- The right module `Hom(⊕ O_ν, M)` over the opposite of the all-down matrix ring. -/
abbrev downHomModule (M : Karoubi (Mat_ (Vc))) :
    Module (downwardMatrix (Q) ν)ᵐᵒᵖ ((toKaroubi _).obj (downSum (Q) ν) ⟶ M) :=
  HomTensor.homModule _ (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := ν))) M

/-- The matrix map of `Fᵢ` on opposite rings. -/
abbrev blackMatrixOp :
    (downwardMatrix (Q) ν)ᵐᵒᵖ →ₙ+* (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ :=
  KLR.Diagram.MatEnd.mapEmbOp F (appendDown_injective i) (blackAct_downObj (Q) i)

theorem blackMatrixOp_apply (f : (downwardMatrix (Q) ν)ᵐᵒᵖ) :
    blackMatrixOp P t i ν f = op (blackMatrix (Q) i f.unop) := rfl

/-- **`Fᵢ` on the categorical side as an induction** (Webster, arXiv:1309.3796v3, §5,
Proposition 5.3): for `M` in the completed block of content `ν`, morphisms from the all-down
sum to `Fᵢ M` are the induction of `Hom(⊕ O_ν, M)` along the matrix map of `Fᵢ`. -/
def blackHomInd (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν) :
    letI := downHomModule P t ν M
    Ind ((toKaroubi _).obj (downSum (Q) ν) ⟶ M) (blackMatrixOp P t i ν) ≃+
      ((toKaroubi _).obj (downSum (Q) ({i} + ν)) ⟶ (completionMap F).obj M) :=
  KLR.Diagram.MatEnd.indEquivKaroubi F (appendDown_injective i) (blackAct_downObj (Q) i)
    (karoubi_isGeneratedBy_downSum P ν t M hM).choose_spec.choose
    (karoubi_isGeneratedBy_downSum P ν t M hM).choose_spec.choose_spec.choose
    (karoubi_isGeneratedBy_downSum P ν t M hM).choose_spec.choose_spec.choose_spec

theorem blackHomInd_smul (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν)
    (b : (downwardMatrix (Q) ({i} + ν))ᵐᵒᵖ)
    (x : letI := downHomModule P t ν M
      Ind ((toKaroubi _).obj (downSum (Q) ν) ⟶ M) (blackMatrixOp P t i ν)) :
    blackHomInd P t i ν M hM (b • x) =
      (KLR.Diagram.MatEnd.karoubiMatrixOpY (downObj (Q) (ν := {i} + ν)) b).unop ≫
        blackHomInd P t i ν M hM x :=
  KLR.Diagram.MatEnd.indEquivKaroubi_smul _ _ _ _ _ _ b x

end Block

end DoubleDiagram

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => TensorProductAlgebra k (CL.qCL KL) Λ

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i : I) (ν : Multiset I)

local notation "Pin" => addDownRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C)
  (affineCoverQ (clDownwardQ KL) Λ) (signedCapKLPresentation (RDc)
    (redWeight (cyclotomicCoverWeightDatum Λ C)) P (clDownwardQ KL) Λ fun _ _ => 1)
local notation "PD" => addRedUpRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k
  (addMixedBlackRelations (RDc) (Subtype.val ∘ coordinateRedWeights Λ C) k
    (CL.CLScalars.t KL) (Pin))
local notation "Vc" => ViolatingCategory (PD)
  (downRightWeight (RDc) (coordinateRedWeights Λ C) ν)
local notation "F" => blackAct (PD) [(false, i)] (wt_downRightWeight i ν)

/-- The repaired Lemma 4.29 on opposite rings. -/
abbrev clOpEquiv (ν : Multiset I) : (T ν)ᵐᵒᵖ ≃+* (downwardMatrix (PD) ν)ᵐᵒᵖ :=
  RingEquiv.op (clToDownwardMatrixKLEquiv (ν := ν) hstd hP hwf).toRingEquiv

/-- The right `T^λ_ν`-module `Hom(⊕ O_ν, M)` of the Morita equivalence (Webster,
arXiv:1309.3796v3, Theorem 4.30): `T^λ_ν` acts through the repaired Lemma 4.29. -/
abbrev clHomModule (M : Karoubi (Mat_ (Vc))) :
    Module (T ν)ᵐᵒᵖ ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) :=
  HomTensor.homModule _ ((clOpEquiv hstd hP hwf ν).trans
    (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (PD) (ν := ν)))) M

/-- `T^λ_ν` acts on `Hom(⊕ O_ν, M)` through the matrix ring. -/
theorem clHomModule_smul (M : Karoubi (Mat_ (Vc))) (z : (T ν)ᵐᵒᵖ)
    (f : (toKaroubi _).obj (downSum (PD) ν) ⟶ M) :
    (clHomModule hstd hP hwf ν M).smul z f =
      (downHomModule (Pin) (KL).t ν M).smul (clOpEquiv hstd hP hwf ν z) f :=
  rfl

theorem clOpEquiv_appendBlack (z : (T ν)ᵐᵒᵖ) :
    blackMatrixOp (Pin) (KL).t i ν (clOpEquiv hstd hP hwf ν z) =
      clOpEquiv hstd hP hwf ({i} + ν) (appendBlackOp (CL.qCL KL) Λ i ν z) := by
  rw [blackMatrixOp_apply]
  exact congrArg op (clToDownwardMatrix_appendBlack _ Λ (KL).t i ν KL z.unop).symm

/-- `Hom(⊕ O_ν, M)` over `T^λ_ν` and over the all-down matrix ring, with the inductions along
`appendBlackOp` and along the matrix map of `Fᵢ` identified by the repaired Lemma 4.29. -/
def clIndTransport (M : Karoubi (Mat_ (Vc))) :
    letI := clHomModule hstd hP hwf ν M
    letI := downHomModule (Pin) (KL).t ν M
    Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (CL.qCL KL) Λ i ν) ≃+
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (blackMatrixOp (Pin) (KL).t i ν) :=
  letI := clHomModule hstd hP hwf ν M
  letI := downHomModule (Pin) (KL).t ν M
  Ind.transport (φ := appendBlackOp (CL.qCL KL) Λ i ν)
    (φ' := blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν) (clOpEquiv hstd hP hwf ν)
    (clOpEquiv hstd hP hwf ({i} + ν)) (clOpEquiv_appendBlack hstd hP hwf i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) ν) ⟶ M)) (clHomModule_smul hstd hP hwf ν M)

theorem clIndTransport_smul (M : Karoubi (Mat_ (Vc))) (b : (T ({i} + ν))ᵐᵒᵖ)
    (x : letI := clHomModule hstd hP hwf ν M
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (CL.qCL KL) Λ i ν)) :
    letI := clHomModule hstd hP hwf ν M
    letI := downHomModule (Pin) (KL).t ν M
    clIndTransport hstd hP hwf i ν M (b • x) =
      clOpEquiv hstd hP hwf ({i} + ν) b • clIndTransport hstd hP hwf i ν M x := by
  let _ := clHomModule hstd hP hwf ν M
  let _ := downHomModule (Pin) (KL).t ν M
  have key := Ind.transport_smul (φ := appendBlackOp (CL.qCL KL) Λ i ν)
    (φ' := blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν) (clOpEquiv hstd hP hwf ν)
    (clOpEquiv hstd hP hwf ({i} + ν)) (clOpEquiv_appendBlack hstd hP hwf i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) ν) ⟶ M)) (clHomModule_smul hstd hP hwf ν M)
    b x
  exact key

/-- **Webster's `Fᵢ` is the categorical `Fᵢ`** (Webster, arXiv:1309.3796v3, §5,
Proposition 5.3, with §4.6 and the repaired Lemma 4.29 and Theorem 4.30), at the standard
Khovanov–Lauda parameters over a field: for `M` in the completed block of content `ν`,
Webster's `Fᵢ` applied to the right `T^λ_ν`-module `Hom(⊕ O_ν, M)` is
`Hom(⊕ O_{ν+i}, Fᵢ M)`, semilinearly for `T^λ_{ν+i}` (`clBlackHomInd_smul`). -/
def clBlackHomInd (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν) :
    letI := clHomModule hstd hP hwf ν M
    Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (CL.qCL KL) Λ i ν) ≃+
      ((toKaroubi _).obj (downSum (PD) ({i} + ν)) ⟶ (completionMap F).obj M) :=
  letI := clHomModule hstd hP hwf ν M
  letI := downHomModule (Pin) (KL).t ν M
  (clIndTransport hstd hP hwf i ν M).trans (blackHomInd (Pin) (KL).t i ν M hM)

theorem clBlackHomInd_smul (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν) (b : (T ({i} + ν))ᵐᵒᵖ)
    (x : letI := clHomModule hstd hP hwf ν M
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (CL.qCL KL) Λ i ν)) :
    clBlackHomInd hstd hP hwf i ν M hM (b • x) =
      (KLR.Diagram.MatEnd.karoubiMatrixOpY (downObj (PD) (ν := {i} + ν))
        (clOpEquiv hstd hP hwf ({i} + ν) b)).unop ≫ clBlackHomInd hstd hP hwf i ν M hM x :=
  letI := clHomModule hstd hP hwf ν M
  letI := downHomModule (Pin) (KL).t ν M
  (congrArg (blackHomInd (Pin) (KL).t i ν M hM) (clIndTransport_smul hstd hP hwf i ν M b x)).trans
    (blackHomInd_smul (Pin) (KL).t i ν M hM _ _)

end CL

end Categorification.Stendhal
