/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicBlackAction
import Categorification.WeightedKLR.RedStrands.DoubleBlackInduction
import Categorification.WeightedKLR.RedStrands.DoubleBlackRestriction
import Categorification.WeightedKLR.RedStrands.SingleRedInduction

/-!
# `Eᵢ` and `Fᵢ` on cyclotomic KLR modules

Webster, arXiv:1309.3796v2, §3, Theorem 3.17, at the standard Khovanov–Lauda black
parameters over a field. The Khovanov–Lauda 2-category acts on the categories of right
`R^λ_ν`-modules with `Fᵢ` the induction `N ↦ N ⊗_{R^λ_ν} e R^λ_{ν+i}` along the last-strand
inclusion `R^λ_ν → R^λ_{ν+i}` and `Eᵢ` the restriction along it.

The 2-functor is `clBlackAction` for one red strand (`clBlackAction_cyclotomic`): its value at
`λ - ν` is the completed block of `DT^λ_ν`, whose all-down boundaries `⊕ O_ν` have endomorphism
ring `R^λ_ν`. Here the categorical `Fᵢ` and `Eᵢ` are identified with induction and restriction
along the cyclotomic last-strand map, on the right `R^λ_ν`-modules `Hom(⊕ O_ν, M)` of the
Morita equivalence:

* `cycBlackHomInd`: `Hom(⊕ O_{ν+i}, Fᵢ M)` is the induction of `Hom(⊕ O_ν, M)`;
* `cycBlackHomRes`: `Hom(⊕ O_ν, Eᵢ M)` is the restriction of `Hom(⊕ O_{ν+i}, M)`;

both semilinearly for the cyclotomic algebras. They are obtained from the tensor product
versions `clBlackHomInd`, `clBlackHomRes` (Webster §4.6) by transport along the one-red
isomorphism `R^λ_ν ≅ T^λ_ν` of Theorem 4.18 (v3 Theorem 4.20, `SingleRed.cyclotomicEquiv`),
which intertwines the last-strand map with `appendBlack`
(`SingleRed.appendBlack_cyclotomicEquiv`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

variable {I : Type u} {Λ : Fin 1 → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => TensorProductAlgebra k (CL.qCL KL) Λ
local notation "R" => CycKLR k (CL.qCL KL) (fun j => (Polynomial.X : Polynomial k) ^ Λ 0 j)

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 :
      I ⊕ Fin 1 → ℤ) P)
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
set_option quotPrecheck false in
local notation "Vc'" => ViolatingCategory (PD)
  (downRightWeight (RDc) (coordinateRedWeights Λ C) (({i} : Multiset I) + ν))
local notation "F" => blackAct (PD) [(false, i)] (wt_downRightWeight i ν)
local notation "E" => blackAct (PD) [(true, i)] (wt_upDownRightWeight i ν)

/-- The opposite of the cyclotomic last-strand map `R^λ_ν → R^λ_{ν+i}`. -/
def cyclotomicLastOp : (R ν)ᵐᵒᵖ →ₙ+* (R (({i} : Multiset I) + ν))ᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom
    (KLRAlgebra.AbsentColour.cyclotomicLast (CL.qCL KL) i
      (fun j => (Polynomial.X : Polynomial k) ^ Λ 0 j) ν))

/-- The one-red isomorphism `R^λ_ν ≅ T^λ_ν` (Webster, Theorem 4.18) on opposite rings. -/
abbrev cycOpEquiv (ν : Multiset I) : (R ν)ᵐᵒᵖ ≃+* (T ν)ᵐᵒᵖ :=
  RingEquiv.op (SingleRed.cyclotomicEquiv (CL.qCL KL) Λ ν).toRingEquiv

theorem cycOpEquiv_cyclotomicLast (z : (R ν)ᵐᵒᵖ) :
    appendBlackOp (CL.qCL KL) Λ i ν (cycOpEquiv ν z) =
      cycOpEquiv (({i} : Multiset I) + ν) (cyclotomicLastOp i ν z) :=
  congrArg op (SingleRed.appendBlack_cyclotomicEquiv i ν (CL.qCL KL) Λ z.unop)

/-- The right `R^λ_ν`-module `Hom(⊕ O_ν, M)` of the Morita equivalence: `R^λ_ν` acts through
`R^λ_ν ≅ T^λ_ν` and the repaired Lemma 4.29. -/
abbrev cycHomModule (ν : Multiset I)
    (M : Karoubi (Mat_ (ViolatingCategory (PD) (downRightWeight (RDc) (coordinateRedWeights Λ C) ν)))) :
    Module (R ν)ᵐᵒᵖ ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) :=
  HomTensor.homModule _ ((cycOpEquiv ν).trans ((clOpEquiv hstd hP hwf ν).trans
    (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (PD) (ν := ν))))) M

theorem cycHomModule_smul (ν : Multiset I)
    (M : Karoubi (Mat_ (ViolatingCategory (PD) (downRightWeight (RDc) (coordinateRedWeights Λ C) ν))))
    (z : (R ν)ᵐᵒᵖ) (f : (toKaroubi _).obj (downSum (PD) ν) ⟶ M) :
    (cycHomModule hstd hP hwf ν M).smul z f =
      (clHomModule hstd hP hwf ν M).smul (cycOpEquiv ν z) f :=
  rfl

/-- `Hom(⊕ O_ν, M)` over `R^λ_ν` and over `T^λ_ν`, with the inductions along the last-strand
map and along `appendBlackOp` identified by the one-red isomorphism. -/
def cycIndTransport (M : Karoubi (Mat_ (Vc))) :
    letI := cycHomModule hstd hP hwf ν M
    letI := clHomModule hstd hP hwf ν M
    Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (cyclotomicLastOp i ν) ≃+
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (appendBlackOp (CL.qCL KL) Λ i ν) :=
  letI := cycHomModule hstd hP hwf ν M
  letI := clHomModule hstd hP hwf ν M
  Ind.transport (φ := cyclotomicLastOp i ν) (φ' := appendBlackOp (CL.qCL KL) Λ i ν)
    (cycOpEquiv ν) (cycOpEquiv (({i} : Multiset I) + ν)) (cycOpEquiv_cyclotomicLast i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) ν) ⟶ M)) (cycHomModule_smul hstd hP hwf ν M)

/-- **Webster, arXiv:1309.3796v2, Theorem 3.17, `Fᵢ`**, at the standard Khovanov–Lauda
parameters over a field: for one red strand of label `λ` and `M` in the completed block of
content `ν`, the induction of the right `R^λ_ν`-module `Hom(⊕ O_ν, M)` along the last-strand
map `R^λ_ν → R^λ_{ν+i}` is `Hom(⊕ O_{ν+i}, Fᵢ M)`, semilinearly for `R^λ_{ν+i}`
(`cycBlackHomInd_smul`). -/
def cycBlackHomInd (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν) :
    letI := cycHomModule hstd hP hwf ν M
    Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (cyclotomicLastOp i ν) ≃+
      ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ (completionMap F).obj M) :=
  letI := cycHomModule hstd hP hwf ν M
  letI := clHomModule hstd hP hwf ν M
  (cycIndTransport hstd hP hwf i ν M).trans (clBlackHomInd hstd hP hwf i ν M hM)

theorem cycBlackHomInd_smul (M : Karoubi (Mat_ (Vc)))
    (hM : ∀ j, (M.X.X j).as.val.signedContent = contentVector ν)
    (b : (R (({i} : Multiset I) + ν))ᵐᵒᵖ)
    (x : letI := cycHomModule hstd hP hwf ν M
      Ind ((toKaroubi _).obj (downSum (PD) ν) ⟶ M) (cyclotomicLastOp i ν)) :
    cycBlackHomInd hstd hP hwf i ν M hM (b • x) =
      (KLR.Diagram.MatEnd.karoubiMatrixOpY (downObj (PD) (ν := ({i} : Multiset I) + ν))
        (clOpEquiv hstd hP hwf (({i} : Multiset I) + ν)
          (cycOpEquiv (({i} : Multiset I) + ν) b))).unop ≫
        cycBlackHomInd hstd hP hwf i ν M hM x :=
  letI := cycHomModule hstd hP hwf ν M
  letI := clHomModule hstd hP hwf ν M
  (congrArg (clBlackHomInd hstd hP hwf i ν M hM)
    (Ind.transport_smul (φ := cyclotomicLastOp i ν) (φ' := appendBlackOp (CL.qCL KL) Λ i ν)
      (cycOpEquiv ν) (cycOpEquiv (({i} : Multiset I) + ν)) (cycOpEquiv_cyclotomicLast i ν)
      (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) ν) ⟶ M))
      (cycHomModule_smul hstd hP hwf ν M) b x)).trans
    (clBlackHomInd_smul hstd hP hwf i ν M hM _ _)

/-- `Hom(⊕ O_{ν+i}, M)` restricted along the last-strand map over `R^λ_ν` and along
`appendBlackOp` over `T^λ_ν`, identified by the one-red isomorphism. -/
def cycResTransport (M : Karoubi (Mat_ (Vc'))) :
    letI := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    Res (cyclotomicLastOp i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) ≃+
      Res (appendBlackOp (CL.qCL KL) Λ i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) :=
  letI := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  Res.transport (cycOpEquiv ν) (cycOpEquiv (({i} : Multiset I) + ν))
    (cycOpEquiv_cyclotomicLast i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M))
    (cycHomModule_smul hstd hP hwf (({i} : Multiset I) + ν) M)

/-- **Webster, arXiv:1309.3796v2, Theorem 3.17, `Eᵢ`**, at the standard Khovanov–Lauda
parameters over a field: for one red strand of label `λ` and `M` in the completed block of
content `ν + i`, the restriction of the right `R^λ_{ν+i}`-module `Hom(⊕ O_{ν+i}, M)` along the
last-strand map `R^λ_ν → R^λ_{ν+i}` is `Hom(⊕ O_ν, Eᵢ M)`, semilinearly for `R^λ_ν`
(`cycBlackHomRes_smul`). -/
def cycBlackHomRes (M : Karoubi (Mat_ (Vc'))) :
    letI := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    Res (cyclotomicLastOp i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) ≃+
      ((toKaroubi _).obj (downSum (PD) ν) ⟶ (completionMap E).obj M) :=
  letI := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  (cycResTransport hstd hP hwf i ν M).trans (clBlackHomRes hstd hP hwf i ν M)

theorem cycBlackHomRes_smul (M : Karoubi (Mat_ (Vc'))) (z : (R ν)ᵐᵒᵖ)
    (g : letI := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
      Res (cyclotomicLastOp i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M)) :
    letI := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    cycBlackHomRes hstd hP hwf i ν M (z • g) =
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (PD) (ν := ν))
          (clOpEquiv hstd hP hwf ν (cycOpEquiv ν z))).unop ≫
        cycBlackHomRes hstd hP hwf i ν M g := by
  let _ := cycHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  let _ := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  exact (congrArg (clBlackHomRes hstd hP hwf i ν M)
    (Res.transport_smul (cycOpEquiv ν) (cycOpEquiv (({i} : Multiset I) + ν))
      (cycOpEquiv_cyclotomicLast i ν)
      (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M))
      (cycHomModule_smul hstd hP hwf (({i} : Multiset I) + ν) M) z g)).trans
    (clBlackHomRes_smul hstd hP hwf i ν M _ _)

end Categorification.Stendhal
