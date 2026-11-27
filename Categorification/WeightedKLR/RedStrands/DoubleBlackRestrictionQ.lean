/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackRestriction
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackInductionQ
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction
import Categorification.Diagrams.KLR.MatEndCornerRes
import Categorification.Algebra.InductionAlongAssoc

/-!
# `Eᵢ` on the categorical side is Webster's `Eᵢ` on modules

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31 and the paragraph after it. Webster defines
`Eᵢ` on right `T^λ_{ν+i}`-modules as the restriction along `appendBlackOp`, the right adjoint
of `Fᵢ`. On the categorical side, the upward black strand of colour `i` is right adjoint to
the downward one in the completed black action (`blackCompletedAdjunctionQ`, the image of the
biadjunction of the Khovanov–Lauda 2-category). For `M` in the completed block of content
`ν + i`, `Hom(⊕ O_ν, Eᵢ M)` is the restriction of `Hom(⊕ O_{ν+i}, M)` along the matrix map of
`Fᵢ` (`DoubleDiagram.blackHomResQ`), and along `appendBlackOp` through the repaired Lemma 4.29
(`clBlackHomResQ`), semilinearly for the actions of the source rings. Unlike the induction side
this needs no generation hypothesis on `M`.

This is the version of `DoubleBlackRestriction` in which the black strands carry the relations of
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

section Adjunction

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)

omit [AddCommGroup Y] in
/-- A downward Khovanov–Lauda strand of colour `i` as a 1-morphism `ν ⟶ μ`, with `ν` the
weight to the left of `μ`. -/
def downStrandHomQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    (⟨ν⟩ : (KL3.Diagram.CLQ.pres RD k sc).Bicat) ⟶ ⟨μ⟩ :=
  ⟨⟨ν, [⟨dn i, μ⟩]⟩, rfl, by subst h; exact ⟨rfl, trivial⟩, rfl⟩

/-- **The upward black strand is right adjoint to the downward one** in the completed black
action: the image of the biadjunction of the Khovanov–Lauda 2-category. -/
def blackCompletedAdjunctionQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) :
    completionMap (blackAct P [(false, i)] h) ⊣ completionMap (blackAct P [(true, i)] h') :=
  Adjunction.ofCat ((blackActionCompletedQ sc P hP).mapAdjunction
    (RevBicat.adjunction ((KL3.Diagram.CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i h) ⟨dn i, μ⟩ rfl).right)))

/-- The adjunction `Fᵢ ⊣ Eᵢ` on morphism groups, as an additive isomorphism. -/
def blackHomEquivQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) (A : Karoubi (Mat_ (ViolatingCategory P μ)))
    (M : Karoubi (Mat_ (ViolatingCategory P ν))) :
    ((completionMap (blackAct P [(false, i)] h)).obj A ⟶ M) ≃+
      (A ⟶ (completionMap (blackAct P [(true, i)] h')).obj M) :=
  { (blackCompletedAdjunctionQ P hP i h h').homEquiv A M with
    map_add' := fun f g => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_add,
        Preadditive.comp_add] }

theorem blackHomEquiv_applyQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) (A : Karoubi (Mat_ (ViolatingCategory P μ)))
    (M : Karoubi (Mat_ (ViolatingCategory P ν)))
    (f : (completionMap (blackAct P [(false, i)] h)).obj A ⟶ M) :
    blackHomEquivQ P hP i h h' A M f = (blackCompletedAdjunctionQ P hP i h h').homEquiv A M f :=
  rfl

end Adjunction

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)
local notation "E" => blackAct (Q) [(true, i)] (wt_upDownRightWeight i ν)
set_option quotPrecheck false in
local notation "Vc'" => ViolatingCategory (Q) (downRightWeight RD Λ ({i} + ν))


/-- **`Eᵢ` on the categorical side as a restriction** (Webster, arXiv:1309.3796v3, §4.6,
after Theorem 4.31): for `M` in the completed block of content `ν + i`, morphisms from the
all-down sum of content `ν` to `Eᵢ M` are the restriction of `Hom(⊕ O_{ν+i}, M)` along the
matrix map of `Fᵢ`. -/
def blackHomResQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    (M : Karoubi (Mat_ (Vc'))) :
    letI := downHomModule P t ({i} + ν) M
    Res (blackMatrixOp P t i ν) ((toKaroubi _).obj (downSum (Q) ({i} + ν)) ⟶ M) ≃+
      ((toKaroubi _).obj (downSum (Q) ν) ⟶ (completionMap E).obj M) :=
  letI := downHomModule P t ({i} + ν) M
  (KLR.Diagram.MatEnd.resEquivKaroubi F (appendDown_injective i) (blackAct_downObj (Q) i)
    M).trans (blackHomEquivQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν) _ M)

/-- The restriction comparison is semilinear: the all-down matrix ring of content `ν` acts on
`Hom(⊕ O_ν, Eᵢ M)` by precomposition. -/
theorem blackHomRes_smulQ (hP : ∀ r : (KL3.Diagram.CLQ.pres RD k sc).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((KL3.Diagram.CLQ.pres RD k sc).rel r)) = 0)
    (M : Karoubi (Mat_ (Vc'))) (m : (downwardMatrix (Q) ν)ᵐᵒᵖ)
    (g : letI := downHomModule P t ({i} + ν) M
      Res (blackMatrixOp P t i ν) ((toKaroubi _).obj (downSum (Q) ({i} + ν)) ⟶ M)) :
    letI := downHomModule P t ({i} + ν) M
    (blackHomResQ P t i ν hP M) (m • g) =
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := ν)) m).unop ≫
        (blackHomResQ P t i ν hP M) g := by
  let _ := downHomModule P t ({i} + ν) M
  simp only [blackHomResQ, AddEquiv.trans_apply]
  exact (congrArg (blackHomEquivQ (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν) _ M)
    (KLR.Diagram.MatEnd.resEquivKaroubi_smul F (appendDown_injective i)
      (blackAct_downObj (Q) i) M m g)).trans
    ((blackCompletedAdjunctionQ (Q) hP i _ _).homEquiv_naturality_left _ _)

end Block

end DoubleDiagram

section CL

universe u w

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ
local notation "T" => TensorProductAlgebra k (Q) Λ

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
set_option quotPrecheck false in
local notation "Vc'" => ViolatingCategory (PD)
  (downRightWeight (RDc) (coordinateRedWeights Λ C) (({i} : Multiset I) + ν))
local notation "E" => blackAct (PD) [(true, i)] (wt_upDownRightWeight i ν)

/-- `Hom(⊕ O_{ν+i}, M)` restricted along `appendBlackOp` over `T^λ_ν` and along the matrix map
of `Fᵢ` over the all-down matrix ring, identified by the repaired Lemma 4.29. -/
def clResTransportQ (M : Karoubi (Mat_ (Vc'))) :
    letI := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
    letI := downHomModule (Pin) (CL.CLScalars.t KL) (({i} : Multiset I) + ν) M
    Res (appendBlackOp (Q) Λ i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) ≃+
      Res (blackMatrixOp (Pin) (CL.CLScalars.t KL) i ν) ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) :=
  letI := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
  letI := downHomModule (Pin) (CL.CLScalars.t KL) (({i} : Multiset I) + ν) M
  Res.transport (clOpEquivQ hP hwf ν) (clOpEquivQ hP hwf (({i} : Multiset I) + ν))
    (clOpEquiv_appendBlackQ hP hwf i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M))
    (clHomModule_smulQ hP hwf (({i} : Multiset I) + ν) M)

/-- **Webster's `Eᵢ` is the categorical `Eᵢ`** (Webster, arXiv:1309.3796v3, §4.6,
paragraph after Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30), at the standard
Khovanov–Lauda parameters over a field: for `M` in the completed block of content `ν + i`,
Webster's `Eᵢ`, the restriction along `appendBlackOp` of the right `T^λ_{ν+i}`-module
`Hom(⊕ O_{ν+i}, M)`, is `Hom(⊕ O_ν, Eᵢ M)`, semilinearly for `T^λ_ν`
(`clBlackHomRes_smulQ`). -/
def clBlackHomResQ (M : Karoubi (Mat_ (Vc'))) :
    letI := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
    Res (appendBlackOp (Q) Λ i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) ≃+
      ((toKaroubi _).obj (downSum (PD) ν) ⟶ (completionMap E).obj M) :=
  letI := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
  letI := downHomModule (Pin) (CL.CLScalars.t KL) (({i} : Multiset I) + ν) M
  (clResTransportQ hP hwf i ν M).trans
    (blackHomResQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) M)

/-- The comparison `clBlackHomResQ` is semilinear along `clOpEquivQ`. -/
theorem clBlackHomRes_smulQ (M : Karoubi (Mat_ (Vc'))) (z : (T ν)ᵐᵒᵖ)
    (g : letI := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
      Res (appendBlackOp (Q) Λ i ν) ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M)) :
    letI := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
    (clBlackHomResQ hP hwf i ν M) (z • g) =
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (PD) (ν := ν))
          (clOpEquivQ hP hwf ν z)).unop ≫ (clBlackHomResQ hP hwf i ν M) g := by
  let _ := clHomModuleQ hP hwf (({i} : Multiset I) + ν) M
  let _ := downHomModule (Pin) (CL.CLScalars.t KL) (({i} : Multiset I) + ν) M
  exact (congrArg (blackHomResQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) M)
    (Res.transport_smul _ _ _ _ _ z g)).trans
    (blackHomRes_smulQ (Pin) (CL.CLScalars.t KL) i ν (clDownwardBlockQ_reflectedBlack P) M _ _)

end CL

end Categorification.Stendhal
