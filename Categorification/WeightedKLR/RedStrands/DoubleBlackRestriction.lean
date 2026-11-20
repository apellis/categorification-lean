/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackInduction
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction
import Categorification.Diagrams.KLR.MatEndCornerRes
import Categorification.Algebra.InductionAlongAssoc

/-!
# `Eᵢ` on the categorical side is Webster's `Eᵢ` on modules

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.31 and the paragraph after it. Webster defines
`Eᵢ` on right `T^λ_{ν+i}`-modules as the restriction along `appendBlackOp`, the right adjoint
of `Fᵢ`. On the categorical side, the upward black strand of colour `i` is right adjoint to
the downward one in the completed black action (`blackCompletedAdjunction`, the image of the
biadjunction of the Khovanov–Lauda 2-category). For `M` in the completed block of content
`ν + i`, `Hom(⊕ O_ν, Eᵢ M)` is the restriction of `Hom(⊕ O_{ν+i}, M)` along the matrix map of
`Fᵢ` (`DoubleDiagram.blackHomRes`), and along `appendBlackOp` through the repaired Lemma 4.29
(`clBlackHomRes`), semilinearly for the actions of the source rings. Unlike the induction side
this needs no generation hypothesis on `M`.
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
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (pres RD k).Rel,
      P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

omit [AddCommGroup Y] in
/-- A downward Khovanov–Lauda strand of colour `i` as a 1-morphism `ν ⟶ μ`, with `ν` the
weight to the left of `μ`. -/
def downStrandHom (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    (⟨ν⟩ : (pres RD k).Bicat) ⟶ ⟨μ⟩ :=
  ⟨⟨ν, [⟨dn i, μ⟩]⟩, rfl, by subst h; exact ⟨rfl, trivial⟩, rfl⟩

instance completionMap_blackAct_additive {μ ν : X} (s : List (Letter I)) (hs : wt RD μ s = ν) :
    (completionMap (blackAct P s hs)).Additive := by
  unfold completionMap
  infer_instance

/-- **The upward black strand is right adjoint to the downward one** in the completed black
action: the image of the biadjunction of the Khovanov–Lauda 2-category. -/
def blackCompletedAdjunction (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) :
    completionMap (blackAct P [(false, i)] h) ⊣ completionMap (blackAct P [(true, i)] h') :=
  Adjunction.ofCat ((blackActionCompleted P hP).mapAdjunction
    (RevBicat.adjunction ((biadjColour RD k (downStrandHom (k := k) i h) ⟨dn i, μ⟩ rfl).right)))

/-- The adjunction `Fᵢ ⊣ Eᵢ` on morphism groups, as an additive isomorphism. -/
def blackHomEquiv (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) (A : Karoubi (Mat_ (ViolatingCategory P μ)))
    (M : Karoubi (Mat_ (ViolatingCategory P ν))) :
    ((completionMap (blackAct P [(false, i)] h)).obj A ⟶ M) ≃+
      (A ⟶ (completionMap (blackAct P [(true, i)] h')).obj M) :=
  { (blackCompletedAdjunction P hP i h h').homEquiv A M with
    map_add' := fun f g => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_add,
        Preadditive.comp_add] }

theorem blackHomEquiv_apply (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) (A : Karoubi (Mat_ (ViolatingCategory P μ)))
    (M : Karoubi (Mat_ (ViolatingCategory P ν)))
    (f : (completionMap (blackAct P [(false, i)] h)).obj A ⟶ M) :
    blackHomEquiv P hP i h h' A M f = (blackCompletedAdjunction P hP i h h').homEquiv A M f :=
  rfl

end Adjunction

section Block

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- The weight equation of the word `Eᵢ` between the all-down weights. -/
theorem wt_upDownRightWeight (i : I) (ν : Multiset I) :
    wt RD (downRightWeight RD Λ ({i} + ν)) [(true, i)] = downRightWeight RD Λ ν := by
  simp only [wt_cons, wt_nil, sh, downRightWeight, Multiset.map_add, Multiset.map_singleton,
    Multiset.sum_add, Multiset.sum_singleton]
  change (1 : ℤ) • RD.iX i + _ = _
  abel

local notation "F" => blackAct (Q) [(false, i)] (wt_downRightWeight i ν)
local notation "E" => blackAct (Q) [(true, i)] (wt_upDownRightWeight i ν)
set_option quotPrecheck false in
local notation "Vc'" => ViolatingCategory (Q) (downRightWeight RD Λ ({i} + ν))


/-- **`Eᵢ` on the categorical side as a restriction** (Webster, arXiv:1309.3796v3, §4.6,
after Theorem 4.31): for `M` in the completed block of content `ν + i`, morphisms from the
all-down sum of content `ν` to `Eᵢ M` are the restriction of `Hom(⊕ O_{ν+i}, M)` along the
matrix map of `Fᵢ`. -/
def blackHomRes (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (M : Karoubi (Mat_ (Vc'))) :
    letI := downHomModule P t ({i} + ν) M
    Res (blackMatrixOp P t i ν) ((toKaroubi _).obj (downSum (Q) ({i} + ν)) ⟶ M) ≃+
      ((toKaroubi _).obj (downSum (Q) ν) ⟶ (completionMap E).obj M) :=
  letI := downHomModule P t ({i} + ν) M
  (KLR.Diagram.MatEnd.resEquivKaroubi F (appendDown_injective i) (blackAct_downObj (Q) i)
    M).trans (blackHomEquiv (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν) _ M)

/-- The restriction comparison is semilinear: the all-down matrix ring of content `ν` acts on
`Hom(⊕ O_ν, Eᵢ M)` by precomposition. -/
theorem blackHomRes_smul (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (M : Karoubi (Mat_ (Vc'))) (m : (downwardMatrix (Q) ν)ᵐᵒᵖ)
    (g : letI := downHomModule P t ({i} + ν) M
      Res (blackMatrixOp P t i ν) ((toKaroubi _).obj (downSum (Q) ({i} + ν)) ⟶ M)) :
    letI := downHomModule P t ({i} + ν) M
    (blackHomRes P t i ν hP M) (m • g) =
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := ν)) m).unop ≫
        (blackHomRes P t i ν hP M) g := by
  let _ := downHomModule P t ({i} + ν) M
  simp only [blackHomRes, AddEquiv.trans_apply]
  exact (congrArg (blackHomEquiv (Q) hP i (wt_downRightWeight i ν) (wt_upDownRightWeight i ν) _ M)
    (KLR.Diagram.MatEnd.resEquivKaroubi_smul F (appendDown_injective i)
      (blackAct_downObj (Q) i) M m g)).trans
    ((blackCompletedAdjunction (Q) hP i _ _).homEquiv_naturality_left _ _)

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
set_option quotPrecheck false in
local notation "Vc'" => ViolatingCategory (PD)
  (downRightWeight (RDc) (coordinateRedWeights Λ C) (({i} : Multiset I) + ν))
local notation "E" => blackAct (PD) [(true, i)] (wt_upDownRightWeight i ν)

/-- `Hom(⊕ O_{ν+i}, M)` restricted along `appendBlackOp` over `T^λ_ν` and along the matrix map
of `Fᵢ` over the all-down matrix ring, identified by the repaired Lemma 4.29. -/
def clResTransport (M : Karoubi (Mat_ (Vc'))) :
    letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    letI := downHomModule (Pin) (KL).t (({i} : Multiset I) + ν) M
    Res (appendBlackOp (CL.qCL KL) Λ i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) ≃+
      Res (blackMatrixOp (Pin) (KL).t i ν) ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) :=
  letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  letI := downHomModule (Pin) (KL).t (({i} : Multiset I) + ν) M
  Res.transport (clOpEquiv hstd hP hwf ν) (clOpEquiv hstd hP hwf (({i} : Multiset I) + ν))
    (clOpEquiv_appendBlack hstd hP hwf i ν)
    (AddEquiv.refl ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M))
    (clHomModule_smul hstd hP hwf (({i} : Multiset I) + ν) M)

/-- **Webster's `Eᵢ` is the categorical `Eᵢ`** (Webster, arXiv:1309.3796v3, §4.6,
paragraph after Theorem 4.31, with the repaired Lemma 4.29 and Theorem 4.30), at the standard
Khovanov–Lauda parameters over a field: for `M` in the completed block of content `ν + i`,
Webster's `Eᵢ`, the restriction along `appendBlackOp` of the right `T^λ_{ν+i}`-module
`Hom(⊕ O_{ν+i}, M)`, is `Hom(⊕ O_ν, Eᵢ M)`, semilinearly for `T^λ_ν`
(`clBlackHomRes_smul`). -/
def clBlackHomRes (M : Karoubi (Mat_ (Vc'))) :
    letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    Res (appendBlackOp (CL.qCL KL) Λ i ν)
        ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M) ≃+
      ((toKaroubi _).obj (downSum (PD) ν) ⟶ (completionMap E).obj M) :=
  letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  letI := downHomModule (Pin) (KL).t (({i} : Multiset I) + ν) M
  (clResTransport hstd hP hwf i ν M).trans
    (blackHomRes (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P) M)

/-- The comparison `clBlackHomRes` is semilinear along `clOpEquiv`. -/
theorem clBlackHomRes_smul (M : Karoubi (Mat_ (Vc'))) (z : (T ν)ᵐᵒᵖ)
    (g : letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
      Res (appendBlackOp (CL.qCL KL) Λ i ν) ((toKaroubi _).obj (downSum (PD) (({i} : Multiset I) + ν)) ⟶ M)) :
    letI := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
    (clBlackHomRes hstd hP hwf i ν M) (z • g) =
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (PD) (ν := ν))
          (clOpEquiv hstd hP hwf ν z)).unop ≫ (clBlackHomRes hstd hP hwf i ν M) g := by
  let _ := clHomModule hstd hP hwf (({i} : Multiset I) + ν) M
  let _ := downHomModule (Pin) (KL).t (({i} : Multiset I) + ν) M
  exact (congrArg (blackHomRes (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P) M)
    (Res.transport_smul _ _ _ _ _ z g)).trans
    (blackHomRes_smul (Pin) (KL).t i ν (clDownwardBlock_reflectedBlack P) M _ _)

end CL

end Categorification.Stendhal
