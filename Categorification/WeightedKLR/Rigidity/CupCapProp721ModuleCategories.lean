/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721Packaged
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerivedDGMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDGMixed
import Categorification.WeightedKLR.RedStrands.BlackRouqData

/-!
# Proposition 7.21 on Mathlib's derived categories of modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Definition 7.18 and Proposition 7.21. The coevaluation functor `𝕂 = - ⊗ᴸ K`, its right adjoint
`RHom(K, -)` and the quantum trace `𝕋` are defined on the derived categories of dg modules of
`dg-lean` (`CupCap.coevaluationFunctor`, `CupCap.coevaluationRightAdjoint`,
`CupCap.quantumTraceFunctor`), while the categorical action of Theorem 4.31 on `D(T^λ)`
(`Stendhal.blackPresCL`) lives on Mathlib's derived categories of right modules, with the
blocks `Stendhal.derivedEOfEq` (restriction) and `Stendhal.derivedFOfEq` (induction) along
content equalities. This file transports the functors and the isomorphisms of Proposition 7.21
along the triangulated equivalences `DG.DegreeZero.derivedComparisonEquivalence`, so that they
are stated against these blocks.

## Main definitions

* `CupCap.transportFunctor E₁ E₂ F = E₁⁻¹ ⋙ F ⋙ E₂` and `CupCap.transportSquareIso`, which
  transports an isomorphism `A ⋙ B ≅ C ⋙ D` along comparison isomorphisms.
* `CupCap.moduleCoevaluationFunctor`, `CupCap.moduleCoevaluationRightAdjoint`,
  `CupCap.moduleQuantumTraceFunctor`, and the adjunction `CupCap.moduleCoevaluationAdjunction`.
* `CupCap.moduleCapEIso : 𝕂_β ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂_ν`, `CupCap.moduleCapFIso : 𝕂_ν ⋙ 𝔉⁺_i ≅
  𝔉_i ⋙ 𝕂_β`, and the analogues `CupCap.moduleCapERightAdjointIso`,
  `CupCap.moduleCapFRightAdjointIso`, `CupCap.moduleCapEQuantumTraceIso`,
  `CupCap.moduleCapFQuantumTraceIso`, for any content equalities `h : {i} + ν = β` and
  `hp : {i} + (ν + ν₀) = β + ν₀`; `𝔈`, `𝔉` are the blocks `derivedEOfEq`, `derivedFOfEq` of the
  weight-space functors of `blackRouqData` for the labels `λ` and `λ⁺ = plusLabels Λ Λc j hj`.

Route hypotheses (tracked), those of `CupCap.capEDerivedIso`: `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`; and `C`, `hRq : IsRouquierQ C Q` (Webster's setting for Theorem 4.31).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

/-! ### Transport along equivalences -/

section Transport

variable {𝒟₁ 𝒟₂ 𝒟₃ 𝒟₄ D₁ D₂ D₃ D₄ : Type*} [Category* 𝒟₁] [Category* 𝒟₂] [Category* 𝒟₃]
  [Category* 𝒟₄] [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]

/-- A functor `F : 𝒟₁ ⥤ 𝒟₂` transported along equivalences `E₁ : 𝒟₁ ≌ D₁`, `E₂ : 𝒟₂ ≌ D₂`:
`E₁⁻¹ ⋙ F ⋙ E₂`. -/
abbrev transportFunctor (E₁ : 𝒟₁ ≌ D₁) (E₂ : 𝒟₂ ≌ D₂) (F : 𝒟₁ ⥤ 𝒟₂) : D₁ ⥤ D₂ :=
  E₁.inverse ⋙ F ⋙ E₂.functor

/-- The comparison isomorphism `F ⋙ E₂ ≅ E₁ ⋙ transportFunctor E₁ E₂ F`. -/
def transportFunctorIso (E₁ : 𝒟₁ ≌ D₁) (E₂ : 𝒟₂ ≌ D₂) (F : 𝒟₁ ⥤ 𝒟₂) :
    F ⋙ E₂.functor ≅ E₁.functor ⋙ transportFunctor E₁ E₂ F :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E₁.unitIso _ ≪≫
    Functor.associator _ _ _

/-- **Transport of a commuting square along comparison isomorphisms**: from
`e : A ⋙ B ≅ C ⋙ D` and comparisons `A ⋙ E₂ ≅ E₁ ⋙ Ah` (and so on), with `E₁` an equivalence,
the isomorphism `Ah ⋙ Bh ≅ Ch ⋙ Dh`. -/
def transportSquareIso (E₁ : 𝒟₁ ≌ D₁) (E₂ : 𝒟₂ ≌ D₂) (E₃ : 𝒟₃ ≌ D₃) (E₄ : 𝒟₄ ≌ D₄)
    {A : 𝒟₁ ⥤ 𝒟₂} {B : 𝒟₂ ⥤ 𝒟₃} {C : 𝒟₁ ⥤ 𝒟₄} {D : 𝒟₄ ⥤ 𝒟₃} {Ah : D₁ ⥤ D₂}
    {Bh : D₂ ⥤ D₃} {Ch : D₁ ⥤ D₄} {Dh : D₄ ⥤ D₃} (cA : A ⋙ E₂.functor ≅ E₁.functor ⋙ Ah)
    (cB : B ⋙ E₃.functor ≅ E₂.functor ⋙ Bh) (cC : C ⋙ E₄.functor ≅ E₁.functor ⋙ Ch)
    (cD : D ⋙ E₃.functor ≅ E₄.functor ⋙ Dh) (e : A ⋙ B ≅ C ⋙ D) : Ah ⋙ Bh ≅ Ch ⋙ Dh :=
  (E₁.symm.congrLeft (E := D₃)).fullyFaithfulFunctor.preimageIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight cA.symm Bh ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft A cB.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e E₃.functor ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft C cD ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight cC Dh ≪≫
      Functor.associator _ _ _)

end Transport

/-! ### The functors on Mathlib's derived categories -/

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "EA" μ:max => derivedComparisonEquivalence.{0, 0} (TA μ)ᵐᵒᵖ
set_option hygiene false in
local notation "EP" μ:max => derivedComparisonEquivalence.{0, 0} (TPp μ)ᵐᵒᵖ
set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

variable [∀ β : Multiset I, DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ]
  [∀ β : Multiset I,
    DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) β)ᵐᵒᵖ]
  [∀ β : Multiset I, HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  [∀ β : Multiset I, HasDerivedCategory.{0}
    (ModuleCat.{0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) β)ᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀ L)

/-- **The coevaluation functor on Mathlib's derived categories** of right modules,
`D(T^λ_ν) ⥤ D(T^{λ⁺}_{ν + ν₀})` (Webster, arXiv:1309.3796v3, Definition 7.18): the transport
of `CupCap.coevaluationFunctor` along the comparison equivalences. -/
def moduleCoevaluationFunctor (ν : Multiset I) :
    DerivedCategory (ModuleCat.{0} (TA ν)ᵐᵒᵖ) ⥤ DerivedCategory (ModuleCat.{0} (TPp ν)ᵐᵒᵖ) :=
  transportFunctor (EA ν) (EP ν) (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)

/-- **The right adjoint `RHom(K, -)` on Mathlib's derived categories** of right modules: the
transport of `CupCap.coevaluationRightAdjoint`. -/
def moduleCoevaluationRightAdjoint (ν : Multiset I) :
    DerivedCategory (ModuleCat.{0} (TPp ν)ᵐᵒᵖ) ⥤ DerivedCategory (ModuleCat.{0} (TA ν)ᵐᵒᵖ) :=
  transportFunctor (EP ν) (EA ν) (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)

/-- **The quantum trace `𝕋` on Mathlib's derived categories** of right modules (Webster,
arXiv:1309.3796v3, Definition 7.18): the transport of `CupCap.quantumTraceFunctor`. -/
def moduleQuantumTraceFunctor (ν : Multiset I) (shift : ℤ) :
    DerivedCategory (ModuleCat.{0} (TPp ν)ᵐᵒᵖ) ⥤ DerivedCategory (ModuleCat.{0} (TA ν)ᵐᵒᵖ) :=
  transportFunctor (EP ν) (EA ν) (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)

/-- **The adjunction `𝕂 ⊣ RHom(K, -)` on Mathlib's derived categories**, transported from
`CupCap.coevaluationAdjunction`. -/
def moduleCoevaluationAdjunction (ν : Multiset I) :
    moduleCoevaluationFunctor k Q Λ Λc j hj ν₀ L ν ⊣
      moduleCoevaluationRightAdjoint k Q Λ Λc j hj ν₀ L ν :=
  ((EA ν).symm.toAdjunction.comp (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)).comp
    (EP ν).toAdjunction

/-- `𝕂` on dg modules, followed by the comparison, is the comparison followed by
`CupCap.moduleCoevaluationFunctor`. -/
def moduleCoevaluationComparisonIso (ν : Multiset I) :
    coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L ⋙ derivedComparison.{0, 0} (TPp ν)ᵐᵒᵖ ≅
      derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ ⋙ moduleCoevaluationFunctor k Q Λ Λc j hj ν₀ L ν :=
  transportFunctorIso (EA ν) (EP ν) _

/-! ### The isomorphisms of Proposition 7.21 -/

variable {k Q Λ Λc j hj ν₀ L}
variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  {C : QuantumGroup.CartanDatum I} (hRq : IsRouquierQ C Q)
  {ν β : Multiset I} {i : I}

/-- **`𝕂_β ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂_ν` on Mathlib's derived categories** (Webster, arXiv:1309.3796v3,
Proposition 7.21, the part for `𝔈_i`), for content equalities `h : {i} + ν = β` and
`hp : {i} + (ν + ν₀) = β + ν₀`, with `𝔈_i = derivedEOfEq` the blocks of the weight-space
functors of `blackRouqData` for `λ` and `λ⁺`: the transport of `CupCap.capEDerivedIso`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
def moduleCapEIso (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    moduleCoevaluationFunctor k Q Λ Λc j hj ν₀ L β ⋙
        derivedEOfEq Q (plusLabels Λ Λc j hj) i hp ≅
      derivedEOfEq Q Λ i h ⋙ moduleCoevaluationFunctor k Q Λ Λc j hj ν₀ L ν := by
  subst h
  have cA := moduleCoevaluationComparisonIso k Q Λ Λc j hj ν₀ L νᵢ
  have cB := derivedPlusEOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (rfl : νᵢ = _) hp
  have cC := derivedBlackEOfEqComparisonIso.{0, 0} Q Λ (rfl : νᵢ = _)
  have cD := moduleCoevaluationComparisonIso k Q Λ Λc j hj ν₀ L ν
  have e := capEDerivedIso (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
    ν i hL hQ hκ hP hPL hfin hproj
  exact transportSquareIso (EA νᵢ) (EP νᵢ) (EP ν) (EA ν) cA cB cC cD e

/-- **`𝕂_ν ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂_β` on Mathlib's derived categories** (Webster, arXiv:1309.3796v3,
Proposition 7.21, the part for `𝔉_i`), for content equalities `h : {i} + ν = β` and
`hp : {i} + (ν + ν₀) = β + ν₀`, with `𝔉_i = derivedFOfEq` the blocks of the weight-space
functors of `blackRouqData` for `λ` and `λ⁺`: the transport of `CupCap.capFDerivedIso`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` as in
Theorem 4.31. -/
def moduleCapFIso (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    moduleCoevaluationFunctor k Q Λ Λc j hj ν₀ L ν ⋙
        derivedFOfEq (plusLabels Λ Λc j hj) hRq i hp ≅
      derivedFOfEq Λ hRq i h ⋙ moduleCoevaluationFunctor k Q Λ Λc j hj ν₀ L β := by
  subst h
  haveI := blackFOfEq_preservesFiniteLimits Λ hRq i (rfl : νᵢ = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hRq i (rfl : νᵢ = _)
  haveI := blackFOfEq_preservesFiniteLimits (plusLabels Λ Λc j hj) hRq i hp
  haveI := blackFOfEq_preservesFiniteColimits (plusLabels Λ Λc j hj) hRq i hp
  have cA := moduleCoevaluationComparisonIso k Q Λ Λc j hj ν₀ L ν
  have cB := derivedPlusFOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (rfl : νᵢ = _) C hRq hp
  have cC := derivedBlackFOfEqComparisonIso.{0, 0} Q Λ (rfl : νᵢ = _) C hRq
  have cD := moduleCoevaluationComparisonIso k Q Λ Λc j hj ν₀ L νᵢ
  have e := capFDerivedIso (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
    ν i hL hQ hκ hP hPL hfin hproj C hRq
  exact transportSquareIso (EA ν) (EP ν) (EP νᵢ) (EA νᵢ) cA cB cC cD e

/-- `RHom(K, -)` on dg modules, followed by the comparison, is the comparison followed by
`CupCap.moduleCoevaluationRightAdjoint`. -/
def moduleCoevaluationRightAdjointComparisonIso (ν : Multiset I) :
    coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ⋙ derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ ≅
      derivedComparison.{0, 0} (TPp ν)ᵐᵒᵖ ⋙
        moduleCoevaluationRightAdjoint k Q Λ Λc j hj ν₀ L ν :=
  transportFunctorIso (EP ν) (EA ν) _

/-- `𝕋` on dg modules, followed by the comparison, is the comparison followed by
`CupCap.moduleQuantumTraceFunctor`. -/
def moduleQuantumTraceComparisonIso (ν : Multiset I) (shift : ℤ) :
    quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ⋙ derivedComparison.{0, 0} (TA ν)ᵐᵒᵖ ≅
      derivedComparison.{0, 0} (TPp ν)ᵐᵒᵖ ⋙
        moduleQuantumTraceFunctor k Q Λ Λc j hj ν₀ L ν shift :=
  transportFunctorIso (EP ν) (EA ν) _

/-- **`𝔈⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i` on Mathlib's derived categories** (Webster,
arXiv:1309.3796v3, proof of Proposition 7.21): the transport of `CupCap.capERightAdjointIso`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq`. -/
def moduleCapERightAdjointIso (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    derivedEOfEq Q (plusLabels Λ Λc j hj) i hp ⋙
        moduleCoevaluationRightAdjoint k Q Λ Λc j hj ν₀ L ν ≅
      moduleCoevaluationRightAdjoint k Q Λ Λc j hj ν₀ L β ⋙ derivedEOfEq Q Λ i h := by
  subst h
  have cA := derivedPlusEOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (rfl : νᵢ = _) hp
  have cB := moduleCoevaluationRightAdjointComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      ν
  have cC := moduleCoevaluationRightAdjointComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      (({i} : Multiset I) + ν)
  have cD := derivedBlackEOfEqComparisonIso.{0, 0} Q Λ (rfl : νᵢ = _)
  have e := capERightAdjointIso (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
    ν i hL hQ hκ hP hPL hfin hproj C hRq
  exact transportSquareIso (EP νᵢ) (EP ν) (EA ν) (EA νᵢ) cA cB cC cD e

/-- **`𝔉⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` on Mathlib's derived categories** (Webster,
arXiv:1309.3796v3, proof of Proposition 7.21): the transport of `CupCap.capFRightAdjointIso`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq`. -/
def moduleCapFRightAdjointIso (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    derivedFOfEq (plusLabels Λ Λc j hj) hRq i hp ⋙
        moduleCoevaluationRightAdjoint k Q Λ Λc j hj ν₀ L β ≅
      moduleCoevaluationRightAdjoint k Q Λ Λc j hj ν₀ L ν ⋙ derivedFOfEq Λ hRq i h := by
  subst h
  haveI := blackFOfEq_preservesFiniteLimits Λ hRq i (rfl : νᵢ = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hRq i (rfl : νᵢ = _)
  haveI := blackFOfEq_preservesFiniteLimits (plusLabels Λ Λc j hj) hRq i hp
  haveI := blackFOfEq_preservesFiniteColimits (plusLabels Λ Λc j hj) hRq i hp
  have cA := derivedPlusFOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (rfl : νᵢ = _) C hRq hp
  have cB := moduleCoevaluationRightAdjointComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      (({i} : Multiset I) + ν)
  have cC := moduleCoevaluationRightAdjointComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      ν
  have cD := derivedBlackFOfEqComparisonIso.{0, 0} Q Λ (rfl : νᵢ = _) C hRq
  have e := capFRightAdjointIso (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
    ν i hL hQ hκ hP hPL hfin hproj C hRq
  exact transportSquareIso (EP ν) (EP νᵢ) (EA νᵢ) (EA ν) cA cB cC cD e

/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` on Mathlib's derived categories** for the quantum trace with
homological shift `shift` (Webster, arXiv:1309.3796v3, Proposition 7.21): the transport of
`CupCap.capEQuantumTraceIso`. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`; `hRq`. -/
def moduleCapEQuantumTraceIso (shift : ℤ) (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    derivedEOfEq Q (plusLabels Λ Λc j hj) i hp ⋙
        moduleQuantumTraceFunctor k Q Λ Λc j hj ν₀ L ν shift ≅
      moduleQuantumTraceFunctor k Q Λ Λc j hj ν₀ L β shift ⋙ derivedEOfEq Q Λ i h := by
  subst h
  have cA := derivedPlusEOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (rfl : νᵢ = _) hp
  have cB := moduleQuantumTraceComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      ν shift
  have cC := moduleQuantumTraceComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      (({i} : Multiset I) + ν) shift
  have cD := derivedBlackEOfEqComparisonIso.{0, 0} Q Λ (rfl : νᵢ = _)
  have e := capEQuantumTraceIso (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
    ν i hL hQ hκ hP hPL hfin hproj C hRq shift
  exact transportSquareIso (EP νᵢ) (EP ν) (EA ν) (EA νᵢ) cA cB cC cD e

/-- **`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` on Mathlib's derived categories** for the quantum trace with
homological shift `shift` (Webster, arXiv:1309.3796v3, Proposition 7.21): the transport of
`CupCap.capFQuantumTraceIso`. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`; `hRq`. -/
def moduleCapFQuantumTraceIso (shift : ℤ) (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    derivedFOfEq (plusLabels Λ Λc j hj) hRq i hp ⋙
        moduleQuantumTraceFunctor k Q Λ Λc j hj ν₀ L β shift ≅
      moduleQuantumTraceFunctor k Q Λ Λc j hj ν₀ L ν shift ⋙ derivedFOfEq Λ hRq i h := by
  subst h
  haveI := blackFOfEq_preservesFiniteLimits Λ hRq i (rfl : νᵢ = _)
  haveI := blackFOfEq_preservesFiniteColimits Λ hRq i (rfl : νᵢ = _)
  haveI := blackFOfEq_preservesFiniteLimits (plusLabels Λ Λc j hj) hRq i hp
  haveI := blackFOfEq_preservesFiniteColimits (plusLabels Λ Λc j hj) hRq i hp
  have cA := derivedPlusFOfEqComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ (rfl : νᵢ = _) C hRq hp
  have cB := moduleQuantumTraceComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      (({i} : Multiset I) + ν) shift
  have cC := moduleQuantumTraceComparisonIso (k := k) (Q := Q) (Λ := Λ) (Λc := Λc)
      (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
      ν shift
  have cD := derivedBlackFOfEqComparisonIso.{0, 0} Q Λ (rfl : νᵢ = _) C hRq
  have e := capFQuantumTraceIso (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (L := L)
    ν i hL hQ hκ hP hPL hfin hproj C hRq shift
  exact transportSquareIso (EP ν) (EP νᵢ) (EA νᵢ) (EA ν) cA cB cC cD e

end Categorification.Stendhal.CupCap
