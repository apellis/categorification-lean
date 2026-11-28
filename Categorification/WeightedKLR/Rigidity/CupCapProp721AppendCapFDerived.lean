/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFData
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerived

/-!
# `𝕂 ∘ 𝔉_i ≅ 𝔉_i ∘ 𝕂` on derived categories

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`, on derived categories. On modules the isomorphism
`(M ⊗ e' T) ⊗ K_{{i} + ν} ≅ (M ⊗ K_ν) ⊗ e'⁺ T⁺` is `CupCap.capFOrdIso`. All functors involved
are exact: the tensor products with `K_ν` and `K_{{i} + ν}` because these bimodules are projective
as left modules (`projective_midCapBimodule`), and induction along appending a black strand, on
both sides, by Webster's Theorem 4.31 (`projective_blackCorner`). On the `λ⁺` side Theorem 4.31 is
applied to the labels `λ⁺` at the black weight `ν + ν₀` and transported along the identification
of the black weights `{i} + (ν + ν₀) = ({i} + ν) + ν₀` (`CupCap.projective_plusCorner`). Hence
the module isomorphism passes to Mathlib's derived categories of modules
(`CupCap.capFDerivedOrdIso`) and to the coevaluation functor `𝕂` of Definition 7.18
(`CupCap.capFDerivedIsoOfData`): `𝕂_ν ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂_{{i} + ν}`.

## Main definitions

* `CupCap.plusCornerEquiv`: the corner of appending a black strand in `T^{λ⁺}` at the two black
  weights.
* `CupCap.derivedPlusF`: `𝔉_i` on derived categories of right `T^{λ⁺}`-modules.
* `CupCap.derivedPlusFComparisonIso`: `derivedPlusF` is the derived functor of induction.
* `CupCap.capFDerivedOrdIso`, `CupCap.capFDerivedIsoOfData`.
* `CupCap.capFDerivedIsoMid`, `CupCap.capFDerivedIsoTop`: the two cases `j < ℓ` and `j = ℓ`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for the part for
`𝔈_i`. The exactness of `𝔉_i` uses `IsRouquierQ C Q` (Theorem 4.31), which is Webster's own
setting. The ground ring is a field, as in Webster's paper.
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "aB" => appendBlackOp Q (plusLabels Λ Λc j hj) i (ν + ν₀)
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

/-! ### Theorem 4.31 on the `λ⁺` side -/

variable (k Q Λ Λc j hj ν₀) in
/-- The corner of appending a black strand in `T^{λ⁺}`, at the black weights `{i} + (ν + ν₀)`
and `({i} + ν) + ν₀`. -/
def plusCornerEquiv : Corner aB ≃ₗ[TPpᵐᵒᵖᵐᵒᵖ] Corner aT where
  toFun := transportCorner (RingEquiv.refl _) (plusWeightOp k Q Λ Λc j hj ν ν₀ i)
    appendBlackTPAOp_eq
  invFun := transportCorner (RingEquiv.refl _).symm (plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm
    (transport_symm _ _ appendBlackTPAOp_eq)
  map_add' z z' := Subtype.ext (map_add (plusWeightOp k Q Λ Λc j hj ν ν₀ i) z.1 z'.1)
  map_smul' r z := transportCorner_op_smul (RingEquiv.refl _) _ appendBlackTPAOp_eq r.unop z
  left_inv z := Subtype.ext ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm_apply_apply z.1)
  right_inv z := Subtype.ext ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).apply_symm_apply z.1)

variable (k Q Λ Λc j hj ν₀) in
/-- **Webster's Theorem 4.31 on the `λ⁺` side**: the corner of appending a black strand in
`T^{λ⁺}` is a projective right `T^{λ⁺}_{ν + ν₀}`-module, for Rouquier polynomials over a
field. -/
theorem projective_plusCorner (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    Module.Projective TPpᵐᵒᵖᵐᵒᵖ (Corner aT) :=
  have := projective_blackCorner (Q := Q) (Λ := plusLabels Λ Λc j hj) i (ν + ν₀) C hQ
  Module.Projective.of_equiv (plusCornerEquiv k Q Λ Λc j hj ν₀ ν i)

private theorem blackF_additive_capF : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackF_additive_capF

/-! ### Mathlib's derived categories of modules -/

section ModuleDerived

variable [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

variable {ν i}

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on Mathlib's derived categories of right modules** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the derived functors of the two sides of
`CupCap.capFOrdIso`, for `K_ν` and `K_{{i} + ν}` projective as left modules and Rouquier
polynomials (Theorem 4.31). -/
def capFDerivedOrdIso (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (D : CapFData k Q Λ Λc j hj ν₀ L ν i) [Module.Projective TA CB]
    [Module.Projective TAᵢ CBᵢ] :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
    letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hQ
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    (blackF Q Λ i ν).mapDerivedCategory ⋙ (OrdKᵢ).mapDerivedCategory ≅
      (OrdK).mapDerivedCategory ⋙ (InductionAlong.functor.{0, 0} aT).mapDerivedCategory :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
  letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hQ
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ mapDerivedCategoryIsoOfIso (capFOrdIso D) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end ModuleDerived

/-! ### Derived categories of dg modules -/

section DGDerived

variable [DG.HasDerivedCategory.{w, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀ L)

/-- **`𝔉_i` on derived categories of right `T^{λ⁺}`-modules**, `N ↦ N ⊗ᴸ e'⁺ T^{λ⁺}`: the
derived tensor product with the corner of appending a black strand (`appendBlackTPAOp`) in the
opposite ring. -/
def derivedPlusF : DG.DerivedCategory.{w} TPpᵐᵒᵖ ⥤ DG.DerivedCategory.{w} TPpᵢᵐᵒᵖ :=
  derivedTensor.{w} TPpᵢᵐᵒᵖ TPpᵐᵒᵖ (Corner aT)

/-- **`derivedPlusF` is the derived functor of the exact induction functor**, for Rouquier
polynomials over a field (Theorem 4.31 on the `λ⁺` side, `CupCap.projective_plusCorner`). -/
def derivedPlusFComparisonIso (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hQ
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ⋙ derivedComparison.{w, w'} TPpᵢᵐᵒᵖ ≅
      derivedComparison.{w, w'} TPpᵐᵒᵖ ⋙ (InductionAlong.functor.{0, 0} aT).mapDerivedCategory :=
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hQ
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  derivedTensorComparisonIso.{w, w'} TPpᵢᵐᵒᵖ TPpᵐᵒᵖ (Corner aT) ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryIsoOfIso (indOrdIso aT))

variable {k Q Λ Λc j hj ν₀ L ν i}

/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` on derived categories** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21, the part for `𝔉_i`), for the coevaluation functor `𝕂` of Definition 7.18,
from the bimodule isomorphism `CupCap.CapFData`, the projectivity of `K_ν` and `K_{{i} + ν}` as
left modules, and Rouquier polynomials (Theorem 4.31). -/
def capFDerivedIsoOfData (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (D : CapFData k Q Λ Λc j hj ν₀ L ν i) [Module.Projective TA CB]
    [Module.Projective TAᵢ CBᵢ] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙
        derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackF.{w} Q Λ i ν ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hQ
  letI := blackF_preservesFiniteColimits Q Λ i ν C hQ
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hQ
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  ((Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} TPpᵢᵐᵒᵖ)).whiskeringRight
      _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedPlusFComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ ν i C hQ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (capFDerivedOrdIso.{w'} C hQ D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hQ).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L _).symm ≪≫
      (Functor.associator _ _ _).symm)

/-! ### The two cases -/

section Cases

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

variable (ν i)

/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` on derived categories for `j < ℓ`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21, the part for `𝔉_i`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capFDerivedIsoMid (h : j < ℓ) :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙ derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackF.{w} Q Λ i ν ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capFDerivedIsoOfData.{w, w'} C hRq
    (capFDataMid (hL := hL) (ν := ν) (i := i) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
      hPL hκ h)

/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` on derived categories for `j = ℓ`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21, the part for `𝔉_i`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capFDerivedIsoTop (h : ¬ j < ℓ) :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙ derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackF.{w} Q Λ i ν ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ)
    (ν := (Singleton.singleton i : Multiset I) + ν) hL hQ hκ hP hPL hfin hproj
  capFDerivedIsoOfData.{w, w'} C hRq
    (capFDataTop (hL := hL) (ν := ν) (i := i) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
      hPL hκ h)

end Cases

end DGDerived

end Categorification.Stendhal.CupCap
