/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedTopCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotTop
import Categorification.WeightedKLR.Rigidity.CupCapProp721DerivedSquare
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerived
import Categorification.WeightedKLR.RedStrands.BlackDerivedTwoMorphisms

/-!
# `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` and the 2-morphisms, on derived categories

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. On right modules, the isomorphisms `K ∘ 𝔈_i ≅ 𝔈_i ∘ K`
carry the dot to the dot (`CupCap.capEOrdIsoOfEqMid_dot`, `CupCap.capEOrdIsoOfEqTop_dot`), the
crossing of two strands of the same colour to the crossing (`CupCap.capECompIsoOfEqMid_cross`,
`CupCap.capECompIsoOfEqTop_cross`), and the crossing of two strands of different colours to the
crossing (`CupCap.capECompIsoOfEq'Mid_mixedCross`, `CupCap.capECompIsoOfEq'Top_mixedCross`).
All functors involved are exact when `K_ν` is projective as a left module, so these identities
pass to Mathlib's derived categories of right modules through `CupCap.derivedSquareIso_whisker`.

The derived 2-morphisms are the derived natural transformations of the module-level ones: the
dot is `derivedBlackDot`; on the composite `𝔈_i²` the crossing is stated on the derived functor
of the composite, which `Functor.mapDerivedCategoryCompIso` identifies with the composite of the
derived functors (as in `derivedBlackCross`).

## Main results

* `CupCap.capEDerivedIsoOfEqMid_dot`, `CupCap.capEDerivedIsoOfEqTop_dot`.
* `CupCap.capEDerivedCompIsoOfEqMid_cross`, `CupCap.capEDerivedCompIsoOfEqTop_cross`.
* `CupCap.capEDerivedCompIsoOfEq'Mid_mixedCross`, `CupCap.capEDerivedCompIsoOfEq'Top_mixedCross`.

Route hypotheses (tracked): `hR`-family (`MidKLRRel`, which follows from `midKLRRel hκ hP hPL`),
`hfin`, `hQ`, `hκ`, `hP`, `hPL`, as for the module-level statements, and the projectivity of the
cap bimodules as left modules, which `projective_midCapBimodule` derives from these and `hproj`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

section Exact

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) {μ β : Multiset I}
  (h : ({i} : Multiset I) + μ = β)

private theorem blackE_additive_capETwo (ν : Multiset I) : (blackE Q Λ' i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackEOfEq_additive_capETwo : (blackEOfEq Q Λ' i h).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)).Additive

private theorem blackEOfEq_limits_capETwo :
    Limits.PreservesFiniteLimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs (Limits.PreservesFiniteLimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

private theorem blackEOfEq_colimits_capETwo :
    Limits.PreservesFiniteColimits (blackEOfEq Q Λ' i h) :=
  inferInstanceAs
    (Limits.PreservesFiniteColimits (resFunctor.{0, 0} (appendBlackOpOfEq Q Λ' i h)))

end Exact

attribute [local instance] blackE_additive_capETwo blackEOfEq_additive_capETwo
  blackEOfEq_limits_capETwo blackEOfEq_colimits_capETwo

/-! ### The dot -/

section Dot

universe w

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0}
    (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
    (((Singleton.singleton i : Multiset I) + ν) + ν₀))ᵐᵒᵖ)]

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
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

/-- **`𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` carries the dot to the dot on derived categories, for `j < ℓ`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the derived form of
`CupCap.capEOrdIsoOfEqMid_dot`, for `K_ν` and `K_{{i} + ν}` projective as left modules.
Route hypotheses (tracked): `hR`, `hR'`, `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEDerivedIsoOfEqMid_dot [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]
    (h : j < ℓ) :
    Functor.whiskerRight (derivedBlackDot.{w} Q Λ i ν) (OrdK).mapDerivedCategory ≫
        (derivedSquareIso (capEOrdIsoOfEqMid ν i hR hR' hP hPL hκ hQ hfin h)).hom =
      (derivedSquareIso (capEOrdIsoOfEqMid ν i hR hR' hP hPL hκ hQ hfin h)).hom ≫
        Functor.whiskerLeft (OrdKᵢ).mapDerivedCategory
          (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory :=
  derivedSquareIso_whisker _ _ (capEOrdIsoOfEqMid_dot ν i hR hR' hP hPL hκ hQ hfin h)

/-- **`𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` carries the dot to the dot on derived categories, for `j = ℓ`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the derived form of
`CupCap.capEOrdIsoOfEqTop_dot`, for `K_ν` and `K_{{i} + ν}` projective as left modules.
Route hypotheses (tracked): `hR`, `hR'`, `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEDerivedIsoOfEqTop_dot [Module.Projective TA CB] [Module.Projective TAᵢ CBᵢ]
    (h : ¬ j < ℓ) :
    Functor.whiskerRight (derivedBlackDot.{w} Q Λ i ν) (OrdK).mapDerivedCategory ≫
        (derivedSquareIso (capEOrdIsoOfEqTop ν i hR hR' hP hPL hκ hQ hfin h)).hom =
      (derivedSquareIso (capEOrdIsoOfEqTop ν i hR hR' hP hPL hκ hQ hfin h)).hom ≫
        Functor.whiskerLeft (OrdKᵢ).mapDerivedCategory
          (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).mapDerivedCategory :=
  derivedSquareIso_whisker _ _ (capEOrdIsoOfEqTop_dot ν i hR hR' hP hPL hκ hQ hfin h)

end Dot

/-! ### The crossing of two strands of the same colour -/

section Cross

universe w

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hR'' : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ
    ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν)))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0}
    (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
    (((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν)) +
      ν₀))ᵐᵒᵖ)]

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢᵢ" => TensorProductAlgebra k Q Λ νᵢᵢ
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢᵢ + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢᵢ" => CapBimodule k Q Λ Λc j hj νᵢᵢ ν₀ L
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢᵢ" => ordTensor TPpᵢᵢᵐᵒᵖ TAᵢᵢᵐᵒᵖ (OpBimodule TAᵢᵢ CBᵢᵢ)

/-- **`𝕂 ∘ 𝔈_i² ≅ 𝔈_i² ∘ 𝕂` carries the crossing to the crossing on derived categories, for
`j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the derived form of
`CupCap.capECompIsoOfEqMid_cross`, for `K_ν` and `K_{{i} + ({i} + ν)}` projective as left
modules. Route hypotheses (tracked): `hR`, `hR'`, `hR''`, `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEDerivedCompIsoOfEqMid_cross [Module.Projective TA CB]
    [Module.Projective TAᵢᵢ CBᵢᵢ] (h : j < ℓ) :
    Functor.whiskerRight (blackCross Q Λ i ν).mapDerivedCategory (OrdK).mapDerivedCategory ≫
        (derivedSquareIso (capECompIsoOfEq (capAppendDataMid ν i hR hR' hP hPL hκ hQ hfin h)
          (capAppendDataMid νᵢ i hR' hR'' hP hPL hκ hQ hfin h))).hom =
      (derivedSquareIso (capECompIsoOfEq (capAppendDataMid ν i hR hR' hP hPL hκ hQ hfin h)
          (capAppendDataMid νᵢ i hR' hR'' hP hPL hκ hQ hfin h))).hom ≫
        Functor.whiskerLeft (OrdKᵢᵢ).mapDerivedCategory
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
            (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i)
            (plusWeight_assoc νᵢ ν₀ i)).mapDerivedCategory :=
  derivedSquareIso_whisker _ _ (capECompIsoOfEqMid_cross ν i hR hR' hR'' hP hPL hκ hQ hfin h)

/-- **`𝕂 ∘ 𝔈_i² ≅ 𝔈_i² ∘ 𝕂` carries the crossing to the crossing on derived categories, for
`j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the derived form of
`CupCap.capECompIsoOfEqTop_cross`, for `K_ν` and `K_{{i} + ({i} + ν)}` projective as left
modules. Route hypotheses (tracked): `hR`, `hR'`, `hR''`, `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEDerivedCompIsoOfEqTop_cross [Module.Projective TA CB]
    [Module.Projective TAᵢᵢ CBᵢᵢ] (h : ¬ j < ℓ) :
    Functor.whiskerRight (blackCross Q Λ i ν).mapDerivedCategory (OrdK).mapDerivedCategory ≫
        (derivedSquareIso (capECompIsoOfEq (capAppendDataTop ν i hR hR' hP hPL hκ hQ hfin h)
          (capAppendDataTop νᵢ i hR' hR'' hP hPL hκ hQ hfin h))).hom =
      (derivedSquareIso (capECompIsoOfEq (capAppendDataTop ν i hR hR' hP hPL hκ hQ hfin h)
          (capAppendDataTop νᵢ i hR' hR'' hP hPL hκ hQ hfin h))).hom ≫
        Functor.whiskerLeft (OrdKᵢᵢ).mapDerivedCategory
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
            (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i)
            (plusWeight_assoc νᵢ ν₀ i)).mapDerivedCategory :=
  derivedSquareIso_whisker _ _ (capECompIsoOfEqTop_cross ν i hR hR' hR'' hP hPL hκ hQ hfin h)

end Cross

/-! ### The crossing of two strands of different colours -/

section Mixed

universe w

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (a b : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hRa : MidKLRRel j hj Q Λ Λc ((Singleton.singleton a : Multiset I) + ν) ν₀ L hL)
  (hRb : MidKLRRel j hj Q Λ Λc ((Singleton.singleton b : Multiset I) + ν) ν₀ L hL)
  (hRab : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)) ν₀ L hL)
  (hRba : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ
    ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0}
    (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)]
  [HasDerivedCategory.{w} (ModuleCat.{0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
    (((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)) +
      ν₀))ᵐᵒᵖ)]

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
set_option hygiene false in
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))

/-- **`𝕂 ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ 𝕂` carries the crossing of different colours to the crossing
on derived categories, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21): the derived form of `CupCap.capECompIsoOfEq'Mid_mixedCross`, for `K_ν` and
`K_{{a} + ({b} + ν)}` projective as left modules. Route hypotheses (tracked): `hR`, `hRa`,
`hRb`, `hRab`, `hRba`, `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEDerivedCompIsoOfEq'Mid_mixedCross [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νab) (CB νab)] (h : j < ℓ) (hab : a ≠ b) :
    Functor.whiskerRight
        (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)).mapDerivedCategory
        (OrdK ν).mapDerivedCategory ≫
        (derivedSquareIso (capECompIsoOfEq' (capAppendDataMid ν b hR hRb hP hPL hκ hQ hfin h)
          (capAppendDataMid νb a hRb hRab hP hPL hκ hQ hfin h) rfl
          (plusWeight_assoc νb ν₀ a))).hom =
      (derivedSquareIso (capECompIsoOfEq' (capAppendDataMid ν a hR hRa hP hPL hκ hQ hfin h)
          (capAppendDataMid νa b hRa hRba hP hPL hκ hQ hfin h) (mixedSwap ν a b)
          (plusWeight_assoc_mixed_swap ν a b))).hom ≫
        Functor.whiskerLeft (OrdK νab).mapDerivedCategory
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b)).mapDerivedCategory :=
  derivedSquareIso_whisker _ _
    (capECompIsoOfEq'Mid_mixedCross ν a b hR hRa hRb hRab hRba hP hPL hκ hQ hfin h hab)


/-- **`𝕂 ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ 𝕂` carries the crossing of different colours to the crossing
on derived categories, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21): the derived form of `CupCap.capECompIsoOfEq'Top_mixedCross`, for `K_ν` and
`K_{{a} + ({b} + ν)}` projective as left modules. Route hypotheses (tracked): `hR`, `hRa`,
`hRb`, `hRab`, `hRba`, `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEDerivedCompIsoOfEq'Top_mixedCross [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA νab) (CB νab)] (h : ¬ j < ℓ) (hab : a ≠ b) :
    Functor.whiskerRight
        (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)).mapDerivedCategory
        (OrdK ν).mapDerivedCategory ≫
        (derivedSquareIso (capECompIsoOfEq' (capAppendDataTop ν b hR hRb hP hPL hκ hQ hfin h)
          (capAppendDataTop νb a hRb hRab hP hPL hκ hQ hfin h) rfl
          (plusWeight_assoc νb ν₀ a))).hom =
      (derivedSquareIso (capECompIsoOfEq' (capAppendDataTop ν a hR hRa hP hPL hκ hQ hfin h)
          (capAppendDataTop νa b hRa hRba hP hPL hκ hQ hfin h) (mixedSwap ν a b)
          (plusWeight_assoc_mixed_swap ν a b))).hom ≫
        Functor.whiskerLeft (OrdK νab).mapDerivedCategory
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b)).mapDerivedCategory :=
  derivedSquareIso_whisker _ _
    (capECompIsoOfEq'Top_mixedCross ν a b hR hRa hRb hRab hRba hP hPL hκ hQ hfin h hab)

end Mixed

end Categorification.Stendhal.CupCap
