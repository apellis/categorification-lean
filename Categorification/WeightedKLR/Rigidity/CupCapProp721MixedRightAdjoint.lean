/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerivedDGMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDGMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AdjointTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFAdjoint

/-!
# Crossings of different colours on `RHom(K, -)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The functors `𝔈_i` and `𝔉_i` along a content equality `{i} + ν = β`
(`CupCap.derivedBlackEOfEq`, `CupCap.derivedBlackFOfEq`, and their `λ⁺` versions) are adjoint
(`CupCap.derivedBlackEFAdjunctionOfEq`, `CupCap.derivedPlusEFAdjunctionOfEq`), transported from
Theorem 4.31 (`CupCap.derivedBlackEFAdjunction`, `CupCap.derivedPlusEFAdjunction`).

The crossings of different colours on `𝔉_b 𝔉_a` and `𝔉⁺_b 𝔉⁺_a` are taken as the conjugates
(`CupCap.dgBlackFMixedCrossMate`, `CupCap.dgPlusFMixedCrossMate`) of the crossings
`CupCap.dgMixedCross`, `CupCap.dgPlusMixedCross` along the composite adjunctions. The conjugate
isomorphisms `𝔉_b 𝔉_a ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_b 𝔉_a` of the pasted isomorphisms
`CupCap.capEDerivedIsoPaste'` carry one crossing to the other
(`CupCap.capFRightAdjointIsoPaste'_mixedCross`, and its `j < ℓ` and `j = ℓ` cases).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIsoMid`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)

/-! ### Adjunctions along a content equality -/

section OfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

section Black

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]

/-- **`𝔈_i ⊣ 𝔉_i` along a content equality** `{i} + ν = β` (Webster, arXiv:1309.3796v3,
Theorem 4.31), `CupCap.derivedBlackEFAdjunction` transported along the equality. -/
def derivedBlackEFAdjunctionOfEq :
    derivedBlackEOfEq.{0} Q Λ h ⊣ derivedBlackFOfEq.{0} Q Λ h := by
  subst h
  exact derivedBlackEFAdjunction ν i C hRq

end Black

section Plus

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]
  [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp β)ᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀) in
/-- **`𝔈⁺_i ⊣ 𝔉⁺_i` along a content equality** `{i} + ν = β` (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the `λ⁺` side), `CupCap.derivedPlusEFAdjunction` transported along the
equality. -/
def derivedPlusEFAdjunctionOfEq :
    derivedPlusEOfEq.{0} k Q Λ Λc j hj ν₀ h ⊣ derivedPlusFOfEq.{0} k Q Λ Λc j hj ν₀ h := by
  subst h
  exact derivedPlusEFAdjunction ν i C hRq

end Plus

end OfEq

/-! ### The crossings of different colours on `𝔉_b 𝔉_a` -/

variable (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νab)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp νab)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νab)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The crossing of different colours on the dg derived `𝔉_b 𝔉_a`**: the conjugate, along
the composite adjunctions of `CupCap.derivedBlackEFAdjunction` and
`CupCap.derivedBlackEFAdjunctionOfEq`, of the crossing `CupCap.dgMixedCross` on `𝔈_a 𝔈_b`. -/
def dgBlackFMixedCrossMate (hQ : KLRSymm Q) :
    derivedBlackF.{0} Q Λ b ν ⋙
        derivedBlackFOfEq.{0} Q Λ (rfl : ({a} : Multiset I) + νb = νab) ⟶
      derivedBlackF.{0} Q Λ a ν ⋙ derivedBlackFOfEq.{0} Q Λ (mixedSwap ν a b) :=
  conjugateEquiv ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq).comp (derivedBlackEFAdjunction (Λ := Λ) ν b C hRq))
    ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq).comp
      (derivedBlackEFAdjunction (Λ := Λ) ν a C hRq))
    (dgMixedCross.{0, 0} ν a b hQ)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing of different colours on the dg derived `𝔉⁺_b 𝔉⁺_a`**: the conjugate, along
the composite adjunctions of `CupCap.derivedPlusEFAdjunction` and
`CupCap.derivedPlusEFAdjunctionOfEq`, of the crossing `CupCap.dgPlusMixedCross`. -/
def dgPlusFMixedCrossMate (hQ : KLRSymm Q) :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν b ⋙
        derivedPlusFOfEq.{0} k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) ⟶
      derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν a ⋙
        derivedPlusFOfEq.{0} k Q Λ Λc j hj ν₀ (mixedSwap ν a b) :=
  conjugateEquiv ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀
      (rfl : ({a} : Multiset I) + νb = νab) C hRq).comp (derivedPlusEFAdjunction ν b C hRq))
    ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq).comp
      (derivedPlusEFAdjunction ν a C hRq))
    (dgPlusMixedCross.{0, 0} k Q Λ Λc j hj ν₀ ν a b hQ)

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

/-- **`𝔉_b 𝔉_a ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_b 𝔉_a` carries the crossing of different colours
to the crossing, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21):
the conjugates of the pasted isomorphisms of `CupCap.capAppendDataMid` for the two orders of
appending carry `CupCap.dgPlusFMixedCrossMate` to `CupCap.dgBlackFMixedCrossMate`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIsoPaste'Mid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerRight (dgPlusFMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj νab ν₀ L) ≫
        (coevaluationRightAdjointCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq).comp
            (derivedBlackEFAdjunction (Λ := Λ) ν a C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq).comp
            (derivedPlusEFAdjunction ν a C hRq))
          (capEDerivedIsoPaste'.{0, 0} (mixedSwap ν a b)
            (capAppendDataMid (hL := hL) ν a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataMid (hL := hL) νa b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h))).hom =
      (coevaluationRightAdjointCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
            hRq).comp (derivedBlackEFAdjunction (Λ := Λ) ν b C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀
            (rfl : ({a} : Multiset I) + νb = νab) C hRq).comp (derivedPlusEFAdjunction ν b C hRq))
          (capEDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab)
            (capAppendDataMid (hL := hL) ν b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataMid (hL := hL) νb a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h))).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFMixedCrossMate ν a b C hRq hQ) :=
  rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capEDerivedIsoPaste'Mid_mixedCross.{0, 0} ν a b hL hQ hκ hP hPL hfin hproj h hab)

/-- **`𝔉_b 𝔉_a ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_b 𝔉_a` carries the crossing of different colours
to the crossing, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21),
for the pasted isomorphisms of `CupCap.capAppendDataTop`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIsoPaste'Top_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerRight (dgPlusFMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj νab ν₀ L) ≫
        (coevaluationRightAdjointCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq).comp
            (derivedBlackEFAdjunction (Λ := Λ) ν a C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq).comp
            (derivedPlusEFAdjunction ν a C hRq))
          (capEDerivedIsoPaste'.{0, 0} (mixedSwap ν a b)
            (capAppendDataTop (hL := hL) ν a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataTop (hL := hL) νa b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h))).hom =
      (coevaluationRightAdjointCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
            hRq).comp (derivedBlackEFAdjunction (Λ := Λ) ν b C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀
            (rfl : ({a} : Multiset I) + νb = νab) C hRq).comp (derivedPlusEFAdjunction ν b C hRq))
          (capEDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab)
            (capAppendDataTop (hL := hL) ν b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataTop (hL := hL) νb a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h))).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFMixedCrossMate ν a b C hRq hQ) :=
  rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capEDerivedIsoPaste'Top_mixedCross.{0, 0} ν a b hL hQ hκ hP hPL hfin hproj h hab)

end Cases

end Categorification.Stendhal.CupCap
