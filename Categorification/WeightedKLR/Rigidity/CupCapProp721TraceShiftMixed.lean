/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721MixedCrossDegreewise

/-!
# `𝔉_b 𝔉_a 𝕋 ≅ 𝕋 𝔉_b 𝔉_a` and the crossing of different colours

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21, for the quantum trace `𝕋` of Definition 7.18 with its homological shift.
The functor `𝔈_i` along a content equality `h : {i} + ν = β` (`CupCap.derivedBlackEOfEq`)
carries the derived tensor shift transported along `h` (`CupCap.derivedBlackEOfEq_commShift`),
and `𝔉_i` along `h` the shift induced by `𝔈_i ⊣ 𝔉_i`
(`CupCap.derivedBlackFOfEqAdjointCommShift`), as in `CupCap.capFQuantumTraceShiftIso`. With
these, the conjugates of the pasted isomorphisms `CupCap.capEDerivedIsoPaste'` along the
composite adjunctions, followed by the shift, carry the crossing of different colours
`CupCap.dgPlusFMixedCrossMate` on `𝔉⁺_b 𝔉⁺_a` to `CupCap.dgBlackFMixedCrossMate` on `𝔉_b 𝔉_a`
(`CupCap.capFQuantumTraceShiftIsoMid_mixedCross`, `CupCap.capFQuantumTraceShiftIsoTop_mixedCross`),
for `a ≠ b`, since the crossing `CupCap.dgMixedCross` on `𝔈_a 𝔈_b` commutes with the derived
tensor shift (`dgMixedCross_commShift`).

## Main definitions

* `CupCap.derivedBlackFOfEqAdjointCommShift`.

## Main results

* `CupCap.derivedBlackEFAdjunctionOfEq_adjointCommShift`.
* `CupCap.dgBlackFMixedCrossMate_adjointCommShift`.
* `CupCap.capFQuantumTraceShiftIsoMid_mixedCross`, `CupCap.capFQuantumTraceShiftIsoTop_mixedCross`.

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

/-! ### Shifts along a content equality -/

section OfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]

variable (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The shift compatibility of `𝔉_i` along a content equality induced by `𝔈_i ⊣ 𝔉_i`**
(Theorem 4.31), from `CupCap.derivedBlackEOfEq_commShift`. -/
abbrev derivedBlackFOfEqAdjointCommShift : (derivedBlackFOfEq.{0} Q Λ h).CommShift ℤ :=
  (derivedBlackEFAdjunctionOfEq (Λ := Λ) h C hRq).rightAdjointCommShift ℤ

/-- With the induced shift compatibility, `𝔈_i ⊣ 𝔉_i` along a content equality commutes with
the shift. -/
theorem derivedBlackEFAdjunctionOfEq_adjointCommShift :
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) h C hRq
    (derivedBlackEFAdjunctionOfEq (Λ := Λ) h C hRq).CommShift ℤ :=
  (derivedBlackEFAdjunctionOfEq (Λ := Λ) h C hRq).commShift_of_leftAdjoint ℤ

end OfEq

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

/-- **The conjugate crossing of different colours on `𝔉_b 𝔉_a` commutes with the induced
shift** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `a ≠ b`, since the
crossing `CupCap.dgMixedCross` on `𝔈_a 𝔈_b` commutes with the derived tensor shift
(`dgMixedCross_commShift`). -/
theorem dgBlackFMixedCrossMate_adjointCommShift (hQ : KLRSymm Q) (hab : a ≠ b) :
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    NatTrans.CommShift (dgBlackFMixedCrossMate (Λ := Λ) ν a b C hRq hQ) ℤ := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν a C hRq
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν b C hRq
  let := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  let := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq
  have := derivedBlackEFAdjunction_adjointCommShift (Λ := Λ) ν a C hRq
  have := derivedBlackEFAdjunction_adjointCommShift (Λ := Λ) ν b C hRq
  have := derivedBlackEFAdjunctionOfEq_adjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  have := derivedBlackEFAdjunctionOfEq_adjointCommShift (Λ := Λ)
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  have := dgMixedCross_commShift (Q := Q) (Λ := Λ) (ν := ν) hQ hab
  exact conjugateEquiv_commShift ℤ _ _ _

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
  (shift : ℤ)

/-- **`𝔉⁺_b 𝔉⁺_a ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_b 𝔉_a` carries the crossing of different colours to the
crossing, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
quantum trace with homological shift `shift`: the conjugates of the pasted isomorphisms of
`CupCap.capAppendDataMid` for the two orders of appending, followed by the shift, carry
`CupCap.dgPlusFMixedCrossMate` to `CupCap.dgBlackFMixedCrossMate`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFQuantumTraceShiftIsoMid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    Functor.whiskerRight (dgPlusFMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj νab ν₀ L shift) ≫
        (quantumTraceCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq).comp
            (derivedBlackEFAdjunction (Λ := Λ) ν a C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq).comp
            (derivedPlusEFAdjunction ν a C hRq))
          (capEDerivedIsoPaste'.{0, 0} (mixedSwap ν a b)
            (capAppendDataMid (hL := hL) ν a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataMid (hL := hL) νa b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)) shift).hom =
      (quantumTraceCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
            hRq).comp (derivedBlackEFAdjunction (Λ := Λ) ν b C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀
            (rfl : ({a} : Multiset I) + νb = νab) C hRq).comp (derivedPlusEFAdjunction ν b C hRq))
          (capEDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab)
            (capAppendDataMid (hL := hL) ν b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataMid (hL := hL) νb a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)) shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFMixedCrossMate ν a b C hRq hQ) := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν a C hRq
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν b C hRq
  let := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  let := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackFMixedCrossMate_adjointCommShift (Λ := Λ) ν a b C hRq hQ hab)
    (capEDerivedIsoPaste'Mid_mixedCross.{0, 0} ν a b hL hQ hκ hP hPL hfin hproj h hab) shift

/-- **`𝔉⁺_b 𝔉⁺_a ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_b 𝔉_a` carries the crossing of different colours to the
crossing, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
pasted isomorphisms of `CupCap.capAppendDataTop` and the quantum trace with homological shift
`shift`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFQuantumTraceShiftIsoTop_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    Functor.whiskerRight (dgPlusFMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj νab ν₀ L shift) ≫
        (quantumTraceCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq).comp
            (derivedBlackEFAdjunction (Λ := Λ) ν a C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq).comp
            (derivedPlusEFAdjunction ν a C hRq))
          (capEDerivedIsoPaste'.{0, 0} (mixedSwap ν a b)
            (capAppendDataTop (hL := hL) ν a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataTop (hL := hL) νa b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)) shift).hom =
      (quantumTraceCommIso
          ((derivedBlackEFAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
            hRq).comp (derivedBlackEFAdjunction (Λ := Λ) ν b C hRq))
          ((derivedPlusEFAdjunctionOfEq k Q Λ Λc j hj ν₀
            (rfl : ({a} : Multiset I) + νb = νab) C hRq).comp (derivedPlusEFAdjunction ν b C hRq))
          (capEDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab)
            (capAppendDataTop (hL := hL) ν b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)
            (capAppendDataTop (hL := hL) νb a (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL
              hκ hQ hfin h)) shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFMixedCrossMate ν a b C hRq hQ) := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν a C hRq
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν b C hRq
  let := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  let := derivedBlackFOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackFMixedCrossMate_adjointCommShift (Λ := Λ) ν a b C hRq hQ hab)
    (capEDerivedIsoPaste'Top_mixedCross.{0, 0} ν a b hL hQ hκ hP hPL hfin hproj h hab) shift

end Cases

end Categorification.Stendhal.CupCap
