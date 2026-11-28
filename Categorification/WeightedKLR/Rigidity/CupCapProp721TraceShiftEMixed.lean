/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721FMixedCrossDegreewise
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftMixed

/-!
# `𝔈_a 𝔈_b 𝕋 ≅ 𝕋 𝔈_a 𝔈_b` and the crossing of different colours

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21, for the quantum trace `𝕋` of Definition 7.18 with its homological shift.
This is the `𝔈` counterpart of `CupCap.capFQuantumTraceShiftIsoMid_mixedCross`. The functors
`𝔉_i` and `𝔈_i` along a content equality `h : {i} + ν = β` are adjoint, `𝔉_i ⊣ 𝔈_i`
(`CupCap.derivedBlackFEAdjunctionOfEq`, `CupCap.derivedPlusFEAdjunctionOfEq`, transported from
Theorem 4.31), `𝔉_i` along `h` carries the derived tensor shift transported along `h`
(`CupCap.derivedBlackFOfEq_commShift`) and `𝔈_i` along `h` the shift induced by the adjunction
(`CupCap.derivedBlackEOfEqAdjointCommShift`), as in `CupCap.capEQuantumTraceShiftIso`.

The crossings of different colours on `𝔈_a 𝔈_b` and `𝔈⁺_a 𝔈⁺_b` are taken as the conjugates
(`CupCap.dgBlackEMixedCrossMate`, `CupCap.dgPlusEMixedCrossMate`) of the crossings
`CupCap.dgBlackFMixedCross`, `CupCap.dgPlusFMixedCross` on `𝔉_a 𝔉_b`, `𝔉⁺_a 𝔉⁺_b` along the
composite adjunctions. The conjugates of the pasted isomorphisms `CupCap.capFDerivedIsoPaste'`
along the composite adjunctions, followed by the shift, carry one crossing to the other
(`CupCap.capEQuantumTraceShiftIsoMid_mixedCross`, `CupCap.capEQuantumTraceShiftIsoTop_mixedCross`),
for `a ≠ b`, since `CupCap.dgBlackFMixedCross` commutes with the derived tensor shift
(`Stendhal.dgBlackFMixedCross_commShift`).

## Main definitions

* `CupCap.derivedBlackFEAdjunctionOfEq`, `CupCap.derivedPlusFEAdjunctionOfEq`.
* `CupCap.derivedBlackEOfEqAdjointCommShift`.
* `CupCap.dgBlackEMixedCrossMate`, `CupCap.dgPlusEMixedCrossMate`.

## Main results

* `CupCap.derivedBlackFEAdjunctionOfEq_adjointCommShift`.
* `CupCap.dgBlackEMixedCrossMate_adjointCommShift`.
* `CupCap.capEQuantumTraceShiftIsoMid_mixedCross`, `CupCap.capEQuantumTraceShiftIsoTop_mixedCross`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capFDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
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
set_option hygiene false in
local notation "aT" μ:max i':max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i'

/-! ### `𝔉_i ⊣ 𝔈_i` along a content equality -/

section OfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

section Black

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]

/-- **`𝔉_i ⊣ 𝔈_i` along a content equality** `{i} + ν = β` (Webster, arXiv:1309.3796v3,
Theorem 4.31), `CupCap.derivedBlackFEAdjunction` transported along the equality. -/
def derivedBlackFEAdjunctionOfEq :
    derivedBlackFOfEq.{0} Q Λ h ⊣ derivedBlackEOfEq.{0} Q Λ h := by
  subst h
  exact derivedBlackFEAdjunction ν i C hRq

/-- **The shift compatibility of `𝔈_i` along a content equality induced by `𝔉_i ⊣ 𝔈_i`**
(Theorem 4.31), from `CupCap.derivedBlackFOfEq_commShift`. -/
abbrev derivedBlackEOfEqAdjointCommShift : (derivedBlackEOfEq.{0} Q Λ h).CommShift ℤ :=
  (derivedBlackFEAdjunctionOfEq (Λ := Λ) h C hRq).rightAdjointCommShift ℤ

/-- With the induced shift compatibility, `𝔉_i ⊣ 𝔈_i` along a content equality commutes with
the shift. -/
theorem derivedBlackFEAdjunctionOfEq_adjointCommShift :
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) h C hRq
    (derivedBlackFEAdjunctionOfEq (Λ := Λ) h C hRq).CommShift ℤ :=
  (derivedBlackFEAdjunctionOfEq (Λ := Λ) h C hRq).commShift_of_leftAdjoint ℤ

end Black

section Plus

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]
  [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp β)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp β)ᵐᵒᵖ)]

variable (k Q Λ Λc j hj ν₀) in
/-- **`𝔉⁺_i ⊣ 𝔈⁺_i` along a content equality** `{i} + ν = β` (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the `λ⁺` side), `CupCap.derivedPlusFEAdjunction` transported along the
equality. -/
def derivedPlusFEAdjunctionOfEq :
    derivedPlusFOfEq.{0} k Q Λ Λc j hj ν₀ h ⊣ derivedPlusEOfEq.{0} k Q Λ Λc j hj ν₀ h := by
  subst h
  exact derivedPlusFEAdjunction ν i C hRq

end Plus

end OfEq

/-! ### The crossings of different colours on `𝔈_a 𝔈_b` -/

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

/-- **The crossing of different colours on the dg derived `𝔈_a 𝔈_b`**: the conjugate, along
the composite adjunctions of `CupCap.derivedBlackFEAdjunction` and
`CupCap.derivedBlackFEAdjunctionOfEq`, of the crossing `CupCap.dgBlackFMixedCross` on
`𝔉_a 𝔉_b`. -/
def dgBlackEMixedCrossMate (hQ : KLRSymm Q) :
    derivedBlackEOfEq.{0} Q Λ (mixedSwap ν a b) ⋙ derivedBlackE.{0} Q Λ a ν ⟶
      derivedBlackEOfEq.{0} Q Λ (rfl : ({a} : Multiset I) + νb = νab) ⋙
        derivedBlackE.{0} Q Λ b ν :=
  letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
  letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  conjugateEquiv ((derivedBlackFEAdjunction (Λ := Λ) ν a C hRq).comp
      (derivedBlackFEAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq))
    ((derivedBlackFEAdjunction (Λ := Λ) ν b C hRq).comp
      (derivedBlackFEAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq))
    (dgBlackFMixedCross.{0, 0} ν a b C hRq hQ)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing of different colours on the dg derived `𝔈⁺_a 𝔈⁺_b`**: the conjugate, along
the composite adjunctions of `CupCap.derivedPlusFEAdjunction` and
`CupCap.derivedPlusFEAdjunctionOfEq`, of the crossing `CupCap.dgPlusFMixedCross`. -/
def dgPlusEMixedCrossMate (hQ : KLRSymm Q) :
    derivedPlusEOfEq.{0} k Q Λ Λc j hj ν₀ (mixedSwap ν a b) ⋙
        derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν a ⟶
      derivedPlusEOfEq.{0} k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) ⋙
        derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν b :=
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
    (plusWeight_assoc ν ν₀ a) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
    (plusWeight_assoc ν ν₀ a) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
    (plusWeight_assoc ν ν₀ b) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
    (plusWeight_assoc ν ν₀ b) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
    (plusWeight_assoc νb ν₀ a) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
    (plusWeight_assoc νb ν₀ a) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
    (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
    (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
  conjugateEquiv ((derivedPlusFEAdjunction ν a C hRq).comp
      (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq))
    ((derivedPlusFEAdjunction ν b C hRq).comp
      (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) C hRq))
    (dgPlusFMixedCross.{0, 0} k Q Λ Λc j hj ν₀ ν a b C hRq hQ)

/-- **The conjugate crossing of different colours on `𝔈_a 𝔈_b` commutes with the induced
shift** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `a ≠ b`, since the
crossing `CupCap.dgBlackFMixedCross` on `𝔉_a 𝔉_b` commutes with the derived tensor shift
(`Stendhal.dgBlackFMixedCross_commShift`). -/
theorem dgBlackEMixedCrossMate_adjointCommShift (hQ : KLRSymm Q) (hab : a ≠ b) :
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    NatTrans.CommShift (dgBlackEMixedCrossMate (Λ := Λ) ν a b C hRq hQ) ℤ := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
  let := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  let := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq
  have := derivedBlackFEAdjunction_adjointCommShift (Λ := Λ) ν a C hRq
  have := derivedBlackFEAdjunction_adjointCommShift (Λ := Λ) ν b C hRq
  have := derivedBlackFEAdjunctionOfEq_adjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  have := derivedBlackFEAdjunctionOfEq_adjointCommShift (Λ := Λ)
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  have := blackF_preservesFiniteLimits Q Λ a ν C hRq
  have := blackF_preservesFiniteColimits Q Λ a ν C hRq
  have := blackF_preservesFiniteLimits Q Λ b ν C hRq
  have := blackF_preservesFiniteColimits Q Λ b ν C hRq
  have := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  have := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a
    (rfl : ({a} : Multiset I) + νb = νab) C hRq
  have := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
  have := dgBlackFMixedCross_commShift (Q := Q) (Λ := Λ) (ν := ν) C hRq hQ hab
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

/-- **`𝔈⁺_a 𝔈⁺_b ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_a 𝔈_b` carries the crossing of different colours to the
crossing, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for
the quantum trace with homological shift `shift`: the conjugates of the pasted isomorphisms of
`CupCap.capFDataMid` for the two orders of appending, followed by the shift, carry
`CupCap.dgPlusEMixedCrossMate` to `CupCap.dgBlackEMixedCrossMate`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIsoMid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
    letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν a C hRq
    letI := functor_preservesFiniteLimits (aT ν a)
    letI := functor_preservesFiniteColimits (aT ν a)
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν b C hRq
    letI := functor_preservesFiniteLimits (aT ν b)
    letI := functor_preservesFiniteColimits (aT ν b)
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    Functor.whiskerRight (dgPlusEMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν b C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          ((derivedPlusFEAdjunction ν b C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          (capFDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab) C hRq
            (capFDataMid (hL := hL) (ν := ν) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataMid (hL := hL) (ν := νb) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom =
      (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν a C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq))
          ((derivedPlusFEAdjunction ν a C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq))
          (capFDerivedIsoPaste'.{0, 0} (mixedSwap ν a b) C hRq
            (capFDataMid (hL := hL) (ν := ν) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataMid (hL := hL) (ν := νa) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νab ν₀ L shift)
          (dgBlackEMixedCrossMate ν a b C hRq hQ) := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
  let := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  let := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackEMixedCrossMate_adjointCommShift (Λ := Λ) ν a b C hRq hQ hab)
    (capFDerivedIsoPaste'Mid_mixedCross.{0, 0} hL hQ hκ hP hPL hfin hproj C hRq ν a b h hab)
    shift

/-- **`𝔈⁺_a 𝔈⁺_b ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_a 𝔈_b` carries the crossing of different colours to the
crossing, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for
the quantum trace with homological shift `shift`: the conjugates of the pasted isomorphisms of
`CupCap.capFDataTop` for the two orders of appending, followed by the shift, carry
`CupCap.dgPlusEMixedCrossMate` to `CupCap.dgBlackEMixedCrossMate`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIsoTop_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    letI := blackF_preservesFiniteLimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ a ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ b ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ b ν C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ a (rfl : ({a} : Multiset I) + νb
      = νab) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q Λ b (mixedSwap ν a b) C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν a C hRq
    letI := functor_preservesFiniteLimits (aT ν a)
    letI := functor_preservesFiniteColimits (aT ν a)
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν b C hRq
    letI := functor_preservesFiniteLimits (aT ν b)
    letI := functor_preservesFiniteColimits (aT ν b)
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc ν ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc ν ν₀ b) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) a
      (plusWeight_assoc νb ν₀ a) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) b
      (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b) C hRq
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νa) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νb) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νab) hL hQ hκ hP hPL
      hfin hproj
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
    letI := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
      hRq
    Functor.whiskerRight (dgPlusEMixedCrossMate k Q Λ Λc j hj ν₀ ν a b C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν b C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          ((derivedPlusFEAdjunction ν b C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) C
              hRq))
          (capFDerivedIsoPaste'.{0, 0} (rfl : ({a} : Multiset I) + νb = νab) C hRq
            (capFDataTop (hL := hL) (ν := ν) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataTop (hL := hL) (ν := νb) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom =
      (quantumTraceCommIso
          ((derivedBlackFEAdjunction (Λ := Λ) ν a C hRq).comp
            (derivedBlackFEAdjunctionOfEq (Λ := Λ) (mixedSwap ν a b) C hRq))
          ((derivedPlusFEAdjunction ν a C hRq).comp
            (derivedPlusFEAdjunctionOfEq k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq))
          (capFDerivedIsoPaste'.{0, 0} (mixedSwap ν a b) C hRq
            (capFDataTop (hL := hL) (ν := ν) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
              hPL hκ h)
            (capFDataTop (hL := hL) (ν := νa) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL)
              hP hPL hκ h)) shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νab ν₀ L shift)
          (dgBlackEMixedCrossMate ν a b C hRq hQ) := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν a C hRq
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν b C hRq
  let := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (mixedSwap ν a b) C hRq
  let := derivedBlackEOfEqAdjointCommShift (Λ := Λ) (rfl : ({a} : Multiset I) + νb = νab) C hRq
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackEMixedCrossMate_adjointCommShift (Λ := Λ) ν a b C hRq hQ hab)
    (capFDerivedIsoPaste'Top_mixedCross.{0, 0} hL hQ hκ hP hPL hfin hproj C hRq ν a b h hab)
    shift

end Cases

end Categorification.Stendhal.CupCap
