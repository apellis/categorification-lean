/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDGMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFCrossCap

/-!
# `𝕂 ∘ 𝔉 ≅ 𝔉 ∘ 𝕂` and the crossings on derived categories of dg modules: the two cases

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`. The generic compatibilities
`CupCap.capFDerivedIsoPaste_cross` and `CupCap.capFDerivedIsoPaste'_mixedCross` applied to the
cap data `CupCap.capFDataMid` (`j < ℓ`) and `CupCap.capFDataTop` (`j = ℓ`), with the module-level
compatibilities `CupCap.capFCompIsoOfEqMid_cross`, `CupCap.capFCompIsoOfEqTop_cross`,
`CupCap.capFCompIsoOfEq'Mid_mixedCross` and `CupCap.capFCompIsoOfEq'Top_mixedCross`. The
exactness of `𝔉_i` and `𝔉⁺_i` (Theorem 4.31) is supplied from `C` and `hRq : IsRouquierQ C Q`,
through `CupCap.blackFOfEq_preservesFiniteLimits_of_isRouquierQ` along content equalities.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`.
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

section Exact

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) {μ β : Multiset I}
  (h : ({i} : Multiset I) + μ = β)

/-- `𝔉_i` along a content equality is left exact (Webster, Theorem 4.31). -/
theorem blackFOfEq_preservesFiniteLimits_of_isRouquierQ (C : QuantumGroup.CartanDatum I)
    (hRq : IsRouquierQ C Q) : Limits.PreservesFiniteLimits (blackFOfEq Q Λ' i h) := by
  subst h
  exact blackF_preservesFiniteLimits Q Λ' i μ C hRq

/-- `𝔉_i` along a content equality is right exact (Webster, Theorem 4.31). -/
theorem blackFOfEq_preservesFiniteColimits_of_isRouquierQ (C : QuantumGroup.CartanDatum I)
    (hRq : IsRouquierQ C Q) : Limits.PreservesFiniteColimits (blackFOfEq Q Λ' i h) := by
  subst h
  exact blackF_preservesFiniteColimits Q Λ' i μ C hRq

end Exact

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "aT" μ:max i':max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i'

section Cross

variable (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))

variable
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νᵢ)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νᵢᵢ)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νᵢᵢ)ᵐᵒᵖ)]

/-- **`𝕂 ⋙ 𝔉_i² ≅ 𝔉_i² ⋙ 𝕂` carries the crossing to the crossing on derived categories of dg
modules, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
pasting of the isomorphisms of `CupCap.capFDataMid` at `ν` and at `{i} + ν`. Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is Webster's setting for
Theorem 4.31. -/
theorem capFDerivedIsoPasteMid_cross (h : j < ℓ) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
    letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits (aT ν i)
    letI := functor_preservesFiniteColimits (aT ν i)
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ νᵢ i C hRq
    letI := functor_preservesFiniteLimits (aT νᵢ i)
    letI := functor_preservesFiniteColimits (aT νᵢ i)
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc ν ν₀ i) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc ν ν₀ i) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc νᵢ ν₀ i) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc νᵢ ν₀ i) C hRq
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFCross.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq hQ) ≫
        (capFDerivedIsoPaste.{w, w'} C hRq (capFDataMid (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel
          hκ hP hPL) hP hPL hκ h)
          (capFDataMid (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)).hom =
      (capFDerivedIsoPaste.{w, w'} C hRq (capFDataMid (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel
        hκ hP hPL) hP hPL hκ h)
          (capFDataMid (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)).hom ≫
        Functor.whiskerRight (dgBlackFCross.{w, w'} ν i C hRq hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L) :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits (aT ν i)
  letI := functor_preservesFiniteColimits (aT ν i)
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ νᵢ i C hRq
  letI := functor_preservesFiniteLimits (aT νᵢ i)
  letI := functor_preservesFiniteColimits (aT νᵢ i)
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc νᵢ ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc νᵢ ν₀ i) C hRq
  letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
    hfin hproj
  letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
    hfin hproj
  letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
    hfin hproj
  capFDerivedIsoPaste_cross C hRq hQ _ _
    (capFCompIsoOfEqMid_cross (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
      hPL hκ hQ h)

/-- **`𝕂 ⋙ 𝔉_i² ≅ 𝔉_i² ⋙ 𝕂` carries the crossing to the crossing on derived categories of dg
modules, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the
pasting of the isomorphisms of `CupCap.capFDataTop` at `ν` and at `{i} + ν`. Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is Webster's setting for
Theorem 4.31. -/
theorem capFDerivedIsoPasteTop_cross (h : ¬ j < ℓ) :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
    letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits (aT ν i)
    letI := functor_preservesFiniteColimits (aT ν i)
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ νᵢ i C hRq
    letI := functor_preservesFiniteLimits (aT νᵢ i)
    letI := functor_preservesFiniteColimits (aT νᵢ i)
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc ν ν₀ i) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc ν ν₀ i) C hRq
    letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc νᵢ ν₀ i) C hRq
    letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
      (plusWeight_assoc νᵢ ν₀ i) C hRq
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
      hfin hproj
    letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
      hfin hproj
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFCross.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq hQ) ≫
        (capFDerivedIsoPaste.{w, w'} C hRq (capFDataTop (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel
          hκ hP hPL) hP hPL hκ h)
          (capFDataTop (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)).hom =
      (capFDerivedIsoPaste.{w, w'} C hRq (capFDataTop (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel
        hκ hP hPL) hP hPL hκ h)
          (capFDataTop (hL := hL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ h)).hom ≫
        Functor.whiskerRight (dgBlackFCross.{w, w'} ν i C hRq hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj νᵢᵢ ν₀ L) :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits (aT ν i)
  letI := functor_preservesFiniteColimits (aT ν i)
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ νᵢ i C hRq
  letI := functor_preservesFiniteLimits (aT νᵢ i)
  letI := functor_preservesFiniteColimits (aT νᵢ i)
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc νᵢ ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc νᵢ ν₀ i) C hRq
  letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL
    hfin hproj
  letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢ) hL hQ hκ hP hPL
    hfin hproj
  letI := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := νᵢᵢ) hL hQ hκ hP hPL
    hfin hproj
  capFDerivedIsoPaste_cross C hRq hQ _ _
    (capFCompIsoOfEqTop_cross (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
      hPL hκ hQ h)

end Cross

section MixedCross

variable (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

variable
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νa)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νb)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νab)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νab)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νab)ᵐᵒᵖ)]

/-- **`𝕂 ⋙ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ⋙ 𝕂` carries the crossing of different colours to the crossing on
derived categories of dg modules, for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for the pastings of the isomorphisms of `CupCap.capFDataMid` for the two orders
of appending. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq`
is Webster's setting for Theorem 4.31. -/
theorem capFDerivedIsoPaste'Mid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
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
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFMixedCross.{w, w'} k Q Λ Λc j hj ν₀ ν a b C hRq hQ) ≫
        (capFDerivedIsoPaste'.{w, w'} (mixedSwap ν a b) C hRq
          (capFDataMid (hL := hL) (ν := ν) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)
          (capFDataMid (hL := hL) (ν := νa) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)).hom =
      (capFDerivedIsoPaste'.{w, w'} (rfl : ({a} : Multiset I) + νb = νab) C hRq
          (capFDataMid (hL := hL) (ν := ν) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)
          (capFDataMid (hL := hL) (ν := νb) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)).hom ≫
        Functor.whiskerRight (dgBlackFMixedCross.{w, w'} ν a b C hRq hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj νab ν₀ L) :=
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
  capFDerivedIsoPaste'_mixedCross C hRq hQ _ _ _ _
    (capFCompIsoOfEq'Mid_mixedCross ν a b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ
      hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ h hab)

/-- **`𝕂 ⋙ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ⋙ 𝕂` carries the crossing of different colours to the crossing on
derived categories of dg modules, for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for the pastings of the isomorphisms of `CupCap.capFDataTop` for the two orders
of appending. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq`
is Webster's setting for Theorem 4.31. -/
theorem capFDerivedIsoPaste'Top_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
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
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFMixedCross.{w, w'} k Q Λ Λc j hj ν₀ ν a b C hRq hQ) ≫
        (capFDerivedIsoPaste'.{w, w'} (mixedSwap ν a b) C hRq
          (capFDataTop (hL := hL) (ν := ν) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)
          (capFDataTop (hL := hL) (ν := νa) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)).hom =
      (capFDerivedIsoPaste'.{w, w'} (rfl : ({a} : Multiset I) + νb = νab) C hRq
          (capFDataTop (hL := hL) (ν := ν) (i := b) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)
          (capFDataTop (hL := hL) (ν := νb) (i := a) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP
            hPL hκ h)).hom ≫
        Functor.whiskerRight (dgBlackFMixedCross.{w, w'} ν a b C hRq hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj νab ν₀ L) :=
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
  capFDerivedIsoPaste'_mixedCross C hRq hQ _ _ _ _
    (capFCompIsoOfEq'Top_mixedCross ν a b (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ
      hP hPL) (midKLRRel hκ hP hPL) (midKLRRel hκ hP hPL) hP hPL hκ hQ h hab)

end MixedCross

end Categorification.Stendhal.CupCap
