/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTraceCross
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDGCases

/-!
# `𝔈_i 𝕋 ≅ 𝕋 𝔈_i`, the dot and the crossing

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The isomorphisms `𝔈_i ⋙ RHom(K_ν, -) ≅ RHom(K_{{i} + ν}, -) ⋙ 𝔈_i`
(`CupCap.capERightAdjointIsoMid`, `CupCap.capERightAdjointIsoTop`) and their quantum-trace forms
(`CupCap.capEQuantumTraceIsoMid`, `CupCap.capEQuantumTraceIsoTop`) are conjugates, along
`𝔉_i ⊣ 𝔈_i`, of `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂`. Since the latter carries the dot to the dot
(`CupCap.capFDerivedIsoMid_dot`) and the crossing to the crossing
(`CupCap.capFDerivedIsoPasteMid_cross`), the former carry the conjugates of the dot and of the
crossing on `𝔉⁺_i` to the conjugates of those on `𝔉_i` (`CupCap.rightAdjointCommIso_whisker`,
`CupCap.rightAdjointCommIso_squarePaste`).

For the quantum trace, the conjugate dot on `𝔈_i` is assumed to commute with the shift (named
hypothesis `hshift`, tracked). The analogous hypothesis on the `𝔉_i` side is reduced to the
compatibility of `𝔈_i ⊣ 𝔉_i` and of the dot on `𝔈_i` with the shifts
(`CupCap.dgBlackFDotMate_commShift`).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capFDerivedIsoMid`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
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

section One

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
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The dot on the dg derived `𝔈_i`**, the conjugate along `𝔉_i ⊣ 𝔈_i`
(`CupCap.derivedBlackFEAdjunction`) of the dot `CupCap.dgBlackFDot` on `𝔉_i`. -/
def dgBlackEDotMate : derivedBlackE.{0} Q Λ i ν ⟶ derivedBlackE.{0} Q Λ i ν :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  conjugateEquiv (derivedBlackFEAdjunction ν i C hRq) (derivedBlackFEAdjunction ν i C hRq)
    (dgBlackFDot.{0, 0} ν i C hRq)

variable (k Q Λ Λc j hj ν₀) in
/-- **The dot on the dg derived `𝔈⁺_i`**, the conjugate along `𝔉⁺_i ⊣ 𝔈⁺_i`
(`CupCap.derivedPlusFEAdjunction`) of the dot `CupCap.dgPlusFDot` on `𝔉⁺_i`. -/
def dgPlusEDotMate :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⟶ derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  conjugateEquiv (derivedPlusFEAdjunction ν i C hRq) (derivedPlusFEAdjunction ν i C hRq)
    (dgPlusFDot.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)

/-- **The `𝔉_i`-side shift hypothesis, reduced**: the conjugate dot `CupCap.dgBlackFDotMate`
commutes with the shift as soon as `𝔈_i ⊣ 𝔉_i` and the dot `CupCap.dgBlackDot` on `𝔈_i` do. -/
theorem dgBlackFDotMate_commShift
    [(derivedBlackEFAdjunction (Λ := Λ) ν i C hRq).CommShift ℤ]
    [NatTrans.CommShift (dgBlackDot.{0, 0} (Q := Q) (Λ := Λ) ν i) ℤ] :
    NatTrans.CommShift (dgBlackFDotMate (Λ := Λ) ν i C hRq) ℤ :=
  conjugateEquiv_commShift ℤ _ _ _

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

/-- **`𝔈_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i` carries the dot to the dot, for `j < ℓ`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), with the dots on `𝔈_i` and
`𝔈⁺_i` the conjugates of those on `𝔉_i` and `𝔉⁺_i`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capERightAdjointIsoMid_dot (h : j < ℓ) :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L) ≫
        (capERightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom =
      (capERightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom ≫
        Functor.whiskerLeft
          (coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L)
          (dgBlackEDotMate ν i C hRq) :=
  rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capFDerivedIsoMid_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h)

/-- **`𝔈_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i` carries the dot to the dot, for `j = ℓ`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capERightAdjointIsoTop_dot (h : ¬ j < ℓ) :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L) ≫
        (capERightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom =
      (capERightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom ≫
        Functor.whiskerLeft
          (coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L)
          (dgBlackEDotMate ν i C hRq) :=
  rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capFDerivedIsoTop_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h)

variable (shift : ℤ)

/-- **`𝔈_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` carries the dot to the dot, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the quantum trace of Definition 7.18
with homological shift `shift`. Named hypothesis (tracked): the dot `CupCap.dgBlackEDotMate`
commutes with the shift. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`. -/
theorem capEQuantumTraceIsoMid_dot
    (hshift : NatTrans.CommShift (dgBlackEDotMate (Λ := Λ) ν i C hRq) ℤ) (h : j < ℓ) :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom =
      (capEQuantumTraceIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj
          ((Singleton.singleton i : Multiset I) + ν) ν₀ L shift) (dgBlackEDotMate ν i C hRq) :=
  rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _ hshift
    (capFDerivedIsoMid_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h) shift

/-- **`𝔈_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` carries the dot to the dot, for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the quantum trace with homological
shift `shift`. Named hypothesis (tracked): the dot `CupCap.dgBlackEDotMate` commutes with the
shift. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceIsoTop_dot
    (hshift : NatTrans.CommShift (dgBlackEDotMate (Λ := Λ) ν i C hRq) ℤ) (h : ¬ j < ℓ) :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom =
      (capEQuantumTraceIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj
          ((Singleton.singleton i : Multiset I) + ν) ν₀ L shift) (dgBlackEDotMate ν i C hRq) :=
  rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _ hshift
    (capFDerivedIsoTop_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h) shift

end One

section Two

variable (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "aT" μ:max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i

variable [DG.HasDerivedCategory.{0, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TA νᵢᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} (TPp νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TPp νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TPp νᵢᵢ)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The crossing on the dg derived `𝔈_i²`** as the conjugate, along the composite adjunction
`𝔉_i² ⊣ 𝔈_i²` (`CupCap.derivedBlackFEAdjunction`), of the crossing `CupCap.dgBlackFCross` on
`𝔉_i²`. -/
def dgBlackECrossMate (hQ : KLRSymm Q) :
    derivedBlackE.{0} Q Λ i νᵢ ⋙ derivedBlackE.{0} Q Λ i ν ⟶
      derivedBlackE.{0} Q Λ i νᵢ ⋙ derivedBlackE.{0} Q Λ i ν :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  conjugateEquiv ((derivedBlackFEAdjunction ν i C hRq).comp (derivedBlackFEAdjunction νᵢ i C hRq))
    ((derivedBlackFEAdjunction ν i C hRq).comp (derivedBlackFEAdjunction νᵢ i C hRq))
    (dgBlackFCross.{0, 0} ν i C hRq hQ)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing on the dg derived `𝔈⁺_i²`** as the conjugate, along the composite adjunction
`𝔉⁺_i² ⊣ 𝔈⁺_i²` (`CupCap.derivedPlusFEAdjunction`), of the crossing `CupCap.dgPlusFCross`. -/
def dgPlusECrossMate (hQ : KLRSymm Q) :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ νᵢ i ⋙ derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⟶
      derivedPlusE.{0} k Q Λ Λc j hj ν₀ νᵢ i ⋙ derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits (aT ν)
  letI := functor_preservesFiniteColimits (aT ν)
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ νᵢ i C hRq
  letI := functor_preservesFiniteLimits (aT νᵢ)
  letI := functor_preservesFiniteColimits (aT νᵢ)
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteLimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc νᵢ ν₀ i) C hRq
  letI := blackFOfEq_preservesFiniteColimits_of_isRouquierQ Q (plusLabels Λ Λc j hj) i
    (plusWeight_assoc νᵢ ν₀ i) C hRq
  conjugateEquiv ((derivedPlusFEAdjunction ν i C hRq).comp (derivedPlusFEAdjunction νᵢ i C hRq))
    ((derivedPlusFEAdjunction ν i C hRq).comp (derivedPlusFEAdjunction νᵢ i C hRq))
    (dgPlusFCross.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq hQ)

variable {ν i}

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

variable (ν i)

/-- **`𝔈_i² ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i²` carries the crossing to the crossing, for
`j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the pasting of two
copies of `CupCap.capERightAdjointIsoMid`, with the crossings on `𝔈_i²` and `𝔈⁺_i²` the
conjugates of those on `𝔉_i²` and `𝔉⁺_i²`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capERightAdjointIsoPasteMid_cross (h : j < ℓ) :
    Functor.whiskerRight (dgPlusECrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L) ≫
        (squarePaste (capERightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capERightAdjointIsoMid νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)).hom =
      (squarePaste (capERightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capERightAdjointIsoMid νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj νᵢᵢ ν₀ L)
          (dgBlackECrossMate ν i C hRq hQ) := by
  rw [capERightAdjointIsoMid, capERightAdjointIsoMid, coevaluationRightAdjointCommIso,
    coevaluationRightAdjointCommIso, ← rightAdjointCommIso_squarePaste]
  exact rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capFDerivedIsoPasteMid_cross.{0, 0} hL hQ hκ hP hPL hfin hproj C hRq ν i h)

/-- **`𝔈_i² ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i²` carries the crossing to the crossing, for
`j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the pasting of two
copies of `CupCap.capERightAdjointIsoTop`, with the crossings on `𝔈_i²` and `𝔈⁺_i²` the
conjugates of those on `𝔉_i²` and `𝔉⁺_i²`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capERightAdjointIsoPasteTop_cross (h : ¬ j < ℓ) :
    Functor.whiskerRight (dgPlusECrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L) ≫
        (squarePaste (capERightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capERightAdjointIsoTop νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)).hom =
      (squarePaste (capERightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capERightAdjointIsoTop νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj νᵢᵢ ν₀ L)
          (dgBlackECrossMate ν i C hRq hQ) := by
  rw [capERightAdjointIsoTop, capERightAdjointIsoTop, coevaluationRightAdjointCommIso,
    coevaluationRightAdjointCommIso, ← rightAdjointCommIso_squarePaste]
  exact rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capFDerivedIsoPasteTop_cross.{0, 0} hL hQ hκ hP hPL hfin hproj C hRq ν i h)

end Two

end Categorification.Stendhal.CupCap
