/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTrace
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDerivedDG
import Categorification.WeightedKLR.Rigidity.CupCapProp721AdjointTwo

/-!
# `𝔉_i 𝕋 ≅ 𝕋 𝔉_i` and the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The isomorphisms `𝔉_i ⋙ RHom(K_{{i} + ν}, -) ≅ RHom(K_ν, -) ⋙ 𝔉_i`
(`CupCap.capFRightAdjointIsoMid`, `CupCap.capFRightAdjointIsoTop`) and their quantum-trace forms
(`CupCap.capFQuantumTraceIsoMid`, `CupCap.capFQuantumTraceIsoTop`) are conjugates, along
`𝔈_i ⊣ 𝔉_i`, of `𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂`. Since the latter carries the dot to the dot
(`CupCap.capEDerivedIsoMid_dot`), they carry the conjugate of the dot on `𝔈⁺_i` to the
conjugate of the dot on `𝔈_i` (`CupCap.rightAdjointCommIso_whisker`).

For the quantum trace, which includes the homological shift of Definition 7.18, the conjugate of
the dot on `𝔈_i` is assumed to commute with the shift (`NatTrans.CommShift`, a named hypothesis
of `CupCap.capFQuantumTraceIsoMid_dot` and `CupCap.capFQuantumTraceIsoTop_dot`, tracked).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIsoMid`; `hRq` is Webster's setting for Theorem 4.31.
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

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
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

/-- **The dot on the dg derived `𝔉_i`**, the conjugate along `𝔈_i ⊣ 𝔉_i`
(`CupCap.derivedBlackEFAdjunction`) of the dot `CupCap.dgBlackDot` on `𝔈_i`. -/
def dgBlackFDotMate : derivedBlackF.{0} Q Λ i ν ⟶ derivedBlackF.{0} Q Λ i ν :=
  conjugateEquiv (derivedBlackEFAdjunction ν i C hRq) (derivedBlackEFAdjunction ν i C hRq)
    (dgBlackDot.{0, 0} ν i)

variable (k Q Λ Λc j hj ν₀) in
/-- **The dot on the dg derived `𝔉⁺_i`**, the conjugate along `𝔈⁺_i ⊣ 𝔉⁺_i`
(`CupCap.derivedPlusEFAdjunction`) of the dot `CupCap.dgPlusDot` on `𝔈⁺_i`. -/
def dgPlusFDotMate :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⟶ derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i :=
  conjugateEquiv (derivedPlusEFAdjunction ν i C hRq) (derivedPlusEFAdjunction ν i C hRq)
    (dgPlusDot.{0, 0} k Q Λ Λc j hj ν₀ ν i)

/-- **`𝔉_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` carries the dot to the dot, for `j < ℓ`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), with the dots on `𝔉_i` and
`𝔉⁺_i` the conjugates of those on `𝔈_i` and `𝔈⁺_i`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIsoMid_dot (h : j < ℓ) :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀
          L) ≫ (capFRightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom =
      (capFRightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFDotMate ν i C hRq) :=
  rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capEDerivedIsoMid_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h)

/-- **`𝔉_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` carries the dot to the dot, for `j = ℓ`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIsoTop_dot (h : ¬ j < ℓ) :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀
          L) ≫ (capFRightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom =
      (capFRightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFDotMate ν i C hRq) :=
  rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capEDerivedIsoTop_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h)

variable (shift : ℤ)

/-- **`𝔉_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carries the dot to the dot, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the quantum trace of Definition 7.18
with homological shift `shift`. Named hypothesis (tracked): the dot `CupCap.dgBlackFDotMate`
commutes with the shift. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`. -/
theorem capFQuantumTraceIsoMid_dot
    (hshift : NatTrans.CommShift (dgBlackFDotMate (Λ := Λ) ν i C hRq) ℤ)
    (h : j < ℓ) :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
          shift) ≫
        (capFQuantumTraceIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom =
      (capFQuantumTraceIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFDotMate ν i C hRq) :=
  rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _ hshift
    (capEDerivedIsoMid_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h) shift

/-- **`𝔉_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carries the dot to the dot, for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the quantum trace with homological
shift `shift`. Named hypothesis (tracked): the dot `CupCap.dgBlackFDotMate` commutes with the
shift. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFQuantumTraceIsoTop_dot
    (hshift : NatTrans.CommShift (dgBlackFDotMate (Λ := Λ) ν i C hRq) ℤ)
    (h : ¬ j < ℓ) :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
          shift) ≫
        (capFQuantumTraceIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom =
      (capFQuantumTraceIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq shift h).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFDotMate ν i C hRq) :=
  rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _ hshift
    (capEDerivedIsoTop_dot.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h) shift

end Categorification.Stendhal.CupCap
