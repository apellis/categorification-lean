/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTraceTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721AdjointPaste

/-!
# `𝔉_i² 𝕋 ≅ 𝕋 𝔉_i²` and the crossing

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The pasting of two copies of `𝔉_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i`
(`CupCap.capFRightAdjointIsoMid`, `CupCap.capFRightAdjointIsoTop`) is the conjugate, along the
composite adjunctions `𝔈_i² ⊣ 𝔉_i²`, of the pasted isomorphism `𝕂 ⋙ 𝔈_i² ≅ 𝔈_i² ⋙ 𝕂`
(`CupCap.rightAdjointCommIso_squarePaste`). Since the latter carries the crossing to the crossing
(`CupCap.capEDerivedIsoPasteMid_cross`), the pasted isomorphism for `𝔉_i²` carries the conjugate
of the crossing on `𝔈⁺_i²` to the conjugate of the crossing on `𝔈_i²`
(`CupCap.capFRightAdjointIsoPasteMid_cross`, `CupCap.capFRightAdjointIsoPasteTop_cross`).

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

/-- **The crossing on the dg derived `𝔉_i²`** as the conjugate, along the composite adjunction
`𝔈_i² ⊣ 𝔉_i²` (`CupCap.derivedBlackEFAdjunction`), of the crossing `CupCap.dgBlackCross` on
`𝔈_i²`. -/
def dgBlackFCrossMate :
    derivedBlackF.{0} Q Λ i ν ⋙ derivedBlackF.{0} Q Λ i νᵢ ⟶
      derivedBlackF.{0} Q Λ i ν ⋙ derivedBlackF.{0} Q Λ i νᵢ :=
  conjugateEquiv ((derivedBlackEFAdjunction νᵢ i C hRq).comp (derivedBlackEFAdjunction ν i C hRq))
    ((derivedBlackEFAdjunction νᵢ i C hRq).comp (derivedBlackEFAdjunction ν i C hRq))
    (dgBlackCross.{0, 0} ν i)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing on the dg derived `𝔉⁺_i²`** as the conjugate, along the composite adjunction
`𝔈⁺_i² ⊣ 𝔉⁺_i²` (`CupCap.derivedPlusEFAdjunction`), of the crossing `CupCap.dgPlusCross`. -/
def dgPlusFCrossMate (hQ : KLRSymm Q) :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙ derivedPlusF.{0} k Q Λ Λc j hj ν₀ νᵢ i ⟶
      derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙ derivedPlusF.{0} k Q Λ Λc j hj ν₀ νᵢ i :=
  conjugateEquiv ((derivedPlusEFAdjunction νᵢ i C hRq).comp (derivedPlusEFAdjunction ν i C hRq))
    ((derivedPlusEFAdjunction νᵢ i C hRq).comp (derivedPlusEFAdjunction ν i C hRq))
    (dgPlusCross.{0, 0} k Q Λ Λc j hj ν₀ ν i hQ)

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

/-- **`𝔉_i² ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i²` carries the crossing to the crossing, for
`j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the pasting of two
copies of `CupCap.capFRightAdjointIsoMid`, with the crossings on `𝔉_i²` and `𝔉⁺_i²` the
conjugates of those on `𝔈_i²` and `𝔈⁺_i²`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIsoPasteMid_cross (h : j < ℓ) :
    Functor.whiskerRight (dgPlusFCrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj νᵢᵢ ν₀ L) ≫
        (squarePaste (capFRightAdjointIsoMid νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capFRightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h)).hom =
      (squarePaste (capFRightAdjointIsoMid νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capFRightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h)).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFCrossMate ν i C hRq) := by
  rw [capFRightAdjointIsoMid, capFRightAdjointIsoMid, coevaluationRightAdjointCommIso,
    coevaluationRightAdjointCommIso, ← rightAdjointCommIso_squarePaste]
  exact rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capEDerivedIsoPasteMid_cross.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h)

/-- **`𝔉_i² ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i²` carries the crossing to the crossing, for
`j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for the pasting of two
copies of `CupCap.capFRightAdjointIsoTop`, with the crossings on `𝔉_i²` and `𝔉⁺_i²` the
conjugates of those on `𝔈_i²` and `𝔈⁺_i²`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIsoPasteTop_cross (h : ¬ j < ℓ) :
    Functor.whiskerRight (dgPlusFCrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj νᵢᵢ ν₀ L) ≫
        (squarePaste (capFRightAdjointIsoTop νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capFRightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h)).hom =
      (squarePaste (capFRightAdjointIsoTop νᵢ i hL hQ hκ hP hPL hfin hproj C hRq h)
          (capFRightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h)).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFCrossMate ν i C hRq) := by
  rw [capFRightAdjointIsoTop, capFRightAdjointIsoTop, coevaluationRightAdjointCommIso,
    coevaluationRightAdjointCommIso, ← rightAdjointCommIso_squarePaste]
  exact rightAdjointCommIso_whisker _ _ _ _ _ _ _ _
    (capEDerivedIsoPasteTop_cross.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h)


end Categorification.Stendhal.CupCap
