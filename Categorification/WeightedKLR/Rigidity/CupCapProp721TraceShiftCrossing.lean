/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CrossDegreewise
import Categorification.WeightedKLR.Rigidity.CupCapProp721FCrossDegreewise

/-!
# `𝔉_i² 𝕋 ≅ 𝕋 𝔉_i²` and `𝔈_i² 𝕋 ≅ 𝕋 𝔈_i²` carry the crossing to the crossing

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21, for the quantum trace `𝕋` of Definition 7.18 with its homological shift.
`CupCap.capFQuantumTraceShiftIso_cross` reduced this to the crossing `CupCap.dgBlackCross` on
`𝔈_i²` commuting with the derived tensor shift (its hypothesis `hcross`), which holds by
`Stendhal.dgBlackCross_commShift`. Likewise `CupCap.capEQuantumTraceShiftIso_cross` reduced the
`𝔈_i` case to the crossing `CupCap.dgBlackFCross` on `𝔉_i²` commuting with the derived tensor
shift, which holds by `Stendhal.dgBlackFCross_commShift`. This file records both statements
without `hcross`.

## Main results

* `CupCap.capFQuantumTraceShiftIso_crossing`.
* `CupCap.capEQuantumTraceShiftIso_crossing`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
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
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

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

variable {ν i}

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (shift : ℤ)

variable (ν i)

/-- **`𝔉⁺_i² ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i²` carries the crossing to the crossing** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, the quantum trace with
homological shift `shift` and the pasting of two copies of `CupCap.capFQuantumTraceShiftIso`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFQuantumTraceShiftIso_crossing :
    Functor.whiskerRight (dgPlusFCrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj νᵢᵢ ν₀ L shift) ≫
        (squarePaste (capFQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom =
      (squarePaste (capFQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFCrossMate ν i C hRq) :=
  capFQuantumTraceShiftIso_cross ν i C hRq hL hQ hκ hP hPL hfin hproj shift
    (dgBlackCross_commShift Q Λ ν i)

/-- **`𝔈⁺_i² ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i²` carries the crossing to the crossing** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, the quantum trace with
homological shift `shift` and the pasting of two copies of `CupCap.capEQuantumTraceShiftIso`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIso_crossing :
    Functor.whiskerRight (dgPlusECrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (squarePaste (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capEQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom =
      (squarePaste (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capEQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢᵢ ν₀ L shift)
          (dgBlackECrossMate ν i C hRq hQ) :=
  capEQuantumTraceShiftIso_cross ν i C hRq hL hQ hκ hP hPL hfin hproj shift
    (dgBlackFCross_commShift Q Λ ν i C hRq hQ)

end Categorification.Stendhal.CupCap
