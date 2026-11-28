/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721PackagedAdjunctionEF
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotMatePlus

/-!
# `𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` and the directly defined dots

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (with the dots of §4.6). The quantum trace `𝕋` intertwines the dots on `𝔈⁺_i`
and `𝔈_i`, both in their direct form (`CupCap.dgPlusDot`, `CupCap.dgBlackDot`):
`CupCap.capEQuantumTraceShiftIso_dgDot`, from `CupCap.capEQuantumTraceShiftIso_dgBlackDot` and
`CupCap.dgPlusEDotMate_eq_dgPlusDot`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj` as for
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
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
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
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) (shift : ℤ)

set_option linter.unusedSectionVars false in
/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for every `j ≤ ℓ` and the quantum trace with homological shift
`shift`, with the directly defined dots `CupCap.dgPlusDot` on `𝔈⁺_i` and `CupCap.dgBlackDot` on
`𝔈_i`. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`,
`hRq`. -/
theorem capEQuantumTraceShiftIso_dgDot :
    Functor.whiskerRight (dgPlusDot.{0, 0} k Q Λ Λc j hj ν₀ ν i)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift)
          (dgBlackDot.{0, 0} (Q := Q) (Λ := Λ) ν i) := by
  rw [← dgPlusEDotMate_eq_dgPlusDot ν i C hRq]
  exact capEQuantumTraceShiftIso_dgBlackDot ν i hL hQ hκ hP hPL hfin hproj C hRq shift

end Categorification.Stendhal.CupCap
