/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateTrace

/-!
# Proposition 7.21: units, counits and dots on `𝕂`, `RHom(K, -)` and `𝕋`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Proposition 7.21 and Definition 7.18. This file collects, for every `j ≤ ℓ`, the statements of
Proposition 7.21 proved so far beyond `CupCap.prop721_coevaluation` (dots and same-colour
crossings on `𝕂`): the compatibility of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` and `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` with the
cups and caps of `𝔉_i ⊣ 𝔈_i` (as a mate identity), the description of the isomorphisms on
`RHom(K, -)` and on the quantum trace `𝕋` as mates along `𝕂 ⊣ RHom(K, -)`, and the dots on
`𝕋` for the shift compatibilities induced by the adjunctions (`…ShiftIso` forms, no shift
hypothesis).

Not included: the crossings on `𝕋` (they still need the named hypothesis `hcross` of
`CupCap.capFQuantumTraceShiftIso_cross`), the crossings of different colours, the cups and caps
of `𝔈_i ⊣ 𝔉_i`, and the identification of the conjugate dots and crossings on `𝔈_i`, `𝔉_i`
with the directly defined ones.

## Main results

* `CupCap.prop721_adjunction`.

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

/-- **Proposition 7.21: units, counits and dots on `𝕂`, `RHom(K, -)` and `𝕋`** (Webster,
arXiv:1309.3796v3, §7.3), for every `j ≤ ℓ`: (1) the mate of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` along
`𝔉_i ⊣ 𝔈_i` is the inverse of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` (cups and caps); (2) the inverse of
`𝔈⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i` is the mate of the inverse of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂`
along `𝕂 ⊣ RHom(K, -)`; (3), (4) the isomorphisms `𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` and
`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carry the dot to the dot, with the shift compatibilities of `𝔈_i`, `𝔉_i`
induced by the adjunctions.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq` are
Webster's setting for Theorem 4.31. -/
theorem prop721_adjunction :
    (mateEquiv (derivedBlackFEAdjunction (Λ := Λ) ν i C hRq)
      (derivedPlusFEAdjunction (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i C hRq)
      (TwoSquare.mk _ _ _ _
        (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom)).natTrans =
      (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).inv ∧
    (capERightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv =
      (mateEquiv (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
        (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
        (TwoSquare.mk _ _ _ _ (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).inv)).natTrans ∧
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift)
          (dgBlackEDotMate ν i C hRq) ∧
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift) ≫
        (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFDotMate ν i C hRq) :=
  ⟨capFDerivedIso_hom_mate ν i hL hQ hκ hP hPL hfin hproj C hRq,
    capERightAdjointIso_inv_eq_mate ν i hL hQ hκ hP hPL hfin hproj C hRq,
    capEQuantumTraceShiftIso_dot ν i C hRq hL hQ hκ hP hPL hfin hproj shift,
    capFQuantumTraceShiftIso_dot ν i C hRq hL hQ hκ hP hPL hfin hproj shift⟩

end Categorification.Stendhal.CupCap
