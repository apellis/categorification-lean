/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721PackagedAdjunction
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotMateDirect

/-!
# Proposition 7.21: both adjunctions, and the direct dot on `𝕋`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Proposition 7.21 and Definition 7.18, with both adjunctions `𝔉_i ⊣ 𝔈_i` and `𝔈_i ⊣ 𝔉_i` of
Theorem 4.31. This file extends `CupCap.prop721_adjunction` by

* the compatibility of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` and `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` with the cups and caps of
  `𝔈_i ⊣ 𝔉_i` (`CupCap.capEDerivedIso_hom_mateEF`) and the description of
  `𝔉⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` as a mate along `𝕂 ⊣ RHom(K, -)`
  (`CupCap.capFRightAdjointIso_inv_eq_mate`), both under the module-level route hypothesis
  `CupCap.CapEFMateCompatibleCases`;
* the dot statement for `𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` with the directly defined dot `CupCap.dgBlackDot`
  on `𝔈_i` (`CupCap.capEQuantumTraceShiftIso_dgBlackDot`, by
  `CupCap.dgBlackEDotMate_eq_dgBlackDot`).

Not included: the crossings on `𝕋` (named hypothesis `hcross` of
`CupCap.capFQuantumTraceShiftIso_cross`), the crossings of different colours on `𝕋`, and the
identification of the conjugate dot on `𝔈⁺_i` and of the conjugate crossings with the direct
ones.

## Main results

* `CupCap.capEQuantumTraceShiftIso_dgBlackDot`.
* `CupCap.prop721_adjunctionEF`.

Route hypotheses (tracked): `hEF : CupCap.CapEFMateCompatibleCases` (cups and caps of
`𝔈_i ⊣ 𝔉_i` on modules); `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
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

/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for every `j ≤ ℓ` and the quantum trace with homological shift
`shift`, with the directly defined dot `CupCap.dgBlackDot` on `𝔈_i` (and on `𝔈⁺_i` the conjugate
of the dot on `𝔉⁺_i`). Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`; `C`, `hRq`. -/
theorem capEQuantumTraceShiftIso_dgBlackDot :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift)
          (dgBlackDot.{0, 0} (Q := Q) (Λ := Λ) ν i) := by
  rw [← dgBlackEDotMate_eq_dgBlackDot ν i C hRq]
  exact capEQuantumTraceShiftIso_dot ν i C hRq hL hQ hκ hP hPL hfin hproj shift

/-- **Proposition 7.21: cups, caps and dots for both adjunctions** (Webster, arXiv:1309.3796v3,
§7.3, with Theorem 4.31), for every `j ≤ ℓ`: (1) `CupCap.prop721_adjunction` (cups and caps of
`𝔉_i ⊣ 𝔈_i`, `RHom(K, -)` for `𝔈_i` as a mate, dots on `𝕋`); (2) the mate of
`𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` along `𝔈_i ⊣ 𝔉_i` is the inverse of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` (cups and caps
of `𝔈_i ⊣ 𝔉_i`); (3) the inverse of `𝔉⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` is the mate of the
inverse of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` along `𝕂 ⊣ RHom(K, -)`; (4) the dot on `𝕋` for `𝔈_i` with the
direct dot `CupCap.dgBlackDot`.
Route hypotheses (tracked): `hEF` (cups and caps of `𝔈_i ⊣ 𝔉_i` on right modules, for (2) and
(3)); `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq` are Webster's setting for
Theorem 4.31. -/
theorem prop721_adjunctionEF
    (hEF : CapEFMateCompatibleCases (Λ := Λ) (hj := hj) ν i hL hQ hκ hP hPL hfin C hRq) :
    ((mateEquiv (derivedBlackFEAdjunction (Λ := Λ) ν i C hRq)
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
          (dgBlackFDotMate ν i C hRq)) ∧
    (mateEquiv (derivedBlackEFAdjunction (Λ := Λ) ν i C hRq)
      (derivedPlusEFAdjunction (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i C hRq)
      (TwoSquare.mk _ _ _ _
        (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).hom)).natTrans =
      (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv ∧
    (capFRightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv =
      (mateEquiv (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
        (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
        (TwoSquare.mk _ _ _ _
          (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv)).natTrans ∧
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift)
          (dgBlackDot.{0, 0} (Q := Q) (Λ := Λ) ν i) :=
  ⟨prop721_adjunction ν i hL hQ hκ hP hPL hfin hproj C hRq shift,
    capEDerivedIso_hom_mateEF hproj hEF,
    capFRightAdjointIso_inv_eq_mate hproj hEF,
    capEQuantumTraceShiftIso_dgBlackDot ν i hL hQ hκ hP hPL hfin hproj C hRq shift⟩

end Categorification.Stendhal.CupCap
