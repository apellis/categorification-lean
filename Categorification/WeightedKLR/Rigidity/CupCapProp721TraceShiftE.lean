/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftF
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotCoefficientF

/-!
# `𝔈_i 𝕋 ≅ 𝕋 𝔈_i` with the shift of `𝔈_i` induced by `𝔉_i ⊣ 𝔈_i`, and the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21 and Definition 7.18. This is the `𝔈_i` counterpart of
`CupCap.capFQuantumTraceShiftIso`. The isomorphism `𝔈_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` is obtained by taking
adjoints of `𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` along `𝔉_i ⊣ 𝔈_i` (Theorem 4.31), and `𝔈_i` is given the shift
compatibility induced from the derived tensor one of `𝔉_i` along this adjunction
(`CupCap.derivedBlackEAdjointCommShift`). The dot on `𝔉_i` is a coefficient map
(`Stendhal.dgBlackFDot_commShift`), so its conjugate on `𝔈_i` commutes with the shift
(`CupCap.dgBlackEDotMate_adjointCommShift`), and `CupCap.capEQuantumTraceShiftIso` carries the
dot to the dot with no shift hypothesis (`CupCap.capEQuantumTraceShiftIso_dot`).

The shift compatibility of `𝔈_i` used here is the induced one, not the one of `𝔈_i` as a derived
tensor functor (`CupCap.derivedBlackE_commShift`).

## Main definitions and results

* `CupCap.derivedBlackEAdjointCommShift`, `CupCap.derivedBlackFEAdjunction_adjointCommShift`.
* `CupCap.dgBlackEDotMate_adjointCommShift`.
* `CupCap.capEQuantumTraceShiftIso`, `CupCap.capEQuantumTraceShiftIso_dot`.

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
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The shift compatibility of `𝔈_i` induced by `𝔉_i ⊣ 𝔈_i`** (Theorem 4.31): the unique
one for which the adjunction commutes with the shift, given the derived tensor shift
compatibility of `𝔉_i` (`CupCap.derivedBlackF_commShift`). -/
abbrev derivedBlackEAdjointCommShift : (derivedBlackE.{0} Q Λ i ν).CommShift ℤ :=
  (derivedBlackFEAdjunction ν i C hRq).rightAdjointCommShift ℤ

/-- With the induced shift compatibility of `𝔈_i`, the adjunction `𝔉_i ⊣ 𝔈_i` commutes with
the shift. -/
theorem derivedBlackFEAdjunction_adjointCommShift :
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
    (derivedBlackFEAdjunction (Λ := Λ) ν i C hRq).CommShift ℤ :=
  (derivedBlackFEAdjunction ν i C hRq).commShift_of_leftAdjoint ℤ

/-- **The conjugate dot on `𝔈_i` commutes with the induced shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the dot on `𝔉_i` is a coefficient map
(`Stendhal.dgBlackFDot_commShift`) and the adjunction commutes with the shift. -/
theorem dgBlackEDotMate_adjointCommShift :
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
    NatTrans.CommShift (dgBlackEDotMate (Λ := Λ) ν i C hRq) ℤ := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
  have := derivedBlackFEAdjunction_adjointCommShift (Λ := Λ) ν i C hRq
  exact conjugateEquiv_commShift ℤ _ _ _

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (shift : ℤ)

/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i`** for the quantum trace of Definition 7.18 with homological shift
`shift` (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, by
taking adjoints of `CupCap.capFDerivedIso` along `𝔉_i ⊣ 𝔈_i`, with the shift compatibility of
`𝔈_i` induced by the adjunction (`CupCap.derivedBlackEAdjointCommShift`).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
def capEQuantumTraceShiftIso :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift ⋙ derivedBlackE.{0} Q Λ i ν :=
  letI := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
  quantumTraceCommIso (derivedBlackFEAdjunction ν i C hRq) (derivedPlusFEAdjunction ν i C hRq)
    (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq) shift

/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for every `j ≤ ℓ` and the quantum trace with homological shift
`shift`, with the dots on `𝔈_i` and `𝔈⁺_i` the conjugates of those on `𝔉_i` and `𝔉⁺_i`.
No shift hypothesis is needed. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIso_dot :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift)
          (dgBlackEDotMate ν i C hRq) := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackEDotMate_adjointCommShift (Λ := Λ) ν i C hRq)
    (capFDerivedIso_dot ν i hL hQ hκ hP hPL hfin hproj C hRq) shift

end Categorification.Stendhal.CupCap
