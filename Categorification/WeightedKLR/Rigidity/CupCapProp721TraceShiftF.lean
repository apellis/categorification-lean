/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721Packaged
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotCoefficient

/-!
# `𝔉_i 𝕋 ≅ 𝕋 𝔉_i` with the shift of `𝔉_i` induced by `𝔈_i ⊣ 𝔉_i`, and the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21 and Definition 7.18. The quantum trace `𝕋` carries a homological shift, and
the isomorphism `𝔉_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` obtained by taking adjoints uses a compatibility of `𝔉_i`
with the shift. Here `𝔉_i` is given the shift compatibility induced from that of `𝔈_i` along
the adjunction `𝔈_i ⊣ 𝔉_i` of Theorem 4.31 (Mathlib's `Adjunction.rightAdjointCommShift`, the
unique one compatible with the adjunction). With it the adjunction commutes with the shift
(`CupCap.derivedBlackEFAdjunction_adjointCommShift`), so the conjugate of the dot on `𝔈_i`,
which is a coefficient map (`Stendhal.dgBlackDot_commShift`), commutes with the shift
(`CupCap.dgBlackFDotMate_adjointCommShift`). The resulting isomorphism
`CupCap.capFQuantumTraceShiftIso` carries the dot to the dot with no shift hypothesis
(`CupCap.capFQuantumTraceShiftIso_dot`).

The shift compatibility of `𝔉_i` used here is the induced one, not the one of `𝔉_i` as a derived
tensor functor (`CupCap.derivedBlackF_commShift`); the two agree exactly when `𝔈_i ⊣ 𝔉_i`
commutes with the derived tensor shifts, which is not proved here.

## Main definitions and results

* `CupCap.derivedBlackFAdjointCommShift`, `CupCap.derivedBlackEFAdjunction_adjointCommShift`.
* `CupCap.dgBlackFDotMate_adjointCommShift`.
* `CupCap.capFQuantumTraceShiftIso`, `CupCap.capFQuantumTraceShiftIso_dot`.

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
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The shift compatibility of `𝔉_i` induced by `𝔈_i ⊣ 𝔉_i`** (Theorem 4.31): the unique
one for which the adjunction commutes with the shift, given the derived tensor shift
compatibility of `𝔈_i` (`CupCap.derivedBlackE_commShift`). -/
abbrev derivedBlackFAdjointCommShift : (derivedBlackF.{0} Q Λ i ν).CommShift ℤ :=
  (derivedBlackEFAdjunction ν i C hRq).rightAdjointCommShift ℤ

/-- With the induced shift compatibility of `𝔉_i`, the adjunction `𝔈_i ⊣ 𝔉_i` commutes with
the shift. -/
theorem derivedBlackEFAdjunction_adjointCommShift :
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
    (derivedBlackEFAdjunction (Λ := Λ) ν i C hRq).CommShift ℤ :=
  (derivedBlackEFAdjunction ν i C hRq).commShift_of_leftAdjoint ℤ

/-- **The conjugate dot on `𝔉_i` commutes with the induced shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the dot on `𝔈_i` is a coefficient map
(`Stendhal.dgBlackDot_commShift`) and the adjunction commutes with the shift. -/
theorem dgBlackFDotMate_adjointCommShift :
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
    NatTrans.CommShift (dgBlackFDotMate (Λ := Λ) ν i C hRq) ℤ := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
  have := derivedBlackEFAdjunction_adjointCommShift (Λ := Λ) ν i C hRq
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

/-- **`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i`** for the quantum trace of Definition 7.18 with homological shift
`shift` (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, by
taking adjoints of `CupCap.capEDerivedIso` along `𝔈_i ⊣ 𝔉_i`, with the shift compatibility of
`𝔉_i` induced by the adjunction (`CupCap.derivedBlackFAdjointCommShift`).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
def capFQuantumTraceShiftIso :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙ quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ⋙ derivedBlackF.{0} Q Λ i ν :=
  letI := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
  quantumTraceCommIso (derivedBlackEFAdjunction ν i C hRq) (derivedPlusEFAdjunction ν i C hRq)
    (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj) shift

/-- **`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for every `j ≤ ℓ` and the quantum trace with homological shift
`shift`, with the dots on `𝔉_i` and `𝔉⁺_i` the conjugates of those on `𝔈_i` and `𝔈⁺_i`.
No shift hypothesis is needed. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`. -/
theorem capFQuantumTraceShiftIso_dot :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift) ≫
        (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFDotMate ν i C hRq) := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackFDotMate_adjointCommShift (Λ := Λ) ν i C hRq)
    (capEDerivedIso_dot ν i hL hQ hκ hP hPL hfin hproj) shift

end Categorification.Stendhal.CupCap
