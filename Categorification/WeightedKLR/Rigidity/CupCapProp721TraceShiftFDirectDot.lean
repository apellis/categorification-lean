/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftF
import Categorification.WeightedKLR.Rigidity.CupCapProp721FDotMatePlus

/-!
# `𝔉_i 𝕋 ≅ 𝕋 𝔉_i` carries the direct dot to the direct dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21 (the dots of the categorical action on derived categories, §4.6). The
isomorphism `CupCap.capFQuantumTraceShiftIso : 𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carries the dot to the dot
(`CupCap.capFQuantumTraceShiftIso_dot`) when the dots on `𝔉_i`, `𝔉⁺_i` are the conjugates of
those on `𝔈_i`, `𝔈⁺_i` along Theorem 4.31. Those conjugates are the direct dots, i.e. the
derived dots on induction (`CupCap.dgBlackFDotMate_eq_dgBlackFDot`,
`CupCap.dgPlusFDotMate_eq_dgPlusFDot`), so the same holds for the direct dots
`CupCap.dgBlackFDot`, `CupCap.dgPlusFDot`.

## Main results

* `CupCap.capFQuantumTraceShiftIso_dgDot`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

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

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (shift : ℤ)

/-- **`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for every `j ≤ ℓ` and the quantum trace with homological shift
`shift`, with the direct dots on `𝔉_i` and `𝔉⁺_i` (the derived dots on induction).
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFQuantumTraceShiftIso_dgDot :
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
    letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
    Functor.whiskerRight (dgPlusFDot.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift) ≫
        (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom =
      (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFDot.{0, 0} (Q := Q) (Λ := Λ) ν i C hRq) := by
  rw [← dgPlusFDotMate_eq_dgPlusFDot, ← dgBlackFDotMate_eq_dgBlackFDot]
  exact capFQuantumTraceShiftIso_dot ν i C hRq hL hQ hκ hP hPL hfin hproj shift

end Categorification.Stendhal.CupCap
