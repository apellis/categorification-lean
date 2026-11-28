/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapTraceE

/-!
# Proposition 7.21: the commutation isomorphisms for all window positions

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Proposition 7.21: the functor `𝕂` of tensoring with the cap bimodule, its right adjoint
`RHom(K, -)` and the quantum trace `𝕋` of Definition 7.18 commute with the functors `𝔈_i`,
`𝔉_i` of the categorical action, compatibly with the dots and crossings.

The isomorphisms are constructed separately for a cap inside the window (`j < ℓ`, the `Mid`
declarations) and at the top (`j = ℓ`, the `Top` declarations). This file assembles them into
one isomorphism for every `j ≤ ℓ`:

* `CupCap.capEDerivedIso : 𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` and `CupCap.capFDerivedIso : 𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`;
* `CupCap.capERightAdjointIso`, `CupCap.capFRightAdjointIso` for `RHom(K, -)`;
* `CupCap.capEQuantumTraceIso`, `CupCap.capFQuantumTraceIso` for `𝕋`,

and states the compatibility with the dots and the same-colour crossings for all of them
(`CupCap.prop721_coevaluation` for `𝕂`, and the `_dot`, `_cross` lemmas).
On `RHom(K, -)` and `𝕋` the dots and crossings are the conjugates, along the adjunctions
`𝔈_i ⊣ 𝔉_i` and `𝔉_i ⊣ 𝔈_i` of Theorem 4.31, of those on the other functor.

Not yet included: the compatibility with the units and counits of the adjunctions (cups and
caps of `𝒰`), the crossings of different colours on `RHom(K, -)` and `𝕋`, and the
identification of the conjugate dots and crossings with the directly defined ones.

Route hypotheses (tracked): `hL` (violated idempotents act by zero on `L`), `hQ` (symmetric
`Q`), `hκ` (cup scalars are units), `hP`, `hPL` (the pull-off identities (7.27), (7.28)),
`hfin`, `hproj` (each `L e(t)` finitely generated and projective over `k`). `C`,
`hRq : IsRouquierQ C Q` over a field is Webster's setting for Theorem 4.31. On the quantum
trace, the named hypotheses `hshiftE`, `hshiftF` (the conjugate dots on `𝔈_i`, `𝔉_i` commute
with the shift) are tracked; `CupCap.dgBlackFDotMate_commShift` reduces `hshiftF`.
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

section One

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
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) (shift : ℤ)

/-- **`𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` on derived categories of dg modules** (Webster, arXiv:1309.3796v3,
Proposition 7.21, the part for `𝔈_i`), for every `j ≤ ℓ`: `CupCap.capEDerivedIsoMid` for
`j < ℓ` and `CupCap.capEDerivedIsoTop` for `j = ℓ`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
def capEDerivedIso :
    coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢ ν₀ L ⋙ derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackE.{0} Q Λ i ν ⋙ coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L :=
  if h : j < ℓ then capEDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h
  else capEDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h

/-- **`𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` on derived categories of dg modules** (Webster, arXiv:1309.3796v3,
Proposition 7.21, the part for `𝔉_i`), for every `j ≤ ℓ`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq` as in
Theorem 4.31. -/
def capFDerivedIso :
    coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L ⋙ derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ≅
      derivedBlackF.{0} Q Λ i ν ⋙ coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢ ν₀ L :=
  if h : j < ℓ then capFDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h
  else capFDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h

/-- **`𝔈⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i`** (Webster, arXiv:1309.3796v3, proof of
Proposition 7.21), for every `j ≤ ℓ`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
def capERightAdjointIso :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj νᵢ ν₀ L ⋙ derivedBlackE.{0} Q Λ i ν :=
  if h : j < ℓ then capERightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h
  else capERightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h

/-- **`𝔉⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i`** (Webster, arXiv:1309.3796v3, proof of
Proposition 7.21), for every `j ≤ ℓ`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
def capFRightAdjointIso :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙ coevaluationRightAdjoint k Q Λ Λc j hj νᵢ ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ⋙ derivedBlackF.{0} Q Λ i ν :=
  if h : j < ℓ then capFRightAdjointIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq h
  else capFRightAdjointIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq h

/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i`** for the quantum trace of Definition 7.18 with homological shift
`shift` (Webster, arXiv:1309.3796v3, Proposition 7.21), for every `j ≤ ℓ`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
def capEQuantumTraceIso :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift ⋙ derivedBlackE.{0} Q Λ i ν :=
  if h : j < ℓ then capEQuantumTraceIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq shift h
  else capEQuantumTraceIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq shift h

/-- **`𝔉⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i`** for the quantum trace of Definition 7.18 with homological shift
`shift` (Webster, arXiv:1309.3796v3, Proposition 7.21), for every `j ≤ ℓ`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
def capFQuantumTraceIso :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙ quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ⋙ derivedBlackF.{0} Q Λ i ν :=
  if h : j < ℓ then capFQuantumTraceIsoMid ν i hL hQ hκ hP hPL hfin hproj C hRq shift h
  else capFQuantumTraceIsoTop ν i hL hQ hκ hP hPL hfin hproj C hRq shift h

/-- `CupCap.capEDerivedIso` carries the dot to the dot (Webster, arXiv:1309.3796v3,
Proposition 7.21). Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`. -/
theorem capEDerivedIso_dot :
    Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢ ν₀ L)
        (dgPlusDot.{0, 0} k Q Λ Λc j hj ν₀ ν i) ≫
        (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).hom =
      (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).hom ≫
        Functor.whiskerRight (dgBlackDot.{0, 0} ν i)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L) := by
  by_cases h : j < ℓ
  · simp only [capEDerivedIso, dite_eq_left h]
    exact capEDerivedIsoMid_dot ν i hL hQ hκ hP hPL hfin hproj h
  · simp only [capEDerivedIso, dite_eq_right h]
    exact capEDerivedIsoTop_dot ν i hL hQ hκ hP hPL hfin hproj h

/-- `CupCap.capFDerivedIso` carries the dot to the dot (Webster, arXiv:1309.3796v3,
Proposition 7.21). Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`,
`hproj`. -/
theorem capFDerivedIso_dot :
    letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
    letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
    letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
    Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFDot.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq) ≫
        (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom =
      (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom ≫
        Functor.whiskerRight (dgBlackFDot.{0, 0} ν i C hRq)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢ ν₀ L) := by
  by_cases h : j < ℓ
  · simp only [capFDerivedIso, dite_eq_left h]
    exact capFDerivedIsoMid_dot ν i hL hQ hκ hP hPL hfin hproj C hRq h
  · simp only [capFDerivedIso, dite_eq_right h]
    exact capFDerivedIsoTop_dot ν i hL hQ hκ hP hPL hfin hproj C hRq h

/-- `CupCap.capERightAdjointIso` carries the conjugate dot to the conjugate dot (Webster,
arXiv:1309.3796v3, proof of Proposition 7.21). Route hypotheses (tracked): `hL`, `hQ`, `hκ`,
`hP`, `hPL`, `hfin`, `hproj`. -/
theorem capERightAdjointIso_dot :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L) ≫
        (capERightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom =
      (capERightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj νᵢ ν₀ L)
          (dgBlackEDotMate ν i C hRq) := by
  by_cases h : j < ℓ
  · simp only [capERightAdjointIso, dite_eq_left h]
    exact capERightAdjointIsoMid_dot ν i C hRq hL hQ hκ hP hPL hfin hproj h
  · simp only [capERightAdjointIso, dite_eq_right h]
    exact capERightAdjointIsoTop_dot ν i C hRq hL hQ hκ hP hPL hfin hproj h

/-- `CupCap.capFRightAdjointIso` carries the conjugate dot to the conjugate dot (Webster,
arXiv:1309.3796v3, proof of Proposition 7.21). Route hypotheses (tracked): `hL`, `hQ`, `hκ`,
`hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIso_dot :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (coevaluationRightAdjoint k Q Λ Λc j hj νᵢ ν₀ L) ≫
        (capFRightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom =
      (capFRightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFDotMate ν i C hRq) := by
  by_cases h : j < ℓ
  · simp only [capFRightAdjointIso, dite_eq_left h]
    exact capFRightAdjointIsoMid_dot ν i hL hQ hκ hP hPL hfin hproj C hRq h
  · simp only [capFRightAdjointIso, dite_eq_right h]
    exact capFRightAdjointIsoTop_dot ν i hL hQ hκ hP hPL hfin hproj C hRq h

/-- `CupCap.capEQuantumTraceIso` carries the conjugate dot to the conjugate dot (Webster,
arXiv:1309.3796v3, Proposition 7.21). Named hypothesis (tracked): `hshiftE`. Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEQuantumTraceIso_dot
    (hshiftE : NatTrans.CommShift (dgBlackEDotMate (Λ := Λ) ν i C hRq) ℤ) :
    Functor.whiskerRight (dgPlusEDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (capEQuantumTraceIso ν i hL hQ hκ hP hPL hfin hproj C hRq shift).hom =
      (capEQuantumTraceIso ν i hL hQ hκ hP hPL hfin hproj C hRq shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift)
          (dgBlackEDotMate ν i C hRq) := by
  by_cases h : j < ℓ
  · simp only [capEQuantumTraceIso, dite_eq_left h]
    exact capEQuantumTraceIsoMid_dot ν i C hRq hL hQ hκ hP hPL hfin hproj shift hshiftE h
  · simp only [capEQuantumTraceIso, dite_eq_right h]
    exact capEQuantumTraceIsoTop_dot ν i C hRq hL hQ hκ hP hPL hfin hproj shift hshiftE h

/-- `CupCap.capFQuantumTraceIso` carries the conjugate dot to the conjugate dot (Webster,
arXiv:1309.3796v3, Proposition 7.21). Named hypothesis (tracked): `hshiftF`. Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFQuantumTraceIso_dot
    (hshiftF : NatTrans.CommShift (dgBlackFDotMate (Λ := Λ) ν i C hRq) ℤ) :
    Functor.whiskerRight (dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq)
        (quantumTraceFunctor k Q Λ Λc j hj νᵢ ν₀ L shift) ≫
        (capFQuantumTraceIso ν i hL hQ hκ hP hPL hfin hproj C hRq shift).hom =
      (capFQuantumTraceIso ν i hL hQ hκ hP hPL hfin hproj C hRq shift).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFDotMate ν i C hRq) := by
  by_cases h : j < ℓ
  · simp only [capFQuantumTraceIso, dite_eq_left h]
    exact capFQuantumTraceIsoMid_dot ν i hL hQ hκ hP hPL hfin hproj C hRq shift hshiftF h
  · simp only [capFQuantumTraceIso, dite_eq_right h]
    exact capFQuantumTraceIsoTop_dot ν i hL hQ hκ hP hPL hfin hproj C hRq shift hshiftF h

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
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- The pasting of two copies of `CupCap.capEDerivedIso`, `𝕂 ⋙ 𝔈⁺_i² ≅ 𝔈_i² ⋙ 𝕂`, carries the
crossing to the crossing (Webster, arXiv:1309.3796v3, Proposition 7.21). Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capEDerivedIso_cross :
    Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢᵢ ν₀ L)
        (dgPlusCross.{0, 0} k Q Λ Λc j hj ν₀ ν i hQ) ≫
        (squarePaste (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).symm
          (capEDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj).symm).symm.hom =
      (squarePaste (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).symm
          (capEDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj).symm).symm.hom ≫
        Functor.whiskerRight (dgBlackCross.{0, 0} ν i)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L) := by
  by_cases h : j < ℓ
  · simp only [capEDerivedIso, dite_eq_left h]
    exact capEDerivedIsoPasteMid_cross ν i hL hQ hκ hP hPL hfin hproj h
  · simp only [capEDerivedIso, dite_eq_right h]
    exact capEDerivedIsoPasteTop_cross ν i hL hQ hκ hP hPL hfin hproj h

/-- The pasting of two copies of `CupCap.capFDerivedIso`, `𝕂 ⋙ 𝔉⁺_i² ≅ 𝔉_i² ⋙ 𝕂`, carries the
crossing to the crossing (Webster, arXiv:1309.3796v3, Proposition 7.21). Route hypotheses
(tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFDerivedIso_cross :
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
    Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFCross.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq hQ) ≫
        (squarePaste (capFDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq).symm
          (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).symm).symm.hom =
      (squarePaste (capFDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq).symm
          (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).symm).symm.hom ≫
        Functor.whiskerRight (dgBlackFCross.{0, 0} ν i C hRq hQ)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢᵢ ν₀ L) := by
  by_cases h : j < ℓ
  · simp only [capFDerivedIso, dite_eq_left h]
    exact capFDerivedIsoPasteMid_cross hL hQ hκ hP hPL hfin hproj C hRq ν i h
  · simp only [capFDerivedIso, dite_eq_right h]
    exact capFDerivedIsoPasteTop_cross hL hQ hκ hP hPL hfin hproj C hRq ν i h

/-- The pasting of two copies of `CupCap.capERightAdjointIso`,
`𝔈⁺_i² ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i²`, carries the conjugate crossing to the conjugate
crossing (Webster, arXiv:1309.3796v3, proof of Proposition 7.21). Route hypotheses (tracked):
`hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capERightAdjointIso_cross :
    Functor.whiskerRight (dgPlusECrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L) ≫
        (squarePaste (capERightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq)
          (capERightAdjointIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq)).hom =
      (squarePaste (capERightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq)
          (capERightAdjointIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq)).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj νᵢᵢ ν₀ L)
          (dgBlackECrossMate ν i C hRq hQ) := by
  by_cases h : j < ℓ
  · simp only [capERightAdjointIso, dite_eq_left h]
    exact capERightAdjointIsoPasteMid_cross ν i C hRq hL hQ hκ hP hPL hfin hproj h
  · simp only [capERightAdjointIso, dite_eq_right h]
    exact capERightAdjointIsoPasteTop_cross ν i C hRq hL hQ hκ hP hPL hfin hproj h

/-- The pasting of two copies of `CupCap.capFRightAdjointIso`,
`𝔉⁺_i² ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i²`, carries the conjugate crossing to the conjugate
crossing (Webster, arXiv:1309.3796v3, proof of Proposition 7.21). Route hypotheses (tracked):
`hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`. -/
theorem capFRightAdjointIso_cross :
    Functor.whiskerRight (dgPlusFCrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (coevaluationRightAdjoint k Q Λ Λc j hj νᵢᵢ ν₀ L) ≫
        (squarePaste (capFRightAdjointIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq)
          (capFRightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq)).hom =
      (squarePaste (capFRightAdjointIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq)
          (capFRightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq)).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L)
          (dgBlackFCrossMate ν i C hRq) := by
  by_cases h : j < ℓ
  · simp only [capFRightAdjointIso, dite_eq_left h]
    exact capFRightAdjointIsoPasteMid_cross ν i C hRq hL hQ hκ hP hPL hfin hproj h
  · simp only [capFRightAdjointIso, dite_eq_right h]
    exact capFRightAdjointIsoPasteTop_cross ν i C hRq hL hQ hκ hP hPL hfin hproj h

/-- **Proposition 7.21 for `𝕂`, on derived categories of dg modules** (Webster,
arXiv:1309.3796v3, §7.3): for every `j ≤ ℓ`, the isomorphisms `CupCap.capEDerivedIso`,
`𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂`, and `CupCap.capFDerivedIso`, `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂`, carry the dot to the
dot, and their pastings carry the same-colour crossing to the crossing.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq` are
Webster's setting for Theorem 4.31. The units and counits (cups and caps) and the crossings of
different colours are not included here. -/
theorem prop721_coevaluation :
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
    (Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢ ν₀ L)
        (dgPlusDot.{0, 0} k Q Λ Λc j hj ν₀ ν i) ≫
        (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).hom =
      (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).hom ≫
        Functor.whiskerRight (dgBlackDot.{0, 0} ν i)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)) ∧
    (Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFDot.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq) ≫
        (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom =
      (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom ≫
        Functor.whiskerRight (dgBlackFDot.{0, 0} ν i C hRq)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢ ν₀ L)) ∧
    (Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢᵢ ν₀ L)
        (dgPlusCross.{0, 0} k Q Λ Λc j hj ν₀ ν i hQ) ≫
        (squarePaste (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).symm
          (capEDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj).symm).symm.hom =
      (squarePaste (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).symm
          (capEDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj).symm).symm.hom ≫
        Functor.whiskerRight (dgBlackCross.{0, 0} ν i)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)) ∧
    (Functor.whiskerLeft (coevaluationFunctor.{0, 0} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFCross.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq hQ) ≫
        (squarePaste (capFDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq).symm
          (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).symm).symm.hom =
      (squarePaste (capFDerivedIso νᵢ i hL hQ hκ hP hPL hfin hproj C hRq).symm
          (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).symm).symm.hom ≫
        Functor.whiskerRight (dgBlackFCross.{0, 0} ν i C hRq hQ)
          (coevaluationFunctor.{0, 0} k Q Λ Λc j hj νᵢᵢ ν₀ L)) :=
  ⟨capEDerivedIso_dot ν i hL hQ hκ hP hPL hfin hproj,
    capFDerivedIso_dot ν i hL hQ hκ hP hPL hfin hproj C hRq,
    capEDerivedIso_cross ν i hL hQ hκ hP hPL hfin hproj,
    capFDerivedIso_cross ν i hL hQ hκ hP hPL hfin hproj C hRq⟩

end Two

end Categorification.Stendhal.CupCap
