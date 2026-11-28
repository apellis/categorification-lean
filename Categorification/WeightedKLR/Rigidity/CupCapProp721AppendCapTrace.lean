/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFAdjoint
import Categorification.Algebra.DerivedTensorTriangulated

/-!
# `𝔈_i 𝕋 ≅ 𝕋 𝔈_i` and `𝔉_i 𝕋 ≅ 𝕋 𝔉_i` for the quantum trace

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The functors `𝔈_i` and `𝔉_i` on the derived categories of dg modules over
`T^λ` and `T^{λ⁺}` (`derivedBlackE`, `derivedBlackF`, `CupCap.derivedPlusE`,
`CupCap.derivedPlusF`) are derived tensor products with ordinary bimodules, so they commute with
the homological shift and are triangulated (`derivedTensor_commShift`,
`derivedTensor_isTriangulated`). With this, the commutation of `RHom(K, -)` with `𝔈_i` and
`𝔉_i` (`CupCap.capERightAdjointIsoMid`, `CupCap.capFRightAdjointIsoMid` and their `j = ℓ`
counterparts) passes to the quantum trace `𝕋^{λ⁺}_λ` of Definition 7.18, with its homological
shift (`CupCap.quantumTraceCommIso`).

## Main definitions

* `derivedBlackE_commShift`, `derivedBlackF_commShift`, `CupCap.derivedPlusE_commShift`,
  `CupCap.derivedPlusF_commShift`, and the corresponding `IsTriangulated` instances.
* `CupCap.capEQuantumTraceIsoMid`, `CupCap.capEQuantumTraceIsoTop`:
  `𝔈_i ⋙ 𝕋_ν ≅ 𝕋_{{i} + ν} ⋙ 𝔈_i`.
* `CupCap.capFQuantumTraceIsoMid`, `CupCap.capFQuantumTraceIsoTop`:
  `𝔉_i ⋙ 𝕋_{{i} + ν} ≅ 𝕋_ν ⋙ 𝔉_i`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIsoMid`; `IsRouquierQ C Q` over a field is Webster's setting for
Theorem 4.31. The compatibility of these isomorphisms with the 2-morphisms is not treated here.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-! ### Shifts -/

section Shift

universe w u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)
  [DG.HasDerivedCategory.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ]

/-- `𝔈_i` on derived categories commutes with the homological shift. -/
instance derivedBlackE_commShift : (derivedBlackE.{w} Q Λ i ν).CommShift ℤ :=
  inferInstanceAs ((derivedTensor.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ
    (RCorner (appendBlackOp Q Λ i ν))).CommShift ℤ)

instance derivedBlackE_isTriangulated : (derivedBlackE.{w} Q Λ i ν).IsTriangulated :=
  inferInstanceAs (derivedTensor.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ
    (RCorner (appendBlackOp Q Λ i ν))).IsTriangulated

/-- `𝔉_i` on derived categories commutes with the homological shift. -/
instance derivedBlackF_commShift : (derivedBlackF.{w} Q Λ i ν).CommShift ℤ :=
  inferInstanceAs ((derivedTensor.{w}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ
    (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (Corner (appendBlackOp Q Λ i ν))).CommShift ℤ)

instance derivedBlackF_isTriangulated : (derivedBlackF.{w} Q Λ i ν).IsTriangulated :=
  inferInstanceAs (derivedTensor.{w}
    (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ
    (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (Corner (appendBlackOp Q Λ i ν))).IsTriangulated

end Shift

namespace CupCap

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
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i

section Shift

universe w

variable [DG.HasDerivedCategory.{w, 0}
    (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
    (((Singleton.singleton i : Multiset I) + ν) + ν₀))ᵐᵒᵖ]

/-- `𝔈_i` on derived categories over `T^{λ⁺}` commutes with the homological shift. -/
instance derivedPlusE_commShift :
    (derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i).CommShift ℤ :=
  inferInstanceAs ((derivedTensor.{w} TPpᵐᵒᵖ TPpᵢᵐᵒᵖ (RCorner aT)).CommShift ℤ)

instance derivedPlusE_isTriangulated :
    (derivedPlusE.{w} k Q Λ Λc j hj ν₀ ν i).IsTriangulated :=
  inferInstanceAs (derivedTensor.{w} TPpᵐᵒᵖ TPpᵢᵐᵒᵖ (RCorner aT)).IsTriangulated

/-- `𝔉_i` on derived categories over `T^{λ⁺}` commutes with the homological shift. -/
instance derivedPlusF_commShift :
    (derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i).CommShift ℤ :=
  inferInstanceAs ((derivedTensor.{w} TPpᵢᵐᵒᵖ TPpᵐᵒᵖ (Corner aT)).CommShift ℤ)

instance derivedPlusF_isTriangulated :
    (derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i).IsTriangulated :=
  inferInstanceAs (derivedTensor.{w} TPpᵢᵐᵒᵖ TPpᵐᵒᵖ (Corner aT)).IsTriangulated

end Shift

/-! ### The quantum trace -/

section Cases

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
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) (shift : ℤ)

/-- **`𝔈_i ⋙ 𝕋_ν ≅ 𝕋_{{i} + ν} ⋙ 𝔈_i` for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for the quantum trace of Definition 7.18 with homological shift
`shift`, by taking adjoints of the part for `𝔉_i` along `𝔉_i ⊣ 𝔈_i`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capEQuantumTraceIsoMid (h : j < ℓ) :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L shift ⋙
        derivedBlackE.{0} Q Λ i ν :=
  quantumTraceCommIso (derivedBlackFEAdjunction ν i C hRq) (derivedPlusFEAdjunction ν i C hRq)
    (capFDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h) shift

/-- **`𝔈_i ⋙ 𝕋_ν ≅ 𝕋_{{i} + ν} ⋙ 𝔈_i` for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for the quantum trace of Definition 7.18 with homological shift
`shift`, by taking adjoints of the part for `𝔉_i` along `𝔉_i ⊣ 𝔈_i`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capEQuantumTraceIsoTop (h : ¬ j < ℓ) :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⋙ quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L shift ⋙
        derivedBlackE.{0} Q Λ i ν :=
  quantumTraceCommIso (derivedBlackFEAdjunction ν i C hRq) (derivedPlusFEAdjunction ν i C hRq)
    (capFDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj C hRq h) shift

/-- **`𝔉_i ⋙ 𝕋_{{i} + ν} ≅ 𝕋_ν ⋙ 𝔉_i` for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for the quantum trace of Definition 7.18 with homological shift
`shift`, by taking adjoints of the part for `𝔈_i` along `𝔈_i ⊣ 𝔉_i` (Theorem 4.31).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capFQuantumTraceIsoMid (h : j < ℓ) :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙
        quantumTraceFunctor k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ⋙ derivedBlackF.{0} Q Λ i ν :=
  quantumTraceCommIso (derivedBlackEFAdjunction ν i C hRq) (derivedPlusEFAdjunction ν i C hRq)
    (capEDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h) shift

/-- **`𝔉_i ⋙ 𝕋_{{i} + ν} ≅ 𝕋_ν ⋙ 𝔉_i` for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for the quantum trace of Definition 7.18 with homological shift
`shift`, by taking adjoints of the part for `𝔈_i` along `𝔈_i ⊣ 𝔉_i` (Theorem 4.31).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capFQuantumTraceIsoTop (h : ¬ j < ℓ) :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙
        quantumTraceFunctor k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L shift ≅
      quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift ⋙ derivedBlackF.{0} Q Λ i ν :=
  quantumTraceCommIso (derivedBlackEFAdjunction ν i C hRq) (derivedPlusEFAdjunction ν i C hRq)
    (capEDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h) shift

end Cases

end CupCap

end Categorification.Stendhal
