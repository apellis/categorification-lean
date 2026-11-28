/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapAdjoint
import Categorification.WeightedKLR.RedStrands.BlackModuleResIndAdjunctionQ

/-!
# `𝔈_i ⊣ 𝔉_i` on derived categories of dg modules, and `𝔉_i 𝕋 ≅ 𝕋 𝔉_i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31
and §7.3, proof of Proposition 7.21. Theorem 4.31 gives, besides `𝔉_i ⊣ 𝔈_i`, the adjunction
`𝔈_i ⊣ 𝔉_i` on right `T^λ`-modules (`clBlackResIndAdjunctionQ`). That declaration is stated
with the classical decidable equality on the colour set and with an auxiliary presentation `P`
of extra relations together with two side conditions on it; the conclusion mentions neither.
Here it is specialised to the presentation with no relations, where both side conditions hold
vacuously, and moved to an arbitrary decidable equality (`CupCap.blackEFAdjunction`).

On the `λ⁺` side, Theorem 4.31 for the labels `λ⁺` at the black weight `ν + ν₀` is transported
along the identification of the black weights `{i} + (ν + ν₀) = ({i} + ν) + ν₀`
(`plusWeightOp`) by `InductionAlong.resIndAdjunctionTransport` (`CupCap.plusEFAdjunction`).

Both adjunctions pass to Mathlib's derived categories and then, along the comparison
equivalences, to the derived categories of dg modules (`CupCap.derivedBlackEFAdjunction`,
`CupCap.derivedPlusEFAdjunction`). Taking adjoints (`CupCap.coevaluationRightAdjointCommIso`)
of the isomorphism `𝕂 ⋙ 𝔈_i ≅ 𝔈_i ⋙ 𝕂` (`CupCap.capEDerivedIsoMid`, `CupCap.capEDerivedIsoTop`)
gives `𝔉_i ⋙ RHom(K_{{i} + ν}, -) ≅ RHom(K_ν, -) ⋙ 𝔉_i`.

## Main definitions

* `CupCap.blackEFAdjunction`: `blackE ⊣ blackF` on modules (Theorem 4.31).
* `CupCap.plusEFAdjunction`: restriction left adjoint to induction along appending a black
  strand in `T^{λ⁺}` (Theorem 4.31 on the `λ⁺` side).
* `CupCap.derivedBlackEFAdjunction`: `derivedBlackE ⊣ derivedBlackF`.
* `CupCap.derivedPlusEFAdjunction`: `derivedPlusE ⊣ derivedPlusF`.
* `CupCap.capFRightAdjointIsoMid`, `CupCap.capFRightAdjointIsoTop`:
  `𝔉_i ⋙ RHom(K_{{i} + ν}, -) ≅ RHom(K_ν, -) ⋙ 𝔉_i`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIsoMid`; `IsRouquierQ C Q` over a field is Webster's setting for
Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

/-! ### `𝔈_i ⊣ 𝔉_i` on modules -/

section Modules

universe u

variable {I : Type u} [inst : DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

/-- **`𝔈_i ⊣ 𝔉_i` on right `T^λ`-modules** (Webster, arXiv:1309.3796v3, Theorem 4.31), for
Rouquier polynomials over a field: `clBlackResIndAdjunctionQ` for the presentation with no
extra relations, at the given decidable equality on the colours. -/
def blackEFAdjunction (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) :
    blackE Q Λ i ν ⊣ blackF Q Λ i ν := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  exact clBlackResIndAdjunctionQ.{u, 0} (hQ := hRq)
    (P := ⟨PEmpty, PEmpty.elim, PEmpty.elim, fun r => r.elim⟩)
    (fun r => r.elim) (fun r => r.elim) i ν

end Modules

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
set_option hygiene false in
local notation "aB" => appendBlackOp Q (plusLabels Λ Λc j hj) i (ν + ν₀)

variable (k Q Λ Λc j hj ν₀) in
/-- **`𝔈_i ⊣ 𝔉_i` on right `T^{λ⁺}`-modules** (Webster, arXiv:1309.3796v3, Theorem 4.31 on
the `λ⁺` side): restriction along appending a black strand (`appendBlackTPAOp`) is left
adjoint to induction along it, for Rouquier polynomials over a field. Transported from
`CupCap.blackEFAdjunction` for the labels `λ⁺` along `plusWeightOp`. -/
def plusEFAdjunction (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q) :
    resFunctor.{0, 0} aT ⊣ InductionAlong.functor.{0, 0} aT :=
  resIndAdjunctionTransport.{0, 0} (RingEquiv.refl _)
    (plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm
    (fun t => ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm_apply_apply (aB t)).symm)
    (blackEFAdjunction Q (plusLabels Λ Λc j hj) i (ν + ν₀) C hRq)

private theorem blackF_additive_capEF : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

private theorem blackE_additive_capEF : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (resFunctor.{0, 0} (appendBlackOp Q Λ i ν)).Additive

attribute [local instance] blackF_additive_capEF blackE_additive_capEF

/-! ### `𝔈_i ⊣ 𝔉_i` on derived categories of dg modules -/

section Adjunctions

variable [DG.HasDerivedCategory.{0, 0} TAᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TAᵢᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TAᵢᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **`𝔈_i ⊣ 𝔉_i` on derived categories of dg modules** over `T^λ` (Webster,
arXiv:1309.3796v3, Theorem 4.31), the derived form of `CupCap.blackEFAdjunction`, for Rouquier
polynomials over a field. -/
def derivedBlackEFAdjunction : derivedBlackE.{0} Q Λ i ν ⊣ derivedBlackF.{0} Q Λ i ν :=
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  adjunctionOfComparison (derivedComparisonEquivalence.{0, 0} TAᵢᵐᵒᵖ)
    (derivedComparisonEquivalence.{0, 0} TAᵐᵒᵖ)
    (derivedBlackResIndAdjunction.{0} Q Λ i ν C hRq (blackEFAdjunction Q Λ i ν C hRq))
    (derivedBlackEComparisonIso.{0, 0} Q Λ i ν) (derivedBlackFComparisonIso.{0, 0} Q Λ i ν C hRq)

/-- **`𝔈_i ⊣ 𝔉_i` on derived categories of dg modules** over `T^{λ⁺}` (Webster,
arXiv:1309.3796v3, Theorem 4.31 on the `λ⁺` side), the derived form of
`CupCap.plusEFAdjunction`, for Rouquier polynomials over a field. -/
def derivedPlusEFAdjunction :
    derivedPlusE.{0} k Q Λ Λc j hj ν₀ ν i ⊣ derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i :=
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits aT
  letI := functor_preservesFiniteColimits aT
  adjunctionOfComparison (derivedComparisonEquivalence.{0, 0} TPpᵢᵐᵒᵖ)
    (derivedComparisonEquivalence.{0, 0} TPpᵐᵒᵖ)
    (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).mapDerivedCategory
    (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)
    (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)

end Adjunctions

/-! ### `𝔉_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔉_i` -/

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
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **`𝔉_i ⋙ RHom(K_{{i} + ν}, -) ≅ RHom(K_ν, -) ⋙ 𝔉_i` for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, by taking adjoints of the part for `𝔈_i`
along `𝔈_i ⊣ 𝔉_i` of Theorem 4.31).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capFRightAdjointIsoMid (h : j < ℓ) :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙
        coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ⋙ derivedBlackF.{0} Q Λ i ν :=
  coevaluationRightAdjointCommIso (derivedBlackEFAdjunction ν i C hRq)
    (derivedPlusEFAdjunction ν i C hRq)
    (capEDerivedIsoMid.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h)

/-- **`𝔉_i ⋙ RHom(K_{{i} + ν}, -) ≅ RHom(K_ν, -) ⋙ 𝔉_i` for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, by taking adjoints of the part for `𝔈_i`
along `𝔈_i ⊣ 𝔉_i` of Theorem 4.31).

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `hRq` is
Webster's setting for Theorem 4.31. -/
def capFRightAdjointIsoTop (h : ¬ j < ℓ) :
    derivedPlusF.{0} k Q Λ Λc j hj ν₀ ν i ⋙
        coevaluationRightAdjoint k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L ≅
      coevaluationRightAdjoint k Q Λ Λc j hj ν ν₀ L ⋙ derivedBlackF.{0} Q Λ i ν :=
  coevaluationRightAdjointCommIso (derivedBlackEFAdjunction ν i C hRq)
    (derivedPlusEFAdjunction ν i C hRq)
    (capEDerivedIsoTop.{0, 0} ν i hL hQ hκ hP hPL hfin hproj h)

end Cases

end Categorification.Stendhal.CupCap
