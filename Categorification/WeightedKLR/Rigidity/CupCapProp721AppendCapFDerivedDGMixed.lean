/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDerivedDGTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFMixedCap

/-!
# `𝕂 ∘ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ∘ 𝕂` and the mixed crossing, on derived categories of dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`. The crossing of two strands of different colours `a ≠ b`
relates `𝔉_a 𝔉_b` and `𝔉_b 𝔉_a`, whose contents agree only up to the equality `mixedSwap`. On
the dg side, `𝔉_i` along a content equality `h : {i} + ν = β` is `derivedBlackF` transported
along `h` (`CupCap.derivedBlackFOfEq`), and likewise on the `λ⁺` side
(`CupCap.derivedPlusFOfEq`); `CupCap.capFDerivedIsoOfData'` is `CupCap.capFDerivedIsoOfData`
transported along `h`, conjugate to the derived `CupCap.capFOrdIsoOfEq'`. The mixed crossings
on the dg side are the conjugates of the derived crossings `indCrossOfEq`
(`CupCap.dgBlackFMixedCross`, `CupCap.dgPlusFMixedCross`), and the module-level compatibility
passes to the dg side (`CupCap.capFDerivedIsoPaste'_mixedCross`).

The exactness of `𝔉_i` and `𝔉⁺_i` (Theorem 4.31) enters as instance arguments; inside the
proofs it is supplied from `C` and `hRq : IsRouquierQ C Q`.
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] OpBimodule.projective_opOp

section Additive

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) {μ β : Multiset I}
  (h : ({i} : Multiset I) + μ = β)

private theorem blackF_additive_capFMix (ν : Multiset I) : (blackF Q Λ' i ν).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOp Q Λ' i ν)).Additive

private theorem blackFOfEq_additive_capFMix : (blackFOfEq Q Λ' i h).Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} (appendBlackOpOfEq Q Λ' i h)).Additive

end Additive

attribute [local instance] blackF_additive_capFMix blackFOfEq_additive_capFMix

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
set_option hygiene false in
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
set_option hygiene false in
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))
set_option hygiene false in
local notation "aT" μ:max i':max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i'
set_option hygiene false in
local notation "Fᵖ" μ:max i':max =>
  blackFOfEq Q (plusLabels Λ Λc j hj) i' (plusWeight_assoc μ ν₀ i')

/-! ### `𝔉_i` along a content equality -/

section OfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TA β)ᵐᵒᵖ]

variable (Q Λ) in
/-- **`𝔉_i` on derived categories of dg modules along a content equality** `{i} + ν = β`:
`derivedBlackF` transported along the equality. -/
def derivedBlackFOfEq :
    DG.DerivedCategory.{w} (TA ν)ᵐᵒᵖ ⥤ DG.DerivedCategory.{w} (TA β)ᵐᵒᵖ := by
  subst h
  exact derivedBlackF.{w} Q Λ i ν

variable [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]
  [Limits.PreservesFiniteLimits (blackFOfEq Q Λ i h)]
  [Limits.PreservesFiniteColimits (blackFOfEq Q Λ i h)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

variable (Q Λ) in
/-- The comparison isomorphism of `CupCap.derivedBlackFOfEq` with the derived `blackFOfEq`. -/
def derivedBlackFOfEqComparisonIso :
    derivedBlackFOfEq.{w} Q Λ h ⋙ derivedComparison.{w, w'} (TA β)ᵐᵒᵖ ≅
      derivedComparison.{w, w'} (TA ν)ᵐᵒᵖ ⋙ (blackFOfEq Q Λ i h).mapDerivedCategory := by
  subst h
  exact derivedBlackFComparisonIso.{w, w'} Q Λ i ν C hRq

end OfEq

section PlusOfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp β)ᵐᵒᵖ]

variable (k Q Λ Λc j hj ν₀) in
/-- **`𝔉⁺_i` on derived categories of dg modules along a content equality** `{i} + ν = β`:
`CupCap.derivedPlusF` transported along the equality. -/
def derivedPlusFOfEq :
    DG.DerivedCategory.{w} (TPp ν)ᵐᵒᵖ ⥤ DG.DerivedCategory.{w} (TPp β)ᵐᵒᵖ := by
  subst h
  exact derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν i

variable [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp β)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

variable (k Q Λ Λc j hj ν₀) in
/-- The comparison isomorphism of `CupCap.derivedPlusFOfEq` with the derived `blackFOfEq` for
any `hp : {i} + (ν + ν₀) = β + ν₀`. -/
def derivedPlusFOfEqComparisonIso (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀)
    [Limits.PreservesFiniteLimits (blackFOfEq Q (plusLabels Λ Λc j hj) i hp)]
    [Limits.PreservesFiniteColimits (blackFOfEq Q (plusLabels Λ Λc j hj) i hp)] :
    derivedPlusFOfEq.{w} k Q Λ Λc j hj ν₀ h ⋙ derivedComparison.{w, w'} (TPp β)ᵐᵒᵖ ≅
      derivedComparison.{w, w'} (TPp ν)ᵐᵒᵖ ⋙
        (blackFOfEq Q (plusLabels Λ Λc j hj) i hp).mapDerivedCategory := by
  subst h
  letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
  letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
  letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  letI := functor_preservesFiniteLimits (aT ν i)
  letI := functor_preservesFiniteColimits (aT ν i)
  exact derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν i C hRq

end PlusOfEq

section DataOfEq

variable {ν : Multiset I} {i : I} {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TA β)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp β)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA β)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp β)ᵐᵒᵖ)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **`𝕂 ⋙ 𝔉_i ≅ 𝔉_i ⋙ 𝕂` along a content equality** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21): `CupCap.capFDerivedIsoOfData` transported along `h`. -/
def capFDerivedIsoOfData' (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    [Module.Projective (TA ν) (CB ν)] [Module.Projective (TA β) (CB β)] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙
        derivedPlusFOfEq.{w} k Q Λ Λc j hj ν₀ h ≅
      derivedBlackFOfEq.{w} Q Λ h ⋙ coevaluationFunctor.{0, w} k Q Λ Λc j hj β ν₀ L := by
  subst h
  exact capFDerivedIsoOfData.{w, w'} C hRq D

variable [Limits.PreservesFiniteLimits (blackFOfEq Q Λ i h)]
  [Limits.PreservesFiniteColimits (blackFOfEq Q Λ i h)]

/-- `CupCap.capFDerivedIsoOfData'` is conjugate to the derived `CupCap.capFOrdIsoOfEq'`. -/
theorem capFDerivedIsoOfData'_isComparisonSquare (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀)
    [Limits.PreservesFiniteLimits (blackFOfEq Q (plusLabels Λ Λc j hj) i hp)]
    [Limits.PreservesFiniteColimits (blackFOfEq Q (plusLabels Λ Λc j hj) i hp)]
    [Module.Projective (TA ν) (CB ν)] [Module.Projective (TA β) (CB β)] :
    IsComparisonSquare (derivedBlackFOfEqComparisonIso.{w, w'} Q Λ h C hRq)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L β)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (derivedPlusFOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ h C hRq hp)
      (derivedSquareIso (capFOrdIsoOfEq' D h hp)) (capFDerivedIsoOfData'.{w, w'} h C hRq D) := by
  subst h
  have := blackF_preservesFiniteLimits Q Λ i ν C hRq
  have := blackF_preservesFiniteColimits Q Λ i ν C hRq
  have := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  have := functor_preservesFiniteLimits (aT ν i)
  have := functor_preservesFiniteColimits (aT ν i)
  exact capFDerivedIsoOfData_isComparisonSquareOfEq C hRq D

end DataOfEq

/-! ### Pasting along a content equality -/

section Paste

variable {ν : Multiset I} {a b : I} {δ : Multiset I}
  (h : ({a} : Multiset I) + (({b} : Multiset I) + ν) = δ)
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA (({b} : Multiset I) + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TPp (({b} : Multiset I) + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA δ)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp δ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA (({b} : Multiset I) + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp (({b} : Multiset I) + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA δ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp δ)ᵐᵒᵖ)]
  [Limits.PreservesFiniteLimits (blackF Q Λ b ν)]
  [Limits.PreservesFiniteColimits (blackF Q Λ b ν)]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} (aT ν b))]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} (aT ν b))]
  [Limits.PreservesFiniteLimits (Fᵖ ν b)]
  [Limits.PreservesFiniteColimits (Fᵖ ν b)]
  [Limits.PreservesFiniteLimits (blackFOfEq Q Λ a h)]
  [Limits.PreservesFiniteColimits (blackFOfEq Q Λ a h)]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **`𝕂 ⋙ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ⋙ 𝕂` on derived categories of dg modules** along a content
equality `{a} + ({b} + ν) = δ` (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21):
the pasting of `CupCap.capFDerivedIsoOfData` and `CupCap.capFDerivedIsoOfData'`. -/
def capFDerivedIsoPaste' (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a)
    [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA (({b} : Multiset I) + ν)) (CB (({b} : Multiset I) + ν))]
    [Module.Projective (TA δ) (CB δ)] :
    coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L ⋙
        (derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν b ⋙ derivedPlusFOfEq.{w} k Q Λ Λc j hj ν₀ h) ≅
      (derivedBlackF.{w} Q Λ b ν ⋙ derivedBlackFOfEq.{w} Q Λ h) ⋙
        coevaluationFunctor.{0, w} k Q Λ Λc j hj δ ν₀ L :=
  (squarePaste (capFDerivedIsoOfData'.{w, w'} h C hRq D₂).symm
    (capFDerivedIsoOfData.{w, w'} C hRq D₁).symm).symm

/-- **`CupCap.capFDerivedIsoPaste'` is conjugate to the derived `CupCap.capFCompIsoOfEq'`**, with
the composites of the derived functors identified with the derived functors of the composites
by `Functor.mapDerivedCategoryCompIso`. -/
theorem capFDerivedIsoPaste'_isComparisonSquare (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a)
    (hp : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = δ + ν₀)
    [Limits.PreservesFiniteLimits (blackFOfEq Q (plusLabels Λ Λc j hj) a hp)]
    [Limits.PreservesFiniteColimits (blackFOfEq Q (plusLabels Λ Λc j hj) a hp)]
    [Module.Projective (TA ν) (CB ν)]
    [Module.Projective (TA (({b} : Multiset I) + ν)) (CB (({b} : Multiset I) + ν))]
    [Module.Projective (TA δ) (CB δ)] :
    IsComparisonSquare
      (squarePaste (derivedBlackFOfEqComparisonIso.{w, w'} Q Λ h C hRq)
        (derivedBlackFComparisonIso.{w, w'} Q Λ b ν C hRq) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L δ)
      (coevaluationComparisonOrdIso.{w, w'} k Q Λ Λc j hj ν₀ L ν)
      (squarePaste (derivedPlusFOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ h C hRq hp)
        (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν b C hRq) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))
      (derivedSquareIso (capFCompIsoOfEq' D₁ D₂ h hp))
      (capFDerivedIsoPaste'.{w, w'} h C hRq D₁ D₂) :=
  (((capFDerivedIsoOfData'_isComparisonSquare h C hRq D₂ hp).paste
      (capFDerivedIsoOfData_isComparisonSquareOfEq C hRq D₁)).changeX
      (Functor.mapDerivedCategoryCompIso _ _) (eh' := Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryCompIso _ _).symm _ ≪≫ squarePaste _ _) rfl).changeY
    (Functor.mapDerivedCategoryCompIso _ _) (by
      rw [Iso.trans_hom, Category.assoc, ← derivedSquareIso_squarePaste, ← Category.assoc,
        Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp, Iso.symm_hom, Iso.inv_hom_id,
        Functor.whiskerRight_id', Category.id_comp]
      rfl)

end Paste

/-! ### The mixed crossing -/

section MixedCross

variable (ν : Multiset I) (a b : I)

set_option hygiene false in
local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
set_option hygiene false in
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
set_option hygiene false in
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

variable
  [DG.HasDerivedCategory.{w, 0} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νa)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νa)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νb)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νb)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} (TA νab)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (TPp νab)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νa)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νb)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νab)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TPp νab)ᵐᵒᵖ)]
  [Limits.PreservesFiniteLimits (blackF Q Λ a ν)]
  [Limits.PreservesFiniteColimits (blackF Q Λ a ν)]
  [Limits.PreservesFiniteLimits (blackF Q Λ b ν)]
  [Limits.PreservesFiniteColimits (blackF Q Λ b ν)]
  [Limits.PreservesFiniteLimits (blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))]
  [Limits.PreservesFiniteColimits (blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))]
  [Limits.PreservesFiniteLimits (blackFOfEq Q Λ b (mixedSwap ν a b))]
  [Limits.PreservesFiniteColimits (blackFOfEq Q Λ b (mixedSwap ν a b))]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} (aT ν a))]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} (aT ν a))]
  [Limits.PreservesFiniteLimits (InductionAlong.functor.{0, 0} (aT ν b))]
  [Limits.PreservesFiniteColimits (InductionAlong.functor.{0, 0} (aT ν b))]
  [Limits.PreservesFiniteLimits (Fᵖ ν a)]
  [Limits.PreservesFiniteColimits (Fᵖ ν a)]
  [Limits.PreservesFiniteLimits (Fᵖ ν b)]
  [Limits.PreservesFiniteColimits (Fᵖ ν b)]
  [Limits.PreservesFiniteLimits
    (blackFOfEq Q (plusLabels Λ Λc j hj) a (plusWeight_assoc νb ν₀ a))]
  [Limits.PreservesFiniteColimits
    (blackFOfEq Q (plusLabels Λ Λc j hj) a (plusWeight_assoc νb ν₀ a))]
  [Limits.PreservesFiniteLimits (blackFOfEq Q (plusLabels Λ Λc j hj) b
    (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b))]
  [Limits.PreservesFiniteColimits (blackFOfEq Q (plusLabels Λ Λc j hj) b
    (plusWeight_assoc_mixed_swap (ν₀ := ν₀) ν a b))]
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The crossing of different colours on the dg derived `𝔉_a 𝔉_b`** of right
`T^λ`-modules: the conjugate of the derived crossing `indCrossOfEq` (through
`Functor.mapDerivedCategoryCompIso`) along the pasted comparison isomorphisms. -/
def dgBlackFMixedCross (hQ : KLRSymm Q) :
    derivedBlackF.{w} Q Λ b ν ⋙ derivedBlackFOfEq.{w} Q Λ (rfl : ({a} : Multiset I) + νb = νab) ⟶
      derivedBlackF.{w} Q Λ a ν ⋙ derivedBlackFOfEq.{w} Q Λ (mixedSwap ν a b) :=
  comparisonConj (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TA νab)ᵐᵒᵖ))
    (squarePaste
      (derivedBlackFOfEqComparisonIso.{w, w'} Q Λ (rfl : ({a} : Multiset I) + νb = νab) C hRq)
      (derivedBlackFComparisonIso.{w, w'} Q Λ b ν C hRq))
    (squarePaste (derivedBlackFOfEqComparisonIso.{w, w'} Q Λ (mixedSwap ν a b) C hRq)
      (derivedBlackFComparisonIso.{w, w'} Q Λ a ν C hRq))
    ((Functor.mapDerivedCategoryCompIso (blackF Q Λ b ν)
        (blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))).hom ≫
      NatTrans.mapDerivedCategory
        (F := blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab))
        (G := blackF Q Λ a ν ⋙ blackFOfEq Q Λ b (mixedSwap ν a b))
        (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) ≫
      (Functor.mapDerivedCategoryCompIso (blackF Q Λ a ν)
        (blackFOfEq Q Λ b (mixedSwap ν a b))).inv)

variable (k Q Λ Λc j hj ν₀) in
/-- **The crossing of different colours on the dg derived `𝔉⁺_a 𝔉⁺_b`** of right
`T^{λ⁺}`-modules: the conjugate of the derived crossing `indCrossOfEq` of `T^{λ⁺}` along the
pasted comparison isomorphisms. -/
def dgPlusFMixedCross (hQ : KLRSymm Q) :
    derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν b ⋙
        derivedPlusFOfEq.{w} k Q Λ Λc j hj ν₀ (rfl : ({a} : Multiset I) + νb = νab) ⟶
      derivedPlusF.{w} k Q Λ Λc j hj ν₀ ν a ⋙
        derivedPlusFOfEq.{w} k Q Λ Λc j hj ν₀ (mixedSwap ν a b) :=
  comparisonConj
    (Functor.FullyFaithful.ofFullyFaithful (derivedComparison.{w, w'} (TPp νab)ᵐᵒᵖ))
    (squarePaste (derivedPlusFOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀
        (rfl : ({a} : Multiset I) + νb = νab) C hRq (plusWeight_assoc νb ν₀ a))
      (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν b C hRq))
    (squarePaste (derivedPlusFOfEqComparisonIso.{w, w'} k Q Λ Λc j hj ν₀ (mixedSwap ν a b) C hRq
        (plusWeight_assoc_mixed_swap ν a b))
      (derivedPlusFComparisonIsoOfEq.{w, w'} k Q Λ Λc j hj ν₀ ν a C hRq))
    ((Functor.mapDerivedCategoryCompIso (Fᵖ ν b)
        (blackFOfEq Q (plusLabels Λ Λc j hj) a (plusWeight_assoc νb ν₀ a))).hom ≫
      (indCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
        (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
        (plusWeight_assoc_mixed_swap ν a b)).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso (Fᵖ ν a)
        (blackFOfEq Q (plusLabels Λ Λc j hj) b (plusWeight_assoc_mixed_swap ν a b))).inv)

variable {ν a b}

/-- **`𝕂 ⋙ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ⋙ 𝕂` carries the crossing of different colours to the crossing on
derived categories of dg modules** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), from the module-level compatibility `hmix` for `CupCap.capFCompIsoOfEq'`. -/
theorem capFDerivedIsoPaste'_mixedCross (hQ : KLRSymm Q)
    (D_b : CapFData k Q Λ Λc j hj ν₀ L ν b) (D_ba : CapFData k Q Λ Λc j hj ν₀ L νb a)
    (D_a : CapFData k Q Λ Λc j hj ν₀ L ν a) (D_ab : CapFData k Q Λ Λc j hj ν₀ L νa b)
    [Module.Projective (TA ν) (CB ν)] [Module.Projective (TA νa) (CB νa)]
    [Module.Projective (TA νb) (CB νb)] [Module.Projective (TA νab) (CB νab)]
    (hmix : (Functor.whiskerRight (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b))
          (OrdK νab) :
        (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + νb = νab)) ⋙ OrdK νab ⟶
          (blackF Q Λ a ν ⋙ blackFOfEq Q Λ b (mixedSwap ν a b)) ⋙ OrdK νab) ≫
        (capFCompIsoOfEq' D_a D_ab (mixedSwap ν a b) (plusWeight_assoc_mixed_swap ν a b)).hom =
      (capFCompIsoOfEq' D_b D_ba rfl (plusWeight_assoc νb ν₀ a)).hom ≫
        Functor.whiskerLeft (OrdK ν)
          (indCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b))) :
    Functor.whiskerLeft (coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L)
        (dgPlusFMixedCross.{w, w'} k Q Λ Λc j hj ν₀ ν a b C hRq hQ) ≫
        (capFDerivedIsoPaste'.{w, w'} (mixedSwap ν a b) C hRq D_a D_ab).hom =
      (capFDerivedIsoPaste'.{w, w'} (rfl : ({a} : Multiset I) + νb = νab) C hRq D_b D_ba).hom ≫
        Functor.whiskerRight (dgBlackFMixedCross.{w, w'} ν a b C hRq hQ)
          (coevaluationFunctor.{0, w} k Q Λ Λc j hj νab ν₀ L) :=
  (capFDerivedIsoPaste'_isComparisonSquare rfl C hRq D_b D_ba (plusWeight_assoc νb ν₀ a)).whisker
    (capFDerivedIsoPaste'_isComparisonSquare (mixedSwap ν a b) C hRq D_a D_ab
      (plusWeight_assoc_mixed_swap ν a b))
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    ((isComparisonConj_comparisonConj _ _ _ _).trans_whiskerLeft _ _ (by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    (derivedSquareIso_whisker _ _ hmix)

end MixedCross

end Categorification.Stendhal.CupCap
