/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721FDotMateDirect
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotMatePlus
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDot

/-!
# The conjugate dot on `𝔉⁺_i` is the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the dots of the categorical action on derived categories, §4.6), on the `λ⁺`
side. On derived categories of dg modules over `T^{λ⁺}`, the dot on `𝔉⁺_i` was defined in two
ways: directly, as the conjugate along the comparison isomorphism of the derived dot
`indDotOfEq` on induction along `appendBlackOpOfEq` (`CupCap.dgPlusFDot`), and as the conjugate
along `𝔈⁺_i ⊣ 𝔉⁺_i` of the dot on `𝔈⁺_i` (`CupCap.dgPlusFDotMate`). They agree
(`CupCap.dgPlusFDotMate_eq_dgPlusFDot`).

The adjunction `𝔈⁺_i ⊣ 𝔉⁺_i` (`CupCap.plusEFAdjunction`) is along `appendBlackTPAOp` and is
transported from `CupCap.blackEFAdjunction` for the labels `λ⁺`, so its trace is symmetric
against the cast of the dot (`CupCap.plusEFAdjunction_conjugate_dot`, from
`CupCap.blackEFAdjunction_trace_dot` and `CupCap.resIndTrace_transport_cyclic`). The dots use
`appendBlackOpOfEq`; the two ring maps agree pointwise (`CupCap.appendBlackTPAOp_eq_ofEq`), and
the identifications `resFunctorIsoOfEq`, `indFunctorIsoOfEq` carry the dots to each other
(`CupCap.resFunctorIsoOfEq_plusResDot`, `CupCap.indFunctorIsoOfEq_plusIndDot`).

## Main definitions

* `CupCap.plusResDot`: the dot on restriction along `appendBlackTPAOp`.

## Main results

* `CupCap.IsComparisonConj.of_trans_whiskerLeft`.
* `CupCap.plusEFAdjunction_conjugate_dot`.
* `CupCap.dgPlusFDotMate_eq_dgPlusFDot`.

Route hypotheses: none beyond `C`, `hRq : IsRouquierQ C Q` (Webster's setting for
Theorem 4.31).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory Limits KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Conj

variable {𝒟₁ 𝒟₂ D₁ D₂ : Type*} [Category* 𝒟₁] [Category* 𝒟₂] [Category* D₁] [Category* D₂]
  {Φ₁ : 𝒟₁ ⥤ D₁} {Φ₂ : 𝒟₂ ⥤ D₂} {X X' : 𝒟₁ ⥤ 𝒟₂} {Xh Xh' Xh₂ Xh₂' : D₁ ⥤ D₂}

/-- **Removing an isomorphism from both sides of a conjugacy** (the converse direction of
`CupCap.IsComparisonConj.trans_whiskerLeft`). -/
theorem IsComparisonConj.of_trans_whiskerLeft {cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh}
    {cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh'} {γ : Xh ≅ Xh₂} {γ' : Xh' ≅ Xh₂'} {αh : Xh ⟶ Xh'}
    {αh₂ : Xh₂ ⟶ Xh₂'} {α : X ⟶ X'}
    (hα : IsComparisonConj (cX ≪≫ Functor.isoWhiskerLeft Φ₁ γ)
      (cX' ≪≫ Functor.isoWhiskerLeft Φ₁ γ') αh₂ α)
    (h : γ.hom ≫ αh₂ = αh ≫ γ'.hom) : IsComparisonConj cX cX' αh α := fun x => by
  have h' := congrArg (fun t => NatTrans.app t (Φ₁.obj x)) h
  simp only [NatTrans.comp_app] at h'
  rw [hα x]
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc, reassoc_of% h',
    Iso.hom_inv_id_app_assoc]

end Conj

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "aB" => appendBlackOp Q (plusLabels Λ Λc j hj) i (ν + ν₀)
set_option hygiene false in
local notation "ph" => plusWeight_assoc ν ν₀ i
set_option hygiene false in
local notation "c₀" =>
  castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
    (op (appendedDot Q (plusLabels Λ Λc j hj) i (ν + ν₀)))

/-! ### On modules -/

/-- The cast of the dot commutes with the image of `appendBlackTPAOp`. -/
theorem plusDot_commute (t : TPpᵐᵒᵖ) : c₀ * aT t = aT t * c₀ := by
  rw [appendBlackTPAOp_eq_ofEq]
  exact castOp_appendedDot_commute Q _ i ph t

variable (k Q Λ Λc j hj ν₀) in
/-- **The dot on `𝔈⁺_i` along `appendBlackTPAOp`**: left multiplication by the cast of the dot
on the appended strand. -/
def plusResDot : resFunctor.{0, 0} aT ⟶ resFunctor.{0, 0} aT where
  app M := ModuleCat.ofHom (resAct c₀ (plusDot_commute ν i) M)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext
    (f.hom.map_smul c₀ r.val).symm)

/-- The dot on restriction along a content equality is left multiplication by the cast dot. -/
theorem resDotOfEq_app_eq_resAct {n : ℕ} (Λ' : Fin n → I →₀ ℕ) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (M : ModuleCat.{0} (TensorProductAlgebra k Q Λ' β)ᵐᵒᵖ) :
    (resDotOfEq Q Λ' i h).app M =
      ModuleCat.ofHom (resAct _ (castOp_appendedDot_commute Q Λ' i h) M) := by
  subst h; rfl

/-- **`resFunctorIsoOfEq` carries the dot to the dot.** -/
theorem resFunctorIsoOfEq_plusResDot :
    (resFunctorIsoOfEq.{0, 0} (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)).hom ≫
        resDotOfEq Q (plusLabels Λ Λc j hj) i ph =
      plusResDot k Q Λ Λc j hj ν₀ ν i ≫
        (resFunctorIsoOfEq.{0, 0} (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)).hom := by
  ext M : 2
  rw [NatTrans.comp_app, NatTrans.comp_app, resDotOfEq_app_eq_resAct]
  exact ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext rfl)

/-- The conjugate of `plusResDot` along induction ⊣ restriction is right multiplication. -/
theorem conjugateEquiv_symm_plusResDot :
    (conjugateEquiv (InductionAlong.adjunction.{0, 0} aT) (InductionAlong.adjunction aT)).symm
        (plusResDot k Q Λ Λc j hj ν₀ ν i) =
      natTrans.{0, 0} (intertwines_of_commute (plusDot_commute (k := k) (Q := Q) (Λ := Λ)
        (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i)) :=
  NatTrans.ext (funext fun N => conjugateEquiv_symm_resAct_app (plusDot_commute ν i) _
    (fun _ => rfl) N)

/-- **`indFunctorIsoOfEq` carries the dot to the dot.** -/
theorem indFunctorIsoOfEq_plusIndDot :
    (indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)).hom ≫
        indDotOfEq Q (plusLabels Λ Λc j hj) i ph =
      (conjugateEquiv (InductionAlong.adjunction.{0, 0} aT) (InductionAlong.adjunction aT)).symm
          (plusResDot k Q Λ Λc j hj ν₀ ν i) ≫
        (indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)).hom := by
  rw [conjugateEquiv_symm_plusResDot, indDotOfEq_eq_natTrans]
  change natTrans _ ≫ natTrans _ = natTrans _ ≫ natTrans _
  rw [natTrans_comp, natTrans_comp]
  exact natTrans_congr _ (plusDot_commute ν i 1).symm

variable (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The trace of `𝔈⁺_i ⊣ 𝔉⁺_i` is symmetric against the dot** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the `λ⁺` side), transported from `CupCap.blackEFAdjunction_trace_dot`. -/
theorem plusEFAdjunction_conjugate_dot :
    conjugateEquiv (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq)
        (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq) (plusResDot k Q Λ Λc j hj ν₀ ν i) =
      (conjugateEquiv (InductionAlong.adjunction.{0, 0} aT) (InductionAlong.adjunction aT)).symm
        (plusResDot k Q Λ Λc j hj ν₀ ν i) := by
  have he : (plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm c₀ =
      op (appendedDot Q (plusLabels Λ Λc j hj) i (ν + ν₀)) := by
    rw [castOp_op]
    exact (plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm_apply_apply _
  refine conjugateEquiv_resAct_eq_of_trace _ (plusDot_commute ν i) _ (fun _ => rfl)
    fun z hz => ?_
  exact resIndTrace_transport_cyclic (RingEquiv.refl _) (plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm
    (fun t => ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm_apply_apply (aB t)).symm)
    (blackEFAdjunction Q (plusLabels Λ Λc j hj) i (ν + ν₀) C hRq) (plusDot_commute ν i)
    (resIndTrace_cyclic_of_eq _ he
      (transport_commute (RingEquiv.refl _) (plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm
        (fun t => ((plusWeightOp k Q Λ Λc j hj ν ν₀ i).symm_apply_apply (aB t)).symm)
        (plusDot_commute ν i))
      (op_appendedDot_commute Q _ i _)
      (blackEFAdjunction_trace_dot Q (plusLabels Λ Λc j hj) i (ν + ν₀) C hRq)) z hz

/-! ### On derived categories -/

set_option hygiene false in
local notation "Fᵖ" => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)
set_option hygiene false in
local notation "Eᵖ" => blackEOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)

private theorem blackFOfEq_additive_fDotMatePlus : Fᵖ.Additive :=
  inferInstanceAs (InductionAlong.functor.{0, 0} _).Additive

private theorem blackEOfEq_additive_fDotMatePlus : Eᵖ.Additive :=
  inferInstanceAs (resFunctor.{0, 0} _).Additive

private theorem blackEOfEq_limits_fDotMatePlus : PreservesFiniteLimits Eᵖ :=
  inferInstanceAs (PreservesFiniteLimits (resFunctor.{0, 0} _))

private theorem blackEOfEq_colimits_fDotMatePlus : PreservesFiniteColimits Eᵖ :=
  inferInstanceAs (PreservesFiniteColimits (resFunctor.{0, 0} _))

attribute [local instance] blackFOfEq_additive_fDotMatePlus blackEOfEq_additive_fDotMatePlus
  blackEOfEq_limits_fDotMatePlus blackEOfEq_colimits_fDotMatePlus

variable [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ({i} + ν))ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} TPpᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} TPpᵢᵐᵒᵖ]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ({i} + ν))ᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵐᵒᵖ)]
  [HasDerivedCategory.{0} (ModuleCat.{0} TPpᵢᵐᵒᵖ)]

set_option linter.unusedSectionVars false in
/-- **The conjugate dot on `𝔉⁺_i` is the dot** (Webster, arXiv:1309.3796v3, Theorem 4.31, §4.6
and §7.3, proof of Proposition 7.21): on derived categories of dg modules over `T^{λ⁺}`, the
conjugate along `𝔈⁺_i ⊣ 𝔉⁺_i` of the dot on `𝔈⁺_i` is the dot on `𝔉⁺_i`. -/
theorem dgPlusFDotMate_eq_dgPlusFDot :
    letI := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
    letI := functor_preservesFiniteLimits aT
    letI := functor_preservesFiniteColimits aT
    letI := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
    letI := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
    dgPlusFDotMate k Q Λ Λc j hj ν₀ ν i C hRq = dgPlusFDot.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq := by
  let := projective_plusCorner k Q Λ Λc j hj ν₀ ν i C hRq
  let := functor_preservesFiniteLimits aT
  let := functor_preservesFiniteColimits aT
  let := blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  let := blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  let : PreservesFiniteLimits (InductionAlong.functor.{0, 0}
      (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))) :=
    blackFOfEqPlus_preservesFiniteLimits k Q Λ Λc j hj ν₀ ν i
  let : PreservesFiniteColimits (InductionAlong.functor.{0, 0}
      (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i))) :=
    blackFOfEqPlus_preservesFiniteColimits k Q Λ Λc j hj ν₀ ν i
  have he := appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i
  have hder := conjugateEquiv_mapDerivedCategory (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq)
    (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq) (plusResDot k Q Λ Λc j hj ν₀ ν i)
  rw [plusEFAdjunction_conjugate_dot] at hder
  refine conjugateEquiv_eq_of_comparison
    (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)
    (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq)
    (adj' := (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).mapDerivedCategory)
    (fun d => adjunctionOfComparison_counit_map (derivedComparisonEquivalence.{0, 0} TPpᵢᵐᵒᵖ)
      (derivedComparisonEquivalence.{0, 0} TPpᵐᵒᵖ)
      (plusEFAdjunction k Q Λ Λc j hj ν₀ ν i C hRq).mapDerivedCategory
      (derivedPlusEComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i)
      (derivedPlusFComparisonIso.{0, 0} k Q Λ Λc j hj ν₀ ν i C hRq) d)
    _ _ hder _ _ ?_ ?_
  · refine IsComparisonConj.of_trans_whiskerLeft (γ := mapDerivedCategoryIsoOfIso
      (resFunctorIsoOfEq.{0, 0} he)) (γ' := mapDerivedCategoryIsoOfIso
      (resFunctorIsoOfEq.{0, 0} he)) (isComparisonConj_comparisonConj _ _ _ _) ?_
    rw [mapDerivedCategoryIsoOfIso_hom_eq, ← NatTrans.mapDerivedCategory_comp,
      ← NatTrans.mapDerivedCategory_comp, resFunctorIsoOfEq_plusResDot]
  · refine IsComparisonConj.of_trans_whiskerLeft (γ := mapDerivedCategoryIsoOfIso
      (indFunctorIsoOfEq he)) (γ' := mapDerivedCategoryIsoOfIso
      (indFunctorIsoOfEq he)) (isComparisonConj_comparisonConj _ _ _ _) ?_
    rw [mapDerivedCategoryIsoOfIso_hom_eq, ← NatTrans.mapDerivedCategory_comp,
      ← NatTrans.mapDerivedCategory_comp, indFunctorIsoOfEq_plusIndDot]

end Categorification.Stendhal.CupCap
