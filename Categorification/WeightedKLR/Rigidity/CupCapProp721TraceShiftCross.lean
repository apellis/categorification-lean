/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftE

/-!
# `𝔈_i² 𝕋 ≅ 𝕋 𝔈_i²` and `𝔉_i² 𝕋 ≅ 𝕋 𝔉_i²`: the crossing

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21, for the quantum trace `𝕋` of Definition 7.18 with its homological shift.
The isomorphisms `CupCap.capFQuantumTraceShiftIso` and `CupCap.capEQuantumTraceShiftIso` are
conjugates of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` and `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` followed by the shift. The
conjugate of a pasted square followed by the shift is the pasting of the shifted conjugates
(`CupCap.rightAdjointShiftCommIso_squarePaste`), so the pasted `𝕋` isomorphisms carry the
conjugate crossing to the conjugate crossing as soon as the conjugate crossing on the target
commutes with the shift. With the induced shift compatibilities
(`CupCap.derivedBlackFAdjointCommShift`, `CupCap.derivedBlackEAdjointCommShift`) the composite
adjunctions commute with the shift, so this reduces to the
crossing `CupCap.dgBlackCross` on `𝔈_i²` (resp. `CupCap.dgBlackFCross` on `𝔉_i²`) commuting
with the derived tensor shift: the named hypothesis `hcross` (tracked).

## Main results

* `CupCap.rightAdjointShiftCommIso_squarePaste` (generic).
* `CupCap.dgBlackFCrossMate_adjointCommShift`, `CupCap.dgBlackECrossMate_adjointCommShift`.
* `CupCap.capFQuantumTraceShiftIso_cross`, `CupCap.capEQuantumTraceShiftIso_cross`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capEDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31;
named hypothesis `hcross` as above.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory

section Generic

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {B₁ : Type u₄} {B₂ : Type u₅}
  {B₃ : Type u₆} [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]
  [Category.{v₄} B₁] [Category.{v₅} B₂] [Category.{v₆} B₃]
  {K₁ : A₁ ⥤ B₁} {T₁ : B₁ ⥤ A₁} {K₂ : A₂ ⥤ B₂} {T₂ : B₂ ⥤ A₂} {K₃ : A₃ ⥤ B₃} {T₃ : B₃ ⥤ A₃}
  {EA : A₁ ⥤ A₂} {FA : A₂ ⥤ A₁} {EB : B₁ ⥤ B₂} {FB : B₂ ⥤ B₁}
  {EA' : A₂ ⥤ A₃} {FA' : A₃ ⥤ A₂} {EB' : B₂ ⥤ B₃} {FB' : B₃ ⥤ B₂}
  [HasShift A₁ ℤ] [HasShift A₂ ℤ] [HasShift A₃ ℤ] [FA.CommShift ℤ] [FA'.CommShift ℤ]

/-- **The shifted conjugate of a pasted square is the pasting of the shifted conjugates**, for
the shift compatibility of the composite `F_A' ⋙ F_A` composed from those of the factors. -/
theorem rightAdjointShiftCommIso_squarePaste (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂)
    (adj₃ : K₃ ⊣ T₃) (adjA : EA ⊣ FA) (adjB : EB ⊣ FB) (adjA' : EA' ⊣ FA') (adjB' : EB' ⊣ FB')
    (c₁ : K₁ ⋙ EB ≅ EA ⋙ K₂) (c₂ : K₂ ⋙ EB' ≅ EA' ⋙ K₃) (n : ℤ) :
    rightAdjointShiftCommIso adj₁ adj₃ (adjA.comp adjA') (adjB.comp adjB')
        (squarePaste c₂.symm c₁.symm).symm n =
      squarePaste (rightAdjointShiftCommIso adj₁ adj₂ adjA adjB c₁ n)
        (rightAdjointShiftCommIso adj₂ adj₃ adjA' adjB' c₂ n) := by
  have h := rightAdjointCommIso_squarePaste adj₁ adj₂ adj₃ adjA adjB adjA' adjB' c₁ c₂
  ext x
  have hx := congrArg (fun e => e.hom.app x) h
  simp only [squarePaste_hom_app] at hx
  simp only [rightAdjointShiftCommIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, squarePaste_hom_app, Functor.comp_obj]
  rw [hx, Functor.commShiftIso_comp_inv_app, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (FA.commShiftIso n).inv.naturality _

end Generic

open KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

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
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
set_option hygiene false in
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)

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
  (C : QuantumGroup.CartanDatum I) (hRq : IsRouquierQ C Q)

/-- **The conjugate crossing on `𝔉_i²` commutes with the induced shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), provided the crossing `CupCap.dgBlackCross`
on `𝔈_i²` commutes with the derived tensor shift (named hypothesis `hcross`). -/
theorem dgBlackFCrossMate_adjointCommShift
    (hcross : NatTrans.CommShift (dgBlackCross.{0, 0} (Q := Q) (Λ := Λ) ν i) ℤ) :
    letI := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
    letI := derivedBlackFAdjointCommShift (Λ := Λ) νᵢ i C hRq
    NatTrans.CommShift (dgBlackFCrossMate (Λ := Λ) ν i C hRq) ℤ := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
  let := derivedBlackFAdjointCommShift (Λ := Λ) νᵢ i C hRq
  have := derivedBlackEFAdjunction_adjointCommShift (Λ := Λ) ν i C hRq
  have := derivedBlackEFAdjunction_adjointCommShift (Λ := Λ) νᵢ i C hRq
  exact conjugateEquiv_commShift ℤ _ _ _

/-- **The conjugate crossing on `𝔈_i²` commutes with the induced shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), provided the crossing
`CupCap.dgBlackFCross` on `𝔉_i²` commutes with the derived tensor shift (named hypothesis
`hcross`). -/
theorem dgBlackECrossMate_adjointCommShift (hQ : KLRSymm Q)
    (hcross :
      letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
      letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
      letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
      letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
      NatTrans.CommShift (dgBlackFCross.{0, 0} (Q := Q) (Λ := Λ) ν i C hRq hQ) ℤ) :
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
    letI := derivedBlackEAdjointCommShift (Λ := Λ) νᵢ i C hRq
    NatTrans.CommShift (dgBlackECrossMate (Λ := Λ) ν i C hRq hQ) ℤ := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
  let := derivedBlackEAdjointCommShift (Λ := Λ) νᵢ i C hRq
  have := derivedBlackFEAdjunction_adjointCommShift (Λ := Λ) ν i C hRq
  have := derivedBlackFEAdjunction_adjointCommShift (Λ := Λ) νᵢ i C hRq
  have := blackF_preservesFiniteLimits Q Λ i ν C hRq
  have := blackF_preservesFiniteColimits Q Λ i ν C hRq
  have := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
  have := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
  exact conjugateEquiv_commShift ℤ _ _ _

variable {ν i}

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hQ : KLRSymm Q) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
  (shift : ℤ)

variable (ν i)

/-- **`𝔉⁺_i² ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i²` carries the crossing to the crossing** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, the quantum trace with
homological shift `shift` and the pasting of two copies of `CupCap.capFQuantumTraceShiftIso`,
with the crossings on `𝔉_i²` and `𝔉⁺_i²` the conjugates of those on `𝔈_i²` and `𝔈⁺_i²`.
Named hypothesis (tracked): `hcross`, the crossing `CupCap.dgBlackCross` on `𝔈_i²` commutes
with the derived tensor shift. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`. -/
theorem capFQuantumTraceShiftIso_cross
    (hcross : NatTrans.CommShift (dgBlackCross.{0, 0} (Q := Q) (Λ := Λ) ν i) ℤ) :
    Functor.whiskerRight (dgPlusFCrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj νᵢᵢ ν₀ L shift) ≫
        (squarePaste (capFQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom =
      (squarePaste (capFQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capFQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift)
          (dgBlackFCrossMate ν i C hRq) := by
  let := derivedBlackFAdjointCommShift (Λ := Λ) ν i C hRq
  let := derivedBlackFAdjointCommShift (Λ := Λ) νᵢ i C hRq
  rw [capFQuantumTraceShiftIso, capFQuantumTraceShiftIso, quantumTraceCommIso,
    quantumTraceCommIso, ← rightAdjointShiftCommIso_squarePaste]
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackFCrossMate_adjointCommShift (Λ := Λ) ν i C hRq hcross)
    (capEDerivedIso_cross ν i hL hQ hκ hP hPL hfin hproj) shift

/-- **`𝔈⁺_i² ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i²` carries the crossing to the crossing** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, the quantum trace with
homological shift `shift` and the pasting of two copies of `CupCap.capEQuantumTraceShiftIso`,
with the crossings on `𝔈_i²` and `𝔈⁺_i²` the conjugates of those on `𝔉_i²` and `𝔉⁺_i²`.
Named hypothesis (tracked): `hcross`, the crossing `CupCap.dgBlackFCross` on `𝔉_i²` commutes
with the derived tensor shift. Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`,
`hfin`, `hproj`. -/
theorem capEQuantumTraceShiftIso_cross
    (hcross :
      letI := blackF_preservesFiniteLimits Q Λ i ν C hRq
      letI := blackF_preservesFiniteColimits Q Λ i ν C hRq
      letI := blackF_preservesFiniteLimits Q Λ i νᵢ C hRq
      letI := blackF_preservesFiniteColimits Q Λ i νᵢ C hRq
      NatTrans.CommShift (dgBlackFCross.{0, 0} (Q := Q) (Λ := Λ) ν i C hRq hQ) ℤ) :
    Functor.whiskerRight (dgPlusECrossMate k Q Λ Λc j hj ν₀ ν i C hRq hQ)
        (quantumTraceFunctor k Q Λ Λc j hj ν ν₀ L shift) ≫
        (squarePaste (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capEQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom =
      (squarePaste (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift)
          (capEQuantumTraceShiftIso νᵢ i C hRq hL hQ hκ hP hPL hfin hproj shift)).hom ≫
        Functor.whiskerLeft (quantumTraceFunctor k Q Λ Λc j hj νᵢᵢ ν₀ L shift)
          (dgBlackECrossMate ν i C hRq hQ) := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
  let := derivedBlackEAdjointCommShift (Λ := Λ) νᵢ i C hRq
  rw [capEQuantumTraceShiftIso, capEQuantumTraceShiftIso, quantumTraceCommIso,
    quantumTraceCommIso, ← rightAdjointShiftCommIso_squarePaste]
  exact rightAdjointShiftCommIso_whisker _ _ _ _ _ _ _ _
    (dgBlackECrossMate_adjointCommShift (Λ := Λ) ν i C hRq hQ hcross)
    (capFDerivedIso_cross ν i hL hQ hκ hP hPL hfin hproj C hRq) shift

end Categorification.Stendhal.CupCap
