/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateDG
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftE

/-!
# Units and counits on `RHom(K, -)` and on the quantum trace `𝕋`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 and Definition 7.18. The isomorphism `𝔈⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i`
is defined by taking adjoints of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` along `𝔉_i ⊣ 𝔈_i`
(`CupCap.capERightAdjointIso`). Since the mate of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` along `𝔉_i ⊣ 𝔈_i` is
the inverse of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` (`CupCap.capFDerivedIso_hom_mate`, compatibility with the
cup and cap of `𝔉_i ⊣ 𝔈_i`), the same isomorphism is the mate of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂` along the
coevaluation adjunctions `𝕂 ⊣ RHom(K, -)` (`CupCap.capERightAdjointIso_inv_eq_mate`). The
quantum trace version, with the shift of `𝔈_i` induced by `𝔉_i ⊣ 𝔈_i`, is
`CupCap.capEQuantumTraceShiftIso_inv_eq_mate`.

The generic step is Mathlib's identification of iterated mates with conjugates
(`CupCap.rightAdjointCommIso_inv_eq_mate`, `CupCap.rightAdjointShiftCommIso_inv_eq_mate`).

## Main results

* `CupCap.capFDerivedIso_hom_mate` (every `j ≤ ℓ`).
* `CupCap.capERightAdjointIso_inv_eq_mate`, `CupCap.capEQuantumTraceShiftIso_inv_eq_mate`.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`, as for
`CupCap.capFDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong DG.DegreeZero

section Generic

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
  [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
  {K₁ : A₁ ⥤ B₁} {T₁ : B₁ ⥤ A₁} {K₂ : A₂ ⥤ B₂} {T₂ : B₂ ⥤ A₂}
  {EA : A₁ ⥤ A₂} {FA : A₂ ⥤ A₁} {EB : B₁ ⥤ B₂} {FB : B₂ ⥤ B₁}
  (adj₁ : K₁ ⊣ T₁) (adj₂ : K₂ ⊣ T₂) (adjA : EA ⊣ FA) (adjB : EB ⊣ FB)

/-- **The conjugate isomorphism is an iterated mate**: the inverse of `rightAdjointCommIso` is
the mate, along `K₂ ⊣ T₂` and `K₁ ⊣ T₁`, of the mate of `c` along `E_A ⊣ F_A`, `E_B ⊣ F_B`. -/
theorem rightAdjointCommIso_inv_eq_mate (c : K₁ ⋙ EB ≅ EA ⋙ K₂) (β : FA ⋙ K₁ ⟶ K₂ ⋙ FB)
    (hβ : (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ c.hom)).natTrans = β) :
    (rightAdjointCommIso adj₁ adj₂ adjA adjB c).inv =
      (mateEquiv adj₂ adj₁ (TwoSquare.mk _ _ _ _ β)).natTrans := by
  subst hβ
  exact (iterated_mateEquiv_conjugateEquiv adjA adjB adj₁ adj₂
    (TwoSquare.mk _ _ _ _ c.hom)).symm

/-- **The shifted conjugate isomorphism through an iterated mate**: the inverse of
`rightAdjointShiftCommIso` is the shift compatibility of `F_A` followed by the shift of the mate,
along `K₂ ⊣ T₂` and `K₁ ⊣ T₁`, of the mate of `c`. -/
theorem rightAdjointShiftCommIso_inv_eq_mate [HasShift A₁ ℤ] [HasShift A₂ ℤ] [FA.CommShift ℤ]
    (c : K₁ ⋙ EB ≅ EA ⋙ K₂) (β : FA ⋙ K₁ ⟶ K₂ ⋙ FB)
    (hβ : (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ c.hom)).natTrans = β) (n : ℤ) :
    (rightAdjointShiftCommIso adj₁ adj₂ adjA adjB c n).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft T₂ (FA.commShiftIso n).hom ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (mateEquiv adj₂ adj₁ (TwoSquare.mk _ _ _ _ β)).natTrans
          (shiftFunctor A₁ n) ≫ (Functor.associator _ _ _).hom := by
  rw [← rightAdjointCommIso_inv_eq_mate adj₁ adj₂ adjA adjB c β hβ]
  simp only [rightAdjointShiftCommIso, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc]

end Generic

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

/-- **The mate of `𝕂 ⋙ 𝔉⁺_i ≅ 𝔉_i ⋙ 𝕂` is the inverse of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`, along `𝔉_i ⊣ 𝔈_i` on
derived categories of dg modules over `T^λ` and `T^{λ⁺}`: the two commutation isomorphisms are
compatible with the cups and caps of `𝔉_i ⊣ 𝔈_i`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
theorem capFDerivedIso_hom_mate :
    (mateEquiv (derivedBlackFEAdjunction (Λ := Λ) ν i C hRq)
      (derivedPlusFEAdjunction (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i C hRq)
      (TwoSquare.mk _ _ _ _
        (capFDerivedIso ν i hL hQ hκ hP hPL hfin hproj C hRq).hom)).natTrans =
      (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).inv := by
  unfold capFDerivedIso capEDerivedIso
  split_ifs with h
  · exact capFDerivedIsoMid_hom_mate ν i hL hQ hκ hP hPL hfin hproj C hRq h
  · exact capFDerivedIsoTop_hom_mate ν i hL hQ hκ hP hPL hfin hproj C hRq h

/-- **`𝔈⁺_i ⋙ RHom(K, -) ≅ RHom(K, -) ⋙ 𝔈_i` is the mate of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂`**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for every `j ≤ ℓ`: the inverse
of `CupCap.capERightAdjointIso`, defined by taking adjoints along `𝔉_i ⊣ 𝔈_i`, is the mate of
the inverse of `CupCap.capEDerivedIso` along the coevaluation adjunctions `𝕂 ⊣ RHom(K, -)`.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
theorem capERightAdjointIso_inv_eq_mate :
    (capERightAdjointIso ν i hL hQ hκ hP hPL hfin hproj C hRq).inv =
      (mateEquiv (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
        (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
        (TwoSquare.mk _ _ _ _ (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).inv)).natTrans := by
  have h := rightAdjointCommIso_inv_eq_mate (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
    (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L) (derivedBlackFEAdjunction ν i C hRq)
    (derivedPlusFEAdjunction ν i C hRq) _ _
    (capFDerivedIso_hom_mate ν i hL hQ hκ hP hPL hfin hproj C hRq)
  refine Eq.trans ?_ h
  unfold capERightAdjointIso capFDerivedIso
  split_ifs <;> rfl

/-- **`𝔈⁺_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` through the mate of `𝕂 ⋙ 𝔈⁺_i ≅ 𝔈_i ⋙ 𝕂`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21 and Definition 7.18), for every `j ≤ ℓ` and
the quantum trace with homological shift `shift`, with the shift of `𝔈_i` induced by
`𝔉_i ⊣ 𝔈_i`: the inverse of `CupCap.capEQuantumTraceShiftIso` is the shift compatibility of
`𝔈_i` followed by the shift of the mate of the inverse of `CupCap.capEDerivedIso` along the
coevaluation adjunctions.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj`; `C`, `hRq`. -/
theorem capEQuantumTraceShiftIso_inv_eq_mate :
    letI := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
    (capEQuantumTraceShiftIso ν i C hRq hL hQ hκ hP hPL hfin hproj shift).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (coevaluationRightAdjoint k Q Λ Λc j hj νᵢ ν₀ L)
          ((derivedBlackE.{0} Q Λ i ν).commShiftIso shift).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (mateEquiv (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L)
          (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
          (TwoSquare.mk _ _ _ _ (capEDerivedIso ν i hL hQ hκ hP hPL hfin hproj).inv)).natTrans
          (shiftFunctor _ shift) ≫ (Functor.associator _ _ _).hom := by
  let := derivedBlackEAdjointCommShift (Λ := Λ) ν i C hRq
  exact rightAdjointShiftCommIso_inv_eq_mate (coevaluationAdjunction k Q Λ Λc j hj ν ν₀ L)
    (coevaluationAdjunction k Q Λ Λc j hj νᵢ ν₀ L) (derivedBlackFEAdjunction ν i C hRq)
    (derivedPlusFEAdjunction ν i C hRq) _ _
    (capFDerivedIso_hom_mate ν i hL hQ hκ hP hPL hfin hproj C hRq) shift

end Categorification.Stendhal.CupCap
