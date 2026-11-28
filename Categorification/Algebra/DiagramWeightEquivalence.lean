/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightFullyFaithful
import Categorification.Algebra.DiagramWeightInternalShift
import Categorification.Algebra.DiagramWeightTensorDerived
import Categorification.Algebra.DerivedTensorTriangulated
import Categorification.Algebra.WeightSumRepresentable
import Categorification.Algebra.WeightConstForgetShift
import Categorification.Algebra.CompactGeneratorEquivalence
import Categorification.Algebra.DerivedTensorCoproducts

/-!
# Graded derived diagram tensors which are equivalences

For a homogeneous coefficient bimodule `M` with weight decomposition `G`, if the derived tensor
`M ⊗ᴸ_B - : D(B) ⥤ D(A)` is an equivalence, then so is the graded derived tensor
`D ⊗ᴸ - : D(C_B) ⥤ D(C_A)` with the diagram weight bimodule `D = diagramWeightBimodule G`
(`Categorification.isEquivalence_diagramWeightDerivedTensor`).

The graded tensor is fully faithful (`Categorification.diagramWeightDerivedTensorFullyFaithful`)
and preserves coproducts, since forgetting the weights reflects isomorphisms. The internal
shifts of the representable modules compactly generate `D(C_B)`; their images are compact, since
compactness is detected after forgetting the weights, and they detect zero objects: if every
morphism from them to `Z` vanishes, then every morphism from the images of the representables to
the internal shifts of `Z` vanishes, hence every morphism from them to `Ψ (Φ Z)`, where `Φ`
forgets the weights and `Ψ` is its right adjoint. Transporting along the ungraded equivalence,
`Ψ_B` of the corresponding object of `D(C_B)` vanishes, so `Φ Z` and then `Z` vanish. The
criterion `Categorification.isEquivalence_of_compactlyGenerates` concludes.

This is the graded form of the equivalence statement of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Theorem 6.15, for the graded braiding functors of
Definition 6.6.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits DG MulOpposite
open scoped DG.DegreeZero

universe u w

variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M]
  (G : ℤ → AddSubgroup M) [DirectSum.Decomposition G]
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)]

open CatModule.DerivedCategory in
/-- The internal shifts of the representable modules over `C_B`. -/
abbrev weightShiftedRepresentable (B : Type u) [Ring B] [InternalGrading B] [BigradedDGRing B]
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory B)] (p : WeightCategory B × ℤ) :
    CatModule.DerivedCategory.{u,u} (WeightCategory B) :=
  (internalShift B p.2).obj (Q.obj (CatModule.representableW.{u} (WeightCategory B) p.1))

open CatModule.DerivedCategory in
/-- The internal shifts of the representable modules compactly generate `D(C_B)`. -/
theorem compactlyGenerates_weightShiftedRepresentable :
    CompactlyGenerates (weightShiftedRepresentable B) where
  isCompact p := (isCompact_internalShift_obj_iff B p.2 _).mpr
    ((CatModule.DerivedCategory.compactlyGenerates.{u, u, 0} (C := WeightCategory B)).isCompact
      p.1)
  isZero_of_forall_eq_zero Z h :=
    (CatModule.DerivedCategory.compactlyGenerates.{u, u, 0}
      (C := WeightCategory B)).isZero_of_forall_eq_zero Z fun X n φ => by
      let e := (internalShiftZeroIso B).app
        (Q.obj (CatModule.representableW.{u} (WeightCategory B) X))
      have := h (X, 0) n ((shiftFunctor _ n).map e.hom ≫ φ)
      simpa [← Functor.map_comp_assoc] using (shiftFunctor _ n).map e.inv ≫= this

variable [DG.HasDerivedCategory.{w,u} A] [DG.HasDerivedCategory.{w,u} B]
  [(derivedTensor.{w} A B M).IsEquivalence]

set_option hygiene false in
local notation "T̃" => diagramWeightDerivedTensor.{u, u} G hl hr
set_option hygiene false in
local notation "T" => derivedTensor.{w} A B M
set_option hygiene false in
local notation "σ" => diagramWeightForgetDerivedIso.{u, u, w} G hl hr
set_option hygiene false in
local notation "ΦA" => CatModule.weightForgetDerived.{u, w} A
set_option hygiene false in
local notation "ΦB" => CatModule.weightForgetDerived.{u, w} B


open CatModule.DerivedCategory

omit [(derivedTensor.{w} A B M).IsEquivalence] in
/-- The graded derived tensor preserves coproducts, since the ungraded one does and forgetting
the weights reflects isomorphisms. -/
theorem preservesColimitsOfShape_diagramWeightDerivedTensor (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (T̃) :=
  preservesColimitsOfShape_of_comparison (σ)

/-- The graded derived tensor sends the representable modules to compact objects. -/
theorem isCompact_diagramWeightDerivedTensor_representable (X : WeightCategory B) :
    IsCompact.{u} ((T̃).obj (Q.obj (CatModule.representableW.{u} (WeightCategory B) X))) := by
  obtain ⟨k⟩ := X
  have : (T).asEquivalence.functor.Additive :=
    inferInstanceAs (T).Additive
  refine CatModule.isCompact_of_isCompact_weightForgetDerived_obj ?_
  refine IsCompact.of_iso ((σ).app _) ?_
  exact (CatModule.isCompact_weightForgetDerived_representable (A := B) k).map_of_equivalence
    (T).asEquivalence

/-- The images of the internal shifts of the representable modules detect zero objects. -/
theorem isZero_of_forall_diagramWeightDerivedTensor
    (Z : CatModule.DerivedCategory.{u,u} (WeightCategory A))
    (h : ∀ (p : WeightCategory B × ℤ) (n : ℤ)
      (φ : ((T̃).obj (weightShiftedRepresentable B p))⟦n⟧ ⟶ Z), φ = 0) :
    IsZero Z := by
  let R : WeightCategory B → CatModule.DerivedCategory.{u,u} (WeightCategory B) := fun X =>
    Q.obj (CatModule.representableW.{u} (WeightCategory B) X)
  -- Morphisms to the internal shifts of `Z` vanish.
  have h₁ : ∀ (X : WeightCategory B) (n d : ℤ)
      (g : ((T̃).obj (R X))⟦n⟧ ⟶ (internalShift A d).obj Z), g = 0 := by
    intro X n d g
    let E := internalShiftEquiv A d
    apply E.inverse.map_injective
    rw [Functor.map_zero]
    let e₁ : ((T̃).obj (weightShiftedRepresentable B (X, -d)))⟦n⟧ ≅
        E.inverse.obj (((T̃).obj (R X))⟦n⟧) :=
      (shiftFunctor _ n).mapIso (diagramWeightDerivedTensorInternalShiftIso G hl hr (-d) _) ≪≫
        (internalShiftShiftIso A (-d) n _).symm
    let e₂ : E.inverse.obj ((internalShift A d).obj Z) ≅ Z := E.unitIso.symm.app Z
    have := h (X, -d) n (e₁.hom ≫ E.inverse.map g ≫ e₂.hom)
    rw [Preadditive.IsIso.comp_left_eq_zero] at this
    exact (cancel_mono e₂.hom).1 (this.trans Limits.zero_comp.symm)
  -- Hence morphisms after forgetting the weights vanish.
  have h₂ : ∀ (X : WeightCategory B) (n : ℤ)
      (φ : (ΦA).obj (((T̃).obj (R X))⟦n⟧) ⟶
        (ΦA).obj Z), φ = 0 := by
    intro X n φ
    let adj := CatModule.weightForgetDerivedAdjunction.{u, w} A
    have hW : IsCompact.{u} (((T̃).obj (R X))⟦n⟧) :=
      (isCompact_diagramWeightDerivedTensor_representable G hl hr X).shift n
    have := CatModule.eq_zero_of_compact_weightConstForget hW (h₁ X n) (adj.homEquiv _ _ φ)
    exact (adj.homEquiv _ _).injective (by
      rw [this, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero])
  -- Transport along the ungraded equivalence.
  let eT := (T).asEquivalence
  let Y' := eT.inverse.obj ((ΦA).obj Z)
  let c : (T).obj Y' ≅ (ΦA).obj Z := eT.counitIso.app _
  have h₃ : ∀ (X : WeightCategory B) (n : ℤ)
      (ψ : (ΦB).obj ((R X)⟦n⟧) ⟶ Y'), ψ = 0 := by
    intro X n ψ
    apply (T).map_injective
    rw [Functor.map_zero]
    let e₃ : (ΦA).obj (((T̃).obj (R X))⟦n⟧) ≅
        (T).obj ((ΦB).obj ((R X)⟦n⟧)) :=
      (ΦA).mapIso (((T̃).commShiftIso n).app _).symm ≪≫
        (σ).app _
    have := h₂ X n (e₃.hom ≫ (T).map ψ ≫ c.hom)
    rw [Preadditive.IsIso.comp_left_eq_zero] at this
    exact (cancel_mono c.hom).1 (this.trans Limits.zero_comp.symm)
  have h₄ : IsZero ((CatModule.weightConstDerived B).obj Y') := by
    refine (CatModule.DerivedCategory.compactlyGenerates.{u, u, 0}
      (C := WeightCategory B)).isZero_of_forall_eq_zero _ fun X n χ => ?_
    let adj := CatModule.weightForgetDerivedAdjunction.{u, w} B
    have := h₃ X n ((adj.homEquiv _ _).symm χ)
    exact (adj.homEquiv _ _).symm.injective (by rw [this, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp])
  have h₅ : IsZero Y' := CatModule.isZero_of_isZero_weightConstDerived_obj h₄
  exact CatModule.isZero_of_isZero_weightForgetDerived_obj
    (IsZero.of_iso ((T).map_isZero h₅) c.symm)

/-- **The graded derived diagram tensor is an equivalence when the ungraded one is**: if
`M ⊗ᴸ_B - : D(B) ⥤ D(A)` is an equivalence, then so is `D ⊗ᴸ - : D(C_B) ⥤ D(C_A)`. -/
theorem isEquivalence_diagramWeightDerivedTensor : (T̃).IsEquivalence :=
  isEquivalence_of_compactlyGenerates (T̃) compactlyGenerates_weightShiftedRepresentable
    (preservesColimitsOfShape_diagramWeightDerivedTensor G hl hr)
    { isCompact := fun p => IsCompact.of_iso
        (diagramWeightDerivedTensorInternalShiftIso G hl hr p.2 _)
        ((isCompact_internalShift_obj_iff A p.2 _).mpr
          (isCompact_diagramWeightDerivedTensor_representable G hl hr p.1))
      isZero_of_forall_eq_zero := isZero_of_forall_diagramWeightDerivedTensor G hl hr }
    (fun _ _ _ _ => (diagramWeightDerivedTensorFullyFaithful G hl hr
      (Functor.FullyFaithful.ofFullyFaithful (T))).map_bijective _ _)

end Categorification
