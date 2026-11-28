/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForgetDerivedCompact
import DG.Bigraded.Derived
import DG.Category.Derived.Coproducts
import DG.Category.Derived.Compact

/-!
# Forgetting the weights and then taking the constant module

For a dg module `N` over `C_A = DG.WeightCategory A`, the constant dg module on the weight sum
`⨁ k, N⟨k⟩` is the direct sum of the internal shifts of `N`: at the weight `j` both are
`⨁ d, N⟨j + d⟩` (`DG.CatModule.weightShiftSumIso`). On derived categories,
`Ψ (Φ Z) ≅ ∐ d, Z⟨d⟩` (`DG.CatModule.weightConstForgetDerivedIso`), where `Φ` forgets the
weights and `Ψ` is the constant module.

Consequently a morphism from a compact object `W` to `Ψ (Φ Z)` vanishes as soon as every morphism
`W ⟶ Z⟨d⟩` does (`DG.CatModule.eq_zero_of_compact_weightConstForget`), and `Ψ` reflects zero
objects (`DG.CatModule.isZero_of_isZero_weightConstDerived_obj`).

This is used for the graded braiding functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Definition 6.6 and Theorem 6.15.
-/

open CategoryTheory Limits DirectSum

universe w₁ w₂ u

noncomputable section

namespace DG

namespace CatModule

open WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

section Module

variable (N : CatModule.{u} (WeightCategory A))

/-- The family of internal shifts `d ↦ N⟨d⟩` of a dg module over `C_A`. -/
abbrev weightShiftFamily (d : ℤ) : CatModule.{u} (WeightCategory A) :=
  precompObj (WeightCategory.shiftFunctor A d) N

/-- The inclusion of the internal shift `N⟨d⟩` into the constant module on `⨁ k, N⟨k⟩`. -/
def weightShiftι (d : ℤ) :
    weightShiftFamily N d ⟶ (weightConstFunctor A).obj ((weightForget A).obj N) where
  app j := weightSumOf N (j.as + d)
  map_mem' {j _ _} hm := DG.DirectSum.of_mem_grading (fun k : ℤ => N.obj ⟨k⟩) (j.as + d) hm
  map_d' m := (weightSum_d_of N _ m).symm
  map_smul' {j j'} f m := by
    change weightSumOf N (j'.as + d) (N.act ((WeightCategory.shiftFunctor A d).map f) m) =
      f.1 • weightSumOf N (j.as + d) m
    exact (weightSum_smul_of' N ((WeightCategory.shiftFunctor A d).map f)
      (show N.obj ⟨j.as + d⟩ from m)).symm

/-- **The constant module on the weight sum is the direct sum of the internal shifts.** -/
def weightShiftSumHom :
    directSum (weightShiftFamily N) ⟶ (weightConstFunctor A).obj ((weightForget A).obj N) :=
  directSumDesc (weightShiftι N)

omit [DGRing A] in
theorem weightShiftSumHom_bijective (j : WeightCategory A) :
    Function.Bijective ((weightShiftSumHom N).app j) := by
  classical
  let E : N.WeightSum ≃+ ⨁ d : ℤ, (weightShiftFamily N d).obj j :=
    DirectSum.equivCongrLeft (β := fun k : ℤ => N.obj ⟨k⟩) (Equiv.addLeft j.as).symm
  let f : (⨁ d : ℤ, (weightShiftFamily N d).obj j) →+ N.WeightSum := (weightShiftSumHom N).app j
  change Function.Bijective f
  have h : ∀ x, E (f x) = x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of d y =>
      change E (DirectSum.toAddMonoid (fun d => (weightShiftι N d).app j)
        (DirectSum.of _ d y)) = _
      rw [DirectSum.toAddMonoid_of]
      change E (DirectSum.of (fun k : ℤ => N.obj ⟨k⟩) (j.as + d) y) = _
      exact DirectSum.equivCongrLeft_of (β := fun k : ℤ => N.obj ⟨k⟩)
        (Equiv.addLeft j.as).symm d y
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have he : ⇑f = ⇑E.symm :=
    funext fun x => by rw [← h x, AddEquiv.symm_apply_apply, h]
  rw [he]
  exact E.symm.bijective

instance : IsIso (weightShiftSumHom N) :=
  isIso_of_bijective _ (weightShiftSumHom_bijective N)

end Module

/-- A morphism from an object that is compact for `ℤ`-indexed coproducts to the point of a
coproduct cofan vanishes when every morphism to a summand does. -/
theorem _root_.DG.IsCompact.eq_zero_of_isColimit {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {W : 𝒞} (hW : IsCompact.{0} W) {Y : ℤ → 𝒞} {c : Cofan Y} (hc : IsColimit c)
    (h : ∀ (d : ℤ) (g : W ⟶ Y d), g = 0) (f : W ⟶ c.pt) : f = 0 := by
  classical
  have : HasCoproduct Y := HasColimit.mk ⟨c, hc⟩
  let e : c.pt ≅ ∐ Y := hc.coconePointUniqueUpToIso (colimit.isColimit _)
  obtain ⟨a, ha⟩ := (hW ℤ Y).2 (f ≫ e.hom)
  have ha0 : a = 0 := DFinsupp.ext fun d => by rw [h d (a d)]; rfl
  have : f ≫ e.hom = 0 := by rw [← ha, ha0, map_zero]
  simpa using this =≫ e.inv

variable [CatModule.HasDerivedCategory.{w₁, u} (WeightCategory A)] [DG.HasDerivedCategory.{w₂, u} A]

instance Q_preservesIntCoproducts :
    PreservesColimitsOfShape (Discrete ℤ)
      (CatModule.DerivedCategory.Q : CatModule.{u} (WeightCategory A) ⥤ _) := by
  have := DerivedCategory.Qh_preservesColimitsOfShape.{0, u, w₁} (WeightCategory A) ℤ
  dsimp only [CatModule.DerivedCategory.Q]
  infer_instance

/-- `Ψ (Φ (Q N)) ≅ Q (⨁ d, N⟨d⟩)`. -/
def weightConstForgetDerivedIso (N : CatModule.{u} (WeightCategory A)) :
    (weightConstDerived A).obj ((weightForgetDerived A).obj (CatModule.DerivedCategory.Q.obj N)) ≅
      CatModule.DerivedCategory.Q.obj (directSum (weightShiftFamily N)) :=
  (weightConstDerived A).mapIso ((QCompWeightForgetDerivedIso A).app N) ≪≫
    (QCompWeightConstDerivedIso A).app ((weightForget A).obj N) ≪≫
      CatModule.DerivedCategory.Q.mapIso (asIso (weightShiftSumHom N)).symm

/-- **A morphism from a compact object to `Ψ (Φ Z)` vanishes as soon as every morphism to an
internal shift of `Z` does.** -/
theorem eq_zero_of_compact_weightConstForget {W Z : CatModule.DerivedCategory.{w₁, u}
      (WeightCategory A)} (hW : IsCompact.{u} W)
    (h : ∀ (d : ℤ) (g : W ⟶ (CatModule.DerivedCategory.internalShift A d).obj Z), g = 0)
    (f : W ⟶ (weightConstDerived A).obj ((weightForgetDerived A).obj Z)) : f = 0 := by
  classical
  obtain ⟨N, ⟨eN⟩⟩ := CatModule.DerivedCategory.exists_iso_Q_obj Z
  let e := (weightConstDerived A).mapIso ((weightForgetDerived A).mapIso eN) ≪≫
    weightConstForgetDerivedIso N
  have hc := isColimitCofanMkObjOfIsColimit CatModule.DerivedCategory.Q _ _
    (coproductCoconeIsColimit.{u, 0} (weightShiftFamily N))
  have h' : ∀ (d : ℤ) (g : W ⟶ CatModule.DerivedCategory.Q.obj (weightShiftFamily N d)),
      g = 0 := by
    intro d g
    have e' : CatModule.DerivedCategory.Q.obj (weightShiftFamily N d) ≅
        (CatModule.DerivedCategory.internalShift A d).obj Z :=
      ((CatModule.DerivedCategory.QCompInternalShiftIso A d).app N).symm ≪≫
        (CatModule.DerivedCategory.internalShift A d).mapIso eN.symm
    have := h d (g ≫ e'.hom)
    simpa using this =≫ e'.inv
  have := IsCompact.eq_zero_of_isColimit (hW.down.{0, u}) hc h' (f ≫ e.hom)
  simpa using this =≫ e.inv

/-- **The derived constant module reflects zero objects.** -/
theorem isZero_of_isZero_weightConstDerived_obj {X : DG.DerivedCategory.{w₂, u} A}
    (hX : IsZero ((weightConstDerived A).obj X)) : IsZero X := by
  obtain ⟨M, ⟨eM⟩⟩ := DG.DerivedCategory.exists_iso_Q_obj X
  refine IsZero.of_iso ?_ eM
  rw [DG.DerivedCategory.isZero_Q_obj_iff]
  have h : IsZero (CatModule.DerivedCategory.Q.obj ((weightConstFunctor A).obj M)) :=
    IsZero.of_iso hX (((QCompWeightConstDerivedIso A).app M).symm ≪≫
      (weightConstDerived A).mapIso eM.symm)
  rw [CatModule.DerivedCategory.isZero_Q_obj_iff] at h
  exact h ⟨0⟩

end CatModule

end DG
