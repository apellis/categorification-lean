/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleDecomp
import Categorification.Diagrams.KLR.MatEndModuleNaturality
import Categorification.Algebra.SumDecompNaturality

/-!
# Naturality of the commutation isomorphisms of induction and restriction

For a decomposition of functors `G ≅ G' ⊕ H^{⊕ ι₀}`, the isomorphisms
`Res_{φ₁} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂ × M^ι₀` and
`Ind (Res_{φ₂} M) φ₂ ≅ Res_{φ₁} (Ind M φ₁) × M^ι₀` of `MatEndModuleDecomp`, built from the
decomposition on modules (`HomTensor.sumDecompModule`), are natural in the module `M`
(`MatEnd.resIndEquivIndResProd_map`, `MatEnd.indResEquivResIndProd_map`).

These are the module-level forms of Webster's commutation relations
`E_i F_i ≅ F_i E_i ⊕ 1^{⊕ n}` (arXiv:1309.3796v3, Theorem 4.31) that are compatible with module
maps, as used for the tensor factors in the proof of Proposition 5.5 there.
-/

namespace Categorification

open CategoryTheory

noncomputable section

namespace HomTensor

variable {A : Type*} [Category A] [Preadditive A] (O : A) {M M' : Type*} [AddCommGroup M]
  [Module (End O)ᵐᵒᵖ M] [AddCommGroup M'] [Module (End O)ᵐᵒᵖ M']

attribute [local instance] bimodule

/-- `unitModuleEquivOfEq` is natural in the module. -/
theorem unitModuleEquivOfEq_map (G : A ⥤ A) [G.Additive] (h : G = 𝟭 A)
    (g : M →ₗ[(End O)ᵐᵒᵖ] M') (m : M) :
    unitModuleEquivOfEq O M' G h (g m) =
      BalancedTensor.mapRight g (unitModuleEquivOfEq O M G h m) := by
  have h1 : (unitModuleEquiv ℤ O M').symm (g m) =
      BalancedTensor.mapRight g ((unitModuleEquiv ℤ O M).symm m) := by
    apply (unitModuleEquiv ℤ O M').injective
    rw [LinearEquiv.apply_symm_apply, unitModuleEquiv_mapRight, LinearEquiv.apply_symm_apply]
  simp only [unitModuleEquivOfEq, LinearEquiv.trans_apply, h1]
  exact natModuleEquiv_mapRight _ _ _ _ _

end HomTensor

namespace KLR.Diagram.MatEnd

open CategoryTheory.Idempotents MulOpposite InductionAlong

universe v w

attribute [local instance] HomTensor.bimodule

variable {C : Type*} [Category.{v} C] [Preadditive C] {D₁ : Type*} [Category.{v} D₁]
  [Preadditive D₁] {C₂ : Type*} [Category.{v} C₂] [Preadditive C₂]
  {ι κ₁ κ₂ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ₁] [DecidableEq κ₁]
  [Fintype κ₂] [DecidableEq κ₂] {X : ι → C} {Y₁ : κ₁ → D₁} {Z : κ₂ → C₂}
  (F₁ : C ⥤ D₁) [F₁.Additive] {e₁ : ι → κ₁} (he₁ : Function.Injective e₁)
  (h₁ : ∀ i, F₁.obj (X i) = Y₁ (e₁ i))
  {E₁ : Karoubi (Mat_ D₁) ⥤ Karoubi (Mat_ C)} (adj₁ : mapKaroubi F₁.mapMat_ ⊣ E₁) [E₁.Additive]
  {G : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G.Additive] (eG : G ≅ mapKaroubi F₁.mapMat_ ⋙ E₁)
  (F₂ : C₂ ⥤ C) [F₂.Additive] {e₂ : κ₂ → ι} (he₂ : Function.Injective e₂)
  (h₂ : ∀ j, F₂.obj (Z j) = X (e₂ j))
  {E₂ : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C₂)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂) [E₂.Additive]
  {J : Type*} [Fintype J]
  (π : J → (E₂.obj ((toKaroubi _).obj (familySum X)) ⟶ (toKaroubi _).obj (familySum Z)))
  (ι' : J → ((toKaroubi _).obj (familySum Z) ⟶ E₂.obj ((toKaroubi _).obj (familySum X))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)
  {G' : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G'.Additive]
  (eG' : G' ≅ E₂ ⋙ mapKaroubi F₂.mapMat_)
  {H : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [H.Additive] (hH : H = 𝟭 _)
  {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]
  {M M₂ : Type (max w v)} [AddCommGroup M] [Module (MatEnd X)ᵐᵒᵖ M] [AddCommGroup M₂]
  [Module (MatEnd X)ᵐᵒᵖ M₂] (f : M →ₗ[(MatEnd X)ᵐᵒᵖ] M₂)

/-- **Naturality of `resIndEquivIndResProd`**: for the decomposition of modules induced by a
decomposition `Df` of functors, the isomorphism
`Res_{φ₁} (Ind M φ₁) ≅ Ind (Res_{φ₂} M) φ₂ × M^ι₀` carries `Res (Ind f)` to
`Ind (Res f) × f^ι₀`. -/
theorem resIndEquivIndResProd_map (Df : SumDecomp G G' (fun _ : ι₀ => H))
    (x : Res (mapEmbOp F₁ he₁ h₁) (Ind M (mapEmbOp F₁ he₁ h₁))) :
    resIndEquivIndResProd F₁ he₁ h₁ adj₁ eG F₂ he₂ h₂ adj₂ π ι' hπ eG' hH M₂
        (letI := HomTensor.transferModule (karoubiMatrixOp X) M₂;
          HomTensor.sumDecompModule _ _ M₂ Df) (Res.map (Ind.map f) x) =
      (Ind.map (Res.map f)
          (resIndEquivIndResProd F₁ he₁ h₁ adj₁ eG F₂ he₂ h₂ adj₂ π ι' hπ eG' hH M
            (letI := HomTensor.transferModule (karoubiMatrixOp X) M;
              HomTensor.sumDecompModule _ _ M Df) x).1,
        fun s => f ((resIndEquivIndResProd F₁ he₁ h₁ adj₁ eG F₂ he₂ h₂ adj₂ π ι' hπ eG' hH M
            (letI := HomTensor.transferModule (karoubiMatrixOp X) M;
              HomTensor.sumDecompModule _ _ M Df) x).2 s)) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M₂
  let tf := HomTensor.transferLinearMap (karoubiMatrixOp X) f
  exact SumDecomp.semilinearEquiv_naturality (karoubiMatrixOp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ (BalancedTensor.mapRight tf) (BalancedTensor.mapRight tf) (BalancedTensor.mapRight tf)
    (fun x => resIndModuleEquivOfIso_map F₁ he₁ h₁ f adj₁ eG x)
    (fun y => indResModuleEquivOfIso_map F₂ he₂ h₂ adj₂ f π ι' hπ eG' y)
    (fun m => HomTensor.unitModuleEquivOfEq_map _ H hH tf m)
    (fun y => HomTensor.natModuleMap_mapRight _ _ _ tf y)
    (fun s y => HomTensor.natModuleMap_mapRight _ _ _ tf y) x

/-- **Naturality of `indResEquivResIndProd`**: for the decomposition of modules induced by a
decomposition `Df` of functors, the isomorphism
`Ind (Res_{φ₂} M) φ₂ ≅ Res_{φ₁} (Ind M φ₁) × M^ι₀` carries `Ind (Res f)` to
`Res (Ind f) × f^ι₀`. -/
theorem indResEquivResIndProd_map (Df : SumDecomp G' G (fun _ : ι₀ => H))
    (x : Ind (Res (mapEmbOp F₂ he₂ h₂) M) (mapEmbOp F₂ he₂ h₂)) :
    indResEquivResIndProd F₁ he₁ h₁ adj₁ eG F₂ he₂ h₂ adj₂ π ι' hπ eG' hH M₂
        (letI := HomTensor.transferModule (karoubiMatrixOp X) M₂;
          HomTensor.sumDecompModule _ _ M₂ Df) (Ind.map (Res.map f) x) =
      (Res.map (Ind.map f)
          (indResEquivResIndProd F₁ he₁ h₁ adj₁ eG F₂ he₂ h₂ adj₂ π ι' hπ eG' hH M
            (letI := HomTensor.transferModule (karoubiMatrixOp X) M;
              HomTensor.sumDecompModule _ _ M Df) x).1,
        fun s => f ((indResEquivResIndProd F₁ he₁ h₁ adj₁ eG F₂ he₂ h₂ adj₂ π ι' hπ eG' hH M
            (letI := HomTensor.transferModule (karoubiMatrixOp X) M;
              HomTensor.sumDecompModule _ _ M Df) x).2 s)) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M₂
  let tf := HomTensor.transferLinearMap (karoubiMatrixOp X) f
  exact SumDecomp.semilinearEquiv_naturality (karoubiMatrixOp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ (BalancedTensor.mapRight tf) (BalancedTensor.mapRight tf) (BalancedTensor.mapRight tf)
    (fun y => indResModuleEquivOfIso_map F₂ he₂ h₂ adj₂ f π ι' hπ eG' y)
    (fun x => resIndModuleEquivOfIso_map F₁ he₁ h₁ f adj₁ eG x)
    (fun m => HomTensor.unitModuleEquivOfEq_map _ H hH tf m)
    (fun y => HomTensor.natModuleMap_mapRight _ _ _ tf y)
    (fun s y => HomTensor.natModuleMap_mapRight _ _ _ tf y) x

end KLR.Diagram.MatEnd

end

end Categorification
