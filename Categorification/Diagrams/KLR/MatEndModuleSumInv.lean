/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleSigma
import Categorification.Diagrams.KLR.MatEndModuleDot
import Categorification.TwoRep.SumInvModuleTransfer

/-!
# Brundan's inversion relations along two matrix maps, on all modules

In the setting of `MatEnd.resIndModuleEquiv_sigmaLin` (two composable additive functors with
matrix maps `φ₁`, `φ₂`, completed adjunctions `F₁' ⊣ E₁`, `F₂' ⊣ E₂`, and a natural
transformation `σK : E₁ ⋙ F₁' ⟶ F₂' ⋙ E₂` agreeing with `z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m` on the
generator), together with a natural endomorphism `α` of `F₁'` agreeing with right
multiplication by `d` (as in `MatEnd.indResModuleEquiv_natMap`):

* an explicit inverse of `(σK, E₁ α^m ε₁)` in the functor category on the completed additive
  envelope gives an explicit inverse of `(sigmaLin, counit ∘ (· d)^m)` on every module over the
  matrix ring (`MatEnd.resIndSumInvTo`), and
* an explicit inverse of `(σK, η₂ α₂^m E₂)` gives one of `(sigmaLin, (· d₂)^m ∘ unit)`
  (`MatEnd.resIndSumInvFrom`).

These are Brundan's conditions (arXiv:1501.00350v1, (1.8) and (1.9)) for Webster's functors on
all modules (arXiv:1309.3796v3, §4.6, Theorem 4.31), from those on the completed categories.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory CategoryTheory.Idempotents Preadditive MulOpposite InductionAlong TwoRep

namespace MatEnd

universe v w

attribute [local instance] HomTensor.bimodule
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

section Pow

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))
  {d : (MatEnd Y)ᵐᵒᵖ} (hd : Intertwines (mapEmbOp F he h) (mapEmbOp F he h) d)
  {α : mapKaroubi F.mapMat_ ⟶ mapKaroubi F.mapMat_}
  (hα : karoubiCorner F he h (cornerMul hd (unitGen (mapEmbOp F he h))) =
    karoubiGen F he h ≫ α.app ((toKaroubi _).obj (familySum X)))
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} (adj : mapKaroubi F.mapMat_ ⊣ E) [E.Additive]
  (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd Y)ᵐᵒᵖ M]
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

include hα in
/-- **Powers of right multiplication by `d` on `Ind (Res M)` are module maps of `E ◁ α^m`.** -/
theorem indResModuleEquiv_natMap_pow (m : ℕ)
    (x : Ind (Res (mapEmbOp F he h) M) (mapEmbOp F he h)) :
    letI := HomTensor.transferModule (karoubiMatrixOpY Y) M
    indResModuleEquiv F he h adj M π ι' hπ ((natMap hd ^ m : Module.End _ _) x) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum Y))
        ((toKaroubi _).obj (familySum Y)) M
        (Functor.whiskerLeft E ((show End (mapKaroubi F.mapMat_) from α) ^ m))
        (indResModuleEquiv F he h adj M π ι' hπ x) := by
  let _ := HomTensor.transferModule (karoubiMatrixOpY Y) M
  induction m generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, Module.End.one_apply, End.one_def, Functor.whiskerLeft_id']
    exact (LinearMap.congr_fun (HomTensor.natModuleMap_id ℤ ((toKaroubi _).obj (familySum Y))
      ((toKaroubi _).obj (familySum Y)) (M := M) (F := E ⋙ mapKaroubi F.mapMat_)) _).symm
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, indResModuleEquiv_natMap F he h hd hα adj M π ι' hπ,
      ih, pow_succ', End.mul_def, Functor.whiskerLeft_comp, HomTensor.natModuleMap_comp,
      LinearMap.comp_apply]

include hα in
/-- **Powers of right multiplication by `d` on `Res (Ind N)` are module maps of `α^m ▷ E`.** -/
theorem resIndModuleEquiv_resMap_natMap_pow (N : Type (max w v)) [AddCommGroup N]
    [Module (MatEnd X)ᵐᵒᵖ N] (m : ℕ) (y : Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    resIndModuleEquiv F he h N adj (Res.map (natMap hd ^ m : Module.End _ _) y) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum X))
        ((toKaroubi _).obj (familySum X)) N
        (Functor.whiskerRight ((show End (mapKaroubi F.mapMat_) from α) ^ m) E)
        (resIndModuleEquiv F he h N adj y) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  induction m generalizing y with
  | zero =>
    rw [pow_zero, pow_zero, End.one_def, Functor.whiskerRight_id']
    refine (congrArg _ (Res.ext rfl)).trans (LinearMap.congr_fun
      (HomTensor.natModuleMap_id ℤ ((toKaroubi _).obj (familySum X))
      ((toKaroubi _).obj (familySum X)) (M := N) (F := mapKaroubi F.mapMat_ ⋙ E)) _).symm
  | succ m ih =>
    have e : Res.map (φ := mapEmbOp F he h) (natMap (N := N) hd ^ (m + 1) : Module.End _ _) y =
        Res.map (natMap hd) (Res.map (natMap hd ^ m : Module.End _ _) y) := by
      apply Res.ext
      rw [Res.val_map, Res.val_map, Res.val_map, pow_succ', Module.End.mul_apply]
    rw [e, resIndModuleEquiv_resMap_natMap F he h hd hα adj N, ih, pow_succ', End.mul_def,
      Functor.whiskerRight_comp, HomTensor.natModuleMap_comp, LinearMap.comp_apply]

include hα in
/-- **The dotted cup on modules is the module map of `η ≫ α^m ▷ E`**: under
`resIndModuleEquiv`, `n ↦ φ(1) d^m ⊗ n` is the module map of `η ≫ α^m ▷ E` at `𝟙 ⊗ n`. -/
theorem resIndModuleEquiv_dottedCup (N : Type (max w v)) [AddCommGroup N]
    [Module (MatEnd X)ᵐᵒᵖ N] (m : ℕ) (z : N) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    resIndModuleEquiv F he h N adj
        (Res.map (natMap hd ^ m : Module.End _ _) (unitMap (φ := mapEmbOp F he h) N z)) =
      HomTensor.natModuleMap ℤ ((toKaroubi _).obj (familySum X))
        ((toKaroubi _).obj (familySum X)) N
        (adj.unit ≫ Functor.whiskerRight ((show End (mapKaroubi F.mapMat_) from α) ^ m) E)
        (BalancedTensor.tmul (show (toKaroubi _).obj (familySum X) ⟶
          (𝟭 _).obj ((toKaroubi _).obj (familySum X)) from 𝟙 _) z) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) N
  rw [HomTensor.natModuleMap_comp, LinearMap.comp_apply,
    resIndModuleEquiv_resMap_natMap_pow F he h hd hα adj N m, resIndModuleEquiv_unitMap,
    HomTensor.natModuleMap_tmul, HomTensor.natModuleMap_tmul, HomTensor.natModuleMap_tmul]
  erw [Category.id_comp]

end Pow

section SumInv

variable {C₀ : Type*} [Category.{v} C₀] [Preadditive C₀] {C₁ : Type*} [Category.{v} C₁]
  [Preadditive C₁] {C₂ : Type*} [Category.{v} C₂] [Preadditive C₂]
  {ι₀ ι₁ ι₂ : Type w} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] {X₀ : ι₀ → C₀} {X₁ : ι₁ → C₁} {X₂ : ι₂ → C₂}
  (F₁ : C₀ ⥤ C₁) [F₁.Additive] (F₂ : C₁ ⥤ C₂) [F₂.Additive] {e₁ : ι₀ → ι₁} {e₂ : ι₁ → ι₂}
  (he₁ : Function.Injective e₁) (h₁ : ∀ i, F₁.obj (X₀ i) = X₁ (e₁ i))
  (he₂ : Function.Injective e₂) (h₂ : ∀ j, F₂.obj (X₁ j) = X₂ (e₂ j))
  {E₂ : Karoubi (Mat_ C₂) ⥤ Karoubi (Mat_ C₁)} (adj₂ : mapKaroubi F₂.mapMat_ ⊣ E₂)
  [E₂.Additive]
  {c : (MatEnd X₂)ᵐᵒᵖ}
  (hc : ∀ a, c * mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) =
    mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ a) * c)
  {E₁ : Karoubi (Mat_ C₁) ⥤ Karoubi (Mat_ C₀)} (adj₁ : mapKaroubi F₁.mapMat_ ⊣ E₁)
  [E₁.Additive]
  (σK : E₁ ⋙ mapKaroubi F₁.mapMat_ ⟶ mapKaroubi F₂.mapMat_ ⋙ E₂)
  (hσ : adj₂.homEquiv _ _ (karoubiSect F₂ h₂) ≫ E₂.map (karoubiCorner F₂ he₂ h₂
      (sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) c (unitGen (mapEmbOp F₁ he₁ h₁)))) =
    (karoubiGen F₁ he₁ h₁ ≫ (mapKaroubi F₁.mapMat_).map (adj₁.homEquiv _ _ (karoubiSect F₁ h₁))) ≫
      σK.app ((toKaroubi _).obj (familySum X₁)))
  {d : (MatEnd X₁)ᵐᵒᵖ} (hd : Intertwines (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₁ he₁ h₁) d)
  {α : mapKaroubi F₁.mapMat_ ⟶ mapKaroubi F₁.mapMat_}
  (hα : karoubiCorner F₁ he₁ h₁ (cornerMul hd (unitGen (mapEmbOp F₁ he₁ h₁))) =
    karoubiGen F₁ he₁ h₁ ≫ α.app ((toKaroubi _).obj (familySum X₀)))
  (M : ModuleCat.{max w v} (MatEnd X₁)ᵐᵒᵖ) {J : Type*} [Fintype J]
  (π : J → (E₁.obj ((toKaroubi _).obj (familySum X₁)) ⟶ (toKaroubi _).obj (familySum X₀)))
  (ι' : J → ((toKaroubi _).obj (familySum X₀) ⟶ E₁.obj ((toKaroubi _).obj (familySum X₁))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _) {n : ℕ}

/-- **Brundan (1.8) on all modules, from the completed categories**: an explicit inverse of
`(σK, E₁ α^m ε₁)` among functors of the completed additive envelope gives an explicit inverse
of `(sigmaLin, z ⊗ m ↦ z d^m m)` on every module over the matrix ring of `X₁`. -/
def resIndSumInvTo
    (S : SumInvTo σK (fun m => Functor.whiskerLeft E₁
      ((show End (mapKaroubi F₁.mapMat_) from α) ^ m) ≫ adj₁.counit) n) :
    SumInvTo (X := ModuleCat.of _ (Ind (Res (mapEmbOp F₁ he₁ h₁) M) (mapEmbOp F₁ he₁ h₁)))
      (Y := ModuleCat.of _ (Res (mapEmbOp F₂ he₂ h₂) (Ind M (mapEmbOp F₂ he₂ h₂)))) (Z := M)
      (ModuleCat.ofHom (sigmaLin (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) hc M))
      (fun m => ModuleCat.ofHom (counitMap (φ := mapEmbOp F₁ he₁ h₁) M ∘ₗ
        (natMap hd ^ m : Module.End _ _))) n :=
  letI := HomTensor.transferModule (karoubiMatrixOp X₁) M
  (HomTensor.sumInvToModule ((toKaroubi _).obj (familySum X₁))
    ((toKaroubi _).obj (familySum X₁)) M S).transferAdd
    (indResModuleEquiv F₁ he₁ h₁ adj₁ M π ι' hπ).toAddEquiv
    (resIndModuleEquiv F₂ he₂ h₂ M adj₂).toAddEquiv
    (HomTensor.unitModuleEquiv ℤ ((toKaroubi _).obj (familySum X₁)) M).symm.toAddEquiv
    (fun x => resIndModuleEquiv_sigmaLin F₁ F₂ he₁ h₁ he₂ h₂ adj₂ hc adj₁ σK hσ M π ι' hπ x)
    (fun m x => by
      change BalancedTensor.tmul _ _ = HomTensor.natModuleMap ℤ _ _ M _ _
      rw [HomTensor.natModuleMap_comp, LinearMap.comp_apply]
      erw [← indResModuleEquiv_natMap_pow F₁ he₁ h₁ hd hα adj₁ M π ι' hπ m x,
        natModuleMap_counit_indResModuleEquiv]
      rfl)

/-- **Brundan (1.9) on all modules, from the completed categories**: an explicit inverse of
`(σK, η₂ α₂^m E₂)` among functors of the completed additive envelope gives an explicit inverse
of `(sigmaLin, m ↦ φ₂(1) d₂^m ⊗ m)` on every module over the matrix ring of `X₁`. -/
def resIndSumInvFrom
    {d₂ : (MatEnd X₂)ᵐᵒᵖ} (hd₂ : Intertwines (mapEmbOp F₂ he₂ h₂) (mapEmbOp F₂ he₂ h₂) d₂)
    {α₂ : mapKaroubi F₂.mapMat_ ⟶ mapKaroubi F₂.mapMat_}
    (hα₂ : karoubiCorner F₂ he₂ h₂ (cornerMul hd₂ (unitGen (mapEmbOp F₂ he₂ h₂))) =
      karoubiGen F₂ he₂ h₂ ≫ α₂.app ((toKaroubi _).obj (familySum X₁)))
    (S : SumInvFrom σK (fun m => adj₂.unit ≫ Functor.whiskerRight
      ((show End (mapKaroubi F₂.mapMat_) from α₂) ^ m) E₂) n) :
    SumInvFrom (X := ModuleCat.of _ (Res (mapEmbOp F₂ he₂ h₂) (Ind M (mapEmbOp F₂ he₂ h₂))))
      (Y := ModuleCat.of _ (Ind (Res (mapEmbOp F₁ he₁ h₁) M) (mapEmbOp F₁ he₁ h₁))) (Z := M)
      (ModuleCat.ofHom (sigmaLin (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) hc M))
      (fun m => ModuleCat.ofHom (Res.map (natMap hd₂ ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := mapEmbOp F₂ he₂ h₂) M)) n :=
  letI := HomTensor.transferModule (karoubiMatrixOp X₁) M
  (HomTensor.sumInvFromModule ((toKaroubi _).obj (familySum X₁))
    ((toKaroubi _).obj (familySum X₁)) M S).transferAdd
    (resIndModuleEquiv F₂ he₂ h₂ M adj₂).toAddEquiv
    (indResModuleEquiv F₁ he₁ h₁ adj₁ M π ι' hπ).toAddEquiv
    (HomTensor.unitModuleEquiv ℤ ((toKaroubi _).obj (familySum X₁)) M).symm.toAddEquiv
    (fun x => resIndModuleEquiv_sigmaLin F₁ F₂ he₁ h₁ he₂ h₂ adj₂ hc adj₁ σK hσ M π ι' hπ x)
    (fun m z => by
      exact resIndModuleEquiv_dottedCup F₂ he₂ h₂ hd₂ hα₂ adj₂ M m z)

end SumInv

end MatEnd

end Categorification.KLR.Diagram
