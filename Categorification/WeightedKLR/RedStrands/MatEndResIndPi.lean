/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndModuleDecompNaturality

/-!
# Restriction after induction when the complementary summand vanishes

Let `φ₁` be the matrix map of an additive functor `F₁` out of a family `X`, with an adjoint on
completions, so that restriction after induction along `φ₁` is the module functor of an
endofunctor `G ≅ F₁' ⋙ E₁` of the completion (`MatEnd.resIndModuleEquivOfIso`). If the module
functor of `G` decomposes as that of `G'` plus `ι₀` copies of that of an endofunctor equal to the
identity, and there are no morphisms from the sum of `X` to `G'` of it other than zero, then
`Res_{φ₁} (Ind M φ₁) ≅ M^ι₀` as modules over the matrix ring of `X`
(`MatEnd.resIndEquivPiOfSubsingleton`), naturally in `M`
(`MatEnd.resIndEquivPiOfSubsingleton_map`).

This is the case of the commutation relation `Eᵢ Fᵢ ≅ Fᵢ Eᵢ ⊕ 1^{⊕ n}` in which `Eᵢ` vanishes,
as used in Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
proof of Proposition 5.5, for a colour `i` outside the black content.
-/

noncomputable section

namespace Categorification

open CategoryTheory

namespace BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N]

/-- A balanced tensor product with a subsingleton left factor is a subsingleton. -/
theorem subsingleton_of_left [Subsingleton M] : Subsingleton (BalancedTensor k B A M N) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : BalancedTensor k B A M N, z = 0 := fun z =>
    induction_on z rfl (fun m n => by rw [Subsingleton.elim m 0, zero_tmul])
      (fun x y hx hy => by rw [hx, hy, add_zero])
  rw [h x, h y]

end BalancedTensor

section Semilinear

variable {R : Type*} {S : Type*} [Ring R] [Ring S] (σ : R ≃+* S)
  {U V M U' V' M' : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup M] [Module R U]
  [Module R V] [Module R M] [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup M']
  [Module R U'] [Module R V'] [Module R M']
  {T₁ T₂ T₃ T₁' T₂' T₃' : ModuleCat S} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Naturality of the second component of `SumDecomp.semilinearEquiv`: it needs no
compatibility on the first summand. -/
theorem SumDecomp.semilinearEquiv_snd_naturality (D : SumDecomp T₁ T₂ (fun _ : ι => T₃))
    (eU : U ≃ₗ[ℤ] T₁) (heU : ∀ (a : R) (x : U), eU (a • x) = σ a • eU x)
    (eV : V ≃ₗ[ℤ] T₂) (heV : ∀ (a : R) (x : V), eV (a • x) = σ a • eV x)
    (eM : M ≃ₗ[ℤ] T₃) (heM : ∀ (a : R) (x : M), eM (a • x) = σ a • eM x)
    (D' : SumDecomp T₁' T₂' (fun _ : ι => T₃'))
    (eU' : U' ≃ₗ[ℤ] T₁') (heU' : ∀ (a : R) (x : U'), eU' (a • x) = σ a • eU' x)
    (eV' : V' ≃ₗ[ℤ] T₂') (heV' : ∀ (a : R) (x : V'), eV' (a • x) = σ a • eV' x)
    (eM' : M' ≃ₗ[ℤ] T₃') (heM' : ∀ (a : R) (x : M'), eM' (a • x) = σ a • eM' x)
    (fU : U → U') (fM : M → M') (t₁ : T₁ → T₁') (t₃ : T₃ → T₃')
    (hU : ∀ x, eU' (fU x) = t₁ (eU x)) (hM : ∀ m, eM' (fM m) = t₃ (eM m))
    (ha : ∀ s y, (D'.a s).hom (t₁ y) = t₃ ((D.a s).hom y)) (x : U) :
    (SumDecomp.semilinearEquiv σ D' eU' heU' eV' heV' eM' heM' (fU x)).2 =
      fun s => fM ((SumDecomp.semilinearEquiv σ D eU heU eV heV eM heM x).2 s) := by
  funext s
  apply eM'.injective
  change eM' (eM'.symm ((D'.a s).hom (eU' (fU x)))) =
    eM' (fM (eM.symm ((D.a s).hom (eU x))))
  rw [LinearEquiv.apply_symm_apply, hM, LinearEquiv.apply_symm_apply, hU, ha]

end Semilinear

namespace KLR.Diagram.MatEnd

open CategoryTheory.Idempotents MulOpposite InductionAlong

universe v w

attribute [local instance] HomTensor.bimodule

variable {C : Type*} [Category.{v} C] [Preadditive C] {D₁ : Type*} [Category.{v} D₁]
  [Preadditive D₁] {ι κ₁ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ₁] [DecidableEq κ₁]
  {X : ι → C} {Y₁ : κ₁ → D₁}
  (F₁ : C ⥤ D₁) [F₁.Additive] {e₁ : ι → κ₁} (he₁ : Function.Injective e₁)
  (h₁ : ∀ i, F₁.obj (X i) = Y₁ (e₁ i))
  {E₁ : Karoubi (Mat_ D₁) ⥤ Karoubi (Mat_ C)} (adj₁ : mapKaroubi F₁.mapMat_ ⊣ E₁) [E₁.Additive]
  {G : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G.Additive] (eG : G ≅ mapKaroubi F₁.mapMat_ ⋙ E₁)
  {G' : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [G'.Additive]
  (hG' : Subsingleton ((toKaroubi _).obj (familySum X) ⟶ G'.obj ((toKaroubi _).obj (familySum X))))
  {H : Karoubi (Mat_ C) ⥤ Karoubi (Mat_ C)} [H.Additive] (hH : H = 𝟭 _)
  {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]

/-- **Restriction after induction with a vanishing complementary summand**: a decomposition of
the module functor of `G ≅ F₁' ⋙ E₁` as that of `G'` plus `ι₀` copies of the module functor of
the identity, where every morphism from the sum of `X` to `G'` of it is zero, gives
`Res_{φ₁} (Ind M φ₁) ≅ M^ι₀` as modules over the matrix ring of `X`. -/
def resIndEquivPiOfSubsingleton (M : Type (max w v)) [AddCommGroup M] [Module (MatEnd X)ᵐᵒᵖ M]
    (Dc : letI := HomTensor.transferModule (karoubiMatrixOp X) M
      SumDecomp (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M G)
        (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M G')
        (fun _ : ι₀ => HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
          ((toKaroubi _).obj (familySum X)) M H)) :
    Res (mapEmbOp F₁ he₁ h₁) (Ind M (mapEmbOp F₁ he₁ h₁)) ≃ₗ[(MatEnd X)ᵐᵒᵖ] (ι₀ → M) :=
  letI := HomTensor.transferModule (karoubiMatrixOp X) M
  haveI := hG'
  haveI : Subsingleton (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
      ((toKaroubi _).obj (familySum X)) M G') := BalancedTensor.subsingleton_of_left
  (SumDecomp.semilinearEquiv (karoubiMatrixOp X) Dc
    (resIndModuleEquivOfIso F₁ he₁ h₁ M adj₁ eG)
    (fun a m => resIndModuleEquivOfIso_smul F₁ he₁ h₁ M adj₁ eG a m)
    (LinearEquiv.ofSubsingleton Unit (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
      ((toKaroubi _).obj (familySum X)) M G'))
    (fun _ _ => Subsingleton.elim _ _)
    ((HomTensor.unitModuleEquivOfEq _ M H hH).restrictScalars ℤ)
    (fun a x => by
      rw [← HomTensor.transferModule_smul (σ := karoubiMatrixOp X) a x]
      exact (HomTensor.unitModuleEquivOfEq _ M H hH).map_smul (karoubiMatrixOp X a) x)).trans
    LinearEquiv.uniqueProd

/-- **Naturality of `resIndEquivPiOfSubsingleton`**: for the decomposition of modules induced
by a decomposition `Df` of functors, the isomorphism `Res_{φ₁} (Ind M φ₁) ≅ M^ι₀` carries
`Res (Ind f)` to `f^ι₀`. -/
theorem resIndEquivPiOfSubsingleton_map {M M₂ : Type (max w v)} [AddCommGroup M]
    [Module (MatEnd X)ᵐᵒᵖ M] [AddCommGroup M₂] [Module (MatEnd X)ᵐᵒᵖ M₂]
    (f : M →ₗ[(MatEnd X)ᵐᵒᵖ] M₂) (Df : SumDecomp G G' (fun _ : ι₀ => H))
    (x : Res (mapEmbOp F₁ he₁ h₁) (Ind M (mapEmbOp F₁ he₁ h₁))) :
    resIndEquivPiOfSubsingleton F₁ he₁ h₁ adj₁ eG hG' hH M₂
        (letI := HomTensor.transferModule (karoubiMatrixOp X) M₂;
          HomTensor.sumDecompModule _ _ M₂ Df) (Res.map (Ind.map f) x) =
      fun s => f (resIndEquivPiOfSubsingleton F₁ he₁ h₁ adj₁ eG hG' hH M
        (letI := HomTensor.transferModule (karoubiMatrixOp X) M;
          HomTensor.sumDecompModule _ _ M Df) x s) := by
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M
  let _ := HomTensor.transferModule (karoubiMatrixOp X) M₂
  have := hG'
  have : Subsingleton (HomTensor.tensorObj ((toKaroubi _).obj (familySum X))
      ((toKaroubi _).obj (familySum X)) M₂ G') := BalancedTensor.subsingleton_of_left
  let tf := HomTensor.transferLinearMap (karoubiMatrixOp X) f
  simp only [resIndEquivPiOfSubsingleton, LinearEquiv.trans_apply,
    LinearEquiv.uniqueProd_apply]
  exact SumDecomp.semilinearEquiv_snd_naturality (karoubiMatrixOp X) _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ (BalancedTensor.mapRight tf) (BalancedTensor.mapRight tf)
    (fun x => resIndModuleEquivOfIso_map F₁ he₁ h₁ f adj₁ eG x)
    (fun m => HomTensor.unitModuleEquivOfEq_map _ H hH tf m)
    (fun s y => HomTensor.natModuleMap_mapRight _ _ _ tf y) x

end KLR.Diagram.MatEnd

end Categorification
