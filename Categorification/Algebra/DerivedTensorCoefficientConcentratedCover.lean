/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficientAcyclicCover
import Categorification.Algebra.DerivedTensorOrdinaryLinear
import Categorification.Algebra.DerivedTensorCoefficientRetract

/-!
# Tor concentrated in degree zero from covers of the coefficient

The coefficient form of `isZero_derivedTensorHomology_of_concentratedCovers`. Fix a left
`B`-module `Y`. Let `𝒞` be a class of right `B`-modules in which every member `N` has a cover
`0 → K → P → N → 0` with `K ∈ 𝒞`, `P ⊗ᴸ_B Y` without higher Tor and
`Tor₀(K, Y) → Tor₀(P, Y)` injective. Then no member of `𝒞` has higher Tor against `Y`: the long
exact sequence gives `Tor₁(N, Y) = ker(Tor₀(K, Y) → Tor₀(P, Y)) = 0` and
`Tor_{m+1}(N, Y) ≅ Tor_m(K, Y)` for `m ≥ 1`, and induction on `m` runs over the whole class.

The triangles are those of `CoefficientSyzygyChain`: the short exact sequence of coefficients
tensored with the K-projective resolution of `Y`. The injectivity hypothesis is stated for the
derived coefficient map `derivedTensorCoefficientMap`, whose degree-zero part is `f ⊗ id` on
the ordinary tensor products (`ambientH0CoefficientMap_tmul`).

This is the diagonal dimension shift of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22 (gap (c)), on the side where the
varying factor is the right module: in the S-move pairing the right factor is the reflection of
`𝕊(P_∅ ⊠ S(M))` for arbitrary finite-dimensional `M`, the left factor a fixed summand of a
reflected standard.

## Main results

* `coefficientResolutionComparison_naturality`: the comparison of the coefficient triangle with
  the derived tensor product commutes with the coefficient maps.
* `isZero_derivedTensorHomology_of_concentratedCoefficientCovers`: no higher Tor for a class of
  coefficients with covers without higher Tor whose `Tor₀` map is injective.
* `mono_homology_derivedTensorCoefficientMap_of_injective`: that `Tor₀` map is injective when
  `f ⊗_B id` is injective on the ordinary tensor products.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} B]

section Comparison

variable {k : Type} [CommRing k] [HasDerivedCategory.{w, 0} k]

/-- The comparison `Q(N ⊗_B P) → N ⊗ᴸ_B Y` for the K-projective resolution `P` of `Y`. -/
def coefficientResolutionComparison (N : CoefficientModule k B) (Y : ModuleCat.{0} B) :
    Q.obj ((DGModuleCat.tensorFunctor k (InDegreeZero N)).obj
        (projectiveResolutionDGModel (projectiveResolution Y))) ≅
      (derivedTensor.{w} k B N).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)) :=
  (derivedTensorObjIso (projectiveResolutionDGModel_kProjective (projectiveResolution Y))).symm ≪≫
    (derivedTensor.{w} k B N).mapIso
      (@asIso _ _ _ _ (Q.map (projectiveResolutionDGAugToOrdinary (projectiveResolution Y)))
        ((isIso_Q_map_iff _).mpr
          (projectiveResolutionDGAugToOrdinary_quasiIso (projectiveResolution Y))))

/-- **Naturality of the resolution comparison in the coefficient**: for a map `f : N → N'` of
coefficients, the ordinary coefficient map on `N ⊗_B P` corresponds to the derived coefficient
map on `N ⊗ᴸ_B Y`. -/
theorem coefficientResolutionComparison_naturality {N N' : CoefficientModule k B}
    (f : N →ₗ[k] N') (hf : ∀ (b : B) (m : N), f (op b • m) = op b • f m)
    (Y : ModuleCat.{0} B) :
    Q.map ((ordinaryTensorCoefficientMap f hf).app
        (projectiveResolutionDGModel (projectiveResolution Y))) ≫
      (coefficientResolutionComparison.{w} N' Y).hom =
    (coefficientResolutionComparison.{w} N Y).hom ≫
      (derivedTensorCoefficientMap f hf).app (Q.obj ((degreeZeroModuleFunctor B).obj Y)) := by
  have hP := projectiveResolutionDGModel_kProjective (projectiveResolution Y)
  have h₁ := derivedTensorObjIso_coefficient_naturality.{0, w} f hf hP
  have h₂ := (derivedTensorCoefficientMap.{0, w} f hf).naturality
    (Q.map (projectiveResolutionDGAugToOrdinary (projectiveResolution Y)))
  have h₁' : Q.map ((ordinaryTensorCoefficientMap f hf).app
      (projectiveResolutionDGModel (projectiveResolution Y))) ≫
      (derivedTensorObjIso (M := N') hP).inv =
      (derivedTensorObjIso (M := N) hP).inv ≫ (derivedTensorCoefficientMap f hf).app
        (Q.obj (projectiveResolutionDGModel (projectiveResolution Y))) := by
    rw [Iso.comp_inv_eq, Category.assoc, h₁, Iso.inv_hom_id_assoc]
  change _ ≫ ((derivedTensorObjIso (M := N') hP).inv ≫ (derivedTensor.{w} k B N').map
      (Q.map (projectiveResolutionDGAugToOrdinary (projectiveResolution Y)))) =
    ((derivedTensorObjIso (M := N) hP).inv ≫ (derivedTensor.{w} k B N).map
      (Q.map (projectiveResolutionDGAugToOrdinary (projectiveResolution Y)))) ≫ _
  rw [← Category.assoc, h₁']
  exact (Category.assoc _ _ _).trans
    ((congrArg ((derivedTensorObjIso (M := N) hP).inv ≫ ·) h₂.symm).trans
      (Category.assoc _ _ _).symm)

end Comparison

variable [HasDerivedCategory.{w, 0} ℤ]

noncomputable local instance coefficientConcentratedShiftSequence :
    (homologyFunctor (A := ℤ) ℤ 0).ShiftSequence ℤ := by
  letI : (DG.HomotopyCategory.homologyFunctor.{0} ℤ ℤ 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} ℤ ℤ ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)
        0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh ℤ 0) ℤ
    (homologyFunctor ℤ) (homologyFunctorFactorsh ℤ)

/-- In a distinguished triangle with `Hʲ(obj₂) = 0` and `Hʲ⁺¹(obj₁) = 0`, `Hʲ(obj₃) = 0`. -/
private theorem isZero_homology_obj₃_of_isZero (T : Triangle (DerivedCategory.{w, 0} ℤ))
    (hT : T ∈ distTriang _) (j : ℤ) (h₂ : IsZero ((homologyFunctor (A := ℤ) ℤ j).obj T.obj₂))
    (h₁ : IsZero ((homologyFunctor (A := ℤ) ℤ (j + 1)).obj T.obj₁)) :
    IsZero ((homologyFunctor (A := ℤ) ℤ j).obj T.obj₃) := by
  let G := homologyFunctor (A := ℤ) ℤ 0
  have es (j : ℤ) : G.shift j = homologyFunctor ℤ j := rfl
  have hmono : Mono (G.homologySequenceδ T j (j + 1) rfl) :=
    (G.homologySequence_exact₃ T hT j (j + 1) rfl).mono_g
      (((es j).symm ▸ h₂ : IsZero ((G.shift j).obj T.obj₂)).eq_of_src _ _)
  have hz : IsZero ((G.shift (j + 1)).obj T.obj₁) := by rw [es]; exact h₁
  rw [← es]
  exact IsZero.of_mono (G.homologySequenceδ T j (j + 1) rfl) hz

/-- **Tor concentrated in degree zero from covers of the coefficient** (the diagonal dimension
shift in B. Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, on the coefficient
side): fix a left module `Y`. If every member `N` of a class `𝒞` of right modules has a short
exact sequence `0 → K → P → N → 0` with `K ∈ 𝒞`, `P ⊗ᴸ_B Y` without cohomology outside degree
zero, and the degree-zero coefficient map `Tor₀(K, Y) → Tor₀(P, Y)` injective, then `N ⊗ᴸ_B Y`
has no cohomology outside degree zero for every member `N` of `𝒞`. -/
theorem isZero_derivedTensorHomology_of_concentratedCoefficientCovers (Y : ModuleCat.{0} B)
    (𝒞 : ModuleCat.{0} Bᵐᵒᵖ → Prop)
    (hcov : ∀ N, 𝒞 N → ∃ S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ), S.ShortExact ∧ 𝒞 S.X₁ ∧
      (∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ B S.X₂).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y))))) ∧
      Mono ((homologyFunctor (A := ℤ) ℤ 0).map ((derivedTensorCoefficientMap
        (S.f.hom.restrictScalars ℤ) (fun b m => S.f.hom.map_smul (op b) m)).app
          (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) ∧ Nonempty (S.X₃ ≅ N))
    (N : ModuleCat.{0} Bᵐᵒᵖ) (hN : 𝒞 N) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ B N).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  -- Transport along an isomorphism of coefficients.
  have hiso : ∀ {N N' : ModuleCat.{0} Bᵐᵒᵖ} (_ : N ≅ N') (j : ℤ),
      IsZero ((homologyFunctor (A := ℤ) ℤ j).obj
        ((derivedTensor.{w} ℤ B N).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) →
      IsZero ((homologyFunctor (A := ℤ) ℤ j).obj
        ((derivedTensor.{w} ℤ B N').obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
    intro N N' e j h
    let g : N →ₗ[ℤ] N' := e.hom.hom.restrictScalars ℤ
    let g' : N' →ₗ[ℤ] N := e.inv.hom.restrictScalars ℤ
    have hg : ∀ (b : B) (m : N), g (op b • m) = op b • g m := fun b m => e.hom.hom.map_smul _ m
    have hg' : ∀ (b : B) (m : N'), g' (op b • m) = op b • g' m :=
      fun b m => e.inv.hom.map_smul _ m
    -- `N'` is a retract of `N` in the derived coefficient.
    exact isZero_derivedTensorHomology_coefficient_retract g' hg' g hg
      (LinearMap.ext fun x => congrArg (fun φ => φ.hom x) e.inv_hom_id) Y j h
  have key : ∀ m : ℕ, ∀ N, 𝒞 N → IsZero ((homologyFunctor (A := ℤ) ℤ (-((m + 1 : ℕ) : ℤ))).obj
      ((derivedTensor.{w} ℤ B N).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
    intro m
    induction m with
    | zero =>
      intro N hN
      obtain ⟨S, hS, -, hP, hmono, ⟨i⟩⟩ := hcov N hN
      refine hiso i _ ?_
      let P := projectiveResolutionDGModel (projectiveResolution Y)
      let f : CoefficientModule.ofRight S.X₁ →ₗ[ℤ] CoefficientModule.ofRight S.X₂ :=
        S.f.hom.restrictScalars ℤ
      let g : CoefficientModule.ofRight S.X₂ →ₗ[ℤ] CoefficientModule.ofRight S.X₃ :=
        S.g.hom.restrictScalars ℤ
      have hf : ∀ (b : B) (m : CoefficientModule.ofRight S.X₁), f (op b • m) = op b • f m :=
        fun b m => S.f.hom.map_smul _ m
      have hg : ∀ (b : B) (m : CoefficientModule.ofRight S.X₂), g (op b • m) = op b • g m :=
        fun b m => S.g.hom.map_smul _ m
      have hex : Function.Exact f g :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
      have hinj : Function.Injective f := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
      have hsurj : Function.Surjective g := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
      have hfg : g.comp f = 0 := LinearMap.ext fun x => hex.apply_apply_eq_zero x
      have hSP := coefficientTensor_shortExact f hf g hg hfg hinj hex hsurj P
      obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact _ hSP
      have hP' := (hP (-1) (by norm_num)).of_iso
        ((homologyFunctor (A := ℤ) ℤ (-1)).mapIso
          (coefficientResolutionComparison (CoefficientModule.ofRight S.X₂) Y))
      have hn := congrArg (homologyFunctor (A := ℤ) ℤ 0).map
        (coefficientResolutionComparison_naturality.{w} f hf Y)
      simp only [Functor.map_comp] at hn
      have hm : Mono ((homologyFunctor (A := ℤ) ℤ 0).map
          (Q.map ((ordinaryTensorCoefficientMap f hf).app P))) := by
        have : Mono ((homologyFunctor (A := ℤ) ℤ 0).map
            (Q.map ((ordinaryTensorCoefficientMap f hf).app P)) ≫
            (homologyFunctor (A := ℤ) ℤ 0).map
              (coefficientResolutionComparison (CoefficientModule.ofRight S.X₂) Y).hom) := by
          rw [hn]
          exact mono_comp _ _
        exact mono_of_mono _ ((homologyFunctor (A := ℤ) ℤ 0).map
          (coefficientResolutionComparison (CoefficientModule.ofRight S.X₂) Y).hom)
      have h := isZero_homology_neg_one_obj₃ _ hT hP' hm
      exact h.of_iso ((homologyFunctor (A := ℤ) ℤ (-1)).mapIso
        (coefficientResolutionComparison (CoefficientModule.ofRight S.X₃) Y)).symm
    | succ m ih =>
      intro N hN
      obtain ⟨S, hS, hK, hP, -, ⟨i⟩⟩ := hcov N hN
      refine hiso i _ ?_
      let P := projectiveResolutionDGModel (projectiveResolution Y)
      let f : CoefficientModule.ofRight S.X₁ →ₗ[ℤ] CoefficientModule.ofRight S.X₂ :=
        S.f.hom.restrictScalars ℤ
      let g : CoefficientModule.ofRight S.X₂ →ₗ[ℤ] CoefficientModule.ofRight S.X₃ :=
        S.g.hom.restrictScalars ℤ
      have hf : ∀ (b : B) (m : CoefficientModule.ofRight S.X₁), f (op b • m) = op b • f m :=
        fun b m => S.f.hom.map_smul _ m
      have hg : ∀ (b : B) (m : CoefficientModule.ofRight S.X₂), g (op b • m) = op b • g m :=
        fun b m => S.g.hom.map_smul _ m
      have hex : Function.Exact f g :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
      have hinj : Function.Injective f := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
      have hsurj : Function.Surjective g := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
      have hfg : g.comp f = 0 := LinearMap.ext fun x => hex.apply_apply_eq_zero x
      have hSP := coefficientTensor_shortExact f hf g hg hfg hinj hex hsurj P
      obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact _ hSP
      let j : ℤ := -((m + 1 + 1 : ℕ) : ℤ)
      have hj : j + 1 = -((m + 1 : ℕ) : ℤ) := by simp only [j]; push_cast; ring
      have hP' := (hP j (by omega)).of_iso
        ((homologyFunctor (A := ℤ) ℤ j).mapIso
          (coefficientResolutionComparison (CoefficientModule.ofRight S.X₂) Y))
      have hK' := (ih S.X₁ hK).of_iso ((homologyFunctor (A := ℤ) ℤ _).mapIso
        (coefficientResolutionComparison (CoefficientModule.ofRight S.X₁) Y))
      rw [← hj] at hK'
      have h := isZero_homology_obj₃_of_isZero _ hT j hP' hK'
      exact h.of_iso ((homologyFunctor (A := ℤ) ℤ j).mapIso
        (coefficientResolutionComparison (CoefficientModule.ofRight S.X₃) Y)).symm
  rcases lt_or_gt_of_ne hn with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m + 1 : ℕ) : ℤ) := ⟨(-n).toNat - 1, by omega⟩
    exact key m N hN
  · exact isZero_derivedTensorHomology_module_of_pos (k := ℤ) (N : Type) Y hn

/-- **The `Tor₀` map of a coefficient map is `f ⊗ id`**: the degree-zero derived coefficient map
of a map `f : N → N'` of right modules is injective when `f ⊗_B id_Y` is. -/
theorem mono_homology_derivedTensorCoefficientMap_of_injective {N N' : ModuleCat.{0} Bᵐᵒᵖ}
    (f : N ⟶ N') (Y : ModuleCat.{0} B)
    (hinj : Function.Injective (TensorProductOver.map f.hom (LinearMap.id : Y →ₗ[B] Y))) :
    Mono ((homologyFunctor (A := ℤ) ℤ 0).map ((derivedTensorCoefficientMap
      (f.hom.restrictScalars ℤ) (fun b m => f.hom.map_smul (op b) m)).app
        (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  let φ := (homologyFunctor (A := ℤ) ℤ 0).map ((derivedTensorCoefficientMap
    (f.hom.restrictScalars ℤ) (fun b m => f.hom.map_smul (op b) m)).app
      (Q.obj ((degreeZeroModuleFunctor B).obj Y)))
  let e := ambientDerivedTensorH0Equiv (k := ℤ) (A := B) (N := N) (Y : Type)
  let e' := ambientDerivedTensorH0Equiv (k := ℤ) (A := B) (N := N') (Y : Type)
  have hφ : ∀ z, e' (φ.hom (e.symm z)) = TensorProductOver.map f.hom LinearMap.id z := by
    intro z
    induction z using TensorProductOver.induction_on with
    | zero =>
      have h0 : φ.hom (e.symm 0) = 0 := by rw [map_zero]; exact φ.hom.map_zero
      rw [h0]
      exact e'.map_zero.trans (map_zero _).symm
    | tmul m y =>
      exact ambientH0CoefficientMap_tmul (k := ℤ) (A := B) (N := N) (N' := N') (X := Y)
        (f.hom.restrictScalars ℤ) (fun b m => f.hom.map_smul (op b) m) m y
    | add x y hx hy =>
      have h0 : φ.hom (e.symm (x + y)) = φ.hom (e.symm x) + φ.hom (e.symm y) := by
        rw [map_add]; exact φ.hom.map_add _ _
      rw [h0, map_add]
      exact (e'.map_add (φ.hom (e.symm x)) (φ.hom (e.symm y))).trans (by rw [hx, hy])
  have key : ∀ a b, e' (φ.hom (e.symm a)) = e' (φ.hom (e.symm b)) → a = b := fun a b h => by
    rw [hφ, hφ] at h
    exact hinj h
  rw [ModuleCat.mono_iff_injective]
  intro a b hab
  have h := key (e a) (e b) (by
    erw [e.symm_apply_apply, e.symm_apply_apply]
    exact congrArg e' hab)
  exact e.injective h

end Categorification
