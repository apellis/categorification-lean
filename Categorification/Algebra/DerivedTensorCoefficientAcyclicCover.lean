/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorAcyclicCover
import Categorification.Algebra.DerivedTensorSyzygyChain
import Categorification.Algebra.DerivedTensorCoefficientCovers

/-!
# Tor-acyclicity from acyclic covers of the coefficient

The coefficient form of `torAcyclic_of_acyclicCovers`. Fix a left `B`-module `Y`. A class `𝒞`
of right `B`-modules in which every member `N` has a cover `0 → K → P → N → 0` with `K ∈ 𝒞` and
`P ⊗ᴸ_B Y` acyclic consists of right modules `N` with `N ⊗ᴸ_B Y` acyclic. The triangles are
those of `CoefficientSyzygyChain`: the short exact sequence of coefficients is tensored with the
K-projective resolution of `Y` (`coefficientTensor_shortExact`), and the result is compared
with the derived tensor product by `derivedTensorHomologyResolutionIso`.

This is the dévissage of the right module in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22: the right factor of
the S-move pairing is resolved by standardizations of finite-dimensional modules, which are
covered by standardizations of free modules.

## Main definitions and results

* `CoefficientModule.ofRight`: a right module as a coefficient over `ℤ`.
* `nonempty_linearEquiv_derivedTensorHomology_coefficient_shortExact`: the dimension shift
  `Hʲ(N₃ ⊗ᴸ Y) ≅ Hʲ⁺¹(N₁ ⊗ᴸ Y)` along a short exact sequence of coefficients with acyclic
  middle term.
* `TorAcyclic.of_coefficient_shortExact`: acyclicity passes to extensions of coefficients.
* `TorAcyclic.of_coefficient_iso`: acyclicity is invariant under isomorphism of coefficients.
* `torAcyclic_of_acyclicCoefficientCovers`: Tor-acyclicity of a class of coefficients with
  acyclic covers.
* `torAcyclic_of_twoSidedCovers`: both dévissages together. If two classes of right and left
  modules have covers whose middle terms are pairwise Tor-acyclic, every pair of members is.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

/-- A right `B`-module as a coefficient `(ℤ, B)`-bimodule. -/
abbrev CoefficientModule.ofRight {B : Type} [Ring B] (N : ModuleCat.{0} Bᵐᵒᵖ) :
    CoefficientModule ℤ B :=
  ⟨N⟩

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]

/-- **Dimension shift in the coefficient** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): for a short exact sequence `0 → N₁ → N₂ → N₃ → 0` of right modules with
`N₂ ⊗ᴸ_B Y` acyclic, `Hʲ(N₃ ⊗ᴸ_B Y) ≅ Hʲ⁺¹(N₁ ⊗ᴸ_B Y)`. -/
theorem nonempty_linearEquiv_derivedTensorHomology_coefficient_shortExact
    (Y : ModuleCat.{0} B) {S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ)} (hS : S.ShortExact)
    (h₂ : TorAcyclic.{w} (k := ℤ) S.X₂ Y) (j : ℤ) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ j).obj ((derivedTensor.{w} ℤ B S.X₃).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj Y))) ≃ₗ[ℤ]
      (homologyFunctor (A := ℤ) ℤ (j + 1)).obj ((derivedTensor.{w} ℤ B S.X₁).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  let P := projectiveResolutionDGModel (projectiveResolution Y)
  let f : S.X₁ →ₗ[ℤ] S.X₂ := S.f.hom.restrictScalars ℤ
  let g : S.X₂ →ₗ[ℤ] S.X₃ := S.g.hom.restrictScalars ℤ
  have hf : ∀ (b : B) (m : S.X₁), f (op b • m) = op b • f m := fun b m => S.f.hom.map_smul _ m
  have hg : ∀ (b : B) (m : S.X₂), g (op b • m) = op b • g m := fun b m => S.g.hom.map_smul _ m
  have hex : Function.Exact f g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hsurj : Function.Surjective g := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hfg : g.comp f = 0 := LinearMap.ext fun x => hex.apply_apply_eq_zero x
  have hSP := coefficientTensor_shortExact f hf g hg hfg hinj hex hsurj P
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact _ hSP
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_obj₃_of_isZero_obj₂ _ hT (fun i =>
    (h₂ i).of_iso (derivedTensorHomologyResolutionIso (CoefficientModule.ofRight S.X₂) Y i)) j
  exact ⟨(derivedTensorHomologyResolutionIso (CoefficientModule.ofRight S.X₃) Y
    j).toLinearEquiv.symm.trans (e.trans
      (derivedTensorHomologyResolutionIso (CoefficientModule.ofRight S.X₁) Y
        (j + 1)).toLinearEquiv)⟩

/-- **Acyclicity passes to extensions of coefficients**: if `N₁ ⊗ᴸ_B Y` and `N₃ ⊗ᴸ_B Y` are
acyclic for a short exact sequence `0 → N₁ → N₂ → N₃ → 0`, so is `N₂ ⊗ᴸ_B Y`. -/
theorem TorAcyclic.of_coefficient_shortExact (Y : ModuleCat.{0} B)
    {S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ)} (hS : S.ShortExact)
    (h₁ : TorAcyclic.{w} (k := ℤ) S.X₁ Y) (h₃ : TorAcyclic.{w} (k := ℤ) S.X₃ Y) :
    TorAcyclic.{w} (k := ℤ) S.X₂ Y := by
  let P := projectiveResolutionDGModel (projectiveResolution Y)
  let f : S.X₁ →ₗ[ℤ] S.X₂ := S.f.hom.restrictScalars ℤ
  let g : S.X₂ →ₗ[ℤ] S.X₃ := S.g.hom.restrictScalars ℤ
  have hf : ∀ (b : B) (m : S.X₁), f (op b • m) = op b • f m := fun b m => S.f.hom.map_smul _ m
  have hg : ∀ (b : B) (m : S.X₂), g (op b • m) = op b • g m := fun b m => S.g.hom.map_smul _ m
  have hex : Function.Exact f g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hsurj : Function.Surjective g := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hfg : g.comp f = 0 := LinearMap.ext fun x => hex.apply_apply_eq_zero x
  have hSP := coefficientTensor_shortExact f hf g hg hfg hinj hex hsurj P
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact _ hSP
  intro n
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_obj₂_of_isZero_obj₁ _ hT (fun i =>
    (h₁ i).of_iso (derivedTensorHomologyResolutionIso (CoefficientModule.ofRight S.X₁) Y i)) n
  have h₃' := (h₃ n).of_iso
    (derivedTensorHomologyResolutionIso (CoefficientModule.ofRight S.X₃) Y n)
  have h₂' := (ModuleCat.isZero_iff_subsingleton.mpr
    (@Equiv.subsingleton _ _ e.toEquiv (ModuleCat.isZero_iff_subsingleton.mp h₃')))
  exact h₂'.of_iso
    (derivedTensorHomologyResolutionIso (CoefficientModule.ofRight S.X₂) Y n).symm

/-- Replace the last term of a short exact sequence by an isomorphic module. -/
private def shortComplexOfIsoX₃ (S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ)) {N : ModuleCat.{0} Bᵐᵒᵖ}
    (i : S.X₃ ≅ N) : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ) :=
  ShortComplex.mk S.f (S.g ≫ i.hom) (by rw [← Category.assoc, S.zero, zero_comp])

omit [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B] in
private theorem shortComplexOfIsoX₃_shortExact {S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ)}
    (hS : S.ShortExact) {N : ModuleCat.{0} Bᵐᵒᵖ} (i : S.X₃ ≅ N) :
    (shortComplexOfIsoX₃ S i).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := S) (S₂ := shortComplexOfIsoX₃ S i) (Iso.refl _) (Iso.refl _) i
      (by simp [shortComplexOfIsoX₃])
      (by simp [shortComplexOfIsoX₃])) hS

/-- **Tor-acyclicity from acyclic covers of the coefficient** (the dévissage of the right
module in B. Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): fix a left module
`Y`. If every member `N` of a class `𝒞` of right modules has a short exact sequence
`0 → K → P → N → 0` with `K ∈ 𝒞` and `P ⊗ᴸ_B Y` acyclic, then `N ⊗ᴸ_B Y` is acyclic for every
member `N` of `𝒞`. The covers need not form a finite resolution. -/
theorem torAcyclic_of_acyclicCoefficientCovers (Y : ModuleCat.{0} B)
    (𝒞 : ModuleCat.{0} Bᵐᵒᵖ → Prop)
    (hcov : ∀ N, 𝒞 N → ∃ S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ), S.ShortExact ∧ 𝒞 S.X₁ ∧
      TorAcyclic.{w} (k := ℤ) S.X₂ Y ∧ Nonempty (S.X₃ ≅ N))
    (N : ModuleCat.{0} Bᵐᵒᵖ) (hN : 𝒞 N) : TorAcyclic.{w} (k := ℤ) N Y := by
  have key : ∀ m : ℕ, ∀ N, 𝒞 N → IsZero ((homologyFunctor (A := ℤ) ℤ (-(m : ℤ))).obj
      ((derivedTensor.{w} ℤ B N).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
    intro m
    induction m with
    | zero =>
      intro N hN
      obtain ⟨S, hS, -, hP, ⟨i⟩⟩ := hcov N hN
      obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_coefficient_shortExact Y
        (shortComplexOfIsoX₃_shortExact hS i) hP 0
      have hz := isZero_derivedTensorHomology_module_of_pos.{w} (k := ℤ) (B := B)
        (S.X₁ : Type) Y (n := 0 + 1) (by norm_num)
      exact ModuleCat.isZero_iff_subsingleton.mpr
        (@Equiv.subsingleton _ _ e.toEquiv (ModuleCat.isZero_iff_subsingleton.mp hz))
    | succ m ih =>
      intro N hN
      obtain ⟨S, hS, hK, hP, ⟨i⟩⟩ := hcov N hN
      obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_coefficient_shortExact Y
        (shortComplexOfIsoX₃_shortExact hS i) hP (-((m + 1 : ℕ) : ℤ))
      have h1 : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
      rw [h1] at e
      exact ModuleCat.isZero_iff_subsingleton.mpr
        (@Equiv.subsingleton _ _ e.toEquiv (ModuleCat.isZero_iff_subsingleton.mp (ih S.X₁ hK)))
  intro n
  rcases lt_or_ge 0 n with hn | hn
  · exact isZero_derivedTensorHomology_module_of_pos (k := ℤ) (N : Type) Y hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    exact key m N hN

/-- The zero coefficient is acyclic against every module. -/
theorem TorAcyclic.of_subsingleton_coefficient (Y : ModuleCat.{0} B) (N : ModuleCat.{0} Bᵐᵒᵖ)
    [Subsingleton N] : TorAcyclic.{w} (k := ℤ) N Y := fun n => by
  let R := projectiveResolution Y
  let a := @asIso _ _ _ _ (Q.map (projectiveResolutionDGAugToOrdinary R))
    ((isIso_Q_map_iff _).mpr (projectiveResolutionDGAugToOrdinary_quasiIso R))
  exact (isZero_derivedTensorHomology_coefficient_of_subsingleton.{w}
    (projectiveResolutionDGModel_kProjective R) N n).of_iso
    ((homologyFunctor (A := ℤ) ℤ n).mapIso ((derivedTensor.{w} ℤ B N).mapIso a)).symm

/-- The short complex `N → N' → 0` of an isomorphism. -/
private def isoShortComplex {N N' : ModuleCat.{0} Bᵐᵒᵖ} (e : N ≅ N') :
    ShortComplex (ModuleCat.{0} Bᵐᵒᵖ) :=
  ShortComplex.mk e.hom (0 : N' ⟶ ModuleCat.of Bᵐᵒᵖ PUnit) comp_zero

omit [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B] in
private theorem isoShortComplex_shortExact {N N' : ModuleCat.{0} Bᵐᵒᵖ} (e : N ≅ N') :
    (isoShortComplex e).ShortExact := by
  have hm : Mono (isoShortComplex e).f := inferInstanceAs (Mono e.hom)
  have hs : Subsingleton (isoShortComplex e).X₃ := inferInstanceAs (Subsingleton PUnit)
  have he : Epi (isoShortComplex e).g :=
    (ModuleCat.epi_iff_surjective _).mpr fun _ => ⟨0, Subsingleton.elim _ _⟩
  refine ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr fun y =>
    ⟨fun _ => ⟨e.inv.hom y, ?_⟩, fun _ => Subsingleton.elim _ _⟩⟩
  change e.hom.hom (e.inv.hom y) = y
  exact congrArg (fun φ : N' ⟶ N' => φ.hom y) e.inv_hom_id

/-- **Acyclicity is invariant under isomorphism of coefficients.** -/
theorem TorAcyclic.of_coefficient_iso (Y : ModuleCat.{0} B) {N N' : ModuleCat.{0} Bᵐᵒᵖ}
    (e : N ≅ N') (h : TorAcyclic.{w} (k := ℤ) N Y) : TorAcyclic.{w} (k := ℤ) N' Y :=
  haveI : Subsingleton (ModuleCat.of Bᵐᵒᵖ PUnit) := inferInstanceAs (Subsingleton PUnit)
  TorAcyclic.of_coefficient_shortExact (S := isoShortComplex e) Y
    (isoShortComplex_shortExact e) h
    (TorAcyclic.of_subsingleton_coefficient Y (ModuleCat.of Bᵐᵒᵖ PUnit))

/-- **Both dévissages** (B. Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): let
`𝒞_X` be a class of right modules and `𝒞_Y` a class of left modules, each member of which has a
cover `0 → K → P → Z → 0` with `K` in the same class and `P` in `𝒫_X` (resp. `𝒫_Y`). If
`P ⊗ᴸ_B P'` is acyclic for all `P ∈ 𝒫_X` and `P' ∈ 𝒫_Y`, then `X ⊗ᴸ_B Y` is acyclic for all
`X ∈ 𝒞_X` and `Y ∈ 𝒞_Y`. -/
theorem torAcyclic_of_twoSidedCovers (𝒞X 𝒫X : ModuleCat.{0} Bᵐᵒᵖ → Prop)
    (𝒞Y 𝒫Y : ModuleCat.{0} B → Prop)
    (hX : ∀ N, 𝒞X N → ∃ S : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ), S.ShortExact ∧ 𝒞X S.X₁ ∧
      𝒫X S.X₂ ∧ Nonempty (S.X₃ ≅ N))
    (hY : ∀ Y, 𝒞Y Y → ∃ S : ShortComplex (ModuleCat.{0} B), S.ShortExact ∧ 𝒞Y S.X₁ ∧
      𝒫Y S.X₂ ∧ Nonempty (S.X₃ ≅ Y))
    (hP : ∀ P, 𝒫X P → ∀ P', 𝒫Y P' → TorAcyclic.{w} (k := ℤ) P P')
    (N : ModuleCat.{0} Bᵐᵒᵖ) (hN : 𝒞X N) (Y : ModuleCat.{0} B) (hYY : 𝒞Y Y) :
    TorAcyclic.{w} (k := ℤ) N Y := by
  have hPY : ∀ P, 𝒫X P → ∀ Y, 𝒞Y Y → TorAcyclic.{w} (k := ℤ) P Y := fun P hP' =>
    torAcyclic_of_acyclicCovers (k := ℤ) P 𝒞Y fun Y hY' => by
      obtain ⟨S, hS, hK, hM, hi⟩ := hY Y hY'
      exact ⟨S, hS, hK, hP P hP' S.X₂ hM, hi⟩
  refine torAcyclic_of_acyclicCoefficientCovers Y 𝒞X (fun N hN' => ?_) N hN
  obtain ⟨S, hS, hK, hM, hi⟩ := hX N hN'
  exact ⟨S, hS, hK, hPY S.X₂ hM Y hYY, hi⟩

end Categorification
