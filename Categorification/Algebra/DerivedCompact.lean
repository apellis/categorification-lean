/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrdinaryProjectiveResolutionDG
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.DGShortExactTriangle
import DG.Derived.PerfectCompact
import Categorification.Algebra.ModuleFiltration
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

set_option backward.isDefEq.respectTransparency false

/-!
# Compact objects of derived categories of rings

For a ring `S` (in degree `0`), a finitely generated module of finite projective dimension over
a Noetherian ring, placed in degree `0`, is compact in `D(S)`
(`isCompact_Q_inDegreeZero_of_hasProjectiveDimensionLT`). A triangulated functor between
derived categories of dg rings preserves compact objects as soon as it sends the regular module
to a compact object (`isCompact_obj_of_isCompact_obj_self`), since the compact objects are the
thick closure of the regular module (Keller).

This is used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 6.13: the braiding functors preserve perfect complexes.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

universe u

/-- **A triangulated functor sending the regular module to a compact object preserves compact
objects.** -/
theorem isCompact_obj_of_isCompact_obj_self {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
    [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{u, u} A]
    [HasDerivedCategory.{u, u} B] (F : DerivedCategory.{u, u} A ⥤ DerivedCategory.{u, u} B)
    [F.CommShift ℤ] [F.IsTriangulated] (h : IsCompact.{u} (F.obj (Q.obj (DGModuleCat.of A A))))
    {X : DerivedCategory.{u, u} A} (hX : IsCompact.{u} X) : IsCompact.{u} (F.obj X) := by
  have hX' : ThickClosure
      (fun Y : DerivedCategory.{u, u} A => ∃ _ : Unit, Q.obj (DGModuleCat.of A A) = Y) X := by
    rw [thickClosure_self_eq_isCompact]
    exact hX
  refine thickClosure_le ((isThick_isCompact _).comap F) ?_ X hX'
  rintro _ ⟨-, rfl⟩
  exact h

variable {S : Type u} [Ring S] [HasDerivedCategory.{u, u} S]

/-- A finitely generated projective module, placed in degree `0`, is compact. -/
theorem isCompact_Q_inDegreeZero_of_projective (P : ModuleCat.{u} S) [Module.Finite S P]
    [Module.Projective S P] :
    IsCompact.{u} (Q.obj (DGModuleCat.of S (InDegreeZero P))) :=
  DegreeZero.isCompact_Q_obj_of_isPerfectComplex S _
    ((IsPerfectComplex.single ⟨inferInstance, inferInstance⟩ 0).of_iso
      (complexFunctorInDegreeZeroIso P))

/-- **A finitely generated module of finite projective dimension over a Noetherian ring, placed
in degree `0`, is compact.** -/
theorem isCompact_Q_inDegreeZero_of_hasProjectiveDimensionLT [IsNoetherianRing S] (n : ℕ) :
    ∀ (M : ModuleCat.{u} S) [Module.Finite S M], HasProjectiveDimensionLT M (n + 1) →
      IsCompact.{u} (Q.obj (DGModuleCat.of S (InDegreeZero M))) := by
  induction n with
  | zero =>
    intro M _ hM
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
    have : Module.Projective S M := (IsProjective.iff_projective M).mpr this
    exact isCompact_Q_inDegreeZero_of_projective M
  | succ n ih =>
    intro M _ hM
    obtain ⟨r, g, hg⟩ := Module.Finite.exists_fin' S M
    let K := LinearMap.ker g
    let T := ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom g)
      (by ext x; exact x.2)
    have hT : T.ShortExact := by
      have : Mono T.f := (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
      have : Epi T.g := (ModuleCat.epi_iff_surjective _).2 hg
      exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
        (LinearMap.exact_subtype_ker_map g)⟩
    have : Projective (ModuleCat.of S (Fin r → S)) :=
      (IsProjective.iff_projective (Fin r → S)).mp inferInstance
    have hF : HasProjectiveDimensionLT (ModuleCat.of S (Fin r → S)) (n + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
    have hK := hT.hasProjectiveDimensionLT_X₁ (n + 1) hF hM
    have hKc := ih (ModuleCat.of S K) hK
    have hFc := isCompact_Q_inDegreeZero_of_projective (ModuleCat.of S (Fin r → S))
    obtain ⟨δ, hδ⟩ := exists_distinguished_of_shortExact _
      (degreeZeroModuleFunctor_shortExact _ hT)
    exact (isThick_isCompact _).ext₂ _ (rot_of_distTriang _ hδ) hFc (hKc.shift 1)

/-- **A module with a finite filtration by modules that are compact in degree `0` is compact in
degree `0`.** -/
theorem ModuleFiltration.HasFiltration.isCompact_Q {ι : Type*} {L : ι → ModuleCat.{u} S}
    {m : List ι} {Y : ModuleCat.{u} S} (h : ModuleFiltration.HasFiltration L m Y)
    (hL : ∀ c ∈ m, IsCompact.{u} (Q.obj (DGModuleCat.of S (InDegreeZero (L c))))) :
    IsCompact.{u} (Q.obj (DGModuleCat.of S (InDegreeZero Y))) := by
  induction h with
  | @zero Y hY =>
    refine (isThick_isCompact _).of_isZero (Q.map_isZero ?_)
    exact (degreeZeroModuleFunctor S).map_isZero (ModuleCat.isZero_of_subsingleton Y)
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have hX := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    have hZc : IsCompact.{u} (Q.obj (DGModuleCat.of S (InDegreeZero Z))) :=
      (hL c List.mem_cons_self).of_iso (Q.mapIso ((degreeZeroModuleFunctor S).mapIso
        e.toModuleIso))
    let T := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; exact hfg.apply_apply_eq_zero x)
    have hT : T.ShortExact := by
      have : Mono T.f := (ModuleCat.mono_iff_injective _).2 hf
      have : Epi T.g := (ModuleCat.epi_iff_surjective _).2 hg
      exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg⟩
    obtain ⟨δ, hδ⟩ := exists_distinguished_of_shortExact _
      (degreeZeroModuleFunctor_shortExact _ hT)
    exact (isThick_isCompact _).ext₂ _ hδ hX hZc

end Categorification
