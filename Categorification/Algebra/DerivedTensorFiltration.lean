/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration
import Categorification.Algebra.DerivedTensorHomology
import Categorification.Algebra.DerivedTensorTriangulated
import DG.Derived.DimensionShift

/-!
# Derived vanishing for filtered modules

An ordinary module filtration controls nonzero cohomology of a triangulated
functor applied to a module placed in degree zero. Webster uses this in the
dimension shift in Lemma 6.8, (6.21).
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section
namespace Categorification

universe w u
variable {A B : Type u} [Ring A] [Ring B]

/-- Regard an ordinary module as a DG module concentrated in degree zero. -/
def degreeZeroModuleFunctor (B : Type u) [Ring B] : ModuleCat.{u} B ⥤ DGModuleCat.{u} B where
  obj X := DGModuleCat.of B (InDegreeZero X)
  map f := DGModuleCat.ofHom
    { toLinearMap := f.hom
      map_mem' := fun {n x} hx => by
        rw [InDegreeZero.mem_grading_iff] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (h.symm ▸ map_zero f.hom)
      map_d' := fun x => by
        change f.hom 0 = 0
        exact map_zero _ }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

instance : (degreeZeroModuleFunctor B).Additive where
  map_add := by
    intros
    ext x
    rfl

theorem degreeZeroModuleFunctor_shortExact (S : ShortComplex (ModuleCat.{u} B))
    (hS : S.ShortExact) : (S.map (degreeZeroModuleFunctor B)).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  apply (DGModuleCat.shortExact_iff _).mpr
  exact ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact,
    (ModuleCat.epi_iff_surjective _).mp inferInstance⟩

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

namespace ModuleFiltration.HasFiltration

variable {ι : Type*} {L : ι → ModuleCat.{u} B}

/-- Vanishing of derived cohomology on all subquotients of a finite
filtration implies vanishing in the same degree on the filtered module. -/
theorem isZero_derivedHomology (F : DerivedCategory.{w, u} B ⥤ DerivedCategory.{w, u} A)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (n : ℤ)
    {m : List ι} {Y : ModuleCat.{u} B} (h : HasFiltration L m Y)
    (hL : ∀ c ∈ m, IsZero ((homologyFunctor ℤ n).obj
      (F.obj (Q.obj ((degreeZeroModuleFunctor B).obj (L c)))))) :
    IsZero ((homologyFunctor ℤ n).obj (F.obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  let G := degreeZeroModuleFunctor B ⋙ Q ⋙ F ⋙ homologyFunctor ℤ n
  induction h with
  | zero hY =>
    exact G.map_isZero (ModuleCat.isZero_iff_subsingleton.mpr hY)
  | @cons X Y Z f g m c hf hex hg _ he ih =>
    have hzero : ModuleCat.ofHom f ≫ ModuleCat.ofHom g = 0 := by
      ext x
      exact hex.apply_apply_eq_zero x
    let S : ShortComplex (ModuleCat.{u} B) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) hzero
    have hS : S.ShortExact := by
      let : Mono S.f := (ModuleCat.mono_iff_injective _).mpr hf
      let : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr hg
      exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex⟩
    obtain ⟨e⟩ := he
    have hz : IsZero (G.obj Z) :=
      (hL c (List.mem_cons_self)).of_iso (G.mapIso e.toModuleIso)
    exact isZero_homology_middle_of_shortExact ℤ F (S.map (degreeZeroModuleFunctor B))
      (degreeZeroModuleFunctor_shortExact S hS) n
      (ih (fun d hd => hL d (List.mem_cons_of_mem _ hd))) hz

end ModuleFiltration.HasFiltration

/-- The filtered-kernel dimension shift in Webster, arXiv:1309.3796v2,
Lemma 6.8, (6.21). For a short exact presentation, the source requires
vanishing on the kernel's higher standard layers and on the projective
middle term, together with injectivity on degree-zero cohomology. -/
theorem isZero_derivedHomology_quotient_of_filtered_kernel {ι : Type*}
    (F : DerivedCategory.{w, u} B ⥤ DerivedCategory.{w, u} A)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (S : ShortComplex (ModuleCat.{u} B)) (hS : S.ShortExact)
    {L : ι → ModuleCat.{u} B} {m : List ι}
    (hK : ModuleFiltration.HasFiltration L m S.X₁)
    (hL : ∀ c ∈ m, ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor ℤ n).obj
      (F.obj (Q.obj ((degreeZeroModuleFunctor B).obj (L c))))))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor ℤ n).obj
      (F.obj (Q.obj ((degreeZeroModuleFunctor B).obj S.X₂)))))
    (h₀ : Mono ((homologyFunctor ℤ 0).map
      (F.map (Q.map ((degreeZeroModuleFunctor B).map S.f)))))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((homologyFunctor ℤ n).obj
      (F.obj (Q.obj ((degreeZeroModuleFunctor B).obj S.X₃)))) := by
  exact isZero_homology_obj_of_shortExact ℤ F (S.map (degreeZeroModuleFunctor B))
    (degreeZeroModuleFunctor_shortExact S hS)
    (fun j hj => hK.isZero_derivedHomology F j (fun c hc => hL c hc j hj)) hP h₀ n hn

section OrdinaryBalanced

open MulOpposite

variable {k M : Type u} [CommRing k] [Algebra k A] [Algebra k B]
    [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [Module k M] [SMulCommClass A Bᵐᵒᵖ M]
    [IsScalarTower k A M]

/-- The (6.21) vanishing test for the actual derived tensor functor, using
injectivity of the ordinary balanced map on the filtered kernel. -/
theorem isZero_derivedTensorHomology_quotient_of_filtered_kernel {ι : Type*}
    (S : ShortComplex (ModuleCat.{u} B)) (hS : S.ShortExact)
    [Module k S.X₁] [IsScalarTower k B S.X₁] [Module k S.X₂] [IsScalarTower k B S.X₂]
    {L : ι → ModuleCat.{u} B} {m : List ι}
    (hK : ModuleFiltration.HasFiltration L m S.X₁)
    (hL : ∀ c ∈ m, ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor ℤ n).obj
      ((derivedTensor A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj (L c))))))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor ℤ n).obj
      ((derivedTensor A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj S.X₂)))))
    (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m)
    (μ : BalancedTensor k A B M S.X₁ →+ BalancedTensor k A B M S.X₂)
    (hμ : ∀ (x : M) (n : S.X₁), μ (BalancedTensor.tmul x n) = BalancedTensor.tmul x (S.f n))
    (hinj : Function.Injective μ)
    (n : ℤ) (hn : n ≠ 0) : IsZero ((homologyFunctor ℤ n).obj
      ((derivedTensor A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj S.X₃)))) := by
  apply isZero_derivedHomology_quotient_of_filtered_kernel (derivedTensor A B M) S hS hK hL hP _ n hn
  exact mono_derivedTensorHomology_of_ordinaryBalanced (A := A) hM
    ((degreeZeroModuleFunctor B).map S.f) μ hμ hinj

end OrdinaryBalanced

end Categorification
