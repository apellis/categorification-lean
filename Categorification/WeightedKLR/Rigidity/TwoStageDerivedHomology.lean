/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.WeightedKLR.Rigidity.FundamentalDerivedCircle

/-! # A two-step resolution with a single surviving derived homology module -/
noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
namespace Categorification
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [HasZeroObject C] [Pretriangulated C]

/-- Comparison for a two-step resolution whose image is exact at both ends.
The negative Hom vanishing ensures that the two comparisons induce the same
map from the first cone to the degree-zero term. -/
private def twoStageTriangleIso {X₂ X₁ K X₀ L Y₂ Y₁ N Y₀ H : C}
    {f : X₂ ⟶ X₁} {q : X₁ ⟶ K} {u : K ⟶ X₂⟦(1 : ℤ)⟧}
    {i : K ⟶ X₀} {p : X₀ ⟶ L} {v : L ⟶ K⟦(1 : ℤ)⟧}
    {f' : Y₂ ⟶ Y₁} {q' : Y₁ ⟶ N} {u' : N ⟶ Y₂⟦(1 : ℤ)⟧}
    {s : H ⟶ N} {t : N ⟶ Y₀} {w : Y₀ ⟶ H⟦(1 : ℤ)⟧}
    (h₁ : Triangle.mk f q u ∈ distTriang C) (h₂ : Triangle.mk i p v ∈ distTriang C)
    (k₁ : Triangle.mk f' q' u' ∈ distTriang C) (k₂ : Triangle.mk s t w ∈ distTriang C)
    (e₂ : X₂ ≅ Y₂) (e₁ : X₁ ≅ Y₁) (e₀ : X₀ ≅ Y₀)
    (hf : f ≫ e₁.hom = e₂.hom ≫ f')
    (hg : q ≫ i ≫ e₀.hom = e₁.hom ≫ q' ≫ t)
    (hvan : ∀ z : X₂⟦(1 : ℤ)⟧ ⟶ Y₀, z = 0) : L ≅ H⟦(1 : ℤ)⟧ := by
  let T := Triangle.mk f q u
  let T' := Triangle.mk f' q' u'
  let E := isoTriangleOfIso₁₂ T T' h₁ k₁ e₂ e₁ hf
  let eK : K ≅ N := Triangle.π₃.mapIso E
  have hq : q ≫ eK.hom = e₁.hom ≫ q' := by
    change T.mor₂ ≫ E.hom.hom₃ = e₁.hom ≫ T'.mor₂
    rw [E.hom.comm₂]
    rfl
  have hzero : q ≫ (i ≫ e₀.hom - eK.hom ≫ t) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc q eK.hom, hq, Category.assoc, hg, sub_self]
  have hi : i ≫ e₀.hom = eK.hom ≫ t := by
    obtain ⟨z,hz⟩ := T.yoneda_exact₃ h₁ _ hzero
    apply sub_eq_zero.mp
    rw [hz,hvan z,comp_zero]
  exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ (Triangle.mk i p v)
    (Triangle.mk s t w).rotate h₂ (rot_of_distTriang _ k₂) eK e₀ hi)

open DG
open scoped DG.DegreeZero

/-- Put an ordinary module in the derived category in degree zero. -/
abbrev degreeZeroDerivedFunctor (R : Type) [Ring R] [DG.HasDerivedCategory.{v,0} R] :=
  degreeZeroModuleFunctor R ⋙ DG.DerivedCategory.Q

private theorem included_triangle {R : Type} [Ring R] [DG.HasDerivedCategory.{v,0} R]
    {X Y Z : ModuleCat.{0} R} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    (hs : (ShortComplex.mk f g h).ShortExact) :
    ∃ δ, Triangle.mk ((degreeZeroDerivedFunctor R).map f) ((degreeZeroDerivedFunctor R).map g) δ ∈ distTriang _ :=
  DG.DerivedCategory.exists_distinguished_of_shortExact ((ShortComplex.mk f g h).map _)
    (degreeZeroModuleFunctor_shortExact _ hs)

private theorem cokernelStep {R : Type} [Ring R] (T : ShortComplex (ModuleCat.{0} R))
    (hf : Mono T.f) : (ShortComplex.mk T.f T.pOpcycles T.f_pOpcycles).ShortExact := by
  let S := ShortComplex.mk T.f T.pOpcycles T.f_pOpcycles
  let : Mono S.f := hf
  let : Epi S.g := inferInstanceAs (Epi T.pOpcycles)
  exact ⟨S.exact_of_g_is_cokernel T.opcyclesIsCokernel⟩

private theorem homologyStep {R : Type} [Ring R] (T : ShortComplex (ModuleCat.{0} R))
    (hg : Epi T.g) : (ShortComplex.mk T.homologyι T.fromOpcycles T.homologyι_comp_fromOpcycles).ShortExact := by
  let S := ShortComplex.mk T.homologyι T.fromOpcycles T.homologyι_comp_fromOpcycles
  let : Mono S.f := inferInstanceAs (Mono T.homologyι)
  let : Epi S.g := epi_of_epi_fac T.p_fromOpcycles
  exact ⟨S.exact_of_f_is_kernel T.homologyIsKernel⟩

/-- A triangulated functor on a length-two module resolution computes the
degree-one homology of the corresponding complex whenever its end maps are
injective and surjective. The two naturality squares retain the actual differentials. -/
theorem nonempty_shiftedHomologyIso_of_resolution {A B : Type} [Ring A] [Ring B]
    [DG.HasDerivedCategory.{v,0} A] [DG.HasDerivedCategory.{v,0} B]
    (F : DG.DerivedCategory.{v,0} B ⥤ DG.DerivedCategory.{v,0} A) [F.CommShift ℤ] [F.IsTriangulated]
    {P₂ P₁ J P₀ L : ModuleCat.{0} B} (f : P₂ ⟶ P₁) (q : P₁ ⟶ J) (i : J ⟶ P₀) (p : P₀ ⟶ L)
    (h₁ : f ≫ q = 0) (h₂ : i ≫ p = 0)
    (s₁ : (ShortComplex.mk f q h₁).ShortExact) (s₂ : (ShortComplex.mk i p h₂).ShortExact)
    (T : ShortComplex (ModuleCat.{0} A)) (ht₁ : Mono T.f) (ht₂ : Epi T.g)
    (e₂ : F.obj ((degreeZeroDerivedFunctor B).obj P₂) ≅ (degreeZeroDerivedFunctor A).obj T.X₁)
    (e₁ : F.obj ((degreeZeroDerivedFunctor B).obj P₁) ≅ (degreeZeroDerivedFunctor A).obj T.X₂)
    (e₀ : F.obj ((degreeZeroDerivedFunctor B).obj P₀) ≅ (degreeZeroDerivedFunctor A).obj T.X₃)
    (hf : F.map ((degreeZeroDerivedFunctor B).map f) ≫ e₁.hom = e₂.hom ≫ (degreeZeroDerivedFunctor A).map T.f)
    (hg : F.map ((degreeZeroDerivedFunctor B).map (q ≫ i)) ≫ e₀.hom = e₁.hom ≫ (degreeZeroDerivedFunctor A).map T.g) :
    Nonempty (F.obj ((degreeZeroDerivedFunctor B).obj L) ≅ ((degreeZeroDerivedFunctor A).obj T.homology)⟦(1 : ℤ)⟧) := by
  obtain ⟨u,hu⟩ := included_triangle f q h₁ s₁
  obtain ⟨v,hv⟩ := included_triangle i p h₂ s₂
  obtain ⟨u',hu'⟩ := included_triangle T.f T.pOpcycles T.f_pOpcycles (cokernelStep T ht₁)
  obtain ⟨v',hv'⟩ := included_triangle T.homologyι T.fromOpcycles T.homologyι_comp_fromOpcycles (homologyStep T ht₂)
  refine ⟨twoStageTriangleIso (F.map_distinguished _ hu) (F.map_distinguished _ hv) hu' hv' e₂ e₁ e₀ hf ?_ ?_⟩
  · change F.map ((degreeZeroDerivedFunctor B).map q) ≫ F.map ((degreeZeroDerivedFunctor B).map i) ≫ e₀.hom =
      e₁.hom ≫ (degreeZeroDerivedFunctor A).map T.pOpcycles ≫ (degreeZeroDerivedFunctor A).map T.fromOpcycles
    rw [← Category.assoc,← F.map_comp,← Functor.map_comp,← Functor.map_comp,T.p_fromOpcycles,hg]
  · let := _root_.HasDerivedCategory.standard (ModuleCat.{0} A)
    intro z
    let E := (shiftFunctor _ (1 : ℤ)).mapIso e₂
    have hz := Stendhal.FundamentalCorner.degreeZero_shift_one_hom_eq_zero A T.X₁ T.X₃ (E.inv ≫ z)
    rw [← cancel_epi E.inv,comp_zero]
    exact hz


/-- The two-stage comparison using the ordinary elementwise exactness of a
module resolution. The factor between its short exact sequences is the image
of the second differential. -/
theorem nonempty_shiftedHomologyIso_of_exactResolution {A B : Type} [Ring A] [Ring B]
    [DG.HasDerivedCategory.{v,0} A] [DG.HasDerivedCategory.{v,0} B]
    (F : DG.DerivedCategory.{v,0} B ⥤ DG.DerivedCategory.{v,0} A) [F.CommShift ℤ] [F.IsTriangulated]
    {P₂ P₁ P₀ L : ModuleCat.{0} B} (f : P₂ ⟶ P₁) (g : P₁ ⟶ P₀) (p : P₀ ⟶ L)
    (hi : Function.Injective f) (he : Function.Exact f g) (he' : Function.Exact g p)
    (hs : Function.Surjective p) (T : ShortComplex (ModuleCat.{0} A)) (ht₁ : Mono T.f) (ht₂ : Epi T.g)
    (e₂ : F.obj ((degreeZeroDerivedFunctor B).obj P₂) ≅ (degreeZeroDerivedFunctor A).obj T.X₁)
    (e₁ : F.obj ((degreeZeroDerivedFunctor B).obj P₁) ≅ (degreeZeroDerivedFunctor A).obj T.X₂)
    (e₀ : F.obj ((degreeZeroDerivedFunctor B).obj P₀) ≅ (degreeZeroDerivedFunctor A).obj T.X₃)
    (hf : F.map ((degreeZeroDerivedFunctor B).map f) ≫ e₁.hom = e₂.hom ≫ (degreeZeroDerivedFunctor A).map T.f)
    (hg : F.map ((degreeZeroDerivedFunctor B).map g) ≫ e₀.hom = e₁.hom ≫ (degreeZeroDerivedFunctor A).map T.g) :
    Nonempty (F.obj ((degreeZeroDerivedFunctor B).obj L) ≅ ((degreeZeroDerivedFunctor A).obj T.homology)⟦(1 : ℤ)⟧) := by
  let J := ModuleCat.of B (LinearMap.range g.hom)
  let q : P₁ ⟶ J := ModuleCat.ofHom g.hom.rangeRestrict
  let i : J ⟶ P₀ := ModuleCat.ofHom g.hom.range.subtype
  have hq : f ≫ q = 0 := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (he.apply_apply_eq_zero x))
  have hp : i ≫ p = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x,y,rfl⟩
    exact he'.apply_apply_eq_zero y
  let S₁ := ShortComplex.mk f q hq
  let S₂ := ShortComplex.mk i p hp
  let : Mono S₁.f := (ModuleCat.mono_iff_injective f).mpr hi
  let : Epi S₁.g := (ModuleCat.epi_iff_surjective q).mpr g.hom.surjective_rangeRestrict
  let : Mono S₂.f := (ModuleCat.mono_iff_injective i).mpr Subtype.val_injective
  let : Epi S₂.g := (ModuleCat.epi_iff_surjective p).mpr hs
  have s₁ : S₁.ShortExact := by
    refine ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr ?_⟩
    intro x
    exact (Subtype.ext_iff).trans (he x)
  have s₂ : S₂.ShortExact := by
    refine ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr ?_⟩
    intro x
    apply (he' x).trans
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨⟨g y, y,rfl⟩,rfl⟩
    · rintro ⟨⟨y,hy⟩,rfl⟩
      exact hy
  exact nonempty_shiftedHomologyIso_of_resolution F f q i p hq hp s₁ s₂ T ht₁ ht₂ e₂ e₁ e₀ hf hg

end Categorification
