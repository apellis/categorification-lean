/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CompactModules
import Categorification.Algebra.ModuleFiltration
import Categorification.Algebra.IdempotentEquiv
import Categorification.Algebra.DerivedTensorFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# Thick subcategories and filtered modules

Generic inputs for generation statements in derived categories of rings, used for B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, Proposition 5.26 (the
standard modules generate the perfect complexes).

* `ModuleFiltration.hasFiltration_pi`: a finite product of modules has a filtration by its
  factors.
* `ModuleFiltration.HasFiltration.moduleObj_mem`: a thick subcategory of `D(R)` containing the
  subquotients of a finite filtration (in degree `0`) contains the filtered module.
* `moduleObj_regular_mem_of_sum_eq_one`: a thick subcategory containing the projectives `R e`
  for idempotents `e` summing to `1` contains the regular module, since `R` is a retract of
  `⨁ R e`.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

namespace ModuleFiltration

variable {A : Type} [Ring A] {ι : Type} (L : ι → ModuleCat.{0} A)

/-- The functions in `∏ L i` supported on the members of a list. -/
def piSupported (l : List ι) : Submodule A (∀ i, L i) where
  carrier := {f | ∀ i, i ∉ l → f i = 0}
  add_mem' {f g} hf hg i hi := by
    rw [Pi.add_apply, hf i hi, hg i hi, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c f hf i hi := by
    rw [Pi.smul_apply, hf i hi, smul_zero]

theorem mem_piSupported {l : List ι} {f : ∀ i, L i} :
    f ∈ piSupported L l ↔ ∀ i, i ∉ l → f i = 0 := Iff.rfl

theorem hasFiltration_piSupported [DecidableEq ι] (l : List ι) (hl : l.Nodup) :
    HasFiltration L l (ModuleCat.of A (piSupported L l)) := by
  induction l with
  | nil =>
    refine .zero ⟨fun f g => Subtype.ext (funext fun i => ?_)⟩
    rw [f.2 i List.not_mem_nil, g.2 i List.not_mem_nil]
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    have hle : piSupported L l ≤ piSupported L (a :: l) := fun f hf i hi =>
      hf i fun h => hi (List.mem_cons_of_mem a h)
    let g : piSupported L (a :: l) →ₗ[A] L a :=
      LinearMap.proj (R := A) (φ := fun i => L i) a ∘ₗ (piSupported L (a :: l)).subtype
    refine .cons (Submodule.inclusion hle) g l a (Submodule.inclusion_injective hle) ?_ ?_
      (ih (List.nodup_cons.1 hl).2) ⟨LinearEquiv.refl _ _⟩
    · intro y
      constructor
      · intro hy
        refine ⟨⟨y.1, fun i hi => ?_⟩, rfl⟩
        by_cases hia : i = a
        · subst hia
          exact hy
        · exact y.2 i fun h => (List.mem_cons.1 h).elim hia hi
      · rintro ⟨x, rfl⟩
        exact x.2 a ha
    · intro z
      refine ⟨⟨Pi.single (M := fun i => L i) a z, fun i hi => by
        rw [Pi.single_eq_of_ne]
        rintro rfl
        exact hi List.mem_cons_self⟩, ?_⟩
      exact Pi.single_eq_same (M := fun i => L i) a z

/-- **A finite product of modules has a filtration by its factors.** -/
theorem hasFiltration_pi [Fintype ι] [DecidableEq ι] :
    HasFiltration L (Finset.univ : Finset ι).toList (ModuleCat.of A (∀ i, L i)) := by
  have htop : piSupported L (Finset.univ : Finset ι).toList = ⊤ := by
    refine eq_top_iff.2 fun f _ i hi => (hi ?_).elim
    exact Finset.mem_toList.2 (Finset.mem_univ i)
  exact (hasFiltration_piSupported L _ (Finset.nodup_toList _)).of_equiv
    ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)

end ModuleFiltration

variable {R : Type} [Ring R] [HasDerivedCategory.{0, 0} R]

/-- **A thick subcategory containing the subquotients of a finite filtration contains the
filtered module** (all modules in degree `0`). -/
theorem ModuleFiltration.HasFiltration.moduleObj_mem {P : ObjectProperty (DerivedCategory.{0} R)}
    (hP : IsThick P) {ι : Type*} {L : ι → ModuleCat.{0} R} {m : List ι} {Y : ModuleCat.{0} R}
    (h : ModuleFiltration.HasFiltration L m Y) (hL : ∀ c ∈ m, P (moduleObj (L c))) :
    P (moduleObj Y) := by
  induction h with
  | @zero Y hY =>
    refine hP.of_isZero (Q.map_isZero ?_)
    exact (degreeZeroModuleFunctor R).map_isZero (ModuleCat.isZero_of_subsingleton Y)
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have hX := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    have hZc : P (moduleObj Z) :=
      hP.of_iso (Q.mapIso ((degreeZeroModuleFunctor R).mapIso e.toModuleIso))
        (hL c List.mem_cons_self)
    let T := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; exact hfg.apply_apply_eq_zero x)
    have hT : T.ShortExact := by
      have : Mono T.f := (ModuleCat.mono_iff_injective _).2 hf
      have : Epi T.g := (ModuleCat.epi_iff_surjective _).2 hg
      exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg⟩
    obtain ⟨δ, hδ⟩ := exists_distinguished_of_shortExact_module T hT
    exact hP.ext₂ _ hδ hX hZc

/-- **The regular module is generated by the projectives `R e`** for idempotents `e` summing
to `1`: a thick subcategory of `D(R)` containing every `R e` (in degree `0`) contains `R`,
which is a retract of `⨁ R e`. -/
theorem moduleObj_regular_mem_of_sum_eq_one {P : ObjectProperty (DerivedCategory.{0} R)}
    (hP : IsThick P) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → R)
    (he : ∀ i, IsIdempotentElem (e i)) (hsum : ∑ i, e i = 1)
    (h : ∀ i, P (moduleObj (ModuleCat.of R (lIdeal (e i))))) :
    P (moduleObj (ModuleCat.of R R)) := by
  let L : ι → ModuleCat.{0} R := fun i => ModuleCat.of R (lIdeal (e i))
  have hM : P (moduleObj (ModuleCat.of R (∀ i, L i))) :=
    (ModuleFiltration.hasFiltration_pi L).moduleObj_mem hP fun c _ => h c
  let s : R →ₗ[R] (∀ i, L i) :=
    { toFun := fun a i => ⟨a * e i, by
        change a * e i * e i = a * e i
        rw [mul_assoc, (he i).eq]⟩
      map_add' := fun a b => funext fun i => Subtype.ext (add_mul a b (e i))
      map_smul' := fun a b => funext fun i => Subtype.ext (mul_assoc a b (e i)) }
  let r : (∀ i, L i) →ₗ[R] R :=
    ∑ i, (lIdeal (e i)).subtype ∘ₗ LinearMap.proj (R := R) (φ := fun i => L i) i
  have hrs : ∀ a, r (s a) = a := fun a => by
    rw [LinearMap.sum_apply]
    change ∑ i, a * e i = a
    rw [← Finset.mul_sum, hsum, mul_one]
  let Φ := degreeZeroModuleFunctor R ⋙ Q
  refine hP.retract ⟨Φ.map (ModuleCat.ofHom s), Φ.map (ModuleCat.ofHom r), ?_⟩ hM
  rw [← Φ.map_comp]
  have : ModuleCat.ofHom s ≫ ModuleCat.ofHom r = 𝟙 (ModuleCat.of R R) :=
    ModuleCat.hom_ext (LinearMap.ext hrs)
  rw [this, Φ.map_id]
  rfl

end Categorification
