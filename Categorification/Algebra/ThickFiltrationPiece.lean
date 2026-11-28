/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ThickFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# Pieces of filtrations in thick subcategories

Generic inputs for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Proposition 6.20 (mutation of the standard stratification), for modules in
degree `0` of the derived category `D(R)` of a ring.

* `ModuleFiltration.HasFiltration.relabel_of_map_eq`: a filtration whose layers depend only on
  a function of the labels can be relabelled along any list with the same image.
* `moduleObj_mem_of_subsingleton`: a thick subcategory contains every zero module.
* `moduleObj_mem_of_exact₃`, `moduleObj_mem_of_exact₂`: two-out-of-three for a short exact
  sequence.
* `ModuleFiltration.HasFiltration.moduleObj_mem_of_mem_except`: if a thick subcategory contains
  a filtered module and all layers of its filtration but one, it contains that layer.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

namespace ModuleFiltration

universe v

/-- **Relabelling a filtration**: if the layer at a label `c` is `M (v c)` and the labels have
the same image under `v` as a list `m` under `g`, then the module is filtered by `M (g d)` along
`m`. -/
theorem HasFiltration.relabel_of_map_eq {A : Type*} [Ring A] {α ι κ : Type*}
    (M : α → ModuleCat.{v} A)
    {v : ι → α} {g : κ → α} {l : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration (fun c => M (v c)) l Y) {m : List κ} (hlm : l.map v = m.map g) :
    HasFiltration (fun d => M (g d)) m Y := by
  induction h generalizing m with
  | zero hY =>
    obtain rfl : m = [] := List.map_eq_nil_iff.1 hlm.symm
    exact .zero hY
  | cons f g' l c hf hfg hg _ hZ ih =>
    obtain ⟨d, m, rfl⟩ : ∃ d m', m = d :: m' := by
      cases m with
      | nil => simp at hlm
      | cons d m' => exact ⟨d, m', rfl⟩
    simp only [List.map_cons, List.cons.injEq] at hlm
    refine .cons f g' m d hf hfg hg (ih hlm.2) ?_
    rw [← hlm.1]
    exact hZ

end ModuleFiltration

variable {R : Type} [Ring R] [HasDerivedCategory.{0, 0} R]

/-- A thick subcategory contains every zero module (in degree `0`). -/
theorem moduleObj_mem_of_subsingleton {P : ObjectProperty (DerivedCategory.{0} R)}
    (hP : IsThick P) {X : ModuleCat.{0} R} (hX : Subsingleton X) : P (moduleObj X) :=
  hP.of_isZero ((degreeZeroModuleFunctor R ⋙ Q).map_isZero
    ((ModuleCat.isZero_iff_subsingleton).2 hX))

private theorem exists_distinguished_of_exact {K X Z : ModuleCat.{0} R} (i : K →ₗ[R] X)
    (q : X →ₗ[R] Z) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : Function.Exact i q) :
    ∃ T : Triangle (DerivedCategory.{0} R), T ∈ distTriang _ ∧
      T.obj₁ = moduleObj K ∧ T.obj₂ = moduleObj X ∧ T.obj₃ = moduleObj Z := by
  let S := ShortComplex.mk (ModuleCat.ofHom i) (ModuleCat.ofHom q)
    (by ext x; exact hiq.apply_apply_eq_zero x)
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 hi
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hq
    exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hiq⟩
  obtain ⟨δ, hδ⟩ := exists_distinguished_of_shortExact_module S hS
  exact ⟨_, hδ, rfl, rfl, rfl⟩

/-- **The cokernel of a short exact sequence**: a thick subcategory containing the first two
terms of a short exact sequence of modules (in degree `0`) contains the third. -/
theorem moduleObj_mem_of_exact₃ {P : ObjectProperty (DerivedCategory.{0} R)} (hP : IsThick P)
    {K X Z : ModuleCat.{0} R} (i : K →ₗ[R] X) (q : X →ₗ[R] Z) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hiq : Function.Exact i q)
    (hK : P (moduleObj K)) (hX : P (moduleObj X)) : P (moduleObj Z) := by
  obtain ⟨T, hT, h1, h2, h3⟩ := exists_distinguished_of_exact i q hi hq hiq
  have := hP.ext₃ T hT (h1 ▸ hK) (h2 ▸ hX)
  rwa [h3] at this

/-- **The middle of a short exact sequence**: a thick subcategory containing the outer terms of
a short exact sequence of modules (in degree `0`) contains the middle one. -/
theorem moduleObj_mem_of_exact₂ {P : ObjectProperty (DerivedCategory.{0} R)} (hP : IsThick P)
    {K X Z : ModuleCat.{0} R} (i : K →ₗ[R] X) (q : X →ₗ[R] Z) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hiq : Function.Exact i q)
    (hK : P (moduleObj K)) (hZ : P (moduleObj Z)) : P (moduleObj X) := by
  obtain ⟨T, hT, h1, h2, h3⟩ := exists_distinguished_of_exact i q hi hq hiq
  have := hP.ext₂ T hT (h1 ▸ hK) (h3 ▸ hZ)
  rwa [h2] at this

/-- **The missing layer of a filtration**: if a thick subcategory of `D(R)` contains a filtered
module (in degree `0`) and every layer of its filtration except one occurrence of `c`, it
contains the layer at `c`. -/
theorem ModuleFiltration.HasFiltration.moduleObj_mem_of_mem_except
    {P : ObjectProperty (DerivedCategory.{0} R)} (hP : IsThick P) {ι : Type*}
    {L : ι → ModuleCat.{0} R} {m₁ m₂ : List ι} {c : ι} {Y : ModuleCat.{0} R}
    (h : ModuleFiltration.HasFiltration L (m₁ ++ c :: m₂) Y) (hY : P (moduleObj Y))
    (hL : ∀ d ∈ m₁ ++ m₂, P (moduleObj (L d))) : P (moduleObj (L c)) := by
  generalize hm : m₁ ++ c :: m₂ = m at h
  induction h generalizing m₁ with
  | @zero Y hY0 => simp at hm
  | @cons X Y Z f g m c' hf hfg hg hX hZ ih =>
    obtain ⟨e⟩ := hZ
    let T := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; exact hfg.apply_apply_eq_zero x)
    have hT : T.ShortExact := by
      have : Mono T.f := (ModuleCat.mono_iff_injective _).2 hf
      have : Epi T.g := (ModuleCat.epi_iff_surjective _).2 hg
      exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg⟩
    obtain ⟨δ, hδ⟩ := exists_distinguished_of_shortExact_module T hT
    have hZL : ∀ {Z' : ModuleCat.{0} R} (e' : Z' ≃ₗ[R] L c'),
        (P (moduleObj Z') ↔ P (moduleObj (L c'))) := fun e' =>
      ⟨fun hz => hP.of_iso (Q.mapIso ((degreeZeroModuleFunctor R).mapIso e'.symm.toModuleIso)) hz,
        fun hz => hP.of_iso (Q.mapIso ((degreeZeroModuleFunctor R).mapIso e'.toModuleIso)) hz⟩
    cases m₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have hXP : P (moduleObj X) := hX.moduleObj_mem hP fun d hd => hL d (by simpa using hd)
      exact (hZL e).1 (hP.ext₃ _ hδ hXP hY)
    | cons d m₁ =>
      simp only [List.cons_append, List.cons.injEq] at hm
      obtain ⟨rfl, hm⟩ := hm
      have hZP : P (moduleObj Z) := (hZL e).2 (hL _ List.mem_cons_self)
      have hXP : P (moduleObj X) := hP.ext₁ _ hδ hY hZP
      exact ih hXP (fun d' hd' => hL d' (List.mem_cons_of_mem _ hd')) hm

end Categorification
