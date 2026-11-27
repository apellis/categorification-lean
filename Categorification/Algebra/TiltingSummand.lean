/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExtShortExact
import Categorification.Algebra.LocalizingFiltration
import Categorification.Algebra.FittingSummand

set_option backward.isDefEq.respectTransparency false

/-!
# Ringel's comparison of tilting modules

Ringel's argument, used in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 6.14 (second clause), for modules over a ring `R` with a
family of "standard" modules `L c`, placed in degree `0` of `D(R)`, where
`Ext¹(X, Y) = Hom(X, Y⟦1⟧)`:

* `Ext¹` vanishes on filtered modules once it vanishes on their subquotients
  (`HasFiltration.hom_shift_one_eq_zero_left`, `HasFiltration.hom_shift_one_eq_zero_right`), and
  so does `Hom` (`HasFiltration.linearMap_eq_zero`);
* a standard `L s` with `Ext¹(L s, L a) = 0` for the other labels `a` of a filtration can be
  moved to its bottom (`HasFiltration.exists_bottom`);
* if `L s` sits at the bottom of the filtrations of `T` and `B`, each of which has no `Ext¹`
  from the subquotients of the other, and `T` is indecomposable of finite length, then `T` is a
  direct summand of `B` (`exists_leftInverse_of_bottom`).
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  ModuleFiltration
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [HasDerivedCategory.{0, 0} R]

theorem isZero_moduleObj_of_subsingleton {X : ModuleCat.{0} R} (hX : Subsingleton X) :
    IsZero (moduleObj X) :=
  (degreeZeroModuleFunctor R ⋙ Q).map_isZero ((ModuleCat.isZero_iff_subsingleton).2 hX)

/-- Isomorphic modules have the same `Ext¹` into a fixed object. -/
theorem hom_shift_one_eq_zero_of_equiv_left {X X' : ModuleCat.{0} R} (e : X ≃ₗ[R] X')
    {W : DerivedCategory.{0} R} (h : ∀ f : moduleObj X' ⟶ W⟦(1 : ℤ)⟧, f = 0)
    (f : moduleObj X ⟶ W⟦(1 : ℤ)⟧) : f = 0 := by
  let i := Q.mapIso ((degreeZeroModuleFunctor R).mapIso e.toModuleIso)
  have : f = i.hom ≫ i.inv ≫ f := by simp
  rw [this, h (i.inv ≫ f), comp_zero]

/-- Isomorphic modules have the same `Ext¹` from a fixed object. -/
theorem hom_shift_one_eq_zero_of_equiv_right {Y Y' : ModuleCat.{0} R} (e : Y ≃ₗ[R] Y')
    {W : DerivedCategory.{0} R} (h : ∀ f : W ⟶ (moduleObj Y')⟦(1 : ℤ)⟧, f = 0)
    (f : W ⟶ (moduleObj Y)⟦(1 : ℤ)⟧) : f = 0 := by
  let i := (shiftFunctor (DerivedCategory.{0} R) (1 : ℤ)).mapIso
    (Q.mapIso ((degreeZeroModuleFunctor R).mapIso e.toModuleIso))
  have : f = (f ≫ i.hom) ≫ i.inv := by simp
  rw [this, h (f ≫ i.hom), zero_comp]

namespace ModuleFiltration

variable {ι : Type*} {L : ι → ModuleCat.{0} R}

omit [HasDerivedCategory.{0, 0} R] in
/-- `Hom` vanishes from a filtered module once it vanishes from its subquotients. -/
theorem HasFiltration.linearMap_eq_zero {m : List ι} {X : ModuleCat.{0} R}
    (h : HasFiltration L m X) {W : Type} [AddCommGroup W] [Module R W]
    (hL : ∀ c ∈ m, ∀ φ : L c →ₗ[R] W, φ = 0) (φ : X →ₗ[R] W) : φ = 0 := by
  induction h with
  | zero hX =>
    refine LinearMap.ext fun x => ?_
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  | cons f g m c hf hfg hg hX hZ ih =>
    have h0 : φ ∘ₗ f = 0 := ih (fun d hd => hL d (List.mem_cons_of_mem _ hd)) _
    obtain ⟨e⟩ := hZ
    have hle : LinearMap.range f ≤ LinearMap.ker φ := by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun h0 x
    let ψ : _ →ₗ[R] W := (LinearMap.range f).liftQ φ hle ∘ₗ
      (hfg.linearEquivOfSurjective hg).symm.toLinearMap
    have hψ : ψ = 0 := by
      have := hL c List.mem_cons_self (ψ ∘ₗ e.symm.toLinearMap)
      refine LinearMap.ext fun z => ?_
      simpa using LinearMap.congr_fun this (e z)
    refine LinearMap.ext fun y => ?_
    have : ψ (g y) = φ y := by
      simp only [ψ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Function.Exact.linearEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    rw [← this, hψ, LinearMap.zero_apply, LinearMap.zero_apply]

/-- `Ext¹` vanishes from a filtered module once it vanishes from its subquotients. -/
theorem HasFiltration.hom_shift_one_eq_zero_left {m : List ι} {X : ModuleCat.{0} R}
    (h : HasFiltration L m X) {W : DerivedCategory.{0} R}
    (hL : ∀ c ∈ m, ∀ f : moduleObj (L c) ⟶ W⟦(1 : ℤ)⟧, f = 0)
    (f : moduleObj X ⟶ W⟦(1 : ℤ)⟧) : f = 0 := by
  induction h with
  | zero hX => exact (isZero_moduleObj_of_subsingleton hX).eq_of_src _ _
  | cons f₀ g m c hf hfg hg hX hZ ih =>
    obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact_module _
      (shortExact_of_linear f₀ g hf hfg hg)
    obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ hT f
      (ih (fun d hd => hL d (List.mem_cons_of_mem _ hd)) _)
    rw [hu, hom_shift_one_eq_zero_of_equiv_left hZ.some (hL c List.mem_cons_self) u, comp_zero]

/-- `Ext¹` vanishes into a filtered module once it vanishes into its subquotients. -/
theorem HasFiltration.hom_shift_one_eq_zero_right {m : List ι} {Y : ModuleCat.{0} R}
    (h : HasFiltration L m Y) {W : DerivedCategory.{0} R}
    (hL : ∀ c ∈ m, ∀ f : W ⟶ (moduleObj (L c))⟦(1 : ℤ)⟧, f = 0)
    (f : W ⟶ (moduleObj Y)⟦(1 : ℤ)⟧) : f = 0 := by
  induction h with
  | zero hX => exact ((shiftFunctor _ (1 : ℤ)).map_isZero
      (isZero_moduleObj_of_subsingleton hX)).eq_of_tgt _ _
  | cons f₀ g m c hf hfg hg hX hZ ih =>
    obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact_module _
      (shortExact_of_linear f₀ g hf hfg hg)
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ (Triangle.shift_distinguished _ hT 1) f
      (hom_shift_one_eq_zero_of_equiv_right hZ.some (hL c List.mem_cons_self) _)
    rw [hu, ih (fun d hd => hL d (List.mem_cons_of_mem _ hd)) u, zero_comp]

end ModuleFiltration

/-- **A short exact sequence with `Ext¹(Z, X) = 0` splits**: `X → Y` has a retraction. -/
theorem exists_retraction_of_hom_shift_one_eq_zero {X Y Z : ModuleCat.{0} R} (f : X →ₗ[R] Y)
    (g : Y →ₗ[R] Z) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (h : ∀ u : moduleObj Z ⟶ (moduleObj X)⟦(1 : ℤ)⟧, u = 0) :
    ∃ r : Y →ₗ[R] X, r ∘ₗ f = LinearMap.id := by
  obtain ⟨r, hr⟩ := exists_comp_eq_of_shortExact (shortExact_of_linear f g hf hfg hg) X h (𝟙 X)
  exact ⟨r.hom, LinearMap.ext fun x => congrArg (fun φ => ModuleCat.Hom.hom φ x) hr⟩

namespace ModuleFiltration

variable {ι : Type*} {L : ι → ModuleCat.{0} R}

/-- **Moving a standard to the bottom of a filtration**: if `Ext¹(L s, L a) = 0` for every label
`a` of a filtration of `Y` and `s` is one of them, then `L s` embeds in `Y` with cokernel
filtered by the remaining labels. -/
theorem HasFiltration.exists_bottom [DecidableEq ι] {m : List ι} {Y : ModuleCat.{0} R}
    (h : HasFiltration L m Y) {s : ι} (hs : s ∈ m)
    (hext : ∀ a ∈ m, ∀ u : moduleObj (L s) ⟶ (moduleObj (L a))⟦(1 : ℤ)⟧, u = 0) :
    ∃ (Y' : ModuleCat.{0} R) (i : L s →ₗ[R] Y) (p : Y →ₗ[R] Y'), Function.Injective i ∧
      Function.Exact i p ∧ Function.Surjective p ∧ HasFiltration L (m.erase s) Y' := by
  induction h with
  | zero _ => simp at hs
  | @cons X Y Z f g m c hf hfg hg hX hZ ih =>
    by_cases hcs : c = s
    · subst hcs
      obtain ⟨e⟩ := hZ
      have hXext : ∀ u : moduleObj Z ⟶ (moduleObj X)⟦(1 : ℤ)⟧, u = 0 := fun u =>
        hom_shift_one_eq_zero_of_equiv_left e (fun u' => hX.hom_shift_one_eq_zero_right
          (fun a ha => hext a (List.mem_cons_of_mem _ ha)) u') u
      obtain ⟨r, hr⟩ := exists_retraction_of_hom_shift_one_eq_zero f g hf hfg hg hXext
      have hrf : ∀ x, r (f x) = x := fun x => LinearMap.congr_fun hr x
      let ψ : Y →ₗ[R] Y := LinearMap.id - f ∘ₗ r
      have hle : LinearMap.range f ≤ LinearMap.ker ψ := by
        rintro _ ⟨x, rfl⟩
        simp [ψ, hrf]
      let σ : Z →ₗ[R] Y := (LinearMap.range f).liftQ ψ hle ∘ₗ
        (hfg.linearEquivOfSurjective hg).symm.toLinearMap
      have hσ : ∀ y, σ (g y) = y - f (r y) := fun y => by
        simp [σ, ψ, Function.Exact.linearEquivOfSurjective_symm_apply]
      have hgσ : ∀ z, g (σ z) = z := fun z => by
        obtain ⟨y, rfl⟩ := hg z
        rw [hσ, map_sub, hfg.apply_apply_eq_zero, sub_zero]
      have hrσ : ∀ z, r (σ z) = 0 := fun z => by
        obtain ⟨y, rfl⟩ := hg z
        rw [hσ, map_sub, hrf, sub_self]
      refine ⟨X, σ ∘ₗ e.symm.toLinearMap, r, fun a b hab => ?_, fun y => ?_,
        fun x => ⟨f x, hrf x⟩, by rwa [List.erase_cons_head]⟩
      · have := congrArg (fun y => e (g y)) hab
        simpa [hgσ] using this
      · constructor
        · intro hy
          refine ⟨e (g y), ?_⟩
          simp [hσ, hy]
        · rintro ⟨z, rfl⟩
          exact hrσ _
    · have hsm : s ∈ m := (List.mem_cons.1 hs).resolve_left (Ne.symm hcs)
      obtain ⟨X', i, p, hi, hip, hp, hX'⟩ :=
        ih hsm (fun a ha => hext a (List.mem_cons_of_mem _ ha))
      let N := LinearMap.range (f ∘ₗ i)
      have hNf : LinearMap.range i ≤ (LinearMap.range (f ∘ₗ i)).comap f := by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      have hNg : N ≤ LinearMap.ker g := by
        rintro _ ⟨x, rfl⟩
        exact hfg.apply_apply_eq_zero (i x)
      let fb : ModuleCat.of R (X ⧸ LinearMap.range i) →ₗ[R] ModuleCat.of R (Y ⧸ N) :=
        (LinearMap.range i).mapQ N f hNf
      let gb : ModuleCat.of R (Y ⧸ N) →ₗ[R] Z := N.liftQ g hNg
      refine ⟨ModuleCat.of R (Y ⧸ N), f ∘ₗ i, N.mkQ, hf.comp hi, fun y => ?_,
        N.mkQ_surjective, ?_⟩
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        rfl
      · rw [List.erase_cons_tail (by simpa using hcs)]
        refine HasFiltration.cons fb gb _ c ?_ ?_ ?_
          (hX'.of_equiv (hip.linearEquivOfSurjective hp).symm) hZ
        · refine (injective_iff_map_eq_zero fb).2 fun a ha => ?_
          obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
          change N.mkQ (f x) = 0 at ha
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
          obtain ⟨x', hx'⟩ := ha
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨x', hf hx'⟩
        · intro a
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
          change g y = 0 ↔ _
          rw [hfg y]
          constructor
          · rintro ⟨x, rfl⟩
            exact ⟨Submodule.Quotient.mk x, rfl⟩
          · rintro ⟨b, hb⟩
            obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ b
            change N.mkQ (f x) = N.mkQ y at hb
            rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hb
            obtain ⟨x', hx'⟩ := hb
            refine ⟨x - i x', ?_⟩
            rw [map_sub]
            change f x - f (i x') = y
            rw [show f (i x') = f x - y from hx']
            abel
        · intro z
          obtain ⟨y, rfl⟩ := hg z
          exact ⟨N.mkQ y, rfl⟩

end ModuleFiltration

/-- **Ringel's comparison of tilting modules**: suppose `L s` is nonzero and embeds at the bottom
of filtrations of `T` and of `B`, such that `Ext¹` vanishes from the remaining subquotients of
each into the other module. If `T` is indecomposable of finite length, then `T` is a direct
summand of `B`. -/
theorem exists_leftInverse_of_bottom {ι : Type*} {L : ι → ModuleCat.{0} R} {s : ι}
    (hs : Nontrivial (L s)) {T T' B B' : ModuleCat.{0} R} [IsArtinian R T] [IsNoetherian R T]
    (hT : IsIndecomposableModule R T)
    (iT : L s →ₗ[R] T) (pT : T →ₗ[R] T') (hiT : Function.Injective iT)
    (hipT : Function.Exact iT pT) (hpT : Function.Surjective pT) {mT : List ι}
    (hT' : HasFiltration L mT T')
    (iB : L s →ₗ[R] B) (pB : B →ₗ[R] B') (hiB : Function.Injective iB)
    (hipB : Function.Exact iB pB) (hpB : Function.Surjective pB) {mB : List ι}
    (hB' : HasFiltration L mB B')
    (hTB : ∀ a ∈ mT, ∀ u : moduleObj (L a) ⟶ (moduleObj B)⟦(1 : ℤ)⟧, u = 0)
    (hBT : ∀ a ∈ mB, ∀ u : moduleObj (L a) ⟶ (moduleObj T)⟦(1 : ℤ)⟧, u = 0) :
    ∃ (i : T →ₗ[R] B) (p : B →ₗ[R] T), p ∘ₗ i = LinearMap.id := by
  obtain ⟨F, hF⟩ := exists_comp_eq_of_shortExact (shortExact_of_linear iT pT hiT hipT hpT) B
    (fun u => hT'.hom_shift_one_eq_zero_left hTB u) (ModuleCat.ofHom iB)
  obtain ⟨G, hG⟩ := exists_comp_eq_of_shortExact (shortExact_of_linear iB pB hiB hipB hpB) T
    (fun u => hB'.hom_shift_one_eq_zero_left hBT u) (ModuleCat.ofHom iT)
  have hF' : ∀ x, F.hom (iT x) = iB x := fun x => congrArg (fun φ => ModuleCat.Hom.hom φ x) hF
  have hG' : ∀ x, G.hom (iB x) = iT x := fun x => congrArg (fun φ => ModuleCat.Hom.hom φ x) hG
  refine ⟨F.hom, ?_⟩
  refine hT.exists_leftInverse_of_not_isNilpotent F.hom G.hom fun ⟨n, hn⟩ => ?_
  have hfix : ∀ k : ℕ, ∀ x, ((G.hom ∘ₗ F.hom) ^ k) (iT x) = iT x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, LinearMap.comp_apply, hF', hG', ih]
  obtain ⟨x, hx⟩ := exists_ne (0 : L s)
  apply hx
  apply hiT
  rw [← hfix n x, hn, LinearMap.zero_apply, map_zero]

end Categorification
