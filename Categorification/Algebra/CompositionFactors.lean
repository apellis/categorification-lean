/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Composition factors of modules of finite length

For a ring `R` and a module `M` of finite length, `Module.compositionFactors R M` is the
multiset of isomorphism classes of composition factors of `M`, as a finitely supported function
on the isomorphism classes of simple `R`-modules (`Module.SimpleClass R`). It is well defined by
the Jordan–Hölder theorem (`CompositionSeries.jordan_holder`) and additive in short exact
sequences. These are the classes in the Grothendieck group of finite length modules, used for the
`K₀`-data of a weak `sl₂`-categorification (Chuang–Rouquier, arXiv:math/0407205v2, §5.1.1) on
the module categories of Webster's tensor product algebras (Webster, arXiv:1309.3796v2, §5).

## Main definitions and results

* `Module.SimpleClass R`: isomorphism classes of simple `R`-modules.
* `Module.compositionFactors R M`: the composition factors of `M`, with multiplicity.
* `Module.compositionFactors_eq_of_exact`: additivity in short exact sequences.
* `Module.compositionFactors_of_isSimpleModule`: a simple module is its only composition factor.
* `Module.compositionFactors_congr`, `Module.compositionFactors_eq_of_shortExact`: invariance
  under isomorphism and additivity along short exact sequences in `ModuleCat R`.
-/

universe u v

open CategoryTheory

namespace Module

variable (R : Type u) [Ring R]

/-- Isomorphism of simple modules, as a setoid on the simple objects of `ModuleCat R`. -/
def simpleSetoid : Setoid {S : ModuleCat.{v} R // IsSimpleModule R S} where
  r S T := Nonempty (S.1 ≅ T.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Isomorphism classes of simple `R`-modules. -/
def SimpleClass : Type _ := Quotient (simpleSetoid.{u, v} R)

variable {R}

/-- The class of a simple module. -/
def SimpleClass.mk (S : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    SimpleClass.{u, v} R :=
  Quotient.mk _ ⟨ModuleCat.of R S, ‹_›⟩

lemma SimpleClass.mk_eq_mk {S T : Type v} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup T] [Module R T] [IsSimpleModule R T] (e : S ≃ₗ[R] T) :
    SimpleClass.mk (R := R) S = SimpleClass.mk T :=
  Quotient.sound ⟨e.toModuleIso⟩

lemma SimpleClass.nonempty_linearEquiv {S T : Type v} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] [AddCommGroup T] [Module R T] [IsSimpleModule R T]
    (h : SimpleClass.mk (R := R) S = SimpleClass.mk T) : Nonempty (S ≃ₗ[R] T) := by
  obtain ⟨e⟩ := Quotient.exact h
  exact ⟨e.toLinearEquiv⟩

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The class of the subquotient `y / x` of a covering pair `x ⋖ y` of submodules. -/
noncomputable def stepClass {x y : Submodule R M} (h : x ⋖ y) : SimpleClass.{u, v} R :=
  haveI := (covBy_iff_quot_is_simple h.le).1 h
  SimpleClass.mk (y ⧸ x.comap y.subtype)

lemma stepClass_eq_of_eq {x y x' y' : Submodule R M} (h : x ⋖ y) (h' : x' ⋖ y') (hx : x = x')
    (hy : y = y') : stepClass h = stepClass h' := by
  subst hx hy; rfl

/-- Two covering pairs (possibly in different modules) have the same class if there is a
surjection from the second to the first subquotient with the right kernel. -/
lemma stepClass_eq_of_surjective {N : Type v} [AddCommGroup N] [Module R N]
    {x y : Submodule R M} {x' y' : Submodule R N} (h : x ⋖ y) (h' : x' ⋖ y')
    (φ : y' →ₗ[R] y ⧸ x.comap y.subtype) (hφ : Function.Surjective φ)
    (hker : LinearMap.ker φ = x'.comap y'.subtype) : stepClass h' = stepClass h := by
  have := (covBy_iff_quot_is_simple h.le).1 h
  have := (covBy_iff_quot_is_simple h'.le).1 h'
  exact SimpleClass.mk_eq_mk
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ))

lemma stepClass_eq_of_linearEquiv {N : Type v} [AddCommGroup N] [Module R N]
    {x y : Submodule R M} {x' y' : Submodule R N} (h : x ⋖ y) (h' : x' ⋖ y')
    (e : (y' ⧸ x'.comap y'.subtype) ≃ₗ[R] y ⧸ x.comap y.subtype) :
    stepClass h' = stepClass h := by
  have := (covBy_iff_quot_is_simple h.le).1 h
  have := (covBy_iff_quot_is_simple h'.le).1 h'
  exact SimpleClass.mk_eq_mk e

/-- The composition factors of a composition series, with multiplicity. -/
noncomputable def seriesFactors (s : CompositionSeries (Submodule R M)) :
    SimpleClass.{u, v} R →₀ ℕ :=
  ∑ i : Fin s.length, Finsupp.single (stepClass (s.step i)) 1

/-- **Jordan–Hölder**: two composition series with the same ends have the same factors. -/
lemma seriesFactors_eq (s t : CompositionSeries (Submodule R M)) (hb : s.head = t.head)
    (hl : s.last = t.last) : seriesFactors s = seriesFactors t := by
  obtain ⟨e, he⟩ := s.jordan_holder t hb hl
  unfold seriesFactors
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact stepClass_eq_of_linearEquiv (t.step (e i)) (s.step i)
    (JordanHolderLattice.Iso.linearEquiv (he i))

open Classical in
variable (R M) in
/-- The composition factors of `M`, with multiplicity; zero if `M` is not of finite length. -/
noncomputable def compositionFactors : SimpleClass.{u, v} R →₀ ℕ :=
  if h : IsFiniteLength R M then
    seriesFactors (isFiniteLength_iff_exists_compositionSeries.mp h).choose
  else 0

lemma compositionFactors_eq (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥)
    (h₂ : s.last = ⊤) : compositionFactors R M = seriesFactors s := by
  have h : IsFiniteLength R M := isFiniteLength_iff_exists_compositionSeries.mpr ⟨s, h₁, h₂⟩
  simp only [compositionFactors, h, dite_true]
  have hs := (isFiniteLength_iff_exists_compositionSeries.mp h).choose_spec
  exact seriesFactors_eq _ _ (hs.1.trans h₁.symm) (hs.2.trans h₂.symm)

lemma compositionFactors_of_not (h : ¬ IsFiniteLength R M) : compositionFactors R M = 0 := by
  simp [compositionFactors, h]

lemma compositionFactors_of_subsingleton [Subsingleton M] : compositionFactors R M = 0 := by
  rw [compositionFactors_eq (RelSeries.singleton _ (⊥ : Submodule R M)) rfl
    (Subsingleton.elim _ _)]
  simp [seriesFactors]


/-- A simple module has itself as its only composition factor. -/
lemma compositionFactors_of_isSimpleModule [IsSimpleModule R M] :
    compositionFactors R M = Finsupp.single (SimpleClass.mk (R := R) M) 1 := by
  have hc : (⊥ : Submodule R M) ⋖ ⊤ := bot_covBy_top
  let s : CompositionSeries (Submodule R M) := (RelSeries.singleton _ ⊥).snoc ⊤ hc
  rw [compositionFactors_eq s rfl (by simp [s])]
  have hs : s.length = 1 := rfl
  simp only [seriesFactors]
  rw [Fintype.sum_eq_single ⟨0, by simp [hs]⟩ (fun i hi => (hi (Fin.ext (by omega))).elim)]
  congr 1
  refine (stepClass_eq_of_eq _ hc rfl rfl).trans ?_
  have := (covBy_iff_quot_is_simple hc.le).1 hc
  exact SimpleClass.mk_eq_mk ((Submodule.quotEquivOfEqBot _
    (by rw [Submodule.comap_bot]; exact Submodule.ker_subtype _)).trans
    Submodule.topEquiv)

section Exact

variable {N P : Type v} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]

/-- Pushing a covering pair forward along an injective map preserves its class. -/
lemma stepClass_map {f : N →ₗ[R] M} (hf : Function.Injective f) {x y : Submodule R N}
    (h : x ⋖ y) : stepClass (Submodule.map_covBy_of_injective hf h) = stepClass h := by
  let ψ : y →ₗ[R] y ⧸ x.comap y.subtype := (x.comap y.subtype).mkQ
  let e := Submodule.equivMapOfInjective f hf y
  refine stepClass_eq_of_surjective _ _ (ψ.comp e.symm.toLinearMap)
    ((Submodule.mkQ_surjective _).comp e.symm.surjective) ?_
  ext ⟨w, hw⟩
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  have : e.symm ⟨f v, hw⟩ = ⟨v, hv⟩ := e.symm_apply_eq.mpr (Subtype.ext rfl)
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe, this, ψ,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype]
  exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨v', hv', hvv⟩ => hf hvv ▸ hv'⟩

/-- Pulling a covering pair back along a surjective map preserves its class. -/
lemma stepClass_comap {g : M →ₗ[R] P} (hg : Function.Surjective g) {x y : Submodule R P}
    (h : x ⋖ y) : stepClass (Submodule.comap_covBy_of_surjective hg h) = stepClass h := by
  let ρ : Submodule.comap g y →ₗ[R] y := g.restrict (fun _ hw => hw)
  have hρ : Function.Surjective ρ := by
    rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := hg v
    exact ⟨⟨w, hv⟩, rfl⟩
  refine stepClass_eq_of_surjective _ _ ((x.comap y.subtype).mkQ.comp ρ)
    ((Submodule.mkQ_surjective _).comp hρ) ?_
  ext ⟨w, hw⟩
  simp [ρ, LinearMap.restrict_apply]

/-- **Composition factors are additive in short exact sequences.** -/
theorem compositionFactors_eq_of_exact (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hN : IsFiniteLength R N) (hP : IsFiniteLength R P) :
    compositionFactors R M = compositionFactors R N + compositionFactors R P := by
  obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hP
  obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  let s' : CompositionSeries (Submodule R M) :=
    s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
  let t' : CompositionSeries (Submodule R M) :=
    t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
  have hfg : Submodule.map f ⊤ = Submodule.comap g ⊥ := by
    rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  have hc : t'.last = s'.head := by simpa [s', t', hs₁, ht₂] using hfg
  let r := t'.smash s' hc
  rw [compositionFactors_eq s hs₁ hs₂, compositionFactors_eq t ht₁ ht₂,
    compositionFactors_eq r
      (by simpa [r, t', ht₁, -Submodule.map_bot] using Submodule.map_bot f)
      (by simpa [r, s', hs₂, -Submodule.comap_top] using Submodule.comap_top g)]
  unfold seriesFactors
  erw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine (stepClass_eq_of_eq _ (t'.step i) (RelSeries.smash_castAdd hc i)
      (RelSeries.smash_succ_castAdd hc i)).trans ?_
    exact stepClass_map hf (t.step i)
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine (stepClass_eq_of_eq _ (s'.step i) (RelSeries.smash_natAdd hc i)
      (RelSeries.smash_succ_natAdd hc i)).trans ?_
    exact stepClass_comap hg (s.step i)

/-- Composition factors are invariant under linear isomorphism. -/
lemma compositionFactors_congr (e : N ≃ₗ[R] M) :
    compositionFactors R M = compositionFactors R N := by
  by_cases hN : IsFiniteLength R N
  · rw [compositionFactors_eq_of_exact (P := PUnit.{v + 1}) e.toLinearMap 0 e.injective
      (fun _ => ⟨0, rfl⟩) (fun y => ⟨fun _ => ⟨e.symm y, by simp⟩, fun _ => rfl⟩) hN
      (isFiniteLength_of_exists_compositionSeries
        ⟨RelSeries.singleton _ ⊥, rfl, Subsingleton.elim _ _⟩),
      compositionFactors_of_subsingleton (M := PUnit.{v + 1}), add_zero]
  · rw [compositionFactors_of_not hN,
      compositionFactors_of_not fun h => hN (e.symm.isFiniteLength h)]

end Exact

section ModuleCat

open CategoryTheory

/-- Additivity of composition factors along a short exact sequence in `ModuleCat R`. -/
theorem compositionFactors_eq_of_shortExact {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (h₁ : IsFiniteLength R S.X₁) (h₃ : IsFiniteLength R S.X₃) :
    compositionFactors R S.X₂ = compositionFactors R S.X₁ + compositionFactors R S.X₃ :=
  compositionFactors_eq_of_exact S.f.hom S.g.hom hS.moduleCat_injective_f
    hS.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) h₁ h₃

/-- Composition factors of isomorphic objects of `ModuleCat R` agree. -/
lemma compositionFactors_iso {X Y : ModuleCat.{v} R} (e : X ≅ Y) :
    compositionFactors R X = compositionFactors R Y :=
  (compositionFactors_congr e.toLinearEquiv).symm

end ModuleCat

end Module
