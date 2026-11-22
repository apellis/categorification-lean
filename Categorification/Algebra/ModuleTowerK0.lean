/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CompositionFactors
import Categorification.Algebra.ModuleTower
import Categorification.Sl2Categorification.K0Exact
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Preadditive.Schur

/-!
# Grothendieck data for finitely generated modules over a tower of rings

For a tower of left noetherian and artinian rings `A 0, A 1, …` that vanishes from some level
on, the abelian category `FGTower A` of families of finitely generated modules has the
Grothendieck-group data `K0Data` used by Chuang–Rouquier's weak `𝔰𝔩₂`-categorifications
(arXiv:math/0407205v2, §5.1.1).

* A simple object of `FGTower A` is concentrated in one level, where it is a simple module
  (`ModuleTower.isSimpleModule_level`); conversely, a simple module placed at one level is a
  simple object (`ModuleTower.simple_singleFG`).
* `ModuleTower.k0Data`: the class of a family is the sum over the levels of the composition
  factors of its modules, in the `ℚ`-vector space with basis the pairs (level, isomorphism class
  of a simple module at that level).

This is the Grothendieck group of the category of finitely generated modules along an
`i`-string of Webster's tensor product algebras (arXiv:1309.3796v2, §5), on which `Eᵢ` and `Fᵢ`
act.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.ModuleTower

open CategoryTheory Limits

universe u

variable {A : ℕ → Type u} [∀ m, Ring (A m)]

section Pi

/-- The morphism of families that is `φ` at level `m` and zero at the other levels. -/
def levelHom {X Y : ∀ n, ModuleCat.{u} (A n)} (m : ℕ) (φ : X m ⟶ Y m) : X ⟶ Y :=
  fun n => if h : n = m then by subst h; exact φ else 0

lemma levelHom_self {X Y : ∀ n, ModuleCat.{u} (A n)} (m : ℕ) (φ : X m ⟶ Y m) :
    levelHom m φ m = φ := by
  simp [levelHom]

lemma levelHom_ne {X Y : ∀ n, ModuleCat.{u} (A n)} {m n : ℕ} (φ : X m ⟶ Y m) (h : n ≠ m) :
    levelHom m φ n = 0 := by
  simp [levelHom, h]

/-- The family with the module `M` at level `m` and zero at the other levels. -/
def singleObj (m : ℕ) (M : ModuleCat.{u} (A m)) : ∀ n, ModuleCat.{u} (A n) :=
  fun n => if h : n = m then by subst h; exact M else ModuleCat.of (A n) PUnit

lemma singleObj_self (m : ℕ) (M : ModuleCat.{u} (A m)) : singleObj m M m = M := by
  simp [singleObj]

lemma isZero_singleObj {m n : ℕ} (M : ModuleCat.{u} (A m)) (h : n ≠ m) :
    IsZero (singleObj m M n) := by
  simp only [singleObj, h, ↓reduceDIte]
  exact ModuleCat.isZero_of_subsingleton _

lemma mono_pi {X Y : ∀ n, ModuleCat.{u} (A n)} (f : X ⟶ Y) (hf : ∀ n, Mono (f n)) : Mono f :=
  ⟨fun a b h => funext fun n => by
    have h' : a n ≫ f n = b n ≫ f n := congrFun h n
    exact (cancel_mono (f n)).mp h'⟩

end Pi

lemma mono_of_isZero {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    Mono f :=
  ⟨fun a b _ => hX.eq_of_tgt a b⟩

lemma isIso_of_isZero {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (hX : IsZero X)
    (hY : IsZero Y) : IsIso f :=
  ⟨⟨hY.to_ X, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

lemma module_finite_of_isSimpleModule (R : Type u) [Ring R] (M : Type u) [AddCommGroup M]
    [Module R M] [IsSimpleModule R M] : Module.Finite R M := by
  have : Nontrivial M := IsSimpleModule.nontrivial R M
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact ⟨⟨{x}, by rw [Finset.coe_singleton]; exact IsSimpleModule.span_singleton_eq_top R hx⟩⟩


variable [∀ m, IsNoetherianRing (A m)]

namespace FGTower

variable {X Y : FGTower A}

omit [∀ m, IsNoetherianRing (A m)] in
lemma towerFinite_singleObj (m : ℕ) (M : ModuleCat.{u} (A m)) [Module.Finite (A m) M] :
    towerFinite A (singleObj m M) := by
  intro n
  by_cases h : n = m
  · subst h
    rw [singleObj_self]
    infer_instance
  · have : Subsingleton (singleObj m M n) :=
      ModuleCat.subsingleton_of_isZero (isZero_singleObj M h)
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩

/-- The module `M` placed at level `m`, as an object of `FGTower A`. -/
def singleFG (m : ℕ) (M : ModuleCat.{u} (A m)) [Module.Finite (A m) M] : FGTower A :=
  ⟨singleObj m M, towerFinite_singleObj m M⟩

omit [∀ m, IsNoetherianRing (A m)] in
lemma zero_hom_app (n : ℕ) : (0 : X ⟶ Y).hom n = 0 :=
  (FGTower.eval A n).map_zero X Y

omit [∀ m, IsNoetherianRing (A m)] in
lemma id_hom_app (n : ℕ) : (𝟙 X : X ⟶ X).hom n = 𝟙 (X.obj n) := rfl

omit [∀ m, IsNoetherianRing (A m)] in
lemma comp_hom_app {Z : FGTower A} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (f ≫ g).hom n = f.hom n ≫ g.hom n := rfl

omit [∀ m, IsNoetherianRing (A m)] in
lemma hom_eq_zero_iff (f : X ⟶ Y) : f = 0 ↔ ∀ n, f.hom n = 0 := by
  refine ⟨fun h n => by rw [h, zero_hom_app], fun h => ?_⟩
  exact ObjectProperty.hom_ext _ (funext fun n => by rw [h n, zero_hom_app])

omit [∀ m, IsNoetherianRing (A m)] in
lemma isIso_iff (f : X ⟶ Y) : IsIso f ↔ ∀ n, IsIso (f.hom n) := by
  rw [← ObjectProperty.isIso_hom_iff, isIso_pi_iff]

omit [∀ m, IsNoetherianRing (A m)] in
lemma mono_of_hom (f : X ⟶ Y) (hf : ∀ n, Mono (f.hom n)) : Mono f :=
  have : Mono ((towerFinite A).ι.map f) := mono_pi f.hom hf
  (towerFinite A).ι.mono_of_mono_map this

omit [∀ m, IsNoetherianRing (A m)] in
lemma isZero_iff : IsZero X ↔ ∀ n, IsZero (X.obj n) := by
  refine ⟨fun h n => (FGTower.eval A n).map_isZero h, fun h => ?_⟩
  rw [IsZero.iff_id_eq_zero, hom_eq_zero_iff]
  intro n
  exact (h n).eq_of_src _ _

lemma mono_hom (f : X ⟶ Y) [Mono f] (n : ℕ) : Mono (f.hom n) :=
  (FGTower.eval A n).map_mono f

end FGTower

open FGTower

section Simple

variable (S : FGTower A) [Simple S]

omit [∀ m, IsNoetherianRing (A m)] in
lemma exists_level : ∃ m, ¬ IsZero (S.obj m) := by
  by_contra h
  exact Simple.not_isZero S (isZero_iff.mpr fun n => not_not.mp (not_exists.mp h n))

lemma isZero_of_ne {m n : ℕ} (hm : ¬ IsZero (S.obj m)) (h : n ≠ m) : IsZero (S.obj n) := by
  by_contra hn
  let p : S ⟶ S := ObjectProperty.homMk (levelHom n (𝟙 (S.obj n)))
  have hp : p ≠ 0 := by
    intro h0
    apply hn
    rw [IsZero.iff_id_eq_zero]
    have := (hom_eq_zero_iff p).mp h0 n
    rwa [ObjectProperty.homMk_hom, levelHom_self] at this
  have : Mono p := mono_of_nonzero_from_simple hp
  have hpp : p ≫ p = 𝟙 S ≫ p := by
    refine ObjectProperty.hom_ext _ (funext fun k => ?_)
    rw [comp_hom_app, comp_hom_app, id_hom_app]
    by_cases hk : k = n
    · subst hk
      simp [p, levelHom_self]
    · simp [p, levelHom_ne _ hk]
  have h1 : p = 𝟙 S := (cancel_mono p).mp hpp
  apply hm
  rw [IsZero.iff_id_eq_zero]
  have := congrArg (fun g => g.hom m) h1
  simp only [p, ObjectProperty.homMk_hom, levelHom_ne _ h.symm] at this
  exact this.symm

/-- The level at which a simple object of `FGTower A` is concentrated. -/
def level : ℕ := (exists_level S).choose

omit [∀ m, IsNoetherianRing (A m)] in
lemma not_isZero_level : ¬ IsZero (S.obj (level S)) := (exists_level S).choose_spec

lemma isZero_of_ne_level {n : ℕ} (h : n ≠ level S) : IsZero (S.obj n) :=
  isZero_of_ne S (not_isZero_level S) h

lemma level_eq {n : ℕ} (hn : ¬ IsZero (S.obj n)) : level S = n := by
  by_contra h
  exact hn (isZero_of_ne_level S (Ne.symm h))

/-- A simple object of `FGTower A` is a simple module at its level. -/
theorem simple_level : Simple (S.obj (level S)) := by
  constructor
  intro Y g _
  let m := level S
  have : Module.Finite (A m) (S.obj m) := S.property m
  have hg : Function.Injective g.hom := (ModuleCat.mono_iff_injective g).mp ‹_›
  have : Module.Finite (A m) Y := Module.Finite.of_injective g.hom hg
  constructor
  · intro hiso h0
    apply not_isZero_level S
    rw [IsZero.iff_id_eq_zero]
    subst h0
    rw [← IsIso.inv_hom_id (0 : Y ⟶ S.obj m), comp_zero]
  · intro hne
    let G : singleFG m Y ⟶ S :=
      ObjectProperty.homMk (levelHom m (eqToHom (singleObj_self m Y) ≫ g))
    have hG : Mono G := by
      refine mono_of_hom G fun n => ?_
      by_cases hn : n = m
      · subst hn
        simp only [G, ObjectProperty.homMk_hom, levelHom_self]
        infer_instance
      · exact mono_of_isZero _ (isZero_singleObj Y hn)
    have hG0 : G ≠ 0 := by
      intro h0
      apply hne
      have := (hom_eq_zero_iff G).mp h0 m
      simp only [G, ObjectProperty.homMk_hom, levelHom_self] at this
      simpa using this
    have : IsIso G := isIso_of_mono_of_nonzero hG0
    have := (isIso_iff G).mp this m
    simp only [G, ObjectProperty.homMk_hom, levelHom_self] at this
    exact IsIso.of_isIso_comp_left (eqToHom (singleObj_self m Y)) g

instance isSimpleModule_level : IsSimpleModule (A (level S)) (S.obj (level S)) :=
  (simple_iff_isSimpleModule' _).mp (simple_level S)

end Simple

/-- A simple module placed at one level is a simple object of `FGTower A`. -/
theorem simple_singleFG (m : ℕ) (M : ModuleCat.{u} (A m)) [Module.Finite (A m) M]
    [IsSimpleModule (A m) M] : Simple (singleFG m M) := by
  have hM : Simple (singleObj m M m) := by
    rw [singleObj_self]
    exact (simple_iff_isSimpleModule' M).mpr ‹_›
  have : Simple ((singleFG m M).obj m) := hM
  constructor
  intro Y f _
  have hY : ∀ n, n ≠ m → IsZero (Y.obj n) := fun n hn => by
    have : Mono (f.hom n) := mono_hom f n
    have hz : IsZero (singleObj m M n) := isZero_singleObj M hn
    rw [IsZero.iff_id_eq_zero]
    exact (cancel_mono (f.hom n)).mp (hz.eq_of_tgt _ _)
  have : Mono (f.hom m) := mono_hom f m
  have key : IsIso f ↔ IsIso (f.hom m) := by
    rw [isIso_iff]
    refine ⟨fun h => h m, fun h n => ?_⟩
    by_cases hn : n = m
    · subst hn; exact h
    · exact isIso_of_isZero _ (hY n hn) (isZero_singleObj M hn)
  rw [key, Simple.mono_isIso_iff_nonzero, ne_eq, ne_eq, hom_eq_zero_iff]
  refine not_congr ⟨fun h n => ?_, fun h => h m⟩
  by_cases hn : n = m
  · subst hn; exact h
  · exact (isZero_singleObj M hn).eq_of_tgt _ _

lemma level_singleFG (m : ℕ) (M : ModuleCat.{u} (A m)) [Module.Finite (A m) M]
    [IsSimpleModule (A m) M] :
    have := simple_singleFG m M
    level (singleFG m M) = m := by
  intro
  apply level_eq
  change ¬ IsZero (singleObj m M m)
  rw [singleObj_self]
  have : Simple M := (simple_iff_isSimpleModule' M).mpr ‹_›
  exact Simple.not_isZero _


variable (A) in
/-- Indices of simple objects of `FGTower A`: a level and an isomorphism class of simple modules
at that level. -/
abbrev K0Index : Type (u + 1) := Σ m, Module.SimpleClass.{u, u} (A m)

omit [∀ m, IsNoetherianRing (A m)] in
lemma sigma_mk_congr {X : ∀ n, ModuleCat.{u} (A n)} {a b : ℕ} (hab : a = b)
    [IsSimpleModule (A a) (X a)] [IsSimpleModule (A b) (X b)] :
    (⟨a, Module.SimpleClass.mk (X a)⟩ : K0Index A) = ⟨b, Module.SimpleClass.mk (X b)⟩ := by
  subst hab; rfl

omit [∀ m, IsNoetherianRing (A m)] in
lemma eq_and_nonempty_iso_of_sigma_eq {X Y : ∀ n, ModuleCat.{u} (A n)} {a b : ℕ}
    [IsSimpleModule (A a) (X a)] [IsSimpleModule (A b) (Y b)]
    (h : (⟨a, Module.SimpleClass.mk (X a)⟩ : K0Index A) = ⟨b, Module.SimpleClass.mk (Y b)⟩) :
    a = b ∧ Nonempty (X b ≅ Y b) := by
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨e⟩ := Module.SimpleClass.nonempty_linearEquiv (eq_of_heq hh)
  exact ⟨rfl, ⟨e.toModuleIso⟩⟩

/-- A representative simple module of a class. -/
def simpleRep (m : ℕ) (c : Module.SimpleClass.{u, u} (A m)) :
    {S : ModuleCat.{u} (A m) // IsSimpleModule (A m) S} :=
  Quotient.out (s := Module.simpleSetoid (A m)) c

instance (m : ℕ) (c : Module.SimpleClass.{u, u} (A m)) :
    IsSimpleModule (A m) (simpleRep m c).1 :=
  (simpleRep m c).2

instance (m : ℕ) (c : Module.SimpleClass.{u, u} (A m)) :
    Module.Finite (A m) (simpleRep m c).1 :=
  module_finite_of_isSimpleModule _ _

omit [∀ m, IsNoetherianRing (A m)] in
lemma mk_simpleRep (m : ℕ) (c : Module.SimpleClass.{u, u} (A m)) :
    Module.SimpleClass.mk (simpleRep m c).1 = c := by
  conv_rhs => rw [← Quotient.out_eq (s := Module.simpleSetoid (A m)) c]
  exact Quotient.sound ⟨Iso.refl _⟩

section K0

variable [∀ m, IsArtinianRing (A m)]

omit [∀ m, IsNoetherianRing (A m)] in
lemma isFiniteLength_obj [∀ m, IsNoetherianRing (A m)] (X : FGTower A) (m : ℕ) :
    IsFiniteLength (A m) (X.obj m) := by
  have : Module.Finite (A m) (X.obj m) := X.property m
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

variable (A) in
/-- The index of a simple object of `FGTower A`. -/
def simpleIdx (S : FGTower A) [Simple S] : K0Index A :=
  ⟨level S, Module.SimpleClass.mk (S.obj (level S))⟩

variable (N : ℕ)

variable (A) in
/-- Composition multiplicities of a family, over the levels below `N`. -/
def clsN (X : FGTower A) : K0Index A →₀ ℕ :=
  ∑ m ∈ Finset.range N,
    Finsupp.mapDomain (Sigma.mk m) (Module.compositionFactors (A m) (X.obj m))

lemma clsN_add (S : ShortComplex (FGTower A)) (hS : S.ShortExact) :
    clsN A N S.X₂ = clsN A N S.X₁ + clsN A N S.X₃ := by
  rw [clsN, clsN, clsN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finsupp.mapDomain_add]
  congr 1
  have := hS.mono_f
  have := hS.epi_g
  have : Mono ((FGTower.eval A m).map S.f) := (FGTower.eval A m).map_mono _
  have : Epi ((FGTower.eval A m).map S.g) := (FGTower.eval A m).map_epi _
  have hm := hS.map (FGTower.eval A m)
  exact Module.compositionFactors_eq_of_shortExact hm (isFiniteLength_obj S.X₁ m)
    (isFiniteLength_obj S.X₃ m)

variable {N} (hN : ∀ m, N ≤ m → Subsingleton (A m))

include hN in
omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
lemma level_lt (S : FGTower A) [Simple S] : level S < N := by
  by_contra h
  have : Subsingleton (A (level S)) := hN _ (not_lt.mp h)
  have : Subsingleton (S.obj (level S)) := Module.subsingleton (A (level S)) _
  exact not_isZero_level S (ModuleCat.isZero_of_subsingleton _)

include hN in
omit [∀ m, IsArtinianRing (A m)] in
lemma clsN_simple (S : FGTower A) [Simple S] :
    clsN A N S = Finsupp.single (simpleIdx A S) 1 := by
  rw [clsN, Finset.sum_eq_single (level S)]
  · rw [Module.compositionFactors_of_isSimpleModule, Finsupp.mapDomain_single]
    rfl
  · intro m _ hm
    have : Subsingleton (S.obj m) :=
      ModuleCat.subsingleton_of_isZero (isZero_of_ne_level S hm)
    rw [Module.compositionFactors_of_subsingleton, Finsupp.mapDomain_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (level_lt hN S)) h

omit [∀ m, IsArtinianRing (A m)] in
lemma nonempty_iso_of_simpleIdx_eq (S T : FGTower A) [Simple S] [Simple T]
    (h : simpleIdx A S = simpleIdx A T) : Nonempty (S ≅ T) := by
  obtain ⟨hl, ⟨e⟩⟩ := eq_and_nonempty_iso_of_sigma_eq (X := S.obj) (Y := T.obj)
    (a := level S) (b := level T) h
  let f : S ⟶ T := ObjectProperty.homMk (levelHom (level T) e.hom)
  have hf : f ≠ 0 := by
    intro h0
    have := (hom_eq_zero_iff f).mp h0 (level T)
    simp only [f, ObjectProperty.homMk_hom, levelHom_self] at this
    apply not_isZero_level S
    rw [hl, IsZero.iff_id_eq_zero, ← e.hom_inv_id, this, zero_comp]
  have := isIso_of_hom_simple hf
  exact ⟨asIso f⟩

omit [∀ m, IsArtinianRing (A m)] in
lemma simpleIdx_singleFG (m : ℕ) (M : ModuleCat.{u} (A m)) [Module.Finite (A m) M]
    [IsSimpleModule (A m) M] :
    have := simple_singleFG m M
    simpleIdx A (singleFG m M) = ⟨m, Module.SimpleClass.mk M⟩ := by
  intro
  have hM : IsSimpleModule (A m) ((singleFG m M).obj m) := by
    change IsSimpleModule (A m) (singleObj m M m)
    rw [singleObj_self]
    infer_instance
  rw [simpleIdx, sigma_mk_congr (X := (singleFG m M).obj) (level_singleFG m M)]
  exact Sigma.ext rfl (heq_of_eq
    (Module.SimpleClass.mk_eq_mk (eqToIso (singleObj_self m M)).toLinearEquiv))

variable (A) in
/-- The representative simple object of an index. -/
def simpleObj (i : K0Index A) : FGTower A :=
  singleFG i.1 (simpleRep i.1 i.2).1

omit [∀ m, IsArtinianRing (A m)] in
lemma simple_simpleObj (i : K0Index A) : Simple (simpleObj A i) :=
  simple_singleFG _ _

omit [∀ m, IsArtinianRing (A m)] in
lemma simpleIdx_simpleObj (i : K0Index A) :
    have := simple_simpleObj i
    simpleIdx A (simpleObj A i) = i := by
  intro
  exact (simpleIdx_singleFG _ _).trans (Sigma.ext rfl (heq_of_eq (mk_simpleRep _ _)))

variable (A) in
include hN in
/-- The Grothendieck-group data of `FGTower A`, for a tower of noetherian and artinian rings
vanishing from level `N` on. -/
def k0Data : Sl2.K0Data (FGTower A) (K0Index A) (K0Index A →₀ ℚ) where
  B := Finsupp.basisSingleOne
  cls X := Finsupp.mapRange (Nat.cast : ℕ → ℚ) Nat.cast_zero (clsN A N X)
  cls_add S hS := by
    rw [clsN_add N S hS, Finsupp.mapRange_add (fun _ _ => Nat.cast_add _ _)]
  idx S h := have := h; simpleIdx A S
  cls_simple S h := by
    have := h
    rw [clsN_simple hN S, Finsupp.mapRange_single, Nat.cast_one, Finsupp.coe_basisSingleOne]
  iso_of_idx_eq S T hS hT h := by
    have := hS
    have := hT
    exact nonempty_iso_of_simpleIdx_eq S T h
  simple := simpleObj A
  simple_simple := simple_simpleObj
  idx_simple := simpleIdx_simpleObj
  cls_mem_cone X j := by
    simp
  cls_int X j := ⟨clsN A N X j, by simp⟩

include hN in
lemma isZero_of_clsN_eq_zero (X : FGTower A) (h : clsN A N X = 0) : IsZero X := by
  rw [isZero_iff]
  intro n
  by_cases hn : N ≤ n
  · have : Subsingleton (A n) := hN n hn
    have : Subsingleton (X.obj n) := Module.subsingleton (A n) _
    exact ModuleCat.isZero_of_subsingleton _
  · have hz := (Finset.sum_eq_zero_iff.mp h) n (Finset.mem_range.mpr (not_le.mp hn))
    rw [← Finsupp.mapDomain_zero (f := Sigma.mk n)] at hz
    have h0 := Finsupp.mapDomain_injective sigma_mk_injective hz
    have := Module.subsingleton_of_compositionFactors_eq_zero (isFiniteLength_obj X n) h0
    exact ModuleCat.isZero_of_subsingleton _

include hN in
/-- Every object of `FGTower A` is artinian, for a tower of noetherian and artinian rings
vanishing from level `N` on. -/
theorem isArtinianObject (X : FGTower A) : IsArtinianObject X := by
  refine (k0Data A hN).isArtinianObject_of_cls (fun Y hY => ?_) X
  refine isZero_of_clsN_eq_zero hN Y ?_
  ext j
  have := congrArg (fun f => f j) hY
  simpa [k0Data] using this

include hN in
/-- Every object of `FGTower A` is noetherian, for a tower of noetherian and artinian rings
vanishing from level `N` on. -/
theorem isNoetherianObject (X : FGTower A) : IsNoetherianObject X := by
  refine (k0Data A hN).isNoetherianObject_of_cls (fun Y hY => ?_) X
  refine isZero_of_clsN_eq_zero hN Y ?_
  ext j
  have := congrArg (fun f => f j) hY
  simpa [k0Data] using this

include hN in
/-- There are finitely many simple classes along a tower of noetherian and artinian rings
vanishing from level `N` on. -/
theorem finite_k0Index : Finite (K0Index A) := by
  have : ∀ m, Finite (Module.SimpleClass.{u, u} (A m)) := fun m =>
    Module.finite_simpleClass (A m)
  refine Finite.of_surjective
    (fun x : Σ m : Fin N, Module.SimpleClass.{u, u} (A m) => (⟨x.1, x.2⟩ : K0Index A)) ?_
  rintro ⟨m, c⟩
  by_cases hm : m < N
  · exact ⟨⟨⟨m, hm⟩, c⟩, rfl⟩
  · have : Subsingleton (A m) := hN m (not_lt.mp hm)
    induction c using Quotient.inductionOn with
    | h S =>
      obtain ⟨S, hS⟩ := S
      have : Subsingleton S := Module.subsingleton (A m) S
      have : Nontrivial S := IsSimpleModule.nontrivial (A m) S
      exact (not_subsingleton S ‹_›).elim

end K0

end Categorification.ModuleTower
