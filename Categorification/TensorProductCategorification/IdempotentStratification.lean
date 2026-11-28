/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TensorProductCategorification.StandardlyStratified
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Stratifications of module categories by idempotents (Losev–Webster, Definition 2.1)

I. Losev, B. Webster, *On uniqueness of tensor products of irreducible categorifications*,
arXiv:1303.1336v3, Definition 2.1: the generic part of the standardly stratified structure on
modules over a ring `A` with idempotents `e : T → A` labelled by `β : T → Ξ` in a poset (to be
applied to Webster's algebras `T^λ`, arXiv:1309.3796v3, Corollary 5.27).

For `U ⊆ Ξ` the class `supportedIn e β U` consists of the modules `M` with `e(t) M = 0` whenever
`β t ∉ U`; for `U = Iic ξ`, `Iio ξ` these are `C_{≤ξ}` and `C_{<ξ}`. We work in `ModuleCat A`
(all modules; no finiteness is needed).

## Main results

* `isSerreClass_killedBy`: the modules annihilated by a set of idempotents form a Serre class;
  hence `isSerreClass_supportedIn`.
* `exists_simpleSubquotient_not_killed`, `killedBy_eq_spannedBy`: a module is annihilated by a
  set of idempotents iff each of its simple subquotients is.
* `isGreatest_labelSupport_of_maximal`, `exists_isGreatest_labelSupport` (labels): under the
  hypothesis `HasStandardQuotients` (K), a maximal element `ρ(L)` of the label support
  `{β t | e(t) L ≠ 0}` of a simple module `L` is its greatest element, and one exists when
  `∑ e(t) = 1` and `T` is finite.
* `supportedIn_eq_spannedBy`, `le_eq_supportedIn_Iic`, `lt_eq_supportedIn_Iio` (Serre
  subcategories): for a `SimpleLabelling` whose `ρ(λ)` is the greatest label of `L(λ)`, the
  classes `σ.le ξ`, `σ.lt ξ` of `StandardlyStratified.lean` are `C_{≤ξ}`, `C_{<ξ}` defined by
  idempotents; `isSerreClass_le`, `isSerreClass_ltIn` give the Serre-class instances needed by
  `StandardStratification`.
-/

namespace Categorification.TensorProductCategorification

open CategoryTheory Limits

universe u v

section Subquotient

variable {C : Type*} [Category* C] [Abelian C]

/-- If `B` is a subobject of `X` (through a monomorphism `f`) and `g : B ⟶ L` is an epimorphism
onto a simple object, then `L` is a simple subquotient of `X`. -/
theorem IsSimpleSubquotient.of_mono_epi {X B L : C} (f : B ⟶ X) [Mono f] (g : B ⟶ L) [Epi g]
    [Simple L] : IsSimpleSubquotient L X := by
  refine ⟨inferInstance, Subobject.mk (kernel.ι g ≫ f), Subobject.mk f,
    Subobject.mk_le_mk_of_comm (kernel.ι g) rfl, ⟨?_⟩⟩
  exact cokernelIsoOfEq (Subobject.ofLE_mk_le_mk_of_comm (kernel.ι g) rfl) ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    ((Abelian.epiIsCokernelOfKernel _ (kernelIsKernel g)).coconePointUniqueUpToIso
      (colimit.isColimit _)).symm

end Subquotient

section Killed

variable {A : Type u} [Ring A]

/-- The `A`-modules annihilated by every element of `S`. -/
def killedBy (S : Set A) : ObjectProperty (ModuleCat.{v} A) :=
  fun M => ∀ a ∈ S, ∀ m : M, a • m = 0

/-- The modules annihilated by a set of idempotents form a Serre class. -/
theorem isSerreClass_killedBy (S : Set A) (hS : ∀ a ∈ S, IsIdempotentElem a) :
    (killedBy.{u, v} S).IsSerreClass where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
    fun _ _ _ => Subsingleton.elim _ _⟩
  prop_of_mono {X Y} f _ hY a ha m := by
    apply (ModuleCat.mono_iff_injective f).1 inferInstance
    rw [map_smul, hY a ha, map_zero]
  prop_of_epi {X Y} f _ hX a ha m := by
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).1 inferInstance m
    rw [← map_smul, hX a ha, map_zero]
  prop_X₂_of_shortExact {T} hT h₁ h₃ a ha m := by
    obtain ⟨x, hx⟩ := (T.moduleCat_exact_iff.1 hT.exact) (a • m) (by
      rw [map_smul, h₃ a ha, ])
    have := hT.mono_f
    rw [← (hS a ha).eq, mul_smul, ← hx, ← map_smul, h₁ a ha, map_zero]

end Killed
section Detect

variable {A : Type u} [Ring A]

/-- If an idempotent `a` does not annihilate `M`, then some simple subquotient of `M` is not
annihilated by `a`: take a maximal submodule of the cyclic submodule `A (a m)`, `a m ≠ 0`. -/
theorem exists_simpleSubquotient_not_killed {a : A} (ha : IsIdempotentElem a)
    {M : ModuleCat.{v} A} {m : M} (hm : a • m ≠ 0) :
    ∃ L : ModuleCat.{v} A, IsSimpleSubquotient L M ∧ ∃ x : L, a • x ≠ 0 := by
  set R : Submodule A M := Submodule.span A {a • m}
  let x : R := ⟨a • m, Submodule.subset_span rfl⟩
  have hx : x ≠ 0 := fun h => hm (congrArg Subtype.val h)
  have hbot : (⊥ : Submodule A R) ≠ ⊤ := by
    intro h
    exact hx ((Submodule.mem_bot A).1 (h ▸ Submodule.mem_top))
  obtain ⟨Q, hQ, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A R)).resolve_left hbot
  have hxQ : x ∉ Q := by
    intro h
    refine hQ.1 (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 y.2
    have : y = b • x := Subtype.ext hb.symm
    rw [this]
    exact Q.smul_mem b h
  have : IsSimpleModule A (R ⧸ Q) := (isSimpleModule_iff_isCoatom).2 hQ
  let f : ModuleCat.of A R ⟶ M := ModuleCat.ofHom R.subtype
  let g : ModuleCat.of A R ⟶ ModuleCat.of A (R ⧸ Q) := ModuleCat.ofHom Q.mkQ
  have : Mono f := (ModuleCat.mono_iff_injective f).2 R.injective_subtype
  have : Epi g := (ModuleCat.epi_iff_surjective g).2 Q.mkQ_surjective
  refine ⟨ModuleCat.of A (R ⧸ Q), IsSimpleSubquotient.of_mono_epi f g,
    Submodule.Quotient.mk x, ?_⟩
  have hax : a • x = x := Subtype.ext (by simp [x, ← mul_smul, ha.eq])
  rw [← Submodule.Quotient.mk_smul, hax]
  exact fun h => hxQ ((Submodule.Quotient.mk_eq_zero Q).1 h)

/-- Modules annihilated by a set of idempotents are exactly the modules all of whose simple
subquotients are annihilated by it. -/
theorem killedBy_eq_spannedBy (S : Set A) (hS : ∀ a ∈ S, IsIdempotentElem a) :
    killedBy.{u, v} S = spannedBy (killedBy.{u, v} S) := by
  have := isSerreClass_killedBy.{u, v} S hS
  funext M
  apply propext
  constructor
  · rintro hM L ⟨_, B, B', h, ⟨i⟩⟩
    exact (killedBy S).prop_of_iso i ((killedBy S).prop_of_epi (cokernel.π _)
      ((killedBy S).prop_of_mono B'.arrow hM))
  · intro hM a ha m
    by_contra hm
    obtain ⟨L, hL, y, hy⟩ := exists_simpleSubquotient_not_killed (hS a ha) hm
    exact hy (hM L hL a ha y)

end Detect
section Labels

variable {A : Type u} [Ring A] {T : Type*} (e : T → A) {Ξ : Type*} [PartialOrder Ξ] (β : T → Ξ)

/-- The **label support** of `M`: the labels `β t` with `e(t) M ≠ 0`. -/
def labelSupport (M : ModuleCat.{v} A) : Set Ξ :=
  {ξ | ∃ t, β t = ξ ∧ ∃ m : M, e t • m ≠ 0}

/-- The idempotents `e(t)` whose label `β t` lies outside `U`. -/
def idempotentsOff (U : Set Ξ) : Set A :=
  e '' {t | β t ∉ U}

/-- The modules **supported in** `U ⊆ Ξ`: `e(t) M = 0` whenever `β t ∉ U`. For `U = Iic ξ` and
`U = Iio ξ` these are `C_{≤ξ}` and `C_{<ξ}`. -/
abbrev supportedIn (U : Set Ξ) : ObjectProperty (ModuleCat.{v} A) :=
  killedBy (idempotentsOff e β U)

variable {e β} in
omit [PartialOrder Ξ] in
/-- Membership in `C_U`, unfolded. -/
theorem supportedIn_iff {U : Set Ξ} {M : ModuleCat.{v} A} :
    supportedIn e β U M ↔ ∀ t, β t ∉ U → ∀ m : M, e t • m = 0 := by
  constructor
  · intro h t ht m
    exact h _ ⟨t, ht, rfl⟩ m
  · rintro h _ ⟨t, ht, rfl⟩ m
    exact h t ht m

omit [PartialOrder Ξ] in
/-- `C_U` is a Serre class when the `e(t)` are idempotent. -/
theorem isSerreClass_supportedIn (he : ∀ t, IsIdempotentElem (e t)) (U : Set Ξ) :
    (supportedIn.{u, v} e β U).IsSerreClass :=
  isSerreClass_killedBy _ (by rintro _ ⟨t, -, rfl⟩; exact he t)

/-- **Hypothesis (K)** (standard quotients): for each `t` a module `S t` (in the application, a
quotient of `A e(t)`) supported in `{ξ | ξ ≤ β t}`, such that every simple `L` with
`e(t) L ≠ 0` and `β t` maximal in the label support of `L` is a quotient of `S t`. -/
structure HasStandardQuotients (S : T → ModuleCat.{v} A) : Prop where
  supportedIn_Iic : ∀ t, supportedIn e β (Set.Iic (β t)) (S t)
  exists_epi : ∀ t (L : ModuleCat.{v} A), Simple L → (∃ m : L, e t • m ≠ 0) →
    Maximal (· ∈ labelSupport e β L) (β t) → ∃ f : S t ⟶ L, Epi f

variable {e β}

/-- **Labels.** Under (K), a maximal element of the label support of a simple module is its
greatest element. -/
theorem isGreatest_labelSupport_of_maximal {S : T → ModuleCat.{v} A}
    (hK : HasStandardQuotients e β S) (L : ModuleCat.{v} A) [Simple L] {ξ : Ξ}
    (hξ : Maximal (· ∈ labelSupport e β L) ξ) : IsGreatest (labelSupport e β L) ξ := by
  obtain ⟨t, rfl, m, hm⟩ := hξ.1
  obtain ⟨f, hf⟩ := hK.exists_epi t L inferInstance ⟨m, hm⟩ hξ
  refine ⟨hξ.1, ?_⟩
  rintro _ ⟨t', rfl, y, hy⟩
  by_contra h
  obtain ⟨s, rfl⟩ := (ModuleCat.epi_iff_surjective f).1 hf y
  apply hy
  rw [← map_smul, supportedIn_iff.1 (hK.supportedIn_Iic t) t' h s, map_zero]

omit [PartialOrder Ξ] in
/-- A nonzero module has nonempty label support when the `e(t)` sum to `1`. -/
theorem labelSupport_nonempty [Fintype T] (hsum : ∑ t, e t = 1) (M : ModuleCat.{v} A)
    [Nontrivial M] : (labelSupport e β M).Nonempty := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  by_contra h
  have h0 : ∀ t, e t • m = 0 := fun t => by
    by_contra h'
    exact h ⟨β t, t, rfl, m, h'⟩
  apply hm
  calc m = (1 : A) • m := (one_smul A m).symm
    _ = ∑ t, e t • m := by rw [← hsum, Finset.sum_smul]
    _ = 0 := by simp [h0]

/-- **Labels.** Under (K), with `∑ e(t) = 1` and `T` finite, the label support of every simple
module has a greatest element `ρ(L)`. -/
theorem exists_isGreatest_labelSupport [Fintype T] (hsum : ∑ t, e t = 1)
    {S : T → ModuleCat.{v} A} (hK : HasStandardQuotients e β S) (L : ModuleCat.{v} A)
    [Simple L] : ∃ ξ, IsGreatest (labelSupport e β L) ξ := by
  have : Nontrivial L := IsSimpleModule.nontrivial A L
  have hfin : (labelSupport e β L).Finite :=
    (Set.finite_range β).subset (by rintro _ ⟨t, rfl, -⟩; exact ⟨t, rfl⟩)
  obtain ⟨ξ, hξ⟩ := hfin.exists_maximal (labelSupport_nonempty hsum L)
  exact ⟨ξ, isGreatest_labelSupport_of_maximal hK L hξ⟩

end Labels

section Strata

variable {A : Type u} [Ring A] {T : Type*} {e : T → A} {Ξ : Type v} [PartialOrder Ξ]
  {β : T → Ξ} (he : ∀ t, IsIdempotentElem (e t)) (σ : SimpleLabelling (ModuleCat.{v} A) Ξ)
  (hρ : ∀ l, IsGreatest (labelSupport e β (σ.simple l)) (σ.ρ l))

include he hρ in
/-- **Serre subcategories.** If `ρ(λ)` is the greatest label of `L(λ)`, then for a lower set
`U ⊆ Ξ` the modules supported in `U` are exactly the modules all of whose simple subquotients
are `L(λ)` with `ρ(λ) ∈ U`. -/
theorem supportedIn_eq_spannedBy {U : Set Ξ} (hU : IsLowerSet U) :
    supportedIn e β U = spannedBy fun L => ∃ l, σ.ρ l ∈ U ∧ Nonempty (L ≅ σ.simple l) := by
  have hS : ∀ a ∈ idempotentsOff e β U, IsIdempotentElem a := by
    rintro _ ⟨t, -, rfl⟩; exact he t
  have := isSerreClass_killedBy.{u, v} _ hS
  rw [supportedIn, killedBy_eq_spannedBy _ hS]
  funext M
  apply propext
  refine forall_congr' fun L => forall_congr' fun hL => ?_
  have : Simple L := hL.1
  constructor
  · intro hk
    obtain ⟨l, ⟨i⟩⟩ := σ.exists_iso L hL.1
    refine ⟨l, ?_, ⟨i⟩⟩
    by_contra hlU
    obtain ⟨t, ht, m, hm⟩ := (hρ l).1
    exact hm ((killedBy _).prop_of_iso i hk _ ⟨t, by rw [Set.mem_ofPred_eq, ht]; exact hlU, rfl⟩ m)
  · rintro ⟨l, hlU, ⟨i⟩⟩
    refine (killedBy _).prop_of_iso i.symm ?_
    rintro _ ⟨t, ht, rfl⟩ m
    by_contra hm
    exact ht (hU ((hρ l).2 ⟨t, rfl, m, hm⟩) hlU)

include he hρ in
/-- **`C_{≤ξ}` by idempotents.** `σ.le ξ` (spanned by the `L(λ)` with `ρ(λ) ≤ ξ`) is the class of
modules with `e(t) M = 0` whenever `¬ β t ≤ ξ`. -/
theorem le_eq_supportedIn_Iic (ξ : Ξ) : σ.le ξ = supportedIn e β (Set.Iic ξ) :=
  (supportedIn_eq_spannedBy he σ hρ (isLowerSet_Iic ξ)).symm

include he hρ in
/-- **`C_{<ξ}` by idempotents.** `σ.lt ξ` is the class of modules with `e(t) M = 0` whenever
`¬ β t < ξ`. -/
theorem lt_eq_supportedIn_Iio (ξ : Ξ) : σ.lt ξ = supportedIn e β (Set.Iio ξ) :=
  (supportedIn_eq_spannedBy he σ hρ (isLowerSet_Iio ξ)).symm

include he hρ in
/-- `C_{≤ξ}` is a Serre class. -/
theorem isSerreClass_le (ξ : Ξ) : (σ.le ξ).IsSerreClass := by
  rw [le_eq_supportedIn_Iic he σ hρ]
  exact isSerreClass_supportedIn e β he _

include he hρ in
/-- `C_{<ξ}` is a Serre class. -/
theorem isSerreClass_lt (ξ : Ξ) : (σ.lt ξ).IsSerreClass := by
  rw [lt_eq_supportedIn_Iio he σ hρ]
  exact isSerreClass_supportedIn e β he _

include he hρ in
/-- `C_{<ξ}` is a Serre class inside `C_{≤ξ}`. -/
theorem isSerreClass_ltIn (ξ : Ξ) [(σ.le ξ).IsSerreClass] : (σ.ltIn ξ).IsSerreClass := by
  have := isSerreClass_lt he σ hρ ξ
  have hk : ∀ {X Y : (σ.le ξ).FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (σ.le ξ).ι := fun f => (σ.le ξ).preservesKernels_ι f
  have hc : ∀ {X Y : (σ.le ξ).FullSubcategory} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (σ.le ξ).ι := fun f => (σ.le ξ).preservesCokernels_ι f
  have := Functor.preservesFiniteLimits_of_preservesKernels (σ.le ξ).ι
  have := Functor.preservesFiniteColimits_of_preservesCokernels (σ.le ξ).ι
  change ((σ.lt ξ).inverseImage (σ.le ξ).ι).IsSerreClass
  infer_instance

end Strata

end Categorification.TensorProductCategorification
