/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Graded modules over graded algebras

Let `A` be a `k`-algebra graded by `𝒜 : ι → Submodule k A` (`[GradedAlgebra 𝒜]`). Following
Mathlib, a *graded `A`-module* is an `A`-module `M` (which is also a `k`-module, with
`[IsScalarTower k A M]`) together with a family `ℳ : ι → Submodule k M` such that

* `[DirectSum.Decomposition ℳ]` : `M = ⨁ d, ℳ d` (internally), and
* `[SetLike.GradedSMul 𝒜 ℳ]` : `𝒜 i • ℳ j ⊆ ℳ (i + j)`.

The grading is extra data (the family `ℳ`), not part of the type `M`. This file provides the
basic constructions needed for graded representation theory (Khovanov–Lauda I,
arXiv:0803.4121v2, §2.5):

* `Graded.shift ℳ a` : the grading shift `M{a}`, **shifted up by `a`**:
  `shift ℳ a d = ℳ (d - a)`, so an element of degree `d` in `M` has degree `d + a` in `M{a}`.
  This is KL I's convention ("`N{a}` denotes `N` with the grading shifted up by `a`",
  §2.5); with it `gdim (M{a}) = q^a gdim M` (see `Categorification.Algebra.Graded.Dimension`).
* `Graded.prod ℳ 𝒩` : the grading `(ℳ d).prod (𝒩 d)` of the direct sum `M × N`.
* `Graded.comap ℳ f` : the grading `(ℳ d).comap f` pulled back along an injective linear map
  `f : N → M` whose range is homogeneous (`isInternal_comap`). This covers graded submodules
  (`Graded.submodule ℳ p`, for a homogeneous `A`-submodule `p`; `isInternal_submodule`) and
  graded `k`-subspaces such as `e M = {m | e • m = m}` for a degree-zero `e`
  (`Graded.idemSubspace`, `Graded.idem`, `isInternal_idem`).
* `Graded.PreservesGrading ℳ 𝒩 f` : `f` is degree-preserving (maps `ℳ d` into `𝒩 d`); such maps
  commute with the projections to homogeneous components (`decompose_map`). Degree-zero elements
  of `A` commute with them too (`decompose_smul_of_mem_zero`).
* `Graded.GradedEquiv A ℳ 𝒩` : degree-preserving `A`-linear isomorphisms (notation
  `ℳ ≃ᵍ[A] 𝒩`), with `refl`, `symm`, `trans`, `ofLinearMaps`, `shift`, `prodCongr`, `prodComm`.
* `SetLike.GradedSMul` instances for `shift` and `prod` (and for `submodule`), so these are again
  graded `A`-modules.

## Design notes

* All `Decomposition` instances for derived gradings are produced from `DirectSum.IsInternal`
  proofs via `DirectSum.IsInternal.chooseDecomposition`. Since `Decomposition ℳ` is a
  subsingleton, the choice is harmless. For `shift` and `prod` they are instances; for
  `submodule` and `idem` they depend on a homogeneity hypothesis and are provided as definitions
  (`submoduleDecomposition`, `idemDecomposition`) to be installed locally.
* Degree-preserving maps are expressed as a `Prop` (`PreservesGrading`) on ordinary linear maps,
  so they work uniformly for `k`-linear and `A`-linear maps.
-/

namespace Categorification.Graded

open DirectSum SetLike Function

section Decompositions

variable {ι k M N : Type*} [CommRing k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-! ### Pulling back a grading along an injective map -/

/-- The grading `d ↦ (ℳ d).comap f` pulled back along a linear map `f : N → M`. -/
def comap (ℳ : ι → Submodule k M) (f : N →ₗ[k] M) : ι → Submodule k N :=
  fun d => (ℳ d).comap f

@[simp] theorem mem_comap {ℳ : ι → Submodule k M} {f : N →ₗ[k] M} {d : ι} {x : N} :
    x ∈ comap ℳ f d ↔ f x ∈ ℳ d := Iff.rfl

/-- The grading shift `M{a}` of KL I: `M` with the grading shifted **up** by `a`,
`(M{a})_d = M_{d - a}`. -/
def shift [Sub ι] (ℳ : ι → Submodule k M) (a : ι) : ι → Submodule k M := fun d => ℳ (d - a)

theorem shift_apply [Sub ι] (ℳ : ι → Submodule k M) (a d : ι) :
    shift ℳ a d = ℳ (d - a) := rfl

@[simp] theorem mem_shift [Sub ι] {ℳ : ι → Submodule k M} {a d : ι} {x : M} :
    x ∈ shift ℳ a d ↔ x ∈ ℳ (d - a) := Iff.rfl

theorem mem_shift_add [AddGroup ι] {ℳ : ι → Submodule k M} {a d : ι} {x : M} :
    x ∈ shift ℳ a (d + a) ↔ x ∈ ℳ d := by simp

theorem shift_zero [AddGroup ι] (ℳ : ι → Submodule k M) : shift ℳ 0 = ℳ := by
  funext d; simp [shift_apply]

theorem shift_shift [AddCommGroup ι] (ℳ : ι → Submodule k M) (a b : ι) :
    shift (shift ℳ a) b = shift ℳ (a + b) := by
  funext d; simp [shift_apply, sub_sub, add_comm b]

/-- The grading of `M × N` by `d ↦ (ℳ d).prod (𝒩 d)`. -/
def prod (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) : ι → Submodule k (M × N) :=
  fun d => (ℳ d).prod (𝒩 d)

@[simp] theorem mem_prod {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N} {d : ι} {x : M × N} :
    x ∈ prod ℳ 𝒩 d ↔ x.1 ∈ ℳ d ∧ x.2 ∈ 𝒩 d := Iff.rfl

theorem shift_prod [Sub ι] (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) (a : ι) :
    shift (prod ℳ 𝒩) a = prod (shift ℳ a) (shift 𝒩 a) := rfl

variable [DecidableEq ι]

/-- A grading pulled back along an injective map whose range is homogeneous is internal. -/
theorem isInternal_comap (ℳ : ι → Submodule k M) [Decomposition ℳ] (f : N →ₗ[k] M)
    (hf : Injective f) (hrange : ∀ x d, (decompose ℳ (f x) d : M) ∈ LinearMap.range f) :
    IsInternal (comap ℳ f) := by
  have hind := (Decomposition.isInternal ℳ).submodule_iSupIndep
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · intro d
    have h := hind d
    rw [disjoint_iff] at h ⊢
    refine le_bot_iff.1 ?_
    calc comap ℳ f d ⊓ ⨆ (j) (_ : j ≠ d), comap ℳ f j
        ≤ (ℳ d ⊓ ⨆ (j) (_ : j ≠ d), ℳ j).comap f := by
          rw [Submodule.comap_inf]
          exact inf_le_inf_left _ (iSup₂_le fun j hj => Submodule.comap_mono
            (le_iSup₂ (f := fun j (_ : j ≠ d) => ℳ j) j hj))
      _ = ⊥ := by rw [h, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hf]
  · classical
    rw [eq_top_iff]
    intro x _
    choose y hy using hrange x
    have hx : x = ∑ d ∈ (decompose ℳ (f x)).support, y d :=
      hf (by rw [map_sum]; simp only [hy]; exact (sum_support_decompose ℳ (f x)).symm)
    rw [hx]
    exact Submodule.sum_mem _ fun d _ =>
      Submodule.mem_iSup_of_mem d (by rw [mem_comap, hy]; exact (decompose ℳ (f x) d).2)

/-! ### Grading shifts -/

section Shift

variable [AddCommGroup ι]

theorem isInternal_shift (ℳ : ι → Submodule k M) [Decomposition ℳ] (a : ι) :
    IsInternal (shift ℳ a) := by
  have h := Decomposition.isInternal ℳ
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · exact h.submodule_iSupIndep.comp (sub_left_injective (b := a))
  · rw [← h.submodule_iSup_eq_top]
    exact (Equiv.subRight a).iSup_comp (g := ℳ)

noncomputable instance (ℳ : ι → Submodule k M) [Decomposition ℳ] (a : ι) :
    Decomposition (shift ℳ a) :=
  (isInternal_shift ℳ a).chooseDecomposition

theorem decompose_shift (ℳ : ι → Submodule k M) [Decomposition ℳ] (a : ι) (x : M) (d : ι) :
    (decompose (shift ℳ a) x (d + a) : M) = decompose ℳ x d := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => rw [decompose_zero, decompose_zero]; rfl
  | add x y hx hy =>
    rw [decompose_add, decompose_add, add_apply, add_apply, Submodule.coe_add,
      Submodule.coe_add, hx, hy]
  | @homogeneous j x =>
    have hx' : (x : M) ∈ shift ℳ a (j + a) := by simp
    by_cases h : j = d
    · subst h
      rw [decompose_of_mem_same _ x.2, decompose_of_mem_same _ hx']
    · rw [decompose_of_mem_ne _ x.2 h, decompose_of_mem_ne _ hx' (by simpa using h)]

end Shift

/-! ### Direct sums -/

section Prod

theorem isInternal_prod (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) [Decomposition ℳ]
    [Decomposition 𝒩] : IsInternal (prod ℳ 𝒩) := by
  have hM := Decomposition.isInternal ℳ
  have hN := Decomposition.isInternal 𝒩
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · intro d
    have h1 := hM.submodule_iSupIndep d
    have h2 := hN.submodule_iSupIndep d
    rw [disjoint_iff] at h1 h2 ⊢
    refine le_bot_iff.1 ?_
    calc prod ℳ 𝒩 d ⊓ ⨆ (j) (_ : j ≠ d), prod ℳ 𝒩 j
        ≤ (ℳ d).prod (𝒩 d) ⊓ (⨆ (j) (_ : j ≠ d), ℳ j).prod (⨆ (j) (_ : j ≠ d), 𝒩 j) :=
          inf_le_inf_left _ (iSup₂_le fun j hj => Submodule.prod_mono
            (le_iSup₂ (f := fun j (_ : j ≠ d) => ℳ j) j hj)
            (le_iSup₂ (f := fun j (_ : j ≠ d) => 𝒩 j) j hj))
      _ = ⊥ := by rw [Submodule.prod_inf_prod, h1, h2, Submodule.prod_bot]
  · rw [eq_top_iff]
    rintro ⟨m, n⟩ -
    have hm : m ∈ ⨆ d, ℳ d := hM.submodule_iSup_eq_top ▸ Submodule.mem_top
    have hn : n ∈ ⨆ d, 𝒩 d := hN.submodule_iSup_eq_top ▸ Submodule.mem_top
    have h1 : (m, (0 : N)) ∈ ⨆ d, prod ℳ 𝒩 d := by
      have : (m, (0 : N)) ∈ (⨆ d, ℳ d).map (LinearMap.inl k M N) := ⟨m, hm, rfl⟩
      rw [Submodule.map_iSup] at this
      exact (iSup_mono fun d => Submodule.map_le_iff_le_comap.2 fun x hx => by
        simp [hx]) this
    have h2 : ((0 : M), n) ∈ ⨆ d, prod ℳ 𝒩 d := by
      have : ((0 : M), n) ∈ (⨆ d, 𝒩 d).map (LinearMap.inr k M N) := ⟨n, hn, rfl⟩
      rw [Submodule.map_iSup] at this
      exact (iSup_mono fun d => Submodule.map_le_iff_le_comap.2 fun x hx => by
        simp [hx]) this
    simpa using add_mem h1 h2

noncomputable instance (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) [Decomposition ℳ]
    [Decomposition 𝒩] : Decomposition (prod ℳ 𝒩) :=
  (isInternal_prod ℳ 𝒩).chooseDecomposition

end Prod

end Decompositions

/-! ### Degree-preserving maps -/

section Maps

variable {ι R M N P : Type*} {k : Type*} [CommRing k] [Semiring R]
  [AddCommGroup M] [Module k M] [Module R M] [AddCommGroup N] [Module k N] [Module R N]
  [AddCommGroup P] [Module k P] [Module R P]

/-- A linear map is *degree-preserving* (a morphism of graded modules in KL I's sense) if it
maps `ℳ d` into `𝒩 d` for every `d`. -/
def PreservesGrading (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) (f : M →ₗ[R] N) : Prop :=
  ∀ ⦃d : ι⦄ ⦃x : M⦄, x ∈ ℳ d → f x ∈ 𝒩 d

theorem PreservesGrading.comp {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N}
    {𝒬 : ι → Submodule k P} {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hg : PreservesGrading 𝒩 𝒬 g)
    (hf : PreservesGrading ℳ 𝒩 f) : PreservesGrading ℳ 𝒬 (g.comp f) :=
  fun _ _ hx => hg (hf hx)

variable [DecidableEq ι]

/-- Degree-preserving maps commute with taking homogeneous components. -/
theorem decompose_map {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N} [Decomposition ℳ]
    [Decomposition 𝒩] {f : M →ₗ[R] N} (hf : PreservesGrading ℳ 𝒩 f) (x : M) (d : ι) :
    (decompose 𝒩 (f x) d : N) = f (decompose ℳ x d) := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simp [decompose_add, hx, hy]
  | @homogeneous j x =>
    by_cases h : j = d
    · subst h
      rw [decompose_of_mem_same _ x.2, decompose_of_mem_same _ (hf x.2)]
    · rw [decompose_of_mem_ne _ x.2 h, decompose_of_mem_ne _ (hf x.2) h, map_zero]

/-- The range of a degree-preserving map is homogeneous. -/
theorem decompose_mem_range {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N} [Decomposition ℳ]
    [Decomposition 𝒩] {f : M →ₗ[R] N} (hf : PreservesGrading ℳ 𝒩 f) (x : M) (d : ι) :
    (decompose 𝒩 (f x) d : N) ∈ LinearMap.range f :=
  ⟨_, (decompose_map hf x d).symm⟩

end Maps

/-! ### Degree-preserving isomorphisms -/

section Equiv

variable {ι : Type*} (A : Type*) {k M N P : Type*} [CommRing k] [Semiring A]
  [AddCommGroup M] [Module k M] [Module A M] [AddCommGroup N] [Module k N] [Module A N]
  [AddCommGroup P] [Module k P] [Module A P]

/-- A degree-preserving `A`-linear isomorphism between graded modules (an isomorphism in KL I's
category `R(ν)-gmod`). -/
structure GradedEquiv (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) extends M ≃ₗ[A] N where
  map_mem' : ∀ ⦃d : ι⦄ ⦃x : M⦄, x ∈ ℳ d → toLinearEquiv x ∈ 𝒩 d
  symm_map_mem' : ∀ ⦃d : ι⦄ ⦃y : N⦄, y ∈ 𝒩 d → toLinearEquiv.symm y ∈ ℳ d

@[inherit_doc] notation:50 ℳ " ≃ᵍ[" A "] " 𝒩 => GradedEquiv A ℳ 𝒩

namespace GradedEquiv

variable {A} {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N} {𝒬 : ι → Submodule k P}

instance : EquivLike (ℳ ≃ᵍ[A] 𝒩) M N where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g h _ := by
    have : f.toLinearEquiv = g.toLinearEquiv := LinearEquiv.coe_injective h
    cases f; cases g; congr

theorem map_mem (f : ℳ ≃ᵍ[A] 𝒩) {d : ι} {x : M} (hx : x ∈ ℳ d) : f x ∈ 𝒩 d := f.map_mem' hx

@[simp] theorem coe_toLinearEquiv (f : ℳ ≃ᵍ[A] 𝒩) : ⇑f.toLinearEquiv = f := rfl

theorem preservesGrading (f : ℳ ≃ᵍ[A] 𝒩) :
    PreservesGrading ℳ 𝒩 f.toLinearEquiv.toLinearMap := f.map_mem'

/-- The identity isomorphism. -/
@[refl] def refl (ℳ : ι → Submodule k M) : ℳ ≃ᵍ[A] ℳ where
  toLinearEquiv := LinearEquiv.refl A M
  map_mem' _ _ h := h
  symm_map_mem' _ _ h := h

/-- The inverse isomorphism. -/
@[symm] def symm (f : ℳ ≃ᵍ[A] 𝒩) : 𝒩 ≃ᵍ[A] ℳ where
  toLinearEquiv := f.toLinearEquiv.symm
  map_mem' := f.symm_map_mem'
  symm_map_mem' := f.map_mem'

/-- Composition of isomorphisms. -/
@[trans] def trans (f : ℳ ≃ᵍ[A] 𝒩) (g : 𝒩 ≃ᵍ[A] 𝒬) : ℳ ≃ᵍ[A] 𝒬 where
  toLinearEquiv := f.toLinearEquiv.trans g.toLinearEquiv
  map_mem' _ _ h := g.map_mem' (f.map_mem' h)
  symm_map_mem' _ _ h := f.symm_map_mem' (g.symm_map_mem' h)

/-- The identity map is an isomorphism between two gradings with the same homogeneous pieces. -/
def ofEq {ℳ ℳ' : ι → Submodule k M} (h : ℳ = ℳ') : ℳ ≃ᵍ[A] ℳ' where
  toLinearEquiv := LinearEquiv.refl A M
  map_mem' _ _ hx := h ▸ hx
  symm_map_mem' _ _ hx := h ▸ hx

/-- Build a graded isomorphism from mutually inverse degree-preserving linear maps. -/
def ofLinearMaps (f : M →ₗ[A] N) (g : N →ₗ[A] M) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) (hf : PreservesGrading ℳ 𝒩 f) (hg : PreservesGrading 𝒩 ℳ g) :
    ℳ ≃ᵍ[A] 𝒩 where
  toLinearEquiv := LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf)
  map_mem' := hf
  symm_map_mem' := hg

section ShiftProd

variable [AddCommGroup ι]

/-- Shifting preserves graded isomorphisms. -/
def shift (f : ℳ ≃ᵍ[A] 𝒩) (a : ι) : Graded.shift ℳ a ≃ᵍ[A] Graded.shift 𝒩 a where
  toLinearEquiv := f.toLinearEquiv
  map_mem' _ _ h := f.map_mem' h
  symm_map_mem' _ _ h := f.symm_map_mem' h

/-- Direct sums of graded isomorphisms. -/
def prodCongr {M' N' : Type*} [AddCommGroup M'] [Module k M'] [Module A M'] [AddCommGroup N']
    [Module k N'] [Module A N'] {ℳ' : ι → Submodule k M'} {𝒩' : ι → Submodule k N'}
    (f : ℳ ≃ᵍ[A] 𝒩) (g : ℳ' ≃ᵍ[A] 𝒩') : prod ℳ ℳ' ≃ᵍ[A] prod 𝒩 𝒩' where
  toLinearEquiv := f.toLinearEquiv.prodCongr g.toLinearEquiv
  map_mem' _ _ h := ⟨f.map_mem' h.1, g.map_mem' h.2⟩
  symm_map_mem' _ _ h := ⟨f.symm_map_mem' h.1, g.symm_map_mem' h.2⟩

/-- Direct sums are commutative. -/
def prodComm (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) :
    prod ℳ 𝒩 ≃ᵍ[A] prod 𝒩 ℳ where
  toLinearEquiv := LinearEquiv.prodComm A M N
  map_mem' _ _ h := ⟨h.2, h.1⟩
  symm_map_mem' _ _ h := ⟨h.2, h.1⟩

end ShiftProd

end GradedEquiv

end Equiv

/-! ### Compatibility with the action of a graded algebra -/

section GradedSMul

variable {ι k A M N : Type*} [CommRing k] [Semiring A] [Algebra k A] [AddCommGroup M]
  [Module k M] [Module A M] [AddCommGroup N] [Module k N] [Module A N]
  (𝒜 : ι → Submodule k A) (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N)

instance [AddCommGroup ι] [SetLike.GradedSMul 𝒜 ℳ] (a : ι) :
    SetLike.GradedSMul 𝒜 (shift ℳ a) where
  smul_mem i j _ _ hr hx := by
    have := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) hr hx
    simpa [vadd_eq_add, add_sub_assoc] using this

instance [Add ι] [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] :
    SetLike.GradedSMul 𝒜 (prod ℳ 𝒩) where
  smul_mem _ _ _ _ hr hx :=
    ⟨SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) hr hx.1,
      SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒩) hr hx.2⟩

end GradedSMul

/-! ### Graded submodules and graded subspaces -/

section Sub

variable {ι : Type*} {k A M : Type*} [CommRing k] [Ring A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (ℳ : ι → Submodule k M)

/-- The grading of a submodule `p ⊆ M`, `p_d = p ∩ M_d`. It is a grading (`Decomposition`)
when `p` is homogeneous. -/
def submodule (p : Submodule A M) : ι → Submodule k p :=
  comap ℳ (p.subtype.restrictScalars k)

@[simp] theorem mem_submodule {p : Submodule A M} {d : ι} {x : p} :
    x ∈ submodule ℳ p d ↔ (x : M) ∈ ℳ d := Iff.rfl

instance [AddMonoid ι] (𝒜 : ι → Submodule k A) [SetLike.GradedSMul 𝒜 ℳ] (p : Submodule A M) :
    SetLike.GradedSMul 𝒜 (submodule ℳ p) where
  smul_mem _ _ _ _ ha hx := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hx

variable (k M) in
/-- The subspace `e M = {m | e • m = m}` cut out by an element `e : A` (for an idempotent `e`
this is the image of `e`). It is a `k`-subspace; it is not an `A`-submodule in general. -/
def idemSubspace (e : A) : Submodule k M where
  carrier := {m | e • m = m}
  add_mem' {a b} ha hb := by simp_all [smul_add]
  zero_mem' := by simp
  smul_mem' c m hm := by simp_all [smul_comm e c m]

@[simp] theorem mem_idemSubspace {e : A} {m : M} : m ∈ idemSubspace k M e ↔ e • m = m := Iff.rfl

theorem smul_mem_idemSubspace {e : A} (he : IsIdempotentElem e) (m : M) :
    e • m ∈ idemSubspace k M e := by
  rw [mem_idemSubspace, ← mul_smul, he.eq]

/-- The graded vector space `e M`, `(e M)_d = e M ∩ M_d`. -/
def idem (e : A) : ι → Submodule k (idemSubspace k M e) :=
  comap ℳ (idemSubspace k M e).subtype

@[simp] theorem mem_idem {e : A} {d : ι} {x : idemSubspace k M e} :
    x ∈ idem ℳ e d ↔ (x : M) ∈ ℳ d := Iff.rfl

variable [DecidableEq ι] [Decomposition ℳ]

theorem isInternal_submodule {p : Submodule A M} (hp : p.IsHomogeneous ℳ) :
    IsInternal (submodule ℳ p) :=
  isInternal_comap ℳ _ Subtype.val_injective fun x d => ⟨⟨_, hp d x.2⟩, rfl⟩

/-- The graded structure of a homogeneous submodule. -/
noncomputable def submoduleDecomposition {p : Submodule A M} (hp : p.IsHomogeneous ℳ) :
    Decomposition (submodule ℳ p) :=
  (isInternal_submodule ℳ hp).chooseDecomposition

variable [AddMonoid ι] {𝒜 : ι → Submodule k A} [SetLike.GradedSMul 𝒜 ℳ]

omit [IsScalarTower k A M] in
/-- Degree-zero elements commute with taking homogeneous components. -/
theorem decompose_smul_of_mem_zero {a : A} (ha : a ∈ 𝒜 0) (x : M) (d : ι) :
    (decompose ℳ (a • x) d : M) = a • (decompose ℳ x d : M) := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simp [smul_add, decompose_add, hx, hy]
  | @homogeneous j x =>
    have hax : a • (x : M) ∈ ℳ j := by
      simpa using SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha x.2
    by_cases h : j = d
    · subst h
      rw [decompose_of_mem_same _ x.2, decompose_of_mem_same _ hax]
    · rw [decompose_of_mem_ne _ x.2 h, decompose_of_mem_ne _ hax h, smul_zero]

theorem isInternal_idem {e : A} (he : e ∈ 𝒜 0) : IsInternal (idem ℳ e) :=
  isInternal_comap ℳ _ Subtype.val_injective fun x d =>
    ⟨⟨_, by
      simp only [Submodule.coe_subtype, mem_idemSubspace]
      rw [← decompose_smul_of_mem_zero ℳ he, x.2]⟩, rfl⟩

/-- The graded structure of `e M` for `e` of degree zero. -/
noncomputable def idemDecomposition {e : A} (he : e ∈ 𝒜 0) : Decomposition (idem ℳ e) :=
  (isInternal_idem ℳ he).chooseDecomposition

end Sub

end Categorification.Graded
