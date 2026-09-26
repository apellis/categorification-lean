/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.HomForm
import Categorification.Algebra.Graded.Simple
import Categorification.Algebra.Graded.Quotient

/-!
# Graded projectivity, local endomorphism algebras and graded simple quotients

Let `A` be a `ℤ`-graded algebra over a field `k`. This file contains the graded representation
theory behind the Krull–Schmidt statements of Khovanov–Lauda I (arXiv:0803.4121v2, §2.5, TeX
lines 1513–1556): for `R(ν)` "the category `R(ν)-mod` is Krull–Schmidt", "each simple `S_b` has
a projective cover `P_b`", and "`K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module with basis `[P_b]`".

## Main definitions and results

* `Graded.degZero ℳ 𝒩 f` : the degree-zero component of an `A`-linear map `f : M → N` between
  graded modules; it is again `A`-linear (`degZero_apply_of_mem`, `preservesGrading_degZero`,
  `degZero_eq_self`, `comp_degZero`).
* `Graded.exists_lift_of_projective` : **graded projectivity**: a finitely generated graded
  module `P` that is projective as an ungraded module has the lifting property in the category
  of graded modules and degree-preserving maps.
* `Graded.endZero A ℳ` : the `k`-subalgebra of degree-preserving endomorphisms; it is
  finite-dimensional for a finitely generated `M` when `A` has a graded dimension
  (`finiteDimensional_endZero`).
* `isNilpotent_or_isUnit_of_idempotent` : in a finite-dimensional `k`-algebra with no
  idempotents other than `0` and `1`, every element is nilpotent or a unit (Fitting).
* `Graded.quotGradingA ℳ N` : the grading of `M ⧸ N` for a homogeneous submodule `N`;
  `exists_isGradedSimple_quotient` : a nonzero finitely generated graded module has a graded
  simple quotient.
* `Graded.eq_zero_of_gradedEquiv_shift_of_hasGdim` : a nonzero graded module with a graded
  dimension is not isomorphic to a nontrivial shift of itself.
* `GProj.IsIndec` : indecomposable objects of `A-pmod` (no degree-preserving idempotent
  endomorphisms other than `0`, `1`); `GProj.IsIndec.bijective_or_isNilpotent` (their degree-zero
  endomorphism algebra is local), and `GProj.IsIndec.nonempty_iso` : **uniqueness of projective
  covers**: two indecomposable graded projectives with nonzero degree-preserving maps to the same
  graded simple module are isomorphic.
* `GProj.IsIndec.ker_le_ker`, `GProj.IsIndec.nonempty_gradedEquiv` : **uniqueness of the top**:
  the kernels of all nonzero degree-preserving maps from an indecomposable `Q` to graded simple
  modules coincide (this kernel is the graded radical, the unique maximal homogeneous
  submodule), so all graded simple quotients of `Q` are isomorphic.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function

/-! ### The degree-zero component of a linear map -/

section DegZero

/-- Two linear maps out of a graded module agreeing on homogeneous elements are equal. -/
theorem linearMap_ext_of_homogeneous {k R M N : Type*} [CommRing k] [Semiring R]
    [AddCommGroup M] [Module k M] [Module R M] [AddCommGroup N] [Module R N]
    {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
    {f g : M →ₗ[R] N} (h : ∀ j, ∀ x ∈ ℳ j, f x = g x) : f = g := by
  ext x
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | @homogeneous j x => exact h j x x.2

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]
  {M N P : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩]
  (𝒬 : ℤ → Submodule k P) [Decomposition 𝒬]

/-- The `k`-linear degree-zero component of a `k`-linear map: `x ∈ M_d ↦ (f x)_d`. -/
def degZeroK (f : M →ₗ[k] N) : M →ₗ[k] N :=
  (DirectSum.toModule k ℤ N fun d =>
    (𝒩 d).subtype ∘ₗ (DirectSum.component k ℤ (fun i => 𝒩 i) d) ∘ₗ
      (decomposeLinearEquiv 𝒩).toLinearMap ∘ₗ f ∘ₗ (ℳ d).subtype) ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap

theorem degZeroK_apply_of_mem (f : M →ₗ[k] N) {x : M} {j : ℤ} (hx : x ∈ ℳ j) :
    degZeroK ℳ 𝒩 f x = decompose 𝒩 (f x) j := by
  simp only [degZeroK, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    decomposeLinearEquiv_apply, decompose_of_mem ℳ hx]
  erw [DirectSum.toModule_lof]
  rfl

variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]

/-- The **degree-zero component** of an `A`-linear map between graded modules,
`x ∈ M_d ↦ (f x)_d`. It is again `A`-linear. -/
def degZero (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun := degZeroK ℳ 𝒩 (f.restrictScalars k)
  map_add' := map_add _
  map_smul' a x := by
    induction x using Decomposition.inductionOn ℳ with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
    | @homogeneous j x =>
      induction a using Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add a b ha hb =>
        simp only [RingHom.id_apply] at ha hb ⊢
        rw [add_smul, map_add, ha, hb, add_smul]
      | @homogeneous i a =>
        have hax : (a : A) • (x : M) ∈ ℳ (i + j) := by
          simpa [vadd_eq_add] using SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) a.2 x.2
        rw [RingHom.id_apply, degZeroK_apply_of_mem ℳ 𝒩 _ hax,
          degZeroK_apply_of_mem ℳ 𝒩 _ x.2, LinearMap.restrictScalars_apply,
          LinearMap.restrictScalars_apply, map_smul,
          decompose_smul_of_mem_left 𝒜 𝒩 a.2 (f x) (i + j), add_sub_cancel_left]

variable {ℳ 𝒩 𝒬}

theorem degZero_apply_of_mem (f : M →ₗ[A] N) {x : M} {j : ℤ} (hx : x ∈ ℳ j) :
    degZero 𝒜 ℳ 𝒩 f x = decompose 𝒩 (f x) j :=
  degZeroK_apply_of_mem ℳ 𝒩 _ hx

theorem preservesGrading_degZero (f : M →ₗ[A] N) : PreservesGrading ℳ 𝒩 (degZero 𝒜 ℳ 𝒩 f) :=
  fun _ _ hx => by rw [degZero_apply_of_mem 𝒜 f hx]; exact (decompose 𝒩 _ _).2

theorem degZero_eq_self {f : M →ₗ[A] N} (hf : PreservesGrading ℳ 𝒩 f) :
    degZero 𝒜 ℳ 𝒩 f = f :=
  linearMap_ext_of_homogeneous (ℳ := ℳ) fun _ _ hx => by
    rw [degZero_apply_of_mem 𝒜 f hx, decompose_of_mem_same _ (hf hx)]

variable [SetLike.GradedSMul 𝒜 𝒬]

theorem comp_degZero {p : N →ₗ[A] P} (hp : PreservesGrading 𝒩 𝒬 p) (f : M →ₗ[A] N) :
    p ∘ₗ degZero 𝒜 ℳ 𝒩 f = degZero 𝒜 ℳ 𝒬 (p ∘ₗ f) :=
  linearMap_ext_of_homogeneous (ℳ := ℳ) fun _ _ hx => by
    rw [LinearMap.comp_apply, degZero_apply_of_mem 𝒜 _ hx, degZero_apply_of_mem 𝒜 _ hx,
      LinearMap.comp_apply, decompose_map hp]

include 𝒜 in
/-- **Graded projectivity.** If `M` is projective as an ungraded `A`-module, then every
degree-preserving map `h : M → P` lifts along a degree-preserving surjection `p : N → P` to a
degree-preserving map `g : M → N`. -/
theorem exists_lift_of_projective [Module.Projective A M] {p : N →ₗ[A] P}
    (hp : PreservesGrading 𝒩 𝒬 p) (hsurj : Surjective p) {h : M →ₗ[A] P}
    (hh : PreservesGrading ℳ 𝒬 h) :
    ∃ g : M →ₗ[A] N, PreservesGrading ℳ 𝒩 g ∧ p ∘ₗ g = h := by
  obtain ⟨g₀, hg₀⟩ := Module.projective_lifting_property p h hsurj
  exact ⟨degZero 𝒜 ℳ 𝒩 g₀, preservesGrading_degZero (ℳ := ℳ) (𝒩 := 𝒩) 𝒜 g₀, by
    rw [comp_degZero (ℳ := ℳ) 𝒜 hp, hg₀, degZero_eq_self 𝒜 hh]⟩

end DegZero

/-! ### Local finite-dimensional algebras (Fitting's lemma) -/

section Fitting

variable (k : Type*) {E : Type*} [Field k] [Ring E] [Algebra k E] [FiniteDimensional k E]

include k

/-- In a finite-dimensional algebra, a left-invertible element is a unit. -/
theorem isUnit_of_mul_eq_one_left {g f : E} (h : g * f = 1) : IsUnit f := by
  have hinj : Injective (LinearMap.mulLeft k f) := fun x y hxy => by
    have := congrArg (g * ·) hxy
    simpa [← mul_assoc, h] using this
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  have hy' : f * y = 1 := hy
  have hgy : g = y := by rw [← mul_one g, ← hy', ← mul_assoc, h, one_mul]
  exact ⟨⟨f, g, by rw [hgy, hy'], h⟩, rfl⟩

/-- **Fitting's lemma for algebras.** In a finite-dimensional `k`-algebra whose only idempotents
are `0` and `1`, every element is nilpotent or a unit. -/
theorem isNilpotent_or_isUnit_of_idempotent
    (h : ∀ e : E, IsIdempotentElem e → e = 0 ∨ e = 1) (f : E) : IsNilpotent f ∨ IsUnit f := by
  obtain ⟨n, hn, hn1⟩ := ((LinearMap.mulRight k f).eventually_isCompl_ker_pow_range_pow.and
    (Filter.eventually_ge_atTop 1)).exists
  rw [LinearMap.pow_mulRight] at hn
  set K := LinearMap.ker (LinearMap.mulRight k (f ^ n))
  set I := LinearMap.range (LinearMap.mulRight k (f ^ n))
  have hK : ∀ y x, x ∈ K → y * x ∈ K := by
    intro y x hx
    simp only [K, LinearMap.mem_ker, LinearMap.mulRight_apply] at hx ⊢
    rw [mul_assoc, hx, mul_zero]
  have hI : ∀ y x, x ∈ I → y * x ∈ I := by
    rintro y _ ⟨z, rfl⟩
    exact ⟨y * z, by simp [mul_assoc]⟩
  have h1 : (1 : E) ∈ K ⊔ I := by rw [hn.sup_eq_top]; trivial
  obtain ⟨e₁, he₁, e₂, he₂, hsum⟩ := Submodule.mem_sup.1 h1
  have hid : IsIdempotentElem e₁ := by
    have hdis := Submodule.disjoint_def.1 hn.disjoint
    have hK' : e₁ * e₁ - e₁ ∈ K := sub_mem (hK _ _ he₁) he₁
    have heq : e₁ * e₁ - e₁ = -(e₁ * e₂) := by
      have : e₁ * (e₁ + e₂) = e₁ := by rw [hsum, mul_one]
      rw [mul_add] at this
      rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, this, sub_self]
    have hI' : e₁ * e₁ - e₁ ∈ I := by rw [heq]; exact neg_mem (hI _ _ he₂)
    exact sub_eq_zero.1 (hdis _ hK' hI')
  rcases h e₁ hid with h0 | h1'
  · right
    rw [h0, zero_add] at hsum
    obtain ⟨z, hz⟩ : (1 : E) ∈ I := hsum ▸ he₂
    simp only [LinearMap.mulRight_apply] at hz
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
    refine isUnit_of_mul_eq_one_left k (g := z * f ^ m) ?_
    rw [mul_assoc, ← pow_succ, hz]
  · left
    refine ⟨n, ?_⟩
    have : (1 : E) ∈ K := h1' ▸ he₁
    simpa [K] using this

end Fitting

/-! ### Degree-preserving endomorphisms -/

section EndZero

variable {k : Type*} [Field k] (A : Type*) [Ring A] [Algebra k A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The degree-preserving endomorphisms `END(M)_0` of a graded module, a `k`-subalgebra of
`End_A(M)`. -/
def endZero (ℳ : ℤ → Submodule k M) : Subalgebra k (Module.End A M) where
  carrier := {f | PreservesGrading ℳ ℳ f}
  mul_mem' {_ _} hf hg := fun _ _ hx => hf (hg hx)
  one_mem' := fun _ _ hx => hx
  add_mem' {_ _} hf hg := fun _ _ hx => add_mem (hf hx) (hg hx)
  zero_mem' := fun _ _ _ => zero_mem _
  algebraMap_mem' c := fun _ x hx => by
    show (algebraMap k (Module.End A M) c) x ∈ _
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c hx

variable {A}

@[simp] theorem mem_endZero {ℳ : ℤ → Submodule k M} {f : Module.End A M} :
    f ∈ endZero A ℳ ↔ PreservesGrading ℳ ℳ f := Iff.rfl

/-- The degree-preserving endomorphisms are the degree-zero part of `HOM(M, M)`. -/
def endZeroToHomGrade (ℳ : ℤ → Submodule k M) : endZero A ℳ →ₗ[k] homGrade A ℳ ℳ 0 where
  toFun f := ⟨f, fun _ _ hx => by rw [add_zero]; exact f.2 hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem endZeroToHomGrade_injective (ℳ : ℤ → Submodule k M) :
    Injective (endZeroToHomGrade (A := A) ℳ) := fun f g h => by
  have := congrArg Subtype.val h
  exact Subtype.ext this

/-- **`END(M)_0` is finite-dimensional** for a finitely generated graded module over a graded
algebra with a graded dimension. -/
theorem finiteDimensional_endZero (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [HasGdim 𝒜]
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite A M] :
    FiniteDimensional k (endZero A ℳ) := by
  haveI := hasGdim_of_finite 𝒜 ℳ
  haveI := hasGdim_homGrade (A := A) ℳ ℳ
  exact FiniteDimensional.of_injective _ (endZeroToHomGrade_injective ℳ)

end EndZero

/-! ### Quotients by homogeneous submodules and graded simple quotients -/

section Quot

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  (ℳ : ℤ → Submodule k M) (N : Submodule A M)

/-- The grading `(M ⧸ N)_d = image of M_d` of the quotient by an `A`-submodule `N`. It is a
grading when `N` is homogeneous (`isInternal_quotGradingA`). -/
def quotGradingA : ℤ → Submodule k (M ⧸ N) := fun d => (ℳ d).map (N.mkQ.restrictScalars k)

theorem preservesGrading_mkQ : PreservesGrading ℳ (quotGradingA ℳ N) N.mkQ :=
  fun _ _ hx => ⟨_, hx, rfl⟩

instance [SetLike.GradedSMul 𝒜 ℳ] : SetLike.GradedSMul 𝒜 (quotGradingA ℳ N) where
  smul_mem _ _ a _ ha hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨a • x, SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hx, by simp⟩

variable [Decomposition ℳ]

/-- **The quotient of a graded module by a homogeneous submodule is graded.** -/
theorem isInternal_quotGradingA (hN : N.IsHomogeneous ℳ) : IsInternal (quotGradingA ℳ N) := by
  have hint := Decomposition.isInternal ℳ
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro d
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    have hx'' : N.mkQ y ∈ (⨆ (j) (_ : j ≠ d), ℳ j).map (N.mkQ.restrictScalars k) := by
      rw [Submodule.map_iSup]
      simpa only [Submodule.map_iSup] using hx'
    obtain ⟨z, hz, hzy⟩ := hx''
    have hyz : y - z ∈ N := by
      rw [← Submodule.Quotient.eq]
      exact hzy.symm
    have := hN d hyz
    rw [decompose_sub, sub_apply, Submodule.coe_sub, decompose_of_mem_same ℳ hy,
      decompose_eq_zero_of_mem_iSup_ne ℳ hz, sub_zero] at this
    exact (Submodule.Quotient.mk_eq_zero N).2 this
  · show ⨆ d, (ℳ d).map (N.mkQ.restrictScalars k) = ⊤
    rw [← Submodule.map_iSup, hint.submodule_iSup_eq_top, Submodule.map_top,
      LinearMap.range_restrictScalars, Submodule.range_mkQ, Submodule.restrictScalars_top]

/-- The graded structure of `M ⧸ N` for a homogeneous `N`. -/
def quotDecompositionA (hN : N.IsHomogeneous ℳ) : Decomposition (quotGradingA ℳ N) :=
  (isInternal_quotGradingA ℳ N hN).chooseDecomposition

omit [Algebra k A] [IsScalarTower k A M] in
theorem isHomogeneous_bot : (⊥ : Submodule A M).IsHomogeneous ℳ := by
  classical
  intro i m hm
  rw [Submodule.mem_bot] at hm ⊢
  rw [hm, decompose_zero]
  rfl

omit [Algebra k A] [IsScalarTower k A M] in
/-- A nonzero finitely generated graded module has a maximal proper homogeneous submodule. -/
theorem exists_isHomogeneous_maximal [Module.Finite A M] [Nontrivial M] :
    ∃ N : Submodule A M, N.IsHomogeneous ℳ ∧ N ≠ ⊤ ∧
      ∀ N' : Submodule A M, N'.IsHomogeneous ℳ → N ≤ N' → N' = N ∨ N' = ⊤ := by
  have ih : ∀ c ⊆ {N : Submodule A M | N.IsHomogeneous ℳ ∧ N ≠ ⊤}, IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ {N : Submodule A M | N.IsHomogeneous ℳ ∧ N ≠ ⊤}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
    refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro i m hm
      obtain ⟨N, hNc, hmN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hm
      exact le_sSup hNc ((hc hNc).1 i hmN)
    · intro htop
      have hcpt : CompleteLattice.IsCompactElement (⊤ : Submodule A M) :=
        (Submodule.fg_iff_compact _).1 Module.Finite.fg_top
      obtain ⟨N, hNc, hN⟩ :=
        (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ _).1 hcpt c hne hdir htop.ge
      exact (hc hNc).2 (top_le_iff.1 hN)
  obtain ⟨N, -, hN, hmax⟩ := zorn_le_nonempty₀
    {N : Submodule A M | N.IsHomogeneous ℳ ∧ N ≠ ⊤} ih ⊥ ⟨isHomogeneous_bot ℳ, bot_ne_top⟩
  refine ⟨N, hN.1, hN.2, fun N' hN' hle => ?_⟩
  by_cases htop : N' = ⊤
  · exact Or.inr htop
  · exact Or.inl (le_antisymm (hmax ⟨hN', htop⟩ hle) hle)

/-- The quotient by a maximal proper homogeneous submodule is graded simple. -/
theorem isGradedSimple_quot (hN : N.IsHomogeneous ℳ) (hNtop : N ≠ ⊤)
    (hmax : ∀ N' : Submodule A M, N'.IsHomogeneous ℳ → N ≤ N' → N' = N ∨ N' = ⊤) :
    letI := quotDecompositionA ℳ N hN
    IsGradedSimple 𝒜 (quotGradingA ℳ N) := by
  letI := quotDecompositionA ℳ N hN
  refine ⟨Submodule.Quotient.nontrivial_of_lt_top N hNtop.lt_top, fun W hW => ?_⟩
  have hcomap : (W.comap N.mkQ).IsHomogeneous ℳ := fun i x hx => by
    show N.mkQ _ ∈ W
    rw [← decompose_map (preservesGrading_mkQ ℳ N)]
    exact hW i hx
  have hle : N ≤ W.comap N.mkQ := fun x hx => by
    simp [(Submodule.Quotient.mk_eq_zero N).2 hx]
  rcases hmax _ hcomap hle with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    have : x ∈ N := h ▸ (show x ∈ W.comap N.mkQ from hy)
    rw [Submodule.mem_bot]
    exact (Submodule.Quotient.mk_eq_zero N).2 this
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := N.mkQ_surjective y
    have : x ∈ W.comap N.mkQ := h ▸ Submodule.mem_top
    exact this

end Quot

/-! ### Shift rigidity -/

section Rigidity

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module k M]

omit [Algebra k A] in
/-- A nonzero graded module with a graded dimension is not isomorphic to a nontrivial shift of
itself: `M ≅ M{c}` forces `c = 0` (compare the lowest nonzero degrees). -/
theorem eq_zero_of_gradedEquiv_shift_of_hasGdim (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [HasGdim ℳ] [Nontrivial M] {c : ℤ} (e : ℳ ≃ᵍ[A] shift ℳ c) : c = 0 := by
  classical
  have hex : ∃ d, ℳ d ≠ ⊥ := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    by_contra h
    push_neg at h
    apply hm
    rw [← sum_support_decompose ℳ m]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact (Submodule.eq_bot_iff _).1 (h j) _ (decompose ℳ m j).2
  obtain ⟨B, hB⟩ := HasGdim.bddBelow (ℳ := ℳ)
  obtain ⟨d₀, hd₀, hmin⟩ := Int.exists_least_of_bdd ⟨B, fun z hz => hB hz⟩ hex
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd₀
  have h1 : ℳ (d₀ - c) ≠ ⊥ := by
    intro h
    have hev : e v ∈ shift ℳ c d₀ := e.map_mem hv
    rw [shift_apply, h, Submodule.mem_bot] at hev
    exact hv0 (e.toLinearEquiv.injective (hev.trans e.toLinearEquiv.map_zero.symm))
  have h2 : ℳ (d₀ + c) ≠ ⊥ := by
    intro h
    have hv' : v ∈ shift ℳ c (d₀ + c) := by rw [shift_apply, add_sub_cancel_right]; exact hv
    have hev : e.symm v ∈ ℳ (d₀ + c) := e.symm.map_mem hv'
    rw [h, Submodule.mem_bot] at hev
    exact hv0 (e.symm.toLinearEquiv.injective (hev.trans e.symm.toLinearEquiv.map_zero.symm))
  have := hmin _ h1
  have := hmin _ h2
  omega

end Rigidity

/-! ### Indecomposable graded projective modules -/

section Indec

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] [HasGdim 𝒜]

namespace GProj

variable {𝒜}

instance finiteDimensional_endZero (P : GProj 𝒜) : FiniteDimensional k (endZero A P.grading) :=
  Graded.finiteDimensional_endZero 𝒜 P.grading

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
variable (A) in
/-- An object `P` of `A-pmod` is *indecomposable* if it is nonzero and its only degree-preserving
idempotent endomorphisms are `0` and `1` (equivalently, `P` is not a nontrivial direct sum in
`A-pmod`, see `Categorification.Graded.GProj.summand`). -/
structure IsIndec (P : GProj 𝒜) : Prop where
  nontrivial : Nontrivial P.carrier
  eq_zero_or_eq_one : ∀ e ∈ endZero A P.grading, IsIdempotentElem e → e = 0 ∨ e = 1

/-- **The degree-zero endomorphism algebra of an indecomposable is local**: every
degree-preserving endomorphism is bijective or nilpotent. -/
theorem IsIndec.bijective_or_isNilpotent {Q : GProj 𝒜} (hQ : Q.IsIndec A)
    {f : Module.End A Q.carrier} (hf : PreservesGrading Q.grading Q.grading f) :
    Bijective f ∨ IsNilpotent f := by
  have hE : ∀ e : endZero A Q.grading, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he => by
    have he' : IsIdempotentElem (e : Module.End A Q.carrier) := congrArg Subtype.val he
    rcases hQ.eq_zero_or_eq_one e e.2 he' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rcases isNilpotent_or_isUnit_of_idempotent k hE ⟨f, hf⟩ with ⟨n, hn⟩ | hu
  · right
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · left
    exact (Module.End.isUnit_iff _).1 (hu.map (endZero A Q.grading).val)

/-- If `φ ∘ u = φ ≠ 0` for a degree-preserving endomorphism `u` of an indecomposable, then `u`
is bijective. -/
theorem IsIndec.bijective_of_comp_eq {Q : GProj 𝒜} (hQ : Q.IsIndec A) {S : Type*}
    [AddCommGroup S] [Module A S] {φ : Q.carrier →ₗ[A] S} (hφ0 : φ ≠ 0) {u : Module.End A Q.carrier}
    (hu : PreservesGrading Q.grading Q.grading u) (hφu : φ ∘ₗ u = φ) : Bijective u := by
  rcases hQ.bijective_or_isNilpotent hu with h | ⟨n, hn⟩
  · exact h
  · exfalso
    apply hφ0
    have hpow : ∀ m : ℕ, ∀ x, φ ((u ^ m) x) = φ x := by
      intro m
      induction m with
      | zero => intro x; rfl
      | succ m ih =>
        intro x
        rw [pow_succ', Module.End.mul_apply, ← LinearMap.comp_apply φ u, hφu, ih]
    ext x
    rw [← hpow n x, hn]
    simp

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- A nonzero degree-preserving map to a graded simple module is surjective. -/
theorem surjective_of_isGradedSimple {M S : Type*} [AddCommGroup M] [Module A M] [Module k M]
    [AddCommGroup S] [Module A S] [Module k S] {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
    {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] (hS : IsGradedSimple 𝒜 𝒮) {f : M →ₗ[A] S}
    (hf : PreservesGrading ℳ 𝒮 f) (hf0 : f ≠ 0) : Surjective f := by
  rcases hS.eq_bot_or_eq_top _ (isHomogeneous_range hf) with h | h
  · exact absurd (LinearMap.range_eq_bot.1 h) hf0
  · exact LinearMap.range_eq_top.1 h

/-- **Uniqueness of projective covers.** Two indecomposable objects of `A-pmod` admitting nonzero
degree-preserving maps to the same graded simple module are isomorphic. -/
theorem IsIndec.nonempty_iso {Q Q' : GProj 𝒜} (hQ : Q.IsIndec A) (hQ' : Q'.IsIndec A)
    {S : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]
    {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] [SetLike.GradedSMul 𝒜 𝒮]
    (hS : IsGradedSimple 𝒜 𝒮) {f : Q.carrier →ₗ[A] S} (hf : PreservesGrading Q.grading 𝒮 f)
    (hf0 : f ≠ 0) {f' : Q'.carrier →ₗ[A] S} (hf' : PreservesGrading Q'.grading 𝒮 f') (hf'0 : f' ≠ 0) :
    Nonempty (Q.Iso Q') := by
  have hfs := surjective_of_isGradedSimple hS hf hf0
  have hf's := surjective_of_isGradedSimple hS hf' hf'0
  obtain ⟨g, hg, hgf⟩ := exists_lift_of_projective 𝒜 hf' hf's hf
  obtain ⟨g', hg', hg'f⟩ := exists_lift_of_projective 𝒜 hf hfs hf'
  have hu := hQ.bijective_of_comp_eq hf0 (u := g' ∘ₗ g) (hg'.comp hg)
    (by rw [← LinearMap.comp_assoc, hg'f, hgf])
  have hv := hQ'.bijective_of_comp_eq hf'0 (u := g ∘ₗ g') (hg.comp hg')
    (by rw [← LinearMap.comp_assoc, hgf, hg'f])
  refine ⟨GradedEquiv.ofBijective hg ⟨fun x y h => hu.1 ?_, fun y => ?_⟩⟩
  · simp only [LinearMap.comp_apply, h]
  · obtain ⟨x, hx⟩ := hv.2 y
    exact ⟨g' x, hx⟩

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- **Every nonzero object of `A-pmod` has a graded simple quotient.** -/
theorem exists_isGradedSimple_quotient (Q : GProj 𝒜) [Nontrivial Q.carrier] :
    ∃ (S : GMod 𝒜) (f : Q.carrier →ₗ[A] S), IsGradedSimple 𝒜 S.grading ∧
      PreservesGrading Q.grading S.grading f ∧ f ≠ 0 ∧ Module.Finite A S := by
  obtain ⟨N, hN, hNtop, hmax⟩ := exists_isHomogeneous_maximal (A := A) Q.grading
  letI := quotDecompositionA Q.grading N hN
  refine ⟨GMod.of (Q.carrier ⧸ N) (quotGradingA Q.grading N), N.mkQ,
    isGradedSimple_quot 𝒜 Q.grading N hN hNtop hmax, preservesGrading_mkQ Q.grading N, ?_,
    inferInstanceAs (Module.Finite A (Q.carrier ⧸ N))⟩
  intro h
  apply hNtop
  rw [eq_top_iff]
  intro x _
  have := LinearMap.congr_fun h x
  exact (Submodule.Quotient.mk_eq_zero N).1 this

omit [Algebra k A] in
/-- The image of a homogeneous submodule under a degree-preserving map is homogeneous. -/
theorem _root_.Categorification.Graded.isHomogeneous_map {M S : Type*} [AddCommGroup M] [Module A M] [Module k M]
    [AddCommGroup S] [Module A S] [Module k S] {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
    {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] {f : M →ₗ[A] S} (hf : PreservesGrading ℳ 𝒮 f)
    {N : Submodule A M} (hN : N.IsHomogeneous ℳ) : (N.map f).IsHomogeneous 𝒮 := by
  rintro i _ ⟨x, hx, rfl⟩
  rw [decompose_map hf]
  exact ⟨_, hN i hx, rfl⟩

/-- **The top of an indecomposable projective is unique**: if an indecomposable `Q` has nonzero
degree-preserving maps `f`, `f'` to graded simple modules, then `ker f ≤ ker f'` (hence
`ker f = ker f'`: `ker f` is the unique maximal homogeneous submodule of `Q`). -/
theorem IsIndec.ker_le_ker {Q : GProj 𝒜} (hQ : Q.IsIndec A)
    {S S' : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]
    {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] [SetLike.GradedSMul 𝒜 𝒮]
    [AddCommGroup S'] [Module A S'] [Module k S'] [IsScalarTower k A S']
    {𝒮' : ℤ → Submodule k S'} [Decomposition 𝒮'] [SetLike.GradedSMul 𝒜 𝒮']
    (hS' : IsGradedSimple 𝒜 𝒮') {f : Q.carrier →ₗ[A] S} (hf : PreservesGrading Q.grading 𝒮 f)
    (hf0 : f ≠ 0) {f' : Q.carrier →ₗ[A] S'} (hf' : PreservesGrading Q.grading 𝒮' f')
    (hf'0 : f' ≠ 0) : LinearMap.ker f ≤ LinearMap.ker f' := by
  by_contra hle
  set K := LinearMap.ker f
  have hK : K.IsHomogeneous Q.grading := isHomogeneous_ker hf
  -- `f'` maps `K` onto `S'`
  have hmap : K.map f' = ⊤ := by
    rcases hS'.eq_bot_or_eq_top _ (isHomogeneous_map hf' hK) with h | h
    · refine absurd (fun x hx => ?_) hle
      have : f' x ∈ K.map f' := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at this
      exact this
    · exact h
  letI := submoduleDecomposition Q.grading hK
  have hι : PreservesGrading (Graded.submodule Q.grading K) 𝒮' (f' ∘ₗ K.subtype) :=
    fun _ _ hx => hf' hx
  have hιs : Surjective (f' ∘ₗ K.subtype) := by
    intro y
    have hy : y ∈ K.map f' := hmap ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨g, hg, hgf⟩ := exists_lift_of_projective 𝒜 hι hιs hf'
  have hu : PreservesGrading Q.grading Q.grading (K.subtype ∘ₗ g) :=
    fun _ _ hx => (show ((g _ : K) : Q.carrier) ∈ _ from hg hx)
  have hbij := hQ.bijective_of_comp_eq hf'0 hu (by rw [← LinearMap.comp_assoc, hgf])
  apply hf0
  ext y
  obtain ⟨x, rfl⟩ := hbij.2 y
  exact (g x).2

/-- **The top of an indecomposable projective is unique up to isomorphism**: graded simple
modules receiving nonzero degree-preserving maps from the same indecomposable object of `A-pmod`
are isomorphic. -/
theorem IsIndec.nonempty_gradedEquiv {Q : GProj 𝒜} (hQ : Q.IsIndec A)
    {S S' : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]
    {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] [SetLike.GradedSMul 𝒜 𝒮]
    [AddCommGroup S'] [Module A S'] [Module k S'] [IsScalarTower k A S']
    {𝒮' : ℤ → Submodule k S'} [Decomposition 𝒮'] [SetLike.GradedSMul 𝒜 𝒮']
    (hS : IsGradedSimple 𝒜 𝒮) (hS' : IsGradedSimple 𝒜 𝒮') {f : Q.carrier →ₗ[A] S}
    (hf : PreservesGrading Q.grading 𝒮 f) (hf0 : f ≠ 0) {f' : Q.carrier →ₗ[A] S'}
    (hf' : PreservesGrading Q.grading 𝒮' f') (hf'0 : f' ≠ 0) : Nonempty (𝒮 ≃ᵍ[A] 𝒮') := by
  have hfs := surjective_of_isGradedSimple hS hf hf0
  have hle := hQ.ker_le_ker hS' hf hf0 hf' hf'0
  set φ : S →ₗ[A] S' :=
    ((LinearMap.ker f).liftQ f' hle).comp (f.quotKerEquivOfSurjective hfs).symm.toLinearMap
  have hφ : ∀ x, φ (f x) = f' x := fun x => by
    have : (f.quotKerEquivOfSurjective hfs).symm (f x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
      Submodule.liftQ_apply]
  have hφg : PreservesGrading 𝒮 𝒮' φ := by
    intro d y hy
    obtain ⟨x, rfl⟩ := hfs y
    rw [← decompose_of_mem_same 𝒮 hy, decompose_map hf, hφ]
    exact hf' (decompose Q.grading x d).2
  have hφ0 : φ ≠ 0 := by
    intro h
    apply hf'0
    ext x
    rw [← hφ, h, LinearMap.zero_apply, LinearMap.zero_apply]
  exact ⟨GradedEquiv.ofBijective hφg (hS.bijective_of_preservesGrading hS' hφg hφ0)⟩

end GProj

end Indec

end Categorification.Graded
