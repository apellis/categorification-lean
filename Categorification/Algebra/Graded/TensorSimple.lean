/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExternalTensor
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.Algebra.Graded.TensorGdim
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple modules over tensor products of algebras

Let `k` be a field and `A`, `B` be `k`-algebras. Khovanov–Lauda I (arXiv:0803.4121v2, §3.1,
TeX lines ~1890–1900) identify `K₀(R(ν) ⊗ R(ν'))` with `K₀(R(ν)) ⊗ K₀(R(ν'))`; this rests on the
classical description of the simple modules of a tensor product of algebras when one factor is
*absolutely irreducible* (`End_A(S) = k`, KL I Corollary 3.19 for `R(ν)`). This file proves the
module-theoretic input.

## Ungraded results

Let `S` be a simple `A`-module with `End_A(S) = k` (every `A`-endomorphism is a scalar) and `M` a
`k`-vector space; `A` acts on `S ⊗_k M` through the first factor.

* `TensorSimple.exists_eq_range_tmulRightA` : every simple `A`-submodule of `S ⊗_k M` is
  `S ⊗ m` for some `m ∈ M`.
* `TensorSimple.mem_range_map_core` (**isotypic submodules**): every `A`-submodule `W` of
  `S ⊗_k M` is contained in (hence equal to) `S ⊗ M₀`, where `M₀ = {m | S ⊗ m ⊆ W}`
  (`TensorSimple.core W`). The proof uses that `S ⊗_k M` is a semisimple `A`-module.
* `TensorSimple.isSimpleModule_extTensor` : **`S ⊠ S'` is a simple `A ⊗ B`-module** if `S` is
  a simple `A`-module with `End_A(S) = k` and `S'` is a simple `B`-module.

## Graded results

For `ℤ`-graded algebras `(A, 𝒜)`, `(B, ℬ)` with graded dimensions (`HasGdim`), whose graded
simple `A`-modules satisfy `End_A(S) = k`:

* `TensorSimple.exists_top_embedding` : a nonzero finite-dimensional graded `A ⊗ B`-module
  contains a graded simple `A`-submodule `S_b{a}` (for the action of `A = A ⊗ 1`).
* `TensorSimple.exists_gradedEquiv_extTensor_top` (**classification of graded simple
  `A ⊗ B`-modules**): every finite-dimensional graded simple `A ⊗ B`-module is isomorphic, by a
  degree-preserving isomorphism, to `(S_b ⊠ S_{b'}){a}` for tops `S_b`, `S_{b'}` of
  indecomposable graded projective `A`- and `B`-modules (`GProj.IndecClass.top`).
-/

noncomputable section

universe u v

namespace Categorification

open scoped TensorProduct

namespace TensorSimple

/-! ### Ungraded: `A`-submodules of `S ⊗ M` -/

section Isotypic

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
  {S : Type*} [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
  {M : Type*} [AddCommGroup M] [Module k M]

variable (k S) in
/-- `s ↦ s ⊗ m`, an `A`-linear map `S → S ⊗_k M` (`A` acting on the first factor). -/
def tmulRightA (m : M) : S →ₗ[A] S ⊗[k] M where
  toFun s := s ⊗ₜ m
  map_add' _ _ := TensorProduct.add_tmul _ _ _
  map_smul' a s := (TensorProduct.smul_tmul' a s m).symm

@[simp] theorem tmulRightA_apply (m : M) (s : S) : tmulRightA k S (A := A) m s = s ⊗ₜ m := rfl

variable (A) in
/-- The `i`-th coordinate `S ⊗_k M → S` for a basis `b` of `M`; it is `A`-linear. -/
def coordA {ι : Type*} [DecidableEq ι] (b : Basis ι k M) (i : ι) : S ⊗[k] M →ₗ[A] S where
  toFun x := TensorProduct.equivFinsuppOfBasisRight b x i
  map_add' x y := by rw [map_add, Finsupp.add_apply]
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [TensorProduct.smul_tmul', RingHom.id_apply,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, smul_comm]
    | add x y hx hy => rw [smul_add, map_add, Finsupp.add_apply, hx, hy, map_add,
        Finsupp.add_apply, smul_add]

theorem coordA_apply {ι : Type*} [DecidableEq ι] (b : Basis ι k M) (i : ι) (x : S ⊗[k] M) :
    coordA A b i x = TensorProduct.equivFinsuppOfBasisRight b x i := rfl

theorem isSemisimpleModule_tensor [IsSimpleModule A S] :
    IsSemisimpleModule A (S ⊗[k] M) := by
  haveI : IsSemisimpleModule A S := inferInstance
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun m : M => LinearMap.range (tmulRightA k S (A := A) m))
    (fun m => IsSemisimpleModule.range _) ?_
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul s m => exact Submodule.mem_iSup_of_mem m ⟨s, rfl⟩
  | add x y hx hy => exact add_mem hx hy

variable (hS : ∀ f : S →ₗ[A] S, ∃ c : k, f = c • LinearMap.id)
include hS

/-- **Simple submodules of `S ⊗ M` are `S ⊗ m`** when `End_A(S) = k`. -/
theorem exists_eq_range_tmulRightA [IsSimpleModule A S] (N : Submodule A (S ⊗[k] M))
    [hN : IsSimpleModule A N] : ∃ m : M, N = LinearMap.range (tmulRightA k S (A := A) m) := by
  classical
  let b := Basis.ofVectorSpace k M
  let E := TensorProduct.equivFinsuppOfBasisRight (M := S) b
  haveI := IsSimpleModule.nontrivial A N
  obtain ⟨x, hx0⟩ := exists_ne (0 : N)
  have hEx : E (x : S ⊗[k] M) ≠ 0 := fun h => hx0 (Subtype.ext (by
    rw [ZeroMemClass.coe_zero]; exact E.injective (h.trans (map_zero E).symm)))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hEx
  let π : N →ₗ[A] S := (coordA A b i).comp N.subtype
  have hπ : π ≠ 0 := fun h => hi (by
    have := LinearMap.congr_fun h x
    simpa [π, coordA_apply] using this)
  let φ := LinearEquiv.ofBijective π (LinearMap.bijective_of_ne_zero hπ)
  let g : S →ₗ[A] S ⊗[k] M := N.subtype.comp φ.symm.toLinearMap
  have hc : ∀ j, ∃ c : k, (coordA A b j).comp g = c • LinearMap.id := fun j => hS _
  choose c hc using hc
  haveI := IsSimpleModule.nontrivial A S
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  have hgc : ∀ j s, E (g s) j = c j • s := fun j s => by
    have := LinearMap.congr_fun (hc j) s
    simpa [coordA_apply] using this
  let F := (E (g s₀)).support
  have hF : ∀ j, c j ≠ 0 → j ∈ F := fun j hj => by
    rw [Finsupp.mem_support_iff, hgc]
    exact smul_ne_zero hj hs₀
  refine ⟨∑ j ∈ F, c j • b j, ?_⟩
  have hg : g = tmulRightA k S (A := A) (∑ j ∈ F, c j • b j) := by
    refine LinearMap.ext fun s => E.injective (Finsupp.ext fun j => ?_)
    rw [hgc, tmulRightA_apply, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    split_ifs with hj
    · rfl
    · by_cases hcj : c j = 0
      · simp [hcj]
      · exact absurd (hF j hcj) hj
  rw [← hg]
  ext y
  constructor
  · intro hy
    refine ⟨φ ⟨y, hy⟩, ?_⟩
    simp [g]
  · rintro ⟨s, rfl⟩
    exact (φ.symm s).2

omit hS in
variable (k A) in
/-- `M₀ = {m | S ⊗ m ⊆ W}` for an `A`-submodule `W ⊆ S ⊗_k M`. -/
def core (W : Submodule A (S ⊗[k] M)) : Submodule k M where
  carrier := {m | ∀ s : S, s ⊗ₜ[k] m ∈ W}
  add_mem' ha hb s := by rw [TensorProduct.tmul_add]; exact add_mem (ha s) (hb s)
  zero_mem' s := by rw [TensorProduct.tmul_zero]; exact zero_mem _
  smul_mem' c m hm s := by
    rw [TensorProduct.tmul_smul]
    exact W.smul_of_tower_mem c (hm s)

omit hS in
theorem mem_core {W : Submodule A (S ⊗[k] M)} {m : M} :
    m ∈ core k A W ↔ ∀ s : S, s ⊗ₜ[k] m ∈ W := Iff.rfl

/-- **Isotypic submodules of `S ⊗ M`**: if `S` is simple with `End_A(S) = k`, every
`A`-submodule `W ⊆ S ⊗_k M` lies in `S ⊗ M₀`, `M₀ = {m | S ⊗ m ⊆ W}` (so `W = S ⊗ M₀`). -/
theorem mem_range_map_core [IsSimpleModule A S] (W : Submodule A (S ⊗[k] M)) {x : S ⊗[k] M}
    (hx : x ∈ W) :
    x ∈ LinearMap.range (TensorProduct.map (LinearMap.id : S →ₗ[k] S) (core k A W).subtype) := by
  haveI : IsSemisimpleModule A (S ⊗[k] M) := isSemisimpleModule_tensor
  let R : Submodule A (S ⊗[k] M) :=
    { carrier := LinearMap.range (TensorProduct.map (LinearMap.id : S →ₗ[k] S) (core k A W).subtype)
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := by
        rintro a _ ⟨y, rfl⟩
        induction y using TensorProduct.induction_on with
        | zero => rw [map_zero, smul_zero]; exact zero_mem _
        | tmul s m =>
          refine ⟨(a • s) ⊗ₜ m, ?_⟩
          simp [TensorProduct.smul_tmul']
        | add y z hy hz =>
          rw [map_add, smul_add]
          exact add_mem hy hz }
  have hle : W ≤ R := by
    rw [← IsSemisimpleModule.sSup_simples_le W]
    refine sSup_le ?_
    rintro N ⟨hN, hNW⟩
    obtain ⟨m, rfl⟩ := exists_eq_range_tmulRightA hS N
    rintro _ ⟨s, rfl⟩
    exact ⟨s ⊗ₜ ⟨m, fun s' => hNW ⟨s', rfl⟩⟩, rfl⟩
  exact hle hx

/-- `mem_range_map_core` in terms of pure tensors: every element of `W` is a `k`-linear
combination of pure tensors `s ⊗ m` with `S ⊗ m ⊆ W`. -/
theorem mem_span_core [IsSimpleModule A S] (W : Submodule A (S ⊗[k] M)) {x : S ⊗[k] M}
    (hx : x ∈ W) :
    x ∈ Submodule.span k {y | ∃ (s : S) (m : M), m ∈ core k A W ∧ y = s ⊗ₜ[k] m} := by
  obtain ⟨y, rfl⟩ := mem_range_map_core hS W hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul s m => exact Submodule.subset_span ⟨s, m, m.2, rfl⟩
  | add y z hy hz => rw [map_add]; exact add_mem hy hz

end Isotypic

/-! ### The action of `A = A ⊗ 1` on `S ⊠ M` -/

section ExtAction

variable {k : Type*} [Field k] {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {S : Type*} [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]

theorem tmul_one_smul (a : A) (x : ExtTensor k S M) :
    (a ⊗ₜ[k] (1 : B)) • x =
      ExtTensor.equivTensor.symm (a • ExtTensor.equivTensor x) := by
  induction x using ExtTensor.induction_on with
  | zero => simp
  | tmul s m =>
    rw [ExtTensor.smul_tmul, one_smul]
    show _ = ExtTensor.equivTensor.symm (a • (s ⊗ₜ[k] m))
    rw [TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, hx, hy, map_add, smul_add, map_add]

variable (k A B) in
/-- An `A ⊗ B`-submodule of `S ⊠ M`, viewed as an `A`-submodule of `S ⊗_k M`. -/
def toA (K : Submodule (A ⊗[k] B) (ExtTensor k S M)) : Submodule A (S ⊗[k] M) where
  carrier := {x | ExtTensor.equivTensor.symm x ∈ K}
  add_mem' ha hb := by simp only [Set.mem_setOf_eq, map_add]; exact add_mem ha hb
  zero_mem' := by simp
  smul_mem' a x hx := by
    show ExtTensor.equivTensor.symm (a • x) ∈ K
    have := K.smul_mem (a ⊗ₜ[k] (1 : B)) hx
    rw [tmul_one_smul] at this
    exact this

theorem mem_toA {K : Submodule (A ⊗[k] B) (ExtTensor k S M)} {x : S ⊗[k] M} :
    x ∈ toA k A B K ↔ ExtTensor.equivTensor.symm x ∈ K := Iff.rfl

omit [IsScalarTower k A S] [IsScalarTower k B M] in
/-- Pure tensors of nonzero vectors are nonzero. -/
theorem tmul_ne_zero {s : S} {m : M} (hs : s ≠ 0) (hm : m ≠ 0) :
    (ExtTensor.tmul s m : ExtTensor k S M) ≠ 0 := by
  classical
  let b := Basis.ofVectorSpace k S
  intro h
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) (show s ⊗ₜ[k] m = 0 from h)
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, map_zero] at h'
  have hr : b.repr s ≠ 0 := fun h0 => hs (b.repr.map_eq_zero_iff.1 h0)
  obtain ⟨c, hc⟩ := Finsupp.ne_iff.1 hr
  have := congrArg (fun f => f c) h'
  simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at this hc
  exact hm ((smul_eq_zero.1 this).resolve_left hc)

/-- **`S ⊠ S'` is simple**: if `S` is a simple `A`-module with `End_A(S) = k` and `S'` is a
simple `B`-module, the external tensor product `S ⊠ S'` is a simple `A ⊗ B`-module. -/
theorem isSimpleModule_extTensor [IsSimpleModule A S] [IsSimpleModule B M]
    (hS : ∀ f : S →ₗ[A] S, ∃ c : k, f = c • LinearMap.id) :
    IsSimpleModule (A ⊗[k] B) (ExtTensor k S M) := by
  haveI := IsSimpleModule.nontrivial A S
  haveI := IsSimpleModule.nontrivial B M
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hne : (ExtTensor.tmul s₀ m₀ : ExtTensor k S M) ≠ 0 := tmul_ne_zero hs₀ hm₀
  haveI : Nontrivial (ExtTensor k S M) := ⟨⟨_, 0, hne⟩⟩
  refine ⟨fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  -- the core `M₀` is a nonzero `B`-submodule of `M`
  let W' := toA k A B W
  let M₀ : Submodule B M :=
    { carrier := core k A W'
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun b m hm s => by
        show ExtTensor.equivTensor.symm (s ⊗ₜ[k] (b • m)) ∈ W
        have := W.smul_mem ((1 : A) ⊗ₜ[k] b) (show ExtTensor.tmul s m ∈ W from hm s)
        rw [ExtTensor.smul_tmul, one_smul] at this
        exact this }
  have hM₀ : M₀ ≠ ⊥ := by
    intro h
    apply hW
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := mem_range_map_core hS W' (x := ExtTensor.equivTensor x)
      (by show ExtTensor.equivTensor.symm (ExtTensor.equivTensor x) ∈ W; simpa using hx)
    have hcore : ∀ m ∈ core k A W', m = 0 := fun m hm => by
      have : m ∈ M₀ := hm
      rw [h] at this
      exact (Submodule.mem_bot B).1 this
    have hzero : ∀ y : S ⊗[k] core k A W',
        TensorProduct.map LinearMap.id (core k A W').subtype y = 0 := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact map_zero _
      | tmul s m =>
        rw [TensorProduct.map_tmul, Submodule.subtype_apply, hcore m m.2, TensorProduct.tmul_zero]
      | add y z hy hz => rw [map_add, hy, hz, add_zero]
    rw [Submodule.mem_bot, ← ExtTensor.equivTensor.map_eq_zero_iff, ← hy, hzero]
  have htop : M₀ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top M₀).resolve_left hM₀
  rw [eq_top_iff]
  rintro x -
  induction x using ExtTensor.induction_on with
  | zero => exact zero_mem _
  | tmul s m => exact (show m ∈ M₀ from htop ▸ Submodule.mem_top) s
  | add x y hx hy => exact add_mem hx hy

end ExtAction

/-! ### Graded: simple modules over `A ⊗ B` -/

section Graded

open Graded DirectSum GProj Module

variable {k : Type v} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {U : Type u} [AddCommGroup U] [Module k U] [Module (A ⊗[k] B) U]
  [IsScalarTower k (A ⊗[k] B) U] {𝒰 : ℤ → Submodule k U} [Decomposition 𝒰]
  [SetLike.GradedSMul (tensorGrading 𝒜 ℬ) 𝒰]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem extTensor_sum_tmul {S M : Type*} [AddCommGroup S] [Module k S] [AddCommGroup M]
    [Module k M] {ι : Type*} (t : Finset ι) (f : ι → S) (q : M) :
    (ExtTensor.tmul (∑ i ∈ t, f i) q : ExtTensor k S M) = ∑ i ∈ t, ExtTensor.tmul (f i) q :=
  TensorProduct.sum_tmul t f q

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem extTensor_tmul_sum {S M : Type*} [AddCommGroup S] [Module k S] [AddCommGroup M]
    [Module k M] {ι : Type*} (t : Finset ι) (s : S) (f : ι → M) :
    (ExtTensor.tmul s (∑ i ∈ t, f i) : ExtTensor k S M) = ∑ i ∈ t, ExtTensor.tmul s (f i) :=
  TensorProduct.tmul_sum s t f

variable (B) in
/-- The `A`-module structure on an `A ⊗ B`-module, through `a ↦ a ⊗ 1` (a local instance). -/
abbrev moduleA : Module A U :=
  Module.compHom U (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] B)

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [Decomposition 𝒰] in
theorem isScalarTower_moduleA :
    letI := moduleA (k := k) (A := A) (U := U) B
    IsScalarTower k A U := by
  letI := moduleA (k := k) (A := A) (U := U) B
  exact ⟨fun c a u => by
    show ((c • a) ⊗ₜ[k] (1 : B)) • u = c • ((a ⊗ₜ[k] (1 : B)) • u)
    rw [← TensorProduct.smul_tmul', smul_assoc]⟩

omit [GradedAlgebra 𝒜] [Decomposition 𝒰] [IsScalarTower k (A ⊗[k] B) U] in
include ℬ in
theorem gradedSMul_moduleA :
    letI := moduleA (k := k) (A := A) (U := U) B
    SetLike.GradedSMul 𝒜 𝒰 := by
  letI := moduleA (k := k) (A := A) (U := U) B
  exact ⟨fun {i j} a u ha hu => by
    have h1 : a ⊗ₜ[k] (1 : B) ∈ tensorGrading 𝒜 ℬ (i + 0) :=
      tmul_mem_tensorGrading ha SetLike.GradedOne.one_mem
    have := SetLike.GradedSMul.smul_mem (A := tensorGrading 𝒜 ℬ) (B := 𝒰) h1 hu
    rw [vadd_eq_add, add_zero] at this
    exact this⟩

variable [HasGdim 𝒜]

include ℬ in
/-- **A nonzero finite-dimensional graded `A ⊗ B`-module contains a graded simple
`A`-submodule** (for the action of `A = A ⊗ 1`): there are an indecomposable class `b`, a shift
`a` and an injective `A`-linear map `S_b → U` sending `(S_b)_j` into `U_{j + a}`. -/
theorem exists_top_embedding [FiniteDimensional k U] [Nontrivial U] :
    ∃ (b : IndecClass 𝒜) (a : ℤ) (ι : b.top →ₗ[k] U), Function.Injective ι ∧
      (∀ (x : A) (s : b.top), ι (x • s) = (x ⊗ₜ[k] (1 : B)) • ι s) ∧
      ∀ ⦃j : ℤ⦄ ⦃s : b.top⦄, s ∈ b.top.grading j → ι s ∈ 𝒰 (j + a) := by
  classical
  letI := moduleA (k := k) (A := A) (U := U) B
  haveI := isScalarTower_moduleA (k := k) (A := A) (U := U) (B := B)
  haveI := gradedSMul_moduleA (k := k) (A := A) (U := U) (𝒜 := 𝒜) (ℬ := ℬ) (𝒰 := 𝒰)
  -- a nonzero homogeneous `A`-submodule of minimal dimension
  let P : ℕ → Prop := fun n => ∃ p : Submodule A U, p.IsHomogeneous 𝒰 ∧ p ≠ ⊥ ∧
    finrank k (p.restrictScalars k) = n
  have hP : ∃ n, P n := ⟨_, ⊤, fun _ _ _ => Submodule.mem_top, top_ne_bot, rfl⟩
  obtain ⟨p, hphom, hp0, hpn⟩ := Nat.find_spec hP
  have hmin : ∀ p' : Submodule A U, p'.IsHomogeneous 𝒰 → p' ≠ ⊥ → p' ≤ p → p' = p := by
    intro p' h1 h2 h3
    have h4 : Nat.find hP ≤ finrank k (p'.restrictScalars k) := Nat.find_min' hP ⟨p', h1, h2, rfl⟩
    have h5 : p'.restrictScalars k = p.restrictScalars k :=
      Submodule.eq_of_le_of_finrank_le h3 (by rw [hpn]; exact h4)
    exact Submodule.restrictScalars_injective k A U h5
  letI : Decomposition (Graded.submodule 𝒰 p) := submoduleDecomposition 𝒰 hphom
  have hsimple : IsGradedSimple 𝒜 (Graded.submodule 𝒰 p) := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 hp0, fun p' hp' => ?_⟩
    by_cases h : p' = ⊥
    · exact Or.inl h
    right
    let q := p'.map p.subtype
    have hq : q.IsHomogeneous 𝒰 := by
      rintro i _ ⟨y, hy, rfl⟩
      have := decompose_map (ℳ := Graded.submodule 𝒰 p) (𝒩 := 𝒰) (f := p.subtype)
        (fun _ _ h => h) y i
      rw [this]
      exact ⟨_, hp' i hy, rfl⟩
    have hq0 : q ≠ ⊥ := by
      intro hq0
      apply h
      rw [eq_bot_iff]
      intro y hy
      have : (y : U) ∈ q := ⟨y, hy, rfl⟩
      rw [hq0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot A).2 (Subtype.ext this)
    have hqp := hmin q hq hq0 (Submodule.map_subtype_le p p')
    rw [eq_top_iff]
    intro y _
    have : (y : U) ∈ q := by rw [hqp]; exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [show z = y from Subtype.ext hzy] at hz
  obtain ⟨b, a, ⟨e⟩⟩ := IndecClass.exists_gradedEquiv_top_shift (𝒜 := 𝒜) hsimple
  refine ⟨b, a, (p.subtype.restrictScalars k).comp
    (e.symm.toLinearEquiv.toLinearMap.restrictScalars k), ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · intro x s
    show ((e.symm (x • s) : p) : U) = (x ⊗ₜ[k] (1 : B)) • ((e.symm s : p) : U)
    rw [show e.symm (x • s) = x • e.symm s from e.symm.toLinearEquiv.map_smul x s]
    rfl
  · intro j s hs
    have : e.symm s ∈ Graded.submodule 𝒰 p (j + a) :=
      e.symm.map_mem (show s ∈ Graded.shift b.top.grading a (j + a) by
        show s ∈ b.top.grading (j + a - a)
        rwa [add_sub_cancel_right])
    exact this

section Classification

variable [HasGdim ℬ]

/-- The map `Φ : S ⊠ B → U`, `s ⊗ q ↦ (1 ⊗ q) • ι(s)`, for an `A`-linear `ι : S → U`. -/
def extMap {S : Type*} [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
    (ι : S →ₗ[k] U) (hι : ∀ (x : A) (s : S), ι (x • s) = (x ⊗ₜ[k] (1 : B)) • ι s) :
    ExtTensor k S B →ₗ[A ⊗[k] B] U where
  toFun := ExtTensor.lift (LinearMap.mk₂ k (fun s q => ((1 : A) ⊗ₜ[k] q) • ι s)
    (fun s s' q => by beta_reduce; rw [map_add, smul_add])
    (fun c s q => by beta_reduce; rw [map_smul, smul_comm])
    (fun s q q' => by beta_reduce; rw [TensorProduct.tmul_add, add_smul])
    (fun c s q => by beta_reduce; rw [TensorProduct.tmul_smul, smul_assoc]))
  map_add' := map_add _
  map_smul' t x := ExtTensor.smul_eq_induction (map_add _) (map_zero _)
    (fun a y s q => by
      rw [ExtTensor.smul_tmul]
      show ((1 : A) ⊗ₜ[k] (y • q)) • ι (a • s) = (a ⊗ₜ[k] y) • (((1 : A) ⊗ₜ[k] q) • ι s)
      rw [hι, smul_smul, smul_smul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_one, smul_eq_mul]) t x

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [Decomposition 𝒰] [HasGdim 𝒜] [HasGdim ℬ] in
theorem extMap_tmul {S : Type*} [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
    (ι : S →ₗ[k] U) (hι : ∀ (x : A) (s : S), ι (x • s) = (x ⊗ₜ[k] (1 : B)) • ι s) (s : S)
    (q : B) : extMap ι hι (ExtTensor.tmul s q) = ((1 : A) ⊗ₜ[k] q) • ι s := rfl

/-- **Classification of graded simple `A ⊗ B`-modules.** Let `(A, 𝒜)`, `(B, ℬ)` be graded
algebras with graded dimensions such that `End_A(S_b) = k` for the graded simple tops `S_b` of the
indecomposable graded projective `A`-modules. Then every finite-dimensional graded simple
`A ⊗ B`-module is isomorphic, by a degree-preserving isomorphism, to `(S_b ⊠ S_{b'}){a}` for some
indecomposable classes `b` of `A`, `b'` of `B` and a shift `a`. -/
theorem exists_gradedEquiv_extTensor_top
    (hEnd : ∀ (b : IndecClass 𝒜) (f : b.top →ₗ[A] b.top), ∃ c : k, f = c • LinearMap.id)
    [FiniteDimensional k U] (hU : IsGradedSimple (tensorGrading 𝒜 ℬ) 𝒰) :
    ∃ (b : IndecClass 𝒜) (b' : IndecClass ℬ) (a : ℤ),
      Nonempty (𝒰 ≃ᵍ[A ⊗[k] B]
        Graded.shift (ExtTensor.grading b.top.grading b'.top.grading) a) := by
  classical
  haveI := hU.nontrivial
  obtain ⟨b, a₀, ι, hιinj, hιA, hιdeg⟩ := exists_top_embedding (𝒜 := 𝒜) (ℬ := ℬ) (𝒰 := 𝒰)
  haveI : FiniteDimensional k b.top := FiniteDimensional.of_injective ι hιinj
  haveI : IsSimpleModule A b.top := (IndecClass.isGradedSimple_top b).isSimpleModule
  haveI := (IndecClass.isGradedSimple_top b).nontrivial
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : b.top)
  set Φ := extMap (B := B) ι hιA with hΦdef
  set G := ExtTensor.grading b.top.grading ℬ with hGdef
  -- `Φ` shifts degrees by `a₀`
  have hΦdeg : ∀ ⦃d : ℤ⦄ ⦃x : ExtTensor k b.top B⦄, x ∈ G d → Φ x ∈ 𝒰 (d + a₀) := by
    intro d x hx
    refine ExtTensor.grading_map_mem b.top.grading ℬ (fun d => 𝒰 (d + a₀))
      (Φ.restrictScalars k) (fun i j s q hs hq => ?_) hx
    show ((1 : A) ⊗ₜ[k] q) • ι s ∈ 𝒰 (i + j + a₀)
    have h1 : (1 : A) ⊗ₜ[k] q ∈ tensorGrading 𝒜 ℬ (0 + j) :=
      tmul_mem_tensorGrading SetLike.GradedOne.one_mem hq
    have := SetLike.GradedSMul.smul_mem (A := tensorGrading 𝒜 ℬ) (B := 𝒰) h1 (hιdeg hs)
    rw [vadd_eq_add] at this
    convert this using 2
    ring
  have hΦ : PreservesGrading (Graded.shift G a₀) 𝒰 Φ := fun d x hx => by
    have := hΦdeg (d := d - a₀) hx
    rwa [sub_add_cancel] at this
  have hΦs₀ : Φ (ExtTensor.tmul s₀ 1) = ι s₀ := by
    rw [hΦdef, extMap_tmul, ← Algebra.TensorProduct.one_def, one_smul]
  have hΦ0 : Φ ≠ 0 := fun h => by
    have := LinearMap.congr_fun h (ExtTensor.tmul s₀ 1)
    rw [hΦs₀, LinearMap.zero_apply] at this
    exact hs₀ (hιinj (this.trans (map_zero ι).symm))
  have hΦsurj : Function.Surjective Φ := by
    rcases hU.eq_bot_or_eq_top _ (isHomogeneous_range hΦ) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hΦ0
    · exact LinearMap.range_eq_top.1 h
  -- the kernel `K = S ⊠ B₀`
  set K := LinearMap.ker Φ with hKdef
  have hKhom : K.IsHomogeneous G := (isHomogeneous_shift_iff K a₀).1 (isHomogeneous_ker hΦ)
  set W := toA k A B K with hWdef
  let B₀ : Submodule B B :=
    { carrier := core k A W
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun y m hm s => by
        show ExtTensor.tmul s (y • m) ∈ K
        have := K.smul_mem ((1 : A) ⊗ₜ[k] y) (show ExtTensor.tmul s m ∈ K from hm s)
        rwa [ExtTensor.smul_tmul, one_smul] at this }
  have hB₀ : ∀ m : B, m ∈ B₀ ↔ ∀ s : b.top, ExtTensor.tmul s m ∈ K := fun _ => Iff.rfl
  -- `K ⊆ S ⊗ B₀`
  have hKspan : ∀ x ∈ K, x ∈ Submodule.span k
      {y | ∃ (s : b.top) (m : B), m ∈ B₀ ∧ y = ExtTensor.tmul s m} := fun x hx =>
    mem_span_core (hEnd b) W (x := ExtTensor.equivTensor x) hx
  -- `B₀` is homogeneous
  have hcomp : ∀ (j : ℤ) (s : b.top), s ∈ b.top.grading j → ∀ (m : B) (i : ℤ),
      (decompose G (ExtTensor.tmul s m) (i + j) : ExtTensor k b.top B) =
        ExtTensor.tmul s (decompose ℬ m i : B) := by
    intro j s hs m i
    let L : B →ₗ[k] ExtTensor k b.top B :=
      { toFun := fun q => ExtTensor.tmul s q
        map_add' := ExtTensor.tmul_add s
        map_smul' := fun c q => ExtTensor.tmul_smul c s q }
    have hL : PreservesGrading ℬ (Graded.shift G (-j)) L := fun i q hq => by
      show ExtTensor.tmul s q ∈ G (i - -j)
      have := ExtTensor.tmul_mem_grading (k := k) hs hq
      rwa [show i - -j = j + i by ring]
    have h1 := decompose_map hL m i
    have h2 := decompose_shift G (-j) (ExtTensor.tmul s m) (i + j)
    rw [show i + j + -j = i by ring] at h2
    rw [← h2]
    exact h1
  have hB₀hom : B₀.IsHomogeneous ℬ := by
    intro i m hm s
    show ExtTensor.tmul s (decompose ℬ m i : B) ∈ K
    rw [← sum_support_decompose b.top.grading s, extTensor_sum_tmul]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hcomp j _ (decompose b.top.grading s j).2 m i]
    exact hKhom (i + j) (hm _)
  have hB₀top : B₀ ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ B₀ := h ▸ Submodule.mem_top
    have := (hB₀ 1).1 h1 s₀
    rw [LinearMap.mem_ker, hΦs₀] at this
    exact hs₀ (hιinj (this.trans (map_zero ι).symm))
  -- `B₀` is a maximal homogeneous left ideal
  have hmax : ∀ N' : Submodule B B, N'.IsHomogeneous ℬ → B₀ ≤ N' → N' = B₀ ∨ N' = ⊤ := by
    intro N' hN' hle
    let gens : Set U := {u | ∃ (j i : ℤ) (s : b.top) (q : B), s ∈ b.top.grading j ∧
      q ∈ ℬ i ∧ q ∈ N' ∧ u = Φ (ExtTensor.tmul s q)}
    have hX : (Submodule.span (A ⊗[k] B) gens).IsHomogeneous 𝒰 := by
      refine isHomogeneous_span (tensorGrading 𝒜 ℬ) 𝒰 ?_
      rintro _ ⟨j, i, s, q, hs, hq, -, rfl⟩
      exact ⟨j + i + a₀, hΦdeg (ExtTensor.tmul_mem_grading hs hq)⟩
    rcases hU.eq_bot_or_eq_top _ hX with h | h
    · left
      refine le_antisymm (fun q hq s => ?_) hle
      show ExtTensor.tmul s q ∈ K
      rw [← sum_support_decompose b.top.grading s, ← sum_support_decompose ℬ q]
      simp only [extTensor_sum_tmul, extTensor_tmul_sum]
      have hzero : ∀ j i : ℤ, ExtTensor.tmul (decompose b.top.grading s j : b.top)
          (decompose ℬ q i : B) ∈ K := fun j i => by
        have hmem : Φ (ExtTensor.tmul (decompose b.top.grading s j : b.top)
            (decompose ℬ q i : B)) ∈ Submodule.span (A ⊗[k] B) gens :=
          Submodule.subset_span ⟨j, i, _, _, (decompose _ s j).2, (decompose _ q i).2,
            hN' i hq, rfl⟩
        rw [h, Submodule.mem_bot] at hmem
        exact hmem
      exact Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun y _ => hzero _ _
    · right
      -- `1 ∈ N'`
      let RC : Submodule (A ⊗[k] B) (ExtTensor k b.top B) :=
        LinearMap.range (ExtTensor.map (LinearMap.id : b.top →ₗ[A] b.top) N'.subtype)
      have htmulRC : ∀ (s : b.top) (q : B), q ∈ N' → ExtTensor.tmul s q ∈ RC :=
        fun s q hq => ⟨ExtTensor.tmul s ⟨q, hq⟩, rfl⟩
      have hKRC : K ≤ RC := by
        intro x hx
        have := hKspan x hx
        refine (Submodule.span_le (p := RC.restrictScalars k)).2 ?_ this
        rintro _ ⟨s, m, hm, rfl⟩
        exact htmulRC s m (hle hm)
      have hXle : Submodule.span (A ⊗[k] B) gens ≤ RC.map Φ := by
        rw [Submodule.span_le]
        rintro _ ⟨j, i, s, q, -, -, hq, rfl⟩
        exact ⟨_, htmulRC s q hq, rfl⟩
      have h1 : Φ (ExtTensor.tmul s₀ 1) ∈ RC.map Φ := hXle (h ▸ Submodule.mem_top)
      obtain ⟨v, hv, hvΦ⟩ := h1
      have hdiff : ExtTensor.tmul s₀ 1 - v ∈ K := by
        rw [LinearMap.mem_ker, map_sub, hvΦ, sub_self]
      have hs1 : ExtTensor.tmul s₀ (1 : B) ∈ RC := by
        have := RC.add_mem (hKRC hdiff) hv
        rwa [sub_add_cancel] at this
      -- a functional `φ` with `φ s₀ = 1`
      obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k b.top, φ s₀ ≠ 0 :=
        not_forall.1 fun h => hs₀ ((Module.forall_dual_apply_eq_zero_iff k s₀).1 h)
      let ε : ExtTensor k b.top B →ₗ[k] B := ExtTensor.lift (LinearMap.mk₂ k (fun s q => φ s • q)
        (fun s s' q => by beta_reduce; rw [map_add, add_smul])
        (fun c s q => by beta_reduce; rw [map_smul, smul_eq_mul, mul_smul])
        (fun s q q' => smul_add _ _ _) (fun c s q => smul_comm _ _ _))
      have hεRC : ∀ x ∈ RC, ε x ∈ N' := by
        rintro _ ⟨y, rfl⟩
        induction y using ExtTensor.induction_on with
        | zero => rw [map_zero, map_zero]; exact zero_mem _
        | tmul s q =>
          show φ s • (q : B) ∈ N'
          exact N'.smul_of_tower_mem _ q.2
        | add y z hy hz => rw [map_add, map_add]; exact add_mem hy hz
      have h1N : (1 : B) ∈ N' := by
        have := N'.smul_of_tower_mem (φ s₀)⁻¹ (hεRC _ hs1)
        rwa [show ε (ExtTensor.tmul s₀ 1) = φ s₀ • (1 : B) from rfl, smul_smul,
          inv_mul_cancel₀ hφ, one_smul] at this
      exact (Submodule.eq_top_iff'.2 fun q => by simpa using N'.smul_mem q h1N)
  -- the graded simple quotient `B / B₀ ≅ S_{b'}{a₁}`
  letI := quotDecompositionA ℬ B₀ hB₀hom
  have hQ : IsGradedSimple ℬ (quotGradingA ℬ B₀) := isGradedSimple_quot ℬ ℬ B₀ hB₀hom hB₀top hmax
  obtain ⟨b', a₁, ⟨e'⟩⟩ := IndecClass.exists_gradedEquiv_top_shift (𝒜 := ℬ) hQ
  let ψ : B →ₗ[B] b'.top := e'.toLinearEquiv.toLinearMap ∘ₗ B₀.mkQ
  have hψdeg : PreservesGrading ℬ (Graded.shift b'.top.grading a₁) ψ :=
    (e'.preservesGrading).comp (preservesGrading_mkQ ℬ B₀)
  have hψsurj : Function.Surjective ψ := e'.toLinearEquiv.surjective.comp B₀.mkQ_surjective
  have hψB₀ : ∀ q ∈ B₀, ψ q = 0 := fun q hq => by
    show e'.toLinearEquiv (B₀.mkQ q) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero B₀).2 hq, map_zero]
  have hψ1 : ψ 1 ≠ 0 := fun h => hB₀top (by
    rw [eq_top_iff]
    intro q _
    have h1 : (1 : B) ∈ B₀ := by
      rw [show ψ 1 = e'.toLinearEquiv (B₀.mkQ 1) from rfl, LinearEquiv.map_eq_zero_iff] at h
      exact (Submodule.Quotient.mk_eq_zero B₀).1 h
    simpa using B₀.smul_mem q h1)
  -- `χ = id ⊠ ψ : S ⊠ B → S ⊠ S_{b'}` kills `K`, hence factors through `Φ`
  let χ := ExtTensor.map (k := k) (LinearMap.id : b.top →ₗ[A] b.top) ψ
  set T := ExtTensor.grading b.top.grading b'.top.grading with hTdef
  have hχ : PreservesGrading G (Graded.shift T a₁) χ := by
    have := ExtTensor.map_preservesGrading (𝒰 := b.top.grading) (𝒱 := ℬ)
      (𝒰' := b.top.grading) (𝒱' := Graded.shift b'.top.grading a₁)
      (f := (LinearMap.id : b.top →ₗ[A] b.top)) (fun _ _ h => h) hψdeg
    rwa [ExtTensor.grading_shift_right] at this
  have hχsurj : Function.Surjective χ := ExtTensor.map_surjective Function.surjective_id hψsurj
  have hKχ : K ≤ LinearMap.ker χ := by
    intro x hx
    have := hKspan x hx
    refine (Submodule.span_le (p := (LinearMap.ker χ).restrictScalars k)).2 ?_ this
    rintro _ ⟨s, m, hm, rfl⟩
    show ExtTensor.tmul s (ψ m) = 0
    rw [hψB₀ m hm, ExtTensor.tmul_zero]
  let f : U →ₗ[A ⊗[k] B] ExtTensor k b.top b'.top :=
    (K.liftQ χ hKχ) ∘ₗ (Φ.quotKerEquivOfSurjective hΦsurj).symm.toLinearMap
  have hfΦ : ∀ x, f (Φ x) = χ x := fun x => by
    have : (Φ.quotKerEquivOfSurjective hΦsurj).symm (Φ x) = K.mkQ x :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    show K.liftQ χ hKχ ((Φ.quotKerEquivOfSurjective hΦsurj).symm (Φ x)) = χ x
    rw [this]
    rfl
  have hfsurj : Function.Surjective f := fun y => by
    obtain ⟨x, rfl⟩ := hχsurj y
    exact ⟨Φ x, hfΦ x⟩
  have hfdeg : PreservesGrading 𝒰 (Graded.shift (Graded.shift T a₁) a₀) f := by
    intro n u hu
    obtain ⟨x, rfl⟩ := hΦsurj u
    have hx' : Φ (decompose (Graded.shift G a₀) x n) = Φ x := by
      rw [← decompose_map hΦ, decompose_of_mem_same _ hu]
    rw [← hx', hfΦ]
    exact hχ (decompose (Graded.shift G a₀) x n).2
  have hf0 : f ≠ 0 := fun h => by
    have := LinearMap.congr_fun h (Φ (ExtTensor.tmul s₀ 1))
    rw [hfΦ, LinearMap.zero_apply] at this
    exact tmul_ne_zero hs₀ hψ1 this
  have hfinj : Function.Injective f := by
    rcases hU.eq_bot_or_eq_top _ (isHomogeneous_ker hfdeg) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  exact ⟨b, b', a₁ + a₀, ⟨(GradedEquiv.ofBijective hfdeg ⟨hfinj, hfsurj⟩).trans
    (GradedEquiv.ofEq (shift_shift T a₁ a₀))⟩⟩

end Classification

end Graded

end TensorSimple

end Categorification
