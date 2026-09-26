/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.HomForm
import Categorification.Algebra.Graded.Tensor
import Categorification.Algebra.Graded.Simple

/-!
# Duality on graded projective modules and the bar involution on `K₀`

Let `(A, 𝒜)` be a `ℤ`-graded algebra over a field `k` with a degree-preserving antiinvolution `ψ`
(`GradedAntiInvolution 𝒜`). Following Khovanov–Lauda I (arXiv:0803.4121v2, §2.5, TeX lines
~1533–1541), for a finitely generated graded projective left `A`-module `P` we set

  `P̄ = HOM(P, A)^ψ`,

the graded right `A`-module `HOM(P, A)` turned into a left module through `ψ`:
`(a • f)(m) = f(m) ψ(a)`. The paper states that `¯` is a contravariant self-equivalence of
`A-pmod` with `P̄_i ≅ P_i`, `\overline{P_i{a}} ≅ P_i{-a}`, and that it induces a
`ℤ[q, q⁻¹]`-antilinear involution of `K₀`; KL I's bilinear form is
`(P, Q) = gdim (P^ψ ⊗_A Q)`, which is `gdim HOM(P̄, Q)`.

## Main definitions and results

* `homComponent 𝒜 ℳ 𝒩 d f` and `isInternal_homGrade` : for a finitely generated graded `M`,
  `HOM(M, N) = ⨁_d HOM(M, N)_d` (every `A`-linear map is a finite sum of homogeneous ones).
* `GradedAntiInvolution 𝒜` : degree-preserving antiinvolutions.
* `Dual ψ M`, `dualGrading ψ ℳ` : the graded left module `M̄ = HOM(M, A)^ψ`.
* `exists_dualBasis` : finite dual bases of finitely generated projective modules; hence
  `M̄` is finitely generated projective (instances) and `Dual.ev : M → M̄̄` is bijective
  (`Dual.ev_bijective`).
* `GProj.dual ψ P` : **`P̄` as an object of `A-pmod`**, with
  `GProj.dualCongr` (functoriality on isomorphisms), `GProj.dualProd` (`\overline{P ⊕ Q} ≅ P̄ ⊕ Q̄`),
  `GProj.dualShift` (**`\overline{P{a}} ≅ P̄{-a}`**), `GProj.dualDual` (**`P ≅ P̄̄`**) and
  `GProj.dualOfIdempotent` (**`\overline{A e} ≅ A ψ(e)`** for a degree-zero idempotent `e`).
* `K0.bar ψ` : **the bar involution of `K₀(A)`**, `[P] ↦ [P̄]`; `K0.bar_T_smul`
  (`\overline{q^a x} = q^{-a} x̄`), `K0.bar_smul` (antilinearity, via
  `LaurentPolynomial.invert`), `K0.bar_bar`, `K0.bar_ofIdempotent`
  (`\overline{[A e]} = [A ψ(e)]`), `K0.bar_regular`.
* `GProj.dualTransposeEquiv`, `GProj.homGdim_dual_comm` : **`HOM(P̄, Q)_d ≅ HOM(Q̄, P)_d`**
  (transposition), so `gdim HOM(P̄, Q) = gdim HOM(Q̄, P)`.
* `K0.pform 𝒜 ψ` : **KL I's bilinear form** `(x, y) = homForm x̄ y`
  (`([P], [Q]) = gdim HOM(P̄, Q)`), which is `ℤ[q, q⁻¹]`-bilinear (`K0.pform_smul_left`,
  `K0.pform_smul_right`) and **symmetric** (`K0.pform_comm`), with
  `([A e], [A e']) = gdim (ψ(e) A e')` (`K0.pform_ofIdempotent_ofIdempotent`) and
  `homForm x y = pform x̄ y` (`K0.homForm_eq_pform`).

## Design notes

* `Dual ψ M` is a type synonym for `M →ₗ[A] A` carrying the twisted left `A`-module structure
  (and the `k`-module structure of `M →ₗ[A] A`); `GProj.dual` is reducible so that elements of
  `(P.dual ψ).carrier` can be applied as functions.
* We work with ungraded projectivity (`Module.Projective`), as in `Graded.K0`; the grading on
  `P̄` is a `Decomposition` because `P` is finitely generated (`isInternal_homGrade`).
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function

/-! ### Homogeneous components of `A`-linear maps -/

section HomComponent

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]
  {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]

/-- The projection `N → N_d` onto the degree-`d` component, as a `k`-linear map `N → N`. -/
def gradeProj (d : ℤ) : N →ₗ[k] N :=
  (𝒩 d).subtype ∘ₗ (DirectSum.component k ℤ (fun i => 𝒩 i) d) ∘ₗ
    (decomposeLinearEquiv 𝒩).toLinearMap

omit [Module A N] [IsScalarTower k A N] [SetLike.GradedSMul 𝒜 𝒩] in
@[simp] theorem gradeProj_apply (d : ℤ) (n : N) : gradeProj 𝒩 d n = decompose 𝒩 n d := by
  simp [gradeProj, decomposeLinearEquiv_apply, ← DirectSum.apply_eq_component]

/-- The degree-`d` component of an `A`-linear map `f : M → N`, as a `k`-linear map:
`x ∈ M_e ↦ (f x)_{e + d}`. -/
def homComponentK (d : ℤ) (f : M →ₗ[A] N) : M →ₗ[k] N :=
  (DirectSum.toModule k ℤ N fun e =>
      gradeProj 𝒩 (e + d) ∘ₗ (f.restrictScalars k) ∘ₗ (ℳ e).subtype) ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap

omit [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] in
theorem homComponentK_apply_of_mem [Decomposition ℳ] {d e : ℤ} {x : M} (hx : x ∈ ℳ e)
    (f : M →ₗ[A] N) : homComponentK ℳ 𝒩 d f x = decompose 𝒩 (f x) (e + d) := by
  have : decompose ℳ x = DirectSum.lof k ℤ (fun i => ℳ i) e ⟨x, hx⟩ :=
    decompose_of_mem ℳ hx
  simp only [homComponentK, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    decomposeLinearEquiv_apply, this, toModule_lof, Submodule.coe_subtype,
    LinearMap.restrictScalars_apply, gradeProj_apply]

omit [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] in
/-- `k`-linear maps agreeing on homogeneous elements are equal. -/
theorem linearMap_ext_homogeneous {P : Type*} [AddCommGroup P] [Module k P] {f g : M →ₗ[k] P}
    (h : ∀ e, ∀ x ∈ ℳ e, f x = g x) : f = g := by
  ext x
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | @homogeneous e x => exact h e x x.2

include 𝒜 in
theorem homComponentK_smul (d : ℤ) (f : M →ₗ[A] N) (a : A) (x : M) :
    homComponentK ℳ 𝒩 d f (a • x) = a • homComponentK ℳ 𝒩 d f x := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | @homogeneous e x =>
    induction a using Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]
    | @homogeneous i a =>
      have hax : (a : A) • (x : M) ∈ ℳ (i + e) := by
        simpa [vadd_eq_add] using SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) a.2 x.2
      rw [homComponentK_apply_of_mem ℳ 𝒩 hax, homComponentK_apply_of_mem ℳ 𝒩 x.2, map_smul,
        decompose_smul_of_mem_left 𝒜 𝒩 a.2, show i + e + d - i = e + d by ring]

include 𝒜 in
/-- The degree-`d` component `f_d` of an `A`-linear map `f : M → N` (with
`f_d (x) = (f x)_{e + d}` for `x ∈ M_e`), an element of `HOM(M, N)_d`. -/
def homComponent (d : ℤ) : (M →ₗ[A] N) →ₗ[k] (M →ₗ[A] N) where
  toFun f :=
    { toFun := homComponentK ℳ 𝒩 d f
      map_add' := map_add _
      map_smul' := homComponentK_smul 𝒜 ℳ 𝒩 d f }
  map_add' f g := by
    apply LinearMap.restrictScalars_injective k
    apply linearMap_ext_homogeneous ℳ
    intro e x hx
    simp only [LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, homComponentK_apply_of_mem ℳ 𝒩 hx, decompose_add, add_apply,
      Submodule.coe_add]
  map_smul' c f := by
    apply LinearMap.restrictScalars_injective k
    apply linearMap_ext_homogeneous ℳ
    intro e x hx
    simp only [LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, homComponentK_apply_of_mem ℳ 𝒩 hx, RingHom.id_apply,
      decompose_smul, DirectSum.smul_apply, Submodule.coe_smul_of_tower]

theorem homComponent_apply_of_mem {d e : ℤ} {x : M} (hx : x ∈ ℳ e) (f : M →ₗ[A] N) :
    homComponent 𝒜 ℳ 𝒩 d f x = decompose 𝒩 (f x) (e + d) :=
  homComponentK_apply_of_mem ℳ 𝒩 hx f

theorem homComponent_mem (d : ℤ) (f : M →ₗ[A] N) :
    homComponent 𝒜 ℳ 𝒩 d f ∈ homGrade A ℳ 𝒩 d := fun e x hx => by
  rw [homComponent_apply_of_mem 𝒜 ℳ 𝒩 hx]
  exact (decompose 𝒩 (f x) (e + d)).2

theorem homComponent_of_mem {d j : ℤ} {f : M →ₗ[A] N} (hf : f ∈ homGrade A ℳ 𝒩 j) :
    homComponent 𝒜 ℳ 𝒩 d f = if j = d then f else 0 := by
  apply LinearMap.restrictScalars_injective k
  apply linearMap_ext_homogeneous ℳ
  intro e x hx
  simp only [LinearMap.restrictScalars_apply]
  rw [homComponent_apply_of_mem 𝒜 ℳ 𝒩 hx]
  split_ifs with h
  · subst h; exact decompose_of_mem_same 𝒩 (hf hx)
  · rw [LinearMap.zero_apply]
    exact decompose_of_mem_ne 𝒩 (hf hx) (by omega)

/-- A linear map `M → N` from a finitely generated graded module is the sum of finitely many of
its homogeneous components. -/
theorem exists_eq_sum_homComponent [Module.Finite A M] (f : M →ₗ[A] N) :
    ∃ s : Finset ℤ, f = ∑ d ∈ s, homComponent 𝒜 ℳ 𝒩 d f := by
  classical
  obtain ⟨g, hg, hspan⟩ := exists_homogeneous_generators (A := A) ℳ
  rw [Set.image_univ] at hspan
  refine ⟨g.biUnion fun p => (decompose 𝒩 (f p.2)).support.image fun n => n - p.1, ?_⟩
  refine LinearMap.ext_on_range hspan fun p => ?_
  obtain ⟨⟨e, m⟩, hp⟩ := p
  have hm : m ∈ ℳ e := hg _ hp
  simp only [LinearMap.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun d _ => homComponent_apply_of_mem 𝒜 ℳ 𝒩 hm (d := d) f]
  set S := g.biUnion fun p => (decompose 𝒩 (f p.2)).support.image fun n => n - p.1
  have hinj : Set.InjOn (fun d => e + d) S := fun a _ b _ h => by simpa using h
  rw [← Finset.sum_image (f := fun n => (decompose 𝒩 (f m) n : N)) hinj]
  conv_lhs => rw [← sum_support_decompose 𝒩 (f m)]
  refine Finset.sum_subset (fun n hn => ?_) fun n _ hn => ?_
  · rw [Finset.mem_image]
    refine ⟨n - e, Finset.mem_biUnion.2 ⟨(e, m), hp, Finset.mem_image.2 ⟨n, hn, rfl⟩⟩, by ring⟩
  · simpa using hn

include 𝒜 in
/-- **`HOM(M, N) = ⨁_d HOM(M, N)_d`** for a finitely generated graded module `M`: every
`A`-linear map is a finite sum of homogeneous ones, uniquely. -/
theorem isInternal_homGrade [Module.Finite A M] : IsInternal (homGrade A ℳ 𝒩) := by
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro d
    rw [Submodule.disjoint_def]
    intro f hf hf'
    have h1 : homComponent 𝒜 ℳ 𝒩 d f = f := by rw [homComponent_of_mem 𝒜 ℳ 𝒩 hf, if_pos rfl]
    have h2 : homComponent 𝒜 ℳ 𝒩 d f = 0 := by
      refine Submodule.iSup_induction _ (motive := fun f => homComponent 𝒜 ℳ 𝒩 d f = 0) hf'
        (fun j g hg => ?_) (map_zero _) (fun g g' hg hg' => by simp only [map_add, hg, hg', add_zero])
      refine Submodule.iSup_induction _ (motive := fun g => homComponent 𝒜 ℳ 𝒩 d g = 0) hg
        (fun hj g hg => ?_) (map_zero _) (fun g g' hg hg' => by simp only [map_add, hg, hg', add_zero])
      show homComponent 𝒜 ℳ 𝒩 d g = 0
      rw [homComponent_of_mem 𝒜 ℳ 𝒩 hg, if_neg hj]
    rw [← h1, h2]
  · rw [eq_top_iff]
    intro f _
    obtain ⟨s, hs⟩ := exists_eq_sum_homComponent 𝒜 ℳ 𝒩 f
    rw [hs]
    exact Submodule.sum_mem _ fun d _ =>
      Submodule.mem_iSup_of_mem d (homComponent_mem 𝒜 ℳ 𝒩 d f)

end HomComponent

/-! ### Degree-preserving antiinvolutions -/

section AntiInvolution

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

/-- A **degree-preserving antiinvolution** `ψ` of a `ℤ`-graded `k`-algebra `(A, 𝒜)`: a `k`-linear
map with `ψ(a b) = ψ(b) ψ(a)`, `ψ(1) = 1`, `ψ(ψ(a)) = a`, and `ψ(A_d) ⊆ A_d` (KL I, §2.1 and
§2.5: the antiinvolution `ψ` of `R(ν)` reflecting diagrams in a horizontal axis). -/
structure GradedAntiInvolution (𝒜 : ℤ → Submodule k A) where
  /-- The underlying `k`-linear map. -/
  toLinearMap : A →ₗ[k] A
  map_mul' : ∀ a b, toLinearMap (a * b) = toLinearMap b * toLinearMap a
  map_one' : toLinearMap 1 = 1
  invol' : ∀ a, toLinearMap (toLinearMap a) = a
  mem_grade' : ∀ ⦃d : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 d → toLinearMap a ∈ 𝒜 d

namespace GradedAntiInvolution

variable {𝒜 : ℤ → Submodule k A} (ψ : GradedAntiInvolution 𝒜)

instance : CoeFun (GradedAntiInvolution 𝒜) (fun _ => A → A) := ⟨fun ψ => ψ.toLinearMap⟩

@[simp] theorem map_mul (a b : A) : ψ (a * b) = ψ b * ψ a := ψ.map_mul' a b
@[simp] theorem map_one : ψ 1 = 1 := ψ.map_one'
@[simp] theorem invol (a : A) : ψ (ψ a) = a := ψ.invol' a
theorem mem_grade {d : ℤ} {a : A} (ha : a ∈ 𝒜 d) : ψ a ∈ 𝒜 d := ψ.mem_grade' ha
@[simp] theorem map_add (a b : A) : ψ (a + b) = ψ a + ψ b := ψ.toLinearMap.map_add a b
@[simp] theorem map_zero : ψ 0 = 0 := ψ.toLinearMap.map_zero
@[simp] theorem map_neg (a : A) : ψ (-a) = -ψ a := ψ.toLinearMap.map_neg a
@[simp] theorem map_sub (a b : A) : ψ (a - b) = ψ a - ψ b := ψ.toLinearMap.map_sub a b
@[simp] theorem map_smul (c : k) (a : A) : ψ (c • a) = c • ψ a := ψ.toLinearMap.map_smul c a
@[simp] theorem map_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∑ i ∈ s, ψ (f i) := _root_.map_sum ψ.toLinearMap f s

theorem injective : Injective ψ := Function.LeftInverse.injective ψ.invol

@[simp] theorem eq_zero_iff {a : A} : ψ a = 0 ↔ a = 0 :=
  ⟨fun h => ψ.injective (h.trans ψ.map_zero.symm), fun h => h ▸ ψ.map_zero⟩

/-- `ψ` maps idempotents to idempotents. -/
theorem isIdempotentElem {e : A} (he : IsIdempotentElem e) : IsIdempotentElem (ψ e) := by
  rw [IsIdempotentElem, ← map_mul, he.eq]

end GradedAntiInvolution

end AntiInvolution

/-! ### The dual `M̄ = HOM(M, A)^ψ` -/

section Dual

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  (ψ : GradedAntiInvolution 𝒜)

/-- The underlying type of the dual `M̄ = HOM(M, A)^ψ` of an `A`-module `M` (KL I,
arXiv:0803.4121v2, §2.5): the `A`-linear maps `M → A`, a right `A`-module via right
multiplication in `A`, made into a left module through `ψ`: `(a • f)(m) = f(m) ψ(a)`. -/
def Dual (_ψ : GradedAntiInvolution 𝒜) (M : Type*) [AddCommGroup M] [Module A M] : Type _ :=
  M →ₗ[A] A

namespace Dual

variable {M : Type*} [AddCommGroup M] [Module A M]

instance : AddCommGroup (Dual ψ M) := inferInstanceAs (AddCommGroup (M →ₗ[A] A))
instance : Module k (Dual ψ M) := inferInstanceAs (Module k (M →ₗ[A] A))
instance : FunLike (Dual ψ M) M A := inferInstanceAs (FunLike (M →ₗ[A] A) M A)
instance : LinearMapClass (Dual ψ M) A M A := inferInstanceAs (LinearMapClass (M →ₗ[A] A) A M A)

variable {ψ}

/-- An element of `M̄` as an `A`-linear map `M → A`. -/
def toHom (f : Dual ψ M) : M →ₗ[A] A := f

variable (ψ) in
/-- An `A`-linear map `M → A` as an element of `M̄`. -/
def ofHom (f : M →ₗ[A] A) : Dual ψ M := f

@[simp] theorem toHom_apply (f : Dual ψ M) (m : M) : toHom f m = f m := rfl
@[simp] theorem ofHom_apply (f : M →ₗ[A] A) (m : M) : ofHom ψ f m = f m := rfl

@[ext] theorem ext {f g : Dual ψ M} (h : ∀ m, f m = g m) : f = g := LinearMap.ext h

@[simp] theorem add_apply (f g : Dual ψ M) (m : M) : (f + g) m = f m + g m := rfl
@[simp] theorem zero_apply (m : M) : (0 : Dual ψ M) m = 0 := rfl
@[simp] theorem neg_apply (f : Dual ψ M) (m : M) : (-f) m = -f m := rfl
@[simp] theorem sub_apply (f g : Dual ψ M) (m : M) : (f - g) m = f m - g m := rfl
@[simp] theorem kSMul_apply (c : k) (f : Dual ψ M) (m : M) : (c • f) m = c • f m := rfl
@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Dual ψ M) (m : M) :
    (∑ i ∈ s, f i) m = ∑ i ∈ s, f i m :=
  LinearMap.sum_apply (M := M) (M₂ := A) s f m

variable (ψ) in
instance : SMul A (Dual ψ M) :=
  ⟨fun a f => ofHom ψ ((LinearMap.toSpanSingleton A A (ψ a)).comp (toHom f))⟩

/-- `(a • f)(m) = f(m) ψ(a)`. -/
@[simp] theorem smul_apply (a : A) (f : Dual ψ M) (m : M) : (a • f) m = f m * ψ a := rfl

variable (ψ) in
instance : Module A (Dual ψ M) where
  one_smul f := ext fun m => by simp
  mul_smul a b f := ext fun m => by simp [mul_assoc]
  smul_zero a := ext fun m => by simp
  smul_add a f g := ext fun m => by simp [add_mul]
  add_smul a b f := ext fun m => by simp [mul_add]
  zero_smul f := ext fun m => by simp

variable (ψ) in
instance : IsScalarTower k A (Dual ψ M) where
  smul_assoc c a f := ext fun m => by simp

end Dual

variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The grading of `M̄ = HOM(M, A)^ψ`: `M̄_d = HOM(M, A)_d` (maps raising degrees by `d`). -/
def dualGrading (ℳ : ℤ → Submodule k M) : ℤ → Submodule k (Dual ψ M) := homGrade A ℳ 𝒜

omit [IsScalarTower k A M] in
variable {ψ} in
@[simp] theorem mem_dualGrading {ℳ : ℤ → Submodule k M} {d : ℤ} {f : Dual ψ M} :
    f ∈ dualGrading ψ ℳ d ↔ ∀ ⦃e : ℤ⦄ ⦃x : M⦄, x ∈ ℳ e → f x ∈ 𝒜 (e + d) := Iff.rfl

instance [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M) :
    SetLike.GradedSMul 𝒜 (dualGrading ψ ℳ) where
  smul_mem i j a f ha hf e x hx := by
    rw [Dual.smul_apply, vadd_eq_add, ← add_assoc, add_right_comm]
    exact SetLike.GradedMul.mul_mem (hf hx) (ψ.mem_grade ha)

instance [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite A M] : Decomposition (dualGrading ψ ℳ) :=
  (isInternal_homGrade 𝒜 ℳ 𝒜).chooseDecomposition

end Dual

/-! ### Dual bases of finitely generated projective modules -/

section DualBasis

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

/-- A finitely generated projective module has a finite **dual basis**: elements `x_i ∈ M` and
`f_i : M → A` with `m = ∑ᵢ f_i(m) x_i`. -/
theorem exists_dualBasis [Module.Finite A M] [Module.Projective A M] :
    ∃ (n : ℕ) (x : Fin n → M) (f : Fin n → (M →ₗ[A] A)), ∀ m, ∑ i, f i m • x i = m := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i => π fun j => if i = j then 1 else 0, fun i => (LinearMap.proj i).comp s,
    fun m => ?_⟩
  have hm : π (s m) = m := LinearMap.congr_fun hs m
  conv_rhs => rw [← hm, pi_eq_sum_univ (s m), map_sum]
  simp only [LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, map_smul]

end DualBasis

/-! ### `M̄` is finitely generated projective, and `M̄̄ ≅ M` -/

section DualProjective

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  (ψ : GradedAntiInvolution 𝒜) {M : Type*} [AddCommGroup M] [Module A M]

namespace Dual

/-- For a dual basis `(x_i, f_i)` of `M`, every `f ∈ M̄` is `∑ᵢ ψ(f(x_i)) • f_i`. -/
theorem eq_sum_of_dualBasis {n : ℕ} {x : Fin n → M} {g : Fin n → (M →ₗ[A] A)}
    (hxg : ∀ m, ∑ i, g i m • x i = m) (f : Dual ψ M) :
    f = ∑ i, ψ (f (x i)) • ofHom ψ (g i) := by
  ext m
  rw [sum_apply]
  conv_lhs => rw [← hxg m, map_sum]
  simp [map_smul]

/-- The map `M̄ → Aⁿ`, `f ↦ (ψ(f(x_i)))_i`. -/
def toPi {n : ℕ} (x : Fin n → M) : Dual ψ M →ₗ[A] (Fin n → A) where
  toFun f i := ψ (f (x i))
  map_add' f f' := funext fun i => by simp
  map_smul' a f := funext fun i => by simp [smul_eq_mul]

/-- The map `Aⁿ → M̄`, `v ↦ ∑ᵢ v_i • f_i`. -/
def ofPi {n : ℕ} (g : Fin n → (M →ₗ[A] A)) : (Fin n → A) →ₗ[A] Dual ψ M where
  toFun v := ∑ i, v i • ofHom ψ (g i)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, mul_smul]

instance [Module.Finite A M] [Module.Projective A M] : Module.Finite A (Dual ψ M) := by
  obtain ⟨n, x, g, hxg⟩ := exists_dualBasis (A := A) (M := M)
  exact Module.Finite.of_surjective (ofPi ψ g) fun f =>
    ⟨toPi ψ x f, (eq_sum_of_dualBasis ψ hxg f).symm⟩

instance [Module.Finite A M] [Module.Projective A M] : Module.Projective A (Dual ψ M) := by
  obtain ⟨n, x, g, hxg⟩ := exists_dualBasis (A := A) (M := M)
  exact Module.Projective.of_split (toPi ψ x) (ofPi ψ g)
    (LinearMap.ext fun f => (eq_sum_of_dualBasis ψ hxg f).symm)

/-- The evaluation map `M → M̄̄`, `m ↦ (f ↦ ψ(f(m)))`. -/
def ev : M →ₗ[A] Dual ψ (Dual ψ M) where
  toFun m := ofHom ψ
    { toFun := fun f => ψ (f m)
      map_add' := fun f f' => by simp
      map_smul' := fun a f => by simp [smul_eq_mul] }
  map_add' m m' := ext fun f => by simp
  map_smul' a m := ext fun f => by simp [map_smul, smul_eq_mul]

@[simp] theorem ev_apply (m : M) (f : Dual ψ M) : ev ψ m f = ψ (f m) := rfl

theorem ev_injective [Module.Finite A M] [Module.Projective A M] : Injective (ev ψ (M := M)) := by
  obtain ⟨n, x, g, hxg⟩ := exists_dualBasis (A := A) (M := M)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  have h : ∀ i, g i m = 0 := fun i => by
    have := congrArg (fun Φ : Dual ψ (Dual ψ M) => Φ (ofHom ψ (g i))) hm
    simpa using this
  rw [← hxg m]
  simp [h]

theorem ev_surjective [Module.Finite A M] [Module.Projective A M] :
    Surjective (ev ψ (M := M)) := by
  obtain ⟨n, x, g, hxg⟩ := exists_dualBasis (A := A) (M := M)
  intro Φ
  refine ⟨∑ i, ψ (Φ (ofHom ψ (g i))) • x i, ext fun f => ?_⟩
  conv_rhs => rw [eq_sum_of_dualBasis ψ hxg f, map_sum]
  simp [map_smul, smul_eq_mul]

theorem ev_bijective [Module.Finite A M] [Module.Projective A M] : Bijective (ev ψ (M := M)) :=
  ⟨ev_injective ψ, ev_surjective ψ⟩

end Dual

end DualProjective

/-! ### The dual in `A-pmod` -/

section GProjDual

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] (ψ : GradedAntiInvolution 𝒜)

namespace Dual

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The transpose `N̄ → M̄`, `f ↦ f ∘ g`, of an `A`-linear map `g : M → N`. -/
def dualMap (g : M →ₗ[A] N) : Dual ψ N →ₗ[A] Dual ψ M where
  toFun f := ofHom ψ ((toHom f).comp g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [GradedAlgebra 𝒜] in
@[simp] theorem dualMap_apply (g : M →ₗ[A] N) (f : Dual ψ N) (m : M) :
    dualMap ψ g f m = f (g m) := rfl

omit [GradedAlgebra 𝒜] in
theorem dualMap_preservesGrading [Module k M] [Module k N] {ℳ : ℤ → Submodule k M}
    {𝒩 : ℤ → Submodule k N} {g : M →ₗ[A] N} (hg : PreservesGrading ℳ 𝒩 g) :
    PreservesGrading (dualGrading ψ 𝒩) (dualGrading ψ ℳ) (dualMap ψ g) :=
  fun _ _ hf _ _ hx => hf (hg hx)

end Dual

open Dual

namespace GProj

/-- **The dual `P̄ = HOM(P, A)^ψ`** of a finitely generated graded projective module (KL I,
arXiv:0803.4121v2, §2.5, for `A = R(ν)`), again an object of `A-pmod`. -/
abbrev dual (P : GProj 𝒜) : GProj 𝒜 where
  carrier := Dual ψ P.carrier
  grading := dualGrading ψ P.grading

theorem dual_carrier (P : GProj 𝒜) : (P.dual ψ).carrier = Dual ψ P.carrier := rfl

theorem dual_grading (P : GProj 𝒜) : (P.dual ψ).grading = dualGrading ψ P.grading := rfl

variable {ψ}

/-- `¯` is a contravariant functor on isomorphisms: `P ≅ P'` gives `P̄' ≅ P̄`. -/
def dualCongr {P P' : GProj 𝒜} (e : P.Iso P') : (P'.dual ψ).Iso (P.dual ψ) :=
  GradedEquiv.ofLinearMaps (dualMap ψ e.toLinearEquiv.toLinearMap)
    (dualMap ψ e.toLinearEquiv.symm.toLinearMap)
    (fun f => ext fun m => congrArg f (e.toLinearEquiv.apply_symm_apply m))
    (fun f => ext fun m => congrArg f (e.toLinearEquiv.symm_apply_apply m))
    (dualMap_preservesGrading ψ e.map_mem') (dualMap_preservesGrading ψ e.symm_map_mem')

variable (ψ)

/-- `\overline{P ⊕ Q} ≅ P̄ ⊕ Q̄`. -/
def dualProd (P Q : GProj 𝒜) : ((P.prod Q).dual ψ).Iso ((P.dual ψ).prod (Q.dual ψ)) :=
  GradedEquiv.ofLinearMaps
    (LinearMap.prod (dualMap ψ (LinearMap.inl A P.carrier Q.carrier))
      (dualMap ψ (LinearMap.inr A P.carrier Q.carrier)))
    { toFun := fun (fg : Dual ψ P.carrier × Dual ψ Q.carrier) =>
        ofHom ψ (LinearMap.coprod (toHom fg.1) (toHom fg.2))
      map_add' := fun fg fg' => ext fun m => by
        change (fg.1 + fg'.1) m.1 + (fg.2 + fg'.2) m.2 =
          (fg.1 m.1 + fg.2 m.2) + (fg'.1 m.1 + fg'.2 m.2)
        rw [Dual.add_apply, Dual.add_apply]
        abel
      map_smul' := fun a fg => ext fun m => by
        change (a • fg.1) m.1 + (a • fg.2) m.2 = (fg.1 m.1 + fg.2 m.2) * ψ a
        simp only [Dual.smul_apply, add_mul] }
    (fun f => ext fun m => by
      obtain ⟨m₁, m₂⟩ := m
      change f (m₁, 0) + f (0, m₂) = f (m₁, m₂)
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add])
    (fun fg => Prod.ext
      (ext fun m => by
        change fg.1 m + fg.2 0 = fg.1 m
        rw [map_zero, add_zero])
      (ext fun m => by
        change fg.1 0 + fg.2 m = fg.2 m
        rw [map_zero, zero_add]))
    (fun d f hf => ⟨dualMap_preservesGrading ψ (ℳ := P.grading) (𝒩 := (P.prod Q).grading)
        (fun _ _ hx => ⟨hx, zero_mem _⟩) hf,
      dualMap_preservesGrading ψ (ℳ := Q.grading) (𝒩 := (P.prod Q).grading)
        (fun _ _ hx => ⟨zero_mem _, hx⟩) hf⟩)
    (fun d fg hfg e x hx => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ofHom_apply, LinearMap.coprod_apply,
        toHom_apply]
      exact add_mem (hfg.1 hx.1) (hfg.2 hx.2))

/-- `\overline{P{a}} ≅ P̄{-a}`. -/
def dualShift (P : GProj 𝒜) (a : ℤ) : ((P.shift a).dual ψ).Iso ((P.dual ψ).shift (-a)) where
  toLinearEquiv := LinearEquiv.refl A (Dual ψ P.carrier)
  map_mem' d f hf e x hx := by
    have h := hf (e := e + a) (x := x)
      (show x ∈ P.grading (e + a - a) by rwa [add_sub_cancel_right])
    convert h using 2
    ring
  symm_map_mem' d f hf e x hx := by
    have h := hf (e := e - a) (x := x) hx
    convert h using 2
    ring

/-- **`P̄̄ ≅ P`** (via `m ↦ (f ↦ ψ(f(m)))`). -/
def dualDual (P : GProj 𝒜) : P.Iso ((P.dual ψ).dual ψ) :=
  GradedEquiv.ofPreserves (LinearEquiv.ofBijective (ev ψ) (ev_bijective ψ))
    fun e m hm j f hf => by
      change ψ (f m) ∈ 𝒜 (j + e)
      rw [add_comm]
      exact ψ.mem_grade (hf hm)

@[simp] theorem dualDual_apply (P : GProj 𝒜) (m : P.carrier) (f : Dual ψ P.carrier) :
    P.dualDual ψ m f = ψ (f m) := rfl

theorem apply_dualDual_symm (P : GProj 𝒜) (Φ : Dual ψ (Dual ψ P.carrier))
    (f : Dual ψ P.carrier) : f ((P.dualDual ψ).symm Φ) = ψ (Φ f) := by
  have h : P.dualDual ψ ((P.dualDual ψ).symm Φ) = Φ :=
    (P.dualDual ψ).toLinearEquiv.apply_symm_apply Φ
  conv_rhs => rw [← h]
  change f _ = ψ (ψ (f _))
  rw [ψ.invol]

/-- **`\overline{A e} ≅ A ψ(e)`** for a degree-zero idempotent `e` (via `f ↦ ψ(f(e))`). -/
def dualOfIdempotent {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    ((ofIdempotent e he he0).dual ψ).Iso
      (ofIdempotent (ψ e) (ψ.isIdempotentElem he) (ψ.mem_grade he0)) :=
  let ε : leftIdeal e := ⟨e, he.eq⟩
  GradedEquiv.ofLinearMaps (M := Dual ψ (leftIdeal e)) (N := leftIdeal (ψ e))
    { toFun := fun f => ⟨ψ (f ε), by
        show ψ _ * ψ e = ψ _
        rw [← ψ.map_mul]
        congr 1
        rw [← smul_eq_mul, ← map_smul]
        congr 1
        exact Subtype.ext he.eq⟩
      map_add' := fun f f' => Subtype.ext (by simp only [Dual.add_apply, ψ.map_add]; rfl)
      map_smul' := fun a f => Subtype.ext (by
        simp only [Dual.smul_apply, ψ.map_mul, ψ.invol, RingHom.id_apply]; rfl) }
    { toFun := fun b => ofHom ψ ((LinearMap.toSpanSingleton A A (ψ (b : A))).comp
        (leftIdeal e).subtype)
      map_add' := fun b b' => ext fun x => by simp [mul_add]
      map_smul' := fun a b => ext fun x => by simp [smul_eq_mul, mul_assoc] }
    (fun f => ext fun x => by
      change (x : A) * ψ (ψ (f ε)) = f x
      rw [ψ.invol, ← smul_eq_mul, ← map_smul]
      congr 1
      exact Subtype.ext (mem_leftIdeal.1 x.2))
    (fun b => Subtype.ext (by
      change ψ (e * ψ (b : A)) = b
      rw [ψ.map_mul, ψ.invol]
      exact mem_leftIdeal.1 b.2))
    (fun d f hf => by
      have := hf (e := 0) (x := ε) he0
      rw [zero_add] at this
      exact ψ.mem_grade this)
    (fun d b hb m (x : leftIdeal e) hx => by
      change (x : A) * ψ (b : A) ∈ 𝒜 (m + d)
      exact SetLike.GradedMul.mul_mem hx (ψ.mem_grade hb))

end GProj

end GProjDual

/-! ### The bar involution on `K₀` -/

section Bar

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] (ψ : GradedAntiInvolution 𝒜)

open GProj

/-- Duality on isomorphism classes. -/
def GProj.IsoClass.dual : IsoClass 𝒜 → IsoClass 𝒜 :=
  Quotient.map (fun P => P.dual ψ) fun _ _ ⟨e⟩ => ⟨(dualCongr e).symm⟩

@[simp] theorem GProj.IsoClass.dual_isoClass (P : GProj 𝒜) :
    IsoClass.dual ψ (isoClass P) = isoClass (P.dual ψ) := rfl

namespace K0

/-- **The bar involution** `x ↦ x̄` on `K₀(A)`, `[P] ↦ [P̄]` with `P̄ = HOM(P, A)^ψ`
(KL I, arXiv:0803.4121v2, §2.5). It is additive, antilinear (`bar_T_smul`, `bar_smul`) and an
involution (`bar_bar`). -/
def bar : K0 𝒜 →+ K0 𝒜 :=
  QuotientAddGroup.map _ _ (FreeAbelianGroup.map (IsoClass.dual ψ)) <| by
    rw [relSubgroup, AddSubgroup.closure_le]
    rintro _ ⟨P, Q, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨P.dual ψ, Q.dual ψ, ?_⟩
    simp only [map_sub, FreeAbelianGroup.map_of_apply, IsoClass.dual_isoClass]
    rw [isoClass_eq (dualProd ψ P Q)]

@[simp] theorem bar_of (P : GProj 𝒜) : bar ψ (of P) = of (P.dual ψ) := rfl

/-- `\overline{q^a x} = q^{-a} x̄`. -/
theorem bar_T_smul (a : ℤ) (x : K0 𝒜) :
    bar ψ ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) =
      (LaurentPolynomial.T (-a) : LaurentPolynomial ℤ) • bar ψ x := by
  rw [T_smul, T_smul]
  induction x using induction_on with
  | of P => rw [shiftHom_of, bar_of, bar_of, shiftHom_of]; exact of_eq_of_iso (dualShift ψ P a)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | neg x hx => rw [map_neg, map_neg, hx, map_neg, map_neg]

/-- `\overline{p x} = p̄ x̄`, where `p̄(q) = p(q⁻¹)` (`LaurentPolynomial.invert`). -/
theorem bar_smul (p : LaurentPolynomial ℤ) (x : K0 𝒜) :
    bar ψ (p • x) = LaurentPolynomial.invert p • bar ψ x := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_smul]
  | single n m =>
    have hT : ∀ n : ℤ, (Finsupp.single n m : LaurentPolynomial ℤ) =
        m • (LaurentPolynomial.T n : LaurentPolynomial ℤ) := fun n => by
      rw [LaurentPolynomial.T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, smul_assoc, map_zsmul, bar_T_smul, map_zsmul, LaurentPolynomial.invert_T,
      smul_assoc]

/-- **`x̄̄ = x`** (from `P̄̄ ≅ P`). -/
theorem bar_bar (x : K0 𝒜) : bar ψ (bar ψ x) = x := by
  induction x using induction_on with
  | of P => rw [bar_of, bar_of]; exact (of_eq_of_iso (dualDual ψ P)).symm
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | neg x hx => rw [map_neg, map_neg, hx]

theorem bar_involutive : Involutive (bar ψ) := bar_bar ψ

/-- **`\overline{[A e]} = [A ψ(e)]`** for a degree-zero idempotent `e`. -/
theorem bar_ofIdempotent {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    bar ψ (of (ofIdempotent e he he0)) =
      of (ofIdempotent (ψ e) (ψ.isIdempotentElem he) (ψ.mem_grade he0)) := by
  rw [bar_of]
  exact of_eq_of_iso (dualOfIdempotent ψ he he0)

/-- `[A e]` is bar-invariant if `ψ(e) = e`. -/
theorem bar_ofIdempotent_of_fixed {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
    (hψ : ψ e = e) : bar ψ (of (ofIdempotent e he he0)) = of (ofIdempotent e he he0) := by
  rw [bar_ofIdempotent]
  exact of_ofIdempotent_congr hψ _ _ _ _

/-- `[A] = [A 1]` is bar-invariant. -/
theorem bar_regular : bar ψ (of (GProj.regular 𝒜)) = of (GProj.regular 𝒜) := by
  rw [← of_eq_of_iso GProj.ofIdempotentOneIso,
    bar_ofIdempotent_of_fixed ψ _ _ ψ.map_one]

end K0

end Bar

/-! ### The transpose `HOM(P̄, Q) ≅ HOM(Q̄, P)` -/

section Transpose

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] {ψ : GradedAntiInvolution 𝒜}

open Dual

namespace GProj

/-- The transpose `HOM(P̄, Q)_d → HOM(Q̄, P)_d`, `φ ↦ ev_P⁻¹ ∘ φ^*` where
`φ^*(g) = g ∘ φ ∈ P̄̄` for `g ∈ Q̄`. -/
def dualTranspose (P Q : GProj 𝒜) (d : ℤ) :
    homGrade A (P.dual ψ).grading Q.grading d →ₗ[k]
      homGrade A (Q.dual ψ).grading P.grading d where
  toFun φ := ⟨(P.dualDual ψ).symm.toLinearEquiv.toLinearMap ∘ₗ
      dualMap ψ (φ : Dual ψ P.carrier →ₗ[A] Q.carrier), fun j g hg => by
    apply (P.dualDual ψ).symm_map_mem'
    intro m f hf
    change g ((φ : Dual ψ P.carrier →ₗ[A] Q.carrier) f) ∈ 𝒜 (m + (j + d))
    have := hg (φ.2 hf)
    rwa [show m + d + j = m + (j + d) by ring] at this⟩
  map_add' φ φ' := Subtype.ext (LinearMap.ext fun g => by
    simp only [LinearMap.coe_comp, comp_apply, Submodule.coe_add, LinearMap.add_apply]
    rw [← map_add]
    congr 1
    ext f
    simp)
  map_smul' c φ := Subtype.ext (LinearMap.ext fun g => by
    simp only [LinearMap.coe_comp, comp_apply, SetLike.val_smul, LinearMap.smul_apply,
      RingHom.id_apply]
    rw [← LinearMap.map_smul_of_tower]
    congr 1
    ext f
    exact LinearMap.map_smul_of_tower (toHom g) c _)

theorem dualTranspose_apply (P Q : GProj 𝒜) (d : ℤ)
    (φ : homGrade A (P.dual ψ).grading Q.grading d) (g : Dual ψ Q.carrier) :
    ((dualTranspose P Q d φ : homGrade A (Q.dual ψ).grading P.grading d) :
      Dual ψ Q.carrier →ₗ[A] P.carrier) g =
      (P.dualDual ψ).symm (dualMap ψ (φ : Dual ψ P.carrier →ₗ[A] Q.carrier) g) := rfl

/-- The transpose is an involution. -/
theorem dualTranspose_dualTranspose (P Q : GProj 𝒜) (d : ℤ)
    (φ : homGrade A (P.dual ψ).grading Q.grading d) :
    dualTranspose Q P d (dualTranspose P Q d φ) = φ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  rw [dualTranspose_apply]
  have h : dualMap ψ ((dualTranspose P Q d φ : homGrade A (Q.dual ψ).grading P.grading d) :
      Dual ψ Q.carrier →ₗ[A] P.carrier) f =
      Q.dualDual ψ ((φ : Dual ψ P.carrier →ₗ[A] Q.carrier) f) := by
    ext g
    rw [dualMap_apply, dualTranspose_apply, apply_dualDual_symm, dualMap_apply, dualDual_apply]
  rw [h]
  exact (Q.dualDual ψ).toLinearEquiv.symm_apply_apply _

/-- **`HOM(P̄, Q)_d ≅ HOM(Q̄, P)_d`**. -/
def dualTransposeEquiv (P Q : GProj 𝒜) (d : ℤ) :
    homGrade A (P.dual ψ).grading Q.grading d ≃ₗ[k]
      homGrade A (Q.dual ψ).grading P.grading d :=
  LinearEquiv.ofLinear (dualTranspose P Q d) (dualTranspose Q P d)
    (LinearMap.ext fun φ => dualTranspose_dualTranspose Q P d φ)
    (LinearMap.ext fun φ => dualTranspose_dualTranspose P Q d φ)

/-- **`gdim HOM(P̄, Q) = gdim HOM(Q̄, P)`**: the symmetry of KL I's pairing
`gdim (P^ψ ⊗_A Q)` on objects. -/
theorem homGdim_dual_comm (P Q : GProj 𝒜) :
    homGdim (P.dual ψ) Q = homGdim (Q.dual ψ) P :=
  gdim_eq_of_finrank_eq fun d => (dualTransposeEquiv P Q d).finrank_eq

end GProj

end Transpose

/-! ### The bilinear form of KL I -/

section PForm

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] [HasGdim 𝒜] (ψ : GradedAntiInvolution 𝒜)

open GProj

namespace K0

/-- **The bilinear form of KL I** (arXiv:0803.4121v2, §2.5, equation `eq_bil_pair2`),
`(x, y) = gdim HOM(x̄, y)`; on classes, `([P], [Q]) = gdim HOM(P̄, Q)`, which is
`gdim (P^ψ ⊗_A Q)` for `P` projective. It is `ℤ[q, q⁻¹]`-bilinear (`pform_smul_left`,
`pform_smul_right`) and symmetric (`pform_comm`); the sesquilinear form `homForm` is recovered
as `homForm x y = pform x̄ y` (`homForm_eq_pform`). -/
def pform : K0 𝒜 →+ K0 𝒜 →+ LaurentSeries ℤ := (homForm 𝒜).comp (bar ψ)

variable {𝒜}

theorem pform_apply (x y : K0 𝒜) : pform 𝒜 ψ x y = homForm 𝒜 (bar ψ x) y := rfl

@[simp] theorem pform_of (P Q : GProj 𝒜) :
    pform 𝒜 ψ (of P) (of Q) = homGdim (P.dual ψ) Q := by
  rw [pform_apply, bar_of, homForm_of]

theorem homForm_eq_pform (x y : K0 𝒜) : homForm 𝒜 x y = pform 𝒜 ψ (bar ψ x) y := by
  rw [pform_apply, bar_bar]

/-- **The form is symmetric**: `(x, y) = (y, x)`. -/
theorem pform_comm (x y : K0 𝒜) : pform 𝒜 ψ x y = pform 𝒜 ψ y x := by
  induction x using induction_on with
  | of P =>
    induction y using induction_on with
    | of Q => rw [pform_of, pform_of, homGdim_dual_comm]
    | zero => simp
    | add y y' hy hy' => rw [map_add, hy, hy', map_add, AddMonoidHom.add_apply]
    | neg y hy => rw [map_neg, hy, map_neg, AddMonoidHom.neg_apply]
  | zero => simp
  | add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx', map_add]
  | neg x hx => rw [map_neg, AddMonoidHom.neg_apply, hx, map_neg]

/-- `(q^a x, y) = q^a (x, y)`. -/
theorem pform_T_smul_left (a : ℤ) (x y : K0 𝒜) :
    pform 𝒜 ψ ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) y =
      HahnSeries.single a 1 * pform 𝒜 ψ x y := by
  rw [pform_apply, bar_T_smul, homForm_T_smul_left, neg_neg, pform_apply]

/-- `(x, q^a y) = q^a (x, y)`. -/
theorem pform_T_smul_right (a : ℤ) (x y : K0 𝒜) :
    pform 𝒜 ψ x ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • y) =
      HahnSeries.single a 1 * pform 𝒜 ψ x y := by
  rw [pform_apply, homForm_T_smul_right, pform_apply]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem toLaurentSeries_T (a : ℤ) :
    toLaurentSeries (LaurentPolynomial.T a : LaurentPolynomial ℤ) = HahnSeries.single a 1 := by
  have := toLaurentSeries_T_mul (R := ℤ) a 1
  rwa [mul_one, show toLaurentSeries (1 : LaurentPolynomial ℤ) = 1 by
    ext d
    rw [coeff_toLaurentSeries, HahnSeries.coeff_one, ← LaurentPolynomial.T_zero,
      LaurentPolynomial.T, Finsupp.single_apply]
    split_ifs <;> first | rfl | omega, mul_one] at this

omit [Algebra k A] [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- An additive `F` with `F (q^a x) = q^a F x` satisfies `F (p x) = p F x`. -/
theorem map_smul_of_T {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M]
    {F : M →+ LaurentSeries ℤ}
    (hF : ∀ (a : ℤ) (x : M),
      F ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) = HahnSeries.single a 1 * F x)
    (p : LaurentPolynomial ℤ) (x : M) : F (p • x) = toLaurentSeries p * F x := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_mul]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) =
        m • (LaurentPolynomial.T n : LaurentPolynomial ℤ) := by
      rw [LaurentPolynomial.T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, smul_assoc, map_zsmul, hF, map_zsmul, toLaurentSeries_T, smul_mul_assoc]

/-- **`ℤ[q, q⁻¹]`-linearity in the first variable**: `(p x, y) = p (x, y)`. -/
theorem pform_smul_left (p : LaurentPolynomial ℤ) (x y : K0 𝒜) :
    pform 𝒜 ψ (p • x) y = toLaurentSeries p * pform 𝒜 ψ x y :=
  map_smul_of_T (F := (pform 𝒜 ψ).flip y) (fun a x => pform_T_smul_left ψ a x y) p x

/-- **`ℤ[q, q⁻¹]`-linearity in the second variable**: `(x, p y) = p (x, y)`. -/
theorem pform_smul_right (p : LaurentPolynomial ℤ) (x y : K0 𝒜) :
    pform 𝒜 ψ x (p • y) = toLaurentSeries p * pform 𝒜 ψ x y :=
  map_smul_of_T (F := pform 𝒜 ψ x) (fun a y => pform_T_smul_right ψ a x y) p y

/-- `([A e], y) = ([A ψ(e)], y)_{homForm}`. -/
theorem pform_ofIdempotent_left {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
    (y : K0 𝒜) : pform 𝒜 ψ (of (ofIdempotent e he he0)) y =
      homForm 𝒜 (of (ofIdempotent (ψ e) (ψ.isIdempotentElem he) (ψ.mem_grade he0))) y := by
  rw [pform_apply, bar_ofIdempotent]

/-- **`([A e], [Q]) = gdim (ψ(e) Q)`** for a degree-zero idempotent `e`. -/
theorem pform_ofIdempotent {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (Q : GProj 𝒜) :
    pform 𝒜 ψ (of (ofIdempotent e he he0)) (of Q) = gdim (idem Q.grading (ψ e)) := by
  rw [pform_ofIdempotent_left, homForm_ofIdempotent]

/-- **`([A e], [A e']) = gdim (ψ(e) A e')`**; for `ψ(e) = e` this is `gdim (e A e')`. -/
theorem pform_ofIdempotent_ofIdempotent {e e' : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
    (he' : IsIdempotentElem e') (he0' : e' ∈ 𝒜 0) :
    pform 𝒜 ψ (of (ofIdempotent e he he0)) (of (ofIdempotent e' he' he0')) =
      gdim (idem (ofIdempotent e' he' he0').grading (ψ e)) :=
  pform_ofIdempotent ψ he he0 _

/-- Bar-invariant classes: on them `pform` and `homForm` agree in the first variable. -/
theorem pform_eq_homForm_of_bar_eq {x : K0 𝒜} (hx : bar ψ x = x) (y : K0 𝒜) :
    pform 𝒜 ψ x y = homForm 𝒜 x y := by
  rw [pform_apply, hx]

end K0

end PForm

end Categorification.Graded
