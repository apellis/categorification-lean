/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Module
import Categorification.Algebra.BalancedTensor

/-!
# Gradings on tensor products and balanced tensor products

The graded-module constructions needed for induction functors (Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6).

* `Graded.map 𝒳 π` : for a surjective `k`-linear map `π : X → Y` whose kernel is homogeneous,
  the grading `d ↦ π (𝒳 d)` of `Y` (`Graded.mapDecomposition`). This covers quotients by
  homogeneous submodules. If `π` is `B`-equivariant and `X` is a graded `B`-module, so is `Y`
  (`Graded.gradedSMul_map`).
* `Graded.GradedEquiv.ofPreserves` : a linear isomorphism between graded modules whose forward
  map is degree-preserving is a graded isomorphism.
* `Graded.tensorGrading ℳ 𝒩` : the grading of `M ⊗[k] N` with
  `(M ⊗ N)_d = span {m ⊗ n | m ∈ M_i, n ∈ N_j, i + j = d}`; it is a `Decomposition` (an
  instance), compatible with a left action on `M` (`SetLike.GradedSMul` instance) and with
  grading shifts (`tensorGrading_shift_left`, `tensorGrading_shift_right`).
* `Graded.balancedGrading ℳ 𝒩` : the induced grading of the balanced tensor product
  `M ⊗_A N` (`Categorification.BalancedTensor`) over a graded algebra `(A, 𝒜)`, when the right
  action of `A` on `M` and the left action on `N` are graded. It is a `Decomposition`
  (`balancedDecomposition`), and `M ⊗_A N` is a graded `B`-module if `M` is
  (`gradedSMul_balanced`).
-/

noncomputable section

namespace Categorification.Graded

open DirectSum
open scoped TensorProduct

/-! ### Gradings pushed forward along surjections -/

section Map

variable {ι k X Y : Type*} [CommRing k] [AddCommGroup X] [Module k X] [AddCommGroup Y]
  [Module k Y] (𝒳 : ι → Submodule k X) (π : X →ₗ[k] Y)

/-- The grading `d ↦ π (𝒳 d)` of the target of `π`. -/
def map : ι → Submodule k Y := fun d => (𝒳 d).map π

theorem mem_map_of_mem {x : X} {d : ι} (hx : x ∈ 𝒳 d) : π x ∈ map 𝒳 π d :=
  Submodule.mem_map_of_mem hx

/-- The restriction `𝒳 d → π (𝒳 d)`. -/
def mapRestrict (d : ι) : 𝒳 d →ₗ[k] map 𝒳 π d := π.submoduleMap (𝒳 d)

@[simp] theorem coe_mapRestrict (d : ι) (x : 𝒳 d) : (mapRestrict 𝒳 π d x : Y) = π x := rfl

variable [DecidableEq ι]

/-- The componentwise map `⨁ d, 𝒳 d → ⨁ d, π (𝒳 d)`. -/
def mapDirectSum : (⨁ d, 𝒳 d) →ₗ[k] ⨁ d, map 𝒳 π d :=
  DirectSum.toModule k ι _ fun d =>
    (DirectSum.lof k ι (fun d => map 𝒳 π d) d).comp (mapRestrict 𝒳 π d)

theorem mapDirectSum_of (d : ι) (x : 𝒳 d) :
    mapDirectSum 𝒳 π (DirectSum.of _ d x) = DirectSum.of _ d (mapRestrict 𝒳 π d x) := by
  rw [mapDirectSum, ← DirectSum.lof_eq_of k, toModule_lof, LinearMap.comp_apply,
    DirectSum.lof_eq_of]

theorem mapDirectSum_apply (y : ⨁ d, 𝒳 d) (e : ι) :
    mapDirectSum 𝒳 π y e = mapRestrict 𝒳 π e (y e) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of d x =>
    rw [mapDirectSum_of]
    by_cases h : d = e
    · subst h; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ h, DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  | add y z hy hz => rw [map_add, DirectSum.add_apply, hy, hz, DirectSum.add_apply, map_add]

omit [DecidableEq ι] in
theorem coeAddMonoidHom_eq_coeLinearMap {Z : Type*} [AddCommGroup Z] [Module k Z]
    (𝒵 : ι → Submodule k Z) [DecidableEq ι] (z : ⨁ d, 𝒵 d) :
    DirectSum.coeAddMonoidHom 𝒵 z = DirectSum.coeLinearMap 𝒵 z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of d x => rw [coeAddMonoidHom_of, coeLinearMap_of]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem coe_mapDirectSum (y : ⨁ d, 𝒳 d) :
    DirectSum.coeAddMonoidHom (map 𝒳 π) (mapDirectSum 𝒳 π y) =
      π (DirectSum.coeAddMonoidHom 𝒳 y) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of d x => rw [mapDirectSum_of, coeAddMonoidHom_of, coeAddMonoidHom_of, coe_mapRestrict]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

variable [Decomposition 𝒳]

/-- The decomposition of `π x` computed from that of `x`. -/
def mapDecomposeAux : X →ₗ[k] ⨁ d, map 𝒳 π d :=
  (mapDirectSum 𝒳 π).comp (decomposeLinearEquiv 𝒳).toLinearMap

theorem mapDecomposeAux_apply (x : X) :
    mapDecomposeAux 𝒳 π x = mapDirectSum 𝒳 π (decompose 𝒳 x) := rfl

variable {𝒳 π}

theorem ker_le_ker_mapDecomposeAux
    (hker : ∀ x, π x = 0 → ∀ d, π (decompose 𝒳 x d : X) = 0) :
    LinearMap.ker π ≤ LinearMap.ker (mapDecomposeAux 𝒳 π) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  ext e : 1
  rw [mapDecomposeAux_apply, mapDirectSum_apply, DirectSum.zero_apply]
  exact Subtype.ext (hker x hx e)

/-- The decomposition map of the pushed-forward grading. -/
def mapDecompose (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 0 → ∀ d, π (decompose 𝒳 x d : X) = 0) : Y →ₗ[k] ⨁ d, map 𝒳 π d :=
  ((LinearMap.ker π).liftQ (mapDecomposeAux 𝒳 π) (ker_le_ker_mapDecomposeAux hker)).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem mapDecompose_apply (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 0 → ∀ d, π (decompose 𝒳 x d : X) = 0) (x : X) :
    mapDecompose hπ hker (π x) = mapDirectSum 𝒳 π (decompose 𝒳 x) := by
  have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [mapDecompose, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply,
    mapDecomposeAux_apply]

/-- **The grading of `Y` pushed forward along a surjection `π : X → Y` with homogeneous
kernel.** -/
def mapDecomposition (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 0 → ∀ d, π (decompose 𝒳 x d : X) = 0) : Decomposition (map 𝒳 π) where
  decompose' := mapDecompose hπ hker
  left_inv y := by
    obtain ⟨x, rfl⟩ := hπ y
    rw [mapDecompose_apply, coe_mapDirectSum]
    congr 1
    exact (decompose 𝒳).symm_apply_apply x
  right_inv z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of d q =>
      obtain ⟨q, hq⟩ := q
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hq
      rw [coeAddMonoidHom_of, mapDecompose_apply, decompose_of_mem 𝒳 hx, mapDirectSum_of]
      rfl
    | add y z hy hz => rw [map_add, map_add, hy, hz]

omit [DecidableEq ι] [Decomposition 𝒳] in
/-- If `π` is equivariant for a graded action, the pushed-forward grading is compatible with
the action. -/
theorem gradedSMul_map [AddMonoid ι] {B : Type*} [SMul B X] [SMul B Y] {σ : Type*} [SetLike σ B]
    (ℬ : ι → σ) [SetLike.GradedSMul ℬ 𝒳] (hπ : ∀ (b : B) (x : X), π (b • x) = b • π x) :
    SetLike.GradedSMul ℬ (map 𝒳 π) where
  smul_mem i j b y hb hy := by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hπ]
    exact Submodule.mem_map_of_mem (SetLike.GradedSMul.smul_mem hb hx)

end Map

/-! ### Isomorphisms whose forward map is degree-preserving -/

section OfPreserves

variable {ι k A M N : Type*} [CommRing k] [Semiring A] [AddCommGroup M] [Module k M]
  [Module A M] [AddCommGroup N] [Module k N] [Module A N] [DecidableEq ι]
  {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N} [Decomposition ℳ] [Decomposition 𝒩]

/-- A linear isomorphism between graded modules whose forward map is degree-preserving is a
graded isomorphism (the inverse is automatically degree-preserving). -/
def GradedEquiv.ofPreserves (e : M ≃ₗ[A] N) (he : PreservesGrading ℳ 𝒩 e.toLinearMap) :
    ℳ ≃ᵍ[A] 𝒩 where
  toLinearEquiv := e
  map_mem' _ _ hx := he hx
  symm_map_mem' d y hy := by
    have h1 : e (decompose ℳ (e.symm y) d : M) = y := by
      have := decompose_map he (e.symm y) d
      rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
        decompose_of_mem_same 𝒩 hy] at this
      exact this.symm
    have h2 : (decompose ℳ (e.symm y) d : M) = e.symm y :=
      e.injective (by rw [h1, LinearEquiv.apply_symm_apply])
    rw [← h2]
    exact (decompose ℳ (e.symm y) d).2

@[simp] theorem GradedEquiv.ofPreserves_apply (e : M ≃ₗ[A] N)
    (he : PreservesGrading ℳ 𝒩 e.toLinearMap) (x : M) : GradedEquiv.ofPreserves e he x = e x :=
  rfl

end OfPreserves

/-! ### Submodules spanned by homogeneous elements -/

section Span

variable {ι k X : Type*} [CommRing k] [AddCommGroup X] [Module k X] [DecidableEq ι]
  (𝒳 : ι → Submodule k X) [Decomposition 𝒳]

/-- The span of a set of homogeneous elements is homogeneous. -/
theorem decompose_mem_span_of_homogeneous {S : Set X} (hS : ∀ s ∈ S, ∃ e, s ∈ 𝒳 e) {x : X}
    (hx : x ∈ Submodule.span k S) (d : ι) : (decompose 𝒳 x d : X) ∈ Submodule.span k S := by
  induction hx using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨e, he⟩ := hS s hs
    by_cases h : e = d
    · subst h; rw [decompose_of_mem_same 𝒳 he]; exact Submodule.subset_span hs
    · rw [decompose_of_mem_ne 𝒳 he h]; exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [decompose_add, DirectSum.add_apply, Submodule.coe_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]
    exact Submodule.smul_mem _ c hx

end Span

/-! ### The tensor product grading -/

section Tensor

variable {ι k M N : Type*} [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N] [AddCommMonoid ι] (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N)

/-- The grading of `M ⊗[k] N`: `(M ⊗ N)_d` is spanned by the `m ⊗ n` with `m ∈ M_i`, `n ∈ N_j`,
`i + j = d`. -/
def tensorGrading (d : ι) : Submodule k (M ⊗[k] N) :=
  Submodule.span k
    {t | ∃ (i j : ι) (m : M) (n : N), i + j = d ∧ m ∈ ℳ i ∧ n ∈ 𝒩 j ∧ m ⊗ₜ[k] n = t}

variable {ℳ 𝒩} in
theorem tmul_mem_tensorGrading {i j : ι} {m : M} {n : N} (hm : m ∈ ℳ i) (hn : n ∈ 𝒩 j) :
    m ⊗ₜ[k] n ∈ tensorGrading ℳ 𝒩 (i + j) :=
  Submodule.subset_span ⟨i, j, m, n, rfl, hm, hn, rfl⟩

/-- A `k`-linear map out of `M ⊗ N` sending each `M_i ⊗ N_j` into `X_{i+j}` is
degree-preserving. -/
theorem tensorGrading_map_mem {X : Type*} [AddCommGroup X] [Module k X]
    (𝒳 : ι → Submodule k X) (f : M ⊗[k] N →ₗ[k] X)
    (hf : ∀ ⦃i j : ι⦄ ⦃m : M⦄ ⦃n : N⦄, m ∈ ℳ i → n ∈ 𝒩 j → f (m ⊗ₜ n) ∈ 𝒳 (i + j))
    ⦃d : ι⦄ ⦃t : M ⊗[k] N⦄ (ht : t ∈ tensorGrading ℳ 𝒩 d) : f t ∈ 𝒳 d := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, m, n, rfl, hm, hn, rfl⟩ := ht
    exact hf hm hn
  | zero => rw [map_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
  | smul c t _ ht => rw [map_smul]; exact Submodule.smul_mem _ c ht

/-- A left action on `M` is compatible with the tensor product grading. -/
instance gradedSMul_tensor {B : Type*} [Monoid B] [DistribMulAction B M] [SMulCommClass k B M]
    {σ : Type*} [SetLike σ B] (ℬ : ι → σ) [SetLike.GradedSMul ℬ ℳ] :
    SetLike.GradedSMul ℬ (tensorGrading ℳ 𝒩) where
  smul_mem i j b t hb ht := by
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨i', j', m, n, rfl, hm, hn, rfl⟩ := ht
      rw [TensorProduct.smul_tmul', vadd_eq_add, ← add_assoc]
      exact tmul_mem_tensorGrading (SetLike.GradedSMul.smul_mem hb hm) hn
    | zero => rw [smul_zero]; exact zero_mem _
    | add s t _ _ hs ht => rw [smul_add]; exact add_mem hs ht
    | smul c t _ ht => rw [← smul_comm c b t]; exact Submodule.smul_mem _ c ht

section Decomposition

variable [DecidableEq ι] [Decomposition ℳ] [Decomposition 𝒩]

/-- The bilinear map `M_i × N_j → (M ⊗ N)_{i+j}`, `(m, n) ↦ m ⊗ n`. -/
def tensorPairingAux (i j : ι) : ℳ i →ₗ[k] 𝒩 j →ₗ[k] tensorGrading ℳ 𝒩 (i + j) where
  toFun m := LinearMap.codRestrict _ ((TensorProduct.mk k M N (m : M)).comp (𝒩 j).subtype)
    (fun n => tmul_mem_tensorGrading m.2 n.2)
  map_add' m m' := by ext n; simp [TensorProduct.add_tmul]
  map_smul' c m := by ext n; simp [TensorProduct.smul_tmul']

/-- The bilinear map `M_i × N_j → ⨁ d, (M ⊗ N)_d`, `(m, n) ↦ m ⊗ n` in degree `i + j`. -/
def tensorPairing (i j : ι) : ℳ i →ₗ[k] 𝒩 j →ₗ[k] ⨁ d, tensorGrading ℳ 𝒩 d :=
  (tensorPairingAux ℳ 𝒩 i j).compr₂ (DirectSum.lof k ι (fun d => tensorGrading ℳ 𝒩 d) (i + j))

/-- The decomposition map of the tensor product grading. -/
def tensorDecompose : M ⊗[k] N →ₗ[k] ⨁ d, tensorGrading ℳ 𝒩 d :=
  TensorProduct.lift (LinearMap.compl₁₂
    (DirectSum.toModule k ι _ fun i =>
      (DirectSum.toModule k ι _ fun j => (tensorPairing ℳ 𝒩 i j).flip).flip)
    (decomposeLinearEquiv ℳ).toLinearMap (decomposeLinearEquiv 𝒩).toLinearMap)

variable {ℳ 𝒩} in
theorem tensorDecompose_tmul {i j : ι} {m : M} {n : N} (hm : m ∈ ℳ i) (hn : n ∈ 𝒩 j) :
    tensorDecompose ℳ 𝒩 (m ⊗ₜ n) =
      DirectSum.of (fun d => tensorGrading ℳ 𝒩 d) (i + j)
        ⟨m ⊗ₜ n, tmul_mem_tensorGrading hm hn⟩ := by
  rw [tensorDecompose, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, decomposeLinearEquiv_apply, decomposeLinearEquiv_apply,
    decompose_of_mem ℳ hm, decompose_of_mem 𝒩 hn, ← DirectSum.lof_eq_of k,
    ← DirectSum.lof_eq_of k, toModule_lof, LinearMap.flip_apply, toModule_lof,
    LinearMap.flip_apply]
  rfl


-- The default instance search for `Zero (⨁ d, tensorGrading ℳ 𝒩 d)` first explores (and
-- rejects) graded-ring structures, which is slow.
set_option synthInstance.maxHeartbeats 200000 in
instance tensorDecomposition : Decomposition (tensorGrading ℳ 𝒩) where
  decompose' := tensorDecompose ℳ 𝒩
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      induction m using Decomposition.inductionOn ℳ with
      | zero => simp
      | @homogeneous i m =>
        induction n using Decomposition.inductionOn 𝒩 with
        | zero => simp
        | @homogeneous j n =>
          rw [tensorDecompose_tmul m.2 n.2, coeAddMonoidHom_of]
        | add n n' hn hn' =>
          rw [TensorProduct.tmul_add, map_add, map_add, hn, hn']
      | add m m' hm hm' =>
        rw [TensorProduct.add_tmul, map_add, map_add, hm, hm']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv y := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | of d x =>
      obtain ⟨t, ht⟩ := x
      rw [coeAddMonoidHom_of]
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨i, j, m, n, rfl, hm, hn, rfl⟩ := ht
        exact tensorDecompose_tmul hm hn
      | zero =>
        rw [map_zero]
        exact (map_zero (DirectSum.of (fun d => tensorGrading ℳ 𝒩 d) d)).symm
      | add s t hs ht ihs iht =>
        rw [map_add, ihs, iht, ← map_add]; rfl
      | smul c t ht ih =>
        rw [map_smul, ih, ← DirectSum.lof_eq_of k, ← map_smul]; rfl
    | add y z hy hz => rw [map_add, map_add, hy, hz]

end Decomposition

/-! #### Shifts -/

section Shift

variable {ι : Type*} [AddCommGroup ι] (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N)

theorem tensorGrading_shift_left (a : ι) :
    tensorGrading (shift ℳ a) 𝒩 = shift (tensorGrading ℳ 𝒩) a := by
  funext d
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, j, m, n, rfl, hm, hn, rfl⟩
    have h := tmul_mem_tensorGrading (k := k) (show m ∈ ℳ (i - a) from hm) hn
    show m ⊗ₜ n ∈ tensorGrading ℳ 𝒩 (i + j - a)
    rwa [show i + j - a = i - a + j by abel]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, j, m, n, hd, hm, hn, rfl⟩
    have hm' : m ∈ shift ℳ a (i + a) := mem_shift_add.2 hm
    have h := tmul_mem_tensorGrading (k := k) hm' hn
    rwa [show i + a + j = d by rw [eq_sub_iff_add_eq] at hd; rw [← hd]; abel] at h

theorem tensorGrading_shift_right (a : ι) :
    tensorGrading ℳ (shift 𝒩 a) = shift (tensorGrading ℳ 𝒩) a := by
  funext d
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, j, m, n, rfl, hm, hn, rfl⟩
    have h := tmul_mem_tensorGrading (k := k) hm (show n ∈ 𝒩 (j - a) from hn)
    show m ⊗ₜ n ∈ tensorGrading ℳ 𝒩 (i + j - a)
    rwa [show i + j - a = i + (j - a) by abel]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, j, m, n, hd, hm, hn, rfl⟩
    have hn' : n ∈ shift 𝒩 a (j + a) := mem_shift_add.2 hn
    have h := tmul_mem_tensorGrading (k := k) hm hn'
    rwa [show i + (j + a) = d by rw [eq_sub_iff_add_eq] at hd; rw [← hd]; abel] at h

end Shift

end Tensor

/-! ### The grading of a balanced tensor product -/

section Balanced

open BalancedTensor MulOpposite

variable {ι : Type*} [AddCommMonoid ι] {k B A M N : Type*} [CommRing k] [Ring B] [Algebra k B]
  [Ring A] [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]

variable (B A) in
/-- The grading of `M ⊗_A N` induced by gradings of `M` and `N`: the image of the tensor product
grading of `M ⊗[k] N`. -/
def balancedGrading (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N) :
    ι → Submodule k (BalancedTensor k B A M N) :=
  map (tensorGrading ℳ 𝒩) ((BalancedTensor.mk k B A M N).restrictScalars k)

variable {ℳ : ι → Submodule k M} {𝒩 : ι → Submodule k N}

theorem tmul_mem_balancedGrading {i j : ι} {m : M} {n : N} (hm : m ∈ ℳ i) (hn : n ∈ 𝒩 j) :
    (tmul m n : BalancedTensor k B A M N) ∈ balancedGrading B A ℳ 𝒩 (i + j) :=
  mem_map_of_mem _ _ (tmul_mem_tensorGrading hm hn)

/-- A `k`-linear map out of `M ⊗_A N` sending each `tmul m n` with `m ∈ M_i`, `n ∈ N_j` into
`X_{i+j}` is degree-preserving. -/
theorem balancedGrading_map_mem {X : Type*} [AddCommGroup X] [Module k X]
    (𝒳 : ι → Submodule k X) (f : BalancedTensor k B A M N →ₗ[k] X)
    (hf : ∀ ⦃i j : ι⦄ ⦃m : M⦄ ⦃n : N⦄, m ∈ ℳ i → n ∈ 𝒩 j → f (tmul m n) ∈ 𝒳 (i + j))
    ⦃d : ι⦄ ⦃y : BalancedTensor k B A M N⦄ (hy : y ∈ balancedGrading B A ℳ 𝒩 d) : f y ∈ 𝒳 d := by
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 hy
  exact tensorGrading_map_mem ℳ 𝒩 𝒳 (f.comp ((BalancedTensor.mk k B A M N).restrictScalars k))
    (fun i j m n hm hn => hf hm hn) ht

theorem balancedGrading_shift_right {ι : Type*} [AddCommGroup ι] (ℳ : ι → Submodule k M)
    (𝒩 : ι → Submodule k N) (a : ι) :
    balancedGrading B A ℳ (shift 𝒩 a) = shift (balancedGrading B A ℳ 𝒩) a := by
  rw [balancedGrading, tensorGrading_shift_right]
  rfl

/-- `M ⊗_A g` is degree-preserving if `g` is. -/
theorem mapRight_mem_balancedGrading [Algebra k A] [IsScalarTower k A N] [SMulCommClass B Aᵐᵒᵖ M]
    {N' : Type*} [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
    {𝒩' : ι → Submodule k N'} {g : N →ₗ[A] N'} (hg : PreservesGrading 𝒩 𝒩' g) ⦃d : ι⦄
    ⦃y : BalancedTensor k B A M N⦄ (hy : y ∈ balancedGrading B A ℳ 𝒩 d) :
    mapRight g y ∈ balancedGrading B A ℳ 𝒩' d :=
  balancedGrading_map_mem _ ((mapRight g).restrictScalars k)
    (fun _ _ _ _ hm hn => tmul_mem_balancedGrading hm (hg hn)) hy

/-- If `M` is a graded left `B`-module, so is `M ⊗_A N`. -/
theorem gradedSMul_balanced {σ : Type*} [SetLike σ B] (ℬ : ι → σ) [SetLike.GradedSMul ℬ ℳ] :
    SetLike.GradedSMul ℬ (balancedGrading B A ℳ 𝒩) :=
  gradedSMul_map (𝒳 := tensorGrading ℳ 𝒩) (π := (BalancedTensor.mk k B A M N).restrictScalars k)
    ℬ fun b x => map_smul (BalancedTensor.mk k B A M N) b x

section Decomposition

variable [Algebra k A] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k A N]
  [DecidableEq ι] (𝒜 : ι → Submodule k A) [Decomposition 𝒜] [Decomposition ℳ]
  [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]

variable (ℳ 𝒩) in
/-- The homogeneous balancing relations. -/
def relHom : Set (M ⊗[k] N) :=
  {t | ∃ (i l j : ι) (m : M) (a : A) (n : N), m ∈ ℳ i ∧ a ∈ 𝒜 l ∧ n ∈ 𝒩 j ∧
    t = (op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)}

omit [AddCommMonoid ι] [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N] [SetLike.GradedSMul 𝒜 𝒩] in
theorem relSet_subset_span_relHom :
    relSet k A M N ⊆ Submodule.span k (relHom ℳ 𝒩 𝒜) := by
  rintro _ ⟨m, a, n, rfl⟩
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i m =>
    induction a using Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous l a =>
      induction n using Decomposition.inductionOn 𝒩 with
      | zero => simp
      | @homogeneous j n => exact Submodule.subset_span ⟨i, l, j, m, a, n, m.2, a.2, n.2, rfl⟩
      | add n n' hn hn' =>
        convert add_mem hn hn' using 1
        simp only [TensorProduct.tmul_add, smul_add]; abel
    | add a a' ha ha' =>
      convert add_mem ha ha' using 1
      simp only [op_add, add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
  | add m m' hm hm' =>
    convert add_mem hm hm' using 1
    simp only [smul_add, TensorProduct.add_tmul]; abel

/-- The balanced tensor product grading is a grading, provided the right action of `A` on `M`
is graded. -/
def balancedDecomposition
    (hM : ∀ ⦃i l : ι⦄ ⦃m : M⦄ ⦃a : A⦄, m ∈ ℳ i → a ∈ 𝒜 l → op a • m ∈ ℳ (i + l)) :
    Decomposition (balancedGrading B A ℳ 𝒩) := by
  refine mapDecomposition (BalancedTensor.mk_surjective (k := k) (B := B)) ?_
  intro x hx d
  have hx' : x ∈ Submodule.span k (relHom ℳ 𝒩 𝒜) := by
    have : x ∈ (rel k B A M N).restrictScalars k := (Submodule.Quotient.mk_eq_zero _).1 hx
    rw [rel_restrictScalars] at this
    exact Submodule.span_le.2 (relSet_subset_span_relHom 𝒜) this
  have hhom : ∀ s ∈ relHom ℳ 𝒩 𝒜, ∃ e, s ∈ tensorGrading ℳ 𝒩 e := by
    rintro _ ⟨i, l, j, m, a, n, hm, ha, hn, rfl⟩
    refine ⟨i + l + j, sub_mem (tmul_mem_tensorGrading (hM hm ha) hn) ?_⟩
    rw [add_assoc]
    exact tmul_mem_tensorGrading hm (SetLike.GradedSMul.smul_mem ha hn)
  have h := decompose_mem_span_of_homogeneous _ hhom hx' d
  have hrel : Submodule.span k (relHom ℳ 𝒩 𝒜) ≤ (rel k B A M N).restrictScalars k := by
    rw [Submodule.span_le]
    rintro _ ⟨i, l, j, m, a, n, -, -, -, rfl⟩
    exact Submodule.subset_span ⟨m, a, n, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).2 (hrel h)

end Decomposition

end Balanced

end Categorification.Graded

end
