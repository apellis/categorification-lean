/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Duality
import Categorification.KLR.ResProjGraded
import Categorification.KLR.GradingFlip
import Categorification.KLR.ConcatAssoc

/-!
# The bar involution and the bilinear form on `K₀(R(ν))`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5 (TeX lines ~1533–1541) and §3.1, Proposition 3.3.
We specialise the general duality of `Categorification.Algebra.Graded.Duality` to the KLR
algebras `R(ν)` with the antiinvolution `ψ` (`hflip`, degree-preserving for symmetric crossing
degrees, `GradingDatum.hflip_mem_grade`), and to the tensor products `R(ν) ⊗ R(ν')` with
`ψ ⊗ ψ`.

## Main results

Generic (graded algebras `A`, `B` with degree-preserving antiinvolutions `ψ`, `ψ'`):

* `GradedAntiInvolution.tensor ψ ψ'` : the antiinvolution `ψ ⊗ ψ'` of `A ⊗ B`.
* `GProj.extTensorOfIdempotentIso` : `A e ⊠ B e' ≅ (A ⊗ B)(e ⊗ e')` in `(A ⊗ B)-pmod`.
* `K0.bar_extTensor_of_mem_span` : `\overline{x ⊗ x'} = x̄ ⊗ x̄'` for `x`, `x'` in the
  `ℤ[q, q⁻¹]`-spans of the classes `[A e]`, `[B e']` of degree-zero idempotents.
* `K0.pform_extTensor_of_mem_span` : `(x ⊗ x', y ⊗ y') = (x, y)(x', y')` for KL I's bilinear
  form, `x`, `x'` in these spans.

For a grading datum `G` with symmetric crossing degrees (e.g. KL I's):

* `GradingDatum.psi G hsymm ν` : `ψ` as a `GradedAntiInvolution` of `R(ν)`; `KL1.psi` for KL I.
* `GradingDatum.bar_projP` : **`[P_i]` is bar-invariant** (`P̄_i ≅ P_i`, KL I §2.5).
* `GradingDatum.pform_projP` : **`([P_j], [P_i]) = gdim (1_j R(ν) 1_i)`** for KL I's bilinear
  form `pform` (KL I §2.5), and `GradingDatum.pform_projP_left` : `([P_j], [M]) = ch(M, j)`.
* `KLRAlgebra.hflip_concat_tmul_tmul` : `ψ (ι(a ⊗ b)) = ι(ψ a ⊗ ψ b)`.
* `GradingDatum.bar_indK0_of_mem_span` : `\overline{x x'} = x̄ x̄'` on the spans of idempotent
  classes (which contain the image of `γ`).
* `GradingDatum.pform_indK0` : **KL I, Proposition 3.3 (4)** for the bilinear form:
  `(x x', y) = (x ⊗ x', [Res] y)` for `x`, `x'` in the spans of idempotent classes, all `y`.
* `GradingDatum.pform_indK0_right` : **KL I, Proposition 3.3 (3)**:
  `(x, y y') = ([Res] x, y ⊗ y')` for all `x` and `y`, `y'` in the spans of idempotent classes.

## Not formalized here

* The identification `K₀(R(ν) ⊗ R(ν')) ≅ K₀(R(ν)) ⊗ K₀(R(ν'))`; statements (3) and (4) for
  arbitrary `y`, `y'` (resp. `x`, `x'`), which would need the bar involution to commute with
  induction on all of `K₀`.
-/

noncomputable section

universe u v

namespace Categorification

open scoped TensorProduct
open DirectSum Module

namespace Graded

/-! ### `ψ ⊗ ψ'` -/

section TensorInvolution

variable {k : Type*} [CommRing k] {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}

namespace GradedAntiInvolution

/-- The degree-preserving antiinvolution `ψ ⊗ ψ'` of `A ⊗ B` (tensor product grading). -/
def tensor (ψ : GradedAntiInvolution 𝒜) (ψ' : GradedAntiInvolution ℬ) :
    GradedAntiInvolution (tensorGrading 𝒜 ℬ) where
  toLinearMap := TensorProduct.map ψ.toLinearMap ψ'.toLinearMap
  map_mul' s t := by
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
        exact congrArg₂ (· ⊗ₜ[k] ·) (ψ.map_mul' a c) (ψ'.map_mul' b d)
      | add t t' ht ht' => rw [mul_add, _root_.map_add, ht, ht', _root_.map_add, add_mul]
    | add s s' hs hs' => rw [add_mul, _root_.map_add, hs, hs', _root_.map_add, mul_add]
  map_one' := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.map_tmul]
    exact congrArg₂ (· ⊗ₜ[k] ·) ψ.map_one' ψ'.map_one'
  invol' t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.map_tmul]
      exact congrArg₂ (· ⊗ₜ[k] ·) (ψ.invol' a) (ψ'.invol' b)
    | add s t hs ht => rw [_root_.map_add, _root_.map_add, hs, ht]
  mem_grade' d t ht :=
    tensorGrading_map_mem 𝒜 ℬ (tensorGrading 𝒜 ℬ) _
      (fun _ _ _ _ hm hn => by
        rw [TensorProduct.map_tmul]
        exact tmul_mem_tensorGrading (ψ.mem_grade hm) (ψ'.mem_grade hn)) ht

@[simp] theorem tensor_tmul (ψ : GradedAntiInvolution 𝒜) (ψ' : GradedAntiInvolution ℬ)
    (a : A) (b : B) : ψ.tensor ψ' (a ⊗ₜ[k] b) = ψ a ⊗ₜ[k] ψ' b := rfl

end GradedAntiInvolution

end TensorInvolution

/-! ### `A e ⊠ B e' ≅ (A ⊗ B)(e ⊗ e')` in `(A ⊗ B)-pmod` -/

section ExtIdem

variable {k : Type v} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem tmul_mem_tensorGrading_zero {e : A} {e' : B} (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    e ⊗ₜ[k] e' ∈ tensorGrading 𝒜 ℬ 0 := by
  simpa using tmul_mem_tensorGrading (ℳ := 𝒜) (𝒩 := ℬ) he0 he0'

/-- **`A e ⊠ B e' ≅ (A ⊗ B)(e ⊗ e')`** as graded projective `A ⊗ B`-modules. -/
def GProj.extTensorOfIdempotentIso {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    ((GProj.ofIdempotent e he he0).extTensor (GProj.ofIdempotent e' he' he0')).Iso
      (GProj.ofIdempotent (e ⊗ₜ[k] e') (idem_tmul_idem he he')
        (tmul_mem_tensorGrading_zero he0 he0')) :=
  GradedEquiv.ofPreserves (extIdemEquivLeftIdeal he he') fun _ _ hn => extIdemIncl_mem hn

namespace K0

/-- `[A e] ⊗ [B e'] = [(A ⊗ B)(e ⊗ e')]`. -/
theorem extTensor_ofIdempotent {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    extTensor 𝒜 ℬ (of (GProj.ofIdempotent e he he0)) (of (GProj.ofIdempotent e' he' he0')) =
      of (GProj.ofIdempotent (e ⊗ₜ[k] e') (idem_tmul_idem he he')
        (tmul_mem_tensorGrading_zero he0 he0')) := by
  rw [extTensor_of]
  exact of_eq_of_iso (GProj.extTensorOfIdempotentIso he he' he0 he0')

variable (ψ : GradedAntiInvolution 𝒜) (ψ' : GradedAntiInvolution ℬ)

/-- The bar involution preserves the span of the idempotent classes. -/
theorem bar_mem_span_idemClasses {x : K0 𝒜}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses 𝒜)) :
    bar ψ x ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses 𝒜) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, he0, rfl⟩ := hx
    rw [bar_ofIdempotent]
    exact Submodule.subset_span ⟨_, _, _, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul p x _ hx => rw [bar_smul]; exact Submodule.smul_mem _ _ hx

/-- `\overline{[A e] ⊗ [B e']} = \overline{[A e]} ⊗ \overline{[B e']}`. -/
theorem bar_extTensor_ofIdempotent {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    bar (ψ.tensor ψ') (extTensor 𝒜 ℬ (of (GProj.ofIdempotent e he he0))
      (of (GProj.ofIdempotent e' he' he0'))) =
      extTensor 𝒜 ℬ (bar ψ (of (GProj.ofIdempotent e he he0)))
        (bar ψ' (of (GProj.ofIdempotent e' he' he0'))) := by
  rw [extTensor_ofIdempotent, bar_ofIdempotent, bar_ofIdempotent, bar_ofIdempotent,
    extTensor_ofIdempotent]
  exact of_ofIdempotent_congr (GradedAntiInvolution.tensor_tmul ψ ψ' e e') _ _ _ _

/-- **`\overline{x ⊗ x'} = x̄ ⊗ x̄'`** for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes of
modules cut out by degree-zero idempotents. -/
theorem bar_extTensor_of_mem_span {x : K0 𝒜} {x' : K0 ℬ}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses 𝒜))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses ℬ)) :
    bar (ψ.tensor ψ') (extTensor 𝒜 ℬ x x') = extTensor 𝒜 ℬ (bar ψ x) (bar ψ' x') := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, he0, rfl⟩ := hx
    induction hx' using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨e', he', he0', rfl⟩ := hx'
      exact bar_extTensor_ofIdempotent ψ ψ' he he' he0 he0'
    | zero => simp
    | add x' y' _ _ hx' hy' => simp only [map_add, hx', hy']
    | smul p x' _ hx' =>
      rw [map_smul, bar_smul, hx', bar_smul, map_smul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul p x _ hx =>
    rw [map_smul, LinearMap.smul_apply, bar_smul, hx, bar_smul, map_smul, LinearMap.smul_apply]

variable [HasGdim 𝒜] [HasGdim ℬ]

/-- **Product formula for KL I's bilinear form**: `(x ⊗ x', y ⊗ y') = (x, y) (x', y')` for `x`,
`x'` in the spans of idempotent classes and arbitrary `y`, `y'`. -/
theorem pform_extTensor_of_mem_span {x : K0 𝒜} {x' : K0 ℬ}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses 𝒜))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses ℬ)) (y : K0 𝒜) (y' : K0 ℬ) :
    pform (tensorGrading 𝒜 ℬ) (ψ.tensor ψ') (extTensor 𝒜 ℬ x x') (extTensor 𝒜 ℬ y y') =
      pform 𝒜 ψ x y * pform ℬ ψ' x' y' := by
  rw [pform_apply, bar_extTensor_of_mem_span ψ ψ' hx hx',
    homForm_extTensor_of_mem_span (bar_mem_span_idemClasses ψ hx)
      (bar_mem_span_idemClasses ψ' hx'), pform_apply, pform_apply]

end K0

end ExtIdem

end Graded

namespace KLR

open Graded KLRAlgebra TypeA MvPolynomial MulOpposite

/-! ### `ψ` commutes with concatenation -/

namespace KLRAlgebra

section HflipConcat

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' : Multiset I}

private theorem hflip_oneConcat' :
    hflip (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = oneConcat Q ν ν' := by
  simp only [oneConcat, eSum, hflip_sum, hflip_e]

/-- A multiplicative `k`-linear map `φ : R(μ) → R(ν)` whose values on `1` and on the
generators are fixed by `ψ` commutes with `ψ`. -/
private theorem hflip_comm_of_gen' {μ : Multiset I}
    (φ : KLRAlgebra k Q μ →ₗ[k] KLRAlgebra k Q ν)
    (hφ : ∀ a b, φ (a * b) = φ a * φ b) (h1 : hflip (φ 1) = φ 1)
    (he : ∀ i, hflip (φ (e i)) = φ (e i)) (hx : ∀ a, hflip (φ (x a)) = φ (x a))
    (hψ : ∀ j, j + 1 < Multiset.card μ → hflip (φ (ψ j)) = φ (ψ j)) (a : KLRAlgebra k Q μ) :
    hflip (φ a) = φ (hflip a) := by
  let f : KLRAlgebra k Q μ →ₗ[k] (KLRAlgebra k Q ν)ᵐᵒᵖ :=
    { toFun := fun a => op (hflip (φ a))
      map_add' := fun a b => by rw [map_add, hflip_add, op_add]
      map_smul' := fun c a => by rw [map_smul, hflip_smul, op_smul]; rfl }
  let g : KLRAlgebra k Q μ →ₗ[k] (KLRAlgebra k Q ν)ᵐᵒᵖ :=
    { toFun := fun a => op (φ (hflip a))
      map_add' := fun a b => by rw [hflip_add, map_add, op_add]
      map_smul' := fun c a => by rw [hflip_smul, map_smul, op_smul]; rfl }
  have hfg : f = g := by
    refine ext_of_mul f g ?_ ?_ ?_ ?_ ?_ ?_
    · intro a b
      show op (hflip (φ (a * b))) = op (hflip (φ a)) * op (hflip (φ b))
      rw [hφ, hflip_mul, op_mul]
    · intro a b
      show op (φ (hflip (a * b))) = op (φ (hflip a)) * op (φ (hflip b))
      rw [hflip_mul, hφ, op_mul]
    · show op (hflip (φ 1)) = op (φ (hflip 1))
      rw [hflip_one, h1]
    · intro i
      show op (hflip (φ (e i))) = op (φ (hflip (e i)))
      rw [hflip_e, he]
    · intro a
      show op (hflip (φ (x a))) = op (φ (hflip (x a)))
      rw [hflip_x, hx]
    · intro j hj
      show op (hflip (φ (ψ j))) = op (φ (hflip (ψ j)))
      rw [hflip_ψ, hψ j hj]
  exact op_injective (LinearMap.congr_fun hfg a)

private theorem oneConcat_mul_ψ_left' {j : ℕ} (hj : j + 1 < Multiset.card ν) :
    (oneConcat Q ν ν' * ψ j : KLRAlgebra k Q (ν + ν')) = ψ j * oneConcat Q ν ν' := by
  have := oneConcat_mul_ψw (Q := Q) (ν := ν) (ν' := ν') (α := [j]) (α' := [])
    (fun l hl => by simp only [List.mem_singleton] at hl; omega) (fun l hl => by simp at hl)
  simpa [shiftWord] using this

private theorem oneConcat_mul_ψ_right' {j : ℕ} (hj : j + 1 < Multiset.card ν') :
    (oneConcat Q ν ν' * ψ (Multiset.card ν + j) : KLRAlgebra k Q (ν + ν')) =
      ψ (Multiset.card ν + j) * oneConcat Q ν ν' := by
  have := oneConcat_mul_ψw (Q := Q) (ν := ν) (ν' := ν') (α := []) (α' := [j])
    (fun l hl => by simp at hl) (fun l hl => by simp only [List.mem_singleton] at hl; omega)
  simpa [shiftWord] using this

private theorem hflip_concat_tmul_one' (a : KLRAlgebra k Q ν) :
    hflip (concat Q ν ν' (a ⊗ₜ 1)) = concat Q ν ν' (hflip a ⊗ₜ 1) := by
  let φ : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q (ν + ν') :=
    (concat Q ν ν').comp ((TensorProduct.mk k _ _).flip 1)
  have hφa : ∀ a, φ a = concat Q ν ν' (a ⊗ₜ 1) := fun a => rfl
  refine hflip_comm_of_gen' φ ?_ ?_ ?_ ?_ ?_ a
  · intro a b
    rw [hφa, hφa, hφa, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · rw [hφa, concat_one_tmul_one, hflip_oneConcat']
  · intro i
    rw [hφa, concat_e_tmul_one, hflip_sum]
    simp only [hflip_e]
  · intro b
    rw [hφa, concat_x_tmul_one, hflip_mul, hflip_oneConcat', hflip_x, oneConcat, x_mul_eSum]
  · intro j hj
    rw [hφa, concat_ψ_tmul_one hj, hflip_mul, hflip_oneConcat', hflip_ψ,
      oneConcat_mul_ψ_left' hj]

private theorem hflip_concat_one_tmul' (b : KLRAlgebra k Q ν') :
    hflip (concat Q ν ν' (1 ⊗ₜ b)) = concat Q ν ν' (1 ⊗ₜ hflip b) := by
  let φ : KLRAlgebra k Q ν' →ₗ[k] KLRAlgebra k Q (ν + ν') :=
    (concat Q ν ν').comp (TensorProduct.mk k _ _ 1)
  have hφa : ∀ b, φ b = concat Q ν ν' (1 ⊗ₜ b) := fun b => rfl
  refine hflip_comm_of_gen' φ ?_ ?_ ?_ ?_ ?_ b
  · intro a b
    rw [hφa, hφa, hφa, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · rw [hφa, concat_one_tmul_one, hflip_oneConcat']
  · intro i
    rw [hφa, concat_one_tmul_e, hflip_sum]
    simp only [hflip_e]
  · intro b
    rw [hφa, concat_one_tmul_x, hflip_mul, hflip_oneConcat', hflip_x, oneConcat, x_mul_eSum]
  · intro j hj
    rw [hφa, concat_one_tmul_ψ hj, hflip_mul, hflip_oneConcat', hflip_ψ,
      oneConcat_mul_ψ_right' hj]

/-- **`ψ` commutes with `ι_{ν,ν'}`** on pure tensors: `ψ(ι(a ⊗ b)) = ι(ψ a ⊗ ψ b)`. -/
theorem hflip_concat_tmul_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    hflip (concat Q ν ν' (a ⊗ₜ b)) = concat Q ν ν' (hflip a ⊗ₜ hflip b) := by
  have hab : (a ⊗ₜ[k] b : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hba : (hflip a ⊗ₜ[k] hflip b : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') =
      (1 ⊗ₜ hflip b) * (hflip a ⊗ₜ 1) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hba, concat_mul, ← hflip_concat_tmul_one', ← hflip_concat_one_tmul', ← hflip_mul,
    ← concat_mul, ← hab]

end HflipConcat

end KLRAlgebra

/-! ### `ψ` as a graded antiinvolution of `R(ν)` -/

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace GradingDatum

variable (G : GradingDatum Q) (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)

/-- **The antiinvolution `ψ` of `R(ν)`** (`hflip`, KL I §2.1) as a degree-preserving
antiinvolution, for a grading datum with symmetric crossing degrees. -/
def psi (ν : Multiset I) : GradedAntiInvolution (G.grade ν) where
  toLinearMap :=
    { toFun := hflip
      map_add' := hflip_add
      map_smul' := hflip_smul }
  map_mul' := hflip_mul
  map_one' := hflip_one
  invol' := hflip_hflip
  mem_grade' _ _ ha := G.hflip_mem_grade hsymm ha

@[simp] theorem psi_apply (ν : Multiset I) (a : KLRAlgebra k Q ν) : G.psi hsymm ν a = hflip a :=
  rfl

variable {ν ν' : Multiset I}

/-- **`P̄_i ≅ P_i`** (KL I, §2.5): `[P_i]` is bar-invariant. -/
theorem bar_projP (i : Seq ν) : K0.bar (G.psi hsymm ν) (K0.of (G.projP i)) = K0.of (G.projP i) :=
  K0.bar_ofIdempotent_of_fixed _ _ _ (hflip_e i)

/-- The bar involution fixes `[R(ν)]`. -/
theorem bar_regular : K0.bar (G.psi hsymm ν) (K0.of (GProj.regular (G.grade ν))) =
    K0.of (GProj.regular (G.grade ν)) :=
  K0.bar_regular _

variable [HasGdim (G.grade ν)]

/-- **KL I, equation `eq_char1`, for the bilinear form**: `([P_j], [M]) = gdim (1_j M)`. -/
theorem pform_projP_left (j : Seq ν) (M : GProj (G.grade ν)) :
    K0.pform (G.grade ν) (G.psi hsymm ν) (K0.of (G.projP j)) (K0.of M) = G.ch M.toGMod j := by
  rw [K0.pform_eq_homForm_of_bar_eq _ (G.bar_projP hsymm j), homForm_projP_left]

/-- **KL I, §2.5**: `([P_j], [P_i]) = gdim (1_j R(ν) 1_i)` for the bilinear form
`(P, Q) = gdim HOM(P̄, Q)`. -/
theorem pform_projP (j i : Seq ν) :
    K0.pform (G.grade ν) (G.psi hsymm ν) (K0.of (G.projP j)) (K0.of (G.projP i)) =
      gdim (G.cornerGrade j i) := by
  rw [K0.pform_eq_homForm_of_bar_eq _ (G.bar_projP hsymm j), homForm_projP]

/-- On the classes `[P_i]` the bilinear form agrees with `homForm`. -/
theorem pform_projP_eq_homForm (j : Seq ν) (y : K0 (G.grade ν)) :
    K0.pform (G.grade ν) (G.psi hsymm ν) (K0.of (G.projP j)) y =
      K0.homForm (G.grade ν) (K0.of (G.projP j)) y :=
  K0.pform_eq_homForm_of_bar_eq _ (G.bar_projP hsymm j) y

omit [HasGdim (G.grade ν)] in
/-- **`\overline{[R e] [R' e']} = \overline{[R e]} \overline{[R' e']}`** for degree-zero
idempotents. -/
theorem bar_indK0_ofIdempotent {e₁ : KLRAlgebra k Q ν} {e₂ : KLRAlgebra k Q ν'}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (he₁0 : e₁ ∈ G.grade ν 0)
    (he₂0 : e₂ ∈ G.grade ν' 0) :
    K0.bar (G.psi hsymm (ν + ν')) (G.indK0 ν ν' (K0.of (GProj.ofIdempotent e₁ he₁ he₁0))
      (K0.of (GProj.ofIdempotent e₂ he₂ he₂0))) =
      G.indK0 ν ν' (K0.bar (G.psi hsymm ν) (K0.of (GProj.ofIdempotent e₁ he₁ he₁0)))
        (K0.bar (G.psi hsymm ν') (K0.of (GProj.ofIdempotent e₂ he₂ he₂0))) := by
  rw [indK0_ofIdempotent, K0.bar_ofIdempotent, K0.bar_ofIdempotent, K0.bar_ofIdempotent,
    indK0_ofIdempotent]
  exact K0.of_ofIdempotent_congr (hflip_concat_tmul_tmul e₁ e₂) _ _ _ _

omit [HasGdim (G.grade ν)] in
/-- **`\overline{x x'} = x̄ x̄'`** for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes of modules
cut out by degree-zero idempotents (e.g. the `[P_i]` and the divided-power projectives). -/
theorem bar_indK0_of_mem_span {x : K0 (G.grade ν)} {x' : K0 (G.grade ν')}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν'))) :
    K0.bar (G.psi hsymm (ν + ν')) (G.indK0 ν ν' x x') =
      G.indK0 ν ν' (K0.bar (G.psi hsymm ν) x) (K0.bar (G.psi hsymm ν') x') := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e₁, he₁, he₁0, rfl⟩ := hx
    induction hx' using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨e₂, he₂, he₂0, rfl⟩ := hx'
      exact G.bar_indK0_ofIdempotent hsymm he₁ he₂ he₁0 he₂0
    | zero => simp
    | add x' y' _ _ hx' hy' => simp only [map_add, hx', hy']
    | smul p x' _ hx' => rw [map_smul, K0.bar_smul, hx', K0.bar_smul, map_smul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul p x _ hx =>
    rw [map_smul, LinearMap.smul_apply, K0.bar_smul, hx, K0.bar_smul, map_smul,
      LinearMap.smul_apply]

omit [HasGdim (G.grade ν)] in
/-- `ψ ⊗ ψ` on `R(ν) ⊗ R(ν')`. -/
abbrev psiTensor (ν ν' : Multiset I) : GradedAntiInvolution (tensorGrading (G.grade ν) (G.grade ν')) :=
  (G.psi hsymm ν).tensor (G.psi hsymm ν')

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  [HasGdim (G.grade ν')] [HasGdim (G.grade (ν + ν'))]

/-- **KL I, Proposition 3.3 (4), for the bilinear form**: `(x x', y) = (x ⊗ x', [Res] y)` for
`x`, `x'` in the spans of idempotent classes and all `y ∈ K₀(R(ν + ν'))`. -/
theorem pform_indK0 {x : K0 (G.grade ν)} {x' : K0 (G.grade ν')}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν')))
    (y : K0 (G.grade (ν + ν'))) :
    K0.pform (G.grade (ν + ν')) (G.psi hsymm (ν + ν')) (G.indK0 ν ν' x x') y =
      K0.pform (tensorGrading (G.grade ν) (G.grade ν')) (G.psiTensor hsymm ν ν')
        (K0.extTensor (G.grade ν) (G.grade ν') x x') (G.resK0 ν ν' hPQ hP y) := by
  rw [K0.pform_apply, G.bar_indK0_of_mem_span hsymm hx hx', G.homForm_indK0 hPQ hP,
    K0.pform_apply, K0.bar_extTensor_of_mem_span _ _ hx hx']

/-- **KL I, Proposition 3.3 (3)**: `(x, y y') = ([Res] x, y ⊗ y')` for all
`x ∈ K₀(R(ν + ν'))` and `y`, `y'` in the spans of idempotent classes (e.g. in the image of
`γ`). -/
theorem pform_indK0_right (x : K0 (G.grade (ν + ν'))) {y : K0 (G.grade ν)}
    {y' : K0 (G.grade ν')}
    (hy : y ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hy' : y' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν'))) :
    K0.pform (G.grade (ν + ν')) (G.psi hsymm (ν + ν')) x (G.indK0 ν ν' y y') =
      K0.pform (tensorGrading (G.grade ν) (G.grade ν')) (G.psiTensor hsymm ν ν')
        (G.resK0 ν ν' hPQ hP x) (K0.extTensor (G.grade ν) (G.grade ν') y y') := by
  rw [K0.pform_comm, G.pform_indK0 hsymm hPQ hP hy hy', K0.pform_comm]

/-- **KL I, Proposition 3.3 (4), evaluated**: if `[Res] y = ∑_α y_α ⊗ y'_α`, then
`(x x', y) = ∑_α (x, y_α)(x', y'_α)` for `x`, `x'` in the spans of idempotent classes. -/
theorem pform_indK0_eq_sum {x : K0 (G.grade ν)} {x' : K0 (G.grade ν')}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν')))
    (y : K0 (G.grade (ν + ν'))) {ι : Type*} (s : Finset ι) (z : ι → K0 (G.grade ν))
    (z' : ι → K0 (G.grade ν'))
    (hy : G.resK0 ν ν' hPQ hP y = ∑ α ∈ s, K0.extTensor (G.grade ν) (G.grade ν') (z α) (z' α)) :
    K0.pform (G.grade (ν + ν')) (G.psi hsymm (ν + ν')) (G.indK0 ν ν' x x') y =
      ∑ α ∈ s, K0.pform (G.grade ν) (G.psi hsymm ν) x (z α) *
        K0.pform (G.grade ν') (G.psi hsymm ν') x' (z' α) := by
  rw [G.pform_indK0 hsymm hPQ hP hx hx', hy, map_sum]
  exact Finset.sum_congr rfl fun α _ => K0.pform_extTensor_of_mem_span _ _ hx hx' _ _

end GradingDatum

/-! ### KL I -/

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

theorem degΨ_symm (a b : I) :
    (klGradingDatum k Γ).degΨ a b = (klGradingDatum k Γ).degΨ b a := by
  show -cartan Γ a b = -cartan Γ b a
  rw [cartan_symm]

variable (k Γ) in
/-- **The antiinvolution `ψ` of the KL I algebra `R(ν)`** as a degree-preserving
antiinvolution. -/
abbrev psi (ν : Multiset I) : GradedAntiInvolution ((klGradingDatum k Γ).grade ν) :=
  (klGradingDatum k Γ).psi degΨ_symm ν

/-- **`[P_i]` is bar-invariant** for KL I (`P̄_i ≅ P_i`). -/
theorem bar_projP {ν : Multiset I} (i : Seq ν) :
    K0.bar (psi k Γ ν) (K0.of ((klGradingDatum k Γ).projP i)) =
      K0.of ((klGradingDatum k Γ).projP i) :=
  (klGradingDatum k Γ).bar_projP degΨ_symm i

/-- **KL I, §2.5**: `([P_j], [P_i]) = ∑_{w • i = j} q^{-∑_{inv(w)} i_a · i_b} (1 - q²)^{-m}`
for the bilinear form. -/
theorem pform_projP {ν : Multiset I} (j i : Seq ν) :
    K0.pform ((klGradingDatum k Γ).grade ν) (psi k Γ ν) (K0.of ((klGradingDatum k Γ).projP j))
      (K0.of ((klGradingDatum k Γ).projP i)) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
        HahnSeries.single (-∑ p ∈ invSet (Multiset.card ν) w, cartan Γ (i.lbl p.1) (i.lbl p.2)) 1 *
          geomSeries 2 ^ Multiset.card ν := by
  rw [(klGradingDatum k Γ).pform_projP_eq_homForm degΨ_symm, homForm_projP]

end KL1

end KLR

end Categorification
