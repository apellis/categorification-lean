/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.TensorGdim
import Categorification.Algebra.Graded.HomForm
import Categorification.KLR.Induction

/-!
# External tensor products on `K₀`, and the form on `K₀(A ⊗ B)`

Let `(A, 𝒜)`, `(B, ℬ)` be `ℤ`-graded algebras over a field `k`. The external tensor product
`P ⊠ P' = P ⊗[k] P'` of finitely generated graded projective modules is a finitely generated
graded projective `A ⊗ B`-module (for the tensor product gradings). This is used by
Khovanov–Lauda I (arXiv:0803.4121v2, §3.1) for the classes `[Y ⊗ Y'] = [Y] ⊗ [Y']` in
`K₀(R(ν) ⊗ R(ν'))` appearing in Proposition 3.3.

The results are stated for general graded algebras (they are used for `A = R(ν)`,
`B = R(ν')`); this file sits in `KLR/` only because it uses the `K₀` universal properties
`K0.lift`, `K0.lift₂` of `Categorification.KLR.Induction`.

## Main definitions and results

* `GProj.extTensor P P'` : `P ⊠ P'` as an object of `(A ⊗ B)-pmod`, with its compatibility with
  isomorphisms, direct sums and shifts.
* `K0.extTensor` : the `ℤ[q, q⁻¹]`-bilinear map `K₀(A) × K₀(B) → K₀(A ⊗ B)`,
  `[P] ⊗ [P'] ↦ [P ⊠ P']` (`K0.extTensor_of`).
* `homGradeExtIdemEquiv` : `HOM_{A ⊗ B}(A e ⊠ B e', X)_d ≅ ((e ⊗ e') X)_d` for degree-zero
  idempotents `e`, `e'`.
* `finrank_idem_extTensor` : `(e ⊗ e')(S ⊠ S') ≅ e S ⊗ e' S'` degree-wise.
* **Product formula** `GProj.homGdim_extTensor_ofIdempotent` and
  `K0.homForm_extTensor_ofIdempotent`:
  `([A e ⊠ B e'], [S ⊠ S']) = ([A e], [S]) · ([B e'], [S'])` for the form
  `([P], [Q]) = gdim HOM(P, Q)`, and its extension `K0.homForm_extTensor_of_mem_span` to all
  `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes of modules `A e`, `B e'`.

## Scope

The product formula `([P ⊠ P'], [S ⊠ S']) = ([P], [S]) ([P'], [S'])` is proved when `P`, `P'`
are (shifts of) modules `A e`, `B e'` cut out by degree-zero idempotents, with arbitrary `S`,
`S'` in the second slot. This covers the modules `P_i`, `P_{i^{(a)} …}` of KL I (and, by
linearity, the whole image of `γ`). The general case (arbitrary finitely generated graded
projective `P`, `P'`) is not formalized here.
-/

noncomputable section

universe u v

namespace Categorification.Graded

open DirectSum Module
open scoped TensorProduct

variable {k : Type v} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}

/-! ### The external tensor product of graded projective modules -/

namespace GProj

/-- **The external tensor product `P ⊠ P'`** of finitely generated graded projective modules,
a finitely generated graded projective `A ⊗ B`-module for the tensor product gradings. -/
def extTensor (P : GProj 𝒜) (P' : GProj ℬ) : GProj (tensorGrading 𝒜 ℬ) :=
  haveI := ExtTensor.finite (k := k) (A := A) (B := B) (P := P.carrier) (Q := P'.carrier)
  haveI := ExtTensor.projective (k := k) (A := A) (B := B) (P := P.carrier) (Q := P'.carrier)
  { carrier := ExtTensor k P.carrier P'.carrier
    grading := ExtTensor.grading P.grading P'.grading
    decomposition := inferInstance
    gradedSMul := ExtTensor.gradedSMul P.grading P'.grading 𝒜 ℬ
    finite := inferInstance
    projective := inferInstance }

theorem extTensor_carrier (P : GProj 𝒜) (P' : GProj ℬ) :
    (P.extTensor P').carrier = ExtTensor k P.carrier P'.carrier := rfl

theorem extTensor_grading (P : GProj 𝒜) (P' : GProj ℬ) :
    (P.extTensor P').grading = ExtTensor.grading P.grading P'.grading := rfl

/-- `P₁ ⊠ P₁' ≅ P₂ ⊠ P₂'` for `P₁ ≅ P₂`, `P₁' ≅ P₂'`. -/
def extTensorCongr {P₁ P₂ : GProj 𝒜} {P₁' P₂' : GProj ℬ} (e : P₁.Iso P₂) (e' : P₁'.Iso P₂') :
    (P₁.extTensor P₁').Iso (P₂.extTensor P₂') :=
  GradedEquiv.ofPreserves (ExtTensor.congr e.toLinearEquiv e'.toLinearEquiv)
    (ExtTensor.map_preservesGrading e.preservesGrading e'.preservesGrading)

/-- `(P₁ ⊕ P₂) ⊠ P' ≅ P₁ ⊠ P' ⊕ P₂ ⊠ P'`. -/
def extTensorProdLeft (P₁ P₂ : GProj 𝒜) (P' : GProj ℬ) :
    ((P₁.prod P₂).extTensor P').Iso ((P₁.extTensor P').prod (P₂.extTensor P')) :=
  GradedEquiv.ofPreserves (ExtTensor.prodLeft (k := k) (P := P₁.carrier) (P' := P₂.carrier)
    (Q := P'.carrier) (A := A) (B := B))
    fun _ _ hx =>
      ⟨ExtTensor.map_preservesGrading (𝒰 := Graded.prod P₁.grading P₂.grading)
        (𝒱 := P'.grading) (𝒰' := P₁.grading) (f := LinearMap.fst A P₁.carrier P₂.carrier)
        (g := LinearMap.id) (fun _ _ h => h.1) (fun _ _ h => h) hx,
       ExtTensor.map_preservesGrading (𝒰 := Graded.prod P₁.grading P₂.grading)
        (𝒱 := P'.grading) (𝒰' := P₂.grading) (f := LinearMap.snd A P₁.carrier P₂.carrier)
        (g := LinearMap.id) (fun _ _ h => h.2) (fun _ _ h => h) hx⟩

/-- `P ⊠ (P₁' ⊕ P₂') ≅ P ⊠ P₁' ⊕ P ⊠ P₂'`. -/
def extTensorProdRight (P : GProj 𝒜) (P₁' P₂' : GProj ℬ) :
    (P.extTensor (P₁'.prod P₂')).Iso ((P.extTensor P₁').prod (P.extTensor P₂')) :=
  GradedEquiv.ofPreserves (ExtTensor.prodRight (k := k) (P := P.carrier) (Q := P₁'.carrier)
    (Q' := P₂'.carrier) (A := A) (B := B))
    fun _ _ hx =>
      ⟨ExtTensor.map_preservesGrading (𝒰 := P.grading)
        (𝒱 := Graded.prod P₁'.grading P₂'.grading) (𝒱' := P₁'.grading) (f := LinearMap.id)
        (g := LinearMap.fst B P₁'.carrier P₂'.carrier) (fun _ _ h => h) (fun _ _ h => h.1) hx,
       ExtTensor.map_preservesGrading (𝒰 := P.grading)
        (𝒱 := Graded.prod P₁'.grading P₂'.grading) (𝒱' := P₂'.grading) (f := LinearMap.id)
        (g := LinearMap.snd B P₁'.carrier P₂'.carrier) (fun _ _ h => h) (fun _ _ h => h.2) hx⟩

/-- `P{a} ⊠ P' ≅ (P ⊠ P'){a}`. -/
def extTensorShiftLeft (P : GProj 𝒜) (P' : GProj ℬ) (a : ℤ) :
    ((P.shift a).extTensor P').Iso ((P.extTensor P').shift a) :=
  GradedEquiv.ofEq (ExtTensor.grading_shift_left P.grading P'.grading a)

/-- `P ⊠ P'{a} ≅ (P ⊠ P'){a}`. -/
def extTensorShiftRight (P : GProj 𝒜) (P' : GProj ℬ) (a : ℤ) :
    (P.extTensor (P'.shift a)).Iso ((P.extTensor P').shift a) :=
  GradedEquiv.ofEq (ExtTensor.grading_shift_right P.grading P'.grading a)

end GProj

/-! ### The bilinear map `K₀(A) × K₀(B) → K₀(A ⊗ B)` -/

namespace K0

open GProj

variable (𝒜 ℬ) in
/-- The biadditive map `([P], [P']) ↦ [P ⊠ P']`. -/
def extTensorAdd : K0 𝒜 →+ K0 ℬ →+ K0 (tensorGrading 𝒜 ℬ) :=
  lift₂ (fun P P' => of (P.extTensor P'))
    (fun _ _ _ e => of_eq_of_iso (extTensorCongr e (GradedEquiv.refl _)))
    (fun _ _ _ e => of_eq_of_iso (extTensorCongr (GradedEquiv.refl _) e))
    (fun P₁ P₂ P' => by
      beta_reduce; rw [of_eq_of_iso (extTensorProdLeft P₁ P₂ P'), of_prod])
    (fun P P₁ P₂ => by
      beta_reduce; rw [of_eq_of_iso (extTensorProdRight P P₁ P₂), of_prod])

@[simp] theorem extTensorAdd_of (P : GProj 𝒜) (P' : GProj ℬ) :
    extTensorAdd 𝒜 ℬ (of P) (of P') = of (P.extTensor P') :=
  lift₂_of _ _ _ _ _ P P'

theorem extTensorAdd_shift_left (a : ℤ) (x : K0 𝒜) (y : K0 ℬ) :
    extTensorAdd 𝒜 ℬ (shiftHom a x) y = shiftHom a (extTensorAdd 𝒜 ℬ x y) := by
  induction x using induction_on with
  | of P =>
    induction y using induction_on with
    | of P' =>
      rw [shiftHom_of, extTensorAdd_of, extTensorAdd_of, shiftHom_of]
      exact of_eq_of_iso (extTensorShiftLeft P P' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

theorem extTensorAdd_shift_right (a : ℤ) (x : K0 𝒜) (y : K0 ℬ) :
    extTensorAdd 𝒜 ℬ x (shiftHom a y) = shiftHom a (extTensorAdd 𝒜 ℬ x y) := by
  induction x using induction_on with
  | of P =>
    induction y using induction_on with
    | of P' =>
      rw [shiftHom_of, extTensorAdd_of, extTensorAdd_of, shiftHom_of]
      exact of_eq_of_iso (extTensorShiftRight P P' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

variable (𝒜 ℬ) in
/-- **The `ℤ[q, q⁻¹]`-bilinear map `K₀(A) × K₀(B) → K₀(A ⊗ B)`**, `[P] ⊗ [P'] ↦ [P ⊠ P']`
(KL I, §3.1: the class `[Y ⊗ Y']` of an external tensor product). -/
def extTensor : K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 ℬ →ₗ[LaurentPolynomial ℤ]
    K0 (tensorGrading 𝒜 ℬ) :=
  LinearMap.mk₂ (LaurentPolynomial ℤ) (fun x y => extTensorAdd 𝒜 ℬ x y)
    (fun x x' y => by simp only [map_add, AddMonoidHom.add_apply])
    (fun p x y => map_smul_of_shift ((extTensorAdd 𝒜 ℬ).flip y)
      (fun a x => extTensorAdd_shift_left a x y) p x)
    (fun x y y' => map_add _ y y')
    (fun p x y => map_smul_of_shift (extTensorAdd 𝒜 ℬ x)
      (fun a y => extTensorAdd_shift_right a x y) p y)

@[simp] theorem extTensor_apply (x : K0 𝒜) (y : K0 ℬ) :
    extTensor 𝒜 ℬ x y = extTensorAdd 𝒜 ℬ x y := rfl

/-- `[P] ⊗ [P'] ↦ [P ⊠ P']`. -/
theorem extTensor_of (P : GProj 𝒜) (P' : GProj ℬ) :
    extTensor 𝒜 ℬ (of P) (of P') = of (P.extTensor P') :=
  extTensorAdd_of P P'

end K0

/-! ### `HOM(A e ⊠ B e', X) ≅ (e ⊗ e') X` -/

section IdemHom

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

variable (e : A) (e' : B) in
/-- The inclusion `A e ⊠ B e' → A ⊗ B`. -/
def extIdemIncl : ExtTensor k (leftIdeal e) (leftIdeal e') →ₗ[A ⊗[k] B] A ⊗[k] B :=
  (ExtTensor.selfEquiv k A B).toLinearMap ∘ₗ
    ExtTensor.map (leftIdeal e).subtype (leftIdeal e').subtype

@[simp] theorem extIdemIncl_tmul {e : A} {e' : B} (x : leftIdeal e) (y : leftIdeal e') :
    extIdemIncl e e' (ExtTensor.tmul x y) = (x : A) ⊗ₜ[k] (y : B) := rfl

theorem extIdemIncl_smul_unit {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (n : ExtTensor k (leftIdeal e) (leftIdeal e')) :
    extIdemIncl e e' n • ExtTensor.tmul (k := k) (⟨e, he.eq⟩ : leftIdeal e)
      (⟨e', he'.eq⟩ : leftIdeal e') = n := by
  induction n using ExtTensor.induction_on with
  | zero => rw [map_zero, zero_smul]
  | tmul x y =>
    rw [extIdemIncl_tmul, ExtTensor.smul_tmul]
    congr 1
    · exact Subtype.ext (mem_leftIdeal.1 x.2)
    · exact Subtype.ext (mem_leftIdeal.1 y.2)
  | add n n' hn hn' => rw [map_add, add_smul, hn, hn']

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem extIdemIncl_mem {e : A} {e' : B} {d : ℤ} {n : ExtTensor k (leftIdeal e) (leftIdeal e')}
    (hn : n ∈ ExtTensor.grading (Graded.submodule 𝒜 (leftIdeal e))
      (Graded.submodule ℬ (leftIdeal e')) d) :
    extIdemIncl e e' n ∈ tensorGrading 𝒜 ℬ d :=
  ExtTensor.grading_map_mem _ _ (tensorGrading 𝒜 ℬ) ((extIdemIncl e e').restrictScalars k)
    (fun _ _ _ _ hx hy => tmul_mem_tensorGrading hx hy) hn

variable {X : Type*} [AddCommGroup X] [Module (A ⊗[k] B) X] [Module k X]
  [IsScalarTower k (A ⊗[k] B) X] {𝒳 : ℤ → Submodule k X}
  [SetLike.GradedSMul (tensorGrading 𝒜 ℬ) 𝒳]

theorem idem_tmul_idem {e : A} {e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    IsIdempotentElem (e ⊗ₜ[k] e') := by
  rw [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul, he.eq, he'.eq]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
variable (k) in
/-- The generator `e ⊠ e'` of `A e ⊠ B e'`. -/
def extIdemUnit {e : A} {e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    ExtTensor k (leftIdeal e) (leftIdeal e') :=
  ExtTensor.tmul (⟨e, he.eq⟩ : leftIdeal e) (⟨e', he'.eq⟩ : leftIdeal e')

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem extIdemUnit_mem {e : A} {e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    extIdemUnit k he he' ∈ ExtTensor.grading (Graded.submodule 𝒜 (leftIdeal e))
      (Graded.submodule ℬ (leftIdeal e')) 0 := by
  have h0 := ExtTensor.tmul_mem_grading (k := k) (𝒰 := Graded.submodule 𝒜 (leftIdeal e))
    (𝒱 := Graded.submodule ℬ (leftIdeal e')) (i := 0) (j := 0)
    (p := (⟨e, he.eq⟩ : leftIdeal e)) (q := (⟨e', he'.eq⟩ : leftIdeal e')) he0 he0'
  rwa [add_zero] at h0

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [SetLike.GradedSMul (tensorGrading 𝒜 ℬ) 𝒳] in
theorem tmul_smul_extIdemUnit {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') :
    (e ⊗ₜ[k] e') • extIdemUnit k he he' = extIdemUnit k he he' := by
  rw [extIdemUnit, ExtTensor.smul_tmul]
  congr 1
  · exact Subtype.ext he.eq
  · exact Subtype.ext he'.eq

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [SetLike.GradedSMul (tensorGrading 𝒜 ℬ) 𝒳] in
/-- The map `x ↦ (y ↦ y x)` from `X` to `HOM(A e ⊠ B e', X)`. -/
def extIdemHom (e : A) (e' : B) (x : X) : ExtTensor k (leftIdeal e) (leftIdeal e') →ₗ[A ⊗[k] B] X :=
  (LinearMap.toSpanSingleton (A ⊗[k] B) X x).comp (extIdemIncl e e')

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [SetLike.GradedSMul (tensorGrading 𝒜 ℬ) 𝒳]
  [Module k X] [IsScalarTower k (A ⊗[k] B) X] in
theorem extIdemHom_apply (e : A) (e' : B) (x : X) (y : ExtTensor k (leftIdeal e) (leftIdeal e')) :
    extIdemHom e e' x y = extIdemIncl e e' y • x := rfl

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem extIdemHom_mem {e : A} {e' : B} {x : X} {d : ℤ} (hx : x ∈ 𝒳 d) :
    extIdemHom e e' x ∈ homGrade (A ⊗[k] B) (ExtTensor.grading
      (Graded.submodule 𝒜 (leftIdeal e)) (Graded.submodule ℬ (leftIdeal e'))) 𝒳 d := by
  intro i y hy
  rw [extIdemHom_apply]
  exact SetLike.GradedSMul.smul_mem (A := tensorGrading 𝒜 ℬ) (B := 𝒳) (extIdemIncl_mem hy) hx

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- **`HOM(A e ⊠ B e', X)_d ≅ ((e ⊗ e') X)_d`**, `φ ↦ φ(e ⊗ e')`, for degree-zero idempotents
`e`, `e'`. -/
def homGradeExtIdemEquiv {e : A} {e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) (d : ℤ) :
    homGrade (A ⊗[k] B) (ExtTensor.grading (Graded.submodule 𝒜 (leftIdeal e))
      (Graded.submodule ℬ (leftIdeal e'))) 𝒳 d ≃ₗ[k] idem 𝒳 (e ⊗ₜ[k] e') d where
  toFun φ := ⟨⟨φ.1 (extIdemUnit k he he'), by
      show (e ⊗ₜ[k] e') • φ.1 (extIdemUnit k he he') = φ.1 (extIdemUnit k he he')
      rw [← map_smul, tmul_smul_extIdemUnit]⟩, by
      have := φ.2 (extIdemUnit_mem he he' he0 he0')
      rw [zero_add] at this
      exact (mem_idem 𝒳).2 this⟩
  invFun m := ⟨extIdemHom e e' m.1.1, extIdemHom_mem m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := by
    refine Subtype.ext (LinearMap.ext fun y => ?_)
    show extIdemIncl e e' y • φ.1 (extIdemUnit k he he') = φ.1 y
    rw [← map_smul, extIdemUnit, extIdemIncl_smul_unit he he']
  right_inv m := by
    refine Subtype.ext (Subtype.ext ?_)
    show extIdemIncl e e' (extIdemUnit k he he') • (m.1.1 : X) = m.1.1
    exact m.1.2

/-! ### `(e ⊗ e') (S ⊠ S') ≅ e S ⊗ e' S'` -/

section IdemTensor

variable {S S' : Type*} [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
  [AddCommGroup S'] [Module k S'] [Module B S'] [IsScalarTower k B S']

variable (S S') in
/-- The inclusion `e S ⊗ e' S' → S ⊠ S'`. -/
def idemTensorIncl (e : A) (e' : B) :
    idemSubspace k S e ⊗[k] idemSubspace k S' e' →ₗ[k] ExtTensor k S S' :=
  TensorProduct.map (idemSubspace k S e).subtype (idemSubspace k S' e').subtype

theorem idemTensorIncl_tmul {e : A} {e' : B} (a : idemSubspace k S e) (b : idemSubspace k S' e') :
    idemTensorIncl S S' e e' (a ⊗ₜ b) = ExtTensor.tmul (a : S) (b : S') := rfl

theorem idemTensorIncl_injective (e : A) (e' : B) :
    Function.Injective (idemTensorIncl (k := k) S S' e e') :=
  TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective

variable (S S') in
/-- The projection `S ⊠ S' → e S ⊗ e' S'`, `s ⊗ s' ↦ e s ⊗ e' s'`. -/
def idemTensorProj {e : A} {e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    ExtTensor k S S' →ₗ[k] idemSubspace k S e ⊗[k] idemSubspace k S' e' :=
  TensorProduct.map
    (LinearMap.codRestrict _ (DistribMulAction.toLinearMap k S e) (smul_mem_idemSubspace he))
    (LinearMap.codRestrict _ (DistribMulAction.toLinearMap k S' e') (smul_mem_idemSubspace he'))

theorem idemTensorIncl_proj {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (x : ExtTensor k S S') :
    idemTensorIncl S S' e e' (idemTensorProj S S' he he' x) = (e ⊗ₜ[k] e') • x := by
  induction x using ExtTensor.induction_on with
  | zero => simp
  | tmul s s' => rw [ExtTensor.smul_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem range_idemTensorIncl {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') :
    LinearMap.range (idemTensorIncl S S' e e') =
      idemSubspace k (ExtTensor k S S') (e ⊗ₜ[k] e') := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_idemSubspace]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [idemTensorIncl_tmul, ExtTensor.smul_tmul]
      rw [show e • (a : S) = a from a.2, show e' • (b : S') = b from b.2]
    | add y z hy hz => rw [map_add, smul_add, hy, hz]
  · intro x hx
    rw [mem_idemSubspace] at hx
    exact ⟨idemTensorProj S S' he he' x, by rw [idemTensorIncl_proj, hx]⟩

variable {𝒮 : ℤ → Submodule k S} {𝒮' : ℤ → Submodule k S'} [Decomposition 𝒮] [Decomposition 𝒮']
  [SetLike.GradedSMul 𝒜 𝒮] [SetLike.GradedSMul ℬ 𝒮']

omit [Decomposition 𝒮] [Decomposition 𝒮'] [SetLike.GradedSMul 𝒜 𝒮]
  [SetLike.GradedSMul ℬ 𝒮'] in
theorem idemTensorIncl_preservesGrading (e : A) (e' : B) :
    PreservesGrading (tensorGrading (idem 𝒮 e) (idem 𝒮' e')) (ExtTensor.grading 𝒮 𝒮')
      (idemTensorIncl S S' e e') :=
  fun _ _ hx => tensorGrading_map_mem _ _ _ (idemTensorIncl S S' e e')
    (fun _ _ _ _ ha hb => ExtTensor.tmul_mem_grading (k := k) ha hb) hx

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- The grading of `e S ⊗ e' S'` is the one pulled back from `S ⊠ S'`. -/
theorem tensorGrading_idem_eq_comap {e : A} {e' : B} (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    tensorGrading (idem 𝒮 e) (idem 𝒮' e') =
      comap (ExtTensor.grading 𝒮 𝒮') (idemTensorIncl S S' e e') := by
  letI := idemDecomposition 𝒮 he0
  letI := idemDecomposition 𝒮' he0'
  funext d
  apply le_antisymm
  · intro y hy
    exact idemTensorIncl_preservesGrading e e' hy
  · intro y hy
    rw [mem_comap] at hy
    have h1 := decompose_map (idemTensorIncl_preservesGrading (𝒮 := 𝒮) (𝒮' := 𝒮') e e') y d
    rw [decompose_of_mem_same _ hy] at h1
    have h2 := idemTensorIncl_injective e e' h1
    rw [h2]
    exact (decompose (tensorGrading (idem 𝒮 e) (idem 𝒮' e')) y d).2

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- **`dim ((e ⊗ e')(S ⊠ S'))_d = dim (e S ⊗ e' S')_d`**. -/
theorem finrank_idem_extTensor {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) (d : ℤ) :
    finrank k (idem (ExtTensor.grading 𝒮 𝒮') (e ⊗ₜ[k] e') d) =
      finrank k (tensorGrading (idem 𝒮 e) (idem 𝒮' e') d) := by
  have h1 : finrank k (idem (ExtTensor.grading 𝒮 𝒮') (e ⊗ₜ[k] e') d) =
      finrank k ↥(ExtTensor.grading 𝒮 𝒮' d ⊓
        LinearMap.range (idemSubspace k (ExtTensor k S S') (e ⊗ₜ[k] e')).subtype) :=
    finrank_comap (ExtTensor.grading 𝒮 𝒮') Subtype.val_injective d
  have h2 := finrank_comap (ExtTensor.grading 𝒮 𝒮') (idemTensorIncl_injective (S := S)
    (S' := S') e e') d
  rw [h1, tensorGrading_idem_eq_comap he0 he0', h2, range_idemTensorIncl he he',
    Submodule.range_subtype]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- **`gdim ((e ⊗ e')(S ⊠ S')) = gdim (e S) · gdim (e' S')`**. -/
theorem gdim_idem_extTensor [HasGdim 𝒮] [HasGdim 𝒮'] {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    gdim (idem (ExtTensor.grading 𝒮 𝒮') (e ⊗ₜ[k] e')) = gdim (idem 𝒮 e) * gdim (idem 𝒮' e') := by
  letI := idemDecomposition 𝒮 he0
  letI := idemDecomposition 𝒮' he0'
  rw [← gdim_tensorGrading]
  exact gdim_eq_of_finrank_eq (finrank_idem_extTensor he he' he0 he0')

end IdemTensor

end IdemHom

/-! ### The product formula for the form -/

section Form

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]

namespace GProj

/-- **Product formula**: `gdim HOM(A e ⊠ B e', S ⊠ S') = gdim (e S) · gdim (e' S')`. -/
theorem homGdim_extTensor_ofIdempotent {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) (S : GProj 𝒜) (S' : GProj ℬ) :
    homGdim ((ofIdempotent e he he0).extTensor (ofIdempotent e' he' he0')) (S.extTensor S') =
      gdim (idem S.grading e) * gdim (idem S'.grading e') := by
  rw [homGdim, ← gdim_idem_extTensor he he' he0 he0']
  exact gdim_eq_of_finrank_eq fun d =>
    (homGradeExtIdemEquiv (𝒳 := ExtTensor.grading S.grading S'.grading) he he' he0 he0'
      d).finrank_eq

end GProj

namespace K0

open GProj

/-- **Product formula on `K₀`**: `([A e] ⊗ [B e'], y ⊗ y') = ([A e], y) · ([B e'], y')` for the
forms `gdim HOM` on `K₀(A ⊗ B)`, `K₀(A)`, `K₀(B)`. -/
theorem homForm_extTensor_ofIdempotent {e : A} {e' : B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) (y : K0 𝒜) (y' : K0 ℬ) :
    homForm (tensorGrading 𝒜 ℬ) (extTensor 𝒜 ℬ (of (ofIdempotent e he he0))
        (of (ofIdempotent e' he' he0'))) (extTensor 𝒜 ℬ y y') =
      homForm 𝒜 (of (ofIdempotent e he he0)) y * homForm ℬ (of (ofIdempotent e' he' he0')) y' := by
  induction y using induction_on with
  | of S =>
    induction y' using induction_on with
    | of S' =>
      rw [extTensor_of, extTensor_of, homForm_of, homGdim_extTensor_ofIdempotent,
        homForm_ofIdempotent, homForm_ofIdempotent]
    | zero => simp
    | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
    | neg y hy => simp only [map_neg, mul_neg, hy]
  | zero => simp
  | add y y' hy hy' =>
    simp only [map_add, LinearMap.add_apply, add_mul, hy, hy']
  | neg y hy => simp only [map_neg, LinearMap.neg_apply, neg_mul, hy]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- An additive map `F : K₀(A) → ℤ((q))` with `F(x{a}) = q^{-a} F(x)` vanishing at `x` vanishes
on `ℤ[q, q⁻¹] x`. -/
theorem map_smul_eq_zero_of_shift {F : K0 𝒜 →+ LaurentSeries ℤ}
    (hF : ∀ (a : ℤ) (x : K0 𝒜), F (shiftHom a x) = HahnSeries.single (-a) 1 * F x) {x : K0 𝒜}
    (hx : F x = 0) (p : LaurentPolynomial ℤ) : F (p • x) = 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', add_zero]
  | C_mul_T a c => rw [C_mul_T_smul, map_zsmul, hF, hx, mul_zero, zsmul_zero]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- A property of `x ∈ span S` closed under `0`, `+` and `q^a`-shifts (hence `ℤ[q, q⁻¹]`-linear
combinations), expressed as the vanishing of an additive map `F` with `F(x{a}) = q^{-a} F(x)`. -/
theorem map_eq_zero_of_mem_span {F : K0 𝒜 →+ LaurentSeries ℤ}
    (hF : ∀ (a : ℤ) (x : K0 𝒜), F (shiftHom a x) = HahnSeries.single (-a) 1 * F x)
    {s : Set (K0 𝒜)} (hs : ∀ x ∈ s, F x = 0) {x : K0 𝒜}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) s) : F x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact map_zero F
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul p x _ hx => exact map_smul_eq_zero_of_shift hF hx p

variable (𝒜) in
/-- The classes `[A e]` of the modules cut out by degree-zero idempotents. -/
def idemClasses : Set (K0 𝒜) :=
  {x | ∃ (e : A) (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0), x = of (ofIdempotent e he he0)}

/-- The defect `(x ⊗ x', y ⊗ y') - (x, y)(x', y')` as an additive function of `x`. -/
def extFormDefectLeft (x' : K0 ℬ) (y : K0 𝒜) (y' : K0 ℬ) : K0 𝒜 →+ LaurentSeries ℤ where
  toFun x := homForm (tensorGrading 𝒜 ℬ) (extTensor 𝒜 ℬ x x') (extTensor 𝒜 ℬ y y') -
    homForm 𝒜 x y * homForm ℬ x' y'
  map_zero' := by simp
  map_add' x₁ x₂ := by
    simp only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply, add_mul]
    abel

/-- The defect `(x ⊗ x', y ⊗ y') - (x, y)(x', y')` as an additive function of `x'`. -/
def extFormDefectRight (x : K0 𝒜) (y : K0 𝒜) (y' : K0 ℬ) : K0 ℬ →+ LaurentSeries ℤ where
  toFun x' := homForm (tensorGrading 𝒜 ℬ) (extTensor 𝒜 ℬ x x') (extTensor 𝒜 ℬ y y') -
    homForm 𝒜 x y * homForm ℬ x' y'
  map_zero' := by simp
  map_add' x₁ x₂ := by
    simp only [map_add, AddMonoidHom.add_apply, mul_add]
    abel

theorem extFormDefectLeft_shift (x' : K0 ℬ) (y : K0 𝒜) (y' : K0 ℬ) (a : ℤ) (x : K0 𝒜) :
    extFormDefectLeft x' y y' (shiftHom a x) =
      HahnSeries.single (-a) 1 * extFormDefectLeft x' y y' x := by
  simp only [extFormDefectLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, extTensor_apply]
  rw [extTensorAdd_shift_left, ← T_smul, ← T_smul, homForm_T_smul_left, homForm_T_smul_left,
    mul_sub, mul_assoc]

theorem extFormDefectRight_shift (x : K0 𝒜) (y : K0 𝒜) (y' : K0 ℬ) (a : ℤ) (x' : K0 ℬ) :
    extFormDefectRight x y y' (shiftHom a x') =
      HahnSeries.single (-a) 1 * extFormDefectRight x y y' x' := by
  simp only [extFormDefectRight, AddMonoidHom.coe_mk, ZeroHom.coe_mk, extTensor_apply]
  rw [extTensorAdd_shift_right, ← T_smul, ← T_smul, homForm_T_smul_left, homForm_T_smul_left,
    mul_sub, mul_left_comm]

/-- **Product formula on the span of idempotent classes**:
`(x ⊗ x', y ⊗ y') = (x, y) · (x', y')` for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes
`[A e]`, `[B e']` (degree-zero idempotents `e`, `e'`) and arbitrary `y`, `y'`. -/
theorem homForm_extTensor_of_mem_span {x : K0 𝒜} {x' : K0 ℬ}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses 𝒜))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (idemClasses ℬ)) (y : K0 𝒜) (y' : K0 ℬ) :
    homForm (tensorGrading 𝒜 ℬ) (extTensor 𝒜 ℬ x x') (extTensor 𝒜 ℬ y y') =
      homForm 𝒜 x y * homForm ℬ x' y' := by
  have key : extFormDefectLeft x' y y' x = 0 := by
    refine map_eq_zero_of_mem_span (extFormDefectLeft_shift x' y y') ?_ hx
    rintro _ ⟨e, he, he0, rfl⟩
    refine map_eq_zero_of_mem_span (extFormDefectRight_shift _ y y') ?_ hx'
    rintro _ ⟨e', he', he0', rfl⟩
    simp only [extFormDefectRight, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [homForm_extTensor_ofIdempotent, sub_self]
  exact sub_eq_zero.1 key

end K0

end Form

end Categorification.Graded

end
