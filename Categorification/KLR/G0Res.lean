/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.G0Ind
import Categorification.KLR.TensorKLRK0
import Categorification.KLR.ResK0

/-!
# `[Res]` on `G₀`, and `G₀(R(ν) ⊗ R(ν')) ≅ G₀(R(ν)) ⊗ G₀(R(ν'))`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1 (TeX lines 1905–1925): restriction for the inclusion
`R(ν) ⊗ R(ν') ⊂ R(ν + ν')` restricts to finite-dimensional modules and induces
`[Res] : G₀(R(ν + ν')) → G₀(R(ν)) ⊗ G₀(R(ν'))`, "the tensor products here and further are over
`ℤ[q, q⁻¹]`". This file provides the two ingredients:

* the exact functor `Res_{ν,ν'} M = 1_{ν,ν'} M` on finite-dimensional graded modules
  (`GradingDatum.resFin`, `GradingDatum.resFinSES`) and the `ℤ[q, q⁻¹]`-linear map
  `GradingDatum.resG0 : G₀(R(ν + ν')) → G₀(R(ν) ⊗ R(ν'))`;
* the identification `G₀(A) ⊗_{ℤ[q,q⁻¹]} G₀(B) ≅ G₀(A ⊗ B)`, `[M] ⊗ [M'] ↦ [M ⊠ M']`, for graded
  algebras satisfying the hypotheses `Graded.TensorK0Hyp` (finite-dimensional, absolutely
  irreducible graded simples; they hold for `A = R(ν)`, `B = R(ν')`,
  `GradingDatum.tensorK0Hyp`): `Graded.TensorK0Hyp.g0ExtTensorEquiv` and its KLR instance
  `GradingDatum.g0TensorEquiv`. It maps the basis `[S_b] ⊗ [S_{b'}]` to `q^{-a_c} [S_c]`, where
  `S_c ≅ (S_b ⊠ S_{b'}){a_c}` are the graded simple `A ⊗ B`-modules
  (`Graded.TensorK0Hyp.top_iso`).

The external tensor product of finite-dimensional graded modules is exact in each variable
over the field `k` (`Graded.GFin.extTensorSESLeft`, `Graded.GFin.extTensorSESRight`), which gives
the `ℤ[q, q⁻¹]`-bilinear map `Graded.G0.extTensor : G₀(A) × G₀(B) → G₀(A ⊗ B)`.
-/

noncomputable section

universe u v

namespace Categorification

open scoped TensorProduct

namespace Graded

open GProj

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  {B : Type u} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B}

/-! ### `⊠` on finite-dimensional graded modules -/

namespace GFin

/-- `M₁ ⊠ M₁' ≅ M₂ ⊠ M₂'` for `M₁ ≅ M₂`, `M₁' ≅ M₂'`. -/
def extTensorCongr {M₁ M₂ : GFin 𝒜} {M₁' M₂' : GFin ℬ} (e : M₁.Iso M₂) (e' : M₁'.Iso M₂') :
    (M₁.extTensor M₁').Iso (M₂.extTensor M₂') :=
  GradedEquiv.ofPreserves (ExtTensor.congr e.toLinearEquiv e'.toLinearEquiv)
    (ExtTensor.map_preservesGrading e.preservesGrading e'.preservesGrading)

/-- `M{a} ⊠ M' ≅ (M ⊠ M'){a}`. -/
def extTensorShiftLeft (M : GFin 𝒜) (M' : GFin ℬ) (a : ℤ) :
    ((M.shift a).extTensor M').Iso ((M.extTensor M').shift a) :=
  GradedEquiv.ofPreserves (ExtTensor.congr (M.shiftLinearEquiv a) (LinearEquiv.refl _ M'.carrier))
    fun _ y hy => by
      have h := ExtTensor.map_preservesGrading (M.shiftLinearEquiv_preservesGrading a)
        (g := (LinearEquiv.refl B M'.carrier).toLinearMap) (fun _ _ h => h) hy
      rw [ExtTensor.grading_shift_left] at h
      exact h

/-- `M ⊠ M'{a} ≅ (M ⊠ M'){a}`. -/
def extTensorShiftRight (M : GFin 𝒜) (M' : GFin ℬ) (a : ℤ) :
    (M.extTensor (M'.shift a)).Iso ((M.extTensor M').shift a) :=
  GradedEquiv.ofPreserves (ExtTensor.congr (LinearEquiv.refl _ M.carrier) (M'.shiftLinearEquiv a))
    fun _ y hy => by
      have h := ExtTensor.map_preservesGrading (f := (LinearEquiv.refl A M.carrier).toLinearMap)
        (fun _ _ h => h) (M'.shiftLinearEquiv_preservesGrading a) hy
      rw [ExtTensor.grading_shift_right] at h
      exact h

/-- `- ⊠ M'` is exact. -/
def extTensorSESLeft {M₁ M₂ M₃ : GFin 𝒜} (S : ShortExact M₁ M₂ M₃) (M' : GFin ℬ) :
    ShortExact (M₁.extTensor M') (M₂.extTensor M') (M₃.extTensor M') where
  f := ExtTensor.map S.f LinearMap.id
  g := ExtTensor.map S.g LinearMap.id
  preservesGrading_f := ExtTensor.map_preservesGrading S.preservesGrading_f (fun _ _ h => h)
  preservesGrading_g := ExtTensor.map_preservesGrading S.preservesGrading_g (fun _ _ h => h)
  injective := ExtTensor.map_id_injective_left S.injective
  surjective := ExtTensor.map_surjective S.surjective Function.surjective_id
  exact := ExtTensor.map_id_exact_left S.exact S.surjective

/-- `M ⊠ -` is exact. -/
def extTensorSESRight (M : GFin 𝒜) {M₁ M₂ M₃ : GFin ℬ} (S : ShortExact M₁ M₂ M₃) :
    ShortExact (M.extTensor M₁) (M.extTensor M₂) (M.extTensor M₃) where
  f := ExtTensor.map LinearMap.id S.f
  g := ExtTensor.map LinearMap.id S.g
  preservesGrading_f := ExtTensor.map_preservesGrading (fun _ _ h => h) S.preservesGrading_f
  preservesGrading_g := ExtTensor.map_preservesGrading (fun _ _ h => h) S.preservesGrading_g
  injective := ExtTensor.map_id_injective_right S.injective
  surjective := ExtTensor.map_surjective Function.surjective_id S.surjective
  exact := ExtTensor.map_id_exact_right S.exact S.surjective

end GFin

namespace G0

variable (𝒜 ℬ) in
/-- The biadditive map `G₀(A) × G₀(B) → G₀(A ⊗ B)`, `([M], [M']) ↦ [M ⊠ M']`. -/
def extTensorAdd : G0 𝒜 →+ G0 ℬ →+ G0 (tensorGrading 𝒜 ℬ) :=
  lift₂ (fun M M' => of (M.extTensor M'))
    (fun _ _ _ e => of_eq_of_iso (GFin.extTensorCongr e (GradedEquiv.refl _)))
    (fun _ _ _ e => of_eq_of_iso (GFin.extTensorCongr (GradedEquiv.refl _) e))
    (fun _ _ _ M' S => of_eq_add_of_shortExact (GFin.extTensorSESLeft S M'))
    (fun M _ _ _ S => of_eq_add_of_shortExact (GFin.extTensorSESRight M S))

@[simp] theorem extTensorAdd_of (M : GFin 𝒜) (M' : GFin ℬ) :
    extTensorAdd 𝒜 ℬ (of M) (of M') = of (M.extTensor M') :=
  lift₂_of _ _ _ _ _ M M'

theorem extTensorAdd_shift_left (a : ℤ) (x : G0 𝒜) (y : G0 ℬ) :
    extTensorAdd 𝒜 ℬ (shiftHom a x) y = shiftHom a (extTensorAdd 𝒜 ℬ x y) := by
  induction x using G0.induction_on with
  | of M =>
    induction y using G0.induction_on with
    | of M' =>
      rw [shiftHom_of, extTensorAdd_of, extTensorAdd_of, shiftHom_of]
      exact of_eq_of_iso (GFin.extTensorShiftLeft M M' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

theorem extTensorAdd_shift_right (a : ℤ) (x : G0 𝒜) (y : G0 ℬ) :
    extTensorAdd 𝒜 ℬ x (shiftHom a y) = shiftHom a (extTensorAdd 𝒜 ℬ x y) := by
  induction x using G0.induction_on with
  | of M =>
    induction y using G0.induction_on with
    | of M' =>
      rw [shiftHom_of, extTensorAdd_of, extTensorAdd_of, shiftHom_of]
      exact of_eq_of_iso (GFin.extTensorShiftRight M M' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

variable (𝒜 ℬ) in
/-- **The `ℤ[q, q⁻¹]`-bilinear map `G₀(A) × G₀(B) → G₀(A ⊗ B)`**, `[M] ⊗ [M'] ↦ [M ⊠ M']`. -/
def extTensor : G0 𝒜 →ₗ[LaurentPolynomial ℤ] G0 ℬ →ₗ[LaurentPolynomial ℤ]
    G0 (tensorGrading 𝒜 ℬ) :=
  LinearMap.mk₂ (LaurentPolynomial ℤ) (fun x y => extTensorAdd 𝒜 ℬ x y)
    (fun x x' y => by simp only [map_add, AddMonoidHom.add_apply])
    (fun p x y => map_smul_of_shift ((extTensorAdd 𝒜 ℬ).flip y)
      (fun a x => extTensorAdd_shift_left a x y) p x)
    (fun x y y' => map_add _ y y')
    (fun p x y => map_smul_of_shift (extTensorAdd 𝒜 ℬ x)
      (fun a y => extTensorAdd_shift_right a x y) p y)

@[simp] theorem extTensor_of (M : GFin 𝒜) (M' : GFin ℬ) :
    extTensor 𝒜 ℬ (of M) (of M') = of (M.extTensor M') :=
  extTensorAdd_of M M'

end G0

/-! ### `G₀(A) ⊗ G₀(B) ≅ G₀(A ⊗ B)` -/

namespace TensorK0Hyp

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]
  (H : TensorK0Hyp 𝒜 ℬ)

/-- `[S_c] = q^{a_c} [S_{b} ⊠ S_{b'}]` for `S_c ≅ (S_b ⊠ S_{b'}){a_c}`. -/
theorem g0_of_topFin (c : IndecClass (tensorGrading 𝒜 ℬ)) :
    G0.of (IndecClass.topFin H.fdC c) =
      (LaurentPolynomial.T (H.shift c) : LaurentPolynomial ℤ) • G0.of (H.topT (H.fst c) (H.snd c)) := by
  rw [G0.T_smul_of]
  obtain ⟨e⟩ := H.top_iso c
  exact G0.of_eq_of_iso e

/-- `[S_b ⊠ S_{b'}] = q^{-a_c} [S_c]`, `c = indecClassEquiv⁻¹ (b, b')`. -/
theorem g0_of_topT (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    G0.of (H.topT b b') =
      (LaurentPolynomial.T (-H.shift (H.indecClassEquiv.symm (b, b'))) : LaurentPolynomial ℤ) •
        G0.of (IndecClass.topFin H.fdC (H.indecClassEquiv.symm (b, b'))) := by
  set c := H.indecClassEquiv.symm (b, b') with hc
  have hcb : H.indecClassEquiv c = (b, b') := by rw [hc, Equiv.apply_symm_apply]
  rw [indecClassEquiv_apply, Prod.mk.injEq] at hcb
  rw [H.g0_of_topFin c, smul_smul, ← LaurentPolynomial.T_add, neg_add_cancel,
    LaurentPolynomial.T_zero, one_smul, hcb.1, hcb.2]

omit H in
/-- **The isomorphism `G₀(A) ⊗_{ℤ[q,q⁻¹]} G₀(B) ≅ G₀(A ⊗ B)`**, `x ⊗ y ↦ x ⊠ y`
(`g0ExtTensorEquiv_tmul`): it maps the basis `[S_b] ⊗ [S_{b'}]` to the basis `q^{-a_c} [S_c]`,
`c = indecClassEquiv⁻¹ (b, b')`. -/
def g0ExtTensorEquiv (H : TensorK0Hyp 𝒜 ℬ) :
    G0 𝒜 ⊗[LaurentPolynomial ℤ] G0 ℬ ≃ₗ[LaurentPolynomial ℤ] G0 (tensorGrading 𝒜 ℬ) :=
  ((G0.topBasis H.fdA).tensorProduct (G0.topBasis H.fdB)).equiv
    ((G0.topBasis H.fdC).unitsSMul fun c => unitT (-H.shift c))
    H.indecClassEquiv.symm

theorem g0ExtTensorEquiv_toLinearMap :
    H.g0ExtTensorEquiv.toLinearMap = TensorProduct.lift (G0.extTensor 𝒜 ℬ) := by
  refine ((G0.topBasis H.fdA).tensorProduct (G0.topBasis H.fdB)).ext fun i => ?_
  obtain ⟨b, b'⟩ := i
  rw [LinearEquiv.coe_coe, g0ExtTensorEquiv, Basis.equiv_apply, Basis.unitsSMul_apply,
    Basis.tensorProduct_apply, TensorProduct.lift.tmul, G0.topBasis_apply, G0.topBasis_apply,
    G0.topBasis_apply, G0.extTensor_of, Units.smul_def, coe_unitT]
  exact (H.g0_of_topT b b').symm

/-- `g0ExtTensorEquiv (x ⊗ y) = x ⊠ y`. -/
@[simp] theorem g0ExtTensorEquiv_tmul (x : G0 𝒜) (y : G0 ℬ) :
    H.g0ExtTensorEquiv (x ⊗ₜ y) = G0.extTensor 𝒜 ℬ x y := by
  rw [← LinearEquiv.coe_coe, g0ExtTensorEquiv_toLinearMap, TensorProduct.lift.tmul]

/-- The inverse of `g0ExtTensorEquiv` on classes: `[M ⊠ M'] ↦ [M] ⊗ [M']`. -/
theorem g0ExtTensorEquiv_symm_of (M : GFin 𝒜) (M' : GFin ℬ) :
    H.g0ExtTensorEquiv.symm (G0.of (M.extTensor M')) = G0.of M ⊗ₜ G0.of M' := by
  rw [LinearEquiv.symm_apply_eq, g0ExtTensorEquiv_tmul, G0.extTensor_of]

end TensorK0Hyp

end Graded

namespace KLR

open Graded KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' : Multiset I}

/-! ### Exactness of restriction -/

namespace KLRAlgebra

variable {N₁ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (KLRAlgebra k Q (ν + ν')) N₁]
    [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N₁]
  {N₂ : Type*} [AddCommGroup N₂] [Module k N₂] [Module (KLRAlgebra k Q (ν + ν')) N₂]
    [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N₂]
  {N₃ : Type*} [AddCommGroup N₃] [Module k N₃] [Module (KLRAlgebra k Q (ν + ν')) N₃]
    [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N₃]

theorem resIdemMap_injective {f : N₁ →ₗ[KLRAlgebra k Q (ν + ν')] N₂}
    (hf : Function.Injective f) : Function.Injective (resIdemMap (ν := ν) (ν' := ν') f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem resIdemMap_surjective {g : N₂ →ₗ[KLRAlgebra k Q (ν + ν')] N₃}
    (hg : Function.Surjective g) : Function.Surjective (resIdemMap (ν := ν) (ν' := ν') g) := by
  intro n
  obtain ⟨m, hm⟩ := hg (n : N₃)
  refine ⟨⟨oneConcat Q ν ν' • m, smul_mem_idemSubspace oneConcat_idem m⟩, Subtype.ext ?_⟩
  rw [coe_resIdemMap, map_smul, hm]
  exact n.2

theorem resIdemMap_exact {f : N₁ →ₗ[KLRAlgebra k Q (ν + ν')] N₂}
    {g : N₂ →ₗ[KLRAlgebra k Q (ν + ν')] N₃} (hfg : Function.Exact f g) :
    Function.Exact (resIdemMap (ν := ν) (ν' := ν') f) (resIdemMap (ν := ν) (ν' := ν') g) := by
  intro y
  constructor
  · intro hy
    have h0 : g (y : N₂) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (hfg _).1 h0
    refine ⟨⟨oneConcat Q ν ν' • x, smul_mem_idemSubspace oneConcat_idem x⟩, Subtype.ext ?_⟩
    rw [coe_resIdemMap, map_smul, hx]
    exact y.2
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (hfg.apply_apply_eq_zero (x : N₁))

end KLRAlgebra

namespace GradingDatum

variable (G : GradingDatum Q)

/-! ### Restriction of finite-dimensional graded modules -/

section ResFin

variable (ν ν') in
/-- **`Res_{ν,ν'} M = 1_{ν,ν'} M`** of a finite-dimensional graded `R(ν + ν')`-module, as a
finite-dimensional graded `R(ν) ⊗ R(ν')`-module. -/
def resFin (M : GFin (G.grade (ν + ν'))) : GFin (tensorGrading (G.grade ν) (G.grade ν')) :=
  { toGMod :=
      { carrier := ResIdem Q ν ν' M.carrier
        grading := idem M.grading (oneConcat Q ν ν')
        decomposition := idemDecomposition M.grading G.oneConcat_mem_grade
        gradedSMul := G.resIdem_gradedSMul M.grading }
    finiteDimensional := inferInstanceAs
      (FiniteDimensional k (idemSubspace k M.carrier (oneConcat Q ν ν'))) }

theorem resFin_carrier (M : GFin (G.grade (ν + ν'))) :
    (G.resFin ν ν' M).carrier = ResIdem Q ν ν' M.carrier := rfl

@[simp] theorem mem_resFin_grading {M : GFin (G.grade (ν + ν'))} {d : ℤ}
    {n : ResIdem Q ν ν' M.carrier} :
    n ∈ (G.resFin ν ν' M).grading d ↔ (n : M.carrier) ∈ M.grading d := Iff.rfl

/-- `Res M ≅ Res M'` for `M ≅ M'`. -/
def resFinCongr {M M' : GFin (G.grade (ν + ν'))} (e : M.Iso M') :
    (G.resFin ν ν' M).Iso (G.resFin ν ν' M') where
  toLinearEquiv := resIdemCongr e.toLinearEquiv
  map_mem' _ _ hx := e.map_mem hx
  symm_map_mem' _ _ hx := e.symm_map_mem' hx

/-- `Res (M{a}) = (Res M){a}`. -/
def resFinShift (M : GFin (G.grade (ν + ν'))) (a : ℤ) :
    (G.resFin ν ν' (M.shift a)).Iso ((G.resFin ν ν' M).shift a) where
  toLinearEquiv := LinearEquiv.refl _ _
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

/-- **`Res_{ν,ν'}` is exact.** -/
def resFinSES {M₁ M₂ M₃ : GFin (G.grade (ν + ν'))} (S : GFin.ShortExact M₁ M₂ M₃) :
    GFin.ShortExact (G.resFin ν ν' M₁) (G.resFin ν ν' M₂) (G.resFin ν ν' M₃) where
  f := resIdemMap S.f
  g := resIdemMap S.g
  preservesGrading_f _ _ hx := S.preservesGrading_f hx
  preservesGrading_g _ _ hx := S.preservesGrading_g hx
  injective := resIdemMap_injective S.injective
  surjective := resIdemMap_surjective S.surjective
  exact := resIdemMap_exact S.exact

variable (ν ν') in
/-- The additive map `[Res] : G₀(R(ν + ν')) → G₀(R(ν) ⊗ R(ν'))`, `[M] ↦ [1_{ν,ν'} M]`. -/
def resG0Add : G0 (G.grade (ν + ν')) →+ G0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  G0.liftE (fun M => G0.of (G.resFin ν ν' M)) (fun _ _ e => G0.of_eq_of_iso (G.resFinCongr e))
    (fun _ _ _ S => G0.of_eq_add_of_shortExact (G.resFinSES S))

@[simp] theorem resG0Add_of (M : GFin (G.grade (ν + ν'))) :
    G.resG0Add ν ν' (G0.of M) = G0.of (G.resFin ν ν' M) :=
  G0.liftE_of _ _ _ M

theorem resG0Add_shift (a : ℤ) (x : G0 (G.grade (ν + ν'))) :
    G.resG0Add ν ν' (G0.shiftHom a x) = G0.shiftHom a (G.resG0Add ν ν' x) := by
  induction x using G0.induction_on with
  | of M =>
    rw [G0.shiftHom_of, resG0Add_of, resG0Add_of, G0.shiftHom_of]
    exact G0.of_eq_of_iso (G.resFinShift M a)
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

variable (ν ν') in
/-- **`[Res] : G₀(R(ν + ν')) → G₀(R(ν) ⊗ R(ν'))`**, `[M] ↦ [1_{ν,ν'} M]`, a
`ℤ[q, q⁻¹]`-linear map. -/
def resG0 : G0 (G.grade (ν + ν')) →ₗ[LaurentPolynomial ℤ]
    G0 (tensorGrading (G.grade ν) (G.grade ν')) where
  toFun := G.resG0Add ν ν'
  map_add' := map_add _
  map_smul' := G0.map_smul_of_shift _ (G.resG0Add_shift (ν := ν) (ν' := ν'))

@[simp] theorem resG0_of (M : GFin (G.grade (ν + ν'))) :
    G.resG0 ν ν' (G0.of M) = G0.of (G.resFin ν ν' M) :=
  G.resG0Add_of M

end ResFin

/-! ### `G₀(R(ν) ⊗ R(ν')) ≅ G₀(R(ν)) ⊗ G₀(R(ν'))` -/

section TensorEquiv

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (hG : ∀ a, 0 < G.degX a)

/-- **KL I, §3.1: `G₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} G₀(R(ν')) ≅ G₀(R(ν) ⊗ R(ν'))`**, `x ⊗ y ↦ x ⊠ y`. -/
def g0TensorEquiv (ν ν' : Multiset I) :
    G0 (G.grade ν) ⊗[LaurentPolynomial ℤ] G0 (G.grade ν') ≃ₗ[LaurentPolynomial ℤ]
      G0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  (G.tensorK0Hyp hPQ hP hG ν ν').g0ExtTensorEquiv

@[simp] theorem g0TensorEquiv_tmul (x : G0 (G.grade ν)) (y : G0 (G.grade ν')) :
    G.g0TensorEquiv hPQ hP hG ν ν' (x ⊗ₜ y) = G0.extTensor (G.grade ν) (G.grade ν') x y := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  exact (G.tensorK0Hyp hPQ hP hG ν ν').g0ExtTensorEquiv_tmul x y

theorem g0TensorEquiv_symm_of (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) :
    (G.g0TensorEquiv hPQ hP hG ν ν').symm (G0.of (M.extTensor M')) = G0.of M ⊗ₜ G0.of M' := by
  rw [LinearEquiv.symm_apply_eq, g0TensorEquiv_tmul, G0.extTensor_of]

end TensorEquiv

end GradingDatum

end KLR

end Categorification

end
