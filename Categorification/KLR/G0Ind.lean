/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.K0Algebra
import Categorification.KLR.Crystal.IndDecomp
import Categorification.KLR.ExtTensorK0Equiv

/-!
# The Grothendieck algebra `G₀(R)` (KL I, Proposition 3.1, `G₀` part: `[Ind]`)

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1 (TeX lines 1882–1935), **Proposition 3.1**:

> `[Ind]` turns `K₀(R)` and `G₀(R)` into associative unital `ℤ[q,q⁻¹]`-algebras.

The `K₀` statement is `Categorification.KLR.K0Algebra`. Here we prove the `G₀` statement. The
induction functor `Ind_{ν,ν'} N = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} N` takes the external
tensor product `M ⊠ M'` of finite-dimensional graded modules to a finite-dimensional graded
`R(ν + ν')`-module, and it is exact in each variable. Both facts come from Proposition 2.16 in its
right-module form (`KLRAlgebra.indDecomp`: `Ind N ≅ ⊕_u N` as vector spaces, naturally in `N`,
the sum over the shuffles `u`), together with the exactness of `⊗_k` over the field `k`. Hence
`[Ind]` is a well defined `ℤ[q, q⁻¹]`-bilinear map on `G₀`; the associativity and unit
isomorphisms are those used for `K₀` (`KLRAlgebra.assocEquiv`, `unitLEquiv`, `unitREquiv`, which
are degree-preserving for arbitrary graded modules).

## Main definitions and results

* `Graded.G0.lift₂`, `Graded.G0.map_smul_of_shift` : maps out of `G₀`.
* `KLRAlgebra.indDecomp_mapRight` : the decomposition `Ind N ≅ ⊕_u N` is natural in `N`; hence
  `Ind` preserves injections and exact sequences (`KLRAlgebra.mapRight_injective`,
  `KLRAlgebra.mapRight_exact`).
* `GradingDatum.indFin hPQ hP M M'` : `Ind_{ν,ν'} (M ⊠ M')` as an object of `R(ν + ν')-fmod`,
  and `GradingDatum.indFinSESLeft`, `GradingDatum.indFinSESRight` : it is exact in each variable.
* `GradingDatum.indG0 hPQ hP ν ν'` : **the `ℤ[q, q⁻¹]`-bilinear map
  `[Ind] : G₀(R(ν)) × G₀(R(ν')) → G₀(R(ν + ν'))`**, `[M] ⊗ [M'] ↦ [Ind_{ν,ν'} (M ⊠ M')]`.
* `GradingDatum.indG0_assoc`, `GradingDatum.indG0_one_left`, `GradingDatum.indG0_one_right` :
  associativity and unitality, the unit being `[R(0)] = [k]` (`R(0) = k 1_∅` is one-dimensional).
* `GradingDatum.G0R G hPQ hP hG` : `G₀(R) = ⨁_ν G₀(R(ν))` with its `DirectSum.GRing` and
  `DirectSum.GAlgebra ℤ[q, q⁻¹]` structures, hence a `Ring` and an `Algebra ℤ[q, q⁻¹]`
  (**KL I, Proposition 3.1 for `G₀`, algebra part**), whose multiplication on homogeneous
  components is `[Ind]` (`G0R_of_mul_of`) and whose unit is `[R(0)]` (`G0R_one`).

## Hypotheses

`k` is a field and `Q` satisfies the hypotheses `hPQ`, `hP` of the basis theorem (used for
Proposition 2.16). The family `G0fam G hPQ hP hG` is a type synonym for `ν ↦ G₀(R(ν))` carrying
the hypotheses in its type, so that the ring structure can be an instance; `hG` (dots of positive
degree) is not used for the algebra structure, but it is needed for the coalgebra structure of
`Categorification.KLR.Prop31G0`, which lives on the same type.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

/-! ### Maps out of `G₀` -/

namespace Graded.G0

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  {k' : Type*} [Field k'] {A' : Type*} [Ring A'] [Algebra k' A'] {𝒜' : ℤ → Submodule k' A'}
  {Γ : Type*} [AddCommGroup Γ]

/-- `G0.lift` with explicit binders in its hypotheses. -/
def liftE (φ : GFin 𝒜 → Γ) (hiso : ∀ M N : GFin 𝒜, M.Iso N → φ M = φ N)
    (hses : ∀ M N P : GFin 𝒜, GFin.ShortExact M N P → φ N = φ M + φ P) : G0 𝒜 →+ Γ :=
  lift φ (fun e => hiso _ _ e) (fun S => hses _ _ _ S)

@[simp] theorem liftE_of (φ : GFin 𝒜 → Γ) (hiso : ∀ M N : GFin 𝒜, M.Iso N → φ M = φ N)
    (hses : ∀ M N P : GFin 𝒜, GFin.ShortExact M N P → φ N = φ M + φ P) (M : GFin 𝒜) :
    liftE φ hiso hses (of M) = φ M :=
  lift_of φ (fun e => hiso _ _ e) (fun S => hses _ _ _ S) M

/-- A biadditive map `G₀(A) × G₀(A') → Γ` from a function on pairs of objects which is
isomorphism-invariant and additive on short exact sequences in each variable. -/
def lift₂ (f : GFin 𝒜 → GFin 𝒜' → Γ)
    (hiso₁ : ∀ (M₁ M₂ : GFin 𝒜) (N : GFin 𝒜'), M₁.Iso M₂ → f M₁ N = f M₂ N)
    (hiso₂ : ∀ (M : GFin 𝒜) (N₁ N₂ : GFin 𝒜'), N₁.Iso N₂ → f M N₁ = f M N₂)
    (hses₁ : ∀ (M₁ M₂ M₃ : GFin 𝒜) (N : GFin 𝒜'), GFin.ShortExact M₁ M₂ M₃ →
      f M₂ N = f M₁ N + f M₃ N)
    (hses₂ : ∀ (M : GFin 𝒜) (N₁ N₂ N₃ : GFin 𝒜'), GFin.ShortExact N₁ N₂ N₃ →
      f M N₂ = f M N₁ + f M N₃) :
    G0 𝒜 →+ G0 𝒜' →+ Γ :=
  liftE (fun M => liftE (f M) (hiso₂ M) (hses₂ M))
    (fun M₁ M₂ e => hom_ext fun N => by rw [liftE_of, liftE_of, hiso₁ M₁ M₂ N e])
    (fun M₁ M₂ M₃ S => hom_ext fun N => by
      rw [AddMonoidHom.add_apply, liftE_of, liftE_of, liftE_of, hses₁ M₁ M₂ M₃ N S])

@[simp] theorem lift₂_of (f : GFin 𝒜 → GFin 𝒜' → Γ)
    (hiso₁ : ∀ (M₁ M₂ : GFin 𝒜) (N : GFin 𝒜'), M₁.Iso M₂ → f M₁ N = f M₂ N)
    (hiso₂ : ∀ (M : GFin 𝒜) (N₁ N₂ : GFin 𝒜'), N₁.Iso N₂ → f M N₁ = f M N₂)
    (hses₁ : ∀ (M₁ M₂ M₃ : GFin 𝒜) (N : GFin 𝒜'), GFin.ShortExact M₁ M₂ M₃ →
      f M₂ N = f M₁ N + f M₃ N)
    (hses₂ : ∀ (M : GFin 𝒜) (N₁ N₂ N₃ : GFin 𝒜'), GFin.ShortExact N₁ N₂ N₃ →
      f M N₂ = f M N₁ + f M N₃) (M : GFin 𝒜) (N : GFin 𝒜') :
    lift₂ f hiso₁ hiso₂ hses₁ hses₂ (of M) (of N) = f M N := by
  rw [lift₂, liftE_of, liftE_of]

/-- `c q^a` acts on `G₀` by `c` times the shift by `a`. -/
theorem C_mul_T_smul (a c : ℤ) (x : G0 𝒜) :
    (LaurentPolynomial.C c * LaurentPolynomial.T a : LaurentPolynomial ℤ) • x =
      c • shiftHom a x := by
  rw [mul_smul, T_smul, LaurentPolynomial.C_eq_algebraMap, algebraMap_smul]

/-- An additive map between `G₀` groups commuting with the grading shifts is
`ℤ[q, q⁻¹]`-linear. -/
theorem map_smul_of_shift (f : G0 𝒜 →+ G0 𝒜')
    (hf : ∀ (a : ℤ) (x : G0 𝒜), f (shiftHom a x) = shiftHom a (f x))
    (p : LaurentPolynomial ℤ) (x : G0 𝒜) : f (p • x) = p • f x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, add_smul, map_add, hp, hp']
  | C_mul_T a c => rw [C_mul_T_smul, C_mul_T_smul, map_zsmul, hf]

/-- An additive map from `G₀` to a `ℤ[q, q⁻¹]`-module commuting with the grading shifts is
`ℤ[q, q⁻¹]`-linear. -/
theorem map_smul_of_shift' {V : Type*} [AddCommGroup V] [Module (LaurentPolynomial ℤ) V]
    (f : G0 𝒜 →+ V)
    (hf : ∀ (a : ℤ) (x : G0 𝒜), f (shiftHom a x) = (LaurentPolynomial.T a : LaurentPolynomial ℤ) •
      f x)
    (p : LaurentPolynomial ℤ) (x : G0 𝒜) : f (p • x) = p • f x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, add_smul, map_add, hp, hp']
  | C_mul_T a c =>
    rw [C_mul_T_smul, map_zsmul, hf, mul_smul, LaurentPolynomial.C_eq_algebraMap,
      algebraMap_smul]

end Graded.G0

namespace Graded.GFin

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-- The identity `M{a} → M` as a linear equivalence (of ungraded modules). -/
def shiftLinearEquiv (M : GFin 𝒜) (a : ℤ) : (M.shift a).carrier ≃ₗ[A] M.carrier :=
  LinearEquiv.refl _ _

theorem shiftLinearEquiv_preservesGrading (M : GFin 𝒜) (a : ℤ) :
    PreservesGrading (M.shift a).grading (Graded.shift M.grading a)
      (M.shiftLinearEquiv a).toLinearMap :=
  fun _ _ h => h

end Graded.GFin

/-! ### Exactness of `⊠` over a field -/

namespace ExtTensor

variable {k : Type*} [Field k] {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {P₁ P₂ P₃ : Type*} [AddCommGroup P₁] [Module k P₁] [Module A P₁] [IsScalarTower k A P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A P₂] [IsScalarTower k A P₂]
  [AddCommGroup P₃] [Module k P₃] [Module A P₃] [IsScalarTower k A P₃]
  {Q₁ Q₂ Q₃ : Type*} [AddCommGroup Q₁] [Module k Q₁] [Module B Q₁] [IsScalarTower k B Q₁]
  [AddCommGroup Q₂] [Module k Q₂] [Module B Q₂] [IsScalarTower k B Q₂]
  [AddCommGroup Q₃] [Module k Q₃] [Module B Q₃] [IsScalarTower k B Q₃]

theorem coe_map_id_left (f : P₁ →ₗ[A] P₂) :
    ⇑(map (k := k) f (LinearMap.id : Q₁ →ₗ[B] Q₁)) = ⇑((f.restrictScalars k).rTensor Q₁) := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul p q => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem coe_map_id_right (g : Q₁ →ₗ[B] Q₂) :
    ⇑(map (k := k) (LinearMap.id : P₁ →ₗ[A] P₁) g) = ⇑((g.restrictScalars k).lTensor P₁) := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul p q => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_id_injective_left {f : P₁ →ₗ[A] P₂} (hf : Function.Injective f) :
    Function.Injective (map (k := k) f (LinearMap.id : Q₁ →ₗ[B] Q₁)) := by
  rw [coe_map_id_left]
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := Q₁) (f.restrictScalars k) hf

theorem map_id_injective_right {g : Q₁ →ₗ[B] Q₂} (hg : Function.Injective g) :
    Function.Injective (map (k := k) (LinearMap.id : P₁ →ₗ[A] P₁) g) := by
  rw [coe_map_id_right]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := P₁) (g.restrictScalars k) hg

theorem map_id_exact_left {f : P₁ →ₗ[A] P₂} {g : P₂ →ₗ[A] P₃} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (map (k := k) f (LinearMap.id : Q₁ →ₗ[B] Q₁))
      (map (k := k) g (LinearMap.id : Q₁ →ₗ[B] Q₁)) := by
  rw [coe_map_id_left, coe_map_id_left]
  exact rTensor_exact Q₁ (f := f.restrictScalars k) (g := g.restrictScalars k) hfg hg

theorem map_id_exact_right {f : Q₁ →ₗ[B] Q₂} {g : Q₂ →ₗ[B] Q₃} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (map (k := k) (LinearMap.id : P₁ →ₗ[A] P₁) f)
      (map (k := k) (LinearMap.id : P₁ →ₗ[A] P₁) g) := by
  rw [coe_map_id_right, coe_map_id_right]
  exact lTensor_exact P₁ (f := f.restrictScalars k) (g := g.restrictScalars k) hfg hg

end ExtTensor

namespace KLR

open Graded KLRAlgebra MulOpposite

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-! ### Exactness of induction -/

namespace KLRAlgebra

section Exact

variable {ν ν' : Multiset I}
  {N₁ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (TensorKLR Q ν ν') N₁]
    [IsScalarTower k (TensorKLR Q ν ν') N₁]
  {N₂ : Type*} [AddCommGroup N₂] [Module k N₂] [Module (TensorKLR Q ν ν') N₂]
    [IsScalarTower k (TensorKLR Q ν ν') N₂]
  {N₃ : Type*} [AddCommGroup N₃] [Module k N₃] [Module (TensorKLR Q ν ν') N₃]
    [IsScalarTower k (TensorKLR Q ν ν') N₃]

/-- `Ind` applied to a map `g : N₁ → N₂`, `r ⊗ n ↦ r ⊗ g n`. -/
abbrev indMap (g : N₁ →ₗ[TensorKLR Q ν ν'] N₂) :
    Ind Q ν ν' N₁ →ₗ[KLRAlgebra k Q (ν + ν')] Ind Q ν ν' N₂ :=
  BalancedTensor.mapRight g

/-- **The decomposition `Ind N ≅ ⊕_u N` is natural in `N`.** -/
theorem indDecomp_mapRight (g : N₁ →ₗ[TensorKLR Q ν ν'] N₂) (y : Ind Q ν ν' N₁) :
    indDecomp hPQ hP N₂ (indMap g y) = fun u => g (indDecomp hPQ hP N₁ y u) := by
  induction y using BalancedTensor.induction_on with
  | zero =>
    rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero]
    funext u
    exact (LinearMap.map_zero g).symm
  | tmul r n =>
    funext u
    rw [indMap, BalancedTensor.mapRight_tmul, indDecomp_tmul, indDecomp_tmul, map_smul]
  | add x y hx hy =>
    rw [LinearMap.map_add, LinearEquiv.map_add, LinearEquiv.map_add, hx, hy]
    funext u
    exact (LinearMap.map_add g _ _).symm

include hPQ hP in
/-- `Ind` preserves injections. -/
theorem mapRight_injective {g : N₁ →ₗ[TensorKLR Q ν ν'] N₂} (hg : Function.Injective g) :
    Function.Injective (indMap (Q := Q) g) := by
  intro x y h
  apply (indDecomp hPQ hP N₁).injective
  funext u
  apply hg
  have := congrFun (congrArg (indDecomp hPQ hP N₂) h) u
  rwa [indDecomp_mapRight, indDecomp_mapRight] at this

include hPQ hP in
/-- `Ind` preserves exact sequences. -/
theorem mapRight_exact {f : N₁ →ₗ[TensorKLR Q ν ν'] N₂} {g : N₂ →ₗ[TensorKLR Q ν ν'] N₃}
    (hfg : Function.Exact f g) : Function.Exact (indMap (Q := Q) f) (indMap (Q := Q) g) := by
  intro y
  constructor
  · intro hy
    have h1 : ∀ u, g (indDecomp hPQ hP N₂ y u) = 0 := fun u => by
      have := congrFun (congrArg (indDecomp hPQ hP N₃) hy) u
      rwa [indDecomp_mapRight, LinearEquiv.map_zero] at this
    choose x hx using fun u => (hfg _).1 (h1 u)
    refine ⟨(indDecomp hPQ hP N₁).symm x, (indDecomp hPQ hP N₂).injective ?_⟩
    rw [indDecomp_mapRight, LinearEquiv.apply_symm_apply]
    funext u
    exact hx u
  · rintro ⟨x, rfl⟩
    apply (indDecomp hPQ hP N₃).injective
    rw [indDecomp_mapRight, indDecomp_mapRight, LinearEquiv.map_zero]
    funext u
    exact hfg.apply_apply_eq_zero _

end Exact

end KLRAlgebra

namespace GradingDatum

variable (G : GradingDatum Q) {ν ν' ν'' : Multiset I}

/-! ### Induction of finite-dimensional graded modules -/

section IndFin

/-- **`Ind_{ν,ν'} (M ⊠ M')`** for finite-dimensional graded `M`, `M'`: a finite-dimensional
graded `R(ν + ν')`-module. -/
def indFin (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) : GFin (G.grade (ν + ν')) :=
  haveI : FiniteDimensional k (ExtTensor k M.carrier M'.carrier) :=
    inferInstanceAs (FiniteDimensional k (M.carrier ⊗[k] M'.carrier))
  { toGMod :=
      { carrier := Ind Q ν ν' (ExtTensor k M.carrier M'.carrier)
        grading := G.indGrading ν ν' (ExtTensor.grading M.grading M'.grading)
        decomposition := balancedDecomposition (tensorGrading (G.grade ν) (G.grade ν'))
          (fun _ _ _ _ hm ht => G.op_smul_mem_bimodGrading hm ht)
        gradedSMul := gradedSMul_balanced (G.grade (ν + ν')) }
    finiteDimensional := finiteDimensional_ind hPQ hP _ }

theorem indFin_carrier (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) :
    (G.indFin hPQ hP M M').carrier = Ind Q ν ν' (ExtTensor k M.carrier M'.carrier) := rfl

theorem indFin_grading (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) :
    (G.indFin hPQ hP M M').grading = G.indGrading ν ν' (ExtTensor.grading M.grading M'.grading) :=
  rfl

/-- `Ind (M₁ ⊠ M₁') ≅ Ind (M₂ ⊠ M₂')` for `M₁ ≅ M₂`, `M₁' ≅ M₂'`. -/
def indFinCongr {M₁ M₂ : GFin (G.grade ν)} {M₁' M₂' : GFin (G.grade ν')} (e : M₁.Iso M₂)
    (e' : M₁'.Iso M₂') : (G.indFin hPQ hP M₁ M₁').Iso (G.indFin hPQ hP M₂ M₂') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr e.toLinearEquiv
    e'.toLinearEquiv)) fun _ y hy =>
      mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
        (ExtTensor.map_preservesGrading e.preservesGrading e'.preservesGrading) (y := y) hy

/-- `Ind (M{a} ⊠ M') ≅ Ind (M ⊠ M'){a}`. -/
def indFinShiftLeft (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) (a : ℤ) :
    (G.indFin hPQ hP (M.shift a) M').Iso ((G.indFin hPQ hP M M').shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr (M.shiftLinearEquiv a)
      (LinearEquiv.refl _ M'.carrier))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν'))
      (ℳ := G.bimodGrading ν ν') (𝒩' := ExtTensor.grading (shift M.grading a) M'.grading)
      (ExtTensor.map_preservesGrading (M.shiftLinearEquiv_preservesGrading a)
        (g := (LinearEquiv.refl (KLRAlgebra k Q ν') M'.carrier).toLinearMap)
        (fun _ _ h => h)) (y := y) hy
    rw [ExtTensor.grading_shift_left, balancedGrading_shift_right] at h
    exact h

/-- `Ind (M ⊠ M'{a}) ≅ Ind (M ⊠ M'){a}`. -/
def indFinShiftRight (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) (a : ℤ) :
    (G.indFin hPQ hP M (M'.shift a)).Iso ((G.indFin hPQ hP M M').shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr
      (LinearEquiv.refl _ M.carrier) (M'.shiftLinearEquiv a))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν'))
      (ℳ := G.bimodGrading ν ν') (𝒩' := ExtTensor.grading M.grading (shift M'.grading a))
      (ExtTensor.map_preservesGrading
        (f := (LinearEquiv.refl (KLRAlgebra k Q ν) M.carrier).toLinearMap) (fun _ _ h => h)
        (M'.shiftLinearEquiv_preservesGrading a)) (y := y) hy
    rw [ExtTensor.grading_shift_right, balancedGrading_shift_right] at h
    exact h

/-- **`Ind (- ⊠ M')` is exact**: a short exact sequence `0 → M₁ → M₂ → M₃ → 0` gives a short
exact sequence `0 → Ind (M₁ ⊠ M') → Ind (M₂ ⊠ M') → Ind (M₃ ⊠ M') → 0`. -/
def indFinSESLeft {M₁ M₂ M₃ : GFin (G.grade ν)} (S : GFin.ShortExact M₁ M₂ M₃)
    (M' : GFin (G.grade ν')) :
    GFin.ShortExact (G.indFin hPQ hP M₁ M') (G.indFin hPQ hP M₂ M') (G.indFin hPQ hP M₃ M') where
  f := indMap (ExtTensor.map S.f LinearMap.id)
  g := indMap (ExtTensor.map S.g LinearMap.id)
  preservesGrading_f _ _ hy :=
    mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
      (ExtTensor.map_preservesGrading S.preservesGrading_f (fun _ _ h => h)) hy
  preservesGrading_g _ _ hy :=
    mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
      (ExtTensor.map_preservesGrading S.preservesGrading_g (fun _ _ h => h)) hy
  injective := mapRight_injective hPQ hP (ExtTensor.map_id_injective_left S.injective)
  surjective := BalancedTensor.mapRight_surjective
    (ExtTensor.map_surjective S.surjective Function.surjective_id)
  exact := mapRight_exact hPQ hP (ExtTensor.map_id_exact_left S.exact S.surjective)

/-- **`Ind (M ⊠ -)` is exact.** -/
def indFinSESRight (M : GFin (G.grade ν)) {M₁ M₂ M₃ : GFin (G.grade ν')}
    (S : GFin.ShortExact M₁ M₂ M₃) :
    GFin.ShortExact (G.indFin hPQ hP M M₁) (G.indFin hPQ hP M M₂) (G.indFin hPQ hP M M₃) where
  f := indMap (ExtTensor.map LinearMap.id S.f)
  g := indMap (ExtTensor.map LinearMap.id S.g)
  preservesGrading_f _ _ hy :=
    mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
      (ExtTensor.map_preservesGrading (fun _ _ h => h) S.preservesGrading_f) hy
  preservesGrading_g _ _ hy :=
    mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
      (ExtTensor.map_preservesGrading (fun _ _ h => h) S.preservesGrading_g) hy
  injective := mapRight_injective hPQ hP (ExtTensor.map_id_injective_right S.injective)
  surjective := BalancedTensor.mapRight_surjective
    (ExtTensor.map_surjective Function.surjective_id S.surjective)
  exact := mapRight_exact hPQ hP (ExtTensor.map_id_exact_right S.exact S.surjective)

end IndFin

/-! ### `[Ind]` on `G₀` -/

section IndG0

variable (ν ν') in
/-- The biadditive map `G₀(R(ν)) × G₀(R(ν')) → G₀(R(ν + ν'))`,
`([M], [M']) ↦ [Ind_{ν,ν'} (M ⊠ M')]`. -/
def indG0Add : G0 (G.grade ν) →+ G0 (G.grade ν') →+ G0 (G.grade (ν + ν')) :=
  G0.lift₂ (fun M M' => G0.of (G.indFin hPQ hP M M'))
    (fun _ _ _ e => G0.of_eq_of_iso (G.indFinCongr hPQ hP e (GradedEquiv.refl _)))
    (fun _ _ _ e => G0.of_eq_of_iso (G.indFinCongr hPQ hP (GradedEquiv.refl _) e))
    (fun _ _ _ M' S => G0.of_eq_add_of_shortExact (G.indFinSESLeft hPQ hP S M'))
    (fun M _ _ _ S => G0.of_eq_add_of_shortExact (G.indFinSESRight hPQ hP M S))

@[simp] theorem indG0Add_of (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) :
    G.indG0Add hPQ hP ν ν' (G0.of M) (G0.of M') = G0.of (G.indFin hPQ hP M M') :=
  G0.lift₂_of _ _ _ _ _ M M'

theorem indG0Add_shift_left (a : ℤ) (x : G0 (G.grade ν)) (y : G0 (G.grade ν')) :
    G.indG0Add hPQ hP ν ν' (G0.shiftHom a x) y = G0.shiftHom a (G.indG0Add hPQ hP ν ν' x y) := by
  induction x using G0.induction_on with
  | of M =>
    induction y using G0.induction_on with
    | of M' =>
      rw [G0.shiftHom_of, indG0Add_of, indG0Add_of, G0.shiftHom_of]
      exact G0.of_eq_of_iso (G.indFinShiftLeft hPQ hP M M' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

theorem indG0Add_shift_right (a : ℤ) (x : G0 (G.grade ν)) (y : G0 (G.grade ν')) :
    G.indG0Add hPQ hP ν ν' x (G0.shiftHom a y) = G0.shiftHom a (G.indG0Add hPQ hP ν ν' x y) := by
  induction x using G0.induction_on with
  | of M =>
    induction y using G0.induction_on with
    | of M' =>
      rw [G0.shiftHom_of, indG0Add_of, indG0Add_of, G0.shiftHom_of]
      exact G0.of_eq_of_iso (G.indFinShiftRight hPQ hP M M' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

variable (ν ν') in
/-- **The `ℤ[q, q⁻¹]`-bilinear map `[Ind] : G₀(R(ν)) × G₀(R(ν')) → G₀(R(ν + ν'))`** of KL I,
§3.1: `[M] ⊗ [M'] ↦ [Ind_{ν,ν'} (M ⊠ M')]`. -/
def indG0 : G0 (G.grade ν) →ₗ[LaurentPolynomial ℤ] G0 (G.grade ν') →ₗ[LaurentPolynomial ℤ]
    G0 (G.grade (ν + ν')) :=
  LinearMap.mk₂ (LaurentPolynomial ℤ) (fun x y => G.indG0Add hPQ hP ν ν' x y)
    (fun x x' y => by simp only [map_add, AddMonoidHom.add_apply])
    (fun p x y => G0.map_smul_of_shift ((G.indG0Add hPQ hP ν ν').flip y)
      (fun a x => G.indG0Add_shift_left hPQ hP a x y) p x)
    (fun x y y' => map_add _ y y')
    (fun p x y => G0.map_smul_of_shift (G.indG0Add hPQ hP ν ν' x)
      (fun a y => G.indG0Add_shift_right hPQ hP a x y) p y)

@[simp] theorem indG0_apply (x : G0 (G.grade ν)) (y : G0 (G.grade ν')) :
    G.indG0 hPQ hP ν ν' x y = G.indG0Add hPQ hP ν ν' x y := rfl

/-- `[M] · [M'] = [Ind_{ν,ν'} (M ⊠ M')]`. -/
theorem indG0_of (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) :
    G.indG0 hPQ hP ν ν' (G0.of M) (G0.of M') = G0.of (G.indFin hPQ hP M M') :=
  G.indG0Add_of hPQ hP M M'

end IndG0

/-! ### Transport of `G₀` along equalities of weights -/

section Cast

variable {μ μ' : Multiset I}

/-- The identification `G₀(R(μ)) ≅ G₀(R(μ'))` for `μ = μ'`. -/
def G0cast (h : μ = μ') : G0 (G.grade μ) →+ G0 (G.grade μ') := by
  subst h; exact AddMonoidHom.id _

@[simp] theorem G0cast_rfl (x : G0 (G.grade μ)) : G.G0cast rfl x = x := rfl

theorem G0cast_trans {μ'' : Multiset I} (h : μ = μ') (h' : μ' = μ'') (x : G0 (G.grade μ)) :
    G.G0cast h' (G.G0cast h x) = G.G0cast (h.trans h') x := by
  subst h; subst h'; rfl

theorem G0cast_smul (h : μ = μ') (p : LaurentPolynomial ℤ) (x : G0 (G.grade μ)) :
    G.G0cast h (p • x) = p • G.G0cast h x := by
  subst h; rfl

/-- `G0cast` on classes: an isomorphism `X ≅ Y` of the underlying `k`-modules which is
semilinear along `castKLR : R(μ) ≃ R(μ')` and degree-preserving identifies `[X]` with `[Y]`. -/
theorem G0cast_of_linearEquiv (h : μ = μ') (X : GFin (G.grade μ)) (Y : GFin (G.grade μ'))
    (φ : X.carrier ≃ₗ[k] Y.carrier)
    (hφ : ∀ (b : KLRAlgebra k Q μ) (x : X.carrier), φ (b • x) = castKLR Q h b • φ x)
    (hgr : ∀ ⦃d : ℤ⦄ ⦃x : X.carrier⦄, x ∈ X.grading d → φ x ∈ Y.grading d) :
    G.G0cast h (G0.of X) = G0.of Y := by
  subst h
  rw [G0cast_rfl]
  exact G0.of_eq_of_iso (GradedEquiv.ofPreserves
    (φ.toAddEquiv.toLinearEquiv fun b x => (hφ b x).trans (by rw [castKLR_rfl]; rfl))
    (fun _ _ hx => hgr hx))

end Cast

/-! ### Associativity and unitality -/

section Assoc

theorem G0cast_indFin_assoc (M : GFin (G.grade ν)) (M' : GFin (G.grade ν'))
    (M'' : GFin (G.grade ν'')) :
    G.G0cast (add_assoc ν ν' ν'') (G0.of (G.indFin hPQ hP (G.indFin hPQ hP M M') M'')) =
      G0.of (G.indFin hPQ hP M (G.indFin hPQ hP M' M'')) :=
  G.G0cast_of_linearEquiv _ _ _ (assocEquiv Q ν ν' ν'' M.carrier M'.carrier M''.carrier)
    (fun b x => assocEquiv_smul M.carrier M'.carrier M''.carrier b x)
    (fun _ _ hx => G.assocFwd_mem_grading M.grading M'.grading M''.grading hx)

/-- **Associativity of `[Ind]` on `G₀`** (KL I, Proposition 3.1): for all `x ∈ G₀(R(ν))`,
`y ∈ G₀(R(ν'))`, `z ∈ G₀(R(ν''))`, `(x y) z = x (y z)` (after identifying
`G₀(R((ν + ν') + ν'')) = G₀(R(ν + (ν' + ν'')))`). -/
theorem indG0_assoc (x : G0 (G.grade ν)) (y : G0 (G.grade ν')) (z : G0 (G.grade ν'')) :
    G.G0cast (add_assoc ν ν' ν'') (G.indG0 hPQ hP (ν + ν') ν'' (G.indG0 hPQ hP ν ν' x y) z) =
      G.indG0 hPQ hP ν (ν' + ν'') x (G.indG0 hPQ hP ν' ν'' y z) := by
  induction x using G0.induction_on with
  | of M =>
    induction y using G0.induction_on with
    | of M' =>
      induction z using G0.induction_on with
      | of M'' =>
        rw [indG0_of, indG0_of, indG0_of, indG0_of]
        exact G.G0cast_indFin_assoc hPQ hP M M' M''
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | neg z hz => simp only [map_neg, hz]
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | neg y hy => simp only [map_neg, LinearMap.neg_apply, hy]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

include hPQ hP in
/-- `R(0) = k 1_∅` is finite-dimensional. -/
theorem finiteDimensional_zero : FiniteDimensional k (KLRAlgebra k Q 0) := by
  classical
  let B := KLRAlgebra.basis hPQ hP (fun w : Equiv.Perm (Fin (Multiset.card (0 : Multiset I))) =>
      TypeA.canWord _ w)
    (fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩)
  haveI : Finite (Fin (Multiset.card (0 : Multiset I)) →₀ ℕ) := by
    haveI : IsEmpty (Fin (Multiset.card (0 : Multiset I))) := by
      rw [Multiset.card_zero]; exact Fin.isEmpty'
    infer_instance
  exact FiniteDimensional.of_fintype_basis B

/-- The unit module `R(0) = k`, graded by `G.grade 0`, as an object of `R(0)-fmod`. -/
def unitFin : GFin (G.grade (0 : Multiset I)) :=
  { toGMod := GMod.regular (G.grade 0)
    finiteDimensional := finiteDimensional_zero hPQ hP }

/-- The unit `[R(0)] ∈ G₀(R(0))`. -/
def G0one : G0 (G.grade (0 : Multiset I)) := G0.of (G.unitFin hPQ hP)

/-- **Left unitality of `[Ind]` on `G₀`**: `[R(0)] x = x`. -/
theorem indG0_one_left (x : G0 (G.grade ν)) :
    G.G0cast (zero_add ν) (G.indG0 hPQ hP 0 ν (G.G0one hPQ hP) x) = x := by
  induction x using G0.induction_on with
  | of M =>
    rw [G0one, indG0_of]
    exact G.G0cast_of_linearEquiv _ _ _ (unitLEquiv Q ν M.carrier)
      (fun b x => unitLEquiv_smul M.carrier b x)
      (fun _ _ hx => G.unitLFwd_mem_grading M.grading hx)
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

/-- **Right unitality of `[Ind]` on `G₀`**: `x [R(0)] = x`. -/
theorem indG0_one_right (x : G0 (G.grade ν)) :
    G.G0cast (add_zero ν) (G.indG0 hPQ hP ν 0 x (G.G0one hPQ hP)) = x := by
  induction x using G0.induction_on with
  | of M =>
    rw [G0one, indG0_of]
    exact G.G0cast_of_linearEquiv _ _ _ (unitREquiv Q ν M.carrier)
      (fun b x => unitREquiv_smul M.carrier b x)
      (fun _ _ hx => G.unitRFwd_mem_grading M.grading hx)
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

end Assoc

/-! ### The algebra `G₀(R) = ⨁_ν G₀(R(ν))` -/

section G0R

variable (hG : ∀ a, 0 < G.degX a)

/-- The family `ν ↦ G₀(R(ν))`, a type synonym recording the hypotheses `hPQ`, `hP`, `hG` (so
that the algebra and coalgebra structures of `G₀(R)` can be instances). -/
@[nolint unusedArguments]
def G0fam (_hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
    (_hP : ∀ a b, a ≠ b → P a b ≠ 0) (_hG : ∀ a, 0 < G.degX a) (ν : Multiset I) : Type _ :=
  G0 (G.grade ν)

instance (ν : Multiset I) : AddCommGroup (G.G0fam hPQ hP hG ν) :=
  inferInstanceAs (AddCommGroup (G0 (G.grade ν)))

instance (ν : Multiset I) : Module (LaurentPolynomial ℤ) (G.G0fam hPQ hP hG ν) :=
  inferInstanceAs (Module (LaurentPolynomial ℤ) (G0 (G.grade ν)))

/-- An element of `G₀(R(ν))` as an element of the family. -/
def toG0fam {ν : Multiset I} : G0 (G.grade ν) ≃ₗ[LaurentPolynomial ℤ] G.G0fam hPQ hP hG ν :=
  LinearEquiv.refl _ _

instance gMulG0 : GradedMonoid.GMul (G.G0fam hPQ hP hG) where
  mul {ν ν'} x y := G.indG0 hPQ hP ν ν' x y

instance gOneG0 : GradedMonoid.GOne (G.G0fam hPQ hP hG) where
  one := G.G0one hPQ hP

theorem G0_gMul_def {ν ν' : Multiset I} (x : G.G0fam hPQ hP hG ν) (y : G.G0fam hPQ hP hG ν') :
    GradedMonoid.GMul.mul (A := G.G0fam hPQ hP hG) x y = G.indG0 hPQ hP ν ν' x y :=
  rfl

theorem G0_mk_mul_mk {ν ν' : Multiset I} (x : G.G0fam hPQ hP hG ν) (y : G.G0fam hPQ hP hG ν') :
    GradedMonoid.mk (A := G.G0fam hPQ hP hG) ν x * GradedMonoid.mk ν' y =
      GradedMonoid.mk (A := G.G0fam hPQ hP hG) (ν + ν') (G.indG0 hPQ hP ν ν' x y) := rfl

theorem G0_mk_cast {μ μ' : Multiset I} (h : μ = μ') (x : G.G0fam hPQ hP hG μ) :
    GradedMonoid.mk (A := G.G0fam hPQ hP hG) μ x =
      GradedMonoid.mk (A := G.G0fam hPQ hP hG) μ' (G.G0cast h x) := by
  subst h; rfl

theorem G0_one_mk_mul {ν : Multiset I} (x : G.G0fam hPQ hP hG ν) :
    (1 : GradedMonoid (G.G0fam hPQ hP hG)) * GradedMonoid.mk ν x = GradedMonoid.mk ν x := by
  show GradedMonoid.mk (A := G.G0fam hPQ hP hG) (0 + ν) (G.indG0 hPQ hP 0 ν (G.G0one hPQ hP) x) = _
  rw [G.G0_mk_cast hPQ hP hG (zero_add ν), indG0_one_left]

theorem G0_mk_mul_one {ν : Multiset I} (x : G.G0fam hPQ hP hG ν) :
    GradedMonoid.mk (A := G.G0fam hPQ hP hG) ν x * (1 : GradedMonoid (G.G0fam hPQ hP hG)) =
      GradedMonoid.mk ν x := by
  show GradedMonoid.mk (A := G.G0fam hPQ hP hG) (ν + 0) (G.indG0 hPQ hP ν 0 x (G.G0one hPQ hP)) = _
  rw [G.G0_mk_cast hPQ hP hG (add_zero ν), indG0_one_right]

instance gMonoidG0 : GradedMonoid.GMonoid (G.G0fam hPQ hP hG) where
  one_mul a := by obtain ⟨ν, x⟩ := a; exact G.G0_one_mk_mul hPQ hP hG x
  mul_one a := by obtain ⟨ν, x⟩ := a; exact G.G0_mk_mul_one hPQ hP hG x
  mul_assoc a b c := by
    obtain ⟨ν, x⟩ := a
    obtain ⟨ν', y⟩ := b
    obtain ⟨ν'', z⟩ := c
    show GradedMonoid.mk (A := G.G0fam hPQ hP hG) ν x * GradedMonoid.mk ν' y *
        GradedMonoid.mk ν'' z =
      GradedMonoid.mk (A := G.G0fam hPQ hP hG) ν x * (GradedMonoid.mk ν' y * GradedMonoid.mk ν'' z)
    rw [G0_mk_mul_mk, G0_mk_mul_mk, G0_mk_mul_mk, G0_mk_mul_mk,
      G.G0_mk_cast hPQ hP hG (add_assoc ν ν' ν'')]
    exact congrArg _ (G.indG0_assoc hPQ hP x y z)

instance gRingG0 : DirectSum.GRing (G.G0fam hPQ hP hG) where
  mul_zero {ν ν'} x := by rw [G0_gMul_def, map_zero]
  zero_mul {ν ν'} y := by rw [G0_gMul_def, map_zero, LinearMap.zero_apply]
  mul_add {ν ν'} x y y' := by rw [G0_gMul_def, G0_gMul_def, G0_gMul_def, map_add]
  add_mul {ν ν'} x x' y := by
    rw [G0_gMul_def, G0_gMul_def, G0_gMul_def, map_add, LinearMap.add_apply]
  natCast n := n • (G.G0one hPQ hP : G.G0fam hPQ hP hG 0)
  natCast_zero := zero_smul _ _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • (G.G0one hPQ hP : G.G0fam hPQ hP hG 0)
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

instance gAlgebraG0 : DirectSum.GAlgebra (LaurentPolynomial ℤ) (G.G0fam hPQ hP hG) where
  toFun :=
    { toFun := fun p => p • (G.G0one hPQ hP : G.G0fam hPQ hP hG 0)
      map_zero' := zero_smul _ _
      map_add' := fun p p' => add_smul _ _ _ }
  map_one := one_smul _ _
  map_mul r s := by
    show GradedMonoid.mk (A := G.G0fam hPQ hP hG) 0 ((r * s) • G.G0one hPQ hP) =
      GradedMonoid.mk (0 + 0) (G.indG0 hPQ hP 0 0 (r • G.G0one hPQ hP) (s • G.G0one hPQ hP))
    rw [G.G0_mk_cast hPQ hP hG (zero_add (0 : Multiset I))]
    simp only [LinearMap.map_smul₂, LinearMap.map_smul, LinearMap.smul_apply, G0cast_smul]
    rw [indG0_one_left, mul_smul]
  commutes r x := by
    obtain ⟨ν, x⟩ := x
    show GradedMonoid.mk (A := G.G0fam hPQ hP hG) (0 + ν)
        (G.indG0 hPQ hP 0 ν (r • G.G0one hPQ hP) x) =
      GradedMonoid.mk (ν + 0) (G.indG0 hPQ hP ν 0 x (r • G.G0one hPQ hP))
    rw [G.G0_mk_cast hPQ hP hG (zero_add ν), G.G0_mk_cast hPQ hP hG (add_zero ν)]
    simp only [LinearMap.map_smul₂, LinearMap.map_smul, LinearMap.smul_apply, G0cast_smul]
    rw [indG0_one_left, indG0_one_right]
  smul_def r x := by
    obtain ⟨ν, x⟩ := x
    show GradedMonoid.mk (A := G.G0fam hPQ hP hG) ν (r • x) =
      GradedMonoid.mk (0 + ν) (G.indG0 hPQ hP 0 ν (r • G.G0one hPQ hP) x)
    rw [G.G0_mk_cast hPQ hP hG (zero_add ν)]
    simp only [LinearMap.map_smul₂, LinearMap.smul_apply, G0cast_smul]
    rw [indG0_one_left]

/-- **The Grothendieck algebra** `G₀(R) = ⨁_{ν ∈ ℕ[I]} G₀(R(ν))` (KL I, §3.1, Proposition 3.1):
an associative unital `ℤ[q, q⁻¹]`-algebra (`inferInstance : Algebra (LaurentPolynomial ℤ) _`)
whose product on homogeneous components is `[Ind]` (`G0R_of_mul_of`) and whose unit is
`[R(0)]` (`G0R_one`). -/
abbrev G0R : Type _ := DirectSum (Multiset I) (G.G0fam hPQ hP hG)

example : Ring (G.G0R hPQ hP hG) := inferInstance

example : Algebra (LaurentPolynomial ℤ) (G.G0R hPQ hP hG) := inferInstance

/-- The product on `G₀(R)` of homogeneous elements is `[Ind]`. -/
theorem G0R_of_mul_of {ν ν' : Multiset I} (x : G.G0fam hPQ hP hG ν) (y : G.G0fam hPQ hP hG ν') :
    (DirectSum.of (G.G0fam hPQ hP hG) ν x * DirectSum.of (G.G0fam hPQ hP hG) ν' y :
        G.G0R hPQ hP hG) =
      DirectSum.of (G.G0fam hPQ hP hG) (ν + ν') (G.indG0 hPQ hP ν ν' x y) :=
  DirectSum.of_mul_of (A := G.G0fam hPQ hP hG) x y

/-- The unit of `G₀(R)` is `[R(0)]`. -/
theorem G0R_one :
    (1 : G.G0R hPQ hP hG) = DirectSum.of (G.G0fam hPQ hP hG) 0 (G0.of (G.unitFin hPQ hP)) :=
  rfl

/-- `[M] [M'] = [Ind (M ⊠ M')]` in `G₀(R)`. -/
theorem G0R_of_of_mul_of_of {ν ν' : Multiset I} (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')) :
    (DirectSum.of (G.G0fam hPQ hP hG) ν (G0.of M) * DirectSum.of (G.G0fam hPQ hP hG) ν' (G0.of M') :
        G.G0R hPQ hP hG) =
      DirectSum.of (G.G0fam hPQ hP hG) (ν + ν') (G0.of (G.indFin hPQ hP M M')) := by
  rw [G0R_of_mul_of]
  exact congrArg _ (G.indG0_of hPQ hP M M')

/-- The `ℤ[q, q⁻¹]`-algebra structure: `algebraMap p = p [R(0)]`. -/
theorem G0R_algebraMap (p : LaurentPolynomial ℤ) :
    algebraMap (LaurentPolynomial ℤ) (G.G0R hPQ hP hG) p =
      DirectSum.of (G.G0fam hPQ hP hG) 0 (p • G0.of (G.unitFin hPQ hP)) :=
  rfl

end G0R

end GradingDatum

end KLR

end Categorification

end
