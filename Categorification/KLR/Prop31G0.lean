/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.G0Res
import Categorification.KLR.Crystal.Thm317Graded

/-!
# KL I, Proposition 3.1 for `G₀`: `G₀(R)` is an algebra and a coalgebra

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1 (TeX lines 1882–1935):

> **Proposition 3.1.** `[Ind]` turns `K₀(R)` and `G₀(R)` into associative unital
> `ℤ[q,q⁻¹]`-algebras. `[Res]` turns `K₀(R)` and `G₀(R)` into coassociative counital
> `ℤ[q,q⁻¹]`-coalgebras.
>
> Proof follows from the associativity of induction and restriction. The unit element is given
> by inducing with the one-dimensional module over `R(∅)`. The counit is given by restricting
> to `R(∅)` and taking the graded dimension.

Here `G₀(R) = ⨁_ν G₀(R(ν))` and `[Res]` is the sum over all `ν, ν'` of the maps
`G₀(R(ν + ν')) → G₀(R(ν)) ⊗ G₀(R(ν'))` (tensor products over `ℤ[q, q⁻¹]`). The `K₀` statements
are `Categorification.KLR.K0Algebra` and `KLGamma.coassoc` (`Categorification.KLR.Bialgebra`).
The algebra structure on `G₀(R)` is `Categorification.KLR.G0Ind`; this file constructs the
coalgebra structure and proves **the `G₀` half of Proposition 3.1**.

## Definitions

* `GradingDatum.coprodG0` : **`Δ = [Res] : G₀(R) → G₀(R) ⊗ G₀(R)`**: on `G₀(R(μ))`, the sum over
  the decompositions `μ = ν + ν'` of `[Res_{ν,ν'}] : G₀(R(ν + ν')) → G₀(R(ν) ⊗ R(ν'))` followed by
  `G₀(R(ν) ⊗ R(ν')) ≅ G₀(R(ν)) ⊗ G₀(R(ν'))` (`GradingDatum.g0TensorEquiv`). Its components are the
  maps `[Res_{ν,ν'}]` (`GradingDatum.coprodG0_spec`).
* `GradingDatum.counitG0` : **`ε : G₀(R) → ℤ[q, q⁻¹]`**, the graded dimension of the
  `R(∅)`-component (`R(∅) = k`, so restriction to `R(∅)` is the `ν = 0` component).

## Main results

* `GradingDatum.coprodG0_coassoc` : `(Δ ⊗ 1) Δ = (1 ⊗ Δ) Δ` (up to the associativity of `⊗`).
* `GradingDatum.counitG0_rTensor_coprodG0`, `GradingDatum.counitG0_lTensor_coprodG0` :
  `(ε ⊗ 1) Δ x = 1 ⊗ x`, `(1 ⊗ ε) Δ x = x ⊗ 1`.
* `GradingDatum.instCoalgebraG0R` : `G₀(R)` is a `Coalgebra ℤ[q, q⁻¹]` (Mathlib's class of
  coassociative counital coalgebras) with `comul = Δ` and `counit = ε`.
* `GradingDatum.prop_3_1_G0` (**KL I, Proposition 3.1, `G₀` part**): the multiplication `[Ind]`
  of `G₀(R)` is associative and unital, and the comultiplication `[Res]` is coassociative and
  counital.
* `KL1.G0RKL` : `G₀(R)` for KL I's rings `R(ν)` (graph `Γ`, KL I's grading, which satisfies all
  hypotheses), an `Algebra` and a `Coalgebra` over `ℤ[q, q⁻¹]`.

## Proof of coassociativity and counitality

The paper's proof ("from the associativity of restriction") compares the functors
`(Res ⊗ 1) ∘ Res` and `(1 ⊗ Res) ∘ Res`. Rather than identifying Grothendieck groups of triple
tensor products, we use characters. The character map `ch : G₀(R(ν)) → ℤ[q, q⁻¹]^{Seq(ν)}` is
injective (KL I, Theorem 3.17, `KLRAlgebra.thm_3_17_G0`); assembling them gives an injective map
`chW : G₀(R) → (W →₀ ℤ[q, q⁻¹])`, `W = Σ_ν Seq(ν)` the set of all sequences
(`GradingDatum.chW_injective`). As `G₀(R)` is free, `chW ⊗ chW` and `(chW ⊗ chW) ⊗ chW` are still
injective (tensor products of injective maps of flat modules over the domain `ℤ[q, q⁻¹]`).
Restriction is the idempotent truncation `1_{ν,ν'} M`, so
`ch(Δ x)(i, j) = ch(x)(ij)` (`GradingDatum.chW2_coprodG0`): the character of the
`R(ν) ⊗ R(ν')`-module `1_{ν,ν'} M` at `(i, j)` is `gdim 1_{ij} M`, and under
`G₀(R(ν) ⊗ R(ν')) ≅ G₀(R(ν)) ⊗ G₀(R(ν'))` the character of `M ⊠ M'` at `(i, j)` is
`gdim (1_i M) · gdim (1_j M')`. Coassociativity is then the associativity of concatenation of
sequences, and counitality is `∅ i = i = i ∅` together with `1_∅ = 1` in `R(∅)`.

## Hypotheses

`k` is a field, `Q` satisfies the hypotheses `hPQ`, `hP` of the basis theorem, and the grading
datum has dots of positive degree (`hG`); these are the hypotheses of Theorem 3.17 and of the
identification `G₀(R(ν) ⊗ R(ν')) ≅ G₀(R(ν)) ⊗ G₀(R(ν'))`. KL I's grading
(`KLR.klGradingDatum`) satisfies them.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

/-! ### Generalities -/

namespace Graded

section LaurentMul

variable {R : Type*} [CommRing R]

theorem toLaurentSeries_single (a : ℤ) (c : R) :
    toLaurentSeries (Finsupp.single a c : LaurentPolynomial R) = HahnSeries.single a c := by
  ext n
  rw [coeff_toLaurentSeries, HahnSeries.coeff_single, Finsupp.single_apply]
  by_cases h : n = a
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- `R[q, q⁻¹] → R((q))` is multiplicative. -/
theorem toLaurentSeries_mul (p p' : LaurentPolynomial R) :
    toLaurentSeries (p * p') = toLaurentSeries p * toLaurentSeries p' := by
  induction p using Finsupp.induction_linear with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add p₁ p₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  | single a c =>
    induction p' using Finsupp.induction_linear with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add p₁ p₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
    | single b d =>
      erw [AddMonoidAlgebra.single_mul_single]
      rw [toLaurentSeries_single, toLaurentSeries_single, toLaurentSeries_single,
        HahnSeries.single_mul_single]

end LaurentMul

section GdimPoly

variable {k : Type*} [Field k] {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N]

/-- Gradings with the same dimensions in each degree have the same graded dimension. -/
theorem gdimPoly_eq_of_finrank_eq {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    (h : ∀ d, Module.finrank k (ℳ d) = Module.finrank k (𝒩 d)) : gdimPoly ℳ = gdimPoly 𝒩 := by
  have h' : (fun d => (Module.finrank k (ℳ d) : ℤ)) = fun d => (Module.finrank k (𝒩 d) : ℤ) :=
    funext fun d => by rw [h d]
  unfold gdimPoly
  rw [h']

end GdimPoly

section IdemCh

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [SetLike.GradedMonoid 𝒜] {e : A}

theorem gdimPoly_idem_hses (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) {M N P : GFin 𝒜}
    (S : GFin.ShortExact M N P) :
    gdimPoly (idem N.grading e) = gdimPoly (idem M.grading e) + gdimPoly (idem P.grading e) := by
  letI := idemDecomposition M.grading he0
  letI := idemDecomposition N.grading he0
  letI := idemDecomposition P.grading he0
  haveI := HasGdim.of_finiteDimensional N.grading
  apply toLaurentSeries_injective
  rw [map_add, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly]
  exact gdim_idem_eq_add_of_exact he he0 S.preservesGrading_f S.preservesGrading_g S.injective
    S.surjective S.exact

omit [SetLike.GradedMonoid 𝒜] in
theorem gdimPoly_idem_congr' {M N : GFin 𝒜} (f : M.Iso N) :
    gdimPoly (idem M.grading e) = gdimPoly (idem N.grading e) :=
  KLR.KLRAlgebra.gdimPoly_idem_congr f e

variable (𝒜) in
/-- The additive map `[M] ↦ gdim (e M)` on `G₀(A)`, for an idempotent `e` of degree `0`. -/
def G0.idemChAdd (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) : G0 𝒜 →+ LaurentPolynomial ℤ :=
  G0.liftE (fun M => gdimPoly (idem M.grading e)) (fun _ _ f => gdimPoly_idem_congr' f)
    (fun _ _ _ S => gdimPoly_idem_hses he he0 S)

@[simp] theorem G0.idemChAdd_of (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (M : GFin 𝒜) :
    G0.idemChAdd 𝒜 he he0 (G0.of M) = gdimPoly (idem M.grading e) :=
  G0.liftE_of _ _ _ M

theorem G0.idemChAdd_shift (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (a : ℤ) (x : G0 𝒜) :
    G0.idemChAdd 𝒜 he he0 (G0.shiftHom a x) =
      (LaurentPolynomial.T a : LaurentPolynomial ℤ) • G0.idemChAdd 𝒜 he he0 x := by
  induction x using G0.induction_on with
  | of M =>
    rw [G0.shiftHom_of, G0.idemChAdd_of, G0.idemChAdd_of, smul_eq_mul]
    letI := idemDecomposition M.grading he0
    exact gdimPoly_shift (idem M.grading e) a
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | neg x hx => rw [map_neg, map_neg, hx, map_neg, smul_neg]

variable (𝒜) in
/-- **The `e`-character** `G₀(A) → ℤ[q, q⁻¹]`, `[M] ↦ gdim (e M)`, a `ℤ[q, q⁻¹]`-linear map. -/
def G0.idemCh (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    G0 𝒜 →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ where
  toFun := G0.idemChAdd 𝒜 he he0
  map_add' := map_add _
  map_smul' := G0.map_smul_of_shift' _ (G0.idemChAdd_shift he he0)

@[simp] theorem G0.idemCh_of (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (M : GFin 𝒜) :
    G0.idemCh 𝒜 he he0 (G0.of M) = gdimPoly (idem M.grading e) :=
  G0.idemChAdd_of he he0 M

end IdemCh

section GdimLin

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

variable (𝒜) in
/-- The graded dimension `G₀(A) → ℤ[q, q⁻¹]` as a `ℤ[q, q⁻¹]`-linear map. -/
def G0.gdimLin : G0 𝒜 →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ where
  toFun := G0.gdim
  map_add' := map_add _
  map_smul' := G0.map_smul_of_shift' _ fun a x => by
    rw [← G0.T_smul, G0.gdim_T_smul, smul_eq_mul]

@[simp] theorem G0.gdimLin_of (M : GFin 𝒜) : G0.gdimLin 𝒜 (G0.of M) = gdimPoly M.grading :=
  G0.gdim_of M

end GdimLin

section ExtTensorIdem

universe u

variable {k : Type*} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}

/-- **`gdim ((e ⊗ e')(M ⊠ M')) = gdim (e M) · gdim (e' M')`** for idempotents of degree `0`. -/
theorem gdimPoly_idem_extTensor (M : GFin 𝒜) (M' : GFin ℬ) {e : A} {e' : B}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    gdimPoly (idem (M.extTensor M').grading (e ⊗ₜ[k] e')) =
      gdimPoly (idem M.grading e) * gdimPoly (idem M'.grading e') := by
  letI := idemDecomposition M.grading he0
  letI := idemDecomposition M'.grading he0'
  haveI := HasGdim.of_finiteDimensional (idem M.grading e)
  haveI := HasGdim.of_finiteDimensional (idem M'.grading e')
  refine (gdimPoly_eq_of_finrank_eq (𝒩 := tensorGrading (idem M.grading e) (idem M'.grading e'))
    (finrank_idem_extTensor he he' he0 he0')).trans ?_
  apply toLaurentSeries_injective
  rw [toLaurentSeries_mul, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly,
    toLaurentSeries_gdimPoly, gdim_tensorGrading]

end ExtTensorIdem

end Graded

/-! ### Tensor products of injective characters -/

section InjTensor

variable {R : Type*} [CommRing R] [IsDomain R] {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Module.Flat R V] [Module.Flat R W] {X Y : Type*}

/-- For injective maps `φ : V → (X →₀ R)`, `ψ : W → (Y →₀ R)` from flat modules over a domain,
`v ⊗ w ↦ ((x, y) ↦ φ v x · ψ w y)` is injective. -/
def charTensor (φ : V →ₗ[R] X →₀ R) (ψ : W →ₗ[R] Y →₀ R) : V ⊗[R] W →ₗ[R] X × Y →₀ R :=
  (finsuppTensorFinsupp' R X Y).toLinearMap ∘ₗ TensorProduct.map φ ψ

omit [IsDomain R] [Module.Flat R V] [Module.Flat R W] in
@[simp] theorem charTensor_tmul (φ : V →ₗ[R] X →₀ R) (ψ : W →ₗ[R] Y →₀ R) (v : V) (w : W)
    (x : X) (y : Y) : charTensor φ ψ (v ⊗ₜ w) (x, y) = φ v x * ψ w y := by
  simp [charTensor]

theorem charTensor_injective {φ : V →ₗ[R] X →₀ R} {ψ : W →ₗ[R] Y →₀ R}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    Function.Injective (charTensor φ ψ) :=
  (finsuppTensorFinsupp' R X Y).injective.comp
    (TensorProduct.map_injective_of_flat_flat_of_isDomain φ ψ hφ hψ)

end InjTensor

namespace KLR

open Graded KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)

local notation "LP" => LaurentPolynomial ℤ

namespace GradingDatum

/-! ### Components of `G₀(R) ⊗ G₀(R)` -/

section Components

/-- The projection `G₀(R) → G₀(R(μ))` onto the `μ`-component. -/
def G0proj (μ : Multiset I) : G.G0R hPQ hP hG →ₗ[LP] G0 (G.grade μ) :=
  (G.toG0fam hPQ hP hG).symm.toLinearMap ∘ₗ
    DirectSum.component LP (Multiset I) (G.G0fam hPQ hP hG) μ

/-- The inclusion `G₀(R(μ)) → G₀(R)` of the `μ`-component. -/
def G0incl (μ : Multiset I) : G0 (G.grade μ) →ₗ[LP] G.G0R hPQ hP hG :=
  DirectSum.lof LP (Multiset I) (G.G0fam hPQ hP hG) μ ∘ₗ (G.toG0fam hPQ hP hG).toLinearMap

theorem G0incl_apply (μ : Multiset I) (y : G0 (G.grade μ)) :
    G.G0incl hPQ hP hG μ y = DirectSum.of (G.G0fam hPQ hP hG) μ y := rfl

theorem G0proj_lof_self (μ : Multiset I) (y : G.G0fam hPQ hP hG μ) :
    G.G0proj hPQ hP hG μ (DirectSum.lof LP (Multiset I) (G.G0fam hPQ hP hG) μ y) = y := by
  rw [G0proj, LinearMap.comp_apply, DirectSum.component.lof_self]
  rfl

theorem G0proj_lof_of_ne {μ ν : Multiset I} (h : ν ≠ μ) (y : G.G0fam hPQ hP hG ν) :
    G.G0proj hPQ hP hG μ (DirectSum.lof LP (Multiset I) (G.G0fam hPQ hP hG) ν y) = 0 := by
  rw [G0proj, LinearMap.comp_apply, DirectSum.component.of, dif_neg h, LinearEquiv.coe_coe,
    LinearEquiv.map_zero]

theorem G0proj_incl_self (μ : Multiset I) (y : G0 (G.grade μ)) :
    G.G0proj hPQ hP hG μ (G.G0incl hPQ hP hG μ y) = y :=
  G.G0proj_lof_self hPQ hP hG μ y

theorem G0proj_incl_of_ne {μ ν : Multiset I} (h : ν ≠ μ) (y : G0 (G.grade ν)) :
    G.G0proj hPQ hP hG μ (G.G0incl hPQ hP hG ν y) = 0 :=
  G.G0proj_lof_of_ne hPQ hP hG h y

theorem G0proj_of_self (μ : Multiset I) (y : G0 (G.grade μ)) :
    G.G0proj hPQ hP hG μ (DirectSum.of (G.G0fam hPQ hP hG) μ y) = y :=
  G.G0proj_lof_self hPQ hP hG μ y

/-- The component map `G₀(R) ⊗ G₀(R) → G₀(R(ν)) ⊗ G₀(R(ν'))`. -/
def G0compTT (ν ν' : Multiset I) :
    G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG →ₗ[LP] G0 (G.grade ν) ⊗[LP] G0 (G.grade ν') :=
  TensorProduct.map (G.G0proj hPQ hP hG ν) (G.G0proj hPQ hP hG ν')

/-- The inclusion `G₀(R(ν)) ⊗ G₀(R(ν')) → G₀(R) ⊗ G₀(R)`. -/
def G0inclTT (ν ν' : Multiset I) :
    G0 (G.grade ν) ⊗[LP] G0 (G.grade ν') →ₗ[LP] G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG :=
  TensorProduct.map (G.G0incl hPQ hP hG ν) (G.G0incl hPQ hP hG ν')

theorem G0compTT_inclTT_self (ν ν' : Multiset I) (z : G0 (G.grade ν) ⊗[LP] G0 (G.grade ν')) :
    G.G0compTT hPQ hP hG ν ν' (G.G0inclTT hPQ hP hG ν ν' z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [G0inclTT, TensorProduct.map_tmul, G0compTT, TensorProduct.map_tmul, G0proj_incl_self,
      G0proj_incl_self]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem G0compTT_inclTT_of_ne {ν ν' μ μ' : Multiset I} (h : (ν, ν') ≠ (μ, μ'))
    (z : G0 (G.grade ν) ⊗[LP] G0 (G.grade ν')) :
    G.G0compTT hPQ hP hG μ μ' (G.G0inclTT hPQ hP hG ν ν' z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [G0inclTT, TensorProduct.map_tmul, G0compTT, TensorProduct.map_tmul]
    by_cases h1 : ν = μ
    · have h2 : ν' ≠ μ' := fun h2 => h (by rw [h1, h2])
      rw [G.G0proj_incl_of_ne hPQ hP hG h2, TensorProduct.tmul_zero]
    · rw [G.G0proj_incl_of_ne hPQ hP hG h1, TensorProduct.zero_tmul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', add_zero]

end Components

/-! ### The coproduct `Δ = [Res]` and the counit -/

section Coprod

/-- `[Res_{ν,ν'}]` on the `ν + ν'` component of `G₀(R)`. -/
def G0resComp (ν ν' : Multiset I) :
    G.G0R hPQ hP hG →ₗ[LP] G0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  G.resG0 ν ν' ∘ₗ G.G0proj hPQ hP hG (ν + ν')

/-- **`Δ = [Res] : G₀(R) → G₀(R) ⊗ G₀(R)`** (KL I, §3.1): on `G₀(R(μ))`, the sum over the
decompositions `μ = ν + ν'` of `[Res_{ν,ν'}]`, followed by
`G₀(R(ν) ⊗ R(ν')) ≅ G₀(R(ν)) ⊗ G₀(R(ν'))`. -/
def coprodG0 : G.G0R hPQ hP hG →ₗ[LP] G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG :=
  DirectSum.toModule LP (Multiset I) _ fun μ =>
    ∑ p ∈ (Multiset.antidiagonal μ).toFinset,
      G.G0inclTT hPQ hP hG p.1 p.2 ∘ₗ (G.g0TensorEquiv hPQ hP hG p.1 p.2).symm.toLinearMap ∘ₗ
        G.G0resComp hPQ hP hG p.1 p.2 ∘ₗ DirectSum.lof LP (Multiset I) (G.G0fam hPQ hP hG) μ

/-- **`Δ` is `[Res]`**: the `(ν, ν')`-component of `Δ x` is `[Res_{ν,ν'}] x_{ν+ν'}` under
`G₀(R(ν)) ⊗ G₀(R(ν')) ≅ G₀(R(ν) ⊗ R(ν'))`. -/
theorem coprodG0_spec (ν ν' : Multiset I) (x : G.G0R hPQ hP hG) :
    G.g0TensorEquiv hPQ hP hG ν ν' (G.G0compTT hPQ hP hG ν ν' (G.coprodG0 hPQ hP hG x)) =
      G.G0resComp hPQ hP hG ν ν' x := by
  rw [← LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearEquiv.map_zero]
  | add x y hx hy =>
    rw [LinearMap.map_add, LinearMap.map_add, hx, hy, LinearMap.map_add, LinearEquiv.map_add]
  | of μ y =>
    rw [coprodG0, ← DirectSum.lof_eq_of LP, DirectSum.toModule_lof, LinearMap.sum_apply, map_sum]
    by_cases hμ : ν + ν' = μ
    · rw [Finset.sum_eq_single (ν, ν')]
      · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          G0compTT_inclTT_self, LinearEquiv.coe_coe]
      · intro p _ hp
        rw [LinearMap.comp_apply]
        exact G.G0compTT_inclTT_of_ne hPQ hP hG hp _
      · intro h
        exact absurd (Multiset.mem_toFinset.2 (Multiset.mem_antidiagonal.2 hμ)) h
    · have h0 : G.G0resComp hPQ hP hG ν ν' (DirectSum.lof LP (Multiset I)
          (G.G0fam hPQ hP hG) μ y) = 0 := by
        rw [G0resComp, LinearMap.comp_apply, G.G0proj_lof_of_ne hPQ hP hG (Ne.symm hμ),
          LinearMap.map_zero]
      rw [h0, LinearEquiv.map_zero]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [LinearMap.comp_apply]
      refine G.G0compTT_inclTT_of_ne hPQ hP hG ?_ _
      intro he
      rw [Multiset.mem_toFinset, Multiset.mem_antidiagonal] at hp
      apply hμ
      rw [← hp, ← (Prod.mk.inj he).1, ← (Prod.mk.inj he).2]

/-- **The counit `ε : G₀(R) → ℤ[q, q⁻¹]`**: restriction to `R(∅)` (the `ν = 0` component)
followed by the graded dimension. -/
def counitG0 : G.G0R hPQ hP hG →ₗ[LP] LP :=
  G0.gdimLin (G.grade 0) ∘ₗ G.G0proj hPQ hP hG 0

@[simp] theorem counitG0_of (M : GFin (G.grade 0)) :
    G.counitG0 hPQ hP hG (DirectSum.of (G.G0fam hPQ hP hG) 0 (G0.of M)) = gdimPoly M.grading := by
  rw [counitG0, LinearMap.comp_apply, G0proj_of_self]
  exact G0.gdimLin_of M

end Coprod

/-! ### Characters on `G₀(R)` -/

section Characters

/-- All sequences `W = Σ_ν Seq(ν)`. -/
abbrev AllSeq (I : Type*) : Type _ := Σ μ : Multiset I, Seq μ

/-- Concatenation of sequences `(ν, i) · (ν', j) = (ν + ν', ij)`. -/
def AllSeq.append (a b : AllSeq I) : AllSeq I := ⟨a.1 + b.1, a.2.append b.2⟩

omit [DecidableEq I] in
theorem AllSeq.mk_cast {μ μ' : Multiset I} (h : μ = μ') (s : Seq μ) :
    (⟨μ, s⟩ : AllSeq I) = ⟨μ', Seq.cast h s⟩ := by
  subst h; rfl

omit [DecidableEq I] in
theorem AllSeq.append_assoc (a b c : AllSeq I) :
    (a.append b).append c = a.append (b.append c) := by
  obtain ⟨ν, i⟩ := a
  obtain ⟨ν', j⟩ := b
  obtain ⟨ν'', l⟩ := c
  show (⟨ν + ν' + ν'', (i.append j).append l⟩ : AllSeq I) = ⟨ν + (ν' + ν''), i.append (j.append l)⟩
  rw [AllSeq.mk_cast (add_assoc ν ν' ν''), Seq.append_assoc]

/-- The empty sequence. -/
def AllSeq.nil : AllSeq I := ⟨0, Seq.nil⟩

omit [DecidableEq I] in
theorem AllSeq.nil_append (b : AllSeq I) : AllSeq.nil.append b = b := by
  obtain ⟨ν, i⟩ := b
  show (⟨0 + ν, Seq.nil.append i⟩ : AllSeq I) = ⟨ν, i⟩
  rw [AllSeq.mk_cast (zero_add ν), Seq.nil_append]

omit [DecidableEq I] in
theorem AllSeq.append_nil (a : AllSeq I) : a.append AllSeq.nil = a := by
  obtain ⟨ν, i⟩ := a
  show (⟨ν + 0, i.append Seq.nil⟩ : AllSeq I) = ⟨ν, i⟩
  rw [AllSeq.mk_cast (add_zero ν), Seq.append_nil]

/-- The character of the `ν`-component, as a finitely supported function on all sequences. -/
def chFin (μ : Multiset I) : G0 (G.grade μ) →ₗ[LP] AllSeq I →₀ LP :=
  Finsupp.lmapDomain LP LP (Sigma.mk μ) ∘ₗ
    (Finsupp.linearEquivFunOnFinite LP LP (Seq μ)).symm.toLinearMap ∘ₗ chMap G (ν := μ)

/-- **The character map on `G₀(R)`**: `x ↦ ((ν, s) ↦ gdim (1_s x_ν))`. -/
def chW : G.G0R hPQ hP hG →ₗ[LP] AllSeq I →₀ LP :=
  DirectSum.toModule LP (Multiset I) _ fun μ =>
    G.chFin μ ∘ₗ (G.toG0fam hPQ hP hG (ν := μ)).symm.toLinearMap

theorem chFin_apply (μ : Multiset I) (y : G0 (G.grade μ)) (a : AllSeq I) :
    G.chFin μ y a = if h : a.1 = μ then chMap G (ν := μ) y (Seq.cast h a.2) else 0 := by
  obtain ⟨ν, s⟩ := a
  by_cases h : ν = μ
  · subst h
    rw [dif_pos rfl, chFin, LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_apply sigma_mk_injective, Seq.cast_rfl]
    rw [LinearEquiv.coe_coe]
    exact congrFun ((Finsupp.linearEquivFunOnFinite LP LP (Seq ν)).apply_symm_apply
      (chMap G y)) s
  · rw [dif_neg h, chFin, LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_notin_range]
    rintro ⟨s', hs'⟩
    exact h (congrArg Sigma.fst hs').symm

/-- `chW x (ν, s) = gdim (1_s x_ν)`. -/
theorem chW_apply (x : G.G0R hPQ hP hG) (μ : Multiset I) (s : Seq μ) :
    G.chW hPQ hP hG x ⟨μ, s⟩ = chMap G (ν := μ) (G.G0proj hPQ hP hG μ x) s := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, Finsupp.zero_apply, map_zero, Pi.zero_apply]
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, map_add, map_add, Pi.add_apply]
  | of ν y =>
    rw [chW, ← DirectSum.lof_eq_of LP, DirectSum.toModule_lof, LinearMap.comp_apply, chFin_apply]
    by_cases h : μ = ν
    · subst h
      rw [dif_pos rfl, G0proj_lof_self, Seq.cast_rfl]
      rfl
    · rw [dif_neg h, G.G0proj_lof_of_ne hPQ hP hG (Ne.symm h), LinearMap.map_zero]
      rfl

include hPQ hP hG in
/-- **The character map on `G₀(R)` is injective** (KL I, Theorem 3.17 in each weight). -/
theorem chW_injective : Function.Injective (G.chW hPQ hP hG) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  refine DirectSum.ext_component LP fun μ => ?_
  have h0 : G.G0proj hPQ hP hG μ x = 0 := by
    apply thm_3_17_G0 hPQ hP G hG
    funext s
    have := DFunLike.congr_fun hx ⟨μ, s⟩
    rw [chW_apply, Finsupp.zero_apply] at this
    rw [this, LinearMap.map_zero]
    rfl
  rw [LinearMap.map_zero]
  exact (G.toG0fam hPQ hP hG).symm.injective (h0.trans (LinearEquiv.map_zero _).symm)

instance (μ : Multiset I) : Module.Free LP (G.G0fam hPQ hP hG μ) :=
  G.g0_free hPQ hP hG μ

/-- The character of `G₀(R) ⊗ G₀(R)`: `x ⊗ y ↦ ((a, b) ↦ chW x a · chW y b)`. -/
def chW2 : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG →ₗ[LP] AllSeq I × AllSeq I →₀ LP :=
  charTensor (G.chW hPQ hP hG) (G.chW hPQ hP hG)

/-- The character of `(G₀(R) ⊗ G₀(R)) ⊗ G₀(R)`. -/
def chW3 : (G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG) ⊗[LP] G.G0R hPQ hP hG →ₗ[LP]
    (AllSeq I × AllSeq I) × AllSeq I →₀ LP :=
  charTensor (G.chW2 hPQ hP hG) (G.chW hPQ hP hG)

include hPQ hP hG in
theorem chW2_injective : Function.Injective (G.chW2 hPQ hP hG) :=
  charTensor_injective (G.chW_injective hPQ hP hG) (G.chW_injective hPQ hP hG)

include hPQ hP hG in
theorem chW3_injective : Function.Injective (G.chW3 hPQ hP hG) :=
  charTensor_injective (G.chW2_injective hPQ hP hG) (G.chW_injective hPQ hP hG)

/-- The character of `G₀(R(ν)) ⊗ G₀(R(ν'))` at `(i, j)`. -/
def chT {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν') :
    G0 (G.grade ν) ⊗[LP] G0 (G.grade ν') →ₗ[LP] LP :=
  TensorProduct.lift ((LinearMap.mul LP LP).compl₁₂ (LinearMap.proj i ∘ₗ chMap G (ν := ν))
    (LinearMap.proj j ∘ₗ chMap G (ν := ν')))

@[simp] theorem chT_tmul {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν') (x : G0 (G.grade ν))
    (y : G0 (G.grade ν')) : G.chT i j (x ⊗ₜ y) = chMap G x i * chMap G y j := rfl

theorem chW2_apply (Z : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG) {ν ν' : Multiset I} (i : Seq ν)
    (j : Seq ν') :
    G.chW2 hPQ hP hG Z (⟨ν, i⟩, ⟨ν', j⟩) = G.chT i j (G.G0compTT hPQ hP hG ν ν' Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [chW2, charTensor_tmul, chW_apply, chW_apply, G0compTT, TensorProduct.map_tmul, chT_tmul]
  | add Z Z' hZ hZ' => rw [map_add, Finsupp.add_apply, hZ, hZ', map_add, map_add]

theorem e_tmul_e_mem_tensorGrading' {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν') :
    ((e i : KLRAlgebra k Q ν) ⊗ₜ[k] (e j : KLRAlgebra k Q ν')) ∈
      tensorGrading (G.grade ν) (G.grade ν') 0 := by
  simpa using tmul_mem_tensorGrading (G.e_mem_grade i) (G.e_mem_grade j)

/-- The character of `G₀(R(ν) ⊗ R(ν'))` at `(i, j)`: `[N] ↦ gdim ((1_i ⊗ 1_j) N)`. -/
def chTen {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν') :
    G0 (tensorGrading (G.grade ν) (G.grade ν')) →ₗ[LP] LP :=
  G0.idemCh (tensorGrading (G.grade ν) (G.grade ν'))
    (e := (e i : KLRAlgebra k Q ν) ⊗ₜ[k] (e j : KLRAlgebra k Q ν'))
    (by rw [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul, e_mul_self, e_mul_self])
    (G.e_tmul_e_mem_tensorGrading' i j)

theorem chT_eq_chTen {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν')
    (z : G0 (G.grade ν) ⊗[LP] G0 (G.grade ν')) :
    G.chT i j z = G.chTen i j (G.g0TensorEquiv hPQ hP hG ν ν' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]
  | tmul x y =>
    rw [chT_tmul, g0TensorEquiv_tmul]
    induction x using G0.induction_on with
    | of M =>
      induction y using G0.induction_on with
      | of M' =>
        rw [G0.extTensor_of, chTen, G0.idemCh_of]
        show chG0 G i (G0.of M) * chG0 G j (G0.of M') = _
        rw [chG0_of, chG0_of]
        exact (gdimPoly_idem_extTensor M M' (e_mul_self i) (e_mul_self j) (G.e_mem_grade i)
          (G.e_mem_grade j)).symm
      | zero => simp
      | add y y' hy hy' =>
        simp only [map_add, Pi.add_apply, mul_add, hy, hy']
      | neg y hy => simp only [map_neg, Pi.neg_apply, mul_neg, hy]
    | zero => simp
    | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, add_mul, hx, hx']
    | neg x hx => simp only [map_neg, LinearMap.neg_apply, Pi.neg_apply, neg_mul, hx]

theorem oneConcat_mul_e_append {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν') :
    (oneConcat Q ν ν' * e (i.append j) : KLRAlgebra k Q (ν + ν')) = e (i.append j) := by
  rw [← concat_e_tmul_e (Q := Q) i j, oneConcat_mul_concat]

/-- `(1_i ⊗ 1_j)(1_{ν,ν'} M) = 1_{ij} M`, degree by degree. -/
def resIdemIdemEquiv {ν ν' : Multiset I} (M : GFin (G.grade (ν + ν'))) (i : Seq ν) (j : Seq ν')
    (d : ℤ) :
    idem (G.resFin ν ν' M).grading ((e i : KLRAlgebra k Q ν) ⊗ₜ[k] (e j : KLRAlgebra k Q ν')) d
      ≃ₗ[k] idem M.grading (e (i.append j) : KLRAlgebra k Q (ν + ν')) d where
  toFun z := ⟨⟨z.1.1.1, by
    have h := congrArg Subtype.val z.1.2
    rw [coe_resIdem_smul, concat_e_tmul_e] at h
    exact h⟩, z.2⟩
  invFun w := ⟨⟨⟨w.1.1, by
    show oneConcat Q ν ν' • w.1.1 = w.1.1
    have hw : (e (i.append j) : KLRAlgebra k Q (ν + ν')) • w.1.1 = w.1.1 := w.1.2
    rw [← hw, smul_smul, oneConcat_mul_e_append]⟩, by
    apply Subtype.ext
    rw [coe_resIdem_smul, concat_e_tmul_e]
    exact w.1.2⟩, w.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The character of `1_{ν,ν'} M` at `(i, j)` is the character of `M` at `ij`. -/
theorem chTen_resG0 {ν ν' : Multiset I} (i : Seq ν) (j : Seq ν') (x : G0 (G.grade (ν + ν'))) :
    G.chTen i j (G.resG0 ν ν' x) = chMap G x (i.append j) := by
  induction x using G0.induction_on with
  | of M =>
    rw [resG0_of, chTen, G0.idemCh_of]
    show _ = chG0 G (i.append j) (G0.of M)
    rw [chG0_of]
    exact gdimPoly_eq_of_finrank_eq fun d => (G.resIdemIdemEquiv M i j d).finrank_eq
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Pi.add_apply]
  | neg x hx => rw [map_neg, map_neg, hx, map_neg, Pi.neg_apply]

/-- **The character of `Δ x`**: `ch(Δ x)(a, b) = ch(x)(ab)`. -/
theorem chW2_coprodG0 (x : G.G0R hPQ hP hG) (a b : AllSeq I) :
    G.chW2 hPQ hP hG (G.coprodG0 hPQ hP hG x) (a, b) = G.chW hPQ hP hG x (a.append b) := by
  obtain ⟨ν, i⟩ := a
  obtain ⟨ν', j⟩ := b
  rw [chW2_apply]
  have h := G.coprodG0_spec hPQ hP hG ν ν' x
  rw [← LinearEquiv.eq_symm_apply] at h
  rw [h, chT_eq_chTen, LinearEquiv.apply_symm_apply, G0resComp, LinearMap.comp_apply,
    chTen_resG0]
  show _ = G.chW hPQ hP hG x ⟨ν + ν', i.append j⟩
  rw [chW_apply]

theorem chW_nil (x : G.G0R hPQ hP hG) :
    G.chW hPQ hP hG x AllSeq.nil = G.counitG0 hPQ hP hG x := by
  rw [AllSeq.nil, chW_apply, counitG0, LinearMap.comp_apply]
  generalize G.G0proj hPQ hP hG 0 x = y
  have he1 : (e Seq.nil : KLRAlgebra k Q 0) = 1 := by
    rw [← sum_e (Q := Q) (ν := 0), Fintype.sum_unique]
    rfl
  induction y using G0.induction_on with
  | of M =>
    show chG0 G Seq.nil (G0.of M) = G0.gdimLin (G.grade 0) (G0.of M)
    rw [chG0_of, G0.gdimLin_of]
    refine gdimPoly_eq_of_finrank_eq fun d => LinearEquiv.finrank_eq ?_
    exact
      { toFun := fun z => ⟨z.1.1, z.2⟩
        invFun := fun w => ⟨⟨w.1, by rw [mem_idemSubspace, he1, one_smul]⟩, w.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy]
  | neg x hx => rw [map_neg, map_neg, Pi.neg_apply, hx]

end Characters

/-! ### Coassociativity and counitality -/

section Coalgebra

set_option synthInstance.maxHeartbeats 200000

theorem chW3_rTensor (Z : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG) (a b c : AllSeq I) :
    G.chW3 hPQ hP hG ((G.coprodG0 hPQ hP hG).rTensor (G.G0R hPQ hP hG) Z) ((a, b), c) =
      G.chW2 hPQ hP hG Z (a.append b, c) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, Finsupp.zero_apply]
  | tmul x z =>
    rw [LinearMap.rTensor_tmul, chW3, charTensor_tmul, chW2_coprodG0, chW2, charTensor_tmul]
  | add Z Z' hZ hZ' =>
    rw [LinearMap.map_add, LinearMap.map_add, Finsupp.add_apply, hZ, hZ', LinearMap.map_add,
      Finsupp.add_apply]

theorem chW3_assoc_symm_tmul (x : G.G0R hPQ hP hG) (Y : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG)
    (a b c : AllSeq I) :
    G.chW3 hPQ hP hG ((TensorProduct.assoc LP (G.G0R hPQ hP hG) (G.G0R hPQ hP hG)
        (G.G0R hPQ hP hG)).symm (x ⊗ₜ Y)) ((a, b), c) =
      G.chW hPQ hP hG x a * G.chW2 hPQ hP hG Y (b, c) := by
  induction Y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
      Finsupp.zero_apply, mul_zero]
  | tmul y z =>
    rw [TensorProduct.assoc_symm_tmul, chW3, charTensor_tmul, chW2, charTensor_tmul,
      charTensor_tmul, mul_assoc]
  | add Y Y' hY hY' =>
    rw [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add, Finsupp.add_apply, hY, hY',
      LinearMap.map_add, Finsupp.add_apply, mul_add]

theorem chW3_lTensor (Z : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG) (a b c : AllSeq I) :
    G.chW3 hPQ hP hG ((TensorProduct.assoc LP (G.G0R hPQ hP hG) (G.G0R hPQ hP hG)
        (G.G0R hPQ hP hG)).symm ((G.coprodG0 hPQ hP hG).lTensor (G.G0R hPQ hP hG) Z))
        ((a, b), c) =
      G.chW2 hPQ hP hG Z (a, b.append c) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, Finsupp.zero_apply]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, chW3_assoc_symm_tmul, chW2_coprodG0, chW2, charTensor_tmul]
  | add Z Z' hZ hZ' =>
    rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, Finsupp.add_apply, hZ, hZ',
      LinearMap.map_add, Finsupp.add_apply]

/-- **Coassociativity of `[Res]` on `G₀(R)`** (KL I, Proposition 3.1): `(Δ ⊗ 1) ∘ Δ = (1 ⊗ Δ) ∘ Δ`,
up to the associativity of `⊗`. -/
theorem coprodG0_coassoc (x : G.G0R hPQ hP hG) :
    (G.coprodG0 hPQ hP hG).rTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x) =
      (TensorProduct.assoc LP (G.G0R hPQ hP hG) (G.G0R hPQ hP hG) (G.G0R hPQ hP hG)).symm
        ((G.coprodG0 hPQ hP hG).lTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x)) := by
  apply G.chW3_injective hPQ hP hG
  ext ⟨⟨a, b⟩, c⟩
  rw [chW3_rTensor, chW3_lTensor, chW2_coprodG0, chW2_coprodG0, AllSeq.append_assoc]

theorem chW_lid_rTensor (Z : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG) (b : AllSeq I) :
    G.chW hPQ hP hG (TensorProduct.lid LP (G.G0R hPQ hP hG)
        ((G.counitG0 hPQ hP hG).rTensor (G.G0R hPQ hP hG) Z)) b =
      G.chW2 hPQ hP hG Z (AllSeq.nil, b) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, Finsupp.zero_apply]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.map_smul, Finsupp.smul_apply,
      smul_eq_mul, chW2, charTensor_tmul, chW_nil]
  | add Z Z' hZ hZ' =>
    rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, Finsupp.add_apply, hZ, hZ',
      LinearMap.map_add, Finsupp.add_apply]

theorem chW_rid_lTensor (Z : G.G0R hPQ hP hG ⊗[LP] G.G0R hPQ hP hG) (a : AllSeq I) :
    G.chW hPQ hP hG (TensorProduct.rid LP (G.G0R hPQ hP hG)
        ((G.counitG0 hPQ hP hG).lTensor (G.G0R hPQ hP hG) Z)) a =
      G.chW2 hPQ hP hG Z (a, AllSeq.nil) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, Finsupp.zero_apply]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, LinearMap.map_smul, Finsupp.smul_apply,
      smul_eq_mul, chW2, charTensor_tmul, chW_nil, mul_comm]
  | add Z Z' hZ hZ' =>
    rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, Finsupp.add_apply, hZ, hZ',
      LinearMap.map_add, Finsupp.add_apply]

/-- **Left counitality**: `(ε ⊗ 1) Δ x = 1 ⊗ x`. -/
theorem counitG0_rTensor_coprodG0 (x : G.G0R hPQ hP hG) :
    (G.counitG0 hPQ hP hG).rTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x) = 1 ⊗ₜ x := by
  apply (TensorProduct.lid LP (G.G0R hPQ hP hG)).injective
  apply G.chW_injective hPQ hP hG
  ext b
  rw [chW_lid_rTensor, chW2_coprodG0, AllSeq.nil_append, TensorProduct.lid_tmul, one_smul]

/-- **Right counitality**: `(1 ⊗ ε) Δ x = x ⊗ 1`. -/
theorem counitG0_lTensor_coprodG0 (x : G.G0R hPQ hP hG) :
    (G.counitG0 hPQ hP hG).lTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x) = x ⊗ₜ 1 := by
  apply (TensorProduct.rid LP (G.G0R hPQ hP hG)).injective
  apply G.chW_injective hPQ hP hG
  ext a
  rw [chW_rid_lTensor, chW2_coprodG0, AllSeq.append_nil, TensorProduct.rid_tmul, one_smul]

/-- **`G₀(R)` is a coassociative counital `ℤ[q, q⁻¹]`-coalgebra** with comultiplication `[Res]`
and counit `ε` (KL I, Proposition 3.1). -/
instance instCoalgebraG0R : Coalgebra LP (G.G0R hPQ hP hG) where
  comul := G.coprodG0 hPQ hP hG
  counit := G.counitG0 hPQ hP hG
  coassoc := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [coprodG0_coassoc, LinearEquiv.apply_symm_apply]
  rTensor_counit_comp_comul := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, counitG0_rTensor_coprodG0, TensorProduct.mk_apply]
  lTensor_counit_comp_comul := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, counitG0_lTensor_coprodG0, LinearMap.flip_apply,
      TensorProduct.mk_apply]

theorem comul_G0R : (Coalgebra.comul : G.G0R hPQ hP hG →ₗ[LP] _) = G.coprodG0 hPQ hP hG := rfl

theorem counit_G0R : (Coalgebra.counit : G.G0R hPQ hP hG →ₗ[LP] LP) = G.counitG0 hPQ hP hG := rfl

end Coalgebra

/-! ### Proposition 3.1 for `G₀` -/

/-- **KL I, Proposition 3.1, `G₀` part**: `[Ind]` turns `G₀(R) = ⨁_ν G₀(R(ν))` into an
associative unital `ℤ[q, q⁻¹]`-algebra (unit `[R(∅)]`), and `[Res]` turns `G₀(R)` into a
coassociative counital `ℤ[q, q⁻¹]`-coalgebra (counit: restriction to `R(∅)` followed by the
graded dimension). Explicitly:
1. the product of homogeneous elements is `[Ind]`, `[M] [M'] = [Ind_{ν,ν'} (M ⊠ M')]`;
2. the product is associative, and `1 = [R(∅)]` is a two-sided unit;
3. the components of `Δ` are `[Res_{ν,ν'}] : G₀(R(ν + ν')) → G₀(R(ν)) ⊗ G₀(R(ν'))`;
4. `Δ` is coassociative;
5. `ε` is a two-sided counit. -/
theorem prop_3_1_G0 :
    (∀ {ν ν' : Multiset I} (M : GFin (G.grade ν)) (M' : GFin (G.grade ν')),
      (DirectSum.of (G.G0fam hPQ hP hG) ν (G0.of M) *
          DirectSum.of (G.G0fam hPQ hP hG) ν' (G0.of M') : G.G0R hPQ hP hG) =
        DirectSum.of (G.G0fam hPQ hP hG) (ν + ν') (G0.of (G.indFin hPQ hP M M'))) ∧
    (∀ x y z : G.G0R hPQ hP hG, x * y * z = x * (y * z)) ∧
    (1 : G.G0R hPQ hP hG) = DirectSum.of (G.G0fam hPQ hP hG) 0 (G0.of (G.unitFin hPQ hP)) ∧
    (∀ x : G.G0R hPQ hP hG, 1 * x = x ∧ x * 1 = x) ∧
    (∀ (ν ν' : Multiset I) (M : GFin (G.grade (ν + ν'))),
      G.g0TensorEquiv hPQ hP hG ν ν' (G.G0compTT hPQ hP hG ν ν'
        (G.coprodG0 hPQ hP hG (DirectSum.of (G.G0fam hPQ hP hG) (ν + ν') (G0.of M)))) =
        G0.of (G.resFin ν ν' M)) ∧
    (∀ x : G.G0R hPQ hP hG,
      (G.coprodG0 hPQ hP hG).rTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x) =
        (TensorProduct.assoc LP (G.G0R hPQ hP hG) (G.G0R hPQ hP hG) (G.G0R hPQ hP hG)).symm
          ((G.coprodG0 hPQ hP hG).lTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x))) ∧
    (∀ x : G.G0R hPQ hP hG,
      (G.counitG0 hPQ hP hG).rTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x) = 1 ⊗ₜ x ∧
      (G.counitG0 hPQ hP hG).lTensor (G.G0R hPQ hP hG) (G.coprodG0 hPQ hP hG x) = x ⊗ₜ 1) := by
  refine ⟨fun M M' => G.G0R_of_of_mul_of_of hPQ hP hG M M', mul_assoc, G.G0R_one hPQ hP hG,
    fun x => ⟨one_mul x, mul_one x⟩, fun ν ν' M => ?_, G.coprodG0_coassoc hPQ hP hG,
    fun x => ⟨G.counitG0_rTensor_coprodG0 hPQ hP hG x, G.counitG0_lTensor_coprodG0 hPQ hP hG x⟩⟩
  rw [coprodG0_spec, G0resComp, LinearMap.comp_apply, G0proj_of_self, resG0_of]

end GradingDatum

namespace KL1

variable (k) (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- `G₀(R) = ⨁_ν G₀(R(ν))` for KL I's rings `R(ν)` (graph `Γ`, KL I's grading). -/
abbrev G0RKL : Type _ :=
  (klGradingDatum k Γ).G0R (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)
    klGradingDatum_degX_pos

example : Algebra (LaurentPolynomial ℤ) (G0RKL k Γ) := inferInstance

example : Coalgebra (LaurentPolynomial ℤ) (G0RKL k Γ) := inferInstance

end KL1

end KLR

end Categorification

end
