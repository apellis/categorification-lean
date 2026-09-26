/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Restriction
import Categorification.KLR.ExtTensorK0

/-!
# Graded restriction and `[Res]` on `K₀`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6 and §3.1 (TeX lines 1882–1935). For the non-unital
inclusion `ι_{ν,ν'} = concat : R(ν) ⊗ R(ν') → R(ν + ν')`, `ι(1) = 1_{ν,ν'}`, the restriction of
a graded `R(ν + ν')`-module `N` is the graded `R(ν) ⊗ R(ν')`-module

`Res_{ν,ν'} N = 1_{ν,ν'} N`,

graded by `(1_{ν,ν'} N)_d = 1_{ν,ν'} N ∩ N_d` (`1_{ν,ν'}` has degree `0`) and with
`R(ν) ⊗ R(ν')` graded by the tensor product grading. By Proposition 2.16
(`KLRAlgebra.free_oneConcat`) restriction takes finitely generated graded projective modules to
finitely generated graded projective modules (Corollary 2.17, `KLRAlgebra.res_projective`), so it
induces `[Res] : K₀(R(ν + ν')) → K₀(R(ν) ⊗ R(ν'))`.

## Main definitions and results

* `KLRAlgebra.ResIdem Q ν ν' N` : the `k`-subspace `1_{ν,ν'} N`, an `R(ν) ⊗ R(ν')`-module
  (it is `R(ν) ⊗ R(ν')`-linearly isomorphic to `KLRAlgebra.Res Q ν ν' N`, `resIdemEquivRes`).
* `KLRAlgebra.res_finite` : `Res N` is finitely generated if `N` is (from Proposition 2.16).
* `GradingDatum.resGProj hPQ hP X` : **`Res_{ν,ν'} X` as an object of
  `(R(ν) ⊗ R(ν'))-pmod`** for `X ∈ R(ν + ν')-pmod` (graded Corollary 2.17), with its
  compatibility with isomorphisms, direct sums and shifts.
* `GradingDatum.resK0 hPQ hP` : **the `ℤ[q, q⁻¹]`-linear map
  `[Res] : K₀(R(ν + ν')) → K₀(R(ν) ⊗ R(ν'))`**, `[X] ↦ [1_{ν,ν'} X]`.

Here `K₀(R(ν) ⊗ R(ν'))` is `Graded.K0 (tensorGrading (G.grade ν) (G.grade ν'))`; the paper
identifies it with `K₀(R(ν)) ⊗ K₀(R(ν'))`, and the classes `[Y ⊗ Y']` are
`Graded.K0.extTensor` (`Categorification.KLR.ExtTensorK0`). The identification
`K₀(R(ν) ⊗ R(ν')) ≅ K₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} K₀(R(ν'))` is not formalized.
-/

noncomputable section

namespace Categorification.KLR

open Graded MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' : Multiset I}

namespace KLRAlgebra

/-! ### The restriction `1_{ν,ν'} N` as a `k`-subspace -/

section ResIdem

variable (Q ν ν') in
/-- The restriction `Res_{ν,ν'} N = 1_{ν,ν'} N`, as the `k`-subspace `{n | 1_{ν,ν'} n = n}`. -/
abbrev ResIdem (N : Type*) [AddCommGroup N] [Module k N] [Module (KLRAlgebra k Q (ν + ν')) N]
    [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N] : Type _ :=
  idemSubspace k N (oneConcat Q ν ν')

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (KLRAlgebra k Q (ν + ν')) N]
  [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N]

theorem concat_smul_mem_resIdem (t : TensorKLR Q ν ν') (n : N) :
    concat Q ν ν' t • n ∈ idemSubspace k N (oneConcat Q ν ν') := by
  rw [mem_idemSubspace, smul_smul, oneConcat_mul_concat]

instance : SMul (TensorKLR Q ν ν') (ResIdem Q ν ν' N) :=
  ⟨fun t n => ⟨concat Q ν ν' t • n.1, concat_smul_mem_resIdem t n.1⟩⟩

theorem coe_resIdem_smul (t : TensorKLR Q ν ν') (n : ResIdem Q ν ν' N) :
    ((t • n : ResIdem Q ν ν' N) : N) = concat Q ν ν' t • (n : N) := rfl

instance : Module (TensorKLR Q ν ν') (ResIdem Q ν ν' N) where
  one_smul n := Subtype.ext (by rw [coe_resIdem_smul, concat_one]; exact n.2)
  mul_smul s t n := Subtype.ext (by simp only [coe_resIdem_smul, concat_mul, mul_smul])
  smul_zero t := Subtype.ext (by simp only [coe_resIdem_smul, ZeroMemClass.coe_zero, smul_zero])
  smul_add t m n := Subtype.ext (by simp only [coe_resIdem_smul, Submodule.coe_add, smul_add])
  add_smul s t n := Subtype.ext (by simp only [coe_resIdem_smul, map_add, add_smul,
    Submodule.coe_add])
  zero_smul n := Subtype.ext (by simp only [coe_resIdem_smul, map_zero, zero_smul,
    ZeroMemClass.coe_zero])

instance : IsScalarTower k (TensorKLR Q ν ν') (ResIdem Q ν ν' N) where
  smul_assoc c t n := Subtype.ext (by
    rw [coe_resIdem_smul, Submodule.coe_smul, coe_resIdem_smul, map_smul, smul_assoc])

variable (N) in
/-- `1_{ν,ν'} N` as a `k`-subspace and as an additive subgroup (`KLRAlgebra.Res`) are the same
`R(ν) ⊗ R(ν')`-module. -/
def resIdemEquivRes : ResIdem Q ν ν' N ≃ₗ[TensorKLR Q ν ν'] Res Q ν ν' N where
  toFun n := ⟨n, n.2⟩
  invFun n := ⟨n, n.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (KLRAlgebra k Q (ν + ν')) N']
  [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N']

/-- The restriction `1_{ν,ν'} f` of an `R(ν + ν')`-linear map. -/
def resIdemMap (f : N →ₗ[KLRAlgebra k Q (ν + ν')] N') :
    ResIdem Q ν ν' N →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' N' where
  toFun n := ⟨f n, by rw [mem_idemSubspace, ← map_smul]; exact congrArg f n.2⟩
  map_add' m n := Subtype.ext (map_add f _ _)
  map_smul' t n := Subtype.ext (map_smul f (concat Q ν ν' t) (n : N))

@[simp] theorem coe_resIdemMap (f : N →ₗ[KLRAlgebra k Q (ν + ν')] N') (n : ResIdem Q ν ν' N) :
    ((resIdemMap f n : ResIdem Q ν ν' N') : N') = f n := rfl

/-- The restriction of an isomorphism. -/
def resIdemCongr (f : N ≃ₗ[KLRAlgebra k Q (ν + ν')] N') :
    ResIdem Q ν ν' N ≃ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' N' :=
  LinearEquiv.ofLinear (resIdemMap f.toLinearMap) (resIdemMap f.symm.toLinearMap)
    (LinearMap.ext fun n => Subtype.ext (f.apply_symm_apply (n : N')))
    (LinearMap.ext fun n => Subtype.ext (f.symm_apply_apply (n : N)))

variable (N N') in
/-- `1_{ν,ν'} (N × N') ≅ 1_{ν,ν'} N × 1_{ν,ν'} N'`. -/
def resIdemProd :
    ResIdem Q ν ν' (N × N') ≃ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' N × ResIdem Q ν ν' N' where
  toFun n := (⟨(n : N × N').1, congrArg Prod.fst n.2⟩, ⟨(n : N × N').2, congrArg Prod.snd n.2⟩)
  invFun n := ⟨((n.1 : N), (n.2 : N')), Prod.ext n.1.2 n.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end ResIdem

/-! ### Finite generation -/

section Finite

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
/-- `1_{ν,ν'} R(ν + ν')` is a finitely generated `R(ν) ⊗ R(ν')`-module (Proposition 2.16). -/
theorem finite_oneConcatSub :
    Module.Finite (TensorKLR Q ν ν') (oneConcatSub (ν := ν) (ν' := ν') Q) :=
  Module.Finite.of_basis (freeBasis hPQ hP (canWord _) (canWord _) (fun u => canWord _ u.1)
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩)
    (fun u => ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩))

include hPQ hP in
/-- **The restriction of a finitely generated `R(ν + ν')`-module is a finitely generated
`R(ν) ⊗ R(ν')`-module.** -/
theorem res_finite (N : Type*) [AddCommGroup N] [Module (KLRAlgebra k Q (ν + ν')) N]
    [Module.Finite (KLRAlgebra k Q (ν + ν')) N] :
    Module.Finite (TensorKLR Q ν ν') (Res Q ν ν' N) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := KLRAlgebra k Q (ν + ν')) (M := N)
  let f := Finsupp.linearCombination (KLRAlgebra k Q (ν + ν')) s
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs]
  haveI := finite_oneConcatSub (ν := ν) (ν' := ν') hPQ hP
  haveI : Module.Finite (TensorKLR Q ν ν') (Res Q ν ν' (Fin n →₀ KLRAlgebra k Q (ν + ν'))) :=
    Module.Finite.equiv (resFinsuppEquiv (Fin n)).symm
  refine Module.Finite.of_surjective (resMap f) fun y => ?_
  obtain ⟨x, hx⟩ := hf (y : N)
  refine ⟨⟨oneConcat Q ν ν' • x, ?_⟩, Subtype.ext ?_⟩
  · rw [mem_resSubgroup, smul_smul, oneConcat_idem.eq]
  · rw [coe_resMap, map_smul, hx]
    exact y.2

end Finite

end KLRAlgebra

/-! ### Graded restriction -/

namespace GradingDatum

open KLRAlgebra

variable (G : GradingDatum Q)

section Grading

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (KLRAlgebra k Q (ν + ν')) N]
  [IsScalarTower k (KLRAlgebra k Q (ν + ν')) N] (𝒩 : ℤ → Submodule k N)

/-- `1_{ν,ν'} N` is a graded `R(ν) ⊗ R(ν')`-module, for the grading `(1_{ν,ν'} N)_d =
1_{ν,ν'} N ∩ N_d` and the tensor product grading of `R(ν) ⊗ R(ν')`. -/
theorem resIdem_gradedSMul [SetLike.GradedSMul (G.grade (ν + ν')) 𝒩] :
    SetLike.GradedSMul (tensorGrading (G.grade ν) (G.grade ν'))
      (idem 𝒩 (oneConcat Q ν ν') : ℤ → Submodule k (ResIdem Q ν ν' N)) where
  smul_mem i j t n ht hn := by
    rw [mem_idem, coe_resIdem_smul]
    exact SetLike.GradedSMul.smul_mem (A := G.grade (ν + ν')) (G.concat_mem_grade ht) hn

end Grading

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (ν ν') in
/-- **Graded restriction `Res_{ν,ν'} X = 1_{ν,ν'} X`** of a finitely generated graded
projective `R(ν + ν')`-module, as a finitely generated graded projective
`R(ν) ⊗ R(ν')`-module (KL I, Corollary 2.17, graded). -/
def resGProj (X : GProj (G.grade (ν + ν'))) : GProj (tensorGrading (G.grade ν) (G.grade ν')) :=
  haveI := res_finite (ν := ν) (ν' := ν') hPQ hP X.carrier
  haveI := res_projective (ν := ν) (ν' := ν') hPQ hP X.carrier
  { carrier := ResIdem Q ν ν' X.carrier
    grading := idem X.grading (oneConcat Q ν ν')
    decomposition := idemDecomposition X.grading G.oneConcat_mem_grade
    gradedSMul := G.resIdem_gradedSMul X.grading
    finite := Module.Finite.equiv (resIdemEquivRes X.carrier).symm
    projective := Module.Projective.of_equiv (resIdemEquivRes X.carrier).symm }

theorem resGProj_carrier (X : GProj (G.grade (ν + ν'))) :
    (G.resGProj ν ν' hPQ hP X).carrier = ResIdem Q ν ν' X.carrier := rfl

theorem resGProj_grading (X : GProj (G.grade (ν + ν'))) :
    (G.resGProj ν ν' hPQ hP X).grading = idem X.grading (oneConcat Q ν ν') := rfl

@[simp] theorem mem_resGProj_grading {X : GProj (G.grade (ν + ν'))} {d : ℤ}
    {n : ResIdem Q ν ν' X.carrier} :
    n ∈ (G.resGProj ν ν' hPQ hP X).grading d ↔ (n : X.carrier) ∈ X.grading d := Iff.rfl

/-- `Res X ≅ Res X'` for `X ≅ X'`. -/
def resGProjCongr {X X' : GProj (G.grade (ν + ν'))} (e : X.Iso X') :
    (G.resGProj ν ν' hPQ hP X).Iso (G.resGProj ν ν' hPQ hP X') where
  toLinearEquiv := resIdemCongr e.toLinearEquiv
  map_mem' _ _ hx := e.map_mem hx
  symm_map_mem' _ _ hx := e.symm_map_mem' hx

/-- `Res (X ⊕ X') ≅ Res X ⊕ Res X'`. -/
def resGProjProd (X X' : GProj (G.grade (ν + ν'))) :
    (G.resGProj ν ν' hPQ hP (X.prod X')).Iso
      ((G.resGProj ν ν' hPQ hP X).prod (G.resGProj ν ν' hPQ hP X')) where
  toLinearEquiv := resIdemProd X.carrier X'.carrier
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

/-- `Res (X{a}) ≅ (Res X){a}`. -/
def resGProjShift (X : GProj (G.grade (ν + ν'))) (a : ℤ) :
    (G.resGProj ν ν' hPQ hP (X.shift a)).Iso ((G.resGProj ν ν' hPQ hP X).shift a) where
  toLinearEquiv := LinearEquiv.refl _ _
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

variable (ν ν') in
/-- The additive map `[Res] : K₀(R(ν + ν')) → K₀(R(ν) ⊗ R(ν'))`, `[X] ↦ [1_{ν,ν'} X]`. -/
def resK0Add : K0 (G.grade (ν + ν')) →+ K0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  K0.lift (fun X => K0.of (G.resGProj ν ν' hPQ hP X))
    (fun _ _ e => K0.of_eq_of_iso (G.resGProjCongr hPQ hP e))
    (fun X X' => by
      beta_reduce; rw [K0.of_eq_of_iso (G.resGProjProd hPQ hP X X'), K0.of_prod])

@[simp] theorem resK0Add_of (X : GProj (G.grade (ν + ν'))) :
    G.resK0Add ν ν' hPQ hP (K0.of X) = K0.of (G.resGProj ν ν' hPQ hP X) :=
  K0.lift_of _ _ _ X

theorem resK0Add_shift (a : ℤ) (x : K0 (G.grade (ν + ν'))) :
    G.resK0Add ν ν' hPQ hP (K0.shiftHom a x) = K0.shiftHom a (G.resK0Add ν ν' hPQ hP x) := by
  induction x using K0.induction_on with
  | of X =>
    rw [K0.shiftHom_of, resK0Add_of, resK0Add_of, K0.shiftHom_of]
    exact K0.of_eq_of_iso (G.resGProjShift hPQ hP X a)
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

variable (ν ν') in
/-- **`[Res] : K₀(R(ν + ν')) → K₀(R(ν) ⊗ R(ν'))`** (KL I, §3.1), `ℤ[q, q⁻¹]`-linear. -/
def resK0 : K0 (G.grade (ν + ν')) →ₗ[LaurentPolynomial ℤ]
    K0 (tensorGrading (G.grade ν) (G.grade ν')) where
  toFun := G.resK0Add ν ν' hPQ hP
  map_add' := map_add _
  map_smul' p x := K0.map_smul_of_shift (G.resK0Add ν ν' hPQ hP)
    (fun a x => G.resK0Add_shift hPQ hP a x) p x

/-- `[Res] [X] = [1_{ν,ν'} X]`. -/
theorem resK0_of (X : GProj (G.grade (ν + ν'))) :
    G.resK0 ν ν' hPQ hP (K0.of X) = K0.of (G.resGProj ν ν' hPQ hP X) :=
  G.resK0Add_of hPQ hP X

end GradingDatum

end Categorification.KLR

end
