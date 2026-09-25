/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree

/-!
# Restriction takes projectives to projectives

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6. For the non-unital inclusion
`ι = concat : R(ν) ⊗ R(ν') → R(ν + ν')` with `ι(1) = 1_{ν,ν'}`, the restriction functor
`Res_{ν,ν'}` takes an `R(ν + ν')`-module `N` to `1_{ν,ν'} N`, viewed as an
`R(ν) ⊗ R(ν')`-module through `ι`.

## Main definitions and results

* `KLRAlgebra.Res N` — the `R(ν) ⊗ R(ν')`-module `1_{ν,ν'} N`; `KLRAlgebra.resMap f` — the
  restriction of an `R(ν + ν')`-linear map.
* `KLRAlgebra.resFinsuppEquiv` — `Res (X →₀ R(ν + ν')) ≃ (X →₀ 1_{ν,ν'} R(ν + ν'))`.
* `KLRAlgebra.res_projective` (**KL I, Corollary 2.17**): if `N` is a projective
  `R(ν + ν')`-module then `Res N` is a projective `R(ν) ⊗ R(ν')`-module. The proof: `N` is a
  direct summand of a free module, restriction preserves direct summands, and the
  restriction of a free module is free by Proposition 2.16 (`KLRAlgebra.free_oneConcat`).

Gradings are not addressed here.
-/

namespace Categorification.KLR

open MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' : Multiset I}

namespace KLRAlgebra

section Res

variable (ν ν') (N : Type*) [AddCommGroup N] [Module (KLRAlgebra k Q (ν + ν')) N]

variable (Q) in
/-- The additive subgroup `1_{ν,ν'} N = {n | 1_{ν,ν'} n = n}`. -/
def resSubgroup : AddSubgroup N where
  carrier := {n | oneConcat Q ν ν' • n = n}
  add_mem' ha hb := by simp only [Set.mem_setOf_eq, smul_add] at *; rw [ha, hb]
  zero_mem' := smul_zero _
  neg_mem' ha := by simp only [Set.mem_setOf_eq, smul_neg] at *; rw [ha]

variable (Q) in
/-- The restriction `Res_{ν,ν'} N = 1_{ν,ν'} N`. -/
abbrev Res : Type _ := resSubgroup Q ν ν' N

variable {ν ν' N}

theorem mem_resSubgroup {n : N} : n ∈ resSubgroup Q ν ν' N ↔ oneConcat Q ν ν' • n = n :=
  Iff.rfl

theorem concat_smul_mem (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (n : N) :
    concat Q ν ν' t • n ∈ resSubgroup Q ν ν' N := by
  rw [mem_resSubgroup, smul_smul, oneConcat_mul_concat]

noncomputable instance : SMul (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (Res Q ν ν' N) :=
  ⟨fun t n => ⟨concat Q ν ν' t • (n : N), concat_smul_mem t (n : N)⟩⟩

theorem coe_res_smul (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (n : Res Q ν ν' N) :
    ((t • n : Res Q ν ν' N) : N) = concat Q ν ν' t • (n : N) := rfl

noncomputable instance : Module (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (Res Q ν ν' N) where
  one_smul n := Subtype.ext (by rw [coe_res_smul, concat_one]; exact n.2)
  mul_smul s t n := Subtype.ext (by simp only [coe_res_smul, concat_mul, mul_smul])
  smul_zero t := Subtype.ext (by simp only [coe_res_smul, ZeroMemClass.coe_zero, smul_zero])
  smul_add t m n := Subtype.ext (by simp only [coe_res_smul, AddMemClass.coe_add, smul_add])
  add_smul s t n := Subtype.ext (by simp only [coe_res_smul, map_add, add_smul,
    AddMemClass.coe_add])
  zero_smul n := Subtype.ext (by simp only [coe_res_smul, map_zero, zero_smul,
    ZeroMemClass.coe_zero])

variable {N' N'' : Type*} [AddCommGroup N'] [Module (KLRAlgebra k Q (ν + ν')) N']
  [AddCommGroup N''] [Module (KLRAlgebra k Q (ν + ν')) N'']

/-- The restriction of an `R(ν + ν')`-linear map. -/
noncomputable def resMap (f : N →ₗ[KLRAlgebra k Q (ν + ν')] N') :
    Res Q ν ν' N →ₗ[KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'] Res Q ν ν' N' where
  toFun n := ⟨f n, by rw [mem_resSubgroup, ← map_smul, n.2]⟩
  map_add' m n := Subtype.ext (by simp)
  map_smul' t n := Subtype.ext (by simp [coe_res_smul])

@[simp] theorem coe_resMap (f : N →ₗ[KLRAlgebra k Q (ν + ν')] N') (n : Res Q ν ν' N) :
    ((resMap f n : Res Q ν ν' N') : N') = f n := rfl

theorem resMap_comp (f : N →ₗ[KLRAlgebra k Q (ν + ν')] N')
    (g : N' →ₗ[KLRAlgebra k Q (ν + ν')] N'') :
    (resMap g).comp (resMap f) = resMap (Q := Q) (ν := ν) (ν' := ν') (g.comp f) := rfl

theorem resMap_id :
    resMap (Q := Q) (ν := ν) (ν' := ν') (LinearMap.id : N →ₗ[KLRAlgebra k Q (ν + ν')] N) =
      LinearMap.id := rfl

end Res

/-! ### Restriction of free modules -/

section Free

variable (X : Type*)

theorem finsupp_apply_mem {f : X →₀ KLRAlgebra k Q (ν + ν')}
    (hf : f ∈ resSubgroup Q ν ν' (X →₀ KLRAlgebra k Q (ν + ν'))) (x : X) :
    f x ∈ oneConcatSub (ν := ν) (ν' := ν') Q := by
  rw [mem_oneConcatSub]
  have := congrArg (fun g : X →₀ KLRAlgebra k Q (ν + ν') => g x) hf
  simpa using this

/-- `Res (X →₀ R(ν + ν')) ≃ (X →₀ 1_{ν,ν'} R(ν + ν'))`. -/
noncomputable def resFinsuppEquiv :
    Res Q ν ν' (X →₀ KLRAlgebra k Q (ν + ν')) ≃ₗ[KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν']
      (X →₀ oneConcatSub (ν := ν) (ν' := ν') Q) where
  toFun f := Finsupp.onFinset f.1.support (fun x => ⟨f.1 x, finsupp_apply_mem X f.2 x⟩)
    (fun x hx => by
      rw [Finsupp.mem_support_iff]
      intro h
      exact hx (Subtype.ext (by simpa using h)))
  invFun g := ⟨g.mapRange Subtype.val rfl, by
    rw [mem_resSubgroup]
    ext x
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact mem_oneConcatSub.1 (g x).2⟩
  left_inv f := Subtype.ext (by ext x; simp)
  right_inv g := by ext x; simp
  map_add' f g := by ext x; simp
  map_smul' t f := by
    ext x
    simp only [Finsupp.onFinset_apply, RingHom.id_apply, Finsupp.smul_apply]
    rw [coe_tensor_smul, coe_res_smul, Finsupp.smul_apply, smul_eq_mul]

end Free

/-! ### Corollary 2.17 -/

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
/-- **KL I, Corollary 2.17**: the restriction functor `Res_{ν,ν'}` takes projective
`R(ν + ν')`-modules to projective `R(ν) ⊗ R(ν')`-modules. -/
theorem res_projective (N : Type*) [AddCommGroup N] [Module (KLRAlgebra k Q (ν + ν')) N]
    [Module.Projective (KLRAlgebra k Q (ν + ν')) N] :
    Module.Projective (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (Res Q ν ν' N) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective (KLRAlgebra k Q (ν + ν')) N›
  haveI := free_oneConcat (ν := ν) (ν' := ν') hPQ hP
  haveI : Module.Projective (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
      (Res Q ν ν' (N →₀ KLRAlgebra k Q (ν + ν'))) :=
    Module.Projective.of_equiv (resFinsuppEquiv N).symm
  refine Module.Projective.of_split (resMap s)
    (resMap (Finsupp.linearCombination (KLRAlgebra k Q (ν + ν')) id)) ?_
  rw [resMap_comp, hs, resMap_id]

end KLRAlgebra

end Categorification.KLR
