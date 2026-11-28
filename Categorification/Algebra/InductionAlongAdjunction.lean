/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes

/-!
# The induction–restriction adjunction on linear maps

Let `φ : A →ₙ+* B` be a nonunital ring map. Induction `Ind N φ = B φ(1) ⊗_A N` is left adjoint
to restriction `Res φ P = φ(1) P`. The bundled adjunction of `InductionAlongRes` lives on the
module categories of one universe; here the same adjunction is stated on linear maps, for an
`A`-module `N` and a `B`-module `P` in arbitrary universes:

`Hom_B(Ind N φ, P) ≃ Hom_A(N, Res φ P)`, `f ↦ (n ↦ f(φ(1) ⊗ n))`, `g ↦ (z ⊗ n ↦ z · g(n))`.

It is additive, natural in `N` (`Ind.homEquiv_comp_map`) and natural in `P`
(`Ind.homEquiv_comp`). This is used for the reflected cap bimodule in the trace half of
Webster, arXiv:1309.3796v3, Lemma 7.19, where `K^{λ⁺}_λ` is induced from the coefficients at
the maximum of the cap.

## Main definitions

* `InductionAlong.Ind.homRes`: the adjunct `N → Res φ P` of a map `Ind N φ → P`.
* `InductionAlong.Ind.homLift`: the adjunct `Ind N φ → P` of a map `N → Res φ P`.
* `InductionAlong.Ind.homEquiv`: the adjunction, as an additive isomorphism.

## Main results

* `InductionAlong.Ind.homEquiv_comp_map`, `InductionAlong.Ind.homEquiv_comp`: naturality.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w w'

variable {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B}
  {N : Type w} [AddCommGroup N] [Module A N] {P : Type w'} [AddCommGroup P] [Module B P]

namespace Ind

theorem smul_unitGen (z : Corner φ) : z.1 • unitGen φ = z :=
  Subtype.ext z.2

theorem op_smul_unitGen (a : A) : (op a • unitGen φ : Corner φ) = φ a • unitGen φ :=
  Subtype.ext (by
    change φ 1 * φ a = φ a * φ 1
    rw [← map_mul, ← map_mul, mul_one, one_mul])

/-- The adjunct `n ↦ f(φ(1) ⊗ n)` of a map out of an induced module. -/
def homRes (f : Ind N φ →ₗ[B] P) : N →ₗ[A] Res φ P where
  toFun n := Res.mk (f (tmul (unitGen φ) n)) (by
    rw [← map_smul, smul_tmul]
    congr 2
    exact Subtype.ext (unit_mul_unit φ))
  map_add' n n' := Res.ext (by
    simp only [Res.val_add, Res.val_mk, tmul_add, map_add])
  map_smul' a n := Res.ext (by
    change f (tmul (unitGen φ) (a • n)) = φ a • f (tmul (unitGen φ) n)
    rw [← op_smul_tmul, op_smul_unitGen, ← smul_tmul, map_smul])

@[simp] theorem homRes_apply_val (f : Ind N φ →ₗ[B] P) (n : N) :
    (homRes f n).val = f (tmul (unitGen φ) n) := rfl

/-- The adjunct `z ⊗ n ↦ z · g(n)` of a map into a restricted module. -/
def homLift (g : N →ₗ[A] Res φ P) : Ind N φ →ₗ[B] P :=
  lift (fun z n => z.1 • (g n).val) (fun z z' n => add_smul z.1 z'.1 (g n).val)
    (fun z n n' => by rw [map_add, Res.val_add, smul_add])
    (fun z a n => by
      change (z.1 * φ a) • (g n).val = z.1 • (g (a • n)).val
      rw [map_smul, Res.val_smul, mul_smul])
    (fun b z n => by
      change (b * z.1) • (g n).val = b • z.1 • (g n).val
      rw [mul_smul])

@[simp] theorem homLift_tmul (g : N →ₗ[A] Res φ P) (z : Corner φ) (n : N) :
    homLift g (tmul z n) = z.1 • (g n).val := rfl

theorem homLift_homRes (f : Ind N φ →ₗ[B] P) : homLift (homRes f) = f :=
  ext fun z n => by
    rw [homLift_tmul, homRes_apply_val, ← map_smul, smul_tmul, smul_unitGen]

theorem homRes_homLift (g : N →ₗ[A] Res φ P) : homRes (homLift g) = g :=
  LinearMap.ext fun n => Res.ext (by
    rw [homRes_apply_val, homLift_tmul]
    exact (g n).prop)

/-- **The induction–restriction adjunction on linear maps**:
`Hom_B(Ind N φ, P) ≃ Hom_A(N, Res φ P)`. -/
def homEquiv : (Ind N φ →ₗ[B] P) ≃+ (N →ₗ[A] Res φ P) where
  toFun := homRes
  invFun := homLift
  left_inv := homLift_homRes
  right_inv := homRes_homLift
  map_add' _ _ := LinearMap.ext fun _ => Res.ext rfl

@[simp] theorem homEquiv_apply_val (f : Ind N φ →ₗ[B] P) (n : N) :
    (homEquiv f n).val = f (tmul (unitGen φ) n) := rfl

@[simp] theorem homEquiv_symm_tmul (g : N →ₗ[A] Res φ P) (z : Corner φ) (n : N) :
    homEquiv.symm g (tmul z n) = z.1 • (g n).val := rfl

/-- **Naturality in the induced module.** -/
theorem homEquiv_comp_map {N' : Type w} [AddCommGroup N'] [Module A N'] (h : N' →ₗ[A] N)
    (f : Ind N φ →ₗ[B] P) : homEquiv (f.comp (map h)) = (homEquiv f).comp h :=
  LinearMap.ext fun _ => Res.ext rfl

/-- **Naturality in the target.** -/
theorem homEquiv_comp {P' : Type w'} [AddCommGroup P'] [Module B P'] (u : P →ₗ[B] P')
    (f : Ind N φ →ₗ[B] P) : homEquiv (u.comp f) = (Res.map u).comp (homEquiv f) :=
  LinearMap.ext fun _ => Res.ext rfl

theorem homEquiv_symm_comp_map {N' : Type w} [AddCommGroup N'] [Module A N'] (h : N' →ₗ[A] N)
    (g : N →ₗ[A] Res φ P) : homEquiv.symm (g.comp h) = (homEquiv.symm g).comp (map h) :=
  ext fun _ _ => rfl

theorem homEquiv_symm_comp {P' : Type w'} [AddCommGroup P'] [Module B P'] (u : P →ₗ[B] P')
    (g : N →ₗ[A] Res φ P) : homEquiv.symm ((Res.map u).comp g) = u.comp (homEquiv.symm g) :=
  ext fun z n => (map_smul u z.1 (g n).val).symm

end Ind

end InductionAlong

end

end Categorification
