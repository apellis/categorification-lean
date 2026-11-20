/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Group.Idempotent

/-!
# Quotients by kernels of idempotents

Linear algebra used to pass a short exact sequence through a quotient `M / ker q` by the
kernel of an idempotent operator `q`. This is how the Mackey filtration of an induced KLR
module descends to Webster's standard modules (B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5): a standard module is
the quotient of an induced module by the kernel of the idempotent `eSum` of the red-ordered
loadings.

Let `q` be an idempotent operator on `M`.

* `IdempotentQuotient.descend`: a map `φ : X → M` with `φ ∘ p = q ∘ φ` descends to
  `X / ker p → M / ker q`; it is injective when `φ` is (`descend_injective`).
* `IdempotentQuotient.quotientSupEquiv`: for a `q`-stable `Y`, the quotient `M / Y` by the kernel
  of the induced idempotent `q̄` is `M / (ker q ⊔ Y)`.
* `IdempotentQuotient.descendEquiv`: an injective `ψ : Z → M / Y` with `ψ ∘ r = q̄ ∘ ψ` whose
  range contains that of `q̄` induces `Z / ker r ≃ (M / Y) / ker q̄`.
* `IdempotentQuotient.rangeEquiv`: for commuting idempotents `p`, `e`, the fixed vectors of
  `ē` in `M / ker p` are `M / ker (p e)`.
-/

namespace Categorification

namespace IdempotentQuotient

open Submodule LinearMap

variable {R : Type*} [CommRing R] {M X Z : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup X] [Module R X] [AddCommGroup Z] [Module R Z]

section Descend

variable (p : X →ₗ[R] X) (q : M →ₗ[R] M) (φ : X →ₗ[R] M) (hφ : ∀ x, φ (p x) = q (φ x))

/-- `φ : X → M` with `φ ∘ p = q ∘ φ`, as a map `X / ker p → M / ker q`. -/
def descend : (X ⧸ ker p) →ₗ[R] (M ⧸ ker q) :=
  (ker p).mapQ (ker q) φ (fun x hx => by
    rw [mem_comap, mem_ker, ← hφ, mem_ker.mp hx, map_zero])

theorem descend_mk (x : X) : descend p q φ hφ (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk (φ x) := rfl

theorem descend_injective (hinj : Function.Injective φ) :
    Function.Injective (descend p q φ hφ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [mem_ker, descend_mk, Submodule.Quotient.mk_eq_zero, mem_ker, ← hφ] at hz
  rw [Submodule.Quotient.mk_eq_zero, mem_ker]
  exact hinj (by rw [hz, map_zero])

/-- The range of `descend` is the image of the range of `φ`. -/
theorem range_descend :
    LinearMap.range (descend p q φ hφ) = (LinearMap.range φ).map (ker q).mkQ := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨φ x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨m, ⟨x, rfl⟩, rfl⟩
    exact ⟨Submodule.Quotient.mk x, rfl⟩

end Descend

section Sup

variable (q : M →ₗ[R] M) (hq : IsIdempotentElem q) (Y : Submodule R M)
  (hY : ∀ y ∈ Y, q y ∈ Y)

/-- The idempotent induced on `M / Y` by a `q`-stable `Y`. -/
def quotientOp : (M ⧸ Y) →ₗ[R] (M ⧸ Y) := Y.mapQ Y q (fun y hy => hY y hy)

theorem quotientOp_mk (m : M) :
    quotientOp q Y hY (Submodule.Quotient.mk m) = Submodule.Quotient.mk (q m) := rfl

include hq in
theorem isIdempotentElem_quotientOp : IsIdempotentElem (quotientOp q Y hY) := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Module.End.mul_apply, quotientOp_mk, quotientOp_mk, ← Module.End.mul_apply, hq.eq]

include hq in
/-- The kernel of `q̄` is the image of `ker q ⊔ Y`. -/
theorem ker_quotientOp :
    ker (quotientOp q Y hY) = (ker q ⊔ Y).map Y.mkQ := by
  ext z
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [mem_ker, quotientOp_mk, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    refine ⟨m, ?_, rfl⟩
    rw [← sub_add_cancel m (q m)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right h)
    rw [mem_ker, map_sub, ← Module.End.mul_apply, hq.eq, sub_self]
  · rintro ⟨m', hm', he⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm'
    have hd : m - (a + b) ∈ Y := by
      rw [← Submodule.Quotient.eq]
      exact he.symm
    have hq' : q m = q (m - (a + b)) + q b := by
      rw [map_sub, map_add, mem_ker.mp ha, zero_add, sub_add_cancel]
    rw [hq']
    exact Y.add_mem (hY _ hd) (hY _ hb)

/-- `(M / Y) / ker q̄ ≃ M / (ker q ⊔ Y)`. -/
noncomputable def quotientSupEquiv :
    ((M ⧸ Y) ⧸ ker (quotientOp q Y hY)) ≃ₗ[R] (M ⧸ (ker q ⊔ Y)) :=
  (Submodule.quotEquivOfEq _ _ (ker_quotientOp q hq Y hY)).trans
    (Submodule.quotientQuotientEquivQuotient Y (ker q ⊔ Y) le_sup_right)

theorem quotientSupEquiv_mk (m : M) :
    quotientSupEquiv q hq Y hY (Submodule.Quotient.mk (Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk m := rfl

/-- `(M / ker q) / Ȳ ≃ M / (ker q ⊔ Y)`, for `Ȳ` the image of `Y`. -/
noncomputable def quotientMapEquiv :
    ((M ⧸ ker q) ⧸ Y.map (ker q).mkQ) ≃ₗ[R] (M ⧸ (ker q ⊔ Y)) :=
  Submodule.quotientQuotientEquivQuotientSup (ker q) Y

theorem quotientMapEquiv_mk (m : M) :
    quotientMapEquiv q Y (Submodule.Quotient.mk (Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk m := rfl

end Sup

section Surjective

variable (r : Z →ₗ[R] Z) (q : M →ₗ[R] M) (hq : IsIdempotentElem q) (Y : Submodule R M)
  (hY : ∀ y ∈ Y, q y ∈ Y) (ψ : Z →ₗ[R] (M ⧸ Y))
  (hψ : ∀ z, ψ (r z) = quotientOp q Y hY (ψ z))

/-- An injective `ψ : Z → M / Y` with `ψ ∘ r = q̄ ∘ ψ` whose range contains the range of `q̄`
induces `Z / ker r ≃ (M / Y) / ker q̄`. -/
noncomputable def descendEquiv (hinj : Function.Injective ψ)
    (hrange : ∀ m : M, ∃ z, ψ z = quotientOp q Y hY (Submodule.Quotient.mk m)) :
    (Z ⧸ ker r) ≃ₗ[R] ((M ⧸ Y) ⧸ ker (quotientOp q Y hY)) :=
  LinearEquiv.ofBijective (descend r (quotientOp q Y hY) ψ hψ)
    ⟨descend_injective r _ ψ hψ hinj, by
      intro w
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      obtain ⟨z, hz⟩ := hrange m
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      rw [descend_mk, Submodule.Quotient.eq, hz, mem_ker, map_sub, ← Module.End.mul_apply,
        (isIdempotentElem_quotientOp q hq Y hY).eq, sub_self]⟩

theorem descendEquiv_mk (hinj : Function.Injective ψ)
    (hrange : ∀ m : M, ∃ z, ψ z = quotientOp q Y hY (Submodule.Quotient.mk m)) (z : Z) :
    descendEquiv r q hq Y hY ψ hψ hinj hrange (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (ψ z) := rfl

end Surjective

section Range

variable (p e : M →ₗ[R] M) (he : IsIdempotentElem e) (hc : Commute p e)
include hc

/-- The operator induced by `e` on `M / ker p`. -/
def inducedOp : (M ⧸ ker p) →ₗ[R] (M ⧸ ker p) :=
  (ker p).mapQ (ker p) e (fun m hm => by
    rw [mem_comap, mem_ker, ← Module.End.mul_apply, hc.eq, Module.End.mul_apply,
      mem_ker.mp hm, map_zero])

theorem inducedOp_mk (m : M) :
    inducedOp p e hc (Submodule.Quotient.mk m) = Submodule.Quotient.mk (e m) := rfl

/-- The fixed vectors of `ē` in `M / ker p`. -/
def fixedSubmodule : Submodule R (M ⧸ ker p) := ker (inducedOp p e hc - LinearMap.id)

theorem mem_fixedSubmodule {v : M ⧸ ker p} :
    v ∈ fixedSubmodule p e hc ↔ inducedOp p e hc v = v := by
  rw [fixedSubmodule, mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

/-- `m ↦ [e m]`, `M / ker (p e) → (M / ker p)^ē`. -/
def rangeMap : (M ⧸ ker (p * e)) →ₗ[R] fixedSubmodule p e hc :=
  (ker (p * e)).liftQ
    (LinearMap.codRestrict (fixedSubmodule p e hc) ((ker p).mkQ ∘ₗ e) (fun m => by
      rw [mem_fixedSubmodule]
      change inducedOp p e hc (Submodule.Quotient.mk (e m)) = _
      rw [inducedOp_mk, ← Module.End.mul_apply, he.eq]; rfl))
    (fun m hm => by
      apply Subtype.ext
      change Submodule.Quotient.mk (e m) = (0 : M ⧸ ker p)
      rw [Submodule.Quotient.mk_eq_zero, mem_ker]
      exact mem_ker.mp hm)

theorem coe_rangeMap_mk (m : M) :
    (rangeMap p e he hc (Submodule.Quotient.mk m) : M ⧸ ker p) = Submodule.Quotient.mk (e m) :=
  rfl

/-- The fixed vectors of `ē` in `M / ker p` are `M / ker (p e)`, through `m ↦ [e m]`. -/
noncomputable def rangeEquiv : (M ⧸ ker (p * e)) ≃ₗ[R] fixedSubmodule p e hc :=
  LinearEquiv.ofBijective (rangeMap p e he hc) ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have h := congrArg Subtype.val (mem_ker.mp hz)
      rw [coe_rangeMap_mk, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero, mem_ker] at h
      rw [Submodule.Quotient.mk_eq_zero, mem_ker]
      exact h, by
      rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ v
      refine ⟨Submodule.Quotient.mk m, Subtype.ext ?_⟩
      rw [coe_rangeMap_mk]
      exact (mem_fixedSubmodule p e hc).mp hv⟩

theorem coe_rangeEquiv_mk (m : M) :
    (rangeEquiv p e he hc (Submodule.Quotient.mk m) : M ⧸ ker p) =
      Submodule.Quotient.mk (e m) := rfl

end Range

end IdempotentQuotient

end Categorification
