/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SelfDualInjective

/-!
# Duals of right corner modules are injective

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §7.1, proof of Proposition 7.8: the duals `(S^κ)^⋆` of standard modules have
coresolutions by duals of projectives, which are injective.

Let `A` be an algebra over a field `k` and `e ∈ A` idempotent. The dual `(e A)^*` of the right
ideal `e A` is a left `A`-module, `(a φ)(x) = φ(x a)` (`CornerDual`). It is injective
(`CornerDual.injective`): by Baer's criterion, a map `g` on a left ideal `J` gives the functional
`e j ↦ g(j)(e)` on `e J ⊆ e A`, which extends to `e A`. A left module killed by `e` has no nonzero
maps to `(e A)^*` (`CornerDual.eq_zero_of_smul_eq_zero`).
-/

noncomputable section

namespace Categorification

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

variable (k) in
/-- The dual `(e A)^*` of the right ideal `e A`, as a type to carry the left `A`-action. -/
def CornerDual (e : A) : Type _ := Module.Dual k (leftCorner (k := k) e)

namespace CornerDual

variable {e : A}

instance : AddCommGroup (CornerDual k e) := inferInstanceAs (AddCommGroup (Module.Dual k _))

instance : Module k (CornerDual k e) := inferInstanceAs (Module k (Module.Dual k _))

/-- The functional underlying an element of `(e A)^*`. -/
def toDual (φ : CornerDual k e) : Module.Dual k (leftCorner (k := k) e) := φ

/-- An element of `(e A)^*` from a functional. -/
def ofDual (φ : Module.Dual k (leftCorner (k := k) e)) : CornerDual k e := φ

theorem mul_mem (x : leftCorner (k := k) e) (a : A) : (x : A) * a ∈ leftCorner (k := k) e := by
  rw [mem_leftCorner, ← mul_assoc, x.2]

/-- Right multiplication by `a` on `e A`. -/
def rightMul (a : A) : leftCorner (k := k) e →ₗ[k] leftCorner (k := k) e where
  toFun x := ⟨(x : A) * a, mul_mem x a⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (Algebra.smul_mul_assoc _ _ _)

/-- The left action `(a φ)(x) = φ(x a)`. -/
def actionHom : A →+* Module.End k (CornerDual k e) where
  toFun a := LinearMap.lcomp k k (rightMul a)
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun x =>
    show φ ⟨(x : A) * 1, _⟩ = φ x from congrArg φ (Subtype.ext (mul_one _))
  map_mul' a b := LinearMap.ext fun φ => LinearMap.ext fun x =>
    show φ ⟨(x : A) * (a * b), _⟩ = φ ⟨(x : A) * a * b, _⟩ from
      congrArg φ (Subtype.ext (mul_assoc _ _ _).symm)
  map_zero' := LinearMap.ext fun φ => LinearMap.ext fun x =>
    show φ ⟨(x : A) * 0, _⟩ = 0 from
      (congrArg φ (Subtype.ext (mul_zero _) : (⟨(x : A) * 0, _⟩ : leftCorner (k := k) e) = 0)).trans
        φ.map_zero
  map_add' a b := LinearMap.ext fun φ => LinearMap.ext fun x =>
    show φ ⟨(x : A) * (a + b), _⟩ = φ ⟨(x : A) * a, _⟩ + φ ⟨(x : A) * b, _⟩ from
      (congrArg φ (Subtype.ext (mul_add _ _ _) :
        (⟨(x : A) * (a + b), _⟩ : leftCorner (k := k) e) = ⟨(x : A) * a, mul_mem x a⟩ +
          ⟨(x : A) * b, mul_mem x b⟩)).trans (φ.map_add _ _)

instance : Module A (CornerDual k e) := Module.compHom _ (actionHom (k := k) (e := e))

theorem smul_apply (a : A) (φ : CornerDual k e) (x : leftCorner (k := k) e) :
    toDual (a • φ) x = toDual φ ⟨(x : A) * a, mul_mem x a⟩ := rfl

variable (he : IsIdempotentElem e)

include he in
/-- **`(e A)^*` satisfies Baer's criterion.** -/
theorem baer : Module.Baer A (CornerDual k e) := by
  intro J g
  let ε : leftCorner (k := k) e := ⟨e, he.eq⟩
  -- `π : J → e A`, `j ↦ e j`, and `μ : J → k`, `j ↦ g(j)(e)`, both `k`-linear.
  let π : J →ₗ[k] leftCorner (k := k) e :=
    { toFun := fun j => ⟨e * j, by rw [mem_leftCorner, ← mul_assoc, he.eq]⟩
      map_add' := fun x y => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c x => Subtype.ext (Algebra.mul_smul_comm c e _) }
  let μ : J →ₗ[k] k :=
    { toFun := fun j => toDual (g j) ε
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by
        rw [show c • x = (algebraMap k A c) • x from (algebraMap_smul A c x).symm, map_smul,
          smul_apply]
        change toDual (g x) _ = c • toDual (g x) ε
        rw [← map_smul]
        congr 1
        exact Subtype.ext (by
          change e * algebraMap k A c = c • e
          rw [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, mul_one]) }
  have hker : LinearMap.ker π ≤ LinearMap.ker μ := by
    intro j hj
    have hj' : e * (j : A) = 0 := congrArg Subtype.val hj
    change toDual (g j) ε = 0
    have h0 : g ⟨e * j, J.smul_mem e j.2⟩ = 0 := by
      rw [show (⟨e * j, J.smul_mem e j.2⟩ : J) = 0 from Subtype.ext hj', map_zero]
    have h1 : g ⟨e * j, J.smul_mem e j.2⟩ = e • g j := by
      rw [← map_smul]; rfl
    have := congrArg (fun ψ => toDual ψ ε) (h1.symm.trans h0)
    simp only [smul_apply] at this
    exact (congrArg (toDual (g j)) (Subtype.ext he.eq.symm)).trans this
  let μ' : LinearMap.range π →ₗ[k] k :=
    ((LinearMap.ker π).liftQ μ hker).comp (π.quotKerEquivRange.symm : _ →ₗ[k] _)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend μ'
  have hφπ : ∀ j, φ (π j) = μ j := by
    intro j
    have := LinearMap.congr_fun hφ ⟨π j, LinearMap.mem_range_self π j⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    have hq : π.quotKerEquivRange.symm ⟨π j, LinearMap.mem_range_self π j⟩ =
        Submodule.Quotient.mk j := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change (LinearMap.ker π).liftQ μ hker (π.quotKerEquivRange.symm ⟨π j, _⟩) = μ j
    rw [hq]
    rfl
  refine ⟨LinearMap.toSpanSingleton A _ (ofDual φ), fun x hx => ?_⟩
  change x • ofDual φ = g ⟨x, hx⟩
  refine LinearMap.ext fun y => ?_
  change φ ⟨(y : A) * x, mul_mem y x⟩ = toDual (g ⟨x, hx⟩) y
  have hyx : (⟨(y : A) * x, J.smul_mem (y : A) hx⟩ : J) = (y : A) • ⟨x, hx⟩ := rfl
  have h1 : π ⟨(y : A) * x, J.smul_mem (y : A) hx⟩ = ⟨(y : A) * x, mul_mem y x⟩ :=
    Subtype.ext (by change e * ((y : A) * x) = _; rw [← mul_assoc, y.2])
  rw [← h1, hφπ]
  change toDual (g ⟨(y : A) * x, _⟩) ε = _
  rw [hyx, map_smul, smul_apply]
  congr 1
  exact Subtype.ext y.2

include he in
/-- **`(e A)^*` is an injective left module.** -/
theorem injective : Module.Injective A (CornerDual k e) := (baer he).injective

include he in
/-- A left module killed by `e` has no nonzero maps to `(e A)^*`. -/
theorem eq_zero_of_smul_eq_zero {X : Type*} [AddCommGroup X] [Module A X]
    (hX : ∀ x : X, e • x = 0) (f : X →ₗ[A] CornerDual k e) : f = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change toDual (f x) y = 0
  have h : toDual (f x) y = toDual ((y : A) • f x) ⟨e, he.eq⟩ := by
    rw [smul_apply]
    congr 1
    exact Subtype.ext y.2.symm
  rw [h, ← map_smul]
  have : (y : A) • x = e • ((y : A) • x) := by rw [smul_smul, y.2]
  rw [this, hX, map_zero]
  rfl

end CornerDual

end Categorification
