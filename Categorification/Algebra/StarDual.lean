/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerDualInjective
import Categorification.Algebra.IdempotentEquiv
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Duals of left modules twisted by an anti-automorphism

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §7.1, proof of Proposition 7.8, which uses the duals `(S^κ)^⋆` of standard
modules. Let `A` be an algebra over a field `k` with an anti-automorphism `σ : A ≃+* Aᵐᵒᵖ`, written
`a ↦ ā`. The `k`-dual `M^⋆` of a left `A`-module `M` is again a left module, `(a φ)(m) = φ(ā m)`
(`StarDual`). This is contravariant and exact (`starDualMap`, `starDualMap_injective`,
`starDualMap_surjective`, `exact_starDualMap`).

If `ē = e` for an idempotent `e`, then `(A e)^⋆ ≅ (e A)^*` (`lIdealStarDualEquiv`), so `(A e)^⋆`
is injective (`injective_lIdeal`). A module `X` has no nonzero maps to `M^⋆` when `M` is spanned
by vectors fixed by `σ`-fixed elements that kill `X` (`starDual_hom_eq_zero`).
-/

noncomputable section

universe v

namespace Categorification

open MulOpposite

variable {k A : Type v} [Field k] [Ring A] [Algebra k A] (σ : A ≃+* Aᵐᵒᵖ)

/-- The anti-automorphism applied to `a`, as an element of `A`. -/
abbrev StarDual.bar (a : A) : A := (σ a).unop

section Def

variable (M : Type v) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

set_option linter.unusedVariables false in
variable (k) in
/-- The dual `M^⋆` of a left module, with `(a φ)(m) = φ(ā m)`. -/
@[nolint unusedArguments]
def StarDual (σ : A ≃+* Aᵐᵒᵖ) (M : Type v) [AddCommGroup M] [Module k M] : Type _ :=
  Module.Dual k M

namespace StarDual

instance : AddCommGroup (StarDual k σ M) := inferInstanceAs (AddCommGroup (Module.Dual k M))

instance : Module k (StarDual k σ M) := inferInstanceAs (Module k (Module.Dual k M))

variable {σ M}

/-- The functional underlying an element of `M^⋆`. -/
def toDual (φ : StarDual k σ M) : Module.Dual k M := φ

/-- An element of `M^⋆` from a functional. -/
def ofDual (φ : Module.Dual k M) : StarDual k σ M := φ

variable (σ) in
/-- Left multiplication by `ā` on `M`, a `k`-linear map. -/
def barSmul (a : A) : M →ₗ[k] M where
  toFun m := bar σ a • m
  map_add' := smul_add _
  map_smul' c m := smul_comm _ c m

variable (σ M) in
/-- The left action `(a φ)(m) = φ(ā m)`. -/
def actionHom : A →+* Module.End k (StarDual k σ M) where
  toFun a := LinearMap.lcomp k k (barSmul σ (M := M) a)
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun m =>
    show φ (bar σ 1 • m) = φ m by rw [bar, map_one, unop_one, one_smul]
  map_mul' a b := LinearMap.ext fun φ => LinearMap.ext fun m =>
    show φ (bar σ (a * b) • m) = φ (bar σ b • bar σ a • m) by
      rw [bar, map_mul, unop_mul, mul_smul]
  map_zero' := LinearMap.ext fun φ => LinearMap.ext fun m =>
    show φ (bar σ 0 • m) = 0 by rw [bar, map_zero, unop_zero, zero_smul, map_zero]
  map_add' a b := LinearMap.ext fun φ => LinearMap.ext fun m =>
    show φ (bar σ (a + b) • m) = φ (bar σ a • m) + φ (bar σ b • m) by
      rw [bar, map_add, unop_add, add_smul, map_add]

instance : Module A (StarDual k σ M) := Module.compHom _ (actionHom (k := k) σ M)

theorem smul_apply (a : A) (φ : StarDual k σ M) (m : M) :
    toDual (a • φ) m = toDual φ (bar σ a • m) := rfl

end StarDual

end Def

namespace StarDual

variable {σ}
variable {M N : Type v} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- The dual of a map, `f^⋆ φ = φ ∘ f`. -/
def starDualMap (f : M →ₗ[A] N) : StarDual k σ N →ₗ[A] StarDual k σ M where
  toFun φ := ofDual ((toDual φ).comp (f.restrictScalars k))
  map_add' _ _ := rfl
  map_smul' a φ := LinearMap.ext fun m =>
    show toDual φ (bar σ a • f m) = toDual φ (f (bar σ a • m)) by rw [LinearMap.map_smul f]

theorem starDualMap_apply (f : M →ₗ[A] N) (φ : StarDual k σ N) (m : M) :
    toDual (starDualMap f φ) m = toDual φ (f m) := rfl

theorem starDualMap_injective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Injective (starDualMap (σ := σ) (k := k) f) :=
  LinearMap.dualMap_injective_of_surjective (f := f.restrictScalars k) hf

theorem starDualMap_surjective (f : M →ₗ[A] N) (hf : Function.Injective f) :
    Function.Surjective (starDualMap (σ := σ) (k := k) f) :=
  LinearMap.dualMap_surjective_of_injective (f := f.restrictScalars k) hf

/-- Dualizing an exact pair `M₁ → M₂ → M₃` gives an exact pair `M₃^⋆ → M₂^⋆ → M₁^⋆`. -/
theorem exact_starDualMap {P : Type v} [AddCommGroup P] [Module A P] [Module k P]
    [IsScalarTower k A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P) (h : Function.Exact f g) :
    Function.Exact (starDualMap (σ := σ) (k := k) g) (starDualMap (σ := σ) (k := k) f) := by
  have h' : Function.Exact (f.restrictScalars k) (g.restrictScalars k) := h
  intro φ
  constructor
  · intro hφ
    have hker : toDual φ ∈ (LinearMap.range (f.restrictScalars k)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      rintro _ ⟨m, rfl⟩
      exact LinearMap.congr_fun hφ m
    rw [show LinearMap.range (f.restrictScalars k) = LinearMap.ker (g.restrictScalars k) from
      (LinearMap.exact_iff.mp h').symm, ← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hker
    obtain ⟨ψ, hψ⟩ := hker
    exact ⟨ofDual ψ, hψ⟩
  · rintro ⟨ψ, rfl⟩
    refine LinearMap.ext fun m => ?_
    change toDual ψ (g (f m)) = 0
    rw [h.apply_apply_eq_zero, map_zero]

/-- **Maps into a dual vanish on killed modules.** If every vector of `N` lies in the span of
vectors `y` with `e y = y` for some `e` with `ē = e` and `e X = 0`, then every map
`X → N^⋆` vanishes. -/
theorem hom_eq_zero {X : Type v} [AddCommGroup X] [Module A X]
    (hN : ∀ y : N, y ∈ Submodule.span A
      {y : N | ∃ e : A, e • y = y ∧ bar σ e = e ∧ ∀ x : X, e • x = 0})
    (f : X →ₗ[A] StarDual k σ N) : f = 0 := by
  have key : ∀ y : N, ∀ x : X, toDual (f x) y = 0 := by
    intro y
    refine Submodule.span_induction (p := fun y _ => ∀ x : X, toDual (f x) y = 0) ?_ ?_ ?_ ?_
      (hN y)
    · rintro y ⟨e, hey, he, hx⟩ x
      rw [← hey, ← he]
      change toDual (e • f x) y = 0
      rw [← map_smul, hx, map_zero]
      rfl
    · intro x
      exact map_zero _
    · intro y z _ _ hy hz x
      rw [map_add, hy, hz, add_zero]
    · intro a y _ hy x
      have : a = bar σ (σ.symm (op a)) := by rw [bar, RingEquiv.apply_symm_apply, unop_op]
      rw [this]
      change toDual (σ.symm (op a) • f x) y = 0
      rw [← map_smul]
      exact hy _
  exact LinearMap.ext fun x => LinearMap.ext fun y => key y x

/-! ### Isomorphisms and finite products -/

/-- The dual of an isomorphism. -/
def starDualCongr (f : M ≃ₗ[A] N) : StarDual k σ N ≃ₗ[A] StarDual k σ M where
  __ := starDualMap (σ := σ) (k := k) f.toLinearMap
  invFun := starDualMap (σ := σ) (k := k) f.symm.toLinearMap
  left_inv φ := LinearMap.ext fun n => congrArg (toDual φ) (f.apply_symm_apply n)
  right_inv φ := LinearMap.ext fun m => congrArg (toDual φ) (f.symm_apply_apply m)

/-- The dual of a finite product is the product of the duals. -/
def starDualPiEquiv {ι : Type v} [Fintype ι] [DecidableEq ι] (P : ι → Type v)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k A (P i)] :
    StarDual k σ (∀ i, P i) ≃ₗ[A] ∀ i, StarDual k σ (P i) where
  toFun φ i := ofDual ((toDual φ).comp (LinearMap.single k P i))
  invFun ψ := ofDual (∑ i, (toDual (ψ i)).comp (LinearMap.proj i))
  left_inv φ := LinearMap.ext fun p => by
    change (∑ i, ((toDual φ).comp (LinearMap.single k P i)).comp (LinearMap.proj i)) p =
      toDual φ p
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single]
    rw [← map_sum, Finset.univ_sum_single]
  right_inv ψ := by
    funext i
    refine LinearMap.ext fun x => ?_
    change (∑ j, (toDual (ψ j)).comp (LinearMap.proj j)) (Pi.single i x) = toDual (ψ i) x
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
      (by simp), Pi.single_eq_same]
  map_add' _ _ := rfl
  map_smul' a φ := by
    funext i
    refine LinearMap.ext fun x => ?_
    change toDual φ (bar σ a • Pi.single i x) = toDual φ (Pi.single i (bar σ a • x))
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

/-! ### Duals of projectives `A e` -/

omit [Field k] [Algebra k A] in
/-- A module isomorphic to an injective module is injective. -/
theorem _root_.Module.Injective.of_linearEquiv {R : Type*} [Ring R] {P P' : Type v}
    [AddCommGroup P] [AddCommGroup P'] [Module R P] [Module R P'] [Module.Injective R P]
    (f : P ≃ₗ[R] P') : Module.Injective R P' :=
  ⟨fun _ _ _ _ _ _ i hi g => by
    obtain ⟨h, hh⟩ := Module.Injective.out i hi (f.symm.toLinearMap.comp g)
    exact ⟨f.toLinearMap.comp h, fun x => by simp [hh]⟩⟩

section Corner

variable (hσ : ∀ a, bar σ (bar σ a) = a) {e : A} (he : IsIdempotentElem e)
  (hbe : bar σ e = e)

include hbe in
/-- `ā` lies in `e A` for `a ∈ A e`. -/
theorem bar_mem_leftCorner (x : lIdeal e) : bar σ (x : A) ∈ leftCorner (k := k) e := by
  rw [mem_leftCorner]
  have h : bar σ e * bar σ (x : A) = bar σ ((x : A) * e) := by
    rw [bar, bar, bar, map_mul, unop_mul]
  rw [hbe] at h
  rw [h, x.2]

include hbe in
/-- `ā` lies in `A e` for `a ∈ e A`. -/
theorem bar_mem_lIdeal (y : leftCorner (k := k) e) : bar σ (y : A) ∈ lIdeal e := by
  rw [mem_lIdeal]
  have h : bar σ (y : A) * bar σ e = bar σ (e * (y : A)) := by
    rw [bar, bar, bar, map_mul, unop_mul]
  rw [hbe] at h
  rw [h, y.2]

variable (hc : ∀ c : k, bar σ (algebraMap k A c) = algebraMap k A c)

include hc in
theorem bar_smul (c : k) (a : A) : bar σ (c • a) = c • bar σ a := by
  rw [Algebra.smul_def, bar, map_mul, unop_mul, ← bar, ← bar, hc, ← Algebra.commutes,
    ← Algebra.smul_def]

include hσ hc in
/-- The bar map `A e ≅ e A`, a `k`-linear isomorphism. -/
def barEquiv : lIdeal e ≃ₗ[k] leftCorner (k := k) e where
  toFun x := ⟨bar σ (x : A), bar_mem_leftCorner hbe x⟩
  invFun y := ⟨bar σ (y : A), bar_mem_lIdeal hbe y⟩
  left_inv x := Subtype.ext (hσ _)
  right_inv y := Subtype.ext (hσ _)
  map_add' x y := Subtype.ext (by simp [bar])
  map_smul' c x := Subtype.ext (bar_smul hc c (x : A))

include hσ hc in
/-- **`(A e)^⋆ ≅ (e A)^*`** for an idempotent with `ē = e`. -/
def lIdealStarDualEquiv : StarDual k σ (lIdeal e) ≃ₗ[A] CornerDual k e where
  toFun φ := CornerDual.ofDual ((toDual φ).comp (barEquiv hσ hbe hc).symm.toLinearMap)
  invFun ψ := ofDual ((CornerDual.toDual ψ).comp (barEquiv hσ hbe hc).toLinearMap)
  left_inv φ := LinearMap.ext fun x => congrArg (toDual φ) ((barEquiv hσ hbe hc).symm_apply_apply x)
  right_inv ψ := LinearMap.ext fun y =>
    congrArg (CornerDual.toDual ψ) ((barEquiv hσ hbe hc).apply_symm_apply y)
  map_add' _ _ := rfl
  map_smul' a φ := LinearMap.ext fun y => by
    change toDual φ (bar σ a • (barEquiv hσ hbe hc).symm y) =
      toDual φ ((barEquiv hσ hbe hc).symm ⟨(y : A) * a, CornerDual.mul_mem y a⟩)
    congr 1
    exact Subtype.ext (by
      change bar σ a * bar σ (y : A) = bar σ ((y : A) * a)
      rw [bar, bar, bar, map_mul, unop_mul])

include hσ hbe hc he in
/-- **`(A e)^⋆` is injective** for an idempotent with `ē = e`. -/
theorem injective_lIdeal : Module.Injective A (StarDual k σ (lIdeal e)) := by
  have := CornerDual.injective (k := k) he
  exact Module.Injective.of_linearEquiv (lIdealStarDualEquiv hσ hbe hc).symm

include hσ hc in
/-- **The dual of a finite sum of projectives `A eᵢ` is injective**, for idempotents with
`ēᵢ = eᵢ`. -/
theorem injective_of_equiv_pi {Y : Type v} [AddCommGroup Y] [Module A Y] [Module k Y]
    [IsScalarTower k A Y] {ι : Type v} [Fintype ι] [DecidableEq ι] (e : ι → A)
    (he : ∀ i, IsIdempotentElem (e i)) (hbe : ∀ i, bar σ (e i) = e i)
    (f : Y ≃ₗ[A] ∀ i, lIdeal (e i)) : Module.Injective A (StarDual k σ Y) := by
  have : ∀ i, Module.Injective A (StarDual k σ (lIdeal (e i))) := fun i =>
    injective_lIdeal hσ (he i) (hbe i) hc
  exact Module.Injective.of_linearEquiv
    ((starDualPiEquiv (k := k) (σ := σ) fun i => lIdeal (e i)).symm.trans (starDualCongr f))

end Corner

end StarDual

end Categorification
