/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongCornerSelf
import Categorification.Algebra.InductionAlongDerived
import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield

/-!
# Restriction to a corner is a Serre quotient

Let `φ : A →ₙ+* B` be an injective nonunital ring map whose image is the corner
`φ(1) B φ(1)`. Then the unit `N → φ(1) (B φ(1) ⊗_A N)` of induction ⊣ restriction is an
isomorphism, so induction is fully faithful, and restriction `M ↦ φ(1) M` (an exact functor)
is the localization of `B`-modules at the Serre class of modules killed by `φ(1)`
(`InductionAlong.resFunctor_isLocalization`).

This is the standard fact underlying the quotient functors `π_ξ` of a standardly stratified
category (Losev–Webster, arXiv:1303.1336v3, Definition 2.1): for an idempotent `e` of a ring `B`,
`M ↦ eM` identifies `B`-modules modulo the modules with `eM = 0` with `eBe`-modules.

The general form (`Abelian.isLocalization_isoModSerre_kernel_of_fullyFaithful_leftAdjoint`): an
exact functor between abelian categories with a fully faithful left adjoint is a localization at
the Serre class of its kernel.
-/

namespace CategoryTheory.Abelian

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (F : C ⥤ D)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor between abelian categories with a fully faithful left adjoint is the
localization at the Serre class of its kernel (the dual of Mathlib's
`isLocalization_isoModSerre_kernel_of_leftAdjoint`). -/
theorem isLocalization_isoModSerre_kernel_of_fullyFaithful_leftAdjoint {G : D ⥤ C}
    (adj : G ⊣ F) [G.Full] [G.Faithful] : F.IsLocalization F.kernel.isoModSerre := by
  rw [isoModSerre_kernel_eq_inverseImage_isomorphisms F]
  exact adj.isLocalization'

end CategoryTheory.Abelian

namespace Categorification

open CategoryTheory MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B) (hφ : Function.Injective φ)
  (hs : ∀ z : B, ∃ a, φ a = φ 1 * z * φ 1)

section

variable (N : Type w) [AddCommGroup N] [Module A N]

/-- The additive map `B φ(1) ⊗_A N → N`, `z ⊗ n ↦ φ⁻¹(φ(1) z) n`. -/
def cornerContract : Ind N φ →+ N :=
  Ind.liftAdd (fun z n => cornerPre φ hs z.1 • n)
    (fun z z' n => by
      rw [← add_smul]
      congr 1
      refine cornerPre_eq φ hφ hs ?_
      change φ (cornerPre φ hs z.1 + cornerPre φ hs z'.1) = φ 1 * (z.1 + z'.1) * φ 1
      rw [map_add, map_cornerPre, map_cornerPre, mul_add, add_mul])
    (fun z n n' => smul_add _ n n')
    (fun z a n => by
      rw [← mul_smul]
      congr 1
      refine cornerPre_eq φ hφ hs ?_
      have h1 : φ 1 * φ a = φ a := by rw [← map_mul, one_mul]
      have h2 : φ a * φ 1 = φ a := by rw [← map_mul, mul_one]
      rw [op_smul_val, map_mul, map_cornerPre]
      simp only [mul_assoc, h1, h2])

@[simp] theorem cornerContract_tmul (z : Corner φ) (n : N) :
    cornerContract φ hφ hs N (Ind.tmul z n) = cornerPre φ hs z.1 • n := rfl

theorem cornerContract_unitGen (n : N) :
    cornerContract φ hφ hs N (Ind.tmul (unitGen φ) n) = n := by
  rw [cornerContract_tmul]
  have : cornerPre φ hs (unitGen φ).1 = 1 := cornerPre_eq φ hφ hs (by
    change φ 1 = φ 1 * φ 1 * φ 1
    rw [unit_mul_unit, unit_mul_unit])
  rw [this, one_smul]

theorem tmul_unitGen_cornerContract (t : Ind N φ) :
    Ind.tmul (unitGen φ) (cornerContract φ hφ hs N t) = φ 1 • t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, Ind.tmul_zero, smul_zero]
  | tmul z n =>
    rw [cornerContract_tmul, ← Ind.op_smul_tmul, Ind.smul_tmul]
    congr 1
    refine Subtype.ext ?_
    change φ 1 * φ (cornerPre φ hs z.1) = φ 1 * z.1
    rw [map_cornerPre, ← mul_assoc, ← mul_assoc, unit_mul_unit, mul_assoc, z.2]
  | add s t hs' ht => rw [map_add, Ind.tmul_add, hs', ht, smul_add]

include hφ hs in
/-- The unit of induction ⊣ restriction along a corner embedding is bijective. -/
theorem unitMap_bijective : Function.Bijective (unitMap (φ := φ) N) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun m => cornerContract φ hφ hs N m.val, fun n => ?_, fun m => ?_⟩
  · exact cornerContract_unitGen φ hφ hs N n
  · refine Res.ext ?_
    rw [unitMap_val, tmul_unitGen_cornerContract, m.prop]

end

include hφ hs in
theorem isIso_adjunction_unit : IsIso (adjunction.{u, w} φ).unit := by
  have : ∀ N, IsIso ((adjunction.{u, w} φ).unit.app N) := fun N => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact unitMap_bijective φ hφ hs N
  exact NatIso.isIso_of_isIso_app _

include hφ hs in
/-- Induction along a corner embedding is fully faithful. -/
theorem functor_full_faithful : (functor.{u, w} φ).Full ∧ (functor.{u, w} φ).Faithful := by
  have := isIso_adjunction_unit.{u, w} φ hφ hs
  exact ⟨(adjunction φ).fullyFaithfulLOfIsIsoUnit.full,
    (adjunction φ).fullyFaithfulLOfIsIsoUnit.faithful⟩

include hφ hs in
/-- **Restriction to a corner is a Serre quotient.** For an injective `φ : A →ₙ+* B` with image
`φ(1) B φ(1)`, the functor `M ↦ φ(1) M` from `B`-modules to `A`-modules is the localization at
the Serre class of `B`-modules killed by `φ(1)`. -/
theorem resFunctor_isLocalization :
    (resFunctor.{u, u} φ).IsLocalization (resFunctor.{u, u} φ).kernel.isoModSerre := by
  obtain ⟨h1, h2⟩ := functor_full_faithful.{u, u} φ hφ hs
  exact Abelian.isLocalization_isoModSerre_kernel_of_fullyFaithful_leftAdjoint _ (adjunction φ)

end InductionAlong

end

end Categorification
