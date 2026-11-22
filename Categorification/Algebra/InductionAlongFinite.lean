/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensor
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of induced modules and of quotients with compatible actions

Generic finiteness statements used in the dimension count of Webster, arXiv:1309.3796v3,
proof of Proposition 5.5.

## Main results

* `InductionAlong.IndK.finite`: `IndK k N φ` is a finitely generated `B`-module when `N` is a
  finitely generated `A`-module.
* `InductionAlong.IndK.finite_restrict`: if moreover `B` is a finite `k`-module, then
  `IndK k N φ` is a finite `k`-module.
* `Module.Finite.of_surjective_compatible`: if an additive surjection `π : M → V`
  intertwines the action of `a : A` on `M` with the action of `f a : T` on `V`, and `M` is a
  finitely generated `A`-module, then `V` is a finitely generated `T`-module.
* `Module.Finite.restrictScalars_of_finite`: `RestrictScalars k S X` is a finite `k`-module
  when `S` is a finite `k`-algebra and `X` a finitely generated `S`-module.
* `fixSub_finiteDimensional`: the subspace `f M` of a finite-dimensional module over a field
  is finite-dimensional.
* `InductionAlong.Ind.finite`, `InductionAlong.Res.finite`: induction and restriction along a
  nonunital map preserve finite generation (restriction when `B` is a finite algebra over a
  field `k` and `φ` is `k`-linear); these keep Webster's `Fᵢ`, `Eᵢ` on finitely generated
  modules (arXiv:1309.3796v2, §4.6, §5).
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable (k : Type*) [CommRing k] {A : Type u} [Ring A] {B : Type u} [Ring B] [Algebra k B]
  (N : Type w) [AddCommGroup N] [Module A N] (φ : A →ₙ+* B)

/-- **Induction of a finitely generated module is finitely generated**: `B φ(1) ⊗_A N` is a
finitely generated `B`-module when `N` is a finitely generated `A`-module. -/
theorem IndK.finite [Module.Finite A N] : Module.Finite B (IndK k N φ) := by
  have : Module.Finite B (Corner φ) :=
    Module.Finite.of_surjective
      ({ toFun := fun b => ⟨b * φ 1, by rw [mem_lIdeal, mul_assoc, unit_mul_unit]⟩
         map_add' := fun x y => Subtype.ext (add_mul _ _ _)
         map_smul' := fun c x => Subtype.ext (mul_assoc _ _ _) } : B →ₗ[B] Corner φ)
      fun z => ⟨z.1, Subtype.ext z.2⟩
  exact BalancedTensor.finite (k := ℤ)

/-- **Induction of a finitely generated module to a finite `k`-algebra** is a finite
`k`-module. -/
theorem IndK.finite_restrict [Module.Finite A N] [Module.Finite k B] :
    Module.Finite k (IndK k N φ) :=
  haveI := IndK.finite k N φ
  Module.Finite.trans B (IndK k N φ)

end InductionAlong

/-- **Finiteness through a compatible surjection.** Let `π : M → V` be an additive surjection
from an `A`-module to a `T`-module and `f : A → T` a function with
`π (a • m) = f a • π m`. If `M` is a finitely generated `A`-module, then `V` is a finitely
generated `T`-module. -/
theorem Module.Finite.of_surjective_compatible {A T M V : Type*} [Semiring A] [Semiring T]
    [AddCommMonoid M] [Module A M] [AddCommMonoid V] [Module T V] [Module.Finite A M]
    (π : M →+ V) (hπ : Function.Surjective π) (f : A → T)
    (hf : ∀ (a : A) (m : M), π (a • m) = f a • π m) : Module.Finite T V := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := M)
  refine ⟨⟨G.image π, Submodule.eq_top_iff'.2 fun v => ?_⟩⟩
  obtain ⟨m, rfl⟩ := hπ v
  have hm : m ∈ Submodule.span A (G : Set M) := hG ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [hf]; exact Submodule.smul_mem _ _ hx

/-- **Restriction of scalars of a finitely generated module over a finite `k`-algebra** is a
finite `k`-module. -/
theorem Module.Finite.restrictScalars_of_finite (k S X : Type*) [CommSemiring k] [Semiring S]
    [Algebra k S] [AddCommMonoid X] [Module S X] [Module.Finite k S] [Module.Finite S X] :
    Module.Finite k (RestrictScalars k S X) :=
  letI : Module S (RestrictScalars k S X) := RestrictScalars.moduleOrig k S X
  haveI : Module.Finite S (RestrictScalars k S X) := ‹Module.Finite S X›
  Module.Finite.trans S (RestrictScalars k S X)

/-- The subspace `f M = {m | f m = m}` of a finite-dimensional module over a field is
finite-dimensional. -/
theorem fixSub_finiteDimensional (k : Type*) [Field k] {A : Type*} [Ring A] [Algebra k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] (f : A) : FiniteDimensional k (fixSub k M f) :=
  inferInstance

end

end Categorification

set_option backward.isDefEq.respectTransparency false

namespace Categorification.InductionAlong

open MulOpposite

universe u w

section Ind

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B}
  {N : Type w} [AddCommGroup N] [Module A N]

theorem Ind.op_smul_unitGen (a : A) : (op a • unitGen φ : Corner φ) = φ a • unitGen φ :=
  Subtype.ext (by
    change φ 1 * φ a = φ a * φ 1
    rw [← map_mul, ← map_mul, one_mul, mul_one])

theorem Ind.tmul_eq_smul (z : Corner φ) (n : N) :
    Ind.tmul z n = z.1 • Ind.tmul (unitGen φ) n := by
  rw [Ind.smul_tmul]
  congr 1
  exact Subtype.ext z.2.symm

/-- Induction preserves finite generation. -/
theorem Ind.finite [Module.Finite A N] : Module.Finite B (Ind N φ) := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A N).FG)
  refine ⟨⟨S.image (Ind.tmul (unitGen φ)), eq_top_iff.mpr fun t ht => ?_⟩⟩
  have hgen : ∀ n : N, Ind.tmul (unitGen φ) n ∈
      Submodule.span B ((S.image (Ind.tmul (unitGen φ)) : Finset (Ind N φ)) : Set (Ind N φ)) := by
    intro n
    have hn : n ∈ Submodule.span A (S : Set N) := hS ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    | zero => rw [Ind.tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Ind.tmul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← Ind.op_smul_tmul, Ind.op_smul_unitGen, ← Ind.smul_tmul]
      exact Submodule.smul_mem _ _ hx
  clear ht
  induction t using Ind.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul z n => rw [Ind.tmul_eq_smul]; exact Submodule.smul_mem _ _ (hgen n)
  | add s t hs ht => exact Submodule.add_mem _ hs ht

end Ind

section Res

variable (k : Type*) [Field k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] [Module.Finite k B] {φ : A →ₙ+* B} (hφ : ∀ (c : k) (a : A), φ (c • a) = c • φ a)
  {M : Type w} [AddCommGroup M] [Module B M]

include hφ in
/-- Restriction along a `k`-linear map into a finite `k`-algebra preserves finite
generation. -/
theorem Res.finite [Module.Finite B M] : Module.Finite A (Res φ M) := by
  let _ : Module k M := Module.compHom M (algebraMap k B)
  have _ : IsScalarTower k B M := ⟨fun c b m => by
    change (c • b) • m = algebraMap k B c • b • m
    rw [Algebra.smul_def, mul_smul]⟩
  have _ : Module.Finite k M := Module.Finite.trans B M
  let _ : Module k (Res φ M) := Module.compHom (Res φ M) (algebraMap k A)
  have _ : IsScalarTower k A (Res φ M) := ⟨fun c a m => by
    change (c • a) • m = algebraMap k A c • a • m
    rw [Algebra.smul_def, mul_smul]⟩
  let g : Res φ M →ₗ[k] M :=
    { toFun := Res.val
      map_add' := Res.val_add
      map_smul' := fun c m => by
        change (algebraMap k A c • m).val = algebraMap k B c • m.val
        rw [Res.val_smul, Algebra.algebraMap_eq_smul_one, hφ, smul_assoc, m.prop]
        rfl }
  have _ : Module.Finite k (Res φ M) :=
    Module.Finite.of_injective g fun _ _ h => Res.ext h
  exact Module.Finite.of_restrictScalars_finite k A (Res φ M)

end Res

end Categorification.InductionAlong
