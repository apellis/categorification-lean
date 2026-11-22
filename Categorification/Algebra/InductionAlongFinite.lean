/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.InductionAlongRes
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Induction and restriction preserve finite generation

Induction along a nonunital ring map `φ : A → B` sends finitely generated `A`-modules to
finitely generated `B`-modules (`InductionAlong.Ind.finite`). Restriction does so when `B` is a
finite algebra over a field `k` and `φ` is `k`-linear (`InductionAlong.Res.finite`).

These keep Webster's functors `Fᵢ` and `Eᵢ` on finitely generated modules over the tensor
product algebras (arXiv:1309.3796v2, §4.6, §5), the setting of Chuang–Rouquier's weak
`𝔰𝔩₂`-categorifications (arXiv:math/0407205v2, §5.1.1).
-/

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
