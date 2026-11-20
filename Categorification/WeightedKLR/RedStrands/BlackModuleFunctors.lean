/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.Algebra.InductionAlongRes

/-!
# The functors `Eᵢ` and `Fᵢ` on right `T^λ`-modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
the functors `Fᵢ` and `Eᵢ` defined after Theorem 4.31.

The map `appendBlack : T^λ_ν → T^λ_{ν+i}` adjoins a black strand labelled `i` on the right;
it sends `1` to the idempotent `e' = appendBlack 1`. For right modules, Webster's functors are
`Fᵢ M = M ⊗_{T^λ_ν} e' T^λ_{ν+i}` and `Eᵢ N = N e'`, restricted to `T^λ_ν` along `appendBlack`.
Right modules are left modules over the opposite algebra, and these are induction and restriction
(`InductionAlong`) along the opposite map `appendBlackOp`. Hence `Fᵢ` is left adjoint to `Eᵢ`
(`blackAdjunction`), and `Eᵢ` is exact (`blackE_map_injective`, `blackE_map_surjective`,
`blackE_map_exact`). The modules here are ungraded.

## Main definitions

* `Stendhal.appendBlackOp`: the opposite of `appendBlack`.
* `Stendhal.blackF`, `Stendhal.blackE`: the functors `Fᵢ` and `Eᵢ` on right modules.
* `Stendhal.blackAdjunction`: `Fᵢ ⊣ Eᵢ`.
-/

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

/-- The opposite of the black-appending map, `(T^λ_ν)ᵐᵒᵖ → (T^λ_{ν+i})ᵐᵒᵖ`. -/
noncomputable def appendBlackOp :
    (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ →ₙ+*
      (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom (appendBlack Q Λ i ν))

theorem appendBlackOp_op (x : TensorProductAlgebra k Q Λ ν) :
    appendBlackOp Q Λ i ν (op x) = op (appendBlack Q Λ i ν x) :=
  rfl

/-- **Webster's `Fᵢ`** on right modules: `M ↦ M ⊗_{T^λ_ν} e' T^λ_{ν+i}` (arXiv:1309.3796v3,
§4.6). -/
noncomputable def blackF :
    ModuleCat.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ :=
  InductionAlong.functor.{u, u} (appendBlackOp Q Λ i ν)

/-- **Webster's `Eᵢ`** on right modules: `N ↦ N e'`, a right `T^λ_ν`-module through
`appendBlack` (arXiv:1309.3796v3, §4.6). -/
noncomputable def blackE :
    ModuleCat.{u} (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ :=
  InductionAlong.resFunctor.{u, u} (appendBlackOp Q Λ i ν)

/-- `Fᵢ` is left adjoint to `Eᵢ`. -/
noncomputable def blackAdjunction : blackF Q Λ i ν ⊣ blackE Q Λ i ν :=
  InductionAlong.adjunction.{u, u} (appendBlackOp Q Λ i ν)

section Exactness

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B}
  {M M' M'' : Type u} [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M']
  [AddCommGroup M''] [Module B M'']

theorem res_map_injective {f : M →ₗ[B] M'} (hf : Function.Injective f) :
    Function.Injective (Res.map (φ := φ) f) :=
  fun _ _ h => Res.ext (hf (congrArg Res.val h))

theorem res_map_surjective {f : M →ₗ[B] M'} (hf : Function.Surjective f) :
    Function.Surjective (Res.map (φ := φ) f) := by
  intro m
  obtain ⟨n, hn⟩ := hf m.val
  refine ⟨Res.mk (φ 1 • n) (by rw [smul_smul, ← map_mul, one_mul]), Res.ext ?_⟩
  rw [Res.val_map, Res.val_mk, map_smul, hn, m.prop]

theorem res_map_exact {f : M →ₗ[B] M'} {g : M' →ₗ[B] M''} (h : Function.Exact f g) :
    Function.Exact (Res.map (φ := φ) f) (Res.map (φ := φ) g) := by
  intro m
  constructor
  · intro hm
    obtain ⟨n, hn⟩ := (h m.val).1 (congrArg Res.val hm)
    refine ⟨Res.mk (φ 1 • n) (by rw [smul_smul, ← map_mul, one_mul]), Res.ext ?_⟩
    rw [Res.val_map, Res.val_mk, map_smul, hn, m.prop]
  · rintro ⟨n, rfl⟩
    exact Res.ext (by
      rw [Res.val_map, Res.val_map, Res.val_zero]
      exact (h _).2 ⟨n.val, rfl⟩)

end Exactness

variable {Q Λ i ν}
variable {N N' N'' : ModuleCat.{u}
  (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ}

/-- `Eᵢ` preserves injections. -/
theorem blackE_map_injective {f : N ⟶ N'} (hf : Function.Injective f.hom) :
    Function.Injective ((blackE Q Λ i ν).map f).hom :=
  res_map_injective hf

/-- `Eᵢ` preserves surjections. -/
theorem blackE_map_surjective {f : N ⟶ N'} (hf : Function.Surjective f.hom) :
    Function.Surjective ((blackE Q Λ i ν).map f).hom :=
  res_map_surjective hf

/-- `Eᵢ` preserves exactness in the middle. -/
theorem blackE_map_exact {f : N ⟶ N'} {g : N' ⟶ N''} (h : Function.Exact f.hom g.hom) :
    Function.Exact ((blackE Q Λ i ν).map f).hom ((blackE Q Λ i ν).map g).hom :=
  res_map_exact h

end Categorification.Stendhal
