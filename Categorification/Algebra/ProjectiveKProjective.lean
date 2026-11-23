/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensor
import Mathlib.Algebra.Module.Projective

set_option backward.isDefEq.respectTransparency false

/-!
# Projective modules in degree zero are K-projective

For a ring `A` (a dg ring concentrated in degree `0`) and a projective `A`-module `M`, the dg
module `InDegreeZero M` is K-projective: a morphism `f : M → N` to an acyclic dg module lands in
the degree-`0` cocycles of `N`, which are the image of `d : N⁻¹ → N⁰`, and projectivity of `M`
lifts `f` along `d` to a null-homotopy.

This is the input used to compute derived tensor products `M ⊗ᴸ_B -` with bimodules that are
projective over the target ring on K-projective arguments, as in B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v2, proof of Proposition 6.7 (the functors
`𝔈_i`, `𝔉_i` are tensor products with bimodules projective on both sides).

## Main results

* `Categorification.InDegreeZero.isKProjective`: `InDegreeZero M` is K-projective for
  `M` projective.
-/

open CategoryTheory DG DG.DegreeZero

universe w

namespace Categorification.InDegreeZero

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

theorem mem_grading_zero (m : InDegreeZero M) : m ∈ grading (M := InDegreeZero M) 0 :=
  (mem_grading_iff M).mpr (Or.inl rfl)

theorem ring_mem_grading_zero (a : A) : a ∈ grading (M := A) 0 :=
  ring_mem_grading_iff.mpr (Or.inl rfl)

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

variable (A N) in
/-- The differential of a dg module over a ring in degree `0`, as an `A`-linear map. -/
def dLinear : N →ₗ[A] N where
  toFun := d
  map_add' := map_add d
  map_smul' a x := by
    rw [d_smul_of_mem_zero (ring_mem_grading_zero a), ring_d_apply, zero_smul, zero_add]
    rfl

variable (A N) in
/-- The degree `-1` part of a dg module over a ring in degree `0`, as an `A`-submodule. -/
def gradingNegOne : Submodule A N where
  carrier := grading (M := N) (-1)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a x hx := by
    simpa using smul_mem_grading (ring_mem_grading_zero a) hx

instance [Module.Projective A M] : Module.Projective A (InDegreeZero M) :=
  inferInstanceAs (Module.Projective A M)

/-- **A projective module in degree `0` is K-projective.** -/
theorem isKProjective [Module.Projective A M] : IsKProjective.{w} A (InDegreeZero M) := by
  intro N _ _ _ _ hN f
  let g : gradingNegOne A N →ₗ[A] N := (dLinear A N).comp (gradingNegOne A N).subtype
  have hf : ∀ m : InDegreeZero M, f m ∈ LinearMap.range g := by
    intro m
    have hm : f m ∈ grading (M := N) 0 := by simpa using f.map_mem (mem_grading_zero m)
    have hdm : d (f m) = 0 := by rw [← f.map_d, d_apply, map_zero]
    obtain ⟨y, hy, hdy⟩ := hN.exists_d_eq hm hdm
    exact ⟨⟨y, hy⟩, hdy⟩
  let f' : InDegreeZero M →ₗ[A] LinearMap.range g :=
    LinearMap.codRestrict _ (f.toLinearMap) hf
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property g.rangeRestrict f'
    (LinearMap.surjective_rangeRestrict g)
  have hℓ' : ∀ m, d ((ℓ m : gradingNegOne A N) : N) = f m := fun m =>
    congrArg Subtype.val (LinearMap.congr_fun hℓ m)
  let h : Cochain A (InDegreeZero M) N (-1) :=
    { toFun := fun m => (ℓ m : N)
      map_zero' := by simp
      map_add' := fun x y => by simp
      map_mem' := fun i x hx => by
        rcases (mem_grading_iff M).mp hx with rfl | rfl
        · simp
        · simp
      map_smul' := fun {i a} ha x => by
        rcases ring_mem_grading_iff.mp ha with rfl | rfl
        · simp
        · simp }
  refine homotopic_zero_iff_exists.mpr ⟨h, ?_⟩
  ext m
  rw [DG.δ_apply (-1) 0 (by norm_num), Cochain.ofHom_apply, d_apply, map_zero, smul_zero,
    sub_zero]
  exact (hℓ' m).symm

end Categorification.InDegreeZero
