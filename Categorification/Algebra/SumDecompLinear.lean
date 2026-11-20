/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.Karoubi
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Direct sum decompositions of modules as linear equivalences

A decomposition `A ≅ B ⊕ ⨁_s C_s` in a category of modules, given by components
(`SumDecomp`), is a linear equivalence `A ≃ B × Π_s C_s` (`SumDecomp.linearEquiv`). If the
modules over `S` are identified with modules over `R` along a ring isomorphism `σ : R ≃+* S`
by additive maps that are semilinear along `σ`, the decomposition passes to an `R`-linear
equivalence (`SumDecomp.semilinearEquiv`).

This turns the decompositions of module functors used in Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5, into isomorphisms of
modules over the algebras on which Webster's functors act.
-/

namespace Categorification

open CategoryTheory

noncomputable section

universe u w

namespace SumDecomp

variable {S : Type u} [Ring S] {A B : ModuleCat.{w} S} {ι : Type} [Fintype ι] [DecidableEq ι]
  {Cs : ι → ModuleCat.{w} S} (D : SumDecomp A B Cs)

theorem apply_total (x : A) : D.b0.hom (D.a0.hom x) + ∑ s, (D.b s).hom ((D.a s).hom x) = x := by
  have h := congrArg (fun f => f.hom x) D.total
  simpa [ModuleCat.hom_add, ModuleCat.hom_sum] using h

theorem apply_b0_a0 (y : B) : D.a0.hom (D.b0.hom y) = y :=
  congrArg (fun f => f.hom y) D.b0_a0

theorem apply_b_a0 (s : ι) (z : Cs s) : D.a0.hom ((D.b s).hom z) = 0 :=
  congrArg (fun f => f.hom z) (D.b_a0 s)

theorem apply_b0_a (t : ι) (y : B) : (D.a t).hom (D.b0.hom y) = 0 :=
  congrArg (fun f => f.hom y) (D.b0_a t)

theorem apply_b_a (s t : ι) (z : Cs s) :
    (D.a t).hom ((D.b s).hom z) = if h : s = t then h ▸ z else 0 := by
  split_ifs with h
  · subst h
    exact congrArg (fun f => f.hom z) (D.b_a_self s)
  · exact congrArg (fun f => f.hom z) (D.b_a_ne s t h)

/-- A decomposition `A ≅ B ⊕ ⨁_s C_s` of modules as a linear equivalence. -/
def linearEquiv : A ≃ₗ[S] B × ((s : ι) → Cs s) where
  toFun x := (D.a0.hom x, fun s => (D.a s).hom x)
  invFun p := D.b0.hom p.1 + ∑ s, (D.b s).hom (p.2 s)
  map_add' x y := by simp; rfl
  map_smul' c x := by simp; rfl
  left_inv x := D.apply_total x
  right_inv p := by
    obtain ⟨y, z⟩ := p
    refine Prod.ext ?_ (funext fun t => ?_)
    · simp [map_sum, D.apply_b0_a0, D.apply_b_a0]
    · simp only [map_add, map_sum, D.apply_b0_a, D.apply_b_a, zero_add]
      rw [Finset.sum_eq_single t
        (fun s _ hs => dite_eq_right_iff.mpr fun h => absurd h hs) (by simp)]
      simp

@[simp] theorem linearEquiv_apply (x : A) :
    D.linearEquiv x = (D.a0.hom x, fun s => (D.a s).hom x) :=
  rfl

end SumDecomp

section Semilinear

variable {R : Type*} {S : Type u} [Ring R] [Ring S] (σ : R ≃+* S)
  {U V M : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup M] [Module R U]
  [Module R V] [Module R M]
  {T₁ T₂ T₃ : ModuleCat.{w} S} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An `R`-linear equivalence from a decomposition of `S`-modules and additive identifications
semilinear along `σ : R ≃+* S`: if `U ≅ T₁`, `V ≅ T₂` and `M ≅ T₃` semilinearly and
`T₁ ≅ T₂ ⊕ T₃^{⊕ ι}`, then `U ≅ V × M^ι` as `R`-modules. -/
def SumDecomp.semilinearEquiv (D : SumDecomp T₁ T₂ (fun _ : ι => T₃))
    (eU : U ≃ₗ[ℤ] T₁) (heU : ∀ (a : R) (x : U), eU (a • x) = σ a • eU x)
    (eV : V ≃ₗ[ℤ] T₂) (heV : ∀ (a : R) (x : V), eV (a • x) = σ a • eV x)
    (eM : M ≃ₗ[ℤ] T₃) (heM : ∀ (a : R) (x : M), eM (a • x) = σ a • eM x) :
    U ≃ₗ[R] V × (ι → M) where
  toFun x := (eV.symm (D.a0.hom (eU x)), fun s => eM.symm ((D.a s).hom (eU x)))
  invFun p := eU.symm (D.linearEquiv.symm (eV p.1, fun s => eM (p.2 s)))
  map_add' x y := by simp; rfl
  map_smul' a x := by
    have hV : ∀ y : T₂, eV.symm (σ a • y) = a • eV.symm y := fun y => by
      apply eV.injective; rw [heV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hM : ∀ y : T₃, eM.symm (σ a • y) = a • eM.symm y := fun y => by
      apply eM.injective; rw [heM, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [heU, map_smul, hV, hM, RingHom.id_apply, Prod.smul_mk]
    rfl
  left_inv x := by
    apply eU.injective
    simp only [LinearEquiv.apply_symm_apply]
    exact D.linearEquiv.symm_apply_apply (eU x)
  right_inv p := by
    obtain ⟨y, z⟩ := p
    have h := D.linearEquiv.apply_symm_apply (eV y, fun s => eM (z s))
    simp only [SumDecomp.linearEquiv_apply, Prod.mk.injEq] at h
    simp only [LinearEquiv.apply_symm_apply, h.1, LinearEquiv.symm_apply_apply]
    refine Prod.ext rfl (funext fun s => ?_)
    have h2 := congrFun h.2 s
    simp only [h2, LinearEquiv.symm_apply_apply]

end Semilinear

end

end Categorification
