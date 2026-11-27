/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ExtEuler
import Categorification.Algebra.CompactModules

set_option backward.isDefEq.respectTransparency false

/-!
# Modules with finite projective resolutions are compact

If `N` has a finite resolution by finitely generated projectives over `A` (`GFin.Resolution`),
then `N`, as a module over a ring `R ≅ A` placed in degree `0`, is compact in `D(R)`
(`isCompact_resModule_of_resolution`). In Webster, arXiv:1309.3796v3, proof of Theorem 6.15, this
makes the images of the projectives under the braiding compact.
-/

noncomputable section

namespace Categorification.Graded

open CategoryTheory DG DG.DerivedCategory
open scoped DG.DegreeZero

variable {k : Type} [Field k] {A : Type} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  {R : Type} [Ring R] (φ : A ≃+* R)

theorem finite_resModule (P : GFin 𝒜) [Module.Finite A P.carrier] :
    Module.Finite R (resModule φ P) := by
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A P.carrier).FG)
  refine ⟨⟨S, Submodule.eq_top_iff'.2 fun m => ?_⟩⟩
  have hm : m ∈ Submodule.span A (S : Set P.carrier) := by rw [hS]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have e : a • x = (φ a • (show resModule φ P from x) : resModule φ P) := by
      change a • x = φ.symm (φ a) • x
      rw [RingEquiv.symm_apply_apply]
    rw [e]
    exact Submodule.smul_mem _ _ hx

variable [HasDerivedCategory.{0, 0} R]

/-- **A module with a finite resolution by finitely generated projectives is compact** in the
derived category of `R ≅ A`. -/
theorem isCompact_resModule_of_resolution :
    ∀ {N : GFin 𝒜} {l : List (GFin 𝒜)}, GFin.Resolution N l →
      (∀ P ∈ l, Module.Projective A P.carrier ∧ Module.Finite A P.carrier) →
      IsCompact.{0} (moduleObj (resModule φ N))
  | _, _, .single (P := P) e, hl => by
    obtain ⟨h₁, h₂⟩ := hl P (List.mem_singleton_self P)
    have := projective_resModule φ P
    have := finite_resModule φ P
    exact isCompact_moduleObj_of_iso ((resFunctor φ).mapIso e.toLinearEquiv.toModuleIso)
      (isCompact_of_projective _)
  | _, _, .cons (K := K) (P := P) S r, hl => by
    obtain ⟨h₁, h₂⟩ := hl P List.mem_cons_self
    have := projective_resModule φ P
    have := finite_resModule φ P
    have hK := isCompact_resModule_of_resolution r fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    exact isCompact_of_shortExact ((toShortComplex S).map (resFunctor φ))
      ((toShortComplex_shortExact S).map_of_exact (resFunctor φ)) hK
      (isCompact_of_projective (resModule φ P))

end Categorification.Graded
