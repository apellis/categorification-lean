/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.FiniteResolution
import Categorification.Algebra.Graded.UpResolutionTensor
import Categorification.Algebra.Graded.UpResolutionSimple

/-!
# Resolutions in `C↑` of modules of finite projective dimension

Let `A` be a finite-dimensional graded algebra over a field `k`, zero in degrees `< a` (with
`a ≤ 0`). A finite-dimensional graded `A`-module `N` of projective dimension `≤ n` that is zero in
degrees `< m` has a graded projective resolution in `C↑` with constant `n + 1 - m - (n + 1) a`
(`GFin.UpResolution.exists_of_hasProjectiveDimensionLT`). The constant depends only on `n`, `m`
and `a`. This uniformity is what B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.28, uses when he replaces the standard modules in a
standardized resolution by their finite projective resolutions (Corollary 5.24).

## Main results

* `GFin.UpResolution.ofProjective` : `⋯ → 0 → P → P` for a graded projective `P`.
* `GFin.UpResolution.exists_of_hasProjectiveDimensionLT`.
-/

noncomputable section

namespace Categorification.Graded

open CategoryTheory
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [Module.Finite k A]

namespace GFin

namespace UpResolution

/-- The resolution `⋯ → 0 → P → P` of a graded projective module zero in degrees `< m`. -/
def ofProjective (P : GFin 𝒜) [Module.Projective A P.carrier] {m : ℤ}
    (h : ∀ j < m, P.grading j = ⊥) : UpResolution P (1 - m) :=
  haveI : Subsingleton (ker (LinearMap.id : P.carrier →ₗ[A] P.carrier) fun _ _ hx => hx).carrier :=
    ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  ((cons (kerShortExact (LinearMap.id : P.carrier →ₗ[A] P.carrier) (fun _ _ hx => hx)
      Function.surjective_id) (c := -m) (fun j hj => h j (by omega))
    (ofSubsingleton _ (-m))).mono (by omega))

theorem coverKernel_grading_eq_bot (N : GFin 𝒜) {j : ℤ}
    (h : (tensorGrading 𝒜 N.grading) j = ⊥) : (coverKernel N).grading j = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x.1 ∈ (tensorGrading 𝒜 N.grading) j := hx
  rw [h, Submodule.mem_bot] at this
  exact (Submodule.mem_bot k).2 (Subtype.ext this)

/-- **Uniform resolutions in `C↑` for modules of finite projective dimension.** -/
theorem exists_of_hasProjectiveDimensionLT {a : ℤ} (hA : ∀ j < a, 𝒜 j = ⊥) (ha : a ≤ 0)
    (n : ℕ) : ∀ (N : GFin 𝒜) {m : ℤ}, (∀ j < m, N.grading j = ⊥) →
      HasProjectiveDimensionLT (ModuleCat.of A N.carrier) (n + 1) →
      Nonempty (UpResolution N (n + 1 - m - (n + 1) * a)) := by
  induction n with
  | zero =>
    intro N m hN hpd
    have : Module.Projective A N.carrier := (IsProjective.iff_projective _).mpr inferInstance
    exact ⟨(ofProjective N hN).mono (by push_cast; nlinarith)⟩
  | succ n ih =>
    intro N m hN hpd
    let S := coverShortExact N
    let T : ShortComplex (ModuleCat.{u} A) :=
      { X₁ := ModuleCat.of A (coverKernel N).carrier
        X₂ := ModuleCat.of A (cover N).carrier
        X₃ := ModuleCat.of A N.carrier
        f := ModuleCat.ofHom S.f
        g := ModuleCat.ofHom S.g
        zero := by ext x; exact S.exact.apply_apply_eq_zero x }
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T S.exact S.injective S.surjective
    have : Projective T.X₂ := (IsProjective.iff_projective _).mp (cover N).projective
    have hK : HasProjectiveDimensionLT T.X₁ (n + 1) := hT.hasProjectiveDimensionLT_X₁ (n + 1)
      inferInstance hpd
    have hC : ∀ j < a + m, (tensorGrading 𝒜 N.grading) j = ⊥ := fun j hj =>
      tensorGrading_eq_bot hA hN hj
    obtain ⟨R⟩ := ih (coverKernel N) (m := a + m)
      (fun j hj => coverKernel_grading_eq_bot N (hC j hj)) hK
    have : Module.Projective A (cover N).toGFin.carrier := (cover N).projective
    exact ⟨(cons (P := (cover N).toGFin) S (fun j hj => hC j (by nlinarith))
      R).mono (by push_cast; nlinarith)⟩

end UpResolution

end GFin

end Categorification.Graded
