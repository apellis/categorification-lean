/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.Graded.K0
import Categorification.Algebra.Graded.ProjectiveCover

/-!
# Graded `K₀` is additive on graded short exact sequences

For a graded algebra `A` over a field and finitely generated graded projective modules, a short
exact sequence `0 → M → P → Q → 0` of degree-preserving maps splits by a degree-preserving
section (graded projectivity of `Q`, `Graded.exists_lift_of_projective`), so `P ≅ M ⊕ Q` as
graded modules and `[P] = [M] + [Q]` in the graded `K₀`. This is the relation by which classes in
the graded `K₀` of Khovanov–Lauda, arXiv:0803.4121v2, §2.5, and of B. Webster, arXiv:1209.2463v4,
proof of Theorem 2.19, are computed along filtrations.

## Main results
* `Graded.mem_of_injective_of_mem`: an injective degree-preserving map reflects degrees.
* `Graded.K0.of_eq_add_of_exact`: `[P] = [M] + [Q]` for a graded short exact sequence.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Function

/-- An injective degree-preserving map reflects degrees: if `f x` has degree `d`, so does `x`. -/
theorem mem_of_injective_of_mem {k R M N : Type*} [CommRing k] [Semiring R] [AddCommGroup M]
    [Module k M] [Module R M] [AddCommGroup N] [Module k N] [Module R N]
    {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} [Decomposition ℳ] [Decomposition 𝒩]
    {f : M →ₗ[R] N} (hf : PreservesGrading ℳ 𝒩 f) (hinj : Injective f) {d : ℤ} {x : M}
    (hx : f x ∈ 𝒩 d) : x ∈ ℳ d := by
  have h : f (decompose ℳ x d) = f x := by
    rw [← decompose_map hf, decompose_of_mem_same _ hx]
  rw [← hinj h]
  exact (decompose ℳ x d).2

namespace K0

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- **`K₀` of graded projective modules is additive on graded short exact sequences**: for
degree-preserving maps `i : M → P` injective and `p : P → Q` surjective with `ker p = im i`,
`[P] = [M] + [Q]`. -/
theorem of_eq_add_of_exact (M P Q : GProj 𝒜) (i : M.carrier →ₗ[A] P.carrier) (p : P.carrier →ₗ[A] Q.carrier)
    (hi : PreservesGrading M.grading P.grading i) (hp : PreservesGrading P.grading Q.grading p)
    (hinj : Injective i) (hsurj : Surjective p) (hex : Exact i p) :
    of P = of M + of Q := by
  obtain ⟨s, hs, hps⟩ := exists_lift_of_projective 𝒜 (ℳ := Q.grading) (𝒩 := P.grading)
    (𝒬 := Q.grading) hp hsurj (h := LinearMap.id) (fun _ _ hx => hx)
  have hps' : ∀ y, p (s y) = y := fun y => LinearMap.congr_fun hps y
  let f : M.carrier × Q.carrier →ₗ[A] P.carrier := i.coprod s
  have hf : ∀ x : M.carrier × Q.carrier, f x = i x.1 + s x.2 := fun _ => rfl
  have hpf : ∀ x : M.carrier × Q.carrier, p (f x) = x.2 := fun x => by
    rw [hf, map_add, hex.apply_apply_eq_zero, zero_add, hps']
  have hbij : Bijective f := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · have h2 : x.2 = y.2 := by rw [← hpf x, ← hpf y, hxy]
      have h1 : i x.1 = i y.1 := by
        have := hxy
        rw [hf, hf, h2] at this
        exact add_right_cancel this
      exact Prod.ext (hinj h1) h2
    · obtain ⟨m, hm⟩ := (hex (y - s (p y))).1 (by rw [map_sub, hps', sub_self])
      exact ⟨(m, p y), by rw [hf, hm, sub_add_cancel]⟩
  let e := LinearEquiv.ofBijective f hbij
  have he : PreservesGrading (Graded.prod M.grading Q.grading) P.grading f := by
    intro d x hx
    rw [hf]
    exact add_mem (hi (mem_prod.1 hx).1) (hs (mem_prod.1 hx).2)
  have hsymm : PreservesGrading P.grading (Graded.prod M.grading Q.grading)
      e.symm.toLinearMap := by
    intro d y hy
    set x := e.symm y
    have hfx : f x = y := e.apply_symm_apply y
    have hq : x.2 ∈ Q.grading d := by rw [← hpf x, hfx]; exact hp hy
    refine mem_prod.2 ⟨mem_of_injective_of_mem hi hinj ?_, hq⟩
    have : i x.1 = y - s x.2 := by rw [← hfx, hf, add_sub_cancel_right]
    change i x.1 ∈ P.grading d
    rw [this]
    exact sub_mem hy (hs hq)
  have iso : (M.prod Q).Iso P :=
    GradedEquiv.ofLinearMaps f e.symm.toLinearMap (fun x => e.symm_apply_apply x)
      (fun y => e.apply_symm_apply y) he hsymm
  rw [← of_prod]
  exact (of_eq_of_iso iso).symm

end K0

end Categorification.Graded
