/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Projective

/-!
# Projectivity descends along a quotient by an ideal

A general fact used for the left projectivity of `coe^{λ⁺}_λ` (Webster, arXiv:1309.3796v3, §7.3,
the assertion after Lemma 7.19): if `P` is a projective `R`-module, `π : R → S` a surjective ring
map and `f : P → N` a surjective map onto an `S`-module, compatible with `π` and with kernel
spanned by the elements `r • q` with `π r = 0`, then `N` is a projective `S`-module. In other
words `N ≅ S ⊗_R P` is projective.

## Main results

* `CupCap.projective_of_surjective_of_ker_le`: the descent of projectivity.
-/

namespace Categorification.Stendhal.CupCap

open Finsupp

/-- **Projectivity descends along a quotient by an ideal.** If `P` is a projective `R`-module and
`f : P → N` is a surjection onto an `S`-module, semilinear along a surjective ring map
`π : R → S`, whose kernel is spanned by the `r • q` with `π r = 0`, then `N` is projective. -/
theorem projective_of_surjective_of_ker_le {R S P N : Type*} [Ring R] [Ring S]
    [AddCommMonoid P] [Module R P] [AddCommGroup N] [Module S N] [hP : Module.Projective R P]
    (π : R →+* S) (hπ : Function.Surjective π) (f : P →+ N)
    (hf : ∀ (r : R) (p : P), f (r • p) = π r • f p) (hfs : Function.Surjective f)
    (hker : ∀ p, f p = 0 →
      p ∈ Submodule.span R {x | ∃ r : R, π r = 0 ∧ ∃ q : P, x = r • q}) :
    Module.Projective S N := by
  let := Module.addCommMonoidToAddCommGroup R (M := P)
  obtain ⟨s, hs⟩ := hP.out
  let g : P →+ (N →₀ S) :=
    (Finsupp.mapDomain.addMonoidHom f).comp
      ((Finsupp.mapRange.addMonoidHom π.toAddMonoidHom).comp s.toAddMonoidHom)
  have hg : ∀ p, g p = Finsupp.mapDomain f (Finsupp.mapRange π (map_zero π) (s p)) :=
    fun _ => rfl
  have hgs : ∀ (r : R) (p : P), g (r • p) = π r • g p := by
    intro r p
    rw [hg, hg, map_smul, ← Finsupp.mapDomain_smul]
    congr 1
    ext q
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]
  have hgspan : ∀ p ∈ Submodule.span R {x | ∃ r : R, π r = 0 ∧ ∃ q : P, x = r • q},
      g p = 0 := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, q, rfl⟩ := hx
      rw [hgs, hr, zero_smul]
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [hgs, hx, smul_zero]
  have hgk : ∀ p, f p = 0 → g p = 0 := fun p hp => hgspan p (hker p hp)
  have hgf : ∀ p, g (Function.surjInv hfs (f p)) = g p := by
    intro p
    have h0 : f (Function.surjInv hfs (f p) - p) = 0 := by
      rw [map_sub, Function.surjInv_eq hfs, sub_self]
    have := hgk _ h0
    rwa [map_sub, sub_eq_zero] at this
  let t : N →ₗ[S] N →₀ S :=
    { toFun := fun n => g (Function.surjInv hfs n)
      map_add' := fun n n' => by
        obtain ⟨p, rfl⟩ := hfs n
        obtain ⟨p', rfl⟩ := hfs n'
        rw [← map_add, hgf, hgf, hgf, map_add]
      map_smul' := fun c n => by
        obtain ⟨p, rfl⟩ := hfs n
        obtain ⟨r, rfl⟩ := hπ c
        rw [RingHom.id_apply, ← hf, hgf, hgf, hgs] }
  refine ⟨t, fun n => ?_⟩
  obtain ⟨p, rfl⟩ := hfs n
  change Finsupp.linearCombination S id (g (Function.surjInv hfs (f p))) = f p
  rw [hgf, hg, Finsupp.linearCombination_mapDomain, Function.id_comp]
  have key : ∀ x : P →₀ R, Finsupp.linearCombination S f (Finsupp.mapRange π (map_zero π) x) =
      f (Finsupp.linearCombination R id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => rw [Finsupp.mapRange_zero, map_zero, map_zero, map_zero]
    | add x y hx hy =>
      rw [Finsupp.mapRange_add (map_add π), map_add, map_add, map_add, hx, hy]
    | single q r =>
      rw [Finsupp.mapRange_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, id, hf]
  rw [key, hs p]

end Categorification.Stendhal.CupCap
