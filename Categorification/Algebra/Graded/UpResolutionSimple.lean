/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.UpResolution

/-!
# Resolutions in `C↑` from resolutions of simple subquotients

Let `A` be a finite-dimensional graded algebra over a field `k`. If every graded simple
subquotient of a finite-dimensional graded module `N` has a graded projective resolution in
`C↑` (Beilinson–Ginzburg–Soergel, §2.12), then so does `N`
(`GFin.exists_upResolution_of_isSubquotient`): split off a graded simple quotient, resolve the
kernel by induction on the dimension, and glue with the horseshoe lemma. This is the gluing step
of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 5.28 ("we may attach projective resolutions of each composition factor").

## Main definitions and results

* `GFin.UpResolution.ofSubsingleton` : the zero resolution of a zero module.
* `GFin.IsSubquotient L N` : `L` is a graded quotient of a graded submodule of `N`.
* `GFin.exists_upResolution_of_isSubquotient`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Function Module

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [Module.Finite k A]

namespace GFin

/-- The zero resolution `⋯ → 0 → 0 → N` of a zero module. -/
def UpResolution.ofSubsingleton (N : GFin 𝒜) [Subsingleton N.carrier] (c : ℤ) :
    UpResolution N c where
  syz _ := N
  term _ := N
  projective _ := Module.Projective.of_free
  iso := GradedEquiv.refl _
  ses _ :=
    { f := 0
      g := LinearMap.id
      preservesGrading_f := fun _ _ _ => by
        simp only [LinearMap.zero_apply]
        exact zero_mem _
      preservesGrading_g := fun _ _ hx => hx
      injective := fun _ _ _ => Subsingleton.elim _ _
      surjective := surjective_id
      exact := fun y => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩ }
  vanish _ j _ := by
    rw [eq_bot_iff]
    intro x _
    rw [Submodule.mem_bot]
    exact Subsingleton.elim _ _

/-- `L` is a graded subquotient of `N`: a graded quotient of a graded submodule. -/
def IsSubquotient (L N : GFin 𝒜) : Prop :=
  ∃ (X : GFin 𝒜) (f : X.carrier →ₗ[A] N.carrier) (g : X.carrier →ₗ[A] L.carrier),
    PreservesGrading X.grading N.grading f ∧ Injective f ∧
      PreservesGrading X.grading L.grading g ∧ Surjective g

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem IsSubquotient.trans_injective {L K N : GFin 𝒜} (h : IsSubquotient L K)
    {f : K.carrier →ₗ[A] N.carrier} (hf : PreservesGrading K.grading N.grading f)
    (hinj : Injective f) : IsSubquotient L N := by
  obtain ⟨X, f', g, hf', hinj', hg, hs⟩ := h
  exact ⟨X, f ∘ₗ f', g, fun _ _ hx => hf (hf' hx), hinj.comp hinj', hg, hs⟩

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem IsSubquotient.of_surjective {L N : GFin 𝒜} {g : N.carrier →ₗ[A] L.carrier}
    (hg : PreservesGrading N.grading L.grading g) (hs : Surjective g) : IsSubquotient L N :=
  ⟨N, LinearMap.id, g, fun _ _ hx => hx, injective_id, hg, hs⟩

omit [Module.Finite k A] in
/-- **Resolutions from simple subquotients.** If every graded simple subquotient of `N` has a
graded projective resolution in `C↑`, so does `N` (Webster, arXiv:1309.3796v3, proof of
Theorem 5.28: attaching resolutions of the composition factors). -/
theorem exists_upResolution_of_isSubquotient (N : GFin 𝒜)
    (h : ∀ L : GFin 𝒜, IsGradedSimple 𝒜 L.grading → IsSubquotient L N →
      ∃ c, Nonempty (UpResolution L c)) :
    ∃ c, Nonempty (UpResolution N c) := by
  induction hN : finrank k N.carrier using Nat.strong_induction_on generalizing N with
  | _ n ih =>
    by_cases hnt : Nontrivial N.carrier
    · have : Module.Finite A N.carrier := Module.Finite.of_restrictScalars_finite k A _
      obtain ⟨p, hp, hptop, hmax⟩ := exists_isHomogeneous_maximal (A := A) N.grading
      let := quotDecompositionA N.grading p hp
      let Lfin : GFin 𝒜 :=
        { carrier := N.carrier ⧸ p
          grading := quotGradingA N.grading p
          finiteDimensional := Module.Finite.of_surjective (p.mkQ.restrictScalars k)
            p.mkQ_surjective }
      have hmk : PreservesGrading N.grading Lfin.grading p.mkQ :=
        preservesGrading_mkQ N.grading p
      have hker : LinearMap.ker p.mkQ = p := Submodule.ker_mkQ p
      let K := ker (M := N) (N := Lfin) p.mkQ hmk
      have hKlt : finrank k K.carrier < n := by
        rw [← hN]
        have hlt : (LinearMap.ker p.mkQ).restrictScalars k < ⊤ := by
          rw [lt_top_iff_ne_top]
          intro h'
          refine hptop ?_
          rw [eq_top_iff, ← hker]
          intro x _
          have : x ∈ (LinearMap.ker p.mkQ).restrictScalars k := h' ▸ Submodule.mem_top
          exact this
        exact Submodule.finrank_lt hlt.ne
      obtain ⟨cK, ⟨RK⟩⟩ := ih _ hKlt K (fun L hL hLK =>
        h L hL (hLK.trans_injective (f := (LinearMap.ker p.mkQ).subtype) (fun _ _ hx => hx)
          Subtype.val_injective)) rfl
      have hLs : IsGradedSimple 𝒜 Lfin.grading := isGradedSimple_quot 𝒜 N.grading p hp hptop hmax
      obtain ⟨cL, ⟨RL⟩⟩ := h Lfin hLs (IsSubquotient.of_surjective hmk p.mkQ_surjective)
      exact ⟨max cK cL, ⟨UpResolution.horseshoe (kerShortExact _ hmk p.mkQ_surjective)
        (RK.mono (le_max_left _ _)) (RL.mono (le_max_right _ _))⟩⟩
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact ⟨0, ⟨UpResolution.ofSubsingleton N 0⟩⟩

end GFin

end Categorification.Graded
