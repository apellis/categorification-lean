/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CornerHead

/-!
# Projective shift classes for ungraded simple heads

In Webster, arXiv:1309.3796v2, proof of Theorem 5.8, the simple head
can first be formed on underlying modules. Over a finite-dimensional
integer-graded algebra its class then determines a projective shift class.
-/

noncomputable section
namespace Categorification.Stendhal
open Categorification.Graded GProj

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [HasGdim 𝒜]
  (S : Type*) [AddCommGroup S] [Module A S] [IsSimpleModule A S]

/-- Every ungraded simple module for a finite-dimensional integer-graded
algebra is the underlying simple top of a graded projective shift class.
Apply a graded composition series of the regular module to a cyclic quotient
onto the given simple, as needed for the head in Webster, Theorem 5.8. -/
theorem exists_indecClass_of_simple [Module.Finite k A] :
    ∃ b : IndecClass 𝒜, Nonempty (S ≃ₗ[A] b.top) := by
  have step (M : GMod 𝒜) [Module.Finite k M.carrier] (f : M.carrier →ₗ[A] S) (hf : f ≠ 0) :
      ∃ b : IndecClass 𝒜, Nonempty (S ≃ₗ[A] b.top) := by
    induction h : Module.finrank k M.carrier using Nat.strong_induction_on generalizing M with
    | _ n ih =>
      have : Nontrivial M.carrier := by
        by_contra! hM
        exact hf (Subsingleton.elim _ _)
      have := Module.Finite.of_restrictScalars_finite k A M.carrier
      obtain ⟨N,hN,hNt,hm⟩ := exists_isHomogeneous_maximal (A := A) M.grading
      by_cases hkill : f.comp N.subtype = 0
      · let g := N.liftQ f (show N ≤ LinearMap.ker f from
          fun x hx => LinearMap.congr_fun hkill ⟨x,hx⟩)
        have hg : g ≠ 0 := by
          intro hz
          apply hf
          ext x
          exact LinearMap.congr_fun hz (N.mkQ x)
        let := quotDecompositionA M.grading N hN
        let := Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
        have hS := isGradedSimple_quot 𝒜 M.grading N hN hNt hm
        let := hS.isSimpleModule
        obtain ⟨b,d,⟨e⟩⟩ := IndecClass.exists_gradedEquiv_top_shift hS
        exact ⟨b,⟨(LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hg)).symm.trans e.toLinearEquiv⟩⟩
      · let := submoduleDecomposition M.grading hN
        let M' : GMod 𝒜 := GMod.of N (Graded.submodule M.grading N)
        let : Module.Finite k M'.carrier := FiniteDimensional.of_injective (N.subtype.restrictScalars k) Subtype.val_injective
        have hn : N.restrictScalars k ≠ ⊤ := by
          intro ht
          apply hNt
          exact Submodule.eq_top_iff'.mpr fun x => show x ∈ N.restrictScalars k from ht ▸ Submodule.mem_top
        exact ih _ (h ▸ Submodule.finrank_lt hn) M' _ hkill rfl
  let := IsSimpleModule.nontrivial A S
  obtain ⟨x,hx⟩ := exists_ne (0 : S)
  let : Module.Finite k (GMod.regular 𝒜).carrier := inferInstanceAs (Module.Finite k A)
  exact step (GMod.regular 𝒜) (LinearMap.toSpanSingleton A S x) (fun hf => hx
    (by have h := LinearMap.congr_fun hf (1 : A); change (1 : A) • x = 0 at h; simpa using h))

variable [Module.Finite k A]

/-- The graded projective shift classes of a finite-dimensional algebra are finite. -/
theorem finite_indec : Finite (IndecClass 𝒜) := by
  classical
  let := fun b : IndecClass 𝒜 => (IndecClass.isGradedSimple_top b).finiteDimensional (⊥ : Submodule k A)
    (fun a ha m => by rw [(Submodule.mem_bot k).mp ha, zero_smul])
  let := fun b : IndecClass 𝒜 => (IndecClass.isGradedSimple_top b).isSimpleModule
  have z (b : IndecClass 𝒜) : ∃ x : b.top, x ≠ 0 := by
    let := (IndecClass.isGradedSimple_top b).nontrivial
    exact exists_ne 0
  choose x hx using z
  let p (b : IndecClass 𝒜) : A →ₗ[A] b.top :=
    { toFun := fun a => a • x b, map_add' := fun a c => add_smul a c _, map_smul' := fun a c => mul_smul _ _ _ }
  apply (card_le_finrank_of_isSimpleModule (k := k) (fun b : IndecClass 𝒜 => b.top.carrier) p ?_ ?_).1
  · intro b
    apply LinearMap.surjective_of_ne_zero
    intro h
    exact hx b (by simpa [p] using LinearMap.congr_fun h 1)
  · rintro b c ⟨e⟩
    have hz : e.toLinearMap ≠ 0 := by
      intro he
      exact hx b (e.injective ((LinearMap.congr_fun he _).trans e.map_zero.symm))
    obtain ⟨n,⟨g⟩⟩ := IsGradedSimple.exists_gradedEquiv_shift_of_ne_zero (IndecClass.isGradedSimple_top b)
      (IndecClass.isGradedSimple_top c) hz
    exact (IndecClass.eq_of_gradedEquiv_top_shift (a := 0) (a' := n) (by simpa only [shift_zero] using g)).1

end Categorification.Stendhal
