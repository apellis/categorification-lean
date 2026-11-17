/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CornerSimple

/-!
# Descent of simple tops to a graded layer quotient

In the rank count of Webster, arXiv:1309.3796v2, proof of Theorem 4.38, a
simple top annihilated by the smaller-suffix ideal descends, with its
grading, to a simple top of the layer quotient.
-/

noncomputable section
namespace Categorification.Stendhal
open Categorification.Graded GProj

variable {k A C : Type*} [Field k] [Ring A] [Ring C] [Algebra k A] [Algebra k C]
  {𝒜 : ℤ → Submodule k A} {𝒞 : ℤ → Submodule k C}
  [GradedAlgebra 𝒜] [GradedAlgebra 𝒞] [HasGdim 𝒜] [HasGdim 𝒞]
  (q : A →ₐ[k] C)

/-- The two simple tops agree under the quotient action. -/
def RestrictsToTop (s : IndecClass 𝒜) (t : IndecClass 𝒞) : Prop :=
  ∃ f : s.top ≃ₗ[k] t.top, ∀ a x, f (a • x) = q a • f x

omit [GradedAlgebra 𝒞] [HasGdim 𝒞] in
/-- Restriction of the same quotient simple identifies the projectives up to shift. -/
theorem RestrictsToTop.inj [Module.Finite k A] {s t : IndecClass 𝒜} {c : IndecClass 𝒞}
    (hs : RestrictsToTop q s c) (ht : RestrictsToTop q t c) : s=t := by
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := ht
  let := (IndecClass.isGradedSimple_top s).nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0 : s.top)
  let w := g.symm (f v)
  have hn : w≠0 := g.symm.map_ne_zero_iff.mpr (f.map_ne_zero_iff.mpr hv)
  apply indecClass_eq_of_corner_annihilator (e := 1) hv hn (one_smul _ _) (one_smul _ _)
  intro a ha
  apply g.injective
  rw [hg, map_zero, show g w=f v from g.apply_symm_apply _, ← hf, ha, map_zero]

omit [HasGdim 𝒜] in
/-- For a quotient action with a surviving idempotent, descent preserves the
simple top and gives a nonzero vector fixed by that idempotent. -/
theorem exists_restrictsToTop [Module.Finite k A] (s : IndecClass 𝒜)
    (σ : C →ₐ[k] Module.End k s.top)
    (hσ : σ.comp q = Algebra.lsmul k k s.top)
    (hlift : ∀ d (c : C), c ∈ 𝒞 d → ∃ a ∈ 𝒜 d, q a = c)
    (e : C) (he : IsIdempotentElem e) (hne : σ e ≠ 0) :
    ∃ c : IndecClass 𝒞, RestrictsToTop q s c ∧ ∃ w : c.top, w≠0 ∧ e • w=w := by
  let M := s.top
  let := Module.Finite.trans (R := k) (A := A) (M := s.top)
  let := (IndecClass.isGradedSimple_top s).isSimpleModule
  let : Module C M := Module.compHom M σ.toRingHom
  let : IsScalarTower k C M := ⟨fun r a x => by
    change σ (r • a) x = r • σ a x
    rw [map_smul]
    rfl⟩
  have hact (a : A) (x : M) : q a • x = a • x :=
    congrArg (fun f : A →ₐ[k] Module.End k M => f a x) hσ
  let : IsSimpleModule C M := isSimpleModule_iff_toSpanSingleton_surjective.mpr
    ⟨IsSimpleModule.nontrivial A M, by
      intro x hx y
      obtain ⟨a,ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hx y
      exact ⟨q a, (hact a x).trans ha⟩⟩
  let : SetLike.GradedSMul 𝒞 s.top.grading := ⟨fun i _ c x hc hx => by
    obtain ⟨a,ha,rfl⟩ := hlift i c hc
    rw [hact]
    exact SetLike.GradedSMul.smul_mem (A := 𝒜) (B := s.top.grading) ha hx⟩
  let := (IndecClass.isGradedSimple_top s).nontrivial
  have hs : IsGradedSimple 𝒞 s.top.grading :=
    ⟨inferInstance, fun p _ => IsSimpleOrder.eq_bot_or_eq_top p⟩
  obtain ⟨c,d,⟨f⟩⟩ := IndecClass.exists_gradedEquiv_top_shift hs
  let F := f.toLinearEquiv
  have hn : ∃ v : M, σ e v ≠ 0 := by
    by_contra! hz
    exact hne (LinearMap.ext hz)
  obtain ⟨v,hv⟩ := hn
  refine ⟨c, ⟨F.restrictScalars k, fun a x => ?_⟩, F (e • v), F.map_ne_zero_iff.mpr hv, ?_⟩
  · exact (congrArg F (hact a x).symm).trans (F.map_smul _ _)
  · rw [← F.map_smul, ← mul_smul, he.eq]

end Categorification.Stendhal
