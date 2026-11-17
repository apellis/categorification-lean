/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.KrullSchmidt

/-!
# Detecting projective classes on a corner

In the filtration by the number of black strands following the last red strand
(Webster, arXiv:1309.3796v2, proof of Lemma 4.37), one compares simple tops
on a boundary corner. A cyclic vector fixed by the boundary idempotent is
determined up to simple-module isomorphism by its annihilator in that corner.
-/

namespace Categorification.Stendhal

open Categorification.Graded GProj

/-- If the corner annihilator of a cyclic vector in one simple module kills
a nonzero fixed vector in another, the simple modules are isomorphic. -/
theorem simpleEquiv_of_corner_annihilator {A M N : Type*} [Ring A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [IsSimpleModule A M] [IsSimpleModule A N] {e : A} {v : M} {w : N}
    (hv : v ≠ 0) (hw : w ≠ 0) (hev : e • v = v) (hew : e • w = w)
    (h : ∀ a : A, (e * a * e) • v = 0 → (e * a * e) • w = 0) :
    Nonempty (M ≃ₗ[A] N) := by
  let f := LinearMap.toSpanSingleton A M v
  let g := LinearMap.toSpanSingleton A N w
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro a ha
    change a • v = 0 at ha
    change a • w = 0
    by_contra haw
    obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective A haw w
    change b • (a • w) = w at hb
    have hz := h (b * a) (by simp only [mul_smul, hev, ha, smul_zero])
    rw [mul_smul, hew, mul_smul, mul_smul, hb, hew] at hz
    exact hw hz
  have hf := IsSimpleModule.toSpanSingleton_surjective A hv
  let F := ((LinearMap.ker f).liftQ g hker).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hF (a : A) : F (f a) = g a := by
    have ht : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, ht, Submodule.liftQ_apply]
  have hsurj : Function.Surjective F := fun n => by
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hw n
    exact ⟨f a, (hF a).trans ha⟩
  have hne : F ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := hsurj w
    exact hw (by simpa [hzero] using hx.symm)
  exact ⟨LinearEquiv.ofBijective F ⟨(LinearMap.injective_or_eq_zero F).resolve_right hne, hsurj⟩⟩

/-- Two indecomposable graded projectives represent the same shift class if their
simple tops have nonzero fixed vectors with nested corner annihilators. -/
theorem indecClass_eq_of_corner_annihilator {k A : Type*} [Field k] [Ring A]
    [Algebra k A] [Module.Finite k A] {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜]
    {b c : IndecClass 𝒜} {e : A} {v : b.top} {w : c.top}
    (hv : v ≠ 0) (hw : w ≠ 0) (hev : e • v = v) (hew : e • w = w)
    (h : ∀ a : A, (e * a * e) • v = 0 → (e * a * e) • w = 0) : b = c := by
  have := Module.Finite.trans (R := k) (A := A) (M := b.top)
  have := Module.Finite.trans (R := k) (A := A) (M := c.top)
  have hb := IndecClass.isGradedSimple_top b
  have hc := IndecClass.isGradedSimple_top c
  let := hb.isSimpleModule
  let := hc.isSimpleModule
  obtain ⟨f⟩ := simpleEquiv_of_corner_annihilator hv hw hev hew h
  have hn : f.toLinearMap ≠ 0 := by
    intro hz
    apply hv
    apply f.injective
    simpa using LinearMap.congr_fun hz v
  obtain ⟨d, ⟨g⟩⟩ := hb.exists_gradedEquiv_shift_of_ne_zero hc hn
  exact (IndecClass.eq_of_gradedEquiv_top_shift ((GMod.shiftZeroIso b.top).trans g)).1

section Restriction

variable {k A B : Type*} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (φ : B →ₙₐ[k] A) (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The fixed vectors of the image of the unit under the boundary map. -/
def boundaryFixed := ↥(idemSubspace k M (φ 1))

instance : AddCommGroup (boundaryFixed φ M) := inferInstanceAs (AddCommGroup (idemSubspace k M (φ 1)))
instance : Module k (boundaryFixed φ M) := inferInstanceAs (Module k (idemSubspace k M (φ 1)))

instance : Module B (boundaryFixed φ M) where
  smul b x := ⟨φ b • x.1, by
    change φ 1 • (φ b • x.1) = φ b • x.1
    rw [← mul_smul, ← map_mul, one_mul]⟩
  one_smul x := Subtype.ext x.2
  mul_smul a b x := Subtype.ext (by change φ (a*b) • x.1 = _; rw [map_mul, mul_smul]; rfl)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  add_smul a b x := Subtype.ext (by change φ (a+b) • x.1 = _; rw [map_add, add_smul]; rfl)
  zero_smul x := Subtype.ext (by change φ 0 • x.1 = _; rw [map_zero, zero_smul]; rfl)

instance : IsScalarTower k B (boundaryFixed φ M) where
  smul_assoc c b x := Subtype.ext (by change φ (c • b) • x.1 = _; rw [map_smul, smul_assoc]; rfl)

/-- A simple top remains simple on any nonzero boundary which exhausts the
corner operators on its fixed vectors. The condition is imposed on the
representation, allowing diagrams from smaller layers to act by zero. -/
theorem boundaryFixed_simple [IsSimpleModule A M] [Nontrivial (boundaryFixed φ M)]
    (h : ∀ a : A, ∃ b : B, ∀ x : boundaryFixed φ M, φ b • x.1 = φ 1 • (a • x.1)) :
    IsSimpleModule B (boundaryFixed φ M) := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance, ?_⟩
  intro x hx y
  have hx' : x.1 ≠ 0 := fun hz => hx (Subtype.ext hz)
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hx' y.1
  obtain ⟨b, hb⟩ := h a
  refine ⟨b, Subtype.ext ?_⟩
  change φ b • x.1 = y.1
  rw [hb, show a • x.1 = y.1 from ha]
  exact y.2

/-- On simples detected by this boundary, restriction reflects isomorphisms.
Only the compressed action of each algebra element on the two tops is needed. -/
theorem indecClass_eq_of_boundaryEquiv [Module.Finite k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜]
    {s t : IndecClass 𝒜} [Nontrivial (boundaryFixed φ s.top)]
    (f : boundaryFixed φ s.top ≃ₗ[B] boundaryFixed φ t.top)
    (h : ∀ a : A, ∃ b : B,
      (∀ x : boundaryFixed φ s.top, φ b • x.1 = φ 1 • (a • x.1)) ∧
      (∀ y : boundaryFixed φ t.top, φ b • y.1 = φ 1 • (a • y.1))) :
    s = t := by
  obtain ⟨x, hx⟩ := exists_ne (0 : boundaryFixed φ s.top)
  have hy := f.map_ne_zero_iff.mpr hx
  apply indecClass_eq_of_corner_annihilator (v := x.1) (w := (f x).1)
    (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h)) x.2 (f x).2
  intro a ha
  obtain ⟨b, hb, hc⟩ := h a
  rw [mul_smul, show φ 1 • x.1 = x.1 from x.2, mul_smul, ← hb] at ha
  rw [mul_smul, show φ 1 • (f x).1 = (f x).1 from (f x).2, mul_smul, ← hc]
  have hz : b • x = 0 := Subtype.ext ha
  exact congrArg Subtype.val (show b • f x = 0 by rw [← map_smul, hz, map_zero])

variable {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
    {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [HasGdim ℬ]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- The grading on a boundary is inherited from the parent module. -/
def boundaryGrading : ℤ → Submodule k (boundaryFixed φ M) := idem ℳ (φ 1)

omit [GradedAlgebra 𝒜] in
/-- A nonzero boundary restriction of a graded simple has the shift class of
a simple top of the boundary algebra. -/
theorem exists_boundary_top [IsSimpleModule A M] [Nontrivial (boundaryFixed φ M)]
    (hφ : ∀ d b, b ∈ ℬ d → φ b ∈ 𝒜 d)
    (h : ∀ a : A, ∃ b : B, ∀ x : boundaryFixed φ M, φ b • x.1 = φ 1 • (a • x.1)) :
    ∃ (c : IndecClass ℬ) (d : ℤ),
      Nonempty (boundaryGrading φ M ℳ ≃ᵍ[B] Graded.shift c.top.grading d) := by
  have := boundaryFixed_simple φ M h
  have he := hφ 0 1 SetLike.GradedOne.one_mem
  let : DirectSum.Decomposition (boundaryGrading φ M ℳ) := idemDecomposition ℳ he
  let : SetLike.GradedSMul ℬ (boundaryGrading φ M ℳ) :=
    ⟨fun _ _ b x hb hx => SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) (hφ _ _ hb) hx⟩
  have hs : IsGradedSimple ℬ (boundaryGrading φ M ℳ) :=
    ⟨inferInstance, fun p _ => IsSimpleOrder.eq_bot_or_eq_top p⟩
  exact IndecClass.exists_gradedEquiv_top_shift hs

/-- The shift classes of indecomposable projectives detected on a boundary
inject into the shift classes of the algebra surjecting onto that corner. -/
noncomputable def boundaryClassEmbedding [Module.Finite k A] [HasGdim 𝒜]
    (hφ : ∀ d b, b ∈ ℬ d → φ b ∈ 𝒜 d) (hc : ∀ a : A, ∃ b : B, φ b = φ 1 * a * φ 1) :
    {s : IndecClass 𝒜 // Nontrivial (boundaryFixed φ s.top)} ↪ IndecClass ℬ := by
  classical
  have cut (a : A) : ∃ b : B, ∀ {V : Type _} [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] (x : boundaryFixed φ V), φ b • x.1 = φ 1 • (a • x.1) := by
    obtain ⟨b, hb⟩ := hc a
    exact ⟨b, fun x => by rw [hb, mul_smul, show φ 1 • x.1 = x.1 from x.2, mul_smul]⟩
  have top (s : {s : IndecClass 𝒜 // Nontrivial (boundaryFixed φ s.top)}) :
      ∃ (c : IndecClass ℬ) (d : ℤ),
        Nonempty (boundaryGrading φ s.1.top s.1.top.grading ≃ᵍ[B] Graded.shift c.top.grading d) := by
    let := s.2
    have := Module.Finite.trans (R := k) (A := A) (M := s.1.top)
    let := (IndecClass.isGradedSimple_top s.1).isSimpleModule
    exact exists_boundary_top φ s.1.top s.1.top.grading hφ (fun a => ⟨_, (cut a).choose_spec⟩)
  refine ⟨fun s => (top s).choose, ?_⟩
  intro s t hst
  apply Subtype.ext
  obtain ⟨d, ⟨u⟩⟩ := (top s).choose_spec
  change (top s).choose = (top t).choose at hst
  rw [hst] at u
  obtain ⟨d', ⟨v⟩⟩ := (top t).choose_spec
  let := s.2
  exact indecClass_eq_of_boundaryEquiv φ (u.toLinearEquiv.trans v.toLinearEquiv.symm)
    (fun a => ⟨_, (cut a).choose_spec, (cut a).choose_spec⟩)

end Restriction

end Categorification.Stendhal
