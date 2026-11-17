/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExtTensorK0Equiv

/-!
# Homogeneous idempotents under graded quotient maps

The lifting argument in finite degree zero applies both to the ordinary
cyclotomic quotient and to the ordered red diagram quotient.
-/

namespace Categorification.Graded

/-- An idempotent in the image of a finite-dimensional algebra lifts to an idempotent.
The Fitting decomposition is taken for right multiplication by a preimage. -/
theorem exists_idempotent_of_idempotent_image {k E B : Type*} [Field k] [Ring E] [Algebra k E]
    [FiniteDimensional k E] [Ring B] (π : E →+* B) (x : E) (he : IsIdempotentElem (π x)) :
    ∃ p : E, IsIdempotentElem p ∧ π p = π x := by
  let : IsNoetherianRing E := isNoetherian_of_tower k inferInstance
  let : IsArtinianRing E := isArtinian_of_tower k inferInstance
  obtain ⟨n, hn, hn1⟩ := ((LinearMap.mulRight E x).eventually_isCompl_ker_pow_range_pow.and
    (Filter.eventually_ge_atTop 1)).exists
  rw [LinearMap.pow_mulRight] at hn
  let K := LinearMap.ker (LinearMap.mulRight E (x ^ n))
  let J := LinearMap.range (LinearMap.mulRight E (x ^ n))
  have h1 : (1 : E) ∈ K ⊔ J := by rw [hn.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hp : IsIdempotentElem b := by
    have hj : b * b - b ∈ J := J.sub_mem (J.smul_mem b hb) hb
    have hk : b * b - b ∈ K := by
      have hh : b * a + b * b = b := by rw [← mul_add, hab, mul_one]
      have heq : b * b - b = -(b * a) := by rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, add_comm (b * b), hh, sub_self]
      exact heq ▸ K.neg_mem (K.smul_mem b ha)
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hn.disjoint) _ hk hj)
  refine ⟨b, hp, ?_⟩
  have hx : π (x ^ n) = π x := (map_pow π x n).trans (he.pow_eq (by omega))
  have ha0 : π a * π x = 0 := by
    have ha' : a * x ^ n = 0 := ha
    rw [← hx, ← map_mul, ha', map_zero]
  have hb1 : π b * π x = π b := by
    obtain ⟨z, hz⟩ := hb
    change z * x ^ n = b at hz
    rw [← hz, map_mul, hx, mul_assoc, he.eq]
  calc π b = (π a + π b) * π x := by rw [add_mul, ha0, hb1, zero_add]
       _ = π x := by rw [← map_add, hab, map_one, one_mul]

variable {k A B : Type*} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (𝒜 : ℤ → Submodule k A) (ℬ : ℤ → Submodule k B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (π : A →ₐ[k] B) (hπ : PreservesGrading 𝒜 ℬ π.toLinearMap) (hs : Function.Surjective π)

include hπ hs in
open DirectSum in
theorem grade_eq_map_of_surjective (n : ℤ) : ℬ n = (𝒜 n).map π.toLinearMap := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨decompose 𝒜 x n, (decompose 𝒜 x n).property,
      (decompose_map hπ x n).symm.trans (decompose_of_mem_same _ hy)⟩
  · exact Submodule.map_le_iff_le_comap.mpr fun _ hx => hπ hx

include hπ hs in
theorem hasGdim_of_surjective [HasGdim 𝒜] : HasGdim ℬ where
  finiteDimensional n := by
    rw [grade_eq_map_of_surjective 𝒜 ℬ π hπ hs n]
    infer_instance
  bddBelow := by
    obtain ⟨L, hL⟩ := HasGdim.bddBelow (ℳ := 𝒜)
    refine ⟨L, fun n hn => hL ?_⟩
    intro h
    apply hn
    rw [grade_eq_map_of_surjective 𝒜 ℬ π hπ hs n, h, Submodule.map_bot]

include hs hπ in
/-- A homogeneous idempotent lifts in degree zero whenever that degree of the
source is finite dimensional and the graded algebra homomorphism is onto. -/
theorem exists_graded_idempotent_preimage [FiniteDimensional k (𝒜 0)]
    {e : B} (he : IsIdempotentElem e) (he0 : e ∈ ℬ 0) :
    ∃ p : A, IsIdempotentElem p ∧ p ∈ 𝒜 0 ∧ π p = e := by
  rw [grade_eq_map_of_surjective 𝒜 ℬ π hπ hs 0] at he0
  obtain ⟨x, hx, rfl⟩ := he0
  let φ : 𝒜 0 →+* B :=
    { toFun := fun z => π z.val
      map_one' := map_one π
      map_zero' := map_zero π
      map_add' := fun a b => map_add π a.val b.val
      map_mul' := fun a b => map_mul π a.val b.val }
  obtain ⟨p, hp, himg⟩ := exists_idempotent_of_idempotent_image (k := k) φ (⟨x, hx⟩ : 𝒜 0) he
  exact ⟨p.val, congrArg Subtype.val hp.eq, p.property, himg⟩

end Categorification.Graded
