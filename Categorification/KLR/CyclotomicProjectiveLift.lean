/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExtTensorK0Equiv
import Categorification.KLR.CyclotomicGrading

/-!
# Lifting graded cyclotomic projectives to affine idempotents

Webster, arXiv:1309.3796v2, proof of Proposition 3.21. For the generation of
cyclotomic projective classes, every indecomposable projective is a shift of
the image of a principal affine projective. Its degree-zero idempotent lifts by
the Fitting decomposition in the finite-dimensional degree-zero affine algebra.
-/

namespace Categorification.KLR.CycKLR

open Categorification.Graded

private theorem lift_idempotent {k E B : Type*} [Field k] [Ring E] [Algebra k E]
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

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (ν : Multiset I)

local notation "R" => KLRAlgebra k Q ν
local notation "π" => mk k Q (fun i => Polynomial.X ^ Λ i) ν

/-- A degree-zero idempotent of the monomial cyclotomic quotient lifts to a
degree-zero idempotent of the affine algebra. Symmetry of the parameters and
positive dot degrees give finite dimensionality of the affine degree-zero part. -/
theorem exists_idempotent_preimage (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i)
    {e : CycKLR k Q (fun i => Polynomial.X ^ Λ i) ν} (he : IsIdempotentElem e)
    (he0 : e ∈ grade G Λ ν 0) :
    ∃ p : R, IsIdempotentElem p ∧ p ∈ G.grade ν 0 ∧ π p = e := by
  obtain ⟨x, hx, rfl⟩ := he0
  let E := G.grade ν 0
  let := (G.hasGdim_grade' (ν := ν) hsym hX).finiteDimensional 0
  let φ : E →+* CycKLR k Q (fun i => Polynomial.X ^ Λ i) ν :=
    { toFun := fun z => π z.val
      map_one' := map_one π
      map_zero' := map_zero π
      map_add' := fun a b => map_add π a.val b.val
      map_mul' := fun a b => map_mul π a.val b.val }
  obtain ⟨p, hp, himg⟩ := lift_idempotent (k := k) φ (⟨x, hx⟩ : E) he
  exact ⟨p.val, congrArg Subtype.val hp.eq, p.property, himg⟩

/-- Every indecomposable graded projective in a cyclotomic block comes from
a degree-zero affine idempotent, up to a grading shift. -/
theorem exists_iso_of_affineIdempotent (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i)
    [HasGdim (grade G Λ ν)] (P : GProj (grade G Λ ν)) (hP : P.IsIndec _) :
    ∃ (p : R) (hp : IsIdempotentElem p) (hp0 : p ∈ G.grade ν 0) (j : ℤ),
      Nonempty (P.Iso ((GProj.ofIdempotent (π p) (hp.map π)
        (Graded.mem_map_of_mem _ _ hp0)).shift j)) := by
  obtain ⟨e, he, he0, j, h⟩ := hP.exists_iso_ofIdempotent
  obtain ⟨p, hp, hp0, rfl⟩ := exists_idempotent_preimage G Λ ν hsym hX he he0
  exact ⟨p, hp, hp0, j, h⟩

end Categorification.KLR.CycKLR
