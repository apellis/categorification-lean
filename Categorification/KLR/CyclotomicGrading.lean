/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicMultFree
import Categorification.KLR.GradedBasis
import Categorification.Algebra.Graded.QuotientAlgebra

/-!
# Cyclotomic gradings and dimensions of noninteracting corners

Kang–Kashiwara, arXiv:1102.4677v4, §4.1, Definition 4.1: over a base in degree
zero the undeformed cyclotomic relation on a sequence is a power of the dot
times its idempotent. These homogeneous generators give the quotient grading.

Hu–Shi, arXiv:2108.05508v5, Theorems 1.1 and 1.5: for pairwise distinct,
non-adjacent colours the corner monomials have an independent bound on the dot
power at each position. Counting the homogeneous elements of the existing
`CycKLR.cornerBasis` gives the coefficient in each degree in this case.
-/

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded Equiv TypeA

variable {I : Type*} [DecidableEq I]

section Algebra
variable {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q) (Λ : I → ℕ)
  (ν : Multiset I)

local notation "aΛ" => (fun i => Polynomial.X ^ Λ i : I → Polynomial k)

/-- The grading by images of the KLR pieces on the undeformed cyclotomic quotient
(Kang–Kashiwara, §4.1, Definition 4.1). -/
noncomputable def grade : ℤ → Submodule k (CycKLR k Q aΛ ν) :=
  Graded.map (G.grade ν) (mk k Q aΛ ν).toLinearMap

private theorem cycElt_homogeneous (i : Seq ν) :
    ∃ j, cycElt Q aΛ i ∈ G.grade ν j := by
  by_cases h : 0 < Multiset.card ν
  · rw [cycElt_of_pos _ _ _ h, map_pow, Polynomial.aeval_X]
    let p : Fin (Multiset.card ν) := ⟨0, h⟩
    have H := G.mk_mem_grade_of_homAt (G.homAt_fx_pow_mul p (G.homAt_fe i) (Λ (i.lbl p)))
    rw [map_mul, map_pow] at H
    exact ⟨_, H⟩
  · simp [cycElt, h]

/-- The cyclotomic ideal is homogeneous for all multiplicities and all Cartan types.
This construction uses the undeformed polynomials `X ^ Λ i`. -/
noncomputable instance gradedAlgebra : GradedAlgebra (grade G Λ ν) :=
  Graded.mapGradedAlgebra (G.grade ν) _ mk_surjective fun x hx n =>
    (mk_eq_zero_iff _).2 <| by
      have h := (mk_eq_zero_iff x).1 hx
      unfold cycIdeal at h ⊢
      apply Graded.decompose_mem_twoSidedSpan (G.grade ν) _ h n
      rintro _ ⟨i, rfl⟩
      exact cycElt_homogeneous G Λ ν i

end Algebra

section Corner
variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) (Λ : I → ℕ) {ν : Multiset I}
  (hnd : ν.Nodup) (hQ : ∀ i ∈ ν, ∀ j ∈ ν, i ≠ j → Q i j = 1)
  (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
  (i i' : Seq ν) (w : Perm (Fin (Multiset.card ν))) (hw : w • i' = i)

local notation "aΛ" => (fun i => Polynomial.X ^ Λ i : I → Polynomial k)

include hnd hQ hρ hw in
/-- In a corner on distinct, non-adjacent colours, the coefficient in degree `d`
counts the bounded dot exponent vectors giving total degree `d`. For the Cartan
grading the crossing contribution is zero between these colours; the bounds are
`0 ≤ c_p < Λ(i'_p)` (Hu–Shi, Theorem 1.1, this case). -/
theorem coeff_gdim_cornerGrade (d : ℤ) :
    (gdim fun n => grade G Λ ν n ⊓ corner k Q aΛ i i').coeff d =
      (Nat.card {c : DotExp aΛ i' | G.stdDeg ρ (i', w, dotExp c) = d} : ℤ) := by
  let deg := fun c : DotExp aΛ i' => G.stdDeg ρ (i', w, dotExp c)
  have ha : ∀ j, (aΛ j).Monic := fun j => Polynomial.monic_X_pow _
  let b := cornerElt (Q := Q) aΛ ρ i' w
  have hdeg : ∀ c, b c ∈ grade G Λ ν (deg c) := fun c =>
    Graded.mem_map_of_mem _ _ (G.stdElt_mem_grade ρ (i', w, dotExp c))
  have h := coeff_gdim_inf_span (grade G Λ ν) deg
    (linearIndependent_cornerElt hnd hQ ha ρ hρ i' w) hdeg Set.univ
    (fun _ => Set.toFinite _) ((Set.finite_range deg).subset (Set.image_subset_range ..)).bddBelow d
  simpa [deg, span_cornerElt hnd hQ ha ρ hρ i i' w hw] using h

end Corner

end Categorification.KLR.CycKLR
