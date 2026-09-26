/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Idempotent
import Categorification.Algebra.Graded.IdempotentSplitting

/-!
# Classes in `K₀` under splittings of idempotents

Background for M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum
groups I*, arXiv:0803.4121v2, §2.5 (`P_î ≅ P_i^{i!}`, Proposition 2.13).

Let `(A, 𝒜)` be a `ℤ`-graded algebra and `E' = ∑_j a_j b_j` a splitting
(`Graded.IsSplitting`: `b_i a_j = δ_{ij} E_j`) with `a_j ∈ 𝒜_{d_j}`, `b_j ∈ 𝒜_{-d_j}`, where `E'`
and the `E_j` are idempotents of degree `0`. Then the elements `g_j = a_j E_j b_j` are orthogonal
idempotents with `∑_j g_j = E'`, and `g_j` is equivalent to `E_j` via `a_j E_j ∈ 𝒜_{d_j}`,
`b_j ∈ 𝒜_{-d_j}`. Hence, in `K₀(A)`,

  `[A E'] = ∑_j q^{-d_j} [A E_j]`   (`K0.of_ofIdempotent_eq_sum_of_isSplitting`).
-/

namespace Categorification.Graded

universe u v

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

namespace K0

/-- **Classes in `K₀` under a splitting**: if `E' = ∑_j a_j b_j` with `b_i a_j = δ_{ij} E_j`,
`a_j ∈ 𝒜_{d_j}`, `b_j ∈ 𝒜_{-d_j}`, and `E'`, `E_j` are idempotents of degree `0`, then
`[A E'] = ∑_j q^{-d_j} [A E_j]`. -/
theorem of_ofIdempotent_eq_sum_of_isSplitting {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E' : A} {E a b : ι → A} {dg : ι → ℤ} (h : IsSplitting E' E a b)
    (ha : ∀ j, a j ∈ 𝒜 (dg j)) (hb : ∀ j, b j ∈ 𝒜 (-dg j)) (hE' : IsIdempotentElem E')
    (hE : ∀ j, IsIdempotentElem (E j)) (hE'0 : E' ∈ 𝒜 0) (hE0 : ∀ j, E j ∈ 𝒜 0) :
    of (GProj.ofIdempotent E' hE' hE'0) =
      ∑ j, (LaurentPolynomial.T (-dg j) : LaurentPolynomial ℤ) •
        of (GProj.ofIdempotent (E j) (hE j) (hE0 j)) := by
  set a' : ι → A := fun j => a j * E j
  set g : ι → A := fun j => a' j * b j
  have hba : ∀ j, b j * a' j = E j := fun j => by
    simp only [a']; rw [← mul_assoc, h.mul_self, (hE j).eq]
  have ha' : ∀ j, a' j ∈ 𝒜 (dg j) := fun j => by
    simpa using SetLike.GradedMul.mul_mem (ha j) (hE0 j)
  have hg0 : ∀ j, g j ∈ 𝒜 0 := fun j => by
    simpa using SetLike.GradedMul.mul_mem (ha' j) (hb j)
  have hidem : ∀ j, IsIdempotentElem (g j) := fun j => by
    show a' j * b j * (a' j * b j) = a' j * b j
    rw [mul_assoc, ← mul_assoc (b j), hba]
    simp only [a']
    rw [mul_assoc (a j), ← mul_assoc (E j), (hE j).eq, mul_assoc]
  have hortho : Pairwise fun i j => g i * g j = 0 := fun i j hij => by
    show a' i * b i * (a' j * b j) = 0
    simp only [a']
    rw [mul_assoc, ← mul_assoc (b i), ← mul_assoc (b i), h.mul_ne hij, zero_mul, zero_mul,
      mul_zero]
  have horth : OrthogonalIdempotents g := ⟨hidem, hortho⟩
  have hsum : E' = ∑ j, g j := by
    simp only [g, a']
    have : ∀ j, a j * E j * b j = a j * b j * E' := fun j => by
      rw [mul_assoc, ← h.b_mul_right, ← mul_assoc]
    simp_rw [this, ← Finset.sum_mul, h.sum_eq, hE'.eq]
  rw [of_ofIdempotent_congr hsum hE' horth.isIdempotentElem_sum hE'0
    (Submodule.sum_mem _ fun j _ => hg0 j), of_ofIdempotent_sum horth hg0 Finset.univ]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact of_ofIdempotent_eq_T_smul (ha' j) (hb j) rfl (hba j) _ _ _ _

end K0

end Categorification.Graded
