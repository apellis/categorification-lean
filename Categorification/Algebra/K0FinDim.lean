/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Ring.Idempotent

/-!
# Local idempotents under surjective ring homomorphisms (KL III §3.8.1–3.8.3)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.1
(TeX `\subsubsection{$K_0$ of finite-dimensional algebras}`): "Applying `α` to the above
decomposition results in the equation `B ∋ 1 = α(e_1) + ⋯ + α(e_k)` where each `α(e_s)` is
either `0` or a minimal idempotent in `B`", and §3.8.4 (proof of Proposition 3.36 and of
Theorem 1.1): "Homomorphism `βα` […] maps each minimal idempotent `e_r ⊗ e'_{r'} ⊗ 1` either to
`0` or to a minimal degree `0` idempotent".

For a finite-dimensional algebra (or the degree-zero part of a graded algebra with
finite-dimensional graded pieces), a primitive idempotent `e` has a *local* corner ring `eAe`
(Fitting's lemma: every element of `eAe` is nilpotent or invertible in `eAe`;
`Categorification.isNilpotent_or_isUnit_of_idempotent` is the version for the whole algebra).
We record the ring-theoretic step used by KL III, for idempotents with local corner ring
(`IsLocalIdem`), under an arbitrary surjective ring homomorphism `α : R → S`:

* `IsLocalIdem.map`: `α(e)` again has a local corner ring;
* `IsLocalIdem.eq_zero_or_eq_of_map`: every idempotent `f` of the corner `α(e) S α(e)` is `0`
  or `α(e)`, i.e. **`α(e)` is `0` or primitive**.

## Relation to KL III Propositions 3.30–3.34

* Proposition 3.30 (`K₀(A) ⊗ K₀(B) ≅ K₀(A ⊗ B)` when the simples are absolutely irreducible) is
  proved in the graded setting as `Categorification.Graded.TensorK0Hyp.extTensorEquiv`
  (`Categorification.KLR.ExtTensorK0Equiv`).
* Proposition 3.31 (`K₀(A)` free over `ℤ[q, q⁻¹]` on the indecomposable graded projectives, for
  `A` with finite-dimensional graded pieces, bounded below) is
  `Categorification.Graded.K0.indecBasis` / `K0.free`
  (`Categorification.Algebra.Graded.KrullSchmidt`).
* Propositions 3.32 (virtually nilpotent ideals induce isomorphisms on `K₀`), 3.33 (surjections
  of finite-dimensional graded algebras induce surjections on `K₀`) and 3.34 (idempotented
  version of 3.31) are not formalized: the repository has no base-change map
  `K₀(A) → K₀(B)` along graded algebra homomorphisms, nor idempotent lifting modulo graded
  ideals. The idempotent-level input of 3.33 is `IsLocalIdem.eq_zero_or_eq_of_map` below.
-/

namespace Categorification

variable {R S : Type*} [Ring R] [Ring S]

/-- An idempotent `e` with *local corner ring*: every element `y = e y e` is nilpotent or
invertible in the corner `e R e` (whose unit is `e`). For a nonzero idempotent this implies that
`e` is primitive; in a finite-dimensional algebra the converse holds (Fitting's lemma). -/
def IsLocalIdem (e : R) : Prop :=
  ∀ y : R, e * y * e = y → IsNilpotent y ∨ ∃ z : R, e * z * e = z ∧ y * z = e ∧ z * y = e

namespace IsLocalIdem

variable {e : R}

/-- Only `0` and `e` are idempotents of the corner of a local idempotent. -/
theorem eq_zero_or_eq (he : IsIdempotentElem e) (hl : IsLocalIdem e) {f : R}
    (hf : IsIdempotentElem f) (hfe : e * f * e = f) : f = 0 ∨ f = e := by
  rcases hl f hfe with hn | ⟨z, -, hz, -⟩
  · exact Or.inl (hf.eq_zero_of_isNilpotent hn)
  · right
    have h1 : f * e = f := by rw [← hfe, mul_assoc, he.eq]
    calc f = f * e := h1.symm
      _ = f * (f * z) := by rw [hz]
      _ = f * z := by rw [← mul_assoc, hf.eq]
      _ = e := hz

/-- **Images of local idempotents under surjections are local.** -/
theorem map (he : IsIdempotentElem e) (hl : IsLocalIdem e) (α : R →+* S)
    (hα : Function.Surjective α) : IsLocalIdem (α e) := by
  intro y' hy'
  obtain ⟨x, rfl⟩ := hα y'
  have hy : e * (e * x * e) * e = e * x * e := by
    rw [← mul_assoc, ← mul_assoc, he.eq, mul_assoc, he.eq]
  have hαy : α (e * x * e) = α x := by rw [map_mul, map_mul]; exact hy'
  rcases hl (e * x * e) hy with hn | ⟨z, hz, hyz, hzy⟩
  · exact Or.inl (by rw [← hαy]; exact hn.map α)
  · refine Or.inr ⟨α z, by rw [← map_mul, ← map_mul, hz], ?_, ?_⟩
    · rw [← hαy, ← map_mul, hyz]
    · rw [← hαy, ← map_mul, hzy]

/-- **KL III §3.8.1 / Proposition 3.36, idempotent form**: under a surjective ring homomorphism
`α`, the image of an idempotent `e` with local corner ring is `0` or primitive: the only
idempotents `f` with `α(e) f α(e) = f` are `0` and `α(e)`. -/
theorem eq_zero_or_eq_of_map (he : IsIdempotentElem e) (hl : IsLocalIdem e) (α : R →+* S)
    (hα : Function.Surjective α) {f : S} (hf : IsIdempotentElem f)
    (hfe : α e * f * α e = f) : f = 0 ∨ f = α e :=
  (hl.map he α hα).eq_zero_or_eq (he.map α) hf hfe

end IsLocalIdem

end Categorification
