/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CrossingRescale
import Categorification.WeightedKLR.RedStrands.DownwardCornerMap

/-!
# Rescaling black crossings in Webster's `T^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.2, Definitions 4.5–4.7. Let `s` be units with `s a a = 1` and
`Q a b = s a b * s b a * Q' a b` for `a ≠ b`. Rescaling each black–black crossing
`ψ_j e(i)` by `s(i_j, i_{j+1})` and fixing all other generators is an isomorphism
`T^λ(Q) ≅ T^λ(Q')`. This changes the normalization of the downward crossings in the
comparison of Lemma 4.28 (v3 Lemma 4.29) from the parameters of Webster's (2.5e) to the
Cautis–Lauda dual parameters (Cautis–Lauda, arXiv:1111.1431v3, §2.2).
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLR.KLRAlgebra MvPolynomial
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q Q' : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- Extend crossing scalars on black labels by `1` on every crossing that involves a red
strand. -/
def stendhalScale (s : I → I → kˣ) : I ⊕ Fin ℓ → I ⊕ Fin ℓ → kˣ
  | .inl a, .inl b => s a b
  | _, _ => 1

omit [DecidableEq I] in
theorem stendhalScale_self {s : I → I → kˣ} (hs : ∀ a, s a a = 1) :
    ∀ a : I ⊕ Fin ℓ, stendhalScale s a a = 1
  | .inl a => hs a
  | .inr _ => rfl

omit [DecidableEq I] in
theorem affineCoverQ_rescale {s : I → I → kˣ}
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    ∀ a b : I ⊕ Fin ℓ, a ≠ b → affineCoverQ Q Λ a b =
      C ((stendhalScale s a b * stendhalScale s b a : kˣ) : k) * affineCoverQ Q' Λ a b
  | .inl a, .inl b, h => hQ a b fun hab => h (hab ▸ rfl)
  | .inl _, .inr _, _ => by simp [stendhalScale, affineCoverQ]
  | .inr _, .inl _, _ => by simp [stendhalScale, affineCoverQ]
  | .inr _, .inr _, _ => by simp [stendhalScale, affineCoverQ]

omit [DecidableEq I] in
theorem stendhalScale_inv (s : I → I → kˣ) :
    stendhalScale (ℓ := ℓ) s⁻¹ = (stendhalScale s)⁻¹ := by
  funext a b
  cases a <;> cases b <;> simp [stendhalScale]

variable (Λ ν) in
/-- The rescaling of black crossings, as a map of affine covers followed by the projection
to `T^λ(Q')`. -/
def affineRescale (s : I → I → kˣ) (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν) →ₐ[k] TensorProductAlgebra k Q' Λ ν :=
  (affineTensorProjection (Q := Q') Λ ν).comp
    (rescaleHom (stendhalScale s) (stendhalScale_self hs) (affineCoverQ_rescale hQ))

theorem affineTensorIdeal_le_ker_affineRescale (s : I → I → kˣ) (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    affineTensorIdeal Q Λ ν ≤ TwoSidedIdeal.ker (affineRescale Λ ν s hs hQ).toRingHom := by
  refine TwoSidedIdeal.span_le.mpr ?_
  rintro z (⟨t, a, ha, rfl⟩ | ⟨t, ht, rfl⟩)
  · have hmem : (x a * e t : KLRAlgebra k (affineCoverQ Q' Λ) (stendhalWeight ℓ ν)) ∈
        TwoSidedIdeal.ker (affineTensorProjection (Q := Q') Λ ν).toRingHom := by
      rw [ker_affineTensorProjection]
      exact TwoSidedIdeal.subset_span (Or.inl ⟨t, a, ha, rfl⟩)
    rw [TwoSidedIdeal.mem_ker] at hmem
    show _ ∈ TwoSidedIdeal.ker _
    rw [TwoSidedIdeal.mem_ker]
    simpa [affineRescale] using hmem
  · have hmem : (e t : KLRAlgebra k (affineCoverQ Q' Λ) (stendhalWeight ℓ ν)) ∈
        TwoSidedIdeal.ker (affineTensorProjection (Q := Q') Λ ν).toRingHom := by
      rw [ker_affineTensorProjection]
      exact TwoSidedIdeal.subset_span (Or.inr ⟨t, ht, rfl⟩)
    rw [TwoSidedIdeal.mem_ker] at hmem
    show _ ∈ TwoSidedIdeal.ker _
    rw [TwoSidedIdeal.mem_ker]
    simpa [affineRescale] using hmem

variable (Λ ν) in
/-- The rescaling homomorphism `T^λ(Q) → T^λ(Q')`. -/
def tensorRescaleHom (s : I → I → kˣ) (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    TensorProductAlgebra k Q Λ ν →ₐ[k] TensorProductAlgebra k Q' Λ ν :=
  affineTensorLift (affineRescale Λ ν s hs hQ) (affineTensorIdeal_le_ker_affineRescale s hs hQ)

theorem tensorRescaleHom_comp_projection (s : I → I → kˣ) (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    (tensorRescaleHom Λ ν s hs hQ).comp (affineTensorProjection (Q := Q) Λ ν) =
      (affineTensorProjection (Q := Q') Λ ν).comp
        (rescaleHom (stendhalScale s) (stendhalScale_self hs) (affineCoverQ_rescale hQ)) :=
  affineTensorLift_comp _ _

theorem tensorRescaleHom_comp {s t : I → I → kˣ} (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) (ht : ∀ a, t a a = 1)
    (hQ' : ∀ a b, a ≠ b → Q' a b = C ((t a b * t b a : kˣ) : k) * Q a b)
    (hts : ∀ a b, t a b * s a b = 1) :
    (tensorRescaleHom Λ ν t ht hQ').comp (tensorRescaleHom Λ ν s hs hQ) =
      AlgHom.id k (TensorProductAlgebra k Q Λ ν) := by
  have hst : ∀ a b : I ⊕ Fin ℓ, stendhalScale t a b * stendhalScale s a b = 1 := by
    intro a b
    cases a <;> cases b <;> simp [stendhalScale, hts]
  apply AlgHom.ext
  intro z
  obtain ⟨w, rfl⟩ := affineTensorProjection_surjective (Q := Q) Λ ν z
  have h1 := DFunLike.congr_fun (tensorRescaleHom_comp_projection s hs hQ) w
  have h2 := DFunLike.congr_fun (tensorRescaleHom_comp_projection t ht hQ')
    (rescaleHom (stendhalScale s) (stendhalScale_self hs) (affineCoverQ_rescale hQ) w)
  have h3 := DFunLike.congr_fun (rescaleHom_comp (stendhalScale_self hs) (affineCoverQ_rescale hQ)
    (stendhalScale_self ht) (affineCoverQ_rescale hQ') hst) w
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3]

variable (Λ ν) in
/-- **Rescaling black crossings** gives an isomorphism `T^λ(Q) ≅ T^λ(Q')` whenever
`Q a b = s a b * s b a * Q' a b` for `a ≠ b` (Webster, arXiv:1309.3796v2, Definitions
4.5–4.7). It fixes idempotents and dots and multiplies `ψ_j e(i)` by `s(i_j, i_{j+1})` when
both strands are black. -/
def tensorRescale {s : I → I → kˣ} (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b) :
    TensorProductAlgebra k Q Λ ν ≃ₐ[k] TensorProductAlgebra k Q' Λ ν :=
  AlgEquiv.ofAlgHom (tensorRescaleHom Λ ν s hs hQ)
    (tensorRescaleHom Λ ν s⁻¹ (inv_self_eq_one hs) (symm_hQ hQ))
    (tensorRescaleHom_comp _ _ hs hQ fun a b => by simp only [Pi.inv_apply]; exact mul_inv_cancel _)
    (tensorRescaleHom_comp hs hQ _ _ fun a b => by simp only [Pi.inv_apply]; exact inv_mul_cancel _)

section tensorRescale

variable {s : I → I → kˣ} (hs : ∀ a, s a a = 1)
  (hQ : ∀ a b, a ≠ b → Q a b = C ((s a b * s b a : kˣ) : k) * Q' a b)

theorem tensorRescale_projection (z : KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν)) :
    tensorRescale Λ ν hs hQ (affineTensorProjection (Q := Q) Λ ν z) =
      affineTensorProjection (Q := Q') Λ ν
        (rescaleHom (stendhalScale s) (stendhalScale_self hs) (affineCoverQ_rescale hQ) z) :=
  DFunLike.congr_fun (tensorRescaleHom_comp_projection s hs hQ) z

/-- The rescaling fixes the idempotents of `T^λ`. -/
@[simp] theorem tensorRescale_e (t : Seq (stendhalWeight ℓ ν)) :
    tensorRescale Λ ν hs hQ (affineTensorProjection (Q := Q) Λ ν (e t)) =
      affineTensorProjection (Q := Q') Λ ν (e t) := by
  rw [tensorRescale_projection, rescaleHom_e]

/-- The rescaling fixes the dots of `T^λ`. -/
@[simp] theorem tensorRescale_x (a : Fin (stendhalWeight ℓ ν).card) :
    tensorRescale Λ ν hs hQ (affineTensorProjection (Q := Q) Λ ν (x a)) =
      affineTensorProjection (Q := Q') Λ ν (x a) := by
  rw [tensorRescale_projection, rescaleHom_x]

end tensorRescale

end Categorification.Stendhal
