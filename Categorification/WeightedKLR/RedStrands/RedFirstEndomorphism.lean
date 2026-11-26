/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedShuffleFactor
import Categorification.WeightedKLR.RedStrands.RedFirstDominantDimension
import Categorification.Algebra.CornerEndomorphism

set_option backward.isDefEq.respectTransparency false

/-!
# `T^λ` as an endomorphism algebra over the red-first corner

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.30. Let `B = e⁰ T^λ e⁰` be the red-first corner (`≅ R^{∑ λ_r}`, Proposition 5.28)
and, for a red-ordered loading `s`, let `y_s = θ̇_s θ_s ∈ B`, where `θ_s` is the red/black shuffle
from the red-first loading `t_s` to `s` and `θ̇_s` its horizontal reflection. Then `T^λ` is the
algebra of `B`-linear endomorphisms of `⊕_s y_s B`.

The proof follows Webster: `e(s) T^λ e⁰ = θ_s B` (`exists_eq_redShuffle_mul`, Proposition 4.16),
left multiplication by `θ̇_s` is injective on `e(s) T^λ` (Lemma 5.23), so `e(s) T^λ e⁰ ≅ y_s B`,
and `T^λ` is the endomorphism algebra of `T^λ e⁰` (Corollary 5.29).

## Main results

* `mul_redShuffle_injective`: right multiplication by `θ_s` is injective on `T^λ e(s)`.
* `redShuffleDual_mul_injective`: left multiplication by `θ̇_s` is injective on `e(s) T^λ`.
* `redFirstEndEquiv`: **Proposition 5.30** (v3: Proposition 5.33), `T^λ ≅ End_B(⊕_s y_s B)`.
-/

noncomputable section

namespace Categorification.Stendhal

open Equiv KLR TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν

section Shuffle

variable [DecidableEq I] (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

theorem redLoadingIdem_mul_redShuffle (s : Seq μ) (hs : IsRedOrdered s) :
    redLoadingIdem Q Λ ν s hs * redShuffle Q Λ s hs = redShuffle Q Λ s hs := by
  unfold redShuffle redShuffleStendhal
  rw [← map_mul, StendhalAlgebra.e_mul_cut]

theorem redShuffle_mul_redFirstIdem (s : Seq μ) (hs : IsRedOrdered s) :
    redShuffle Q Λ s hs * redFirstIdem Q Λ ν = redShuffle Q Λ s hs := by
  classical
  unfold redShuffle redShuffleStendhal
  rw [← StendhalAlgebra.cut_mul_e, map_mul, mul_assoc]
  change _ * (redLoadingIdem Q Λ ν _ (isRedOrdered_redShuffle hs) * redFirstIdem Q Λ ν) = _
  rw [redLoadingIdem_mul_redFirstIdem_eq,
    ite_eq_left_of_eq_true _ _ (eq_true (isRedFirst_redShuffle s))]

theorem tensorFlip_redLoadingIdem (s : Seq μ) (hs : IsRedOrdered s) :
    tensorFlip (redLoadingIdem Q Λ ν s hs) = redLoadingIdem Q Λ ν s hs :=
  tensorFlip_mk_e s hs

/-- The horizontal reflection `θ̇_s ∈ e(t_s) T^λ e(s)` of the red/black shuffle. -/
def redShuffleDual (s : Seq μ) (hs : IsRedOrdered s) : TensorProductAlgebra k Q Λ ν :=
  tensorFlip (redShuffle Q Λ s hs)

theorem redShuffleDual_mul_redLoadingIdem (s : Seq μ) (hs : IsRedOrdered s) :
    redShuffleDual Q Λ s hs * redLoadingIdem Q Λ ν s hs = redShuffleDual Q Λ s hs := by
  unfold redShuffleDual
  rw [← tensorFlip_redLoadingIdem Q Λ s hs, ← tensorFlip_mul, redLoadingIdem_mul_redShuffle]

theorem redFirstIdem_mul_redShuffleDual (s : Seq μ) (hs : IsRedOrdered s) :
    redFirstIdem Q Λ ν * redShuffleDual Q Λ s hs = redShuffleDual Q Λ s hs := by
  unfold redShuffleDual
  rw [← tensorFlip_redFirstIdem, ← tensorFlip_mul, redShuffle_mul_redFirstIdem]

end Shuffle

section Injective

variable [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} {C : QuantumGroup.CartanDatum I}
  (hQ : IsRouquierQ C Q) (hQs : KLRSymm Q) (hbase : BaseCrossing Q)

include hQ hQs hbase in
/-- Lemma 5.23 with one element for all `x`: there is `c ∈ e(s) T^λ e⁰` with `x ↦ x c` injective
on `T^λ e(s)`. -/
theorem exists_redFirst_mul_injective (Λ : Fin ℓ → I →₀ ℕ) (s : Seq μ) (hs : IsRedOrdered s) :
    ∃ c, redLoadingIdem Q Λ ν s hs * c = c ∧ c * redFirstIdem Q Λ ν = c ∧
      ∀ x, x * redLoadingIdem Q Λ ν s hs = x → x * c = 0 → x = 0 := by
  suffices h : ∃ c, c * redFirstIdem Q Λ ν = c ∧
      ∀ x, x * redLoadingIdem Q Λ ν s hs = x → x * c = 0 → x = 0 by
    obtain ⟨c, hc, hinj⟩ := h
    refine ⟨redLoadingIdem Q Λ ν s hs * c, ?_, by rw [mul_assoc, hc], fun x hx h0 => ?_⟩
    · rw [← mul_assoc, (isIdempotentElem_redLoadingIdem Q Λ ν s hs).eq]
    · exact hinj x hx (by rwa [← mul_assoc, hx] at h0)
  obtain ⟨t, ht, htf, hch⟩ := reach_of_isRedOrdered hQ hQs hbase _ Λ ν rfl s hs
  induction hch using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨redLoadingIdem Q Λ ν t ht, redLoadingIdem_mul_redFirstIdem Q Λ ν t ht htf,
      fun x hx h0 => ?_⟩
    rwa [hx] at h0
  | head hst _ ih =>
    obtain ⟨hs₁, hs', c₁, hinj, hc⟩ := hst
    obtain ⟨c₂, hc₂, hinj₂⟩ := ih hs'
    refine ⟨c₁ * c₂, by rw [mul_assoc, hc₂], fun x hx h0 => hinj x hx (hinj₂ _ ?_ ?_)⟩
    · rw [mul_assoc, hc]
    · rwa [← mul_assoc] at h0

include hQ hQs hbase in
/-- Right multiplication by the red/black shuffle `θ_s` is injective on `T^λ e(s)`
(Webster, arXiv:1309.3796v2, proof of Proposition 5.30, by Lemma 5.23). -/
theorem mul_redShuffle_injective (Λ : Fin ℓ → I →₀ ℕ) (s : Seq μ) (hs : IsRedOrdered s)
    (x : TensorProductAlgebra k Q Λ ν) (hx : x * redLoadingIdem Q Λ ν s hs = x)
    (h0 : x * redShuffle Q Λ s hs = 0) : x = 0 := by
  obtain ⟨c, hc₁, hc₂, hinj⟩ := exists_redFirst_mul_injective hQ hQs hbase Λ s hs
  obtain ⟨y, hy⟩ := exists_eq_redShuffle_mul Q Λ s hs c hc₁ hc₂
  exact hinj x hx (by rw [hy, ← mul_assoc, h0, zero_mul])

include hQ hQs hbase in
/-- Left multiplication by `θ̇_s` is injective on `e(s) T^λ` (Webster, arXiv:1309.3796v2, proof
of Proposition 5.30, via Proposition 5.23). -/
theorem redShuffleDual_mul_injective (Λ : Fin ℓ → I →₀ ℕ) (s : Seq μ) (hs : IsRedOrdered s)
    (x : TensorProductAlgebra k Q Λ ν) (hx : redLoadingIdem Q Λ ν s hs * x = x)
    (h0 : redShuffleDual Q Λ s hs * x = 0) : x = 0 := by
  rw [← tensorFlip_tensorFlip x]
  refine (map_eq_zero_iff _ (tensorFlipEquiv Q Λ ν).injective).2
    (mul_redShuffle_injective hQ hQs hbase Λ s hs _ ?_ ?_)
  · rw [← tensorFlip_redLoadingIdem Q Λ s hs, ← tensorFlip_mul]
    exact congrArg _ hx
  · rw [← tensorFlip_tensorFlip (redShuffle Q Λ s hs), ← tensorFlip_mul]
    exact (map_eq_zero_iff _ (tensorFlipEquiv Q Λ ν).injective).2 h0

end Injective

section Headline

open scoped Classical
open KL3.Diagram

variable {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

/-- The right module `⊕_s y_s B` over the red-first corner `B = e⁰ T^λ e⁰`, where `s` runs over
the red-ordered loadings and `y_s = θ̇_s θ_s` (Webster, arXiv:1309.3796v2, Proposition 5.30). -/
abbrev redShuffleModule (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) : Type _ :=
  CornerEndomorphism.Target (isIdempotentElem_redFirstIdem QL Λ ν)
    (fun s : TensorProductAlgebra.OrderedLoading (ℓ := ℓ) ν => redShuffle QL Λ s.1 s.2)
    (fun s => redShuffleDual QL Λ s.1 s.2)
    (fun s => redShuffle_mul_redFirstIdem QL Λ s.1 s.2)
    (fun s => redFirstIdem_mul_redShuffleDual QL Λ s.1 s.2)

include hR hQs in
/-- **Webster, arXiv:1309.3796v3, Proposition 5.33** (v2: Proposition 5.30): `T^λ` is isomorphic to
the algebra of endomorphisms of the right `B`-module `⊕_s y_s B`, where `B = e⁰ T^λ e⁰ ≅ R^{∑ λ_r}`
is the red-first corner (Proposition 5.28), `s` runs over the red-ordered loadings, and
`y_s = θ̇_s θ_s` with `θ_s` the red/black shuffle from the red-first loading to `s`. The isomorphism
sends `a` to the endomorphism `(θ̇_s e(s) x)_s ↦ (θ̇_s e(s) a x)_s` of `T^λ e⁰ ≅ ⊕_s y_s B`
(`redFirstEndEquiv_apply`). -/
noncomputable def redFirstEndEquiv (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) :
    TensorProductAlgebra k QL Λ ν ≃+*
      Module.End (isIdempotentElem_redFirstIdem QL Λ ν).Cornerᵐᵒᵖ
        (redShuffleModule (k := k) (C := C) Λ ν) :=
  CornerEndomorphism.ringEquiv (isIdempotentElem_redFirstIdem QL Λ ν)
    (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem (k := k) QL Λ ν) _ _
    (fun s => redShuffle_mul_redFirstIdem QL Λ s.1 s.2)
    (fun s => redFirstIdem_mul_redShuffleDual QL Λ s.1 s.2)
    (fun s => redLoadingIdem_mul_redShuffle QL Λ s.1 s.2)
    (fun s x h₁ h₂ => exists_eq_redShuffle_mul QL Λ s.1 s.2 x h₁ h₂)
    (fun s x h₁ h₀ => redShuffleDual_mul_injective hR hQs (baseCrossing_std hR hQs) Λ s.1 s.2
      x h₁ h₀)
    (eq_zero_of_mul_redFirstProjective hR hQs Λ ν)
    (fun f hfN hfe hfb => by
      have he := (isIdempotentElem_redFirstIdem QL Λ ν).eq
      let f' : TensorProductAlgebra k QL Λ ν →ₗ[k] TensorProductAlgebra k QL Λ ν :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun c x => by
            set e := redFirstIdem QL Λ ν
            have h1 : (c • x) * e =
                x * e * (e * (c • (1 : TensorProductAlgebra k QL Λ ν)) * e) := by
              rw [mul_smul_comm, mul_one, smul_mul_assoc, smul_mul_assoc, he, mul_smul_comm,
                mul_assoc x e e, he]
            have h2 : (x * e) * e = x * e := by rw [mul_assoc, he]
            rw [RingHom.id_apply, hfN, h1, hfb _ _ h2, mul_smul_comm, mul_one, smul_mul_assoc,
              he, mul_smul_comm, hfe _ h2, ← hfN] }
      obtain ⟨a, ha, -⟩ := existsUnique_eq_mul_left_redFirst hR hQs Λ ν f' hfe
        (fun b x hx => hfb b x hx)
      exact ⟨a, ha⟩)

include hR hQs in
/-- The isomorphism of Proposition 5.30 is left multiplication, transported along
`T^λ e⁰ ≅ ⊕_s y_s B`, `x ↦ (θ̇_s e(s) x)_s`. -/
theorem redFirstEndEquiv_apply (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (a x : TensorProductAlgebra k QL Λ ν)
    (hx : x * redFirstIdem QL Λ ν = x) (s : TensorProductAlgebra.OrderedLoading (ℓ := ℓ + 1) ν) :
    ∃ m : redShuffleModule (k := k) (C := C) Λ ν, (∀ t, (m t).1.1 = redShuffleDual QL Λ t.1 t.2 *
        TensorProductAlgebra.boundaryIdem QL Λ ν t * x) ∧
      (redFirstEndEquiv hR hQs Λ ν a m s).1.1 =
        redShuffleDual QL Λ s.1 s.2 * TensorProductAlgebra.boundaryIdem QL Λ ν s * (a * x) := by
  refine ⟨CornerEndomorphism.toTarget _
    (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem (k := k) QL Λ ν) _ _ _ _
    (fun s x h₁ h₂ => exists_eq_redShuffle_mul QL Λ s.1 s.2 x h₁ h₂) ⟨x, hx⟩, fun t => rfl, ?_⟩
  unfold redFirstEndEquiv
  rw [CornerEndomorphism.ringEquiv_apply]
  rfl

end Headline

end Categorification.Stendhal
