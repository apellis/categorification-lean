/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistTransport
import Categorification.WeightedKLR.RedStrands.HalfTwistDualityGeneral
import Categorification.WeightedKLR.RedStrands.HalfTwistCokernel
import Categorification.WeightedKLR.RedStrands.BraidRightSequenceCut

set_option backward.isDefEq.respectTransparency false

/-!
# The braiding is faithful on morphisms between sequence projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15. A morphism `e(t) T^λ → e(t') T^λ` of right projectives is left multiplication by
some `x ∈ e(t') T^λ e(t)`, and its braid is left multiplication by `x` on the cut
`e(t) V e_κ`. If that vanishes then `x = 0`: the element `θ_t r̄_b` lies in the cut, where
`θ_t ∈ e(t) T^λ e(t⁰)` is the red/black shuffle and `r̄_b` is the flip of the braid `r_b` of
Corollary 6.8 at the red-first loading `t⁰ = e⁰_{ord,b}`. Right multiplication by `r̄_b` is
injective on `e_ord V e⁰_{ord,b}` (Corollary 6.8 flipped, `mul_violFlip_redBraid_injective`)
and right multiplication by `θ_t` is injective on `T^λ e(t)` (Lemma 5.23,
`mul_redShuffle_injective`).

## Main results

* `mul_violFlip_redBraid_injective`: Corollary 6.8 for right multiplication by `r̄_b`.
* `eq_zero_of_identityCornerMap_mul_violCorner`: faithfulness on the cuts.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "ord" => List.finRange ℓ

theorem violFlip_zero {ν : Multiset I} : violFlip (0 : ViolQuotient k Q Λ ν) = 0 := by
  change (violFlipHom k Q Λ ν 0).unop = 0
  rw [map_zero]
  rfl

variable (hQ : KLRSymm Q)
  (ρ : ∀ ν : Multiset I, Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ ν, TypeA.IsReducedChoice (ρ ν))

include hQ hρ in
/-- **Corollary 6.8 on the right**: right multiplication by the flip `r̄_b` of the braid `r_b`
is injective on `e_ord V e⁰_{ord,b}`. -/
theorem mul_violFlip_redBraid_injective {κ : List (Fin ℓ)} {r₀ : ViolQuotient k Q Λ 0}
    (hr₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ) * r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 ord) = r₀)
    (hne : r₀ ≠ 0) (b : List I) {z : ViolQuotient k Q Λ (blackWeight b)}
    (hz : violMk k Q Λ _ (redProj k Q Λ _ ord) * z * redFirstViol Q Λ ord b = z)
    (h0 : z * violFlip (redBraid r₀ b) = 0) : z = 0 := by
  have hf : redFirstViol Q Λ ord b * violFlip z * violMk k Q Λ _ (redProj k Q Λ _ ord) =
      violFlip z := by
    conv_rhs => rw [← hz]
    rw [violFlip_mul_eq, violFlip_mul_eq, violFlip_redFirstViol, violFlip_violMk, flip_redProj,
      mul_assoc]
  have hinj := (bijective_redBraid_mul hQ ρ hρ hr₀ hne b).1
  have e : violFlip z = 0 := by
    have := @hinj ⟨violFlip z, hf⟩ ⟨0, by rw [mul_zero, zero_mul]⟩ (Subtype.ext (by
      dsimp only
      rw [mul_zero, ← violFlip_violFlip (redBraid r₀ b), ← violFlip_mul_eq, h0, violFlip_zero]))
    exact congrArg Subtype.val this
  rw [← violFlip_violFlip z, e, violFlip_zero]

variable {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q) (hbase : BaseCrossing Q)

include hQ hρ hR hbase in
/-- **The braid of a morphism between sequence projectives determines it** (Webster,
arXiv:1309.3796v3, proof of Theorem 6.15). If `x ∈ T^λ e(t)` acts by zero on the cut
`e(t) V e_κ` for a red order `κ = σ(1, …, ℓ)`, then `x = 0`. -/
theorem eq_zero_of_identityCornerMap_mul_violCorner {ν : Multiset I}
    {t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t) (σ : Perm (Fin ℓ))
    (x : TensorProductAlgebra k Q Λ ν) (hx : x * redLoadingIdem Q Λ ν t ht = x)
    (h0 : ∀ y ∈ violCorner k Q Λ ν t ((List.finRange ℓ).map σ),
      identityCornerMap Q Λ ν (hρ ν) hQ x * y = 0) : x = 0 := by
  refine mul_redShuffle_injective hR hQ hbase Λ t ht x hx ?_
  have ht₀ := isRedOrdered_redShuffle ht
  obtain ⟨b, hb, s₁, hs₁, hcast⟩ := exists_redFirstSeq_eq _ rfl (redShufflePerm t • t)
    (isRedFirst_redShuffle t) ht₀
  subst hb
  change redFirstSeq s₁ b = redShufflePerm t • t at hcast
  have hs₁' : redWord s₁ = ord := hs₁.trans ((redWord_eq_finRange_iff _).2 ht₀)
  obtain ⟨r₀, hne, hr₀⟩ := exists_ne_zero_of_nil (k := k) (Λ := Λ) hQ (Seq.redPerm σ s₁) s₁
  rw [redWord_redPerm, hs₁'] at hr₀
  have hd := (redFirstData_redBraid hQ ρ hρ hr₀ hne b).1
  let φ := identityCornerMap Q Λ (blackWeight b) (hρ _) hQ
  -- `r̄_b e_κ = r̄_b`.
  have hfr : violFlip (redBraid r₀ b) *
      violMk k Q Λ _ (redProj k Q Λ _ ((List.finRange ℓ).map σ)) = violFlip (redBraid r₀ b) := by
    have h : violMk k Q Λ _ (redProj k Q Λ _ ((List.finRange ℓ).map σ)) * redBraid r₀ b =
        redBraid r₀ b := by
      rw [← hd.braid_left, ← mul_assoc, hd.left']
    conv_rhs => rw [← h]
    rw [violFlip_mul_eq, violFlip_violMk, flip_redProj]
  have hy : φ (redShuffle Q Λ t ht) * violFlip (redBraid r₀ b) ∈
      violCorner k Q Λ _ t ((List.finRange ℓ).map σ) := by
    refine mem_violCorner_iff.2 ⟨?_, by rw [mul_assoc, hfr]⟩
    rw [← mul_assoc, ← identityCornerMap_mk_e (hρ _) hQ t ht, ← map_mul]
    exact congrArg (· * _) (congrArg φ (redLoadingIdem_mul_redShuffle Q Λ t ht))
  have h1 := h0 _ hy
  rw [← mul_assoc, ← map_mul] at h1
  have hz : violMk k Q Λ _ (redProj k Q Λ _ ord) * φ (x * redShuffle Q Λ t ht) *
      redFirstViol Q Λ ord b = φ (x * redShuffle Q Λ t ht) := by
    rw [redFirstViol_eq_violMk_e hs₁' b, hcast, ← identityCornerMap_mk_e (hρ _) hQ _ ht₀,
      ← identityCornerMap_one (hρ _) hQ, ← map_mul, ← map_mul, one_mul, mul_assoc]
    exact congrArg φ (congrArg (x * ·) (redShuffle_mul_seqIdem Q Λ t ht))
  have h2 := mul_violFlip_redBraid_injective hQ ρ hρ hr₀ hne b hz h1
  refine (violCornerEquiv (hρ _) hQ).symm.injective (Subtype.ext ?_)
  rw [map_zero]
  exact h2

end Categorification.Stendhal.BraidedStendhalAlgebra
