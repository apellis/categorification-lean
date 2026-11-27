/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistInclusion
import Categorification.KLR.DistinctCrossings

set_option backward.isDefEq.respectTransparency false

/-!
# The element `y` of the half twist is a polynomial in the dots

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. The red/black shuffle `θ_t` from the red-first loading `t⁰ = τ_t • t` to `t` only
crosses red strands with black strands: `τ_t` keeps the order of the red strands and of the
black strands, so every inversion of `τ_t⁻¹` joins a red and a black strand
(`crossesDistinct_redShuffle`). Hence `y = θ̇_t θ_t` is a polynomial in the dots times `e(t⁰)`
(`exists_halfTwistY_eq_pol`).

## Main results

* `crossesDistinct_redShuffle`: each crossing of `θ_t` joins strands with different labels.
* `exists_halfTwistY_eq_pol`: `y = f(x) e(t⁰)` for a polynomial `f`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open Equiv KLR TypeA KLRAlgebra

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I} {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "ι" => ofKLR k Q Λ ν

omit [DecidableEq I] in
/-- Every crossing of the red/black shuffle `θ_t`, read from the red-first loading `τ_t • t`,
joins two strands with different labels. -/
theorem crossesDistinct_redShuffle (t : Seq μ) :
    CrossesDistinct (canWord m (redShufflePerm t)⁻¹) (redShufflePerm t • t) := by
  refine crossesDistinct_of_isReduced (isReduced_canWord _ _) _ fun p hp he => ?_
  rw [wordProd_canWord, mem_invSet] at hp
  obtain ⟨hpq, hqp⟩ := hp
  set τ := redShufflePerm t
  have he' : t.lbl (τ.symm p.1) = t.lbl (τ.symm p.2) := he
  have h1 : τ (τ.symm p.1) < τ (τ.symm p.2) := by simpa using hpq
  rw [redShufflePerm_lt_iff] at h1
  have hqp' : τ.symm p.2 < τ.symm p.1 := hqp
  rw [Fin.lt_def] at hqp'
  unfold redShuffleKey at h1
  rw [he'] at h1
  split_ifs at h1 <;> omega

/-- **The element `y = θ̇_t θ_t`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14) is a
polynomial in the dots times the idempotent of the red-first loading `τ_t • t`. -/
theorem exists_halfTwistY_eq_pol (t : Seq μ) :
    ∃ f : MvPolynomial (Fin m) k, halfTwistY (k := k) (Q := Q) (Λ := Λ) t =
      violMk k Q Λ ν (ι (pol f * KLRAlgebra.e (redShufflePerm t • t))) := by
  set c := canWord m (redShufflePerm t)⁻¹
  set t₀ := redShufflePerm t • t
  obtain ⟨f, hf⟩ := exists_ψw_reverse_mul_ψw_mul_e (k := k) (Q := stendhalQ Q Λ)
    (crossesDistinct_redShuffle t)
  refine ⟨f, ?_⟩
  have h : (ψw c * KLRAlgebra.e t₀ : KLRAlgebra k (stendhalQ Q Λ) μ) =
      KLRAlgebra.e t * ψw c := by
    rw [ψw_mul_e, wordProd_canWord, inv_smul_smul]
  have hc : (KLRAlgebra.e t * ψw c * KLRAlgebra.e t₀ : KLRAlgebra k (stendhalQ Q Λ) μ) =
      ψw c * KLRAlgebra.e t₀ := by
    rw [mul_assoc, h, ← mul_assoc, e_mul_self]
  rw [halfTwistY, violShuffleDual, violShuffle, ← map_mul, ← map_mul]
  congr 2
  calc (KLRAlgebra.e t₀ * ψw c.reverse * KLRAlgebra.e t *
        (KLRAlgebra.e t * ψw c * KLRAlgebra.e t₀) : KLRAlgebra k (stendhalQ Q Λ) μ)
      = KLRAlgebra.e t₀ * ψw c.reverse * (KLRAlgebra.e t * KLRAlgebra.e t * ψw c *
          KLRAlgebra.e t₀) := by simp only [mul_assoc]
    _ = KLRAlgebra.e t₀ * (ψw c.reverse * ψw c * KLRAlgebra.e t₀) := by
        rw [e_mul_self, hc]; simp only [mul_assoc]
    _ = pol f * KLRAlgebra.e t₀ := by
        rw [hf, ← mul_assoc, (e_commute_pol t₀ f).eq, mul_assoc, e_mul_self]

end Categorification.Stendhal.BraidedStendhalAlgebra
