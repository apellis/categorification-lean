/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagSource

/-!
# Flag annihilators at the two upper five-slot loadings

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
Moving the second black back to the left-extreme loading and returning
multiplies by its dot power. The left-extreme flag relation therefore
implies the flag relation with the increased second bound at each upper cut.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra MvPolynomial TypeA TwoBlackFlag Equiv

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "P" => MvPolynomial (Fin N) k
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "jA" => sadj N 2 • v₀
local notation "a₁" => (⟨1, by decide⟩ : Fin N)
local notation "a₂" => (⟨2, by decide⟩ : Fin N)
local notation "a₃" => (⟨3, by decide⟩ : Fin N)
local notation "a₄" => (⟨4, by decide⟩ : Fin N)
local notation "m" => Λ 0 ()
local notation "d" => Λ 1 () + Λ 2 ()
local notation "H" => complete (X a₁ : P) (X a₂) m
local notation "H'" => complete (X a₁ : P) (X a₄) m
local notation "b" => (ψ 2 * (ψ 3 * e v₁) : R)

private theorem red_black_right_square (j : ℕ) (hj : j+1<N) (s : Seq μ) (r : Fin 3)
    (hl : s.lbl ⟨j, by omega⟩ = Sum.inr r) (hr : s.lbl ⟨j+1,hj⟩ = Sum.inl ()) :
    (ψ j * ψ j * e s : R) = x ⟨j+1,hj⟩ ^ (Λ r ()) * e s := by
  rw [ψ_sq j hj, hl, hr]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, ncEval_x2, map_pow, rename_X,
    pol_X, Matrix.cons_val_one, Matrix.cons_val_zero]

private theorem slide_right_polynomial (j : ℕ) (hj : j+1<N) (s : Seq μ)
    (hne : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j+1,hj⟩) (f : P)
    (z : R) (hz : e s * z = z) :
    ψ j * (pol f * z) = pol (swapPol j hj f) * (ψ j * z) := by
  have h := ψ_mul_pol_mul_e (Q := stendhalQ Q Λ) j hj s f
  rw [ite_eq_right hne, add_zero] at h
  simpa only [mul_assoc, hz] using congrArg (· * z) h

private theorem right_first_dot_kills (t : Seq μ) (h₀ : t.lbl ⟨0, by decide⟩ = Sum.inr 0)
    (h₁ : t.lbl a₁ = Sum.inl ()) : F ((x a₁)^m * e t : R) = 0 := by
  let s := sadj N 0 • t
  have violated : IsViolated s := by
    refine ⟨by decide, ?_⟩
    rw [show s.lbl ⟨0, by decide⟩ = t.lbl a₁ by
      change (sadj N 0 • t).1 (⟨0, by decide⟩ : Fin N) = t.1 a₁
      rw [sadj_smul_apply 0 t (⟨0, by decide⟩ : Fin N)]
      exact congrArg t.1 (by decide), h₁]
    rfl
  have zero : F (e s) = 0 := violMk_e violated
  have top : (e s : R) * (ψ 0 * e t) = ψ 0 * e t := by
    rw [← mul_assoc, ← ψ_mul_e, mul_assoc, e_mul_self]
  have killed := congrArg F top
  rw [map_mul, zero, zero_mul] at killed
  have sq := red_black_right_square Q Λ 0 (by decide) t 0 h₀ h₁
  rw [← sq, mul_assoc, map_mul, killed.symm, mul_zero]

private theorem e1_return : ψ 3 * (ψ 2 * b) = (x a₄)^d * e v₁ := by
  have hmid : (e jA : R) * (ψ 3 * e v₁) = ψ 3 * e v₁ := by
    have hs : sadj N 3 • v₁ = jA := by decide
    rw [← hs, ← mul_assoc, ← ψ_mul_e, mul_assoc, e_mul_self]
  have h₂ := red_black_right_square Q Λ 2 (by decide) jA 1 (by decide) (by decide)
  have first : (ψ 2 * (ψ 2 * (ψ 3 * e v₁)) : R) =
      (x a₃)^ (Λ 1 ()) * (ψ 3 * e v₁) := by
    have h := congrArg (· * (ψ 3 * e v₁ : R)) h₂
    change (ψ 2 * ψ 2 * e jA) * (ψ 3 * e v₁) =
      (x a₃ ^ (Λ 1 ()) * e jA) * (ψ 3 * e v₁) at h
    simp only [mul_assoc, hmid] at h
    exact h
  have s₃ := slide_right_polynomial Q Λ 3 (by decide) jA (by decide)
    ((X a₃ : P) ^ (Λ 1 ())) (ψ 3 * e v₁) hmid
  have ns : swapPol 3 (by decide : 3 + 1 < N) ((X a₃ : P) ^ (Λ 1 ())) =
      (X a₄ : P) ^ (Λ 1 ()) := by
    rw [swapPol, map_pow, rename_X, show swap a₃ a₄ a₃ = a₄ by decide]
  rw [ns, map_pow (pol : P →ₐ[k] R), map_pow (pol : P →ₐ[k] R), pol_X, pol_X] at s₃
  rw [first, s₃, ← mul_assoc (ψ 3), red_black_right_square Q Λ 3 (by decide) v₁ 2
    (by decide) (by decide), ← mul_assoc, ← pow_add]

private theorem e1_map_complete (φ : P →ₐ[k] P) (f g : P) (j : ℕ) :
    φ (complete f g j) = complete (φ f) (φ g) j := by
  induction j with
  | zero => simp only [complete, map_zero]
  | succ j ih => simp only [complete, map_add, map_mul, ih, map_pow]

private theorem e1_swap_complete (j : ℕ) :
    swapPol 3 (by decide : 3+1<N) (swapPol 2 (by decide : 2+1<N)
      (complete (X a₁ : P) (X a₂) j)) = complete (X a₁ : P) (X a₄) j := by
  rw [e1_map_complete, e1_map_complete]
  simp only [swapPol, rename_X]
  rw [show swap a₂ a₃ a₁ = a₁ by decide, show swap a₃ a₄ a₁ = a₁ by decide,
    show swap a₂ a₃ a₂ = a₃ by decide, show swap a₃ a₄ a₃ = a₄ by decide]

private theorem e1_complete_higher_kills : F (pol H' * (x a₄)^d * e v₁ : R) = 0 := by
  have kill : F (pol H * e v₀) = 0 := by
    apply fiveSlotLeftExtreme_flagIdeal_kills Q Λ
    exact Ideal.subset_span (Or.inr rfl)
  have hb : (e v₀ : R) * b = b := by
    have h : (e v₀ * (ψw [2,3] * e v₁) : R) = ψw [2,3] * e v₁ := by
      rw [← show wordProd N [2,3] • v₁ = v₀ by decide, ← mul_assoc, e_mul_ψw,
        inv_smul_smul, mul_assoc, e_mul_self]
    simpa only [ψw_cons, ψw_nil, mul_one, mul_assoc] using h
  have hbmid : (e jA : R) * (ψ 2 * b) = ψ 2 * b := by
    rw [← mul_assoc, e_mul_ψ, show sadj N 2 • jA = v₀ by decide, mul_assoc, hb]
  have hs₂ := slide_right_polynomial Q Λ 2 (by decide) v₀ (by decide) H b hb
  have hs₃ := slide_right_polynomial Q Λ 3 (by decide) jA (by decide) (swapPol 2 (by decide) H)
    (ψ 2 * b) hbmid
  have hs := e1_swap_complete (k := k) m
  have hz : F (pol H * b) = 0 := by
    rw [← show (e v₀ : R) * b = b from hb, ← mul_assoc, map_mul, kill, zero_mul]
  have hzero : F (ψ 3 * (ψ 2 * (pol H * b)) : R) = 0 := by
    rw [map_mul, map_mul, hz, mul_zero, mul_zero]
  rw [hs₂, hs₃, hs, e1_return Q Λ, ← mul_assoc] at hzero
  exact hzero

/-- The full two-black flag ideal kills the central loading idempotent. -/
theorem fiveSlotCentral_flagIdeal_kills {f : P}
    (hf : f ∈ TwoBlackFlag.ideal a₁ a₄ m (m+d)) : F (pol f * e v₁) = 0 := by
  rw [TwoBlackFlag.ideal_add_right a₁ a₄ (Nat.le_refl m) d] at hf
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  rw [map_add pol, map_mul pol, map_mul pol, add_mul, mul_assoc, mul_assoc, map_add F,
    map_mul F (pol u), map_mul F (pol v), map_pow (pol : P →ₐ[k] R), pol_X, map_mul pol,
    map_pow (pol : P →ₐ[k] R), pol_X,
    right_first_dot_kills Q Λ v₁ (by decide) (by decide)]
  have hmul : (x a₄)^d * pol H' * e v₁ = (pol H' * (x a₄)^d * e v₁ : R) := by
    rw [← pol_X, ← map_pow, ← map_mul, ← map_mul, mul_comm ((X a₄ : P)^d)]
  rw [hmul, e1_complete_higher_kills Q Λ, mul_zero, mul_zero, add_zero]


private theorem nearby_complete_higher_kills :
    F (pol (complete (X a₁ : P) (X a₃) m) * (x a₃)^(Λ 1 ()) * e jA : R) = 0 := by
  have kill : F (pol H * e v₀) = 0 := by
    apply fiveSlotLeftExtreme_flagIdeal_kills Q Λ
    exact Ideal.subset_span (Or.inr rfl)
  let z : R := ψ 2 * e jA
  have hz : (e v₀ : R) * z = z := by
    change (e v₀ * (ψ 2 * e jA) : R) = ψ 2 * e jA
    rw [← mul_assoc, e_mul_ψ, show sadj N 2 • v₀ = jA by rfl, mul_assoc, e_mul_self]
  have hs := slide_right_polynomial Q Λ 2 (by decide) v₀ (by decide) H z hz
  have hswap : swapPol 2 (by decide : 2+1<N) H = complete (X a₁ : P) (X a₃) m := by
    rw [e1_map_complete]
    simp only [swapPol, rename_X]
    rw [show swap a₂ a₃ a₁ = a₁ by decide, show swap a₂ a₃ a₂ = a₃ by decide]
  have hprod : F (pol H * z) = 0 := by
    rw [← hz, ← mul_assoc, map_mul, kill, zero_mul]
  have hzero : F (ψ 2 * (pol H * z) : R) = 0 := by rw [map_mul, hprod, mul_zero]
  rw [hs, hswap] at hzero
  change F (pol (complete (X a₁ : P) (X a₃) m) * (ψ 2 * (ψ 2 * e jA))) = 0 at hzero
  rw [← mul_assoc (ψ 2), red_black_right_square Q Λ 2 (by decide) jA 1
    (by decide) (by decide), ← mul_assoc] at hzero
  exact hzero

/-- The full two-black flag ideal kills the nearby loading idempotent. -/
theorem fiveSlotNearby_flagIdeal_kills {f : P}
    (hf : f ∈ TwoBlackFlag.ideal a₁ a₃ m (m+Λ 1 ())) : F (pol f * e jA) = 0 := by
  rw [TwoBlackFlag.ideal_add_right a₁ a₃ (Nat.le_refl m) (Λ 1 ())] at hf
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  rw [map_add pol, map_mul pol, map_mul pol, add_mul, mul_assoc, mul_assoc, map_add F,
    map_mul F (pol u), map_mul F (pol v), map_pow (pol : P →ₐ[k] R), pol_X, map_mul pol,
    map_pow (pol : P →ₐ[k] R), pol_X, right_first_dot_kills Q Λ jA (by decide) (by decide)]
  have hmul : (x a₃)^(Λ 1 ()) * pol (complete (X a₁ : P) (X a₃) m) * e jA =
      (pol (complete (X a₁ : P) (X a₃) m) * (x a₃)^(Λ 1 ()) * e jA : R) := by
    rw [← pol_X, ← map_pow, ← map_mul, ← map_mul, mul_comm ((X a₃ : P)^(Λ 1 ()))]
  rw [hmul, nearby_complete_higher_kills Q Λ, mul_zero, mul_zero, add_zero]

end Categorification.Stendhal.BraidedStendhalAlgebra
