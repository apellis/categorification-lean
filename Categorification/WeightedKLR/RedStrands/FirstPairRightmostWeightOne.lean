/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DividedDifference
import Categorification.WeightedKLR.RedStrands.FirstPairTwoAfterSpectator

/-!
# The second spectator crossing at weight one

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21).
The unit braid defect identifies which coefficients killed by the second
spectator crossing can contribute to the higher kernel filtration.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "B" => firstPairOneAfterSpectator true
local notation "D" => sadj N 3 • B
local notation "Rtop" => firstPairTwoAfterSpectator

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "δ" => (ψw [3,2] * e B : A)
local notation "β" => (ψ 3 * e D : A)
local notation "γ" => (ψw [2,3] * e B : A)
local notation "ρ" => (ψ 2 * e Rtop : A)

private theorem firstPair_weightOne_qbar :
    qbar (X 0 : MvPolynomial (Fin 2) k) = 1 := by
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [qbar_spec]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_rightmost_weightOne_braid (one : Λ 2 () = 1) :
    (ρ * δ - β * γ : A) = e B := by
  have tR : wordProd N [3,2] • B = Rtop := by decide +kernel
  have tD : wordProd N [2,3] • B = D := by decide +kernel
  have rCut : (e Rtop : A) * δ = δ := by
    rw [← tR, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc,e_mul_self]
  have dCut : (e D : A) * γ = γ := by
    rw [← tD, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc,e_mul_self]
  have br := braid (Q := stendhalQ Q Λ) 2 (by decide) B
  have hb₁ : (B).lbl ⟨2,by decide⟩ = Sum.inl () := by decide
  have hr : (B).lbl ⟨3,by decide⟩ = Sum.inr 2 := by decide
  have hb₂ : (B).lbl ⟨4,by decide⟩ = Sum.inl () := by decide
  rw [hb₁,hr,hb₂] at br
  have ne : (Sum.inl () : Unit ⊕ Fin 3) ≠ Sum.inr 2 := by decide
  have evalOne (z : Fin 3 → A) : ncEval z (1 : MvPolynomial (Fin 3) k) = 1 := by
    unfold ncEval
    rw [show (1 : MvPolynomial (Fin 3) k).coeff = Finsupp.single 0 1 from rfl]
    refine (Finsupp.sum_single_index ?_).trans ?_
    · rw [map_zero (algebraMap k A), zero_mul]
    · simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero, List.ofFn_const,
        List.prod_replicate, one_pow, mul_one]
      exact map_one (algebraMap k A)
  simp [ne, stendhalQ_inl_inr, one, firstPair_weightOne_qbar] at br
  have ev := evalOne ![x ⟨2, by decide⟩, x ⟨3, by decide⟩, x ⟨4, by decide⟩]
  have br0 : ((ψ 2 * ψ 3 * ψ 2 - ψ 3 * ψ 2 * ψ 3) * e B : A) = e B :=
    br.trans ((congrArg (fun d : A => d * e B) ev).trans (one_mul _))
  rw [mul_assoc (ψ 2) (e Rtop), rCut, mul_assoc (ψ 3) (e D), dCut]
  simpa only [ψw_cons,ψw_nil,mul_one,sub_mul,mul_assoc] using br0

/-- At final spectator weight one, a coefficient annihilated by the
second spectator crossing already comes from the higher terminal loading. -/
theorem firstPairRightmost_secondCrossing_kernel_of_weight_one (one : Λ 2 () = 1)
    (y : V) (left : F (e B) * y = y) (zero : F δ * y = 0) :
    ∃ z : V, F (e D) * z = z ∧ F β * z = y := by
  have br := congrArg (fun c : A => F c * y) (firstPair_rightmost_weightOne_braid Q Λ one)
  have eq : (F ρ * (F δ * y)) - (F β * (F γ * y)) = y := by
    simpa only [map_sub,map_mul F,sub_mul,mul_assoc,left] using br
  let z := -(F γ * y)
  have tD : wordProd N [2,3] • B = D := by decide +kernel
  have cut : F (e D) * F γ = F γ := by
    rw [← map_mul F, ← tD, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc,e_mul_self]
  refine ⟨z, ?_, ?_⟩
  · rw [show z = _ from rfl, mul_neg, ← mul_assoc, cut]
  · rw [zero, mul_zero, zero_sub] at eq
    rw [show z = _ from rfl, mul_neg]
    exact eq

end Categorification.Stendhal.BraidedStendhalAlgebra
