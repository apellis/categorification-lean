/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedTransport
import Categorification.KLR.CyclotomicExact

/-!
# Flag tests for the independent last-red crossings

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21).
The two last-red crossings form a square with the earlier crossing.
The flag test reflects membership in the earlier crossing image through the
last-red crossing. The flag coefficients in the reflected relation lift to
native earlier-crossing images.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra MvPolynomial TypeA Equiv TwoBlackFlag FiveSlotFlag

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "P" => MvPolynomial (Fin N) k
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "near" => sadj N 2 • fixedTopFourExitCut 0
local notation "last" => sadj N 1 • near
local notation "a₁" => (⟨1, by decide⟩ : Fin N)
local notation "a₂" => (⟨2, by decide⟩ : Fin N)
local notation "a₃" => (⟨3, by decide⟩ : Fin N)
local notation "m" => Λ 0 ()
local notation "d" => Λ 1 ()

private theorem dot_slide_nearby : (x a₂ ^ m * (ψ 1 * e near) : R) =
    ψ 1 * (x a₁ ^ m * e near) := by
  have h := ψ_mul_pol_mul_e (Q := stendhalQ Q Λ) 1 (by decide : 1 + 1 < N) near ((X a₁ : P)^m)
  have hswap : swapPol 1 (by decide : 1 + 1 < N) ((X a₁ : P)^m) = (X a₂ : P)^m := by
    simp only [swapPol, map_pow, rename_X, show swap a₁ a₂ a₁ = a₂ by decide]
  rw [ite_eq_right (by decide), add_zero, hswap,
    map_pow (pol : P →ₐ[k] R), map_pow (pol : P →ₐ[k] R), pol_X, pol_X] at h
  simpa only [mul_assoc] using h.symm

private theorem nearby_first_dot_zero : F (x a₁ ^ m * e near) = 0 := by
  have h : (X a₁ : P)^m ∈ ideal a₁ a₃ m (m + d) :=
    Ideal.subset_span (Or.inl rfl)
  simpa only [map_pow pol, pol_X] using fiveSlotNearby_flagIdeal_kills Q Λ h

private theorem last_first_dot_zero : F (x a₂ ^ (m + d) * e last) = 0 := by
  have hclip : (e near : R) * (ψ 1 * e last) = ψ 1 * e last := by
    have hs : sadj N 1 • last = near := by decide +kernel
    simp only [ψ_mul_e, hs, ← mul_assoc, e_mul_self]
  have hreturn : (ψ 1 * e near : R) * (ψ 1 * e last) = x a₂ ^ d * e last := by
    rw [mul_assoc, hclip, ← mul_assoc,
      fiveSlot_red_black_right_square Q Λ 1 (by decide) last 1 (by decide) (by decide)]
  rw [pow_add, mul_assoc, ← hreturn, ← mul_assoc, dot_slide_nearby Q Λ,
    map_mul F, map_mul F, nearby_first_dot_zero Q Λ, mul_zero, zero_mul]

/-- Both cumulative flag relations at the loading with the red strand
after the two adjacent blacks vanish in the actual ordered quotient. -/
theorem fiveSlotLastRed_flagIdeal_kills {f : P}
    (hf : f ∈ ideal a₂ a₃ (m + d) (m + d)) : F (pol f * e last) = 0 := by
  let : Module R V := Module.compHom V (F).toRingHom
  have hdot : F (pol ((X a₂ : P)^(m + d)) * e last) = 0 := by
    rw [map_pow, pol_X, last_first_dot_zero Q Λ]
  have ann (v : V) : (pol ((X a₂ : P)^(m+d)) * e last : R) • v = 0 := by
    change F _ * v = 0
    rw [hdot, zero_mul]
  have hc := dd_smul_eq_zero (Q := stendhalQ Q Λ) 2 (by decide) (i := last)
    (by decide) ann (1 : V)
  change F (pol (NilHecke.dd k N 2 ((X a₂ : P)^(m+d))) * e last) * 1 = 0 at hc
  rw [mul_one, NilHecke.dd_of_lt (by decide : 2+1<N),
    ddiff_X_pow (by decide : a₂ ≠ a₃)] at hc
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  rw [map_add pol, map_mul pol, map_mul pol, add_mul, mul_assoc, mul_assoc, map_add F,
    map_mul F (pol u), map_mul F (pol v), hdot, hc, mul_zero, mul_zero, add_zero]

local notation "δ" => F (ψ 1 * e near)
local notation "τ" => F (ψ 2 * e last)
local notation "ρ" => F (ψ 1 * e last)

/-- Polynomials slide into the source of the earlier red crossing. -/
theorem fiveSlotLastRed_earlierCrossing_polynomialSlide (f : P) :
    F (pol f) * δ = δ * F (pol (swapPol 1 (by decide : 1 + 1 < N) f)) := by
  let swap₁ := swapPol (k := k) 1 (by decide : 1 + 1 < N)
  have hs : swap₁ (swap₁ f) = f := by
    change rename (swap a₁ a₂) (rename (swap a₁ a₂) f) = f
    rw [rename_rename, show ((swap a₁ a₂ : Fin N → Fin N) ∘ swap a₁ a₂) = id from
      funext (swap_apply_self _ _), rename_id]
    rfl
  have h := ψ_mul_pol_mul_e_of_ne (Q := stendhalQ Q Λ) 1 (by decide : 1 + 1 < N)
    (t := near) (by decide) (swap₁ f)
  change ψ 1 * pol (swap₁ f) * e near = pol (swap₁ (swap₁ f)) * ψ 1 * e near at h
  rw [hs] at h
  rw [← map_mul F, ← map_mul F]
  apply congrArg F
  calc
    _ = ψ 1 * pol (swap₁ f) * e near := by rw [h, mul_assoc]
    _ = _ := by rw [mul_assoc, ← (e_commute_pol near (swap₁ f)).eq, ← mul_assoc]

private theorem last_return_bigons : δ * ρ = F (x a₂ ^ d * e last) := by
  rw [← map_mul F]
  apply congrArg F
  have hclip : (e near : R) * (ψ 1 * e last) = ψ 1 * e last := by
    have hs : sadj N 1 • last = near := by decide +kernel
    simp only [ψ_mul_e, hs, ← mul_assoc, e_mul_self]
  rw [mul_assoc, hclip, ← mul_assoc,
    fiveSlot_red_black_right_square Q Λ 1 (by decide) last 1 (by decide) (by decide)]

private theorem last_first_dot_mul_delta : F (x a₂ ^ m) * δ = 0 := by
  rw [← map_mul F, dot_slide_nearby Q Λ, map_mul F,
    nearby_first_dot_zero Q Λ, mul_zero]

private theorem last_divided_slide (y : V) :
    F (x a₃ ^ m) * (τ * (δ * y)) =
      -(F (pol (complete (X a₂ : P) (X a₃) m)) * (δ * y)) := by
  have h := ψ_mul_pol_mul_e_of_eq (Q := stendhalQ Q Λ) 2 (by decide : 2 + 1 < N)
    (t := last) (by decide) ((X a₂ : P)^m)
  have hswap : swapPol 2 (by decide : 2 + 1 < N) ((X a₂ : P)^m) = (X a₃ : P)^m := by
    simp only [swapPol, map_pow, rename_X, show swap a₂ a₃ a₂ = a₃ by decide]
  rw [hswap, map_pow (pol : P →ₐ[k] R), map_pow (pol : P →ₐ[k] R), pol_X, pol_X,
    NilHecke.dd_of_lt (by decide : 2+1<N), ddiff_X_pow (by decide : a₂ ≠ a₃)] at h
  have hD : (e last : R) * (ψ 1 * e near) = ψ 1 * e near := by
    simp only [ψ_mul_e, ← mul_assoc, e_mul_self]
  have affine := congrArg (fun z : R => z * (ψ 1 * e near)) h
  simp only [add_mul, mul_assoc, hD] at affine
  have affine' := congrArg (fun z : R => F z * y) affine
  simp only [map_add F, map_mul F, add_mul, mul_assoc] at affine'
  have hz : F (ψ 2 : R) * (F (x a₂ ^ m) * (δ * y)) = 0 := by
    rw [← mul_assoc (F (x a₂ ^ m)), last_first_dot_mul_delta Q Λ, zero_mul, mul_zero]
  have hτ : τ * (δ * y) = F (ψ 2 : R) * (δ * y) := by
    rw [map_mul F, mul_assoc, ← mul_assoc (F (e last)), ← map_mul F, hD]
  rw [hτ, eq_neg_iff_add_eq_zero]
  rw [map_mul F, mul_assoc] at hz
  simpa only [map_mul F, mul_assoc] using affine'.symm.trans hz

/-- The two rectangular coefficient relations on the swapped descending
PBW row each factor through the earlier red crossing. -/
theorem fiveSlotLastRed_rectangular_lift (f : P)
    (hf : f ∈ (Ideal.span {(X a₂)^d, (X a₃)^m} : Ideal P)) (y : V) :
    ∃ z : V, F (pol f) * (τ * (δ * y)) = δ * z := by
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  let h := complete (X a₂ : P) (X a₃) m
  let q := τ * (δ * y)
  have hcut : F (e last) * q = q := by
    have hs : sadj N 2 • last = last := by decide +kernel
    have hτ : (e last : R) * (ψ 2 * e last) = ψ 2 * e last := by
      simp only [ψ_mul_e, hs, ← mul_assoc, e_mul_self]
    dsimp only [q]
    rw [← mul_assoc, ← map_mul F, hτ]
  have power₁ : F (x a₂ ^ d) * q = δ * (ρ * q) := by
    rw [← mul_assoc δ, last_return_bigons Q Λ, map_mul F, mul_assoc, hcut]
  have power₂ : F (x a₃ ^ m) * q = -(F (pol h) * (δ * y)) :=
    last_divided_slide Q Λ y
  rw [map_add pol, map_mul pol, map_mul pol, map_pow pol, map_pow pol, pol_X, pol_X,
    map_add F, map_mul F, map_mul F, add_mul, mul_assoc, mul_assoc, power₁, power₂,
    ← mul_assoc (F (pol u)), fiveSlotLastRed_earlierCrossing_polynomialSlide Q Λ u, mul_assoc δ,
    mul_neg, ← mul_assoc (F (pol v)), ← map_mul F, ← map_mul pol,
    ← mul_assoc (F (pol (v * h))), fiveSlotLastRed_earlierCrossing_polynomialSlide Q Λ (v * h), mul_assoc δ]
  exact ⟨F (pol (swapPol 1 (by decide) u)) * (ρ * q) -
    F (pol (swapPol 1 (by decide) (v * h))) * y, by rw [mul_sub, sub_eq_add_neg]⟩

/-- A coefficient satisfying the flag relation with the reduced first bound
gives a native lift through the earlier red crossing. -/
theorem fiveSlotLastRed_lift_of_restricted_flag (f : P)
    (hf : f ∈ ideal a₂ a₃ d (m+d)) (y : V) (hy : F (e last) * y = y) :
    ∃ z : V, F (pol f) * y = δ * z := by
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  let h := complete (X a₂ : P) (X a₃) (m+d)
  have hkill : F (pol h * e last) = 0 :=
    fiveSlotLastRed_flagIdeal_kills Q Λ (Ideal.subset_span (Or.inr rfl))
  have hz : F (pol h) * y = 0 := by
    rw [← hy, ← mul_assoc, ← map_mul F, hkill, zero_mul]
  have hp : F (x a₂ ^ d) * y = δ * (ρ * y) := by
    rw [← mul_assoc δ, last_return_bigons Q Λ, map_mul F, mul_assoc, hy]
  use F (pol (swapPol 1 (by decide) u)) * (ρ * y)
  rw [map_add pol, map_mul pol, map_mul pol, map_pow pol, pol_X, map_add F,
    map_mul F, map_mul F, add_mul, mul_assoc, mul_assoc, hp, hz, mul_zero, add_zero,
    ← mul_assoc (F (pol u)), fiveSlotLastRed_earlierCrossing_polynomialSlide Q Λ u, mul_assoc δ]

/-- At zero earlier red weight the return bigon gives every value at the
last-red loading an earlier-crossing preimage. -/
theorem fiveSlotLastRed_lift_of_earlierWeight_zero (weight : d = 0) (y : V)
    (hy : F (e last) * y = y) : ∃ z : V, y = δ * z := by
  refine ⟨ρ * y, ?_⟩
  rw [← mul_assoc, last_return_bigons Q Λ, weight, pow_zero, one_mul, hy]

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra MvPolynomial TypeA Equiv PolyRep
open BraidedStendhalAlgebra TwoBlackFlag

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "N" => Multiset.card weight
local notation "P" => MvPolynomial (Fin N) k
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "D" => sadj N 1 • (sadj N 2 • fixedTopFourExitCut 0)
local notation "B" => sadj N 3 • D
local notation "C" => fixedTopFourExitCut 1
local notation "a₂" => (⟨2, by decide⟩ : Fin N)
local notation "a₃" => (⟨3, by decide⟩ : Fin N)
local notation "a₄" => (⟨4, by decide⟩ : Fin N)
local notation "M₀" => Λ 0 ()
local notation "D₁" => Λ 1 ()
local notation "B₂" => Λ 2 ()
local notation "A" => polyRep (sortedFlagP_factor Q Λ)

private theorem squareWord_action (s : Seq weight) (j : ℕ) (h : j + 1 < N)
    (r : Fin 3) (hb : s.lbl ⟨j, by omega⟩ = .inl ())
    (hr : s.lbl ⟨j + 1, h⟩ = .inr r) (f : P) :
    wordComp (sortedFlagP (k := k) Λ) [j] s f =
      X (⟨j + 1, h⟩ : Fin N) ^ Λ r () * rename (wordProd N [j]) f := by
  rw [wordComp, dite_eq_left h]
  simp only [LinearMap.comp_apply, wordComp, LinearMap.id_apply, wordProd_nil, one_smul,
    wordProd_cons, mul_one, crossComp, hb, hr, reduceCtorEq, ↓reduceIte, sortedFlagP, map_pow,
    rename_X, Matrix.cons_val_one, Matrix.cons_val_zero, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]

private theorem squareCut_eval (s t : Seq weight) (j : ℕ) (step : wordProd N [j] • s = t)
    (z : R) (input : Pol k weight) :
    A ((ψw [j] * e s) * z) input t =
      wordComp (sortedFlagP (k := k) Λ) [j] s (A z input s) := by
  have cut : opE s (A z input) = Pi.single s (A z input s) := by
    funext u
    rw [opE_apply, Pi.single_apply]
  rw [map_mul A, map_mul A, polyRep_ψw, polyRep_e, Module.End.mul_apply,
    Module.End.mul_apply, cut, opΨw_single, step, Pi.single_eq_same]

/-- Flag evaluation transfers an overlap after the last red across that
crossing to the reduced first bound before it. -/
theorem fiveSlotLastRed_square_eval_mem_restricted_flag
    (u v : R) (relation : F (ψw [3] * e D) * F u = F (ψw [1] * e C) * F v)
    (input : Pol k weight) :
    blackEval D (A u input D) ∈ ideal a₂ a₃ D₁ (M₀+D₁) := by
  have top₃ : wordProd N [3] • D = B := by decide +kernel
  have top₁ : wordProd N [1] • C = B := by decide +kernel
  have hz : F ((ψw [3] * e D) * u - (ψw [1] * e C) * v) = 0 := by
    rw [map_sub F, map_mul F (ψw [3] * e D) u, map_mul F (ψw [1] * e C) v,
      relation, sub_self]
  have h := eval_mem_sorted_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesSortedFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz input B
  have idealB : loadingIdeal (k := k) Λ B =
      ideal a₂ a₄ (M₀+D₁) (M₀+D₁+B₂) := by
    unfold loadingIdeal flagBound
    rw [show redsBefore B (firstBlack B) = {0, 1} by decide,
      show redsBefore B (secondBlack B) = Finset.univ by decide,
      show firstBlack B = a₂ by decide, show secondBlack B = a₄ by decide,
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1), Fin.sum_univ_three]
  have e₃ : A ((ψw [3] * e D) * u) input B =
      X a₄ ^ B₂ * rename (wordProd N [3]) (A u input D) :=
    (squareCut_eval Q Λ D B 3 top₃ u input).trans
      (squareWord_action Λ D 3 (by decide) 2 (by decide) (by decide) _)
  have e₁ : A ((ψw [1] * e C) * v) input B =
      X a₂ ^ D₁ * rename (wordProd N [1]) (A v input C) :=
    (squareCut_eval Q Λ C B 1 top₁ v input).trans
      (squareWord_action Λ C 1 (by decide) 1 (by decide) (by decide) _)
  have rename₃ (f : P) : blackEval B (rename (wordProd N [3]) f) =
      rename (wordProd N [3]) (blackEval D f) := by
    rw [← top₃, blackEval_rename_perm]
  have rename₁ (f : P) : blackEval B (rename (wordProd N [1]) f) =
      rename (wordProd N [1]) (blackEval C f) := by
    rw [← top₁, blackEval_rename_perm]
  rw [map_sub A, LinearMap.sub_apply, Pi.sub_apply, map_sub (blackEval B), e₃, e₁] at h
  simp only [map_mul (blackEval B), map_pow (blackEval B), blackEval_X,
    ite_eq_left (by decide : ((B).lbl a₂).isLeft = true),
    ite_eq_left (by decide : ((B).lbl a₄).isLeft = true), rename₃, rename₁, idealB] at h
  let f := rename (wordProd N [3]) (blackEval D (A u input D))
  let g := rename (wordProd N [1]) (blackEval C (A v input C))
  have hsmall : X a₄ ^ B₂ * f - X a₂ ^ D₁ * g ∈ ideal a₂ a₄ D₁ (M₀+D₁+B₂) :=
    restrict_first (m := D₁) (d := M₀) (by simpa only [Nat.add_comm D₁ M₀] using h)
  have hterm : (X a₂ : P) ^ D₁ * g ∈ ideal a₂ a₄ D₁ (M₀+D₁+B₂) :=
    (ideal (k := k) a₂ a₄ D₁ (M₀+D₁+B₂)).mul_mem_right g
      (Ideal.subset_span (Or.inl rfl))
  have hg := (ideal (k := k) a₂ a₄ D₁ (M₀+D₁+B₂)).add_mem hsmall hterm
  rw [sub_add_cancel, mul_comm (X a₄ ^ B₂)] at hg
  have hf := (mul_second_pow_mem_iff (by decide : a₂ ≠ a₄) (Nat.le_add_left D₁ M₀) B₂ f).1 hg
  let w := wordProd N [3]
  have back := rename_mem (w⁻¹ : Perm (Fin N)) hf
  rw [show w⁻¹ a₂ = a₂ by decide, show w⁻¹ a₄ = a₃ by decide] at back
  change rename (w⁻¹ : Perm (Fin N)) (rename w (blackEval D (A u input D))) ∈ _ at back
  rw [rename_rename, show ((w⁻¹ : Perm (Fin N)) : Fin N → Fin N) ∘ w = id from
    w.symm_comp_self, rename_id] at back
  exact back

end Categorification.Stendhal.FiveSlotFlag
