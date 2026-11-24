/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralCornerFlag

/-!
# Moving the last black from the nearby loading to the central loading

Webster, arXiv:1309.3796v2, Lemma 6.8 after (6.21).
The nearby and central cuts have the same first flag bound. The last black
crossing raises the second flag bound by the final red pairing and acts by
the corresponding power of its dot. The nearby flag tests reflect zero.
-/

noncomputable section

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv
open BraidedStendhalAlgebra

local notation "N" => weight.card
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fixedTopFourExitCut 1
local notation "jA" => sadj N 2 • E₀
local notation "i₁" => (⟨1, by decide⟩ : Fin N)
local notation "i₂" => (⟨2, by decide⟩ : Fin N)
local notation "i₃" => (⟨3, by decide⟩ : Fin N)
local notation "i₄" => (⟨4, by decide⟩ : Fin N)
local notation "S" => centralBottomLoading
local notation "H" => centralIntermediateLoading

private def nearbyFinishWord : Fin 3 → List ℕ
  | 0 => [2]
  | 1 => []
  | _ => [3]

private def nearbyStableWord (i : Fin 6) : List ℕ :=
  nearbyFinishWord (centralStableIntermediate i) ++ centralStablePrefix i

private def nearbySwappedWord (i : Fin 6) : List ℕ :=
  nearbyFinishWord (centralSwappedIntermediate i) ++ centralSwappedPrefix i

private theorem nearbyFinish_top (i : Fin 3) :
    wordProd N (nearbyFinishWord i) • H i = jA := by
  fin_cases i <;> decide +kernel

private theorem nearbyFinish_first (i : Fin 3) :
    wordProd N (nearbyFinishWord i) i₁ = i₁ := by
  fin_cases i <;> decide

private theorem nearbyStableWord_top (i : Fin 6) :
    wordProd N (nearbyStableWord i) • S i = jA := by
  rw [nearbyStableWord, wordProd_append, mul_smul, centralStablePrefix_top, nearbyFinish_top]

private theorem nearbySwappedWord_top (i : Fin 6) :
    wordProd N (nearbySwappedWord i) • S i = jA := by
  rw [nearbySwappedWord, wordProd_append, mul_smul, centralSwappedPrefix_top, nearbyFinish_top]

private theorem nearbyWords_spec (i : Fin 6) :
    IsReduced N (nearbyStableWord i) ∧ IsReduced N (nearbySwappedWord i) ∧
      wordProd N (nearbyStableWord i) ≠ wordProd N (nearbySwappedWord i) ∧
      ∀ p : Perm (Fin N), p • S i = jA ↔
        p = wordProd N (nearbyStableWord i) ∨ p = wordProd N (nearbySwappedWord i) := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact ⟨by
        simp [ValidWord, nearbyStableWord, nearbySwappedWord, nearbyFinishWord,
          centralStableIntermediate, centralSwappedIntermediate, centralStablePrefix,
          centralSwappedPrefix, centralBeforeSwap, centralAfterSwap, centralSwapIndex] <;> decide,
        by rw [length_eq_invCount]; decide +kernel⟩
    | decide +kernel

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "P" => MvPolynomial (Fin N) k
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "D" => sortedFlagP (k := k) Λ
local notation "A" => polyRep (sortedFlagP_factor Q Λ)
local notation "m" => Λ 0 ()
local notation "d" => Λ 1 ()
local notation "J" => TwoBlackFlag.ideal (k := k) i₁ i₃ m (m+d)

private def nearbyFinishExponent (i : Fin 3) : ℕ := if i = 0 then d else 0

private theorem nearbyFinish_action (i : Fin 3) (f : P) :
    wordComp D (nearbyFinishWord i) (H i) f =
      X i₃ ^ nearbyFinishExponent Λ i * rename (wordProd N (nearbyFinishWord i)) f := by
  fin_cases i
  · exact central_finish_first Λ f
  · change f = X i₃ ^ (0 : ℕ) * rename (wordProd N []) f
    simp [wordProd]
  · rw [centralUnit_action Λ _ _ (by decide)]
    change _ = X i₃ ^ (0 : ℕ) * _
    rw [pow_zero, one_mul]

private theorem nearbyWords_readout (i : Fin 6) (f g : P) (z : R)
    (hz : z = pol f * (ψw (nearbyStableWord i) * e (S i)) +
      pol g * (ψw (nearbySwappedWord i) * e (S i))) :
    let a₀ := (X i₃ : P) ^ nearbyFinishExponent Λ (centralStableIntermediate i)
    let b₀ := (X i₃ : P) ^ nearbyFinishExponent Λ (centralSwappedIntermediate i)
    A z (Pi.single (S i) 1) jA = f * a₀ ∧
      A z (Pi.single (S i) (X (firstBlack (S i)))) jA =
        f * (a₀ * X i₁) + g * b₀ := by
  have eval (p : P) : A z (Pi.single (S i) p) jA =
      f * wordComp D (nearbyStableWord i) (S i) p +
      g * wordComp D (nearbySwappedWord i) (S i) p := by
    rw [hz, map_add A, LinearMap.add_apply, Pi.add_apply,
      eval_supported_term Q Λ (sortedFlagP_factor Q Λ) _ _ _ (nearbyStableWord_top i),
      eval_supported_term Q Λ (sortedFlagP_factor Q Λ) _ _ _ (nearbySwappedWord_top i)]
  constructor
  · rw [eval, nearbyStableWord, nearbySwappedWord, centralWordComp_append Λ,
      centralWordComp_append Λ, centralStablePrefix_top, centralStablePrefix_action_one Λ,
      centralSwappedPrefix_action_one Λ, nearbyFinish_action Λ, map_one, mul_one,
      map_zero, mul_zero, add_zero]
  · rw [eval, nearbyStableWord, nearbySwappedWord, centralWordComp_append Λ,
      centralWordComp_append Λ, centralStablePrefix_top, centralSwappedPrefix_top,
      centralStablePrefix_action_first Λ, centralSwappedPrefix_action_first Λ,
      nearbyFinish_action Λ, nearbyFinish_action Λ, rename_X, nearbyFinish_first,
      map_one, mul_one]

private theorem nearbyTerm_kill (hQ : KLRSymm Q) (i : Fin 3) (s : Seq weight)
    (front : List ℕ) (hfront : wordProd N front • s = H i) (f : P)
    (hf : blackEval jA f * (X i₃)^nearbyFinishExponent Λ i ∈ J) :
    F (pol f * (ψw (nearbyFinishWord i ++ front) * e s)) = 0 := by
  let l := nearbyFinishWord i
  let z : R := ψw front * e s
  have hleft : (e (H i) : R) * z = z := by
    change (e (H i) * (ψw front * e s) : R) = ψw front * e s
    rw [← hfront, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  have htop : (e jA : R) * (ψw l * z) = ψw l * z := by
    rw [← nearbyFinish_top i, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, hleft]
  have red : F (pol f * e jA) = F (pol (blackEval jA f) * e jA) := by
    have h := congrArg (ofKLR k Q Λ ν) (toKLR_ofKLR_pol_mul_e (Q := Q) (Λ := Λ) f jA)
    rw [ofKLR_toKLR hQ] at h
    exact congrArg (violMk k Q Λ ν) h
  rw [ψw_append, mul_assoc (ψw _)]
  change F (pol f * (ψw l * z)) = 0
  calc
    _ = F (pol f * e jA) * F (ψw l * z) := by rw [← map_mul, mul_assoc, htop]
    _ = F (pol (blackEval jA f) * e jA) * F (ψw l * z) := by rw [red]
    _ = 0 := by
      by_cases hi : i = 0
      · subst i
        have hh := (TwoBlackFlag.mul_second_pow_mem_iff (by decide : i₁ ≠ i₃)
          (le_refl m) d (blackEval jA f)).mp hf
        let w := wordProd N [2]
        have hg := TwoBlackFlag.rename_mem (w⁻¹ : Perm (Fin N)) hh
        rw [show w⁻¹ i₁ = i₁ by decide, show w⁻¹ i₃ = i₂ by decide] at hg
        let g := rename (w⁻¹ : Perm (Fin N)) (blackEval jA f)
        have hrename : rename w g = blackEval jA f := by
          rw [show g = rename (w⁻¹ : Perm (Fin N)) (blackEval jA f) from rfl, rename_rename,
            show ((w : Fin N → Fin N) ∘ ((w⁻¹ : Perm (Fin N)) : Fin N → Fin N)) = id from
              w.self_comp_symm, rename_id]
          rfl
        change (e E₀ : R) * z = z at hleft
        have slide : (ψ 2 : R) * (pol g * z) =
            pol (blackEval jA f) * (ψ 2 * z) := by
          rw [← hrename]
          simpa only [swapPol, w, wordProd_cons, wordProd_nil, mul_one, sadj,
            dite_eq_left (by decide : 2+1<N)] using
            centralSlide_step Q Λ 2 (by decide) E₀ (by decide) g z hleft
        have hz : F (pol g * z) = 0 := by
          rw [← hleft, ← mul_assoc, map_mul F, fiveSlotLeftExtreme_flagIdeal_kills Q Λ hg, zero_mul]
        rw [← map_mul F, mul_assoc, htop]
        change F (pol (blackEval jA f) * (ψw [2] * z)) = 0
        rw [ψw_cons, ψw_nil, mul_one, ← slide, map_mul F, hz, mul_zero]
      · have hp : blackEval jA f ∈ J := by
          simpa only [nearbyFinishExponent, ite_eq_right hi, pow_zero, mul_one] using hf
        rw [fiveSlotNearby_flagIdeal_kills Q Λ hp, zero_mul]

private theorem nearby_eq_zero_of_flagEvaluation (hQ : KLRSymm Q) (s : Seq weight)
    (order : redWord s = redWord E₀) (z : R) (left : e jA * z = z) (right : z * e s = z)
    (test : ∀ f : P, blackEval jA (A z (Pi.single s f) jA) ∈ J) :
    F z = 0 := by
  by_cases hv : IsViolated s
  · rw [← right, map_mul, show F (e s) = 0 from violMk_e hv, mul_zero]
  obtain ⟨i, rfl⟩ := centralBottomLoading_cases s order hv
  obtain ⟨ha, hb, hne, hmatch⟩ := nearbyWords_spec i
  obtain ⟨f,g,hfg⟩ := exists_two_corner_coefficients_of_words
    (stendhalQ_symm Q Λ hQ) (S i) jA (nearbyStableWord i) (nearbySwappedWord i)
    ha hb hne hmatch z left right
  obtain ⟨h₁,h₂⟩ := nearbyWords_readout Q Λ i f g z hfg
  have b₁ : ((jA).lbl i₁).isLeft = true := by decide
  have b₃ : ((jA).lbl i₃).isLeft = true := by decide
  have hf : blackEval jA f * (X i₃)^nearbyFinishExponent Λ (centralStableIntermediate i) ∈ J := by
    have h := test 1
    rwa [h₁, map_mul (blackEval jA), map_pow (blackEval jA), blackEval_X, ite_eq_left b₃] at h
  have hg : blackEval jA g * (X i₃)^nearbyFinishExponent Λ (centralSwappedIntermediate i) ∈ J := by
    have h := test (X (firstBlack (S i)))
    rw [h₂] at h
    simp only [map_add (blackEval jA), map_mul (blackEval jA), map_pow (blackEval jA),
      blackEval_X, ite_eq_left b₁, ite_eq_left b₃, ← mul_assoc] at h
    let L : Ideal P := J
    simpa only [add_sub_cancel_left] using L.sub_mem h (L.mul_mem_right (X i₁) hf)
  rw [hfg, map_add, nearbyStableWord, nearbySwappedWord,
    nearbyTerm_kill Q Λ hQ _ _ _ (centralStablePrefix_top i) f hf,
    nearbyTerm_kill Q Λ hQ _ _ _ (centralSwappedPrefix_top i) g hg, zero_add]

private theorem nearbyToCentral_flag_test (z : R)
    (hz : F ((ψw [3]*e jA)*z)=0) (input : Pol k weight) :
    blackEval jA (A z input jA) ∈ J := by
  let g := A z input
  have cut : opE jA g = Pi.single jA (g jA) := by
    funext u
    rw [opE_apply, Pi.single_apply]
  let w := wordProd N [3]
  have top : w • jA = E₁ := by decide
  have h := eval_mem_sorted_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesSortedFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz input E₁
  have targetIdeal : loadingIdeal (k := k) Λ E₁ =
      TwoBlackFlag.ideal i₁ i₄ m ((m+d)+Λ 2 ()) := by
    unfold loadingIdeal flagBound
    rw [show redsBefore E₁ (firstBlack E₁) = {0} by decide,
      show redsBefore E₁ (secondBlack E₁) = Finset.univ by decide,
      show firstBlack E₁ = i₁ by decide, show secondBlack E₁ = i₄ by decide,
      Finset.sum_singleton, Fin.sum_univ_three]
  rw [map_mul A, map_mul A, polyRep_ψw, polyRep_e, Module.End.mul_apply,
    Module.End.mul_apply, show opE jA (A z input) = Pi.single jA (g jA) from cut,
    opΨw_single, top, Pi.single_eq_same, central_finish_one Λ, targetIdeal] at h
  have same (f : P) : blackEval E₁ (rename w f) = rename w (blackEval jA f) := by
    rw [← top, blackEval_rename_perm]
  rw [map_mul (blackEval E₁), map_pow (blackEval E₁), blackEval_X,
    ite_eq_left (by decide : ((E₁).lbl i₄).isLeft = true), same, mul_comm ((X i₄)^(Λ 2 ()))] at h
  have small := (TwoBlackFlag.mul_second_pow_mem_iff (by decide : i₁ ≠ i₄)
    (Nat.le_add_right m d) (Λ 2 ()) _).1 h
  have back := TwoBlackFlag.rename_mem (w⁻¹ : Perm (Fin N)) small
  rw [show w⁻¹ i₁ = i₁ by decide, show w⁻¹ i₄ = i₃ by decide, rename_rename,
    show ((w⁻¹ : Perm (Fin N)) ∘ (w : Perm (Fin N))) = id from w.symm_comp_self,
    rename_id] at back
  exact back

/-- The single rightward crossing of the final red is injective on the
nearby loading's right projective in the fixed red order. -/
theorem fiveSlotNearby_toCentral_cancel_on_orderCorner (hQ : KLRSymm Q)
    (y : V) (left : F (e jA) * y = y)
    (right : y * F (redIdem k Q Λ (redWord E₀)) = y)
    (zero : F (ψw [3]*e jA) * y = 0) : y = 0 := by
  classical
  obtain ⟨x,hx⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp (ofKLR_surjective (Q := Q) (Λ := Λ)) y
  have vanish (s : Seq weight) (hs : redWord s = redWord E₀) : y * F (e s) = 0 := by
    let z : R := e jA * x * e s
    have image : F z = y * F (e s) := by
      change F (e jA * x * e s) = _
      rw [map_mul, map_mul, show F x = y from hx, left]
    have hz : F ((ψw [3]*e jA)*z) = 0 := by
      rw [map_mul, image, ← mul_assoc, zero, zero_mul]
    rw [← image]
    apply nearby_eq_zero_of_flagEvaluation Q Λ hQ s hs z
      (by simp only [z, ← mul_assoc, e_mul_self]) (by simp only [z, mul_assoc, e_mul_self])
    exact fun f => nearbyToCentral_flag_test Q Λ z hz (Pi.single s f)
  calc
    y = y * F (redIdem k Q Λ (redWord E₀)) := right.symm
    _ = 0 := by
      rw [redIdem, map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun s hs => vanish s (Finset.mem_filter.mp hs).2

end Categorification.Stendhal.FiveSlotFlag
