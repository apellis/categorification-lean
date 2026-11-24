/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedSquareFlags
import Categorification.WeightedKLR.RedStrands.FiveSlotRightHigherPBW

/-!
# Reflection of the earlier crossing image across the last red strand

Webster, arXiv:1309.3796v2, Lemma 6.8 after (6.21).
There are six supported bottom loadings in the fixed red order. The extreme
row factors directly through the earlier crossing. Two nearby rows use the
complete polynomial on the swapped term. In the other three rows, the
tests on one and the first dot separate both coefficients. This lifts
the polynomial flag test to a supported element of the earlier crossing image.
-/

noncomputable section

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv BraidedStendhalAlgebra

local notation "N" => weight.card
local notation "D" => fiveSlotRightLoading 2
local notation "jA" => fiveSlotHigherLoading 2
local notation "S" => centralBottomLoading
local notation "i₂" => (⟨2, by decide⟩ : Fin N)
local notation "i₃" => (⟨3, by decide⟩ : Fin N)

private def lastRedSquareStableWord : Fin 6 → List ℕ
  | 0 => [1,2]
  | 1 => [1]
  | 2 => [1,3]
  | 3 => [3,2]
  | 4 => [3]
  | _ => []

private def lastRedSquareSwappedWord : Fin 6 → List ℕ
  | 0 => [1,2,1]
  | 1 => [2,1]
  | 2 => [2,1,3]
  | 3 => [2,3,2]
  | 4 => [2,3]
  | _ => [2]

local notation "a" => lastRedSquareStableWord
local notation "b" => lastRedSquareSwappedWord

private theorem lastRedSquareWords_spec (i : Fin 6) :
    IsReduced N (a i) ∧ IsReduced N (b i) ∧
      wordProd N (a i) ≠ wordProd N (b i) ∧
      ∀ p : Perm (Fin N), p • S i = D ↔ p = wordProd N (a i) ∨ p = wordProd N (b i) := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact ⟨by simp [ValidWord, lastRedSquareStableWord, lastRedSquareSwappedWord] <;> decide,
        by rw [length_eq_invCount]; decide +kernel⟩
    | decide +kernel

private theorem lastRedSquareStableWord_top (i : Fin 6) : wordProd N (a i) • S i = D := by
  fin_cases i <;> decide +kernel

private theorem lastRedSquareSwappedWord_top (i : Fin 6) : wordProd N (b i) • S i = D := by
  fin_cases i <;> decide +kernel

private theorem lastRedSquare_right_unit (i : Fin 6) (h : 3 ≤ i.val) : unitPath (S i) (a i) = true := by
  fin_cases i <;> first | contradiction | decide +kernel

private theorem lastRedSquare_right_first (i : Fin 6) (h : 3 ≤ i.val) :
    wordProd N (a i) (firstBlack (S i)) = i₂ := by
  fin_cases i <;> first | contradiction | decide +kernel

private theorem lastRedSquare_right_swap (i : Fin 6) (h : 3 ≤ i.val) : b i = 2 :: a i := by
  fin_cases i <;> first | contradiction | rfl

private def lastRedSquareNearbyRow : Bool → Fin 6
  | false => 1
  | true => 2

private def lastRedSquareNearbyTail : Bool → List ℕ
  | false => []
  | true => [3]

private theorem lastRedSquare_nearby_tail (j : Bool) :
    let i := lastRedSquareNearbyRow j
    let l := lastRedSquareNearbyTail j
    wordProd N l • S i = jA ∧ unitPath (S i) l = true ∧
      a i = 1 :: l ∧ b i = 2 :: 1 :: l := by
  cases j <;> decide +kernel

variable {k : Type} [CommRing k] (Λ : Fin 3 → Unit →₀ ℕ)
local notation "P" => MvPolynomial (Fin N) k
local notation "Ψ" => sortedFlagP (k := k) Λ

private theorem unit_sortedFlag (i r : Unit ⊕ Fin 3) (h : unitLabels i r = true) :
    (Ψ i r : MvPolynomial (Fin 2) k) = 1 := by
  cases i <;> cases r <;> simp_all [unitLabels, sortedFlagP]

private theorem lastRedSquare_dd_step (s : Seq weight) (f : P)
    (hs : s.lbl i₂ = s.lbl i₃) :
    crossComp Ψ 2 (by decide) s f = ddiff i₂ i₃ f := by
  rw [crossComp, ite_eq_left hs]

set_option backward.isDefEq.respectTransparency false in
private theorem lastRedSquare_right_readout (i : Fin 6) (h : 3 ≤ i.val) :
    wordComp Ψ (a i) (S i) (1 : P) = 1 ∧
    wordComp Ψ (a i) (S i) (X (firstBlack (S i)) : P) = X i₂ ∧
    wordComp Ψ (b i) (S i) (1 : P) = 0 ∧
    wordComp Ψ (b i) (S i) (X (firstBlack (S i)) : P) = 1 := by
  have hu (f : P) := wordComp_of_unitPath (unit_sortedFlag Λ) (S i) (a i)
    (lastRedSquare_right_unit i h) f
  have h₁ : wordComp Ψ (a i) (S i) (1 : P) = 1 := by rw [hu, map_one]
  have hx : wordComp Ψ (a i) (S i) (X (firstBlack (S i)) : P) = X i₂ := by
    rw [hu, rename_X, lastRedSquare_right_first i h]
  refine ⟨h₁,hx,?_⟩
  rw [lastRedSquare_right_swap i h]
  simp only [wordComp, dite_eq_left (by decide : 2+1<N), LinearMap.comp_apply,
    lastRedSquareStableWord_top, h₁,hx]
  have equal : (D).lbl i₂ = (D).lbl i₃ := by decide
  rw [lastRedSquare_dd_step Λ D (1 : P) equal,
    lastRedSquare_dd_step Λ D (X i₂ : P) equal,
    ddiff_eq_zero_of_rename_eq (by decide : i₂ ≠ i₃) (map_one _),
    ddiff_X_left (by decide : i₂ ≠ i₃)]
  exact ⟨rfl,rfl⟩

private theorem lastRedSquare_delta_action (f : P) :
    crossComp Ψ 1 (by decide) jA f =
      X i₂^(Λ 1 ()) * rename (sadj N 1) f := by
  have hb : (jA).lbl (⟨1, by decide⟩ : Fin N) = Sum.inl () := by decide
  have hr : (jA).lbl i₂ = Sum.inr 1 := by decide
  simp only [crossComp,hb,hr,reduceCtorEq,↓reduceIte,sortedFlagP,map_pow,rename_X,
    Matrix.cons_val_one,Matrix.cons_val_zero,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem lastRedSquare_nearby_readout_one (j : Bool) :
    let i := lastRedSquareNearbyRow j
    wordComp Ψ (a i) (S i) (1 : P) = X i₂^(Λ 1 ()) ∧
      wordComp Ψ (b i) (S i) (1 : P) = TwoBlackFlag.complete (X i₂) (X i₃) (Λ 1 ()) := by
  let i := lastRedSquareNearbyRow j
  let l := lastRedSquareNearbyTail j
  obtain ⟨ht,hu,ha,hb⟩ := lastRedSquare_nearby_tail j
  change wordComp Ψ (a i) (S i) (1 : P) = X i₂^(Λ 1 ()) ∧
    wordComp Ψ (b i) (S i) (1 : P) = TwoBlackFlag.complete (X i₂) (X i₃) (Λ 1 ())
  have h₁ : wordComp Ψ (a i) (S i) (1 : P) = X i₂^(Λ 1 ()) := by
    rw [ha, wordComp, dite_eq_left (by decide : 1+1<N), LinearMap.comp_apply, ht,
      wordComp_of_unitPath (unit_sortedFlag Λ) _ _ hu, map_one,
      lastRedSquare_delta_action Λ, map_one (rename (sadj N 1) : P →ₐ[k] P), mul_one]
  refine ⟨h₁, ?_⟩
  rw [hb, ← ha, wordComp, dite_eq_left (by decide : 2+1<N), LinearMap.comp_apply,
    lastRedSquareStableWord_top, h₁,
    lastRedSquare_dd_step Λ D _ (by decide : (D).lbl i₂ = (D).lbl i₃),
    TwoBlackFlag.ddiff_X_pow (by decide : i₂ ≠ i₃)]

variable (Q : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "A" => polyRep (sortedFlagP_factor Q Λ)

private theorem lastRedSquare_exists_two_pbw (hQ : KLRSymm Q) (i : Fin 6) (z : R)
    (left : e D * z = z) (right : z * e (S i) = z) :
    ∃ f g : P, z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i)) := by
  obtain ⟨ha,hb,hne,hmatch⟩ := lastRedSquareWords_spec i
  exact exists_two_corner_coefficients_of_words (stendhalQ_symm Q Λ hQ)
    (S i) D (a i) (b i) ha hb hne hmatch z left right

private theorem lastRedSquare_eval_pbw (i : Fin 6) (f g p : P) (z : R)
    (hz : z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i))) :
    A z (Pi.single (S i) p) D =
      f * wordComp Ψ (a i) (S i) p + g * wordComp Ψ (b i) (S i) p := by
  rw [hz, map_add A, LinearMap.add_apply, Pi.add_apply,
    eval_supported_term Q Λ (sortedFlagP_factor Q Λ) _ _ _ (lastRedSquareStableWord_top i),
    eval_supported_term Q Λ (sortedFlagP_factor Q Λ) _ _ _ (lastRedSquareSwappedWord_top i)]

private theorem lastRedSquare_right_coefficients_mem (i : Fin 6) (hi : 3 ≤ i.val)
    (L : Ideal P) (f g : P) (z : R)
    (hz : z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i)))
    (test : ∀ p : P, blackEval D (A z (Pi.single (S i) p) D) ∈ L) :
    blackEval D f ∈ L ∧ blackEval D g ∈ L := by
  obtain ⟨h₁,hx,hb₁,hbx⟩ := lastRedSquare_right_readout (k := k) Λ i hi
  have hf := test 1
  have hg := test (X (firstBlack (S i)))
  rw [lastRedSquare_eval_pbw Λ Q i f g 1 z hz, h₁, hb₁, mul_one, mul_zero, add_zero] at hf
  rw [lastRedSquare_eval_pbw Λ Q i f g _ z hz, hx, hbx, mul_one,
    map_add, map_mul, blackEval_X, ite_eq_left (by decide : ((D).lbl i₂).isLeft = true)] at hg
  have h := L.sub_mem hg (L.mul_mem_right (X i₂) hf)
  exact ⟨hf, by simpa only [add_sub_cancel_left] using h⟩

private theorem lastRedSquare_nearby_coefficient_mem (j : Bool) (L : Ideal P)
    (hpow : (X i₂ : P)^(Λ 1 ()) ∈ L) (f g : P) (z : R)
    (hz : let i := lastRedSquareNearbyRow j
      z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i)))
    (test : blackEval D (A z (Pi.single (S (lastRedSquareNearbyRow j)) 1) D) ∈ L) :
    blackEval D g * TwoBlackFlag.complete (X i₂) (X i₃) (Λ 1 ()) ∈ L := by
  let i := lastRedSquareNearbyRow j
  obtain ⟨h₁,h₂⟩ := lastRedSquare_nearby_readout_one (k := k) Λ j
  have h := test
  rw [lastRedSquare_eval_pbw Λ Q i f g 1 z hz, h₁,h₂] at h
  simp only [map_add (blackEval D), map_mul (blackEval D), map_pow (blackEval D),
    blackEval_X, ite_eq_left (by decide : ((D).lbl i₂).isLeft = true)] at h
  have hv := L.sub_mem h (L.mul_mem_left (blackEval D f) hpow)
  have preserve (n : ℕ) : blackEval D (TwoBlackFlag.complete (X i₂) (X i₃) n : P) =
      TwoBlackFlag.complete (X i₂) (X i₃) n := by
    induction n with
    | zero => rw [TwoBlackFlag.complete, map_zero]
    | succ n ih =>
      rw [TwoBlackFlag.complete, map_add, map_mul, ih, map_pow, blackEval_X, blackEval_X,
        ite_eq_left (by decide : ((D).lbl i₂).isLeft = true),
        ite_eq_left (by decide : ((D).lbl i₃).isLeft = true)]
  rw [preserve, add_sub_cancel_left] at hv
  exact hv

private theorem lastRedSquare_pol_factor (s : Seq weight) (l : List ℕ)
    (hl : wordProd N l • s = jA) (f : P) :
    ∃ y : R, pol f * (ψw (1 :: l) * e s) = (ψ 1 * e jA) * y := by
  let z : R := ψw l * e s
  have hz : (e jA : R) * z = z := by
    rw [← hl]
    exact word_leftCut Q Λ l s
  let y : R := pol (swapPol 1 (by decide) f) * z
  have hy : (e jA : R) * y = y := by
    change e jA * (pol _ * z) = pol _ * z
    rw [← pol_e_comm_assoc, hz]
  have hne : (jA).lbl (⟨1, by decide⟩ : Fin N) ≠ (jA).lbl i₂ := by decide
  let swap₁ := swapPol (k := k) 1 (by decide : 1+1<N)
  have hs : swap₁ (swap₁ f) = f := by
    change rename (swap (⟨1, by decide⟩ : Fin N) i₂)
      (rename (swap (⟨1, by decide⟩ : Fin N) i₂) f) = f
    rw [rename_rename,
      show ((swap (⟨1, by decide⟩ : Fin N) i₂ : Fin N → Fin N) ∘ swap ⟨1, by decide⟩ i₂) =
        id from funext (swap_apply_self _ _), rename_id]
    rfl
  have h := ψ_mul_pol_mul_e_of_ne (Q := stendhalQ Q Λ) 1 (by decide : 1+1<N)
    (t := jA) hne (swap₁ f)
  change ψ 1 * pol (swap₁ f) * e jA = pol (swap₁ (swap₁ f)) * ψ 1 * e jA at h
  rw [hs] at h
  refine ⟨y, ?_⟩
  rw [ψw_cons, mul_assoc, mul_assoc, hy]
  simpa only [mul_assoc, hz] using congrArg (· * z) h.symm

private theorem lastRedSquare_extreme_factors (f g : P) (z : R)
    (hz : z = pol f * (ψw (a 0) * e (S 0)) + pol g * (ψw (b 0) * e (S 0))) :
    ∃ y : R, z = (ψ 1 * e jA) * y := by
  have ht : wordProd N [2] • S 0 = jA := by decide
  have ht' : wordProd N [2,1] • S 0 = jA := by decide
  obtain ⟨y, hy⟩ := lastRedSquare_pol_factor Λ Q (S 0) [2] ht f
  obtain ⟨w, hw⟩ := lastRedSquare_pol_factor Λ Q (S 0) [2,1] ht' g
  refine ⟨y+w, ?_⟩
  change z = pol f * (ψw [1,2] * e (S 0)) + pol g * (ψw [1,2,1] * e (S 0)) at hz
  rw [hz,hy,hw,mul_add]

end Categorification.Stendhal.FiveSlotFlag

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv BraidedStendhalAlgebra

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "N" => weight.card
local notation "D" => fiveSlotRightLoading 2
local notation "jA" => sadj N 2 • fixedTopFourExitCut 0
local notation "S" => centralBottomLoading
local notation "i₂" => (⟨2, by decide⟩ : Fin N)
local notation "i₃" => (⟨3, by decide⟩ : Fin N)
local notation "a" => lastRedSquareStableWord
local notation "b" => lastRedSquareSwappedWord
local notation "P" => MvPolynomial (Fin N) k
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "A" => polyRep (sortedFlagP_factor Q Λ)
local notation "m" => Λ 0 ()
local notation "d" => Λ 1 ()
local notation "J" => TwoBlackFlag.ideal (k := k) i₂ i₃ d (m+d)
local notation "Cδ" => F (ψ 1 * e jA : R)
local notation "Cτ" => F (ψ 2 * e D : R)

private theorem lastRedSquare_position :
    sadj N 1 • (sadj N 2 • fixedTopFourExitCut 0) = D := by decide +kernel

private theorem lastRedSquare_normalize_term (hQ : KLRSymm Q) (s : Seq weight) (l : List ℕ)
    (ht : wordProd N l • s = D) (f : P) :
    F (pol f * (ψw l * e s)) = F (pol (blackEval D f)) * F (ψw l * e s) := by
  have hleft : (e D : R) * (ψw l * e s) = ψw l * e s := by
    rw [← ht]
    exact word_leftCut Q Λ l s
  have red : F (pol f * e D) = F (pol (blackEval D f) * e D) := by
    have h := congrArg (ofKLR k Q Λ ν) (toKLR_ofKLR_pol_mul_e (Q := Q) (Λ := Λ) f D)
    rw [ofKLR_toKLR hQ] at h
    exact congrArg (violMk k Q Λ ν) h
  calc
    _ = F (pol f * e D) * F (ψw l * e s) := by rw [← map_mul F, mul_assoc, hleft]
    _ = _ := by rw [red, ← map_mul F, mul_assoc, hleft, map_mul F]

private theorem lastRedSquare_word_in_corner (s : Seq weight) (l : List ℕ)
    (ht : wordProd N l • s = D) : F (e D) * F (ψw l*e s) = F (ψw l*e s) := by
  rw [← map_mul F, ← ht]
  exact congrArg F (word_leftCut Q Λ l s)

section RowLift

private theorem lastRedSquare_lift_nearby_rows (hQ : KLRSymm Q) (hd : d ≠ 0)
    (j : Bool) (f g : P) (z : R)
    (hz : let i := lastRedSquareNearbyRow j
      z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i)))
    (test : blackEval D (A z (Pi.single (S (lastRedSquareNearbyRow j)) 1) D) ∈ J) :
    ∃ y : V, F z = Cδ * y := by
  let i := lastRedSquareNearbyRow j
  let l := lastRedSquareNearbyTail j
  obtain ⟨ht,_,ha,hb⟩ := lastRedSquare_nearby_tail j
  have hpow : (X i₂ : P)^d ∈ J := Ideal.subset_span (Or.inl rfl)
  have h := lastRedSquare_nearby_coefficient_mem Λ Q j J hpow f g z hz test
  have hJ : TwoBlackFlag.ideal (k := k) i₂ i₃ d (m+d) = TwoBlackFlag.ideal i₂ i₃ d (d+m) := by rw [Nat.add_comm m d]
  have gmem := TwoBlackFlag.mem_rectangular_of_mul_complete (by decide : i₂ ≠ i₃) d m hd
    (blackEval D g) (hJ ▸ h)
  obtain ⟨y, hy⟩ := lastRedSquare_pol_factor Λ Q (S i) l ht f
  let p : R := ψw l * e (S i)
  have hword : (ψw (b i) * e (S i) : R) = (ψ 2 * e D) * ((ψ 1 * e jA) * p) := by
    have h₁ : (ψw [1] * e jA : R) * p = ψw (1::l) * e (S i) :=
      cut_word_mul Q Λ [1] l (S i) jA ht
    have h₂ :
        (ψw (2::a i) * e (S i) : R) = (ψw [2] * e D) * (ψw (a i) * e (S i)) :=
      (cut_word_mul Q Λ [2] (a i) (S i) D (lastRedSquareStableWord_top i)).symm
    have hb' : b i = 2::a i := hb.trans (congrArg (2::·) ha.symm)
    rw [hb', h₂, ha, ← h₁]
    simp only [ψw_cons, ψw_nil, mul_one]
  obtain ⟨x,hx⟩ := fiveSlotLastRed_rectangular_lift Q Λ (blackEval D g) gmem (F p)
  rw [lastRedSquare_position] at hx
  refine ⟨F y + x, ?_⟩
  change z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i)) at hz
  have stable : F (pol f * (ψw (a i) * e (S i))) = Cδ * F y := by
    rw [ha, hy, map_mul F, show fiveSlotHigherLoading 2 = jA by rfl]
  have swapped : F (pol g * (ψw (b i) * e (S i))) = Cδ * x := by
    rw [lastRedSquare_normalize_term Q Λ hQ _ _ (lastRedSquareSwappedWord_top i),
      hword, map_mul F (ψ 2 * e D), map_mul F (ψ 1 * e jA)]
    exact hx
  rw [hz, map_add F, stable, swapped, mul_add]

private theorem lastRedSquare_lift_right_rows (hQ : KLRSymm Q) (i : Fin 6) (hi : 3 ≤ i.val)
    (f g : P) (z : R)
    (hz : z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i)))
    (test : ∀ p : P, blackEval D (A z (Pi.single (S i) p) D) ∈ J) :
    ∃ x : V, F z = Cδ * x := by
  obtain ⟨hf,hg⟩ := lastRedSquare_right_coefficients_mem Λ Q i hi J f g z hz test
  obtain ⟨x,hx⟩ := fiveSlotLastRed_lift_of_restricted_flag Q Λ (blackEval D f) hf (F (ψw (a i) * e (S i)))
    (by
      rw [lastRedSquare_position]
      exact lastRedSquare_word_in_corner Q Λ _ _ (lastRedSquareStableWord_top i))
  obtain ⟨y,hy⟩ := fiveSlotLastRed_lift_of_restricted_flag Q Λ (blackEval D g) hg (F (ψw (b i) * e (S i)))
    (by
      rw [lastRedSquare_position]
      exact lastRedSquare_word_in_corner Q Λ _ _ (lastRedSquareSwappedWord_top i))
  refine ⟨x+y, ?_⟩
  rw [hz, map_add F, lastRedSquare_normalize_term Q Λ hQ _ _ (lastRedSquareStableWord_top i),
    lastRedSquare_normalize_term Q Λ hQ _ _ (lastRedSquareSwappedWord_top i), hx, hy, mul_add]

private theorem lastRedSquare_lift_of_flag_tests (hQ : KLRSymm Q) (hd : d ≠ 0) (s : Seq weight)
    (order : redWord s = redWord (fixedTopFourExitCut 0)) (z : R)
    (left : e D * z = z) (right : z * e s = z)
    (test : ∀ p : P, blackEval D (A z (Pi.single s p) D) ∈ J) :
    ∃ y : V, F z = Cδ * y := by
  by_cases hv : IsViolated s
  · refine ⟨0, ?_⟩
    rw [← right, map_mul F, show F (e s) = 0 from violMk_e hv, mul_zero, mul_zero]
  obtain ⟨i, rfl⟩ := centralBottomLoading_cases s order hv
  obtain ⟨f,g,hfg⟩ := lastRedSquare_exists_two_pbw Λ Q hQ i z left right
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i.val := by fin_cases i <;> decide
  rcases hc with rfl | rfl | rfl | hi
  · obtain ⟨y,hy⟩ := lastRedSquare_extreme_factors Λ Q f g z hfg
    exact ⟨F y, (congrArg F hy).trans (map_mul F _ _)⟩
  · exact lastRedSquare_lift_nearby_rows Q Λ hQ hd false f g z hfg (test 1)
  · exact lastRedSquare_lift_nearby_rows Q Λ hQ hd true f g z hfg (test 1)
  · exact lastRedSquare_lift_right_rows Q Λ hQ i hi f g z hfg test

end RowLift

local notation "C" => fixedTopFourExitCut 1
local notation "E₀" => fixedTopFourExitCut 0
local notation "E" => F (redIdem k Q Λ (redWord E₀))
local notation "p" => fun t : Seq weight => F (e t)
local notation "β" => F (ψw [3] * e D)
local notation "λ₀" => F (ψw [1] * e C)

/-- The independent last-red square reflects the image of the earlier
crossing in the actual fixed red-order right corner. -/
theorem fiveSlotLastRed_square_reflects_earlierCrossing (hQ : KLRSymm Q)
    (u v : V) (hu : p D * u = u) (hv : p C * v = v)
    (huE : u * E = u) (_hvE : v * E = v) (rel : β * u = λ₀ * v) :
    ∃ z : V, p jA * z = z ∧ z * E = z ∧ u = Cδ * z := by
  classical
  let image : AddSubmonoid V :=
    { carrier := {w | ∃ z : V, w = Cδ * z}
      zero_mem' := ⟨0, (mul_zero Cδ).symm⟩
      add_mem' := by
        rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
        exact ⟨x+y, (mul_add Cδ x y).symm⟩ }
  have himage : u ∈ image := by
    by_cases hd : d = 0
    · exact fiveSlotLastRed_lift_of_earlierWeight_zero Q Λ hd u (by rwa [lastRedSquare_position])
    obtain ⟨x,hx⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp
      (ofKLR_surjective (Q := Q) (Λ := Λ)) u
    obtain ⟨y,hy⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp
      (ofKLR_surjective (Q := Q) (Λ := Λ)) v
    have each (s : Seq weight) (hs : redWord s = redWord E₀) : u * p s ∈ image := by
      let u₁ : R := e D * x * e s
      let v₁ : R := e C * y * e s
      have hu₁ : F u₁ = u * p s := by
        change F (e D * x * e s) = _
        rw [map_mul F, map_mul F, show F x = u from hx, hu]
      have hv₁ : F v₁ = v * p s := by
        change F (e C * y * e s) = _
        rw [map_mul F, map_mul F, show F y = v from hy, hv]
      have hrel : β * F u₁ = λ₀ * F v₁ := by
        rw [hu₁,hv₁,← mul_assoc,← mul_assoc,rel]
      rw [← hu₁]
      exact lastRedSquare_lift_of_flag_tests Q Λ hQ hd s hs u₁
        (by simp only [u₁, ← mul_assoc, e_mul_self])
        (by simp only [u₁, mul_assoc, e_mul_self])
        (fun f => by
          have h := fiveSlotLastRed_square_eval_mem_restricted_flag Q Λ u₁ v₁
            (by rwa [lastRedSquare_position]) (Pi.single s f)
          rwa [lastRedSquare_position] at h)
    rw [← huE, redIdem, map_sum, Finset.mul_sum]
    exact sum_mem fun s hs => each s (Finset.mem_filter.mp hs).2
  obtain ⟨z,hz⟩ := himage
  have hj : p jA * p jA = p jA := by rw [← map_mul F, e_mul_self]
  have hE : E * E = E := (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₀)).eq
  have hc : Cδ * p jA = Cδ := by rw [← map_mul F, mul_assoc, e_mul_self]
  refine ⟨p jA * z * E, by rw [← mul_assoc, ← mul_assoc, hj], by rw [mul_assoc, hE], ?_⟩
  rw [← mul_assoc Cδ, ← mul_assoc Cδ, hc, ← hz, huE]

end Categorification.Stendhal.FiveSlotFlag
