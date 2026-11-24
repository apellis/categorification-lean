/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotExtremeFlagTest

/-!
# Left crossing cancellation at the five-slot extreme

In Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21),
on the corner at the left extreme the oriented flag tests read the two
black PBW rows for every bottom. A crossing word acting by transport and
increasing the second flag bound by its dot power is therefore injective
on this entire supported right ideal.
-/

noncomputable section
namespace Categorification.Stendhal.FiveSlotFlag
open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv BraidedStendhalAlgebra TwoBlackFlag
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "N" => weight.card
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "E₀" => fixedTopFourExitCut 0
local notation "i₁" => (⟨1,by decide⟩ : Fin N)
local notation "i₂" => (⟨2,by decide⟩ : Fin N)
local notation "C₀" => Λ 0 ()
local notation "P" => MvPolynomial (Fin N) k
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "D" => sortedFlagP (k := k) Λ
local notation "A" => polyRep (sortedFlagP_factor Q Λ)
local notation "I₀" => TwoBlackFlag.ideal (k := k) i₁ i₂ C₀ C₀

private theorem units_sorted (i j : Unit ⊕ Fin 3) (h : unitLabels i j=true) : D i j=1 := by
  cases i <;> cases j <;> simp_all [unitLabels,sortedFlagP]

private theorem flag_test_of_product (l : List ℕ) (t : Seq weight) (d : ℕ)
    (ht : wordProd N l • E₀=t)
    (hj : loadingIdeal (k := k) Λ t=ideal (wordProd N l i₁) (wordProd N l i₂) C₀ (C₀+d))
    (hw : ∀ p : P, wordComp D l E₀ p=X (wordProd N l i₂)^d*rename (wordProd N l) p)
    (z : R) (hz : F ((ψw l*e E₀)*z)=0) (input : Pol k weight) :
    blackEval E₀ (A z input E₀) ∈ I₀ := by
  let w := wordProd N l
  let g := A z input
  have cut : opE E₀ g=Pi.single E₀ (g E₀) := by
    funext u
    rw [opE_apply,Pi.single_apply]
  have h := eval_mem_sorted_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesSortedFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz input t
  rw [map_mul A,map_mul A,polyRep_ψw,polyRep_e,Module.End.mul_apply,Module.End.mul_apply,
    show opE E₀ (A z input)=Pi.single E₀ (g E₀) from cut,opΨw_single,ht,Pi.single_eq_same,hw,hj] at h
  have black : (t.lbl (w i₂)).isLeft := by
    rw [← ht]
    change ((wordProd N l • E₀).1 (w i₂)).isLeft
    rw [KLR.Seq.smul_apply,show (wordProd N l).symm (w i₂)=i₂ from (w).symm_apply_apply _]
    decide
  have same (p : P) : blackEval t (rename w p)=rename w (blackEval E₀ p) := by
    rw [← ht,blackEval_rename_perm]
  rw [map_mul (blackEval t),map_pow (blackEval t),blackEval_X,ite_eq_left black,same,mul_comm ((X _)^d)] at h
  have ne : w i₁≠w i₂ := (w).injective.ne (by decide : i₁≠i₂)
  have small := (mul_second_pow_mem_iff ne (le_refl C₀) d _).1 h
  have back := rename_mem (w⁻¹ : Perm (Fin N)) small
  rw [show w⁻¹ (w i₁)=i₁ from (w).symm_apply_apply _,show w⁻¹ (w i₂)=i₂ from (w).symm_apply_apply _,
    rename_rename,show ((w⁻¹ : Perm (Fin N)) ∘ (w : Perm (Fin N)))=id from (w).symm_comp_self,rename_id] at back
  exact back

/-- Flag transport gives cancellation on the whole extreme right ideal,
without a restriction on the bottom loading or its red order. -/
theorem leftWord_cancel_of_second_flag_push (hQ : KLRSymm Q) (l : List ℕ) (t : Seq weight) (d : ℕ)
    (ht : wordProd N l • E₀=t)
    (hj : loadingIdeal (k := k) Λ t=ideal (wordProd N l i₁) (wordProd N l i₂) C₀ (C₀+d))
    (hw : ∀ p : P, wordComp D l E₀ p=X (wordProd N l i₂)^d*rename (wordProd N l) p)
    (y : V) (left : F (e E₀)*y=y) (zero : F (ψw l*e E₀)*y=0) : y=0 := by
  classical
  obtain ⟨x,hx⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp (ofKLR_surjective (Q := Q) (Λ := Λ)) y
  have vanish (s : Seq weight) : y*F (e s)=0 := by
    let z : R := e E₀*x*e s
    have image : F z=y*F (e s) := by
      change F (e E₀*x*e s)=_
      rw [map_mul,map_mul,show F x=y from hx,left]
    have hz : F ((ψw l*e E₀)*z)=0 := by rw [map_mul,image,← mul_assoc,zero,zero_mul]
    rw [← image]
    apply extreme_eq_zero_of_flagEvaluation Q Λ hQ (sortedFlagP_factor Q Λ) (units_sorted Λ) s z
      (by simp only [z,← mul_assoc,e_mul_self]) (by simp only [z,mul_assoc,e_mul_self])
    exact fun p => flag_test_of_product Q Λ l t d ht hj hw z hz (Pi.single s p)
  have one : ∑ s : Seq weight, F (e s) = 1 := by rw [← map_sum,sum_e,map_one]
  calc
    y = y*∑ s : Seq weight, F (e s) := by rw [one,mul_one]
    _ = 0 := by simp only [Finset.mul_sum,vanish,Finset.sum_const_zero]

end Categorification.Stendhal.FiveSlotFlag
