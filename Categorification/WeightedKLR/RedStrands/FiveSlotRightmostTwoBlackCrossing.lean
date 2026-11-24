/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotExtremeCrossing
import Categorification.WeightedKLR.RedStrands.TwoBlackFlagIdeal

/-!
# The two-black passage to the rightmost loading

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
Passing both equal blacks across the two later reds gives equal dot
powers. Reflection of the first and second powers recovers the
left-extreme flag test and gives cancellation at every bottom.
The passage intertwines the equal-black crossings at its two ends.
-/

noncomputable section
namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv TwoBlackFlag
open BraidedStendhalAlgebra

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)
local notation "N" => weight.card
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fixedTopFourExitCut 1
local notation "E₂" => fixedTopFourExitCut 2
local notation "i₁" => (⟨1,by decide⟩ : Fin N)
local notation "i₂" => (⟨2,by decide⟩ : Fin N)
local notation "i₃" => (⟨3,by decide⟩ : Fin N)
local notation "i₄" => (⟨4,by decide⟩ : Fin N)
local notation "m" => Λ 0 ()
local notation "A₀" => Λ 1 ()
local notation "B₀" => Λ 2 ()
local notation "d" => A₀ + B₀
local notation "P" => MvPolynomial (Fin N) k
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "D" => sortedFlagP (k := k) Λ
local notation "A" => polyRep (sortedFlagP_factor Q Λ)
local notation "I₀" => TwoBlackFlag.ideal (k := k) i₁ i₂ m m
local notation "l" => ([2,1,3,2] : List ℕ)
local notation "w" => wordProd N l

private theorem rightmost_crossComp (s : Seq weight) (j : ℕ) (h : j+1<N)
    (r : Fin 3) (hb : s.lbl ⟨j,by omega⟩=.inl ()) (hr : s.lbl ⟨j+1,h⟩=.inr r) (f : P) :
    crossComp D j h s f = X (⟨j+1,h⟩ : Fin N)^(Λ r ())*rename (sadj N j) f := by
  simp only [crossComp,hb,hr,reduceCtorEq,↓reduceIte,sortedFlagP,map_pow,rename_X,
    Matrix.cons_val_one,Matrix.cons_val_zero,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]

private theorem rightmost_step₁ (f : P) :
    wordComp D [2] E₀ f = X i₃^A₀*rename (wordProd N [2]) f := by
  rw [wordComp,dite_eq_left (by decide : 2+1<N)]
  simp only [LinearMap.comp_apply,wordComp,LinearMap.id_apply,wordProd_nil,one_smul,wordProd_cons,mul_one]
  exact rightmost_crossComp Λ E₀ 2 (by decide) 1 (by decide) (by decide) f

private theorem rightmost_step₂ (f : P) :
    wordComp D [3,2] E₀ f = X i₄^d*rename (wordProd N [3,2]) f := by
  rw [wordComp,dite_eq_left (by decide : 3+1<N),LinearMap.comp_apply,rightmost_step₁,
    rightmost_crossComp Λ _ 3 (by decide) 2 (by decide) (by decide),map_mul (rename (sadj N 3)),
    map_pow (rename (sadj N 3)),rename_X,rename_rename,
    show sadj N 3 i₃=i₄ by decide,pow_add]
  change X i₄^B₀*(X i₄^A₀*rename (wordProd N [3,2]) f)=_
  ring

private theorem rightmost_step₃ (f : P) :
    wordComp D [1,3,2] E₀ f = X i₂^A₀*(X i₄^d*rename (wordProd N [1,3,2]) f) := by
  rw [wordComp,dite_eq_left (by decide : 1+1<N),LinearMap.comp_apply,rightmost_step₂,
    rightmost_crossComp Λ _ 1 (by decide) 1 (by decide) (by decide),
    map_mul (rename (sadj N 1)),map_pow (rename (sadj N 1)),rename_X,rename_rename,
    show sadj N 1 i₄=i₄ by decide]
  rfl

/-- Moving both blacks across the two later reds contributes the same dot power
to each variable in the sorted polynomial action. -/
theorem fiveSlotRightmost_twoBlack_wordComp (f : P) :
    wordComp D l E₀ f = X i₃^d * X i₄^d * rename w f := by
  rw [wordComp,dite_eq_left (by decide : 2+1<N),LinearMap.comp_apply,rightmost_step₃,
    rightmost_crossComp Λ _ 2 (by decide) 2 (by decide) (by decide),
    map_mul (rename (sadj N 2)),map_mul (rename (sadj N 2)),map_pow (rename (sadj N 2)),
    map_pow (rename (sadj N 2)),rename_X,rename_X,rename_rename,
    show sadj N 2 i₂=i₃ by decide,show sadj N 2 i₄=i₄ by decide]
  rw [← mul_assoc ((X i₃ : P)^B₀), ← pow_add, Nat.add_comm B₀ A₀, mul_assoc]
  have hp : (⇑(sadj N 2) ∘ ⇑(wordProd N [1,3,2])) = (w : Fin N → Fin N) := by
    rw [wordProd_cons]
    rfl
  rw [hp]

private theorem rightmost_ideal :
    loadingIdeal (k := k) Λ E₂ = TwoBlackFlag.ideal i₃ i₄ (m+d) (m+d) := by
  have h₁ : redsBefore E₂ (firstBlack E₂) = Finset.univ := by decide
  have h₂ : redsBefore E₂ (secondBlack E₂) = Finset.univ := by decide
  unfold loadingIdeal flagBound
  rw [h₁,h₂,show firstBlack E₂=i₃ by decide,show secondBlack E₂=i₄ by decide,
    Fin.sum_univ_three,Nat.add_assoc]

private theorem rightmost_twoDot_test (z : R) (hz : F ((ψw l*e E₀)*z)=0)
    (input : Pol k weight) : blackEval E₀ (A z input E₀) ∈ I₀ := by
  let g := A z input
  have cut : opE E₀ g=Pi.single E₀ (g E₀) := by
    funext u
    rw [opE_apply,Pi.single_apply]
  have top : w • E₀=E₂ := by decide
  have h := eval_mem_sorted_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesSortedFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz input E₂
  rw [map_mul A,map_mul A,polyRep_ψw,polyRep_e,Module.End.mul_apply,Module.End.mul_apply,
    show opE E₀ (A z input)=Pi.single E₀ (g E₀) from cut,opΨw_single,top,Pi.single_eq_same,
    fiveSlotRightmost_twoBlack_wordComp Λ,rightmost_ideal Λ] at h
  have same (f : P) : blackEval E₂ (rename w f)=rename w (blackEval E₀ f) := by
    rw [← top,blackEval_rename_perm]
  have b₃ : ((E₂).lbl i₃).isLeft = true := by decide
  have b₄ : ((E₂).lbl i₄).isLeft = true := by decide
  rw [map_mul (blackEval E₂),map_mul (blackEval E₂),map_pow (blackEval E₂),
    map_pow (blackEval E₂),blackEval_X,blackEval_X,ite_eq_left b₃,ite_eq_left b₄,same] at h
  let a := rename w (blackEval E₀ (A z input E₀))
  have h' : (a * (X i₄)^d) * (X i₃)^d ∈ TwoBlackFlag.ideal i₃ i₄ (m+d) (m+d) := by
    have permute (f g q : P) : f * g * q = q * g * f :=
      (mul_comm (f*g) q).trans ((congrArg (q * ·) (mul_comm f g)).trans (mul_assoc q g f).symm)
    rw [permute]
    exact h
  have hne : i₃≠i₄ := by decide
  have intermediate := (mul_first_pow_mem_iff hne m (m+d) d _).mp h'
  have small := (mul_second_pow_mem_iff hne (le_refl m) d _).mp intermediate
  have back := rename_mem (w⁻¹ : Perm (Fin N)) small
  change rename (w⁻¹ : Perm (Fin N)) (rename w (blackEval E₀ (A z input E₀))) ∈ _ at back
  rw [show w⁻¹ i₃=i₁ by decide,show w⁻¹ i₄=i₂ by decide,rename_rename,
    show ((w⁻¹ : Perm (Fin N)) ∘ (w : Perm (Fin N)))=id from (w).symm_comp_self,rename_id] at back
  exact back

/-- The simultaneous two-black crossing from the left extreme to the right
extreme is injective on the whole supported right ideal. -/
theorem fiveSlotRightmost_twoBlack_cancel_of_leftSupport (hQ : KLRSymm Q)
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
    apply extreme_eq_zero_of_flagEvaluation Q Λ hQ (sortedFlagP_factor Q Λ)
      (fun i j h => by cases i <;> cases j <;> simp_all [unitLabels,sortedFlagP]) s z
      (by simp only [z,← mul_assoc,e_mul_self]) (by simp only [z,mul_assoc,e_mul_self])
    exact fun f => rightmost_twoDot_test Q Λ z hz (Pi.single s f)
  have one : ∑ s : Seq weight, F (e s) = 1 := by rw [← map_sum,sum_e,map_one]
  calc
    y = y*∑ s : Seq weight, F (e s) := by rw [one,mul_one]
    _ = 0 := by simp only [Finset.mul_sum,vanish,Finset.sum_const_zero]


private theorem braid_slide_ne (j : ℕ) (hj : j+2<N) (s : Seq weight)
    (hne : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩) (z : R) (hz : e s * z = z) :
    ψ (j+1) * (ψ j * (ψ (j+1) * z)) = ψ j * (ψ (j+1) * (ψ j * z)) := by
  have h := KLRAlgebra.braid (Q := stendhalQ Q Λ) j hj s
  rw [ite_eq_right (fun hh => hne hh.1), sub_mul, sub_eq_zero] at h
  simpa only [mul_assoc, hz] using congrArg (· * z) h.symm

/-- The simultaneous passage of both equal blacks carries their bottom
nilHecke crossing to the equal-black crossing at the right extreme. -/
theorem fiveSlotRightmost_twoBlack_intertwines :
    (ψ 3 * (ψw l * e E₀) : R) = (ψw l * e E₀) * (ψ 1 * e E₀) := by
  let t := wordProd N [1,2] • E₀
  let z : R := ψ 1 * (ψ 2 * e E₀)
  have ht : (e t : R) * z = z := by
    have h : (e t * (ψw [1,2] * e E₀) : R) = ψw [1,2] * e E₀ := by
      rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
    simpa only [z, ψw_cons, ψw_nil, mul_one, mul_assoc] using h
  have h₂ := braid_slide_ne Q Λ 2 (by decide) t (by decide) z ht
  have h₁ := braid_slide_ne Q Λ 1 (by decide) E₀ (by decide) (e E₀) (e_mul_self _)
  have hc (b : R) : ψ 1 * (ψ 3 * b) = ψ 3 * (ψ 1 * b) := by
    rw [← mul_assoc, ψ_mul_ψ 1 3 (by decide), mul_assoc]
  have hf : (e E₀ : R) * (ψ 1 * e E₀) = ψ 1 * e E₀ := by
    rw [← mul_assoc, e_mul_ψ, show sadj N 1 • E₀ = E₀ by decide, mul_assoc, e_mul_self]
  rw [mul_assoc, hf]
  simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
  rw [hc (ψ 2 * e E₀), h₂, h₁, ← hc]


private theorem rightmost_twoBlack_middle_cut :
    (e E₁ : R) * (ψw [3,2] * e E₀) = ψw [3,2] * e E₀ := by
  have top : wordProd N [3,2] • E₀ = E₁ := by decide
  rw [← top, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

private theorem rightmost_twoBlack_from_central :
    (ψw [2,1] * e E₁ : R) * (ψw [3,2] * e E₀) = ψw l * e E₀ := by
  rw [mul_assoc, rightmost_twoBlack_middle_cut Q Λ, ← mul_assoc, ← ψw_append]
  rfl

/-- The first E1 crossing map is injective on the image of the left-extreme
loading projective. -/
theorem fiveSlotRightmost_firstCrossing_cancel_on_leftExtreme (hQ : KLRSymm Q)
    (y : V) (hy : F (e E₀) * y = y)
    (zero : F (ψw [2,1] * e E₁) * (F (ψw [3,2] * e E₀) * y) = 0) : y = 0 := by
  apply fiveSlotRightmost_twoBlack_cancel_of_leftSupport Q Λ hQ y hy
  rw [← rightmost_twoBlack_from_central Q Λ, map_mul, mul_assoc]
  exact zero

/-- On the left-extreme generated part of the E1 loading projective, the
second crossing is the injective simultaneous passage after the left-extreme
nilHecke crossing. -/
theorem fiveSlotRightmost_secondCrossing_on_leftExtreme (y : V) :
    F (ψw [3,2,1] * e E₁) * (F (ψw [3,2] * e E₀) * y) =
      F (ψw l * e E₀) * (F (ψ 1 * e E₀) * y) := by
  have h : (ψw [3,2,1] * e E₁ : R) * (ψw [3,2] * e E₀) =
      (ψw l * e E₀) * (ψ 1 * e E₀) := by
    rw [ψw_cons 3 [2,1], mul_assoc, mul_assoc, rightmost_twoBlack_middle_cut Q Λ,
      ← mul_assoc (ψw [2,1]), ← ψw_append,
      show ([2,1]++[3,2] : List ℕ) = l from rfl, fiveSlotRightmost_twoBlack_intertwines Q Λ]
  rw [← mul_assoc, ← map_mul, h, map_mul, mul_assoc]

end Categorification.Stendhal.FiveSlotFlag
