/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotExtremeCrossing
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopIdeal
import Categorification.WeightedKLR.RedStrands.FiveSlotUpperFlagAnnihilator
import Categorification.WeightedKLR.RedStrands.TwoBlackFlagIdeal

/-!
# Flag separation at the central five-slot loading

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
The stable and swapped black matchings at the six nonviolated bottoms
of the fixed red order give separate coefficient tests. Pulling back
each final second-black passage recovers its intermediate flag ideal.
First-dot reflection then gives injectivity of the central-to-rightmost
crossing on the same-order source projective.
-/

noncomputable section

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv
open BraidedStendhalAlgebra

local notation "N" => weight.card
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fixedTopFourExitCut 1
local notation "E₂" => fixedTopFourExitCut 2
local notation "jA" => sadj N 2 • E₀
local notation "rM" => sadj N 2 • E₂
local notation "rL" => sadj N 3 • rM
local notation "i₁" => (⟨1, by decide⟩ : Fin N)

/-- The nonviolated bottom loadings in the standard red order. -/
def centralBottomLoading : Fin 6 → Seq weight
  | 0 => E₀
  | 1 => jA
  | 2 => E₁
  | 3 => E₂
  | 4 => rM
  | _ => rL

/-- The intermediate cuts to which a second-black rightward passage is applied. -/
def centralIntermediateLoading : Fin 3 → Seq weight
  | 0 => E₀
  | 1 => jA
  | _ => E₁

/-- The final rightward passage of the second black to the central loading. -/
def centralFinishWord : Fin 3 → List ℕ
  | 0 => [3,2]
  | 1 => [3]
  | _ => []

def centralStableIntermediate : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | _ => 1

def centralSwappedIntermediate : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | _ => 1

def centralStablePrefix : Fin 6 → List ℕ
  | 3 => [1,2]
  | 4 => [1]
  | 5 => [1]
  | _ => []

def centralBeforeSwap : Fin 6 → List ℕ
  | 1 => [2]
  | 2 => [2,3]
  | 4 => [3]
  | _ => []

def centralSwapIndex : Fin 6 → ℕ
  | 3 => 3
  | 4 => 2
  | 5 => 2
  | _ => 1

def centralAfterSwap : Fin 6 → List ℕ
  | 3 => [1,2]
  | 4 => [1]
  | 5 => [1]
  | _ => []

def centralSwappedPrefix (i : Fin 6) : List ℕ :=
  centralAfterSwap i ++ centralSwapIndex i :: centralBeforeSwap i

def centralStableWord (i : Fin 6) : List ℕ :=
  centralFinishWord (centralStableIntermediate i) ++ centralStablePrefix i

def centralSwappedWord (i : Fin 6) : List ℕ :=
  centralFinishWord (centralSwappedIntermediate i) ++ centralSwappedPrefix i

local notation "S" => centralBottomLoading
local notation "H" => centralIntermediateLoading
local notation "a" => centralStableWord
local notation "b" => centralSwappedWord

private theorem centralBottomLoading_cases (s : Seq weight)
    (order : redWord s = redWord E₀) (hv : ¬ IsViolated s) :
    ∃ i, s = S i := by
  obtain h | rfl | rfl | rfl := fiveSlot_nonviolated_tops s order hv
  · obtain rfl | rfl | rfl := h
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  · exact ⟨0,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨1,rfl⟩

theorem centralStablePrefix_top (i : Fin 6) :
    wordProd N (centralStablePrefix i) • S i = H (centralStableIntermediate i) := by
  fin_cases i <;> decide +kernel

theorem centralSwappedPrefix_top (i : Fin 6) :
    wordProd N (centralSwappedPrefix i) • S i = H (centralSwappedIntermediate i) := by
  fin_cases i <;> decide +kernel

theorem centralStablePrefix_unit (i : Fin 6) :
    unitPath (S i) (centralStablePrefix i) = true := by
  fin_cases i <;> decide +kernel

theorem centralBeforeSwap_unit (i : Fin 6) :
    unitPath (S i) (centralBeforeSwap i) = true := by
  fin_cases i <;> decide +kernel

private def centralAdjacentLoading (i : Fin 6) : Seq weight :=
  wordProd N (centralBeforeSwap i) • S i

private theorem centralSwapIndex_lt (i : Fin 6) : centralSwapIndex i + 1 < N := by
  fin_cases i <;> decide

private theorem centralSwap_equal (i : Fin 6) :
    (centralAdjacentLoading i).lbl ⟨centralSwapIndex i, by have := centralSwapIndex_lt i; omega⟩ =
      (centralAdjacentLoading i).lbl ⟨centralSwapIndex i+1, centralSwapIndex_lt i⟩ := by
  fin_cases i <;> decide +kernel

theorem centralAfterSwap_unit (i : Fin 6) :
    unitPath (sadj N (centralSwapIndex i) • centralAdjacentLoading i) (centralAfterSwap i) = true := by
  fin_cases i <;> decide +kernel

private theorem centralStablePrefix_first (i : Fin 6) :
    wordProd N (centralStablePrefix i) (firstBlack (S i)) = i₁ := by
  fin_cases i <;> decide +kernel

private theorem centralBeforeSwap_first (i : Fin 6) :
    wordProd N (centralBeforeSwap i) (firstBlack (S i)) =
      ⟨centralSwapIndex i, by have := centralSwapIndex_lt i; omega⟩ := by
  fin_cases i <;> decide +kernel

/-- The two words realize the only two black matchings at each supported bottom. -/
theorem centralWords_spec (i : Fin 6) :
    IsReduced N (a i) ∧ IsReduced N (b i) ∧
      wordProd N (a i) ≠ wordProd N (b i) ∧
      ∀ p : Perm (Fin N), p • S i = E₁ ↔ p = wordProd N (a i) ∨ p = wordProd N (b i) := by
  fin_cases i <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact ⟨by
        simp [ValidWord, centralStableWord, centralSwappedWord, centralFinishWord,
          centralStableIntermediate, centralSwappedIntermediate, centralStablePrefix,
          centralSwappedPrefix, centralBeforeSwap, centralAfterSwap, centralSwapIndex] <;> decide,
        by rw [length_eq_invCount]; decide +kernel⟩
    | decide +kernel


section Polynomial
variable {k : Type} [CommRing k] (Λ : Fin 3 → Unit →₀ ℕ)
local notation "P" => MvPolynomial (Fin N) k
local notation "D" => sortedFlagP (k := k) Λ
local notation "pre" => centralBeforeSwap
local notation "post" => centralAfterSwap
local notation "j" => centralSwapIndex

private theorem centralWordComp_append (l r : List ℕ) (s : Seq weight) (f : P) :
    wordComp D (l ++ r) s f = wordComp D l (wordProd N r • s) (wordComp D r s f) := by
  induction l with
  | nil => simp [wordComp]
  | cons c l ih =>
    rw [List.cons_append, wordComp, wordComp]
    by_cases h : c+1<N
    · rw [dite_eq_left h, dite_eq_left h, LinearMap.comp_apply, LinearMap.comp_apply, ih,
        wordProd_append, mul_smul]
    · simp only [dite_eq_right h, LinearMap.zero_apply]

private theorem central_unit_parameter (i r : Unit ⊕ Fin 3) (h : unitLabels i r = true) :
    (D i r : MvPolynomial (Fin 2) k) = 1 := by
  cases i <;> cases r <;> simp_all [unitLabels, sortedFlagP]

private theorem centralUnit_action (s : Seq weight) (l : List ℕ) (hl : unitPath s l = true) (f : P) :
    wordComp D l s f = rename (wordProd N l) f :=
  wordComp_of_unitPath (central_unit_parameter Λ) s l hl f

theorem centralStablePrefix_action_one (i : Fin 6) :
    wordComp D (centralStablePrefix i) (S i) (1 : P) = 1 := by
  rw [centralUnit_action Λ (S i) _ (centralStablePrefix_unit i), map_one]

theorem centralStablePrefix_action_first (i : Fin 6) :
    wordComp D (centralStablePrefix i) (S i) (X (firstBlack (S i)) : P) = X i₁ := by
  rw [centralUnit_action Λ (S i) _ (centralStablePrefix_unit i), rename_X, centralStablePrefix_first]

private theorem centralSwappedPrefix_action (i : Fin 6) (f : P) :
    wordComp D (centralSwappedPrefix i) (S i) f =
      rename (wordProd N (post i)) (ddiff
        ⟨j i, by have := centralSwapIndex_lt i; omega⟩ ⟨j i+1, centralSwapIndex_lt i⟩
        (rename (wordProd N (pre i)) f)) := by
  rw [centralSwappedPrefix, centralWordComp_append, wordComp, dite_eq_left (centralSwapIndex_lt i),
    LinearMap.comp_apply, centralUnit_action Λ (S i) _ (centralBeforeSwap_unit i)]
  change wordComp D (post i) (wordProd N (j i :: pre i) • S i)
    (crossComp D (j i) (centralSwapIndex_lt i) (centralAdjacentLoading i)
      (rename (wordProd N (pre i)) f)) = _
  rw [wordProd_cons, mul_smul, crossComp, ite_eq_left (centralSwap_equal i)]
  exact centralUnit_action Λ _ _ (centralAfterSwap_unit i) _

theorem centralSwappedPrefix_action_one (i : Fin 6) :
    wordComp D (centralSwappedPrefix i) (S i) (1 : P) = 0 := by
  have hne : (⟨j i, by have := centralSwapIndex_lt i; omega⟩ : Fin N) ≠
      ⟨j i+1, centralSwapIndex_lt i⟩ := by
    intro h
    have eq : j i = j i + 1 := congrArg (fun z : Fin N => z.val) h
    omega
  rw [centralSwappedPrefix_action Λ, map_one, ddiff_eq_zero_of_rename_eq hne (map_one _), map_zero]

theorem centralSwappedPrefix_action_first (i : Fin 6) :
    wordComp D (centralSwappedPrefix i) (S i) (X (firstBlack (S i)) : P) = 1 := by
  have hne : (⟨j i, by have := centralSwapIndex_lt i; omega⟩ : Fin N) ≠
      ⟨j i+1, centralSwapIndex_lt i⟩ := by
    intro h
    have eq : j i = j i + 1 := congrArg (fun z : Fin N => z.val) h
    omega
  rw [centralSwappedPrefix_action Λ, rename_X, centralBeforeSwap_first, ddiff_X_left hne, map_one]

end Polynomial


section Finish
variable {k : Type} [CommRing k] (Λ : Fin 3 → Unit →₀ ℕ)
local notation "P" => MvPolynomial (Fin N) k
local notation "D" => sortedFlagP (k := k) Λ
local notation "i₃" => (⟨3, by decide⟩ : Fin N)
local notation "i₄" => (⟨4, by decide⟩ : Fin N)

def centralFinishExponent (Λ : Fin 3 → Unit →₀ ℕ) : Fin 3 → ℕ
  | 0 => Λ 1 () + Λ 2 ()
  | 1 => Λ 2 ()
  | _ => 0

private theorem central_finish_crossComp (s : Seq weight) (j : ℕ) (h : j+1<N)
    (r : Fin 3) (hb : s.lbl ⟨j,by omega⟩=.inl ()) (hr : s.lbl ⟨j+1,h⟩=.inr r) (f : P) :
    crossComp D j h s f = X (⟨j+1,h⟩ : Fin N)^(Λ r ())*rename (sadj N j) f := by
  simp only [crossComp,hb,hr,reduceCtorEq,↓reduceIte,sortedFlagP,map_pow,rename_X,
    Matrix.cons_val_one,Matrix.cons_val_zero,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]

private theorem central_finish_first (f : P) :
    wordComp D [2] E₀ f = X i₃^(Λ 1 ())*rename (wordProd N [2]) f := by
  rw [wordComp,dite_eq_left (by decide : 2+1<N)]
  simp only [LinearMap.comp_apply,wordComp,LinearMap.id_apply,wordProd_nil,one_smul,wordProd_cons,mul_one]
  exact central_finish_crossComp Λ E₀ 2 (by decide) 1 (by decide) (by decide) f

private theorem central_finish_two (f : P) :
    wordComp D [3,2] E₀ f = X i₄^(Λ 1 ()+Λ 2 ())*rename (wordProd N [3,2]) f := by
  rw [wordComp,dite_eq_left (by decide : 3+1<N),LinearMap.comp_apply,central_finish_first,
    central_finish_crossComp Λ _ 3 (by decide) 2 (by decide) (by decide),map_mul (rename (sadj N 3)),
    map_pow (rename (sadj N 3)),rename_X,rename_rename,
    show sadj N 3 i₃=i₄ by decide]
  rw [← mul_assoc ((X i₄ : P)^(Λ 2 ())), ← pow_add, Nat.add_comm (Λ 2 ()) (Λ 1 ())]
  have hp : (⇑(sadj N 3) ∘ ⇑(wordProd N [2])) = (wordProd N [3,2] : Fin N → Fin N) := by
    rw [wordProd_cons]
    rfl
  rw [hp]

private theorem central_finish_one (f : P) :
    wordComp D [3] jA f = X i₄^(Λ 2 ())*rename (wordProd N [3]) f := by
  rw [wordComp,dite_eq_left (by decide : 3+1<N)]
  simp only [LinearMap.comp_apply,wordComp,LinearMap.id_apply,wordProd_nil,one_smul,wordProd_cons,mul_one]
  exact central_finish_crossComp Λ jA 3 (by decide) 2 (by decide) (by decide) f

theorem centralFinish_action (i : Fin 3) (f : P) :
    wordComp D (centralFinishWord i) (H i) f =
      X i₄ ^ centralFinishExponent Λ i * rename (wordProd N (centralFinishWord i)) f := by
  fin_cases i
  · exact central_finish_two Λ f
  · exact central_finish_one Λ f
  · change f = X i₄ ^ (0 : ℕ) * rename (wordProd N []) f
    simp [wordProd]

private theorem centralFinish_first_fixed (i : Fin 3) :
    wordProd N (centralFinishWord i) i₁ = i₁ := by
  fin_cases i <;> decide

theorem centralStableWord_action_one (i : Fin 6) :
    wordComp D (a i) (S i) (1 : P) = X i₄ ^ centralFinishExponent Λ (centralStableIntermediate i) := by
  rw [centralStableWord, centralWordComp_append Λ, centralStablePrefix_top,
    centralStablePrefix_action_one Λ, centralFinish_action Λ, map_one, mul_one]

theorem centralStableWord_action_first (i : Fin 6) :
    wordComp D (a i) (S i) (X (firstBlack (S i)) : P) =
      X i₄ ^ centralFinishExponent Λ (centralStableIntermediate i) * X i₁ := by
  rw [centralStableWord, centralWordComp_append Λ, centralStablePrefix_top,
    centralStablePrefix_action_first Λ, centralFinish_action Λ, rename_X, centralFinish_first_fixed]

theorem centralSwappedWord_action_one (i : Fin 6) :
    wordComp D (b i) (S i) (1 : P) = 0 := by
  rw [centralSwappedWord, centralWordComp_append Λ, centralSwappedPrefix_action_one Λ, map_zero]

theorem centralSwappedWord_action_first (i : Fin 6) :
    wordComp D (b i) (S i) (X (firstBlack (S i)) : P) =
      X i₄ ^ centralFinishExponent Λ (centralSwappedIntermediate i) := by
  rw [centralSwappedWord, centralWordComp_append Λ, centralSwappedPrefix_top,
    centralSwappedPrefix_action_first Λ, centralFinish_action Λ, map_one, mul_one]

end Finish


section Readout
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "P" => MvPolynomial (Fin N) k
local notation "i₄" => (⟨4, by decide⟩ : Fin N)
local notation "δ" => centralFinishExponent Λ

/-- The two polynomial tests read the stable and the swapped PBW coefficient
after their respective final rightward red crossings. -/
theorem centralWords_readout (i : Fin 6) (f g : P)
    (z : R)
    (hz : z = pol f * (ψw (a i) * e (S i)) + pol g * (ψw (b i) * e (S i))) :
    let a₀ := (X i₄ : P) ^ δ (centralStableIntermediate i)
    let b₀ := (X i₄ : P) ^ δ (centralSwappedIntermediate i)
    polyRep (sortedFlagP_factor Q Λ) z (Pi.single (S i) 1) E₁ = f * a₀ ∧
      polyRep (sortedFlagP_factor Q Λ) z (Pi.single (S i) (X (firstBlack (S i)))) E₁ =
        f * (a₀ * X i₁) + g * b₀ := by
  have ha : wordProd N (a i) • S i = E₁ := by fin_cases i <;> decide +kernel
  have hb : wordProd N (b i) • S i = E₁ := by fin_cases i <;> decide +kernel
  have eval (p : P) :
      polyRep (sortedFlagP_factor Q Λ) z (Pi.single (S i) p) E₁ =
        f * wordComp (sortedFlagP Λ) (a i) (S i) p +
          g * wordComp (sortedFlagP Λ) (b i) (S i) p := by
    rw [hz, map_add (polyRep (sortedFlagP_factor Q Λ)), LinearMap.add_apply, Pi.add_apply,
      eval_supported_term Q Λ (sortedFlagP_factor Q Λ) (S i) E₁ (a i) ha,
      eval_supported_term Q Λ (sortedFlagP_factor Q Λ) (S i) E₁ (b i) hb]
  constructor
  · rw [eval, centralStableWord_action_one Λ, centralSwappedWord_action_one Λ, mul_zero, add_zero]
  · rw [eval, centralStableWord_action_first Λ, centralSwappedWord_action_first Λ]

end Readout


section Reflection
open TwoBlackFlag

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "P" => MvPolynomial (Fin N) k
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "i₂" => (⟨2, by decide⟩ : Fin N)
local notation "i₃" => (⟨3, by decide⟩ : Fin N)
local notation "i₄" => (⟨4, by decide⟩ : Fin N)
local notation "m" => Λ 0 ()
local notation "n" => m + (Λ 1 () + Λ 2 ())
local notation "J" => TwoBlackFlag.ideal (k := k) i₁ i₄ m n
local notation "p" => fun i => wordProd N (centralFinishWord i)

private def centralFinishSecond : Fin 3 → Fin N
  | 0 => i₂
  | 1 => i₃
  | _ => i₄

private def centralIntermediateBound (Λ : Fin 3 → Unit →₀ ℕ) : Fin 3 → ℕ
  | 0 => Λ 0 ()
  | 1 => Λ 0 () + Λ 1 ()
  | _ => Λ 0 () + (Λ 1 () + Λ 2 ())

private theorem centralFinish_top (i : Fin 3) : (p i) • H i = E₁ := by
  fin_cases i <;> decide +kernel

private theorem centralFinish_second (i : Fin 3) : (p i) (centralFinishSecond i) = i₄ := by
  fin_cases i <;> decide +kernel

private theorem centralIntermediateBound_le (i : Fin 3) : m ≤ centralIntermediateBound Λ i := by
  fin_cases i <;> simp [centralIntermediateBound]

private theorem centralFinish_bound (i : Fin 3) :
    centralIntermediateBound Λ i + centralFinishExponent Λ i = n := by
  fin_cases i <;> simp [centralIntermediateBound, centralFinishExponent, Nat.add_assoc]

private theorem centralFinish_pullback (i : Fin 3) (f : P)
    (hf : f * (X i₄)^centralFinishExponent Λ i ∈ J) :
    rename ((p i)⁻¹ : Perm (Fin N)) f ∈
      TwoBlackFlag.ideal i₁ (centralFinishSecond i) m (centralIntermediateBound Λ i) := by
  have h : f * (X i₄)^centralFinishExponent Λ i ∈
      TwoBlackFlag.ideal i₁ i₄ m (centralIntermediateBound Λ i + centralFinishExponent Λ i) := by
    rw [centralFinish_bound Λ i]
    exact hf
  have hm := (mul_second_pow_mem_iff (by decide : i₁ ≠ i₄)
    (centralIntermediateBound_le Λ i) _ _).1 h
  have ha := rename_mem ((p i)⁻¹ : Perm (Fin N)) hm
  have ha₁ : (p i)⁻¹ i₁ = i₁ := calc
    _ = (p i)⁻¹ ((p i) i₁) := congrArg (((p i)⁻¹ : Perm (Fin N)) : Fin N → Fin N) (centralFinish_first_fixed i).symm
    _ = _ := (p i).symm_apply_apply _
  have ha₂ : (p i)⁻¹ i₄ = centralFinishSecond i := calc
    _ = (p i)⁻¹ ((p i) (centralFinishSecond i)) :=
      congrArg (((p i)⁻¹ : Perm (Fin N)) : Fin N → Fin N) (centralFinish_second i).symm
    _ = _ := (p i).symm_apply_apply _
  rwa [ha₁, ha₂] at ha

private theorem centralIntermediate_flag_kills (i : Fin 3) (f : P)
    (hf : f ∈ TwoBlackFlag.ideal i₁ (centralFinishSecond i) m (centralIntermediateBound Λ i)) :
    F (pol f * e (H i)) = 0 := by
  fin_cases i
  · exact fiveSlotLeftExtreme_flagIdeal_kills Q Λ hf
  · exact fiveSlotNearby_flagIdeal_kills Q Λ hf
  · exact fiveSlotCentral_flagIdeal_kills Q Λ hf

private theorem centralSlide_step (j : ℕ) (hj : j+1<N) (s : Seq weight)
    (hne : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j+1,hj⟩) (f : P)
    (z : R) (hz : e s * z = z) :
    ψ j * (pol f * z) = pol (swapPol j hj f) * (ψ j * z) := by
  have h := ψ_mul_pol_mul_e (Q := stendhalQ Q Λ) j hj s f
  rw [ite_eq_right hne, add_zero] at h
  simpa only [mul_assoc, hz] using congrArg (· * z) h

private theorem centralFinish_slide (i : Fin 3) (f : P) :
    (ψw (centralFinishWord i) : R) * (pol f * e (H i)) =
      pol (rename (p i) f) * (ψw (centralFinishWord i) * e (H i)) := by
  fin_cases i
  · have cut : (e jA : R) * (ψ 2 * e E₀) = ψ 2 * e E₀ := by
      rw [← mul_assoc, e_mul_ψ, show sadj N 2 • jA = E₀ by decide, mul_assoc, e_mul_self]
    change (ψw [3,2] : R) * (pol f * e E₀) =
      pol (rename (wordProd N [3,2]) f) * (ψw [3,2] * e E₀)
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
    rw [centralSlide_step Q Λ 2 (by decide) E₀ (by decide) f (e E₀) (e_mul_self _),
      centralSlide_step Q Λ 3 (by decide) jA (by decide) _ _ cut]
    simp only [swapPol, rename_rename]
    rfl
  · change (ψw [3] : R) * (pol f * e jA) =
      pol (rename (wordProd N [3]) f) * (ψw [3] * e jA)
    simp only [ψw_cons, ψw_nil, mul_one]
    rw [centralSlide_step Q Λ 3 (by decide) jA (by decide) f (e jA) (e_mul_self _)]
    rfl
  · simp [centralFinishWord, wordProd]

private theorem centralTerm_kill (hQ : KLRSymm Q) (i : Fin 3) (s : Seq weight)
    (front : List ℕ) (hfront : wordProd N front • s = H i)
    (f : P) (hf : blackEval E₁ f * (X i₄)^centralFinishExponent Λ i ∈ J) :
    F (pol f * (ψw (centralFinishWord i ++ front) * e s)) = 0 := by
  let z : R := ψw front * e s
  have hleft : (e (H i) : R) * z = z := by
    change (e (H i) * (ψw front * e s) : R) = ψw front * e s
    rw [← hfront, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  have htop : (e E₁ : R) * (ψw (centralFinishWord i) * z) = ψw (centralFinishWord i) * z := by
    rw [← centralFinish_top i, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, hleft]
  let g := rename ((p i)⁻¹ : Perm (Fin N)) (blackEval E₁ f)
  have hk := centralIntermediate_flag_kills Q Λ i g (centralFinish_pullback Λ i (blackEval E₁ f) hf)
  have hrename : rename (p i) g = blackEval E₁ f := by
    change rename (p i) (rename ((p i)⁻¹ : Perm (Fin N)) (blackEval E₁ f)) = blackEval E₁ f
    rw [rename_rename, show ((p i : Fin N → Fin N) ∘ (((p i)⁻¹ : Perm (Fin N)) : Fin N → Fin N)) = id from
      (p i).self_comp_symm, rename_id]
    rfl
  have h := congrArg (· * z) (centralFinish_slide Q Λ i g)
  simp only [mul_assoc, hleft, hrename] at h
  have red : F (pol f * e E₁) = F (pol (blackEval E₁ f) * e E₁) := by
    have hh := congrArg (ofKLR k Q Λ ν₀) (toKLR_ofKLR_pol_mul_e (Q := Q) (Λ := Λ) f E₁)
    rw [ofKLR_toKLR hQ] at hh
    exact congrArg (violMk k Q Λ ν₀) hh
  change F (pol f * (ψw (centralFinishWord i ++ front) * e s)) = 0
  rw [ψw_append, mul_assoc (ψw _)]
  change F (pol f * (ψw (centralFinishWord i) * z)) = 0
  calc
    _ = F (pol f * e E₁) * F (ψw (centralFinishWord i) * z) := by
      rw [← map_mul, mul_assoc, htop]
    _ = F (pol (blackEval E₁ f) * (ψw (centralFinishWord i) * z)) := by
      rw [red, ← map_mul, mul_assoc, htop]
    _ = F ((ψw (centralFinishWord i) * (pol g * e (H i))) * z) := by
      apply congrArg F
      simpa only [mul_assoc, hleft] using h.symm
    _ = 0 := by rw [map_mul, map_mul, hk, mul_zero, zero_mul]

/-- In the fixed red-order corner, the central polynomial flag tests reflect
vanishing of the diagram. -/
theorem central_eq_zero_of_flagEvaluation (hQ : KLRSymm Q) (s : Seq weight)
    (order : redWord s = redWord E₀) (z : R) (left : e E₁ * z = z) (right : z * e s = z)
    (test : ∀ f : P, blackEval E₁ (polyRep (sortedFlagP_factor Q Λ) z (Pi.single s f) E₁) ∈ J) :
    F z = 0 := by
  by_cases hv : IsViolated s
  · rw [← right, map_mul, show F (e s) = 0 from violMk_e hv, mul_zero]
  obtain ⟨i, rfl⟩ := centralBottomLoading_cases s order hv
  obtain ⟨ha, hb, hne, hmatch⟩ := centralWords_spec i
  obtain ⟨f,g,hfg⟩ := exists_two_corner_coefficients_of_words
    (stendhalQ_symm Q Λ hQ) (S i) E₁ (a i) (b i) ha hb hne hmatch z left right
  obtain ⟨h₁,h₂⟩ := centralWords_readout Q Λ i f g z hfg
  have b₁ : ((E₁).lbl i₁).isLeft = true := by decide
  have b₄ : ((E₁).lbl i₄).isLeft = true := by decide
  have hf : blackEval E₁ f * (X i₄)^centralFinishExponent Λ (centralStableIntermediate i) ∈ J := by
    have h := test 1
    rw [h₁, map_mul (blackEval E₁), map_pow (blackEval E₁), blackEval_X, ite_eq_left b₄] at h
    exact h
  have hg : blackEval E₁ g * (X i₄)^centralFinishExponent Λ (centralSwappedIntermediate i) ∈ J := by
    have h := test (X (firstBlack (S i)))
    rw [h₂] at h
    simp only [map_add (blackEval E₁), map_mul (blackEval E₁), map_pow (blackEval E₁),
      blackEval_X, ite_eq_left b₁, ite_eq_left b₄, ← mul_assoc] at h
    have hd := (J).sub_mem h ((J).mul_mem_right (X i₁) hf)
    simpa only [add_sub_cancel_left] using hd
  rw [hfg, map_add, centralStableWord, centralSwappedWord, centralTerm_kill Q Λ hQ _ _ _ (centralStablePrefix_top i) f hf,
    centralTerm_kill Q Λ hQ _ _ _ (centralSwappedPrefix_top i) g hg, zero_add]

end Reflection


section FirstCrossing
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "P" => MvPolynomial (Fin N) k
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "D" => sortedFlagP (k := k) Λ
local notation "A" => polyRep (sortedFlagP_factor Q Λ)
local notation "i₂" => (⟨2, by decide⟩ : Fin N)
local notation "i₃" => (⟨3, by decide⟩ : Fin N)
local notation "i₄" => (⟨4, by decide⟩ : Fin N)
local notation "m" => Λ 0 ()
local notation "d" => Λ 1 () + Λ 2 ()
local notation "w" => wordProd N [2,1]
local notation "J" => TwoBlackFlag.ideal (k := k) i₁ i₄ m (m+d)

private theorem rightmostFirst_step (f : P) :
    wordComp D [1] E₁ f = X i₂^(Λ 1 ())*rename (wordProd N [1]) f := by
  rw [wordComp,dite_eq_left (by decide : 1+1<N)]
  simp only [LinearMap.comp_apply,wordComp,LinearMap.id_apply,wordProd_nil,one_smul,wordProd_cons,mul_one]
  exact central_finish_crossComp Λ E₁ 1 (by decide) 1 (by decide) (by decide) f

private theorem rightmostFirst_wordComp (f : P) :
    wordComp D [2,1] E₁ f = X i₃^d * rename w f := by
  rw [wordComp, dite_eq_left (by decide : 2+1<N), LinearMap.comp_apply, rightmostFirst_step,
    central_finish_crossComp Λ _ 2 (by decide) 2 (by decide) (by decide),
    map_mul (rename (sadj N 2)), map_pow (rename (sadj N 2)), rename_X, rename_rename,
    show sadj N 2 i₂=i₃ by decide]
  rw [← mul_assoc ((X i₃ : P)^(Λ 2 ())), ← pow_add, Nat.add_comm (Λ 2 ()) (Λ 1 ())]
  have hp : (⇑(sadj N 2) ∘ ⇑(wordProd N [1])) = (w : Fin N → Fin N) := by
    rw [wordProd_cons]
    rfl
  rw [hp]

private theorem rightmostFirst_ideal :
    loadingIdeal (k := k) Λ E₂ = TwoBlackFlag.ideal i₃ i₄ (m+d) (m+d) := by
  unfold loadingIdeal flagBound
  rw [show redsBefore E₂ (firstBlack E₂) = Finset.univ by decide,
    show redsBefore E₂ (secondBlack E₂) = Finset.univ by decide,
    show firstBlack E₂=i₃ by decide, show secondBlack E₂=i₄ by decide, Fin.sum_univ_three, Nat.add_assoc]

private theorem rightmostFirst_flag_test (z : R) (hz : F ((ψw [2,1]*e E₁)*z)=0)
    (input : Pol k weight) : blackEval E₁ (A z input E₁) ∈ J := by
  let g := A z input
  have cut : opE E₁ g=Pi.single E₁ (g E₁) := by
    funext u
    rw [opE_apply,Pi.single_apply]
  have top : w • E₁=E₂ := by decide
  have h := eval_mem_sorted_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesSortedFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz input E₂
  rw [map_mul A,map_mul A,polyRep_ψw,polyRep_e,Module.End.mul_apply,Module.End.mul_apply,
    show opE E₁ (A z input)=Pi.single E₁ (g E₁) from cut,opΨw_single,top,Pi.single_eq_same,
    rightmostFirst_wordComp Λ,rightmostFirst_ideal Λ] at h
  have same (f : P) : blackEval E₂ (rename w f)=rename w (blackEval E₁ f) := by
    rw [← top,blackEval_rename_perm]
  have b₃ : ((E₂).lbl i₃).isLeft = true := by decide
  rw [map_mul (blackEval E₂), map_pow (blackEval E₂), blackEval_X, ite_eq_left b₃, same,
    mul_comm ((X i₃)^d)] at h
  have small := (TwoBlackFlag.mul_first_pow_mem_iff (by decide : i₃≠i₄) m (m+d) d _).1 h
  have back := TwoBlackFlag.rename_mem (w⁻¹ : Perm (Fin N)) small
  rw [show w⁻¹ i₃=i₁ by decide, show w⁻¹ i₄=i₄ by decide, rename_rename,
    show ((w⁻¹ : Perm (Fin N)) ∘ (w : Perm (Fin N)))=id from (w).symm_comp_self, rename_id] at back
  exact back

/-- The first crossing map from the central loading into the rightmost loading
is injective on the fixed right red-order component. -/
theorem fiveSlotRightmost_firstCrossing_cancel_on_orderCorner (hQ : KLRSymm Q)
    (y : V) (left : F (e E₁)*y=y) (right : y*F (redIdem k Q Λ (redWord E₀))=y)
    (zero : F (ψw [2,1]*e E₁)*y=0) : y=0 := by
  classical
  obtain ⟨x,hx⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp (ofKLR_surjective (Q := Q) (Λ := Λ)) y
  have vanish (s : Seq weight) (hs : redWord s=redWord E₀) : y*F (e s)=0 := by
    let z : R := e E₁*x*e s
    have image : F z=y*F (e s) := by
      change F (e E₁*x*e s)=_
      rw [map_mul,map_mul,show F x=y from hx,left]
    have hz : F ((ψw [2,1]*e E₁)*z)=0 := by rw [map_mul,image,← mul_assoc,zero,zero_mul]
    rw [← image]
    apply central_eq_zero_of_flagEvaluation Q Λ hQ s hs z
      (by simp only [z,← mul_assoc,e_mul_self]) (by simp only [z,mul_assoc,e_mul_self])
    exact fun f => rightmostFirst_flag_test Q Λ z hz (Pi.single s f)
  calc
    y = y * F (redIdem k Q Λ (redWord E₀)) := right.symm
    _ = 0 := by
      rw [redIdem, map_sum, Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro s hs
      exact vanish s (Finset.mem_filter.mp hs).2

end FirstCrossing

end Categorification.Stendhal.FiveSlotFlag
