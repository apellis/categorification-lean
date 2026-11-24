/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotExtremeCrossing
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopCancellation

/-!
# The two principal five-slot columns at arbitrary bottoms

For the two one-before-pair upper loadings in Webster, arXiv:1309.3796v2,
§6.1, proof of Lemma 6.8 after (6.21), the principal diagram from the
left extreme crosses the second black past one or both exchanged reds.
These words act injectively on the whole supported right ideal after global
violation, over any commutative ring and for arbitrary red pairings.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv FiveSlotFlag TwoBlackFlag
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "N" => weight.card
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fixedTopFourExitCut 1
local notation "jA" => sadj N 2 • E₀
local notation "i₁" => (⟨1,by decide⟩ : Fin N)
local notation "i₂" => (⟨2,by decide⟩ : Fin N)
local notation "i₃" => (⟨3,by decide⟩ : Fin N)
local notation "i₄" => (⟨4,by decide⟩ : Fin N)
local notation "C₀" => Λ 0 ()
local notation "A₀" => Λ 1 ()
local notation "B₀" => Λ 2 ()
local notation "P" => MvPolynomial (Fin N) k
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "D" => sortedFlagP (k := k) Λ

private theorem sorter_cross (s : Seq weight) (j : ℕ) (h : j+1<N) (r : Fin 3)
    (hb : s.lbl ⟨j,by omega⟩=.inl ()) (hr : s.lbl ⟨j+1,h⟩=.inr r) (p : P) :
    crossComp D j h s p=X (⟨j+1,h⟩ : Fin N)^(Λ r ())*rename (sadj N j) p := by
  simp only [crossComp,hb,hr,reduceCtorEq,↓reduceIte,sortedFlagP,map_pow,rename_X,
    Matrix.cons_val_one,Matrix.cons_val_zero,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]

private theorem near_word (p : P) :
    wordComp D [2] E₀ p=X i₃^A₀*rename (wordProd N [2]) p := by
  rw [wordComp,dite_eq_left (by decide : 2+1<N)]
  simp only [LinearMap.comp_apply,wordComp,LinearMap.id_apply,wordProd_nil,one_smul,wordProd_cons,mul_one]
  exact sorter_cross Λ E₀ 2 (by decide) 1 (by decide) (by decide) p

private theorem central_word (p : P) :
    wordComp D [3,2] E₀ p=X i₄^(A₀+B₀)*rename (wordProd N [3,2]) p := by
  rw [wordComp,dite_eq_left (by decide : 3+1<N),LinearMap.comp_apply,near_word,
    sorter_cross Λ _ 3 (by decide) 2 (by decide) (by decide),map_mul (rename (sadj N 3)),map_pow (rename (sadj N 3)),rename_X,rename_rename,
    show sadj N 3 i₃=i₄ by decide,pow_add]
  change X i₄^B₀*(X i₄^A₀*rename (wordProd N [3,2]) p)=_
  ring

private theorem near_ideal :
    loadingIdeal (k := k) Λ jA=ideal i₁ i₃ C₀ (C₀+A₀) := by
  have h₁ : redsBefore jA (firstBlack jA)={0} := by decide
  have h₂ : redsBefore jA (secondBlack jA)={0,1} := by decide
  unfold loadingIdeal flagBound
  rw [h₁,h₂,show firstBlack jA=i₁ by decide,show secondBlack jA=i₃ by decide,Finset.sum_singleton,
    Finset.sum_pair (by decide : (0 : Fin 3)≠1)]

private theorem central_ideal :
    loadingIdeal (k := k) Λ E₁=ideal i₁ i₄ C₀ (C₀+(A₀+B₀)) := by
  have h₁ : redsBefore E₁ (firstBlack E₁)={0} := by decide
  have h₂ : redsBefore E₁ (secondBlack E₁)=Finset.univ := by decide
  unfold loadingIdeal flagBound
  rw [h₁,h₂,show firstBlack E₁=i₁ by decide,show secondBlack E₁=i₄ by decide,
    Finset.sum_singleton,Fin.sum_univ_three,Nat.add_assoc]

/-- Crossing both exchanged reds is injective on the whole left-extreme
right ideal of the globally violated algebra. -/
theorem fiveSlotCentral_leftWord_cancel_of_leftSupport (hQ : KLRSymm Q)
    (y : V) (left : F (e E₀)*y=y) (zero : F (ψw [3,2]*e E₀)*y=0) : y=0 := by
  apply leftWord_cancel_of_second_flag_push Q Λ hQ [3,2] E₁ (A₀+B₀) (by decide) _ _ y left zero
  · rw [show wordProd N [3,2] i₁=i₁ by decide,show wordProd N [3,2] i₂=i₄ by decide]
    exact central_ideal Λ
  · rw [show wordProd N [3,2] i₂=i₄ by decide]
    exact central_word Λ

/-- Crossing the first exchanged red is injective on the same full right ideal. -/
theorem fiveSlotNearby_leftWord_cancel_of_leftSupport (hQ : KLRSymm Q)
    (y : V) (left : F (e E₀)*y=y) (zero : F (ψ 2*e E₀)*y=0) : y=0 := by
  apply leftWord_cancel_of_second_flag_push Q Λ hQ [2] jA A₀ (by decide) _ _ y left
    (by simpa only [ψw_cons,ψw_nil,mul_one] using zero)
  · rw [show wordProd N [2] i₁=i₁ by decide,show wordProd N [2] i₂=i₃ by decide]
    exact near_ideal Λ
  · rw [show wordProd N [2] i₂=i₃ by decide]
    exact near_word Λ

/-- Both principal higher-ideal upper loadings have injective balanced
kernel columns at every bottom loading, independently of its red order. -/
theorem fiveSlot_oneBlackBeforePair_columnInclusion (hQ : KLRSymm Q) (t s : Seq weight)
    (ht : t=E₁ ∨ t=jA) : Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 s) := by
  rcases ht with rfl|rfl
  · apply fiveSlotCentral_columnInclusion_of_leftCancellation Q Λ hQ s
    intro y hc hz
    apply fiveSlotCentral_leftWord_cancel_of_leftSupport Q Λ hQ y _ hz
    have h := congrArg (F (e E₀)*·) hc
    have sq : F (e E₀)*F (e E₀)=F (e E₀) := by rw [← map_mul,e_mul_self]
    change F (e E₀)*(F (e E₀)*y*F (e s))=F (e E₀)*y at h
    rw [← mul_assoc (F (e E₀)),← mul_assoc (F (e E₀)),sq,hc] at h
    exact h.symm
  · apply fiveSlot_jA_blockKernelColumnInclusion_injective_of_leftCancellation Q Λ hQ s
    exact fun y hl _ hz => fiveSlotNearby_leftWord_cancel_of_leftSupport Q Λ hQ y hl hz

end Categorification.Stendhal.BraidedStendhalAlgebra
