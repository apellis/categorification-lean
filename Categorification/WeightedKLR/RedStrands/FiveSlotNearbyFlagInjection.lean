/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagSource
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagStability
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopCancellation


/-!
# Nearby left cancellation from the positional flag representation

The left-extreme bottom corner has two reduced polynomial rows. At the
nearby top `[0,i,1,i,2]`, the flag representation tests them on `1` and the
first bottom black variable. After the crossing, both tests have a common
power of the second upper black variable. Reflection of that power between
the two flag ideals detects zero in the left-extreme corner and proves the
marked tensor inclusion.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv TwoBlackFlag
variable {k : Type} [CommRing k]
  {D : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) k}
  (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "P" => MvPolynomial (Fin N) k
local notation "bot" => fixedTopFourExitBottom
local notation "v₀" => fixedTopFourExitCut 0
local notation "jA" => sadj N 2 • v₀
local notation "a₁" => (⟨1,by decide⟩ : Fin N)
local notation "a₂" => (⟨2,by decide⟩ : Fin N)
local notation "a₃" => (⟨3,by decide⟩ : Fin N)
local notation "a₄" => (⟨4,by decide⟩ : Fin N)
local notation "w" => wordProd N [3,2,1]
local notation "τ" => sadj N 2

private theorem near_cross_unit (s : Seq μ₀) (j : ℕ) (h : j+1<N)
    (unequal : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+1,h⟩)
    (unit : D (s.lbl ⟨j,by omega⟩) (s.lbl ⟨j+1,h⟩)=1) (p : P) :
    crossComp D j h s p = rename (sadj N j) p := by
  simp only [crossComp,unequal,↓reduceIte,unit,map_one,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply,one_mul]

private theorem near_extreme_word
    (hrb : D (.inr 2) (.inl ())=1) (hrr : D (.inr 2) (.inr 1)=1) (p : P) :
    wordComp D [3,2,1] bot p = rename w p := by
  let s₁ := wordProd N [1] • bot
  let s₂ := wordProd N [2,1] • bot
  have h₁ : ∀ z : P, crossComp D 1 (by decide) bot z=rename (sadj N 1) z := by
    intro z
    exact near_cross_unit bot 1 (by decide) (by decide) hrb z
  have h₂ : ∀ z : P, crossComp D 2 (by decide) s₁ z=rename (sadj N 2) z := by
    intro z
    exact near_cross_unit s₁ 2 (by decide) (by decide) hrb z
  have h₃ : ∀ z : P, crossComp D 3 (by decide) s₂ z=rename (sadj N 3) z := by
    intro z
    exact near_cross_unit s₂ 3 (by decide) (by decide) hrr z
  simp only [wordComp,show 3+1<N by decide,show 2+1<N by decide,show 1+1<N by decide,
    ↓reduceDIte,LinearMap.comp_apply,LinearMap.id_apply,wordProd_nil,one_smul]
  rw [h₁,h₂,h₃,rename_rename,rename_rename]
  rfl

private theorem near_extreme_word_reversed
    (hrb : D (.inr 2) (.inl ())=1) (hrr : D (.inr 2) (.inr 1)=1) (p : P) :
    wordComp D [1,3,2,1] bot p = ddiff a₁ a₂ (rename w p) := by
  rw [wordComp, dite_eq_left (by decide : 1+1<N)]
  simp only [LinearMap.comp_apply]
  rw [near_extreme_word hrb hrr,show w • bot=v₀ by decide,crossComp,ite_eq_left (by decide)]

private theorem near_cross_final
    (hbr : D (.inl ()) (.inr 1)=X 1^(Λ 1 ())) (p : P) :
    crossComp D 2 (by decide) v₀ p = (X a₃)^(Λ 1 ()) * rename τ p := by
  have l : (v₀).lbl a₂=.inl () := by decide
  have r : (v₀).lbl a₃=.inr 1 := by decide
  simp only [crossComp,l,r,reduceCtorEq,↓reduceIte,hbr,map_pow,rename_X,Matrix.cons_val_one,
    Matrix.cons_val_zero,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]

variable (Q : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "C₀" => Λ 0 ()
local notation "A₀" => Λ 1 ()
local notation "J" => TwoBlackFlag.ideal (k := k) a₁ a₃ C₀ (C₀+A₀)
local notation "L" => fun (l : List ℕ) => (ψw l*e bot : R)
local notation "leg" => (ψ 2*e v₀ : R)

private theorem near_eval_coefficient (f : P) :
    blackEval jA (rename τ f)=rename τ (blackSubst v₀ f) := by
  have h := blackEval_rename_perm v₀ τ f
  exact h

private theorem near_reflect_flag {f : P}
    (hf : rename τ f*(X a₃)^A₀ ∈ J) : f ∈ TwoBlackFlag.ideal a₁ a₂ C₀ C₀ := by
  have h := (mul_second_pow_mem_iff (by decide : a₁≠a₃) (le_refl C₀) A₀ (rename τ f)).1 hf
  have back := rename_mem (τ⁻¹ : Perm (Fin N)) h
  rw [show τ⁻¹ a₁=a₁ by decide,show τ⁻¹ a₃=a₂ by decide,rename_rename,
    show ((τ⁻¹ : Perm (Fin N)) ∘ (τ : Perm (Fin N)))=id from (τ).symm_comp_self,rename_id] at back
  exact back

private theorem near_tested
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (p f : P) (l : List ℕ) (ht : wordProd N l • bot=v₀) :
    polyRep hPQ (leg*(pol f*L l)) (Pi.single bot p) jA =
      crossComp D 2 (by decide) v₀ (f*wordComp D l bot p) := by
  have cut : opE bot (Pi.single bot p)=Pi.single bot p := by
    funext s
    rw [opE_apply]
    simp only [Pi.single_apply]
    split_ifs <;> rfl
  let y := polyRep hPQ (pol f*L l) (Pi.single bot p)
  have value : y v₀=f*wordComp D l bot p := by
    dsimp only [y]
    rw [map_mul,map_mul,polyRep_pol,polyRep_ψw,polyRep_e,Module.End.mul_apply,
      Module.End.mul_apply,cut,opMul_apply,opΨw_single,ht,Pi.single_eq_same]
  rw [map_mul,Module.End.mul_apply]
  change polyRep hPQ leg y jA = _
  rw [map_mul,polyRep_ψ,polyRep_e,Module.End.mul_apply,opΨ_apply _ _ (by decide),
    sadj_smul_smul,opE_apply,ite_eq_left rfl,value]

set_option maxHeartbeats 800000 in
theorem fiveSlotNearby_affineRows_reflect_of_flagAction
    (hQ : KLRSymm Q)
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (hrb : D (.inr 2) (.inl ())=1) (hbr : D (.inl ()) (.inr 1)=X 1^A₀)
    (hrr : D (.inr 2) (.inr 1)=1)
    (desc : ∀ z : R, F z=0 → ∀ p : P, blackEval jA (polyRep hPQ z (Pi.single bot p) jA) ∈ J)
    (f g : P)
    (zero : F (leg*(pol f*L [3,2,1]+pol g*L [1,3,2,1]))=0) :
    F (pol f*L [3,2,1]+pol g*L [1,3,2,1])=0 := by
  have test (p : P) := desc _ zero p
  have readings (p : P) :
      blackEval jA ((X a₃)^A₀ * rename τ (f*rename w p)+
        (X a₃)^A₀ * rename τ (g*ddiff a₁ a₂ (rename w p))) ∈ J := by
    have h := test p
    rw [mul_add] at h
    simpa only [map_add,LinearMap.add_apply,Pi.add_apply,
      near_tested Λ Q hPQ _ _ [3,2,1] (by decide),
      near_tested Λ Q hPQ _ _ [1,3,2,1] (by decide),
      near_extreme_word hrb hrr,near_extreme_word_reversed hrb hrr,near_cross_final Λ hbr] using h
  have b₃ : blackEval (k := k) jA (X a₃)=X a₃ := by rw [blackEval_X,ite_eq_left (by decide)]
  have d1 : ddiff a₁ a₂ (1 : P)=0 := ddiff_eq_zero_of_rename_eq (by decide) (map_one _)
  have first : rename τ (blackSubst v₀ f)*(X a₃)^A₀ ∈ J := by
    have h := readings 1
    simp only [map_one,d1,map_zero,mul_one,mul_zero,add_zero,map_mul,map_pow,
      near_eval_coefficient,b₃] at h
    rwa [mul_comm] at h
  have b₁ : blackEval (k := k) jA (X a₁)=X a₁ := by rw [blackEval_X,ite_eq_left (by decide)]
  have src₁ : blackSubst (k := k) v₀ (X a₁)=X a₁ := by rw [blackSubst_X,ite_eq_left (by decide)]
  have second : rename τ (blackSubst v₀ (f*X a₁+g))*(X a₃)^A₀ ∈ J := by
    have h := readings (X a₂)
    simp only [rename_X,show w a₂=a₁ by decide,ddiff_X_left (by decide : a₁≠a₂),mul_one,
      map_add,map_mul,map_pow,near_eval_coefficient,b₃,show τ a₁=a₁ by decide,b₁] at h
    convert h using 1
    simp only [map_add,map_mul,src₁,rename_X,show τ a₁=a₁ by decide]
    ring
  have hf := near_reflect_flag Λ first
  have hfg := near_reflect_flag Λ second
  have hg : blackSubst v₀ g ∈ TwoBlackFlag.ideal a₁ a₂ C₀ C₀ := by
    have hg1 : blackSubst v₀ f * blackSubst v₀ (X a₁) + blackSubst v₀ g ∈
        TwoBlackFlag.ideal a₁ a₂ C₀ C₀ := by
      simpa only [map_add (blackSubst v₀),map_mul (blackSubst v₀)] using hfg
    have minus := (TwoBlackFlag.ideal a₁ a₂ C₀ C₀).sub_mem hg1
      ((TwoBlackFlag.ideal a₁ a₂ C₀ C₀).mul_mem_right (blackSubst v₀ (X a₁)) hf)
    simpa only [add_sub_cancel_left] using minus
  have kill (p : P) (hp : blackSubst v₀ p ∈ TwoBlackFlag.ideal a₁ a₂ C₀ C₀)
      (l : List ℕ) (ht : wordProd N l • bot=v₀) : F (pol p*L l)=0 := by
    have cut : (e v₀ : R)*L l=L l := by
      rw [← ht,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
    have h := fiveSlotLeftExtreme_flagIdeal_kills_blackSubst Q Λ hQ hp
    calc
      _ = F (pol p*e v₀)*F (L l) := by rw [← map_mul,mul_assoc,cut]
      _ = 0 := by rw [h,zero_mul]
  rw [map_add,kill f hf _ (by decide),kill g hg _ (by decide),add_zero]

/-- The exact nearby-left flag test upgrades the reflected affine rows to
cancellation on the actual globally violated bottom corner. -/
theorem fiveSlotNearby_leftCancellation_of_flagAction
    (hQ : KLRSymm Q)
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (hrb : D (.inr 2) (.inl ())=1) (hbr : D (.inl ()) (.inr 1)=X 1^A₀)
    (hrr : D (.inr 2) (.inr 1)=1)
    (desc : ∀ z : R, F z=0 → ∀ p : P, blackEval jA (polyRep hPQ z (Pi.single bot p) jA) ∈ J)
    (y : ViolQuotient k Q Λ ν₀)
    (yl : F (e v₀)*y=y) (yr : y*F (e bot)=y) (hy : F leg*y=0) : y=0 := by
  have surj : Function.Surjective (F : R →ₐ[k] ViolQuotient k Q Λ ν₀) :=
    (violMk_surjective (Q := Q) (Λ := Λ)).comp (ofKLR_surjective (Q := Q) (Λ := Λ))
  obtain ⟨z,hz⟩ := surj y
  let z' : R := e v₀*z*e bot
  have left : e v₀*z'=z' := by
    change e v₀*(e v₀*z*e bot)=e v₀*z*e bot
    rw [← mul_assoc,← mul_assoc,e_mul_self]
  have right : z'*e bot=z' := by
    change e v₀*z*e bot*e bot=e v₀*z*e bot
    rw [mul_assoc,e_mul_self]
  have lifted : F z'=y := by
    change F (e v₀*z*e bot)=y
    rw [map_mul (F),map_mul (F),hz,yl,yr]
  have h₁ : IsReduced N [3,2,1] := by
    refine ⟨by simp [ValidWord,stendhalWeight],?_⟩
    rw [length_eq_invCount]
    decide
  have h₂ : IsReduced N [1,3,2,1] := by
    refine ⟨by simp [ValidWord,stendhalWeight],?_⟩
    rw [length_eq_invCount]
    decide
  obtain ⟨f,g,rows⟩ := exists_two_corner_coefficients_of_words
    (stendhalQ_symm Q Λ hQ) bot v₀ [3,2,1] [1,3,2,1] h₁ h₂ (by decide)
    (by decide +kernel) z' left right
  have zero : F (leg*(pol f*L [3,2,1]+pol g*L [1,3,2,1]))=0 := by
    rw [← rows,map_mul (F),lifted,hy]
  rw [← lifted,rows]
  exact fiveSlotNearby_affineRows_reflect_of_flagAction Λ Q hQ hPQ hrb hbr hrr desc f g zero

open FiveSlotFlag

private theorem nearby_flag_ideal :
    loadingIdeal (k := k) Λ jA = J := by
  have h₁ : redsBefore jA (firstBlack jA)={0} := by decide
  have h₂ : redsBefore jA (secondBlack jA)={0,1} := by decide
  unfold loadingIdeal flagBound
  rw [h₁,h₂,show firstBlack jA=a₁ by decide,
    show secondBlack jA=a₃ by decide,Finset.sum_singleton,Finset.sum_pair (by decide : (0 : Fin 3)≠1)]

/-- The nearby crossing reflects zero on the left-extreme two-interior
bottom corner for every choice of the spectator pairing. -/
theorem fiveSlotNearby_leftCancellation (hQ : KLRSymm Q)
    (y : ViolQuotient k Q Λ ν₀)
    (yl : F (e v₀)*y=y) (yr : y*F (e bot)=y) (hy : F leg*y=0) : y=0 := by
  apply fiveSlotNearby_leftCancellation_of_flagAction Λ Q hQ (flagP_factor Q Λ) rfl rfl
    (by simp [flagP]) ?_ y yl yr hy
  intro z hz p
  rw [← nearby_flag_ideal (k := k) Λ]
  exact eval_mem_flag_of_violMk_eq_zero Q Λ (loadingIdeal Λ)
    (loadingIdeal_preservesFlags Λ) (loadingIdeal_eq_top_of_violated Λ) hz (Pi.single bot p) jA

/-- Webster (6.21) at the nearby left top and the five-slot bottom with
two equal intervening black strands, with unrestricted red pairings. -/
theorem fiveSlotNearby_blockKernelColumnInclusion_injective (hQ : KLRSymm Q) :
    Function.Injective (blockKernelColumnInclusion Q Λ jA 1 2 bot) :=
  fiveSlot_jA_blockKernelColumnInclusion_injective_of_leftCancellation Q Λ hQ bot
    (fiveSlotNearby_leftCancellation Λ Q hQ)

end Categorification.Stendhal.BraidedStendhalAlgebra
