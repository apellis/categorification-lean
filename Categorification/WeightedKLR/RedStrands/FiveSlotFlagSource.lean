/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoBlackFlagIdeal
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralHigher

/-!
# The two flag relations on the left-extreme loading

For the five-slot column of Webster, arXiv:1309.3796v2, §6.1, proof of
Lemma 6.8 after (6.21), the first black dot satisfies the spectator's
cyclotomic relation. Its divided difference gives the complete homogeneous
relation on the two adjacent black dots. Both kill all supported source rows.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra MvPolynomial TypeA Equiv TwoBlackFlag
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "P" => MvPolynomial (Fin N) k
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "B" => ofKLR k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) B
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "bot" => fixedTopFourExitBottom
local notation "a₁" => (⟨1,by decide⟩ : Fin N)
local notation "a₂" => (⟨2,by decide⟩ : Fin N)
local notation "a₄" => (⟨4,by decide⟩ : Fin N)

private theorem complete_kills :
    F (pol (complete (X a₁ : P) (X a₂) (Λ 0 ()))*e v₀)=0 := by
  let : Module R V := Module.compHom V (F).toRingHom
  have dot : F (pol ((X a₁ : P)^(Λ 0 ()))*e v₀)=0 := by
    rw [map_pow,pol_X,fiveSlotLeftExtreme_first_dot_power]
  have ann (v : V) : (pol ((X a₁ : P)^(Λ 0 ()))*e v₀ : R) • v=0 := by
    change F _*v=0
    rw [dot,zero_mul]
  have h := dd_smul_eq_zero (Q := stendhalQ Q Λ) 1 (by decide) (i := v₀) (by decide) ann (1 : V)
  change F (pol (NilHecke.dd k N 1 ((X a₁ : P)^(Λ 0 ())))*e v₀)*1=0 at h
  rwa [mul_one,NilHecke.dd_of_lt (by decide : 1+1<N),ddiff_X_pow (by decide : a₁≠a₂)] at h

/-- The whole two-black flag ideal annihilates the left-extreme idempotent. -/
theorem fiveSlotLeftExtreme_flagIdeal_kills {f : P}
    (hf : f ∈ TwoBlackFlag.ideal a₁ a₂ (Λ 0 ()) (Λ 0 ())) : F (pol f*e v₀)=0 := by
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  have first : F (pol ((X a₁ : P)^(Λ 0 ()))*e v₀)=0 := by
    rw [map_pow,pol_X,fiveSlotLeftExtreme_first_dot_power]
  rw [map_add pol,map_mul pol,map_mul pol,add_mul,mul_assoc,mul_assoc,map_add F,
    map_mul F (pol u),map_mul F (pol v),first,complete_kills,mul_zero,mul_zero,add_zero]

/-- Killing red dots lets the annihilator test use only the two black variables. -/
theorem fiveSlotLeftExtreme_flagIdeal_kills_blackSubst (hQ : KLRSymm Q) {f : P}
    (hf : blackSubst v₀ f ∈ TwoBlackFlag.ideal a₁ a₂ (Λ 0 ()) (Λ 0 ())) : F (pol f*e v₀)=0 := by
  have h := congrArg B (toKLR_ofKLR_pol_mul_e (Q := Q) (Λ := Λ) f v₀)
  rw [ofKLR_toKLR hQ] at h
  change violMk k Q Λ ν₀ (B (pol f*e v₀))=0
  rw [h]
  exact fiveSlotLeftExtreme_flagIdeal_kills Q Λ hf

local notation "w" => wordProd N [3,2]
local notation "C₀" => Λ 0 ()
local notation "d₀" => Λ 1 ()+Λ 2 ()
local notation "J₁" => TwoBlackFlag.ideal (k := k) a₁ a₄ C₀ (C₀+d₀)
local notation "σ" => fun f : P => swapPol 3 (by decide : 3+1<N) (swapPol 2 (by decide : 2+1<N) f)
local notation "q" => (X a₄ : P)^(Λ 2 ())
local notation "L" => fun (l : List ℕ) => (ψw l*e bot : R)

private theorem reflect_flag {f : P} (hf : rename w f*(X a₄)^d₀ ∈ J₁) :
    f ∈ TwoBlackFlag.ideal a₁ a₂ C₀ C₀ := by
  have h := (mul_second_pow_mem_iff (by decide : a₁≠a₄) (le_refl C₀) d₀ (rename w f)).1 hf
  have back := rename_mem (w⁻¹ : Perm (Fin N)) h
  rw [show w⁻¹ a₁=a₁ by decide,show w⁻¹ a₄=a₂ by decide,rename_rename,
    show ((w⁻¹ : Perm (Fin N)) ∘ (w : Perm (Fin N)))=id from (w).symm_comp_self,rename_id] at back
  exact back

/-- The two flag tests needed from the globally violated representation.
Testing the image on `1` reads the first coefficient. Testing on the first
black variable reads its multiple plus the second coefficient. -/
theorem fiveSlotCentral_rowReflection_of_flagTests (hQ : KLRSymm Q)
    (tests : ∀ f g : P, F (pol (σ f*q)*L [2,3,1]+pol (σ g*q)*L [2,3,1,2])=0 →
      let f₀ := blackSubst v₀ f
      let g₀ := blackSubst v₀ g
      rename w f₀*(X a₄)^d₀ ∈ J₁ ∧
        rename w (f₀*X a₁+g₀)*(X a₄)^d₀ ∈ J₁) :
    FiveSlotCentralRowReflection Q Λ := by
  intro f g zero
  obtain ⟨h₁,h₂⟩ := tests f g zero
  have hf := reflect_flag Λ h₁
  have hrg := reflect_flag Λ h₂
  have hg : blackSubst v₀ g ∈ TwoBlackFlag.ideal a₁ a₂ C₀ C₀ := by
    have minus := (TwoBlackFlag.ideal a₁ a₂ C₀ C₀).sub_mem hrg
      ((TwoBlackFlag.ideal a₁ a₂ C₀ C₀).mul_mem_right (X a₁) hf)
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

end Categorification.Stendhal.BraidedStendhalAlgebra
