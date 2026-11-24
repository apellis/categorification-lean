/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopIdeal

/-!
# Five-slot higher kernels with a fundamental spectator

In the two-equal-black example of Webster, arXiv:1309.3796v2, §6.1,
Lemma 6.8 after (6.21), the left-extreme idempotent vanishes when the
spectator pairs with the black colour by at most one. The two loadings
with one black before the merged pair then have zero higher ideal.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA MvPolynomial
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "jA" => sadj N 2 • v₀

/-- Crossing the first black left of the spectator makes the spectator's
cyclotomic dot power vanish on the left-extreme cut. -/
theorem fiveSlotLeftExtreme_first_dot_power :
    F ((x (⟨1,by decide⟩ : Fin N))^(Λ 0 ())*e v₀)=0 := by
  let s := sadj N 0 • v₀
  have violated : IsViolated s := ⟨by decide,by decide⟩
  have zero : F (e s)=0 := violMk_e violated
  have top : (e s : R)*(ψ 0*e v₀)=ψ 0*e v₀ := by
    rw [← mul_assoc,← ψ_mul_e,mul_assoc,e_mul_self]
  have killed := congrArg F top
  rw [map_mul,zero,zero_mul] at killed
  have sq := ψ_sq (Q := stendhalQ Q Λ) 0 (by decide) v₀
  rw [show (v₀).lbl ⟨0,by decide⟩=Sum.inr 0 by decide,
    show (v₀).lbl ⟨1,by decide⟩=Sum.inl () by decide] at sq
  simp only [reduceCtorEq,↓reduceIte,stendhalQ_inr_inl,ncEval_x2,map_pow,rename_X,pol_X,
    Matrix.cons_val_one,Matrix.cons_val_zero] at sq
  rw [← sq,mul_assoc,map_mul,killed.symm,mul_zero]

/-- The spectator supports two consecutive equal blacks only if its pairing
with their colour is at least two. A single remaining dot is eliminated by
the two-strand nilHecke relation. -/
theorem fiveSlotLeftExtreme_idem_zero_of_spectatorWeight_le_one (h : Λ 0 ()≤1) : F (e v₀)=0 := by
  have dot := fiveSlotLeftExtreme_first_dot_power Q Λ
  have weights : Λ 0 ()=0 ∨ Λ 0 ()=1 := by omega
  rcases weights with w|w
  · simpa only [w,pow_zero,one_mul] using dot
  rw [w,pow_one] at dot
  let d : V := F (ψ 1*e v₀)
  have same : (v₀).lbl ⟨1,by decide⟩=(v₀).lbl ⟨2,by decide⟩ := by decide
  have cut : (e v₀ : R)*(ψ 1*e v₀)=ψ 1*e v₀ := by
    rw [ψ_mul_e,sadj_smul_eq_self (by decide) same,← mul_assoc,e_mul_self]
  have ed : F (e v₀)*d=d := (map_mul F _ _).symm.trans (congrArg F cut)
  have nil : d*d=0 := by
    have sq := ψ_sq (Q := stendhalQ Q Λ) 1 (by decide) v₀
    rw [ite_eq_left same] at sq
    change F (ψ 1*e v₀)*F (ψ 1*e v₀)=0
    rw [← map_mul,mul_assoc,cut,← mul_assoc,sq,map_zero]
  have nh := dot_cross_right (Q := stendhalQ Q Λ) 1 (by decide) v₀
  rw [ite_eq_left same,sub_mul,mul_assoc,mul_assoc] at nh
  have image := congrArg F nh
  change F (ψ 1*(x ⟨1,by decide⟩*e v₀)-x ⟨2,by decide⟩*(ψ 1*e v₀))=F (e v₀) at image
  rw [map_sub,map_mul,dot,mul_zero,map_mul,zero_sub] at image
  change -(F (x ⟨2,by decide⟩)*d)=F (e v₀) at image
  have z := congrArg (· * d) image
  rw [ed,neg_mul,mul_assoc,nil,mul_zero,neg_zero] at z
  rw [← z,mul_zero,neg_zero] at image
  exact image.symm

/-- Both one-black-before-pair tops have zero higher ideal for spectator
pairing zero or one, including arbitrary weights on the exchanged reds. -/
theorem fiveSlot_oneBlackBeforePair_upperIdeal_eq_bot_of_spectatorWeight_le_one
    (h : Λ 0 ()≤1) (t : Seq μ₀) (ht : t=v₁ ∨ t=jA) :
    blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 t) (redWord t)=⊥ := by
  rw [fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ t ht,
    fiveSlotLeftExtreme_idem_zero_of_spectatorWeight_le_one Q Λ h]
  apply le_antisymm _ bot_le
  apply TwoSidedIdeal.span_le.mpr
  rintro z (rfl : z=0)
  exact TwoSidedIdeal.zero_mem _

/-- Actual balanced kernel-column injectivity at either one-before-pair
top, for every bottom and arbitrary red parameters, when the spectator
pairing is at most one. -/
theorem fiveSlot_oneBlackBeforePair_columnInclusion_of_spectatorWeight_le_one
    (h : Λ 0 ()≤1) (t s : Seq μ₀) (ht : t=v₁ ∨ t=jA) :
    Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 s) :=
  fiveSlot_blockKernelColumnInclusion_injective_of_upperIdeal_eq_bot Q Λ t s
    (fiveSlot_oneBlackBeforePair_upperIdeal_eq_bot_of_spectatorWeight_le_one Q Λ h t ht)

end Categorification.Stendhal.BraidedStendhalAlgebra
