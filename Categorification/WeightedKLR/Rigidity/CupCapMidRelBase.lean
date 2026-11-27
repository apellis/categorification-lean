/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidGenerators

/-!
# Relations between sliding diagrams on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. To check that the generators of `T̃^λ`
satisfy the KLR relations on the model `L ⊗ e T̃^{λ⁺}` (`CupCap.MidModel`), it suffices to check
that the two sides act alike (`CupCap.MidRel`): they are equal in `λ⁺`, or differ by diagrams in
which a strand leaves the window, or have the same image `e Y e` in `T̃^{λ⁺}`. The relation is
compatible with sums, scalars and products by sliding diagrams.

The diagrams of the generators are cut by the window idempotents: the crossing on the loading `t`
is `midCross p · E_t = midCrossAt t p`, and it ends at the loading `s_p t`.

## Main definitions

* `CupCap.MidRel`: two diagrams act alike on the model.

## Main results

* `CupCap.MidRel.of_sub_mem`, `CupCap.MidRel.of_midElt_eq`: sufficient conditions.
* `CupCap.MidRel.mul_left`, `CupCap.MidRel.mul_right`, `CupCap.MidRel.add`: compatibility.
* `CupCap.midCross_mul_eSum`, `CupCap.eSum_mul_midCrossAt`, `CupCap.midDot_mul_eSum`: cutting
  the generators by the window idempotents.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Cut

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))

theorem eSum_mid_mul_eSum_mid (s t : Seq (stendhalWeight ℓ ν)) :
    (E s * E t : Rp) = if s = t then E s else 0 := by
  split_ifs with h
  · subst h; exact (KLRAlgebra.eSum_idem _).eq
  · rw [← insertMap_one Q Λ Λc s (midPos_le j s), ← insertMap_one Q Λ Λc t (midPos_le j t)]
    exact insertMap_midPos_mul_of_ne h 1 1

theorem midCrossAt_mul_eSum (s t : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p * E t =
      if s = t then midCrossAt j hj Q Λ Λc ν ν₀ s p else 0 := by
  have key : ∀ Y : Rp, Y * E s * E t = if s = t then Y * E s else 0 := fun Y => by
    rw [mul_assoc, eSum_mid_mul_eSum_mid]; split_ifs <;> simp
  unfold midCrossAt
  split_ifs with hp h1 h2 h3 <;> (try split) <;> (try simp only [smul_mul_assoc]) <;>
    (try rw [key]) <;> simp_all

theorem midCross_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    midCross j hj Q Λ Λc ν ν₀ p * E t = midCrossAt j hj Q Λ Λc ν ν₀ t p := by
  rw [midCross, Finset.sum_mul, Finset.sum_eq_single t (fun s _ h => by
    simp [midCrossAt_mul_eSum, h]) (by simp)]
  simp [midCrossAt_mul_eSum]

theorem midCrossAt_eq_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    midCrossAt j hj Q Λ Λc ν ν₀ t p = midCrossAt j hj Q Λ Λc ν ν₀ t p * E t := by
  simp [midCrossAt_mul_eSum]

/-- The crossing on the loading `t` ends at the loading `s_p t`. -/
theorem eSum_mul_midCrossAt (t : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    E (sadj m p • t) * midCrossAt j hj Q Λ Λc ν ν₀ t p = midCrossAt j hj Q Λ Λc ν ν₀ t p := by
  unfold midCrossAt
  split_ifs with hp h1 h2
  · split
    · have hq : p + 1 ≤ m := hp.le
      have hm := midPos_sadj_left j t hp h1
      have hψ : (KLRAlgebra.ψ (p + N) : Rp) = KLRAlgebra.ψ (crossPos p N p) := by
        rw [crossPos_self]
      have hY : KLRAlgebra.ψ (p + N) * underLeft N p * E t =
          E (sadj m p • t) * (KLRAlgebra.ψ (p + N) * underLeft N p) := by
        rw [congrArg (KLRAlgebra.eSum _) (insertSet_congr' t (midPos_le j t) hq h1.symm), hψ]
        simp only [mul_assoc]
        rw [underLeft_mul_eSum, ← mul_assoc (KLRAlgebra.ψ _),
          ψ_crossPos_mul_eSum t _ (Or.inr le_rfl)]
        simp only [← mul_assoc]
        rw [congrArg (KLRAlgebra.eSum _) (insertSet_congr' (sadj m p • t)
          (Nat.le_of_succ_le hq) (midPos_le j (sadj m p • t)) hm.symm)]
      rw [hY, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    · rw [mul_zero]
  · split
    · have hq : p + 1 ≤ m := hp.le
      have hp0 : p ≤ m := by omega
      have hm := midPos_sadj_right j t hp h2
      have hψ : (KLRAlgebra.ψ (p + N) : Rp) = KLRAlgebra.ψ (crossPos p N p) := by
        rw [crossPos_self]
      have hY : underRight N p * KLRAlgebra.ψ (p + N) * E t =
          E (sadj m p • t) * (underRight N p * KLRAlgebra.ψ (p + N)) := by
        rw [congrArg (KLRAlgebra.eSum _) (insertSet_congr' t (midPos_le j t) hp0 h2.symm), hψ]
        simp only [mul_assoc]
        rw [ψ_crossPos_mul_eSum t _ (Or.inr le_rfl), ← mul_assoc (underRight N p),
          underRight_mul_eSum Q Λ Λc _ hq]
        simp only [← mul_assoc]
        rw [congrArg (KLRAlgebra.eSum _) (insertSet_congr' (sadj m p • t) hq
          (midPos_le j (sadj m p • t)) hm.symm)]
      rw [mul_smul_comm, hY, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    · rw [mul_zero]
  · have hf : p + 1 < midPos j t ∨ midPos j t ≤ p := by omega
    have hm := midPos_sadj_of_far j t hp (by omega)
    rw [ψ_crossPos_mul_eSum t _ hf,
      congrArg (KLRAlgebra.eSum _) (insertSet_congr' (sadj m p • t) (midPos_le j t)
        (midPos_le j (sadj m p • t)) hm.symm)]
    simp only [← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
  · rw [mul_zero]

theorem midDot_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    midDot j hj Q Λ Λc ν ν₀ a * E t =
      KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        ⟨midPos j t, Nat.lt_succ_of_le (midPos_le j t)⟩ a) * E t := by
  rw [midDot, Finset.sum_mul, Finset.sum_eq_single t (fun s _ h => by
    simp [mul_assoc, eSum_mid_mul_eSum_mid, h]) (by simp), mul_assoc,
    (KLRAlgebra.eSum_idem _).eq]

theorem midIdem_mul_eSum (s t : Seq (stendhalWeight ℓ ν)) :
    midIdem j hj Q Λ Λc ν ν₀ s * E t = if s = t then E s else 0 :=
  eSum_mid_mul_eSum_mid s t

end Cut

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Rel

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

variable (j hj Q Λ Λc ν ν₀) in
/-- **Two diagrams act alike on the model**: whenever both slide, they give the same
endomorphism. -/
def MidRel (Y Y' : Rp) : Prop :=
  ∀ (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y'),
    midEnd L hL hY = midEnd L hL hY'

variable {L hL}

theorem MidRel.of_eq {Y Y' : Rp} (h : Y = Y') : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y' :=
  fun hY hY' => midEnd_eq_of_eq hL hY hY' h

theorem MidRel.of_sub_mem {Y Y' : Rp} (h : Y - Y' ∈ midExit j hj Q Λ Λc ν ν₀) :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y Y' :=
  fun hY hY' => midEnd_congr hL hY hY' h

theorem MidRel.of_midElt_eq {Y Y' : Rp}
    (h : midElt j hj Q Λ Λc ν ν₀ Y = midElt j hj Q Λ Λc ν ν₀ Y') :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y Y' :=
  fun hY hY' => natMapOn_eq_of_sub_mem _ _ (by rw [h, sub_self]; exact zero_mem _)

theorem MidRel.refl (Y : Rp) : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y := MidRel.of_eq rfl

theorem MidRel.symm {Y Y' : Rp} (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y') :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y' Y := fun hY hY' => (h hY' hY).symm

theorem MidRel.trans {Y Y' Y'' : Rp} (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y')
    (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y') (h' : MidRel j hj Q Λ Λc ν ν₀ L hL Y' Y'') :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y Y'' := fun hY hY'' => (h hY hY').trans (h' hY' hY'')

theorem MidRel.mul_left {Z Y Y' : Rp} (hZ : MidSlides j hj Q Λ Λc ν ν₀ Z)
    (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y')
    (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y') :
    MidRel j hj Q Λ Λc ν ν₀ L hL (Z * Y) (Z * Y') := fun h1 h2 => by
  rw [midEnd_eq_of_eq hL h1 (hZ.mul hY) rfl, midEnd_eq_of_eq hL h2 (hZ.mul hY') rfl,
    midEnd_mul hL hZ hY, midEnd_mul hL hZ hY', h hY hY']

theorem MidRel.mul_right {Z Y Y' : Rp} (hZ : MidSlides j hj Q Λ Λc ν ν₀ Z)
    (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y')
    (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y') :
    MidRel j hj Q Λ Λc ν ν₀ L hL (Y * Z) (Y' * Z) := fun h1 h2 => by
  rw [midEnd_eq_of_eq hL h1 (hY.mul hZ) rfl, midEnd_eq_of_eq hL h2 (hY'.mul hZ) rfl,
    midEnd_mul hL hY hZ, midEnd_mul hL hY' hZ, h hY hY']

theorem MidRel.add {Y₁ Y₂ Y₁' Y₂' : Rp} (hY₁ : MidSlides j hj Q Λ Λc ν ν₀ Y₁)
    (hY₂ : MidSlides j hj Q Λ Λc ν ν₀ Y₂) (hY₁' : MidSlides j hj Q Λ Λc ν ν₀ Y₁')
    (hY₂' : MidSlides j hj Q Λ Λc ν ν₀ Y₂') (h₁ : MidRel j hj Q Λ Λc ν ν₀ L hL Y₁ Y₁')
    (h₂ : MidRel j hj Q Λ Λc ν ν₀ L hL Y₂ Y₂') :
    MidRel j hj Q Λ Λc ν ν₀ L hL (Y₁ + Y₂) (Y₁' + Y₂') := fun h1 h2 => by
  rw [midEnd_eq_of_eq hL h1 (hY₁.add hY₂) rfl, midEnd_eq_of_eq hL h2 (hY₁'.add hY₂') rfl,
    midEnd_add hL hY₁ hY₂, midEnd_add hL hY₁' hY₂', h₁ hY₁ hY₁', h₂ hY₂ hY₂']

theorem MidRel.smul (c : k) {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y') :
    MidRel j hj Q Λ Λc ν ν₀ L hL (c • Y) (c • Y') := fun h1 h2 => by
  rw [midEnd_eq_of_eq hL h1 (hY.smul c) rfl, midEnd_eq_of_eq hL h2 (hY'.smul c) rfl]
  ext y
  rw [midEnd_smul L hL c hY, midEnd_smul L hL c hY', h hY hY']

theorem MidRel.sum {ι' : Type*} (S : Finset ι') {Y Y' : ι' → Rp}
    (hY : ∀ a ∈ S, MidSlides j hj Q Λ Λc ν ν₀ (Y a))
    (hY' : ∀ a ∈ S, MidSlides j hj Q Λ Λc ν ν₀ (Y' a))
    (h : ∀ a ∈ S, MidRel j hj Q Λ Λc ν ν₀ L hL (Y a) (Y' a)) :
    MidRel j hj Q Λ Λc ν ν₀ L hL (∑ a ∈ S, Y a) (∑ a ∈ S, Y' a) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact MidRel.refl _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact MidRel.add (hY a (by simp)) (MidSlides.sum _ fun b hb => hY b (by simp [hb]))
      (hY' a (by simp)) (MidSlides.sum _ fun b hb => hY' b (by simp [hb])) (h a (by simp))
      (ih (fun b hb => hY b (by simp [hb])) (fun b hb => hY' b (by simp [hb]))
        (fun b hb => h b (by simp [hb])))

/-- Acting alike on the model is acting alike through `midEndAlg`. -/
theorem midEndAlg_eq_of_midRel {Y Y' : midSlidesSub j hj Q Λ Λc ν ν₀}
    (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y Y') : midEndAlg L hL Y = midEndAlg L hL Y' := by
  ext y
  rw [midEndAlg_apply, midEndAlg_apply, h]

end Rel

end Categorification.Stendhal.CupCap
