/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedTransport
import Categorification.WeightedKLR.RedStrands.FiveSlotRightHigherPBW

/-!
# Higher generators with the last red strand on the right

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
For the five-slot loading with both black strands between the exchanged reds,
the three supported higher cuts factor through the nearby loading. Two
crossing maps suffice, related by the top nilHecke crossing.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "t" => fiveSlotRightLoading 2
local notation "jA" => fiveSlotHigherLoading 2
local notation "S" => fiveSlotHigherLoading
local notation "W" => fiveSlotRightHigherWords
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun s : Seq μ => F (e s)

private def lastRedTail : Fin 3 → List ℕ
  | 0 => [2]
  | 1 => [3]
  | _ => []

private theorem lastRedTail_top (i : Fin 3) : wordProd N (lastRedTail i) • S i = jA := by
  fin_cases i <;> decide +kernel

local notation "c₀" => (ψw [1] * e jA : R)
local notation "c₁" => (ψw [2,1] * e jA : R)

private theorem lastRed_factor_words (i : Fin 3) :
    (ψw (W i 2).1 * e (S i) : R) = c₀ * (ψw (lastRedTail i) * e (S i)) ∧
    (ψw (W i 2).2 * e (S i) : R) = c₁ * (ψw (lastRedTail i) * e (S i)) := by
  rw [FiveSlotFlag.cut_word_mul Q Λ _ _ _ _ (lastRedTail_top i),
    FiveSlotFlag.cut_word_mul Q Λ _ _ _ _ (lastRedTail_top i)]
  fin_cases i
  · refine ⟨rfl, ?_⟩
    exact FiveSlotFlag.crossing_braid_ne Q Λ 1 (by decide) (S 0) (by decide)
  · constructor
    · change (ψw [3,1] * e (S 1) : R) = ψw [1,3] * e (S 1)
      simp only [ψw_cons, ψw_nil, mul_one]
      rw [← ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide)]
    · change (ψw [2,3,1] * e (S 1) : R) = ψw [2,1,3] * e (S 1)
      simp only [ψw_cons, ψw_nil, mul_one]
      rw [← ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide)]
  · exact ⟨rfl, rfl⟩

private theorem lastRed_slide_first (f : MvPolynomial (Fin N) k) (z : R)
    (hz : e jA * z = z) :
    ∃ y : R, e jA * y = y ∧ pol f * (c₀ * z) = c₀ * y := by
  let y : R := pol (swapPol 1 (by decide) f) * z
  have h := slide_pol_from_left Q Λ 1 (by decide) jA f z hz
  have diff : ((jA).lbl ⟨1,by decide⟩) ≠ ((jA).lbl ⟨2,by decide⟩) := by decide
  simp only [diff, ite_false, sub_zero] at h
  refine ⟨y, ?_, ?_⟩
  · change e jA * (pol _ * z) = pol _ * z
    rw [← pol_e_comm_assoc, hz]
  · have hy : (e jA : R) * y = y := by
      change e jA * (pol _ * z) = pol _ * z
      rw [← pol_e_comm_assoc, hz]
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc, hz, hy]
    exact h

private theorem lastRed_slide_second (f : MvPolynomial (Fin N) k) (z : R)
    (hz : e jA * z = z) :
    ∃ y x : R, e jA * y = y ∧ e jA * x = x ∧
      pol f * (c₁ * z) = c₀ * y + c₁ * x := by
  have ht : (e t : R) * (c₀ * z) = c₀ * z := by
    have top : wordProd N [1] • jA = t := by decide
    rw [← mul_assoc, ← top, FiveSlotFlag.word_leftCut Q Λ]
  have h₂ := slide_pol_from_left Q Λ 2 (by decide) t f (c₀ * z) ht
  have equal : ((t).lbl ⟨2,by decide⟩) = ((t).lbl ⟨3,by decide⟩) := by decide
  simp only [equal, ite_true] at h₂
  obtain ⟨x, hx, hxp⟩ := lastRed_slide_first Q Λ (swapPol 2 (by decide) f) z hz
  obtain ⟨y, hy, hyp⟩ := lastRed_slide_first Q Λ (NilHecke.dd k N 2 (swapPol 2 (by decide) f)) z hz
  refine ⟨-y, x, by rw [mul_neg, hy], hx, ?_⟩
  have hc : c₁ = ψ 2 * c₀ := by rw [ψw_cons, mul_assoc]
  rw [hc, mul_assoc, h₂, hxp, hyp, mul_neg, sub_eq_add_neg]
  calc
    _ = -(c₀ * y) + ψ 2 * (c₀ * x) := add_comm _ _
    _ = _ := congrArg (-(c₀ * y) + ·) (mul_assoc (ψ 2) c₀ x).symm

private theorem lastRedHigher_exists_two_right_factors (hQ : KLRSymm Q) (i : Fin 3) (z : R)
    (hl : e t * z = z) (hr : z * e (S i) = z) :
    ∃ y x : R, e jA * y = y ∧ e jA * x = x ∧ z = c₀ * y + c₁ * x := by
  let w : R := ψw (lastRedTail i) * e (S i)
  obtain ⟨f, g, h⟩ := fiveSlotRightHigher_exists_pbw Q Λ hQ i 2 z hl hr
  obtain ⟨h₀, h₁⟩ := lastRed_factor_words Q Λ i
  rw [h₀,h₁] at h
  have hw : (e jA : R) * w = w := by
    change e jA * (ψw (lastRedTail i) * e (S i)) = _
    rw [← lastRedTail_top i]
    exact FiveSlotFlag.word_leftCut Q Λ _ _
  obtain ⟨a, ha, hfa⟩ := lastRed_slide_first Q Λ f w hw
  obtain ⟨b, c, hb, hc, hgc⟩ := lastRed_slide_second Q Λ g w hw
  refine ⟨a + b, c, by rw [mul_add, ha, hb], hc, ?_⟩
  change z = pol f * (c₀ * w) + pol g * (c₁ * w) at h
  rw [h, hfa, hgc, ← add_assoc, ← mul_add]

private theorem lastRedHigher_quotient_exists_two_right_factors (hQ : KLRSymm Q)
    (i : Fin 3) (z : V) (hl : p t * z = z) (hr : z * p (S i) = z) :
    ∃ y x : V, p jA * y = y ∧ p jA * x = x ∧ z = F c₀ * y + F c₁ * x := by
  obtain ⟨a, ha⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp
    (ofKLR_surjective (Q := Q) (Λ := Λ)) z
  let b : R := e t * a * e (S i)
  have hb : F b = z := by
    change F (e t * a * e (S i)) = z
    rw [map_mul, map_mul, show F a = z from ha, hl, hr]
  have hbl : (e t : R) * b = b := by
    change e t * (e t * a * e (S i)) = e t * a * e (S i)
    rw [← mul_assoc, ← mul_assoc, e_mul_self]
  have hbr : b * e (S i) = b := by
    change e t * a * e (S i) * e (S i) = e t * a * e (S i)
    rw [mul_assoc, e_mul_self]
  obtain ⟨y, x, hy, hx, h⟩ := lastRedHigher_exists_two_right_factors Q Λ hQ i b hbl hbr
  refine ⟨F y, F x, (map_mul F _ _).symm.trans (congrArg F hy),
    (map_mul F _ _).symm.trans (congrArg F hx), ?_⟩
  exact hb.symm.trans ((congrArg F h).trans (by simp only [map_add, map_mul]))

section KernelSum

open MulOpposite CornerEndomorphism
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "A" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "L" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t 1 2
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord t))

private theorem kernelSum_idealCut (u : Seq μ) (hu : redWord u = redWord t) (z : V) :
    (blockLoadingRep Q Λ t (z * p u)).1.1 = p t * z * p u := by
  have hE : p u * E = p u := corner_mul_right _ (orderedLoadingIdemAt Q Λ (redWord t) u hu)
  exact (blockLoadingRep_val Q Λ t (z * p u)).trans (by
    change p t * (z * p u) * E = p t * z * p u
    rw [← mul_assoc, mul_assoc (p t * z), hE])

/-- The actual kernel with the final red strand on the right is the sum
of the two supported images of the nearby projective. The second crossing includes the top nilHecke generator. -/
theorem fiveSlotLastRedKernel_exists_two_nearby_factors (hQ : KLRSymm Q)
    (a : L) (ha : a ∈ K) :
    ∃ y z : V, p jA * y = y ∧ p jA * z = z ∧ y * E = y ∧ z * E = z ∧
      a.1.1 = F c₀ * y + F c₁ * z := by
  suffices h : ∃ y z : V, p jA * y = y ∧ p jA * z = z ∧ a.1.1 = F c₀ * y + F c₁ * z by
    obtain ⟨y, z, hy, hz, h⟩ := h
    have hE : E * E = E := (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)).eq
    refine ⟨y * E, z * E, by rw [← mul_assoc, hy], by rw [← mul_assoc, hz],
      by rw [mul_assoc, hE], by rw [mul_assoc, hE], ?_⟩
    exact (corner_mul_right _ a.1).symm.trans (by rw [h, add_mul, mul_assoc, mul_assoc])
  rw [blockLoadingKernel_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, hlt, z, rfl⟩ := hx
    suffices h : ∃ y x : V, p jA * y = y ∧ p jA * x = x ∧
        p t * z * p u = F c₀ * y + F c₁ * x by
      obtain ⟨y, x, hy, hx, h⟩ := h
      exact ⟨y, x, hy, hx, (kernelSum_idealCut Q Λ u hu z).trans h⟩
    by_cases hv : IsViolated u
    · have hzero : p u = 0 := violMk_e hv
      exact ⟨0, 0, mul_zero _, mul_zero _, by rw [hzero, mul_zero, mul_zero, mul_zero, zero_add]⟩
    have hred : redWord u = redWord (fixedTopFourExitCut 0) := hu.trans (by decide)
    have hcut (i : Fin 3) :=
      lastRedHigher_quotient_exists_two_right_factors Q Λ hQ i
        (p t * z * p (S i))
        (by rw [← mul_assoc, ← mul_assoc, ← map_mul, e_mul_self])
        (by rw [mul_assoc, ← map_mul, e_mul_self])
    obtain hr | rfl | rfl | rfl := fiveSlot_nonviolated_tops u hred hv
    · rw [fiveSlotRightTop_blockRoot u hr, fiveSlotRightTop_blockRoot t (Or.inr (Or.inr rfl))] at hlt
      exact (lt_irrefl _ hlt).elim
    · exact hcut 0
    · exact hcut 1
    · exact hcut 2
  | zero =>
    exact ⟨0, 0, mul_zero _, mul_zero _, by change (0 : V) = _; rw [mul_zero, mul_zero, zero_add]⟩
  | add x y _ _ h₁ h₂ =>
    obtain ⟨a, b, ha, hb, rfl₁⟩ := h₁
    obtain ⟨c, d, hc, hd, rfl₂⟩ := h₂
    refine ⟨a + c, b + d, by rw [mul_add, ha, hc], by rw [mul_add, hb, hd], ?_⟩
    change x.1.1 + y.1.1 = _
    rw [rfl₁, rfl₂, mul_add, mul_add]
    exact add_add_add_comm _ _ _ _
  | smul r x _ h =>
    obtain ⟨a, b, ha, hb, h⟩ := h
    refine ⟨a * r.unop.1, b * r.unop.1, by rw [← mul_assoc, ha], by rw [← mul_assoc, hb], ?_⟩
    change x.1.1 * r.unop.1 = _
    rw [h, add_mul, mul_assoc, mul_assoc]

/-- The two nearby images characterize membership in the kernel with the final red on the right. -/
theorem fiveSlotLastRedKernel_mem_iff_two_nearby_factors (hQ : KLRSymm Q) (a : L) :
    a ∈ K ↔
      ∃ y z : V, p jA * y = y ∧ p jA * z = z ∧ y * E = y ∧ z * E = z ∧
        a.1.1 = F c₀ * y + F c₁ * z := by
  refine ⟨fiveSlotLastRedKernel_exists_two_nearby_factors Q Λ hQ a, ?_⟩
  rintro ⟨y, z, _, _, _, _, h⟩
  let J := blockUpperIdeal k Q Λ ν 1 2 (adjacentBlockRoot 1 2 t) (redWord t)
  have higher : adjacentBlockRoot 1 2 t < adjacentBlockRoot 1 2 jA := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro hge
      exact (by decide : ¬ _ ≤ _) (hge (1 : Fin 3) ())
  have hE1 : p jA ∈ J := TwoSidedIdeal.subset_span ⟨jA, by decide, higher, rfl⟩
  have member (w : R) (q : V) : F (w * e jA) * q ∈ J := by
    rw [map_mul]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hE1)
  change a.1.1 ∈ J
  rw [h]
  exact TwoSidedIdeal.add_mem _ (member _ y) (member _ z)


local notation "D" => F (ψ 2 : R)
local notation "i₂" => (⟨2, by decide⟩ : Fin N)
local notation "i₃" => (⟨3, by decide⟩ : Fin N)
local notation "X₂" => F (x i₂ : R)
local notation "X₃" => F (x i₃ : R)

private theorem lastRedCrossing_square (z : V) (hz : p t * z = z) :
    D * (D * z) = 0 := by
  have h : (ψ 2 * ψ 2 * e t : R) = 0 := by
    rw [ψ_sq 2 (by decide), ite_eq_left (by decide)]
  have hm := congrArg F h
  simp only [map_mul, map_zero] at hm
  rw [← mul_assoc, ← hz, ← mul_assoc, hm, zero_mul]

private theorem lastRedCrossing_left_dot (z : V) (hz : p t * z = z) :
    D * (X₂ * z) - X₃ * (D * z) = z := by
  have h : (ψ 2 * x i₂ * e t - x i₃ * ψ 2 * e t : R) = e t := by
    rw [← sub_mul, dot_cross_right 2 (by decide : 2 + 1 < N), ite_eq_left (by decide)]
  have hm := congrArg (fun r => F r * z) h
  simpa only [map_mul, map_sub, sub_mul, mul_assoc, hz] using hm

theorem fiveSlotLastRedKernel_crossing_mem_secondImage (hQ : KLRSymm Q)
    (a : L) (ha : a ∈ K) :
    ∃ z : V, p jA * z = z ∧ z * E = z ∧ D * a.1.1 = F c₁ * z := by
  obtain ⟨y, z, hy, _, hyE, _, hv⟩ :=
    fiveSlotLastRedKernel_exists_two_nearby_factors Q Λ hQ a ha
  have hc : D * F c₀ = F c₁ := by
    rw [← map_mul, ψw_cons 2 [1], mul_assoc]
  have hl : p t * F c₀ = F c₀ := by
    rw [← map_mul F, ← show wordProd N [1] • jA = t by decide]
    exact congrArg F (FiveSlotFlag.word_leftCut Q Λ _ _)
  have hzero : D * F c₁ = 0 := by
    rw [← hc]
    exact lastRedCrossing_square Q Λ _ hl
  refine ⟨y, hy, hyE, ?_⟩
  rw [hv, mul_add, ← mul_assoc D, ← mul_assoc D, hc, hzero, zero_mul, add_zero]

private theorem lastRedKernel_left (a : L) : p t * a.1.1 = a.1.1 := by
  have h := a.2
  change orderedLoadingIdem Q Λ t * a.1 = a.1 at h
  exact congrArg (fun z : A => z.1) h

/-- The equal-black crossing on the higher kernel with the final red on the right. -/
def fiveSlotLastRedKernel_nilHecke : K →ₗ[Aᵐᵒᵖ] K :=
  fiveSlotKernelLeftMul Q Λ t D (by
    rw [← map_mul, ← map_mul, e_mul_ψ, show sadj N 2 • t = t by decide])

theorem fiveSlotLastRedKernel_nilHecke_val (z : K) :
    (fiveSlotLastRedKernel_nilHecke Q Λ z).1.1.1 = D * z.1.1.1 :=
  fiveSlotKernelLeftMul_val Q Λ t D _ z

private def lastRedKernel_dot : K →ₗ[Aᵐᵒᵖ] K :=
  fiveSlotKernelLeftMul Q Λ t X₂ (by rw [← map_mul, ← map_mul, x_mul_e])

local notation "δ" => fiveSlotLastRedKernel_nilHecke Q Λ
local notation "u" => lastRedKernel_dot Q Λ

private theorem lastRedKernel_δ_sq (a : K) : δ (δ a) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (δ (δ a)).1.1.1 = (0 : V)
  simp only [fiveSlotLastRedKernel_nilHecke_val]
  exact lastRedCrossing_square Q Λ a.1.1.1 (lastRedKernel_left Q Λ a.1)

private theorem lastRedKernel_δ_u (a : K) (ha : δ a = 0) : δ (u a) = a := by
  have hz : D * a.1.1.1 = 0 := by
    rw [← fiveSlotLastRedKernel_nilHecke_val Q Λ a]
    exact congrArg (fun b : K => b.1.1.1) ha
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simp only [fiveSlotLastRedKernel_nilHecke_val, lastRedKernel_dot, fiveSlotKernelLeftMul_val]
  simpa only [hz, mul_zero, sub_zero] using
    lastRedCrossing_left_dot Q Λ a.1.1.1 (lastRedKernel_left Q Λ a.1)

/-- The higher kernel is two copies of the range of the top nilHecke operator. -/
def fiveSlotLastRedKernel_equiv_nilHeckeRangeProd :
    K ≃ₗ[Aᵐᵒᵖ] LinearMap.range δ × LinearMap.range δ :=
  nilHeckeRangeProd δ u (lastRedKernel_δ_sq Q Λ) (lastRedKernel_δ_u Q Λ)

end KernelSum

end Categorification.Stendhal.BraidedStendhalAlgebra
