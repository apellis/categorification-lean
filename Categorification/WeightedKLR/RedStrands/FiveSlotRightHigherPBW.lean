/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopIdeal
import Categorification.WeightedKLR.RedStrands.BlockKernelFiltration
import Categorification.KLR.EqualBlackReturnKernel

/-!
# PBW reductions at the right five-slot tops

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
Two reduced words suffice for each supported cut between a right loading
and one of its three surviving higher loadings. At the rightmost loading,
both words can be factored through the central loading. Sliding the
polynomial coefficients to the right gives two fixed crossing maps.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MvPolynomial

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "v₂" => fixedTopFourExitCut 2
local notation "jA" => sadj n₀ 2 • v₀

def fiveSlotHigherLoading : Fin 3 → Seq μ₀
  | 0 => v₀
  | 1 => v₁
  | _ => jA

def fiveSlotRightLoading : Fin 3 → Seq μ₀
  | 0 => v₂
  | 1 => sadj n₀ 2 • v₂
  | _ => sadj n₀ 3 • (sadj n₀ 2 • v₂)

/-- Reduced words for the two black matchings from a higher loading to a right top. -/
def fiveSlotRightHigherWords : Fin 3 → Fin 3 → List ℕ × List ℕ
  | 0, 0 => ([2,1,3,2], [3,2,1,3,2])
  | 0, 1 => ([3,1,2], [3,1,2,1])
  | 0, 2 => ([1,2], [1,2,1])
  | 1, 0 => ([2,1], [3,2,1])
  | 1, 1 => ([1], [2,3,2,1])
  | 1, 2 => ([3,1], [2,3,1])
  | 2, 0 => ([2,1,3], [3,2,1,3])
  | 2, 1 => ([3,1], [3,2,1])
  | 2, 2 => ([1], [2,1])

local notation "W" => fiveSlotRightHigherWords
local notation "S" => fiveSlotHigherLoading
local notation "T" => fiveSlotRightLoading

theorem fiveSlotRightHigherWords_spec (i j : Fin 3) :
    IsReduced n₀ (W i j).1 ∧ IsReduced n₀ (W i j).2 ∧
      wordProd n₀ (W i j).1 ≠ wordProd n₀ (W i j).2 ∧
      ∀ p : Perm (Fin n₀), p • S i = T j ↔
        p = wordProd n₀ (W i j).1 ∨ p = wordProd n₀ (W i j).2 := by
  fin_cases i <;> fin_cases j <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact ⟨by simp [ValidWord, fiveSlotRightHigherWords]; decide, by rw [length_eq_invCount]; decide +kernel⟩
    | decide +kernel

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀

/-- The nine affine cuts controlling the right-top kernel each have the two
explicit PBW terms of the corresponding black matching. -/
theorem fiveSlotRightHigher_exists_pbw (hQ : KLRSymm Q) (i j : Fin 3) (x : R)
    (hl : e (T j) * x = x) (hr : x * e (S i) = x) :
    ∃ f g : MvPolynomial (Fin n₀) k,
      x = pol f * (ψw (W i j).1 * e (S i)) + pol g * (ψw (W i j).2 * e (S i)) := by
  obtain ⟨h₁, h₂, hne, hmatch⟩ := fiveSlotRightHigherWords_spec i j
  exact exists_two_corner_coefficients_of_words (stendhalQ_symm Q Λ hQ)
    (S i) (T j) (W i j).1 (W i j).2 h₁ h₂ hne hmatch x hl hr


private def centralTail : Fin 3 → List ℕ
  | 0 => [3,2]
  | 1 => []
  | _ => [3]

private theorem centralTail_loading (i : Fin 3) : wordProd n₀ (centralTail i) • S i = v₁ := by
  fin_cases i <;> decide

private theorem rightmost_words (i : Fin 3) :
    W i 0 = ([2,1] ++ centralTail i, [3,2,1] ++ centralTail i) := by
  fin_cases i <;> rfl

private theorem factor_rightmost_word (l : List ℕ) (i : Fin 3) :
    (ψw (l ++ centralTail i) * e (S i) : R) =
      (ψw l * e v₁) * (ψw (centralTail i) * e (S i)) := by
  have hcut : (e v₁ : R) * (ψw (centralTail i) * e (S i)) =
      ψw (centralTail i) * e (S i) := by
    rw [← centralTail_loading i, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  rw [ψw_append, mul_assoc, mul_assoc _ (e v₁), hcut]

/-- At the rightmost top the PBW terms from all three higher cuts use the
same two leading words from E1. The second applies the final nilHecke crossing. -/
theorem fiveSlotRightmostHigher_exists_central_factors (hQ : KLRSymm Q) (i : Fin 3) (x : R)
    (hl : e v₂ * x = x) (hr : x * e (S i) = x) :
    ∃ f g : MvPolynomial (Fin n₀) k,
      x = pol f * ((ψw [2,1] * e v₁) * (ψw (centralTail i) * e (S i))) +
          pol g * ((ψw [3,2,1] * e v₁) * (ψw (centralTail i) * e (S i))) := by
  have hl' : e (T 0) * x = x := hl
  obtain ⟨f, g, h⟩ := fiveSlotRightHigher_exists_pbw Q Λ hQ i 0 x hl' hr
  rw [rightmost_words i] at h
  exact ⟨f, g, h.trans (congrArg₂ (· + ·)
    (congrArg (pol f * ·) (factor_rightmost_word Q Λ [2,1] i))
    (congrArg (pol g * ·) (factor_rightmost_word Q Λ [3,2,1] i)))⟩


local notation "P" => MvPolynomial (Fin n₀) k

private theorem slide_pol_from_left (j : ℕ) (hj : j + 1 < n₀) (s : Seq μ₀)
    (f : P) (z : R) (hz : e s * z = z) :
    pol f * (ψ j * z) =
      ψ j * (pol (swapPol j hj f) * z) -
        if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j+1, hj⟩
          then pol (NilHecke.dd k n₀ j (swapPol j hj f)) * z else 0 := by
  classical
  have he : (eqIdem j hj * e s : R) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j+1, hj⟩ then e s else 0 := by
    rw [eqIdem, Finset.sum_mul, Finset.sum_eq_single s]
    · split_ifs
      · exact e_mul_self _
      · exact zero_mul _
    · intro u _ hu
      split_ifs
      · rw [e_mul_e, ite_eq_right hu]
      · exact zero_mul _
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  have hh : (eqIdem j hj * z : R) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j+1, hj⟩ then z else 0 := by
    rw [← hz, ← mul_assoc, he, hz]
    split_ifs
    · exact hz
    · exact zero_mul _
  rw [← mul_assoc, pol_mul_ψ j hj f, sub_mul, mul_assoc, mul_assoc, hh]
  split_ifs
  · rfl
  · rw [mul_zero]

local notation "c₀" => (ψw [2,1] * e v₁ : R)
local notation "c₁" => (ψw [3,2,1] * e v₁ : R)

private theorem centralCrossing_leftSlide (f : P) (z : R) (hz : e v₁ * z = z) :
    ∃ y : R, e v₁ * y = y ∧ pol f * (c₀ * z) = c₀ * y := by
  let s := sadj n₀ 1 • v₁
  have hs : (e s : R) * (ψ 1 * z) = ψ 1 * z := by
    rw [← mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc, hz]
  have h₂ := slide_pol_from_left Q Λ 2 (by decide) s f (ψ 1 * z) hs
  have h₁ := slide_pol_from_left Q Λ 1 (by decide) v₁ (swapPol 2 (by decide) f) z hz
  have hn₂ : s.lbl ⟨2, by decide⟩ ≠ s.lbl ⟨3, by decide⟩ := by decide
  have hn₁ : (v₁).lbl ⟨1, by decide⟩ ≠ (v₁).lbl ⟨2, by decide⟩ := by decide
  simp only [hn₂, ite_false, sub_zero] at h₂
  simp only [hn₁, ite_false, sub_zero] at h₁
  let g := swapPol 1 (by decide : 1+1<n₀) (swapPol 2 (by decide : 2+1<n₀) f)
  refine ⟨pol g * z, ?_, ?_⟩
  · rw [← pol_e_comm_assoc, hz]
  · have hzg : (e v₁ : R) * (pol g * z) = pol g * z := by rw [← pol_e_comm_assoc, hz]
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc, hz, hzg]
    exact h₂.trans (congrArg (ψ 2 * ·) h₁)

private theorem rightmostCrossing_leftSlide (f : P) (z : R) (hz : e v₁ * z = z) :
    ∃ y x : R, e v₁ * y = y ∧ e v₁ * x = x ∧
      pol f * (c₁ * z) = c₀ * y + c₁ * x := by
  have ht : (e v₂ : R) * (c₀ * z) = c₀ * z := by
    rw [← mul_assoc, ← show wordProd n₀ [2,1] • v₁ = v₂ by decide,
      ← mul_assoc (e _) (ψw _), e_mul_ψw, inv_smul_smul, mul_assoc _ (e v₁), hz]
  have h₃ := slide_pol_from_left Q Λ 3 (by decide) v₂ f (c₀ * z) ht
  have he : (v₂).lbl ⟨3, by decide⟩ = (v₂).lbl ⟨4, by decide⟩ := by decide
  simp only [he, ite_true] at h₃
  obtain ⟨x, hx, hxp⟩ := centralCrossing_leftSlide Q Λ (swapPol 3 (by decide) f) z hz
  obtain ⟨y, hy, hyp⟩ := centralCrossing_leftSlide Q Λ (NilHecke.dd k n₀ 3 (swapPol 3 (by decide) f)) z hz
  refine ⟨-y, x, by rw [mul_neg, hy], hx, ?_⟩
  have hc : c₁ = ψ 3 * c₀ := by rw [ψw_cons, mul_assoc]
  rw [hc, mul_assoc, h₃, hxp, hyp, mul_neg, sub_eq_add_neg]
  calc
    _ = -(c₀ * y) + ψ 3 * (c₀ * x) := add_comm _ _
    _ = _ := congrArg (-(c₀ * y) + ·) (mul_assoc (ψ 3) c₀ x).symm

/-- At the rightmost top every cut from a higher loading factors through the
same two maps from the central loading projective, with supported right coefficients. -/
theorem fiveSlotRightmostHigher_exists_two_right_factors (hQ : KLRSymm Q) (i : Fin 3) (z : R)
    (hl : e v₂ * z = z) (hr : z * e (S i) = z) :
    ∃ y x : R, e v₁ * y = y ∧ e v₁ * x = x ∧ z = c₀ * y + c₁ * x := by
  let w : R := ψw (centralTail i) * e (S i)
  have hw : (e v₁ : R) * w = w := by
    change e v₁ * (ψw (centralTail i) * e (S i)) = _
    rw [← centralTail_loading i, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  obtain ⟨f, g, h⟩ := fiveSlotRightmostHigher_exists_central_factors Q Λ hQ i z hl hr
  obtain ⟨a, ha, hfa⟩ := centralCrossing_leftSlide Q Λ f w hw
  obtain ⟨b, c, hb, hc, hgc⟩ := rightmostCrossing_leftSlide Q Λ g w hw
  refine ⟨a + b, c, by rw [mul_add, ha, hb], hc, ?_⟩
  change z = pol f * (c₀ * w) + pol g * (c₁ * w) at h
  rw [h, hfa, hgc, ← add_assoc, ← mul_add]


local notation "V" => ViolQuotient k Q Λ ν₀
local notation "π" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "p" => fun s : Seq μ₀ => π (e s)

/-- The supported quotient cuts at the rightmost top factor through two
fixed maps from the central loading. -/
theorem fiveSlotRightmostHigher_quotient_exists_two_right_factors (hQ : KLRSymm Q)
    (i : Fin 3) (z : V) (hl : p v₂ * z = z) (hr : z * p (S i) = z) :
    ∃ y x : V, p v₁ * y = y ∧ p v₁ * x = x ∧ z = π c₀ * y + π c₁ * x := by
  obtain ⟨a, ha⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp
    (ofKLR_surjective (Q := Q) (Λ := Λ)) z
  let b : R := e v₂ * a * e (S i)
  have hb : π b = z := by
    change π (e v₂ * a * e (S i)) = z
    rw [map_mul, map_mul, show π a = z from ha, hl, hr]
  have hbl : (e v₂ : R) * b = b := by
    change e v₂ * (e v₂ * a * e (S i)) = e v₂ * a * e (S i)
    rw [← mul_assoc, ← mul_assoc, e_mul_self]
  have hbr : b * e (S i) = b := by
    change e v₂ * a * e (S i) * e (S i) = e v₂ * a * e (S i)
    rw [mul_assoc, e_mul_self]
  obtain ⟨y, x, hy, hx, h⟩ := fiveSlotRightmostHigher_exists_two_right_factors Q Λ hQ i b hbl hbr
  refine ⟨π y, π x, (map_mul π _ _).symm.trans (congrArg π hy),
    (map_mul π _ _).symm.trans (congrArg π hx), ?_⟩
  exact hb.symm.trans ((congrArg π h).trans (by simp only [map_add, map_mul]))


section KernelSum

open MulOpposite CornerEndomorphism
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "A" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord v₂))
local notation "L" => rIdeal (orderedLoadingIdem Q Λ v₂)
local notation "K" => blockLoadingKernel Q Λ v₂ 1 2
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord v₂))

private theorem kernelSum_idealCut (u : Seq μ₀) (hu : redWord u = redWord v₂) (z : V) :
    (blockLoadingRep Q Λ v₂ (z * p u)).1.1 = p v₂ * z * p u := by
  have hE : p u * E = p u := corner_mul_right _ (orderedLoadingIdemAt Q Λ (redWord v₂) u hu)
  exact (blockLoadingRep_val Q Λ v₂ (z * p u)).trans (by
    change p v₂ * (z * p u) * E = p v₂ * z * p u
    rw [← mul_assoc, mul_assoc (p v₂ * z), hE])

/-- The actual kernel at the rightmost top is the sum of the two supported
images of the E1 projective. The second crossing includes the top nilHecke generator. -/
theorem fiveSlotRightmostKernel_exists_two_central_factors (hQ : KLRSymm Q)
    (a : L) (ha : a ∈ K) :
    ∃ y z : V, p v₁ * y = y ∧ p v₁ * z = z ∧ y * E = y ∧ z * E = z ∧
      a.1.1 = π c₀ * y + π c₁ * z := by
  suffices h : ∃ y z : V, p v₁ * y = y ∧ p v₁ * z = z ∧ a.1.1 = π c₀ * y + π c₁ * z by
    obtain ⟨y, z, hy, hz, h⟩ := h
    have hE : E * E = E := (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord v₂)).eq
    refine ⟨y * E, z * E, by rw [← mul_assoc, hy], by rw [← mul_assoc, hz],
      by rw [mul_assoc, hE], by rw [mul_assoc, hE], ?_⟩
    exact (corner_mul_right _ a.1).symm.trans (by rw [h, add_mul, mul_assoc, mul_assoc])
  rw [blockLoadingKernel_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, hlt, z, rfl⟩ := hx
    suffices h : ∃ y x : V, p v₁ * y = y ∧ p v₁ * x = x ∧
        p v₂ * z * p u = π c₀ * y + π c₁ * x by
      obtain ⟨y, x, hy, hx, h⟩ := h
      exact ⟨y, x, hy, hx, (kernelSum_idealCut Q Λ u hu z).trans h⟩
    by_cases hv : IsViolated u
    · have hzero : p u = 0 := violMk_e hv
      exact ⟨0, 0, mul_zero _, mul_zero _, by rw [hzero, mul_zero, mul_zero, mul_zero, zero_add]⟩
    have hred : redWord u = redWord v₀ := hu.trans (by decide)
    have hcut (i : Fin 3) :=
      fiveSlotRightmostHigher_quotient_exists_two_right_factors Q Λ hQ i
        (p v₂ * z * p (S i))
        (by rw [← mul_assoc, ← mul_assoc, ← map_mul, e_mul_self])
        (by rw [mul_assoc, ← map_mul, e_mul_self])
    obtain hr | rfl | rfl | rfl := fiveSlot_nonviolated_tops u hred hv
    · rw [fiveSlotRightTop_blockRoot u hr, fiveSlotRightTop_blockRoot v₂ (Or.inl rfl)] at hlt
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

/-- The two fixed E1 images characterize membership in the actual rightmost kernel. -/
theorem fiveSlotRightmostKernel_mem_iff_two_central_factors (hQ : KLRSymm Q) (a : L) :
    a ∈ K ↔
      ∃ y z : V, p v₁ * y = y ∧ p v₁ * z = z ∧ y * E = y ∧ z * E = z ∧
        a.1.1 = π c₀ * y + π c₁ * z := by
  refine ⟨fiveSlotRightmostKernel_exists_two_central_factors Q Λ hQ a, ?_⟩
  rintro ⟨y, z, _, _, _, _, h⟩
  let J := blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 v₂) (redWord v₂)
  have higher : adjacentBlockRoot 1 2 v₂ < adjacentBlockRoot 1 2 v₁ := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro hge
      exact (by decide : ¬ _ ≤ _) (hge (1 : Fin 3) ())
  have hE1 : p v₁ ∈ J := TwoSidedIdeal.subset_span ⟨v₁, by decide, higher, rfl⟩
  have member (w : R) (q : V) : π (w * e v₁) * q ∈ J := by
    rw [map_mul]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hE1)
  change a.1.1 ∈ J
  rw [h]
  exact TwoSidedIdeal.add_mem _ (member _ y) (member _ z)


local notation "D" => π (ψ 3 : R)
local notation "i₃" => (⟨3, by decide⟩ : Fin n₀)
local notation "i₄" => (⟨4, by decide⟩ : Fin n₀)
local notation "X₃" => π (x i₃ : R)
local notation "X₄" => π (x i₄ : R)

private theorem rightmostCrossing_square (z : V) (hz : p v₂ * z = z) :
    D * (D * z) = 0 := by
  have h : (ψ 3 * ψ 3 * e v₂ : R) = 0 := by
    rw [ψ_sq 3 (by decide), ite_eq_left (by decide)]
  have hm := congrArg π h
  simp only [map_mul, map_zero] at hm
  rw [← mul_assoc, ← hz, ← mul_assoc, hm, zero_mul]

private theorem rightmostCrossing_left_dot (z : V) (hz : p v₂ * z = z) :
    D * (X₃ * z) - X₄ * (D * z) = z := by
  have h : (ψ 3 * x i₃ * e v₂ - x i₄ * ψ 3 * e v₂ : R) = e v₂ := by
    rw [← sub_mul, dot_cross_right 3 (by decide : 3 + 1 < n₀), ite_eq_left (by decide)]
  have hm := congrArg (fun r => π r * z) h
  simpa only [map_mul, map_sub, sub_mul, mul_assoc, hz] using hm

private theorem rightmostCrossing_c₀_left :
    p v₂ * π c₀ = π c₀ := by
  rw [← map_mul]
  have top : wordProd n₀ [2,1] • v₁ = v₂ := by decide
  rw [← top, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

private theorem rightmostCrossing_c₀_to_c₁ : D * π c₀ = π c₁ := by
  rw [← map_mul, ψw_cons 3 [2,1], mul_assoc]

private theorem rightmostCrossing_c₁_zero : D * π c₁ = 0 := by
  rw [← rightmostCrossing_c₀_to_c₁]
  exact rightmostCrossing_square Q Λ _ (rightmostCrossing_c₀_left Q Λ)

private theorem rightmostKernel_left (a : L) : p v₂ * a.1.1 = a.1.1 := by
  have h := a.2
  change orderedLoadingIdem Q Λ v₂ * a.1 = a.1 at h
  exact congrArg (fun z : A => z.1) h

/-- The equal-black crossing sends the rightmost kernel into the second E1 image. -/
theorem fiveSlotRightmostKernel_crossing_mem_secondImage (hQ : KLRSymm Q)
    (a : L) (ha : a ∈ K) :
    ∃ y : V, p v₁ * y = y ∧ y * E = y ∧ D * a.1.1 = π c₁ * y := by
  obtain ⟨y, z, hy, _, hyE, _, h⟩ := fiveSlotRightmostKernel_exists_two_central_factors Q Λ hQ a ha
  refine ⟨y, hy, hyE, ?_⟩
  rw [h, mul_add, ← mul_assoc, ← mul_assoc, rightmostCrossing_c₀_to_c₁,
    rightmostCrossing_c₁_zero, zero_mul, add_zero]

/-- At the rightmost top, the kernel of the equal-black crossing acting on the
higher kernel is exactly the second E1 image. -/
theorem fiveSlotRightmostKernel_crossing_eq_zero_iff (hQ : KLRSymm Q)
    (a : L) (ha : a ∈ K) :
    D * a.1.1 = 0 ↔ ∃ y : V, p v₁ * y = y ∧ y * E = y ∧ a.1.1 = π c₁ * y := by
  constructor
  · intro hzero
    let b := blockLoadingRep Q Λ v₂ (X₃ * a.1.1)
    have hb : b.1.1 = X₃ * a.1.1 := by
      have hm : p v₂ * X₃ = X₃ * p v₂ := by
        rw [← map_mul, ← map_mul, x_mul_e]
      have hr : a.1.1 * E = a.1.1 := corner_mul_right _ a.1
      exact (blockLoadingRep_val Q Λ v₂ _).trans (by
        change p v₂ * (X₃ * a.1.1) * E = X₃ * a.1.1
        rw [← mul_assoc, hm, mul_assoc X₃, rightmostKernel_left Q Λ a, mul_assoc, hr])
    have hbK : b ∈ K := by
      let J := blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 v₂) (redWord v₂)
      change b.1.1 ∈ J
      rw [hb]
      exact TwoSidedIdeal.mul_mem_left _ _ _ ha
    obtain ⟨y, hy, hyE, heq⟩ := fiveSlotRightmostKernel_crossing_mem_secondImage Q Λ hQ b hbK
    have hdot := rightmostCrossing_left_dot Q Λ a.1.1 (rightmostKernel_left Q Λ a)
    rw [hzero, mul_zero, sub_zero] at hdot
    exact ⟨y, hy, hyE, hdot.symm.trans ((congrArg (D * ·) hb).symm.trans heq)⟩
  · rintro ⟨y, _, _, h⟩
    rw [h, ← mul_assoc, rightmostCrossing_c₁_zero, zero_mul]


/-- A vector of the first E1 image lies in the second image precisely when
the same coefficient gives zero in the second image. -/
theorem fiveSlotRightmostKernel_central_images_intersect_iff (hQ : KLRSymm Q)
    (y : V) (hy : p v₁ * y = y) (hyE : y * E = y) :
    (∃ z : V, p v₁ * z = z ∧ z * E = z ∧ π c₀ * y = π c₁ * z) ↔ π c₁ * y = 0 := by
  let a := blockLoadingRep Q Λ v₂ (π c₀ * y)
  have ha : a.1.1 = π c₀ * y :=
    (blockLoadingRep_val Q Λ v₂ _).trans (by
      change p v₂ * (π c₀ * y) * E = π c₀ * y
      rw [← mul_assoc, rightmostCrossing_c₀_left, mul_assoc, hyE])
  have haK : a ∈ K := (fiveSlotRightmostKernel_mem_iff_two_central_factors Q Λ hQ a).2
    ⟨y, 0, hy, mul_zero _, hyE, zero_mul _, by rw [ha, mul_zero, add_zero]⟩
  have h := fiveSlotRightmostKernel_crossing_eq_zero_iff Q Λ hQ a haK
  rw [ha, ← mul_assoc, rightmostCrossing_c₀_to_c₁] at h
  exact h.symm


private theorem rightmostKernel_rep_mul_val (c : V) (hc : p v₂ * c = c * p v₂) (a : L) :
    (blockLoadingRep Q Λ v₂ (c * a.1.1)).1.1 = c * a.1.1 := by
  have hr : a.1.1 * E = a.1.1 := corner_mul_right _ a.1
  exact (blockLoadingRep_val Q Λ v₂ _).trans (by
    change p v₂ * (c * a.1.1) * E = c * a.1.1
    rw [← mul_assoc, hc, mul_assoc c, rightmostKernel_left Q Λ a, mul_assoc, hr])

private def rightmostKernel_mul (c : V) (hc : p v₂ * c = c * p v₂) (a : K) : K :=
  ⟨blockLoadingRep Q Λ v₂ (c * a.1.1.1), by
    let J := blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 v₂) (redWord v₂)
    change (blockLoadingRep Q Λ v₂ (c * a.1.1.1)).1.1 ∈ J
    rw [rightmostKernel_rep_mul_val Q Λ c hc a.1]
    exact TwoSidedIdeal.mul_mem_left _ _ _ a.2⟩

private theorem rightmostKernel_mul_val (c : V) (hc : p v₂ * c = c * p v₂) (a : K) :
    (rightmostKernel_mul Q Λ c hc a).1.1.1 = c * a.1.1.1 :=
  rightmostKernel_rep_mul_val Q Λ c hc a.1

private theorem rightmostKernel_val_injective :
    Function.Injective (fun a : K => a.1.1.1) := fun _ _ h =>
  Subtype.ext (Subtype.ext (Subtype.ext h))

private theorem rightmostKernel_mul_add (c : V) (hc : p v₂ * c = c * p v₂) (a b : K) :
    rightmostKernel_mul Q Λ c hc (a + b) =
      rightmostKernel_mul Q Λ c hc a + rightmostKernel_mul Q Λ c hc b := by
  apply rightmostKernel_val_injective Q Λ
  change (rightmostKernel_mul Q Λ c hc (a+b)).1.1.1 =
    (rightmostKernel_mul Q Λ c hc a).1.1.1 + (rightmostKernel_mul Q Λ c hc b).1.1.1
  simp only [rightmostKernel_mul_val]
  exact mul_add c _ _

private theorem rightmostKernel_mul_smul (c : V) (hc : p v₂ * c = c * p v₂) (r : Aᵐᵒᵖ) (a : K) :
    rightmostKernel_mul Q Λ c hc (r • a) = r • rightmostKernel_mul Q Λ c hc a := by
  apply rightmostKernel_val_injective Q Λ
  change (rightmostKernel_mul Q Λ c hc (r • a)).1.1.1 =
    (rightmostKernel_mul Q Λ c hc a).1.1.1 * r.unop.1
  simp only [rightmostKernel_mul_val]
  exact (mul_assoc c _ _).symm

private def rightmostKernel_leftMul (c : V) (hc : p v₂ * c = c * p v₂) :
    K →ₗ[Aᵐᵒᵖ] K where
  toFun := rightmostKernel_mul Q Λ c hc
  map_add' := rightmostKernel_mul_add Q Λ c hc
  map_smul' := rightmostKernel_mul_smul Q Λ c hc

private theorem rightmostKernel_leftMul_val (c : V) (hc : p v₂ * c = c * p v₂) (a : K) :
    (rightmostKernel_leftMul Q Λ c hc a).1.1.1 = c * a.1.1.1 :=
  rightmostKernel_mul_val Q Λ c hc a

/-- The equal-black crossing as an endomorphism of the rightmost higher kernel. -/
def fiveSlotRightmostKernel_nilHecke : K →ₗ[Aᵐᵒᵖ] K :=
  rightmostKernel_leftMul Q Λ D (by
    rw [← map_mul, ← map_mul, e_mul_ψ, show sadj n₀ 3 • v₂ = v₂ by decide])

theorem fiveSlotRightmostKernel_nilHecke_val (z : K) :
    (fiveSlotRightmostKernel_nilHecke Q Λ z).1.1.1 = D * z.1.1.1 :=
  rightmostKernel_leftMul_val Q Λ D _ z

private def rightmostKernel_dot : K →ₗ[Aᵐᵒᵖ] K :=
  rightmostKernel_leftMul Q Λ X₃ (by rw [← map_mul, ← map_mul, x_mul_e])

local notation "d" => fiveSlotRightmostKernel_nilHecke Q Λ
local notation "u" => rightmostKernel_dot Q Λ

private theorem rightmostKernel_d_sq (a : K) : d (d a) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (d (d a)).1.1.1 = (0 : V)
  simp only [fiveSlotRightmostKernel_nilHecke, rightmostKernel_leftMul_val]
  exact rightmostCrossing_square Q Λ a.1.1.1 (rightmostKernel_left Q Λ a.1)

private theorem rightmostKernel_d_u_of_d_zero (a : K) (ha : d a = 0) : d (u a) = a := by
  have hz : D * a.1.1.1 = 0 := by
    rw [← rightmostKernel_leftMul_val Q Λ D _ a]
    exact congrArg (fun b : K => b.1.1.1) ha
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simp only [fiveSlotRightmostKernel_nilHecke, rightmostKernel_dot, rightmostKernel_leftMul_val]
  simpa only [hz, mul_zero, sub_zero] using
    rightmostCrossing_left_dot Q Λ a.1.1.1 (rightmostKernel_left Q Λ a.1)

private def nilHeckeRangeProd {B M : Type} [Ring B] [AddCommGroup M] [Module B M]
    (δ dot : M →ₗ[B] M) (sq : ∀ a, δ (δ a) = 0)
    (contract : ∀ a, δ a = 0 → δ (dot a) = a) :
    M ≃ₗ[B] LinearMap.range δ × LinearMap.range δ where
  toFun a := (⟨a - dot (δ a), dot (a - dot (δ a)), contract _ (by
    rw [map_sub, contract (δ a) (sq a), sub_self])⟩, ⟨δ a, a, rfl⟩)
  invFun w := w.1.1 + dot w.2.1
  left_inv a := sub_add_cancel _ _
  right_inv w := by
    have h₁ : δ w.1.1 = 0 := by
      obtain ⟨a, ha⟩ := w.1.2
      rw [← ha, sq a]
    have h₂ : δ w.2.1 = 0 := by
      obtain ⟨a, ha⟩ := w.2.2
      rw [← ha, sq a]
    have hd : δ (w.1.1 + dot w.2.1) = w.2.1 := by
      rw [map_add, h₁, contract _ h₂, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change w.1.1 + dot w.2.1 - dot (δ (w.1.1 + dot w.2.1)) = w.1.1
      rw [hd, add_sub_cancel_right]
    · exact Subtype.ext hd
  map_add' a b := by
    apply Prod.ext
    · apply Subtype.ext
      change a + b - dot (δ (a + b)) = (a - dot (δ a)) + (b - dot (δ b))
      rw [map_add, map_add]
      abel
    · exact Subtype.ext (map_add δ a b)
  map_smul' r a := by
    apply Prod.ext
    · apply Subtype.ext
      change r • a - dot (δ (r • a)) = r • (a - dot (δ a))
      rw [map_smul, map_smul, smul_sub]
    · exact Subtype.ext (map_smul δ r a)

/-- The rightmost higher kernel is two copies of the image of the equal-black
crossing. Multiplication by the first black dot is a section. -/
def fiveSlotRightmostKernel_equiv_nilHeckeRangeProd :
    K ≃ₗ[Aᵐᵒᵖ] LinearMap.range d × LinearMap.range d :=
  nilHeckeRangeProd d u (rightmostKernel_d_sq Q Λ) (rightmostKernel_d_u_of_d_zero Q Λ)

end KernelSum

end Categorification.Stendhal.BraidedStendhalAlgebra
