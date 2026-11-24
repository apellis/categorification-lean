/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Categorification.KLR.MackeyIntertwine
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationCancel
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.WeightedKLR.RedStrands.StandardBlocks

/-!
# Red-led block permutations in a braid column

Webster, arXiv:1309.3796v2, Proposition 5.20 and the proof of Lemma 6.11
on pp. 65–66. Compose an eligible projective wiring with the upper permutation
of red strands and their following black blocks. The resulting wiring keeps
the original bottom loading and has the prescribed top red order.

The PBW word-change estimate gives shorter subword terms after projecting to
the same loading pair. The factorization of these terms through the earlier
eligible diagrams needed for the standard filtration is a further step.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν

/-- Read the blocks of consecutive positions in their row order. The parameter
(n) records the number of black strands after each red. -/
def braidBlockPositions (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m) :
    (Σ r : Fin ℓ, Fin (n r + 1)) ≃ Fin m :=
  finSigmaFinEquiv.trans (finCongr hn)

/-- Reorder whole red-led blocks, preserving the order inside each block.
The red at output rank (r) is the input red (sigma(r)). -/
def braidBlockPermutation (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m)
    (σ : Perm (Fin ℓ)) : Perm (Fin m) :=
  (braidBlockPositions n hn).symm.trans
    ((Equiv.sigmaCongrLeft (β := fun r => Fin (n r + 1)) σ).symm.trans
      (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn)))

theorem braidBlockPermutation_apply (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m)
    (σ : Perm (Fin ℓ)) (r : Fin ℓ) (a : Fin (n (σ r) + 1)) :
    braidBlockPermutation n hn σ (braidBlockPositions n hn ⟨σ r, a⟩) =
      braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, a⟩ := by
  simp only [braidBlockPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  have h : (Equiv.sigmaCongrLeft (β := fun r => Fin (n r + 1)) σ) ⟨r, a⟩ =
      ⟨σ r, a⟩ := rfl
  rw [← h, Equiv.symm_apply_apply]

theorem braidBlockPositions_red_strictMono (n : Fin ℓ → ℕ) {m : ℕ}
    (hn : (∑ r, (n r + 1)) = m) :
    StrictMono (fun r : Fin ℓ => braidBlockPositions n hn ⟨r, 0⟩) := by
  cases ℓ with
  | zero => intro r; exact r.elim0
  | succ ℓ =>
    rw [Fin.strictMono_iff_lt_succ]
    intro r
    simp only [braidBlockPositions, Equiv.trans_apply, Fin.lt_def, finCongr_apply, Fin.val_cast,
      finSigmaFinEquiv_apply, Fin.val_zero, add_zero]
    let f : Fin (r.val + 1) → ℕ := fun j => n (Fin.castLE (by omega) j) + 1
    change (∑ x : Fin r.val, f x.castSucc) < ∑ x : Fin (r.val + 1), f x
    calc
      _ < (∑ x : Fin r.val, f x.castSucc) + f (Fin.last r.val) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos _)
      _ = _ := (Fin.sum_univ_castSucc f).symm

/-- Reading a strand after moving its block returns its original label. -/
theorem lbl_braidBlockPermutation_smul (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = Multiset.card μ) (σ : Perm (Fin ℓ)) (r : Fin ℓ)
    (a : Fin (n (σ r) + 1)) :
    (braidBlockPermutation n hn σ • s).lbl
        (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, a⟩) =
      s.lbl (braidBlockPositions n hn ⟨σ r, a⟩) := by
  rw [← braidBlockPermutation_apply n hn σ r a, BraidedStendhalAlgebra.lbl_smul]
  simp

variable [DecidableEq I]

theorem redWord_braidBlockPermutation_smul (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = Multiset.card μ) (σ : Perm (Fin ℓ))
    (hr : ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) :
    redWord (braidBlockPermutation n hn σ • s) = (List.finRange ℓ).map σ := by
  let t := braidBlockPermutation n hn σ • s
  let u := Seq.redPerm σ.symm t
  let p := fun r : Fin ℓ => braidBlockPositions (n ∘ σ)
    ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, 0⟩
  have hp (r : Fin ℓ) : u.lbl (p r) = .inr r := by
    change (Seq.redPerm σ.symm t).lbl (p r) = _
    rw [Seq.redPerm_lbl, show t.lbl (p r) = .inr (σ r) from
      (lbl_braidBlockPermutation_smul s n hn σ r 0).trans (hr (σ r))]
    simp
  have hu : IsRedOrdered u := by
    intro a b r r' hab ha hb
    have ha' := lbl_eq_inr_unique ha (hp r)
    have hb' := lbl_eq_inr_unique hb (hp r')
    rw [ha', hb'] at hab
    exact (braidBlockPositions_red_strictMono (n ∘ σ) _).lt_iff_lt.mp hab
  have hEq := (redWord_eq_finRange_iff u).2 hu
  change redWord t = _
  rw [show t = Seq.redPerm σ u by
    dsimp [u]
    rw [Seq.redPerm_redPerm, show σ * σ.symm = 1 from mul_inv_cancel σ, Seq.redPerm_one],
    BraidedStendhalAlgebra.redWord_redPerm, hEq]

/-- The index used in the braid column is the input wiring followed by the
permutation of the red-led blocks at its upper end. -/
def braidColumnBlockIndex (n : Fin ℓ → ℕ) {m : ℕ} (hn : (∑ r, (n r + 1)) = m)
    (σ : Perm (Fin ℓ)) (φ : Perm (Fin m)) : Perm (Fin m) :=
  braidBlockPermutation n hn σ * φ

theorem braidColumnBlockIndex_injective (n : Fin ℓ → ℕ) {m : ℕ}
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ)) :
    Function.Injective (braidColumnBlockIndex n hn σ) :=
  fun _ _ h => mul_left_cancel h

omit [DecidableEq I] in
theorem braidColumnBlockIndex_smul (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = Multiset.card μ) (σ : Perm (Fin ℓ)) (φ : Perm (Fin (Multiset.card μ))) :
    braidColumnBlockIndex n hn σ φ • s = braidBlockPermutation n hn σ • (φ • s) :=
  mul_smul _ _ _

/-- Eligible wirings for the projective filtration of Proposition 5.20.
Read from top to bottom, a black strand only moves to a weakly earlier block.
The minimal representative preserves the order within each bottom black block. -/
structure ProjectiveBlockIndex (s : Seq μ) (φ : Perm (Fin (Multiset.card μ))) : Prop where
  bottom_ordered : IsRedOrdered (φ⁻¹ • s)
  only_rightwards :
    let b := φ⁻¹ • s
    ∀ a i r, b.lbl a = .inl i → redPos b r < a → redPos s r < φ a
  bottom_block_order :
    let b := φ⁻¹ • s
    ∀ a a' i j, b.lbl a = .inl i → b.lbl a' = .inl j → a < a' →
      (∀ r, ¬ (a < redPos b r ∧ redPos b r < a')) → φ a < φ a'

omit [DecidableEq I] in
theorem braidColumnBlockIndex_bottom (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = Multiset.card μ) (σ : Perm (Fin ℓ))
    (φ : Perm (Fin (Multiset.card μ))) :
    (braidColumnBlockIndex n hn σ φ)⁻¹ • (braidBlockPermutation n hn σ • s) = φ⁻¹ • s := by
  rw [braidColumnBlockIndex, mul_inv_rev, mul_smul, inv_smul_smul]

/-- The ordered projective indices give eligible diagram indices in the actual braid column. -/
def braidColumnIndexOfProjective (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = Multiset.card μ) (σ : Perm (Fin ℓ)) :
    {φ // ProjectiveBlockIndex s φ} →
    {w : Perm (Fin (Multiset.card μ)) //
      redWord (w⁻¹ • (braidBlockPermutation n hn σ • s)) = List.finRange ℓ} :=
  fun φ => ⟨braidColumnBlockIndex n hn σ φ.1, by
    rw [braidColumnBlockIndex_bottom]
    exact (redWord_eq_finRange_iff _).2 φ.2.bottom_ordered⟩

omit [DecidableEq I] in
theorem braidColumnIndexOfProjective_injective (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = Multiset.card μ) (σ : Perm (Fin ℓ)) :
    Function.Injective (braidColumnIndexOfProjective s n hn σ) := by
  intro φ ψ h
  exact Subtype.ext (braidColumnBlockIndex_injective n hn σ (congrArg Subtype.val h))

private theorem sum_block_gaps (c : ℕ → ℕ) (hc : Monotone c) (n : ℕ) :
    (∑ i : Fin n, (c (i.val + 1) - c i.val)) = c n - c 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n, (c (i.val + 1) - c i.val)) + (c (n + 1) - c n) =
      c (n + 1) - c 0
    rw [ih]
    have h0 := hc (Nat.zero_le n)
    have h1 : c n ≤ c (n + 1) := hc (Nat.le_succ n)
    omega

/-- Every nonviolated ordered loading is the row of its red-led blocks. The
lengths are the gaps between consecutive red positions, ending at the last slot. -/
theorem exists_braidBlockPositions (s : Seq μ) (hs : IsRedOrdered s) (hv : ¬ IsViolated s) :
    ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = Multiset.card μ),
      ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r := by
  let c (j : ℕ) := if h : j < ℓ then (redPos s ⟨j, h⟩).val else Multiset.card μ
  have hc : Monotone c := by
    intro a b hab
    dsimp [c]
    split_ifs with hₐ hᵦ hᵦ'
    · rcases hab.lt_or_eq with hlt | hEq
      · exact ((redPos_lt_iff hs).2 (show (⟨a, hₐ⟩ : Fin ℓ) < ⟨b, hᵦ⟩ from hlt)).le
      · subst b
        rfl
    · exact (redPos s ⟨a, hₐ⟩).isLt.le
    · omega
    · exact le_rfl
  have hcStep (j : Fin ℓ) : c j.val < c (j.val + 1) := by
    dsimp [c]
    rw [ite_eq_left j.isLt]
    split_ifs with h
    · exact (redPos_lt_iff hs).2 (show j < ⟨j.val + 1, h⟩ from Nat.lt_succ_self _)
    · exact (redPos s j).isLt
  have hc0 : c 0 = 0 := by
    by_cases hm : 0 < Multiset.card μ
    · cases hl : s.lbl ⟨0, hm⟩ with
      | inl i => exact (hv ⟨hm, by simp [hl]⟩).elim
      | inr r =>
        have hp := eq_redPos hl
        have hr : r.val = 0 := by
          by_contra hn
          have hℓ : 0 < ℓ := Nat.zero_lt_of_lt r.isLt
          have h := (redPos_lt_iff hs).2 (show (⟨0, hℓ⟩ : Fin ℓ) < r from
            Nat.pos_of_ne_zero hn)
          rw [← hp] at h
          exact (Nat.not_lt_zero _ h).elim
        have hℓ : 0 < ℓ := Nat.zero_lt_of_lt r.isLt
        have he : (⟨0, hℓ⟩ : Fin ℓ) = r := Fin.ext hr.symm
        simpa only [c, dite_eq_left hℓ, he] using (congrArg Fin.val hp).symm
    · have hℓ : ¬ 0 < ℓ := fun h => hm (Nat.zero_lt_of_lt (redPos s ⟨0, h⟩).isLt)
      simp [c, hℓ, Nat.eq_zero_of_not_pos hm]
  let n (r : Fin ℓ) := c (r.val + 1) - c r.val - 1
  have hn1 (r : Fin ℓ) : n r + 1 = c (r.val + 1) - c r.val := by
    have := hcStep r
    dsimp [n]
    omega
  have hcard : (∑ r, (n r + 1)) = Multiset.card μ := by
    simp only [hn1, sum_block_gaps _ hc, hc0, Nat.sub_zero, c, dite_eq_right (lt_irrefl ℓ)]
  refine ⟨n, hcard, fun r => ?_⟩
  have hpos : braidBlockPositions n hcard ⟨r, 0⟩ = redPos s r := by
    apply Fin.ext
    simp only [braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSigmaFinEquiv_apply, Fin.val_zero, add_zero, hn1, Fin.val_castLE,
      sum_block_gaps _ hc, hc0, Nat.sub_zero, c, dite_eq_left r.isLt]
  rw [hpos, lbl_redPos]

omit [DecidableEq I] in
/-- An eligible representative has no right descent at an adjacent pair in a
bottom black block. -/
theorem ProjectiveBlockIndex.length_mul_sadj
    {s : Seq μ} {φ : Perm (Fin (Multiset.card μ))} (hφ : ProjectiveBlockIndex s φ)
    {j : ℕ} (hj : j + 1 < Multiset.card μ) {i i' : I}
    (h₁ : (φ⁻¹ • s).lbl ⟨j, by omega⟩ = .inl i)
    (h₂ : (φ⁻¹ • s).lbl ⟨j + 1, hj⟩ = .inl i') :
    TypeA.length _ (φ * sadj _ j) = TypeA.length _ φ + 1 := by
  apply length_mul_sadj_of_lt hj
  exact hφ.bottom_block_order _ _ i i' h₁ h₂ (Nat.lt_succ_self _) (fun _ h => by
    have h₁ : j < (redPos (φ⁻¹ • s) _).val := h.1
    have h₂ : (redPos (φ⁻¹ • s) _).val < j + 1 := h.2
    omega)

section WordChange

open BraidedStendhalAlgebra

variable {k : Type} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin ℓ → I →₀ ℕ}

local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν

/-- Project the raw diagram to a fixed pair of loadings in the violated column. -/
noncomputable def braidColumnLoadingProjection (top bottom : Seq μ) : R →ₗ[k] V :=
  (((violMk k Q Λ ν).comp (ofKLR k Q Λ ν)).toLinearMap).comp
    (LinearMap.mulLeft k (e top) ∘ₗ LinearMap.mulRight k (e bottom))

/-- Changing the reduced expression for a permuted projective index produces
shorter subword terms with the same top and bottom loading projections. -/
theorem braidColumnBlockIndex_wordChange (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    (φ : {φ : Perm (Fin m) // ProjectiveBlockIndex s φ})
    {u v : List ℕ} (hu : IsReduced m u) (hv : IsReduced m v)
    (h₁ : wordProd m u = (braidColumnIndexOfProjective s n hn σ φ).val)
    (h₂ : wordProd m v = (braidColumnIndexOfProjective s n hn σ φ).val)
    (p : MvPolynomial (Fin m) k) :
    let t := braidBlockPermutation n hn σ • s
    let b := φ.val⁻¹ • s
    let f := braidColumnLoadingProjection (Q := Q) (Λ := Λ) t b
    f (ψw u * pol p * e b) - f (ψw v * pol p * e b) ∈
      (lowSpan k (stendhalQ Q Λ) μ (subProds m u) (u.length - 2)).map f := by
  intro t b f
  rw [← map_sub]
  exact Submodule.mem_map_of_mem <|
    braidEquiv_sub_mem_lowSpan (braidEquiv_of_isReduced hu hv (h₁.trans h₂.symm)) hu.1 p b

end WordChange

end Categorification.Stendhal

