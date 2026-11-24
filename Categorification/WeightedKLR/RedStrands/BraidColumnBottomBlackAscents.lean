/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomPermutation

/-!
# Adjacent black ascents in a bottom-permuted braid column

Webster, arXiv:1309.3796v3, proof of Lemma 6.12, p. 66. Adjacent black
positions of the reordered bottom lie in one block because successive
blocks are separated by their leading red. The projective index is
increasing on its original bottom black blocks, so the reordered wiring
has an ascent at each such pair.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

private theorem braidBlockPositions_lt_red (n : Fin ℓ → ℕ) {d : ℕ}
    (hn : (∑ r, (n r + 1)) = d) {r p : Fin ℓ} (hr : r < p) (a : Fin (n r + 1)) :
    braidBlockPositions n hn ⟨r, a⟩ < braidBlockPositions n hn ⟨p, 0⟩ := by
  let q : Fin ℓ := ⟨r.val + 1, by omega⟩
  apply lt_of_lt_of_le (b := braidBlockPositions n hn ⟨q, 0⟩)
  · simp only [braidBlockPositions, Equiv.trans_apply, Fin.lt_def, finCongr_apply,
      Fin.val_cast, finSigmaFinEquiv_apply, Fin.val_zero, add_zero]
    let f : Fin (r.val + 1) → ℕ := fun j => n (Fin.castLE (by omega) j) + 1
    change (∑ x : Fin r.val, f x.castSucc) + a.val < ∑ x : Fin (r.val + 1), f x
    rw [Fin.sum_univ_castSucc f]
    exact Nat.add_lt_add_left a.isLt _
  · apply (braidBlockPositions_red_strictMono n hn).monotone
    exact hr

private theorem braidBlockPositions_lt_iff (n : Fin ℓ → ℕ) {d : ℕ}
    (hn : (∑ r, (n r + 1)) = d) (r : Fin ℓ) (a b : Fin (n r + 1)) :
    braidBlockPositions n hn ⟨r, a⟩ < braidBlockPositions n hn ⟨r, b⟩ ↔ a < b := by
  simp only [braidBlockPositions, Equiv.trans_apply, Fin.lt_def, finCongr_apply,
    Fin.val_cast, finSigmaFinEquiv_apply, Nat.add_lt_add_iff_left]

variable [DecidableEq I]
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- A pair of adjacent black strands in the reordered bottom belongs to the
same block. The original minimality condition gives an ascent, under the original
projective eligibility condition. -/
theorem braidColumnBottomBlockIndex_adjacent_black_ascent
    (s : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    {φ : Perm (Fin m)} (hφ : ProjectiveBlockIndex s φ)
    (hr : ∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r)
    {j : ℕ} (hj : j + 1 < m) {i i' : I}
    (hi : ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • s).lbl ⟨j, by omega⟩ = .inl i)
    (hi' : ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • s).lbl ⟨j+1,hj⟩ = .inl i') :
    braidColumnBottomBlockIndex n hn σ φ ⟨j, by omega⟩ <
      braidColumnBottomBlockIndex n hn σ φ ⟨j+1,hj⟩ := by
  let c := φ⁻¹ • s
  let hn' : (∑ r, ((n ∘ σ) r + 1)) = m := (Equiv.sum_comp σ fun r => n r + 1).trans hn
  let p := braidBlockPositions (n ∘ σ) hn'
  let x : Fin m := ⟨j, by omega⟩
  let y : Fin m := ⟨j+1,hj⟩
  obtain ⟨⟨r,a⟩, hx⟩ := p.surjective x
  obtain ⟨⟨r',a'⟩, hy⟩ := p.surjective y
  have red (q : Fin ℓ) : (braidBlockPermutation n hn σ • c).lbl (p ⟨q,0⟩) = .inr (σ q) :=
    (lbl_braidBlockPermutation_smul c n hn σ q 0).trans (hr (σ q))
  have hxBlack : (braidBlockPermutation n hn σ • c).lbl (p ⟨r,a⟩) = .inl i := by
    rw [hx]
    rwa [braidColumnBottomBlockIndex_bottom] at hi
  have hyBlack : (braidBlockPermutation n hn σ • c).lbl (p ⟨r',a'⟩) = .inl i' := by
    rw [hy]
    rwa [braidColumnBottomBlockIndex_bottom] at hi'
  have hapos : 0 < a := by
    apply lt_of_le_of_ne (Fin.zero_le _)
    intro h
    rw [← h, red] at hxBlack
    cases hxBlack
  have hap' : 0 < a' := by
    apply lt_of_le_of_ne (Fin.zero_le _)
    intro h
    rw [← h, red] at hyBlack
    cases hyBlack
  have hxy : p ⟨r,a⟩ < p ⟨r',a'⟩ := by
    rw [hx,hy]
    exact Nat.lt_succ_self _
  have hrr : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · have h1 := braidBlockPositions_lt_red (n ∘ σ) hn' hlt a
      have h2 := (braidBlockPositions_lt_iff (n ∘ σ) hn' r' 0 a').2 hap'
      rw [hx] at h1
      rw [hy] at h2
      have h1' : j < (p ⟨r',0⟩).val := h1
      have h2' : (p ⟨r',0⟩).val < j + 1 := h2
      omega
    · exact heq
    · have h1 := braidBlockPositions_lt_red (n ∘ σ) hn' hgt a'
      have h2 := (braidBlockPositions_lt_iff (n ∘ σ) hn' r 0 a).2 hapos
      exact (not_lt_of_ge (h1.trans h2).le hxy).elim
  subst r'
  have haa := (braidBlockPositions_lt_iff (n ∘ σ) hn' r a a').1 hxy
  have hi₀ : c.lbl (braidBlockPositions n hn ⟨σ r,a⟩) = .inl i :=
    (lbl_braidBlockPermutation_smul c n hn σ r a).symm.trans hxBlack
  have hi₁ : c.lbl (braidBlockPositions n hn ⟨σ r,a'⟩) = .inl i' :=
    (lbl_braidBlockPermutation_smul c n hn σ r a').symm.trans hyBlack
  have horder := hφ.bottom_block_order _ _ _ _ hi₀ hi₁
    ((braidBlockPositions_lt_iff n hn (σ r) a a').2 haa)
  have horder' : φ (braidBlockPositions n hn ⟨σ r,a⟩) <
      φ (braidBlockPositions n hn ⟨σ r,a'⟩) := horder (by
    intro q h
    have he := eq_redPos (hr q)
    rw [← he] at h
    rcases lt_trichotomy q (σ r) with hlt | heq | hgt
    · have ht := braidBlockPositions_lt_red n hn hlt (0 : Fin (n q + 1))
      have ht' := (braidBlockPositions_lt_iff n hn (σ r) 0 a).2 hapos
      exact (not_lt_of_ge (ht.trans ht').le h.1)
    · subst q
      exact (not_lt_of_ge ((braidBlockPositions_lt_iff n hn (σ r) 0 a).2 hapos).le h.1)
    · exact not_lt_of_ge (braidBlockPositions_lt_red n hn hgt a').le h.2)
  change braidColumnBottomBlockIndex n hn σ φ x < braidColumnBottomBlockIndex n hn σ φ y
  rw [← hx,← hy]
  exact (braidColumnBottomBlockIndex_apply n hn σ φ r a).symm ▸
    (braidColumnBottomBlockIndex_apply n hn σ φ r a').symm ▸ horder'

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators
variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- A wiring increasing within each relocated block is obtained by the
bottom-block move of an eligible projective wiring. -/
theorem exists_projectiveIndex_of_bottomBlock_strictMono
    (s b : Seq μ) (hs : IsRedOrdered s) (hb : IsRedOrdered b)
    (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    (hr : ∀ r : Fin ℓ, b.lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r)
    (w : Perm (Fin m)) (hw : w • (braidBlockPermutation n hn σ • b) = s)
    (hmono : ∀ r : Fin ℓ, StrictMono (fun a : Fin (n (σ r) + 1) =>
      w (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r,a⟩))) :
    ∃ φ : Perm (Fin m), ProjectiveBlockIndex s φ ∧ φ⁻¹ • s = b ∧
      braidColumnBottomBlockIndex n hn σ φ = w := by
  let φ := w * braidBlockPermutation n hn σ
  have hφ : φ • b = s := by simpa only [φ,mul_smul] using hw
  have hφb : φ⁻¹ • s = b := by rw [← hφ, inv_smul_smul]
  let p := braidBlockPositions n hn
  have hφMono (r : Fin ℓ) : StrictMono (fun a : Fin (n r + 1) => φ (p ⟨r,a⟩)) := by
    obtain ⟨r, rfl⟩ := σ.surjective r
    intro a a' ha
    change w (braidBlockPermutation n hn σ (p ⟨σ r,a⟩)) <
      w (braidBlockPermutation n hn σ (p ⟨σ r,a'⟩))
    rw [braidBlockPermutation_apply,braidBlockPermutation_apply]
    exact hmono r ha
  have hred (r : Fin ℓ) : p ⟨r,0⟩ = redPos b r := eq_redPos (hr r)
  have hred' (r : Fin ℓ) : φ (p ⟨r,0⟩) = redPos s r := by
    apply eq_redPos
    rw [← hφ, BraidedStendhalAlgebra.lbl_smul]
    simpa only [Perm.inv_def, Equiv.symm_apply_apply] using hr r
  have positive {r : Fin ℓ} {a : Fin (n r + 1)} {i : I}
      (ha : b.lbl (p ⟨r,a⟩) = .inl i) : 0 < a := by
    apply lt_of_le_of_ne (Fin.zero_le _)
    intro h
    rw [← h, hr] at ha
    cases ha
  refine ⟨φ, ?_, hφb, ?_⟩
  · constructor
    · rwa [hφb]
    · dsimp only
      rw [hφb]
      intro a i r ha hbefore
      obtain ⟨⟨q,o⟩, rfl⟩ := p.surjective a
      have hle : r ≤ q := by
        by_contra h
        have hlt := braidBlockPositions_lt_red n hn (lt_of_not_ge h) o
        rw [hred] at hlt
        exact (not_lt_of_ge hlt.le) hbefore
      have ht : redPos s r ≤ redPos s q := by
        rcases hle.lt_or_eq with h | rfl
        · exact ((redPos_lt_iff hs).2 h).le
        · exact le_rfl
      exact ht.trans_lt ((hred' q) ▸ hφMono q (positive ha))
    · dsimp only
      rw [hφb]
      intro a a' i i' ha ha' hlt hbetween
      obtain ⟨⟨r,o⟩, rfl⟩ := p.surjective a
      obtain ⟨⟨r',o'⟩, rfl⟩ := p.surjective a'
      have hsame : r = r' := by
        rcases lt_trichotomy r r' with h | he | h
        · exact (hbetween r' ⟨(hred r') ▸ braidBlockPositions_lt_red n hn h o,
            (hred r') ▸ (braidBlockPositions_lt_iff n hn r' 0 o').2 (positive ha')⟩).elim
        · exact he
        · have h₁ := braidBlockPositions_lt_red n hn h o'
          have h₂ := (braidBlockPositions_lt_iff n hn r 0 o).2 (positive ha)
          exact (not_lt_of_ge (h₁.trans h₂).le hlt).elim
      subst r'
      exact hφMono r ((braidBlockPositions_lt_iff n hn r o o').1 hlt)
  · change (w * braidBlockPermutation n hn σ) * (braidBlockPermutation n hn σ)⁻¹ = _
    rw [mul_assoc, mul_inv_cancel, mul_one]

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators
variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- Ascents at every adjacent pair with a black right slot imply eligibility.
The relocated red slots are the zero offsets, so all consecutive positions
inside a block have a black right slot. -/
theorem exists_projectiveIndex_of_bottomBlock_adjacent_ascents
    (s b : Seq μ) (hs : IsRedOrdered s) (hb : IsRedOrdered b)
    (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    (hr : ∀ r : Fin ℓ, b.lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r)
    (w : Perm (Fin m)) (hw : w • (braidBlockPermutation n hn σ • b) = s)
    (hascent : ∀ (j : ℕ) (hj : j + 1 < m),
      ((braidBlockPermutation n hn σ • b).lbl ⟨j+1,hj⟩).isLeft →
      w ⟨j,by omega⟩ < w ⟨j+1,hj⟩) :
    ∃ φ : Perm (Fin m), ProjectiveBlockIndex s φ ∧ φ⁻¹ • s = b ∧
      braidColumnBottomBlockIndex n hn σ φ = w := by
  apply exists_projectiveIndex_of_bottomBlock_strictMono s b hs hb n hn σ hr w hw
  intro r
  let hn' : (∑ r, ((n ∘ σ) r + 1)) = m := (Equiv.sum_comp σ fun r => n r + 1).trans hn
  let p := braidBlockPositions (n ∘ σ) hn'
  change StrictMono (fun a : Fin (n (σ r) + 1) => w (p ⟨r,a⟩))
  rw [Fin.strictMono_iff_lt_succ]
  intro a
  let x := p ⟨r,a.castSucc⟩
  let y := p ⟨r,a.succ⟩
  have hxy : x.val + 1 = y.val := by
    simp only [x,y,p,braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSigmaFinEquiv_apply, Fin.val_castSucc, Fin.val_succ]
    omega
  have hyBlack : ((braidBlockPermutation n hn σ • b).lbl y).isLeft := by
    cases he : (braidBlockPermutation n hn σ • b).lbl y with
    | inl i => rfl
    | inr k =>
      obtain ⟨q,rfl⟩ := σ.surjective k
      have hred : (braidBlockPermutation n hn σ • b).lbl (p ⟨q,0⟩) = .inr (σ q) :=
        (lbl_braidBlockPermutation_smul b n hn σ q 0).trans (hr (σ q))
      have h := p.injective (lbl_eq_inr_unique he hred)
      have hv := congrArg (fun v : Σ r : Fin ℓ, Fin ((n ∘ σ) r + 1) => v.2.val) h
      change a.val + 1 = 0 at hv
      omega
  have hj : x.val + 1 < m := hxy ▸ y.isLt
  have hy : (⟨x.val+1,hj⟩ : Fin m) = y := Fin.ext hxy
  change w x < w y
  exact hy ▸ hascent x.val hj (hy.symm ▸ hyBlack)

end Categorification.Stendhal
