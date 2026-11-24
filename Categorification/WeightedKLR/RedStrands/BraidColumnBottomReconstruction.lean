/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomPermutation

/-!
# Reconstruction of a reordered braid bottom

Webster, arXiv:1309.3796v3, proof of Lemma 6.12, p. 66. Every nonviolated
bottom with a specified red order is a red-led block permutation of an
ordinary ordered loading. Reading the block lengths after red relabeling
and transporting them along the inverse permutation gives the coordinates.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv
open scoped BigOperators

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- A nonviolated bottom with the prescribed red order is a permutation of
the red-led blocks of an ordinary red-ordered loading. -/
theorem exists_braidBottomBlockReconstruction (c : Seq μ) (σ : Perm (Fin ℓ))
    (hc : redWord c = (List.finRange ℓ).map σ) (hv : ¬ IsViolated c) :
    ∃ (b : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m),
      IsRedOrdered b ∧
      (∀ r : Fin ℓ, b.lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r) ∧
      braidBlockPermutation n hn σ • b = c := by
  let u := Seq.redPerm σ.symm c
  have huWord : redWord u = List.finRange ℓ := by
    change redWord (Seq.redPerm σ.symm c) = _
    rw [BraidedStendhalAlgebra.redWord_redPerm, hc, List.map_map]
    simp [Function.comp_def]
  have huv : ¬ IsViolated u := by
    rintro ⟨hm,h⟩
    apply hv
    refine ⟨hm, ?_⟩
    change (Sum.map id σ.symm (c.lbl ⟨0,hm⟩)).isLeft at h
    cases hcolor : c.lbl ⟨0,hm⟩ <;> simp_all
  obtain ⟨n',hn',hr⟩ := exists_braidBlockPositions u ((redWord_eq_finRange_iff _).1 huWord) huv
  let n := n' ∘ σ.symm
  have hn : (∑ r, (n r + 1)) = m := (Equiv.sum_comp σ.symm fun r => n' r + 1).trans hn'
  have hout : n ∘ σ = n' := by
    funext r
    simp [n,Function.comp_def]
  let B := braidBlockPermutation n hn σ
  let b := B⁻¹ • c
  have hpos (r : Fin ℓ) :
      braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r,0⟩ =
      braidBlockPositions n' hn' ⟨r,0⟩ := by
    apply Fin.ext
    simp only [braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSigmaFinEquiv_apply, Fin.val_zero, add_zero, hout]
  have hred (r : Fin ℓ) : c.lbl (braidBlockPositions n' hn' ⟨r,0⟩) = .inr (σ r) := by
    have h := hr r
    change (Seq.redPerm σ.symm c).lbl _ = _ at h
    rw [Seq.redPerm_lbl] at h
    cases hcol : c.lbl (braidBlockPositions n' hn' ⟨r,0⟩) with
    | inl i => simp [hcol] at h
    | inr q =>
      have he : σ.symm q = r := Sum.inr_injective (by simpa only [hcol, Sum.map_inr] using h)
      exact congrArg Sum.inr ((Equiv.symm_apply_eq σ).1 he)
  have hb (r : Fin ℓ) : b.lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r := by
    obtain ⟨q,rfl⟩ := σ.surjective r
    change (B⁻¹ • c).lbl _ = _
    rw [BraidedStendhalAlgebra.lbl_smul, inv_inv]
    change c.lbl (braidBlockPermutation n hn σ (braidBlockPositions n hn ⟨σ q,0⟩)) = _
    rw [braidBlockPermutation_apply,hpos,hred]
  refine ⟨b,n,hn,?_,hb,smul_inv_smul _ _⟩
  intro a a' r r' hlt ha ha'
  have he := lbl_eq_inr_unique ha (hb r)
  have he' := lbl_eq_inr_unique ha' (hb r')
  rw [he,he'] at hlt
  exact (braidBlockPositions_red_strictMono n hn).lt_iff_lt.1 hlt

end Categorification.Stendhal
