/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstBraiding

set_option backward.isDefEq.respectTransparency false

/-!
# Dots commute with the red braid `r_b`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14 (with Corollary 6.8). The braid `r_b` of `bijective_redBraid_mul` is a diagram `r₀`
without black strands, with the black strands of `b` added as straight strands at the right.
Hence every dot commutes with it: a dot on an added black strand slides along the straight
strand, and in weight `0` every strand is red and carries no dots (`commute_redBraid_x`,
`commute_redBraid_pol`). This is what lets a polynomial in the dots, such as the element `y` of
the half twist, pass through the isomorphism `𝔅(κ', κ) P⁰ ≅ P⁰` of Corollary 6.8.

## Main results

* `commute_appendViol_x_last`, `commute_appendViol_x_appendPos`: dots and the append map.
* `commute_redBraid_x`, `commute_redBraid_pol`: dots commute with `r_b`.
-/

noncomputable section

namespace Categorification.Stendhal

open Equiv KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

namespace BraidedStendhalAlgebra

section Append

variable (i : I) (ν : Multiset I)

set_option quotPrecheck false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ" => stendhalWeight ℓ ν

/-- The position of the appended black strand. -/
def lastPos : Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
  ⟨Multiset.card μ, by
    rw [← stendhalWeight_addBlack i ν, Multiset.card_add, Multiset.card_singleton]; omega⟩

theorem commute_x_appendIdem (p : Fin (Multiset.card (stendhalWeight ℓ νᵢ))) :
    Commute (ofKLR k Q Λ νᵢ (KLRAlgebra.x p)) (appendIdem Q Λ i ν) := by
  rw [appendIdem_eq_sum]
  refine Commute.sum_right _ _ _ fun s _ => ?_
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, x_mul_e]

theorem x_appendPos_mul_appendBlack (q : Fin (Multiset.card μ))
    (z : BraidedStendhalAlgebra k Q Λ ν) :
    ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν q)) * (appendBlack Q Λ i ν z).val =
      (appendBlack Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.x q) * z)).val := by
  rw [map_mul, KLR.Corner.val_mul, appendBlack_ofKLR_x, mul_assoc, KLR.Corner.E_mul_val]

theorem appendBlack_mul_x_appendPos (q : Fin (Multiset.card μ))
    (z : BraidedStendhalAlgebra k Q Λ ν) :
    (appendBlack Q Λ i ν z).val * ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν q)) =
      (appendBlack Q Λ i ν (z * ofKLR k Q Λ ν (KLRAlgebra.x q))).val := by
  rw [map_mul, KLR.Corner.val_mul, appendBlack_ofKLR_x, (commute_x_appendIdem i ν _).eq,
    ← mul_assoc, KLR.Corner.val_mul_E]

private theorem appendAmbient_blockR_x :
    appendAmbient Q Λ i ν (((blockR μ {Sum.inl i}).hom (stendhalQ Q Λ)
        (KLRAlgebra.x ⟨0, by simp⟩)).val) =
      ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν)) * appendIdem Q Λ i ν := by
  rw [BlockEmb.hom_x, val_polCorner, pol_X, map_mul]
  congr 1
  change ofKLR k Q Λ νᵢ (castKLR _ _ (KLRAlgebra.x _)) = _
  rw [castKLR_x]
  congr 2

/-- A dot on the appended black strand commutes with every appended diagram. -/
theorem commute_x_last_appendBlack (z : BraidedStendhalAlgebra k Q Λ ν) :
    Commute (ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν))) (appendBlack Q Λ i ν z).val := by
  obtain ⟨w, rfl⟩ := ofKLR_surjective z
  rw [appendBlack_ofKLR]
  have hc := commute_hom_blockL_blockR (Q := stendhalQ Q Λ) w
    (KLRAlgebra.x ⟨0, by simp⟩ : KLRAlgebra k (stendhalQ Q Λ) ({Sum.inl i} : Multiset (I ⊕ Fin ℓ)))
  have h1 : ((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val *
        ((blockR μ {Sum.inl i}).hom (stendhalQ Q Λ) (KLRAlgebra.x ⟨0, by simp⟩)).val =
      ((blockR μ {Sum.inl i}).hom (stendhalQ Q Λ) (KLRAlgebra.x ⟨0, by simp⟩)).val *
        ((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val :=
    congrArg KLR.Corner.val hc.eq
  have hE : appendIdem Q Λ i ν *
      appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) =
      appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) :=
    KLR.Corner.E_mul_val (appendKLR Q Λ i ν w)
  have hE' : appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) *
      appendIdem Q Λ i ν =
      appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) :=
    KLR.Corner.val_mul_E (appendKLR Q Λ i ν w)
  have hA := appendAmbient_blockR_x (Q := Q) (Λ := Λ) i ν
  change ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν)) *
      appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) =
    appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) *
      ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν))
  calc _ = ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν)) * appendIdem Q Λ i ν *
        appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) := by
          rw [mul_assoc, hE]
    _ = appendAmbient Q Λ i ν (((blockL μ {Sum.inl i}).hom (stendhalQ Q Λ) w).val) *
        (ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν)) * appendIdem Q Λ i ν) := by
          rw [← hA, ← map_mul, ← map_mul, h1]
    _ = _ := by
          rw [(commute_x_appendIdem i ν _).eq, ← mul_assoc, hE']

theorem commute_appendViol_x_last (v : ViolQuotient k Q Λ ν) :
    Commute (violMk k Q Λ νᵢ (ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastPos i ν))))
      (appendViol Q Λ i ν v) := by
  obtain ⟨z, rfl⟩ := violMk_surjective v
  rw [appendViol_violMk]
  exact (commute_x_last_appendBlack i ν z).map (violMk k Q Λ νᵢ)

theorem commute_appendViol_x_appendPos (q : Fin (Multiset.card μ)) {v : ViolQuotient k Q Λ ν}
    (hv : Commute (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.x q))) v) :
    Commute (violMk k Q Λ νᵢ (ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν q))))
      (appendViol Q Λ i ν v) := by
  obtain ⟨z, rfl⟩ := violMk_surjective v
  have h := congrArg (appendViol Q Λ i ν) hv.eq
  rw [← map_mul, ← map_mul, appendViol_violMk, appendViol_violMk] at h
  change violMk _ _ _ _ (appendBlack Q Λ i ν _).val = violMk _ _ _ _ (appendBlack Q Λ i ν _).val
    at h
  rw [← x_appendPos_mul_appendBlack, ← appendBlack_mul_x_appendPos, map_mul, map_mul] at h
  rw [appendViol_violMk]
  exact h

end Append

/-- In weight `0` every strand is red, so dots vanish. -/
theorem ofKLR_x_nil (p : Fin (Multiset.card (stendhalWeight ℓ (0 : Multiset I)))) :
    ofKLR k Q Λ 0 (KLRAlgebra.x p) = 0 := by
  rw [← mul_one (KLRAlgebra.x p), ← KLRAlgebra.sum_e, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ofKLR_x_mul_e_of_red _ _ ?_
  have hm := s.mem p
  simp only [stendhalWeight, Multiset.map_zero, zero_add, Multiset.mem_map] at hm
  obtain ⟨r, -, hr⟩ := hm
  rw [Seq.lbl, ← hr]
  rfl

/-- **Dots commute with the red braid `r_b`** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14): `r_b` is `r₀` with straight black strands added at the right. -/
theorem commute_redBraid_x (r₀ : ViolQuotient k Q Λ 0) :
    ∀ (b : List I) (p : Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))),
      Commute (violMk k Q Λ (blackWeight b) (ofKLR k Q Λ _ (KLRAlgebra.x p))) (redBraid r₀ b)
  | [], p => by
    change Commute (violMk k Q Λ 0 (ofKLR k Q Λ 0 (KLRAlgebra.x p))) r₀
    rw [ofKLR_x_nil, map_zero]
    exact Commute.zero_left _
  | i :: b, p => by
    change Commute _ (appendViol Q Λ i (blackWeight b) (redBraid r₀ b))
    by_cases hp : p.val < Multiset.card (stendhalWeight ℓ (blackWeight b))
    · have he : p = appendPos i (blackWeight b) ⟨p.val, hp⟩ := Fin.ext rfl
      rw [he]
      exact commute_appendViol_x_appendPos i (blackWeight b) _ (commute_redBraid_x r₀ b _)
    · have hlt := p.isLt
      have he : p = lastPos i (blackWeight b) := by
        apply Fin.ext
        change p.val = Multiset.card (stendhalWeight ℓ (blackWeight b))
        change p.val < Multiset.card (stendhalWeight ℓ ({i} + blackWeight b)) at hlt
        rw [← stendhalWeight_addBlack i (blackWeight b), Multiset.card_add,
          Multiset.card_singleton] at hlt
        omega
      rw [he]
      exact commute_appendViol_x_last i (blackWeight b) _

/-- Polynomials in the dots commute with the red braid `r_b`. -/
theorem commute_redBraid_pol (r₀ : ViolQuotient k Q Λ 0) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    Commute (violMk k Q Λ (blackWeight b) (ofKLR k Q Λ _ (pol g))) (redBraid r₀ b) := by
  induction g using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.algHom_C, AlgHom.commutes, AlgHom.commutes]; exact Algebra.commute_algebraMap_left _ _
  | add f g hf hg => rw [map_add, map_add, map_add]; exact hf.add_left hg
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, pol_X]
    exact hf.mul_left (commute_redBraid_x r₀ b p)

end BraidedStendhalAlgebra

end Categorification.Stendhal
