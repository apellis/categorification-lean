/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeTower
import Categorification.WeightedKLR.RedStrands.BlackRescale
import Categorification.WeightedKLR.RedStrands.TensorRescale

/-!
# The dot and crossing on new strands as affine projections

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. The dot
`y = x_n · ν_i(1)` on the newly appended black strand (`appendedDot`) is the product of the
projection of the affine dot `x_n` with the image `ν_i(1)` of the unit
(`appendedDot_eq_projection`), and
the crossing `τ = -ψ_n · ν_i(ν_i(1))` (`appendedCross`) is minus the projection of the affine
crossing `ψ_n` times `ν_i(ν_i(1))` (`appendedCross_eq`). Both are fixed by rescaling the black
crossings with same-colour scalars `1` (`tensorRescale_appendedDot`,
`tensorRescale_appendedCross`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Categorification.Stendhal

open KLR StendhalAlgebraAllOrders

variable {I : Type u} {ℓ : ℕ} [DecidableEq I] {k : Type u} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "n" => Multiset.card (stendhalWeight ℓ ν)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" => ((Singleton.singleton i : Multiset I) + νᵢ)

/-- The position of the new strand at weight `ν + i`. -/
def newPos : Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
  ⟨n, by rw [card_stendhalWeight_addBlack]; omega⟩

theorem affineTensorProjection_x {μ : Multiset I} (a : Fin (Multiset.card (stendhalWeight ℓ μ))) :
    affineTensorProjection (Q := Q) Λ μ (KLRAlgebra.x a) =
      TensorProductAlgebra.mk Q Λ μ ⟨x a * redOrderedIdem k Q Λ μ,
        (orderProjection Q Λ μ (x a)).2⟩ := by
  change TensorProductAlgebra.mk Q Λ μ (orderProjection Q Λ μ (affineCover Q Λ μ _)) = _
  rw [affineCover_x]
  rfl

theorem affineTensorProjection_ψ {μ : Multiset I} (j : ℕ) :
    affineTensorProjection (Q := Q) Λ μ (KLRAlgebra.ψ j) =
      TensorProductAlgebra.mk Q Λ μ ⟨ψ j * redOrderedIdem k Q Λ μ,
        (orderProjection Q Λ μ (ψ j)).2⟩ := by
  change TensorProductAlgebra.mk Q Λ μ (orderProjection Q Λ μ (affineCover Q Λ μ _)) = _
  rw [affineCover_ψ]
  rfl

theorem appendBlack_one_eq :
    appendBlack Q Λ i ν 1 = TensorProductAlgebra.mk Q Λ νᵢ
      ⟨appendBlackValue Q Λ i ν (redOrderedIdem k Q Λ ν), E1_mem Q Λ i ν⟩ := by
  rw [tensorProductAlgebra_one, appendBlack_mk_val]

/-- **The dot on the new strand is the projected affine dot times `ν_i(1)`.** -/
theorem appendedDot_eq_projection :
    appendedDot Q Λ i ν =
      affineTensorProjection (Q := Q) Λ νᵢ (KLRAlgebra.x (newPos i ν)) *
        appendBlack Q Λ i ν 1 := by
  rw [affineTensorProjection_x, appendBlack_one_eq, tensorProductAlgebra_mk_mul, appendedDot]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  rw [mul_assoc, corner_left Q Λ (E1_mem Q Λ i ν)]
  rfl

/-- **The crossing of the new strands is minus the projected affine crossing times
`ν_i(ν_i(1))`.** -/
theorem appendedCross_eq :
    appendedCross Q Λ i ν =
      -(affineTensorProjection (Q := Q) Λ νᵢᵢ (KLRAlgebra.ψ n) *
        appendBlack Q Λ i νᵢ (appendBlack Q Λ i ν 1)) := by
  rw [affineTensorProjection_ψ, appendBlack_one_eq, appendBlack_mk_val,
    tensorProductAlgebra_mk_mul, appendedCross, ← map_neg]
  refine congrArg _ (Subtype.ext ?_)
  change -newCross Q Λ i ν * _ = -(ψ n * redOrderedIdem k Q Λ νᵢᵢ * _)
  rw [mul_assoc, corner_left Q Λ (E2_mem Q Λ i ν), neg_mul]
  rfl

section Rescale

open KLRAlgebra

variable {Q} {Q' : I → I → MvPolynomial (Fin 2) k} {s : I → I → kˣ} (hs : ∀ a, s a a = 1)
  (hQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.C ((s a b * s b a : kˣ) : k) * Q' a b)

private theorem cL_sum' {μ : Multiset (I ⊕ Fin ℓ)}
    {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} {ι : Type*}
    (F : Finset ι) (f : ι → KLRAlgebra k R μ) :
    cL R (Sum.inl i) μ (∑ t ∈ F, f t) = ∑ t ∈ F, cL R (Sum.inl i) μ (f t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cL_zero]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cL_add, ih]

private theorem cast_cL_e' {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k}
    (t : Seq (stendhalWeight ℓ ν)) :
    castKLR R (stendhalWeight_black_cons (ℓ := ℓ) i ν)
        (cL R (Sum.inl i) (stendhalWeight ℓ ν) (KLRAlgebra.e t)) =
      KLRAlgebra.e (appendBlackLoading i ν t) := by
  rw [cL_e, castKLR_e]
  exact congrArg _ (Subtype.ext (funext fun _ => rfl))

private theorem castKLR_cL_one {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} :
    castKLR R (stendhalWeight_black_cons (ℓ := ℓ) i ν)
        (cL R (Sum.inl i) (stendhalWeight ℓ ν) 1) =
      ∑ t, KLRAlgebra.e (appendBlackLoading i ν t) := by
  rw [← KLRAlgebra.sum_e, cL_sum', map_sum]
  exact Finset.sum_congr rfl fun t _ => cast_cL_e' i ν t

/-- The image of the unit after adjoining two black strands, on the affine cover. -/
private abbrev twoAppended (R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) :
    KLRAlgebra k R (stendhalWeight ℓ νᵢᵢ) :=
  castKLR R (stendhalWeight_black_cons (ℓ := ℓ) i νᵢ)
    (cL R (Sum.inl i) (stendhalWeight ℓ νᵢ)
      (castKLR R (stendhalWeight_black_cons (ℓ := ℓ) i ν)
        (cL R (Sum.inl i) (stendhalWeight ℓ ν) 1)))

private theorem twoAppended_eq {R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} :
    twoAppended i ν R =
      ∑ t, KLRAlgebra.e (appendBlackLoading i νᵢ (appendBlackLoading i ν t)) := by
  rw [twoAppended, castKLR_cL_one, cL_sum', map_sum]
  exact Finset.sum_congr rfl fun t _ => cast_cL_e' i νᵢ _

private theorem appendBlack_two_eq {R : I → I → MvPolynomial (Fin 2) k} :
    appendBlack R Λ i νᵢ (appendBlack R Λ i ν 1) =
      affineTensorProjection (Q := R) Λ νᵢᵢ (twoAppended i ν (affineCoverQ R Λ)) := by
  rw [← map_one (affineTensorProjection (Q := R) Λ ν), appendBlack_affineTensorProjection,
    appendBlack_affineTensorProjection]

include hs in
private theorem scaleE_mul_twoAppended :
    scaleE (affineCoverQ Q' Λ) (stendhalScale s) n * twoAppended i ν (affineCoverQ Q' Λ) =
      twoAppended i ν (affineCoverQ Q' Λ) := by
  have hc : Multiset.card (stendhalWeight ℓ νᵢᵢ) = n + 2 := by
    rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]
  rw [twoAppended_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [scaleE_mul_e, crossScale_of_lt _ (by omega)]
  have h1 := appendBlackLoading_lbl_of_lt i νᵢ (appendBlackLoading i ν t)
    ⟨n, by omega⟩ (show n < _ by rw [card_stendhalWeight_addBlack]; omega)
  have h1' := appendBlackLoading_lbl_of_eq i ν t ⟨n, by rw [card_stendhalWeight_addBlack]; omega⟩
    rfl
  have h2 := appendBlackLoading_lbl_of_eq i νᵢ (appendBlackLoading i ν t) ⟨n + 1, by omega⟩
    (card_stendhalWeight_addBlack i ν).symm
  simp only [Seq.lbl] at h1 h1' h2
  rw [h1, h1', h2]
  change ((s i i : kˣ) : k) • _ = _
  rw [hs, Units.val_one, one_smul]

/-- Rescaling the black crossings fixes the dot on the new strand. -/
theorem tensorRescale_appendedDot :
    tensorRescale Λ νᵢ hs hQ (appendedDot Q Λ i ν) = appendedDot Q' Λ i ν := by
  rw [appendedDot_eq_projection, appendedDot_eq_projection, map_mul, tensorRescale_x,
    tensorRescale_appendBlack, map_one]

/-- Rescaling the black crossings with same-colour scalars `1` fixes the crossing of the new
strands. -/
theorem tensorRescale_appendedCross :
    tensorRescale Λ νᵢᵢ hs hQ (appendedCross Q Λ i ν) = appendedCross Q' Λ i ν := by
  rw [appendedCross_eq, appendedCross_eq, map_neg, map_mul, tensorRescale_projection,
    tensorRescale_appendBlack, tensorRescale_appendBlack, map_one, rescaleHom_ψ, rescaleψ,
    appendBlack_two_eq, ← map_mul, ← map_mul, mul_assoc, scaleE_mul_twoAppended Λ i ν hs]

end Rescale

end Categorification.Stendhal
