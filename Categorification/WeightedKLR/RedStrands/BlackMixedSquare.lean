/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackMixedCrossing
import Categorification.KLR.MixedSquare.DoubleLast
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeTower

/-!
# The quadratic relation for the mixed crossings of appended black strands

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Khovanov–Lauda I, §2.1 (the relation `ψ² 1_{…ji} = Q_{ji}(x, x') 1_{…ji}` for `i ≠ j`).

With `δ = i + (j + ν)`, the affine cover `R(b + (c + μ))` (`b = i`, `c = j` black, `μ` the
Stendhal weight of `ν`) maps onto `T^λ_δ` by `mixedProj`. Under it the two orders of appending
black strands are the images of `doubleLast` (`mixedProj_doubleLast`,
`mixedProj_cast_doubleLast`), and both signed crossings are the image of `-ψ_n`. The KLR
quadratic relation then gives

`mixedCrossElem_mul_mixedCrossRevElem : χ_{ij} χ_{ji} = Q_{ji}(y_n, y_{n+1}) · p(f_j 1)`,

with `y_n`, `y_{n+1}` the images of the dots on the strands appended first (`j`) and second
(`i`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite AbsentColour.MixedCrossing

set_option backward.isDefEq.respectTransparency false

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i j : I)

set_option hygiene false in
local notation "σ" => stendhalWeight ℓ ν
set_option hygiene false in
local notation "S" => affineCoverQ Q Λ
set_option hygiene false in
local notation "b" => (Sum.inl i : I ⊕ Fin ℓ)
set_option hygiene false in
local notation "c" => (Sum.inl j : I ⊕ Fin ℓ)
set_option hygiene false in
local notation "νi" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νj" => ((Singleton.singleton j : Multiset I) + ν)
set_option hygiene false in
local notation "δ" => ((Singleton.singleton i : Multiset I) + νj)
set_option hygiene false in
local notation "K" => KLRAlgebra k S (({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ))
set_option hygiene false in
local notation "p" => appendBlack (k := k) Q Λ i νj
set_option hygiene false in
local notation "fj" => appendBlack Q Λ j ν
set_option hygiene false in
local notation "fi" => appendBlack Q Λ i ν
set_option hygiene false in
local notation "r" => appendBlackAt (k := k) (Q := Q) Λ j (mixedSwap ν i j)

omit [DecidableEq I] in
theorem mixedDoubleWeight :
    ({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ) = stendhalWeight ℓ δ := by
  rw [← stendhalWeight_black_cons, ← stendhalWeight_black_cons]

/-- The projection of the affine cover with the two black strands `j`, `i` appended last onto
`T^λ_δ`. -/
def mixedProj : K →ₐ[k] TensorProductAlgebra k Q Λ δ :=
  (affineTensorProjection Λ δ).comp (castKLR S (mixedDoubleWeight ν i j)).toAlgHom

variable {Λ ν i j}

private theorem cL_castKLR {β β' : Multiset (I ⊕ Fin ℓ)} (a : I ⊕ Fin ℓ) (h : β = β')
    (y : KLRAlgebra k S β) :
    cL S a β' (castKLR S h y) = castKLR S (congrArg ({a} + ·) h) (cL S a β y) := by
  subst h; rfl

private theorem castTPA_proj {β β' : Multiset I} (h : β = β')
    (z : KLRAlgebra k S (stendhalWeight ℓ β)) :
    castTensorProductAlgebra Q Λ h (affineTensorProjection Λ β z) =
      affineTensorProjection Λ β' (castKLR S (congrArg (stendhalWeight ℓ) h) z) := by
  subst h; rfl

private theorem castTPA_appendBlack {μ β : Multiset I} (a : I) (h : ({a} : Multiset I) + μ = β)
    (y : TensorProductAlgebra k Q Λ μ) :
    castTensorProductAlgebra Q Λ h (appendBlack Q Λ a μ y) = appendBlackAt Λ a h y := by
  subst h; rfl

/-- Appending `j` and then `i` is the image of `doubleLast`. -/
theorem mixedProj_doubleLast (x : KLRAlgebra k S σ) :
    p (fj (affineTensorProjection Λ ν x)) = mixedProj Λ ν i j (doubleLast S σ b c x) := by
  rw [appendBlack_affineTensorProjection, appendBlack_affineTensorProjection, cL_castKLR,
    castKLR_castKLR]
  rfl

/-- Appending `i` and then `j` is the image of the transported `doubleLast`. -/
theorem mixedProj_cast_doubleLast (x : KLRAlgebra k S σ) :
    r (fi (affineTensorProjection Λ ν x)) =
      mixedProj Λ ν i j (castKLR S (square σ b c) (doubleLast S σ c b x)) := by
  rw [← castTPA_appendBlack, appendBlack_affineTensorProjection,
    appendBlack_affineTensorProjection, cL_castKLR, castKLR_castKLR, castTPA_proj,
    castKLR_castKLR]
  change _ = affineTensorProjection Λ δ (castKLR S _ (castKLR S _ _))
  rw [castKLR_castKLR]
  rfl

private theorem proj_neg_psi {β : Multiset (I ⊕ Fin ℓ)} (h : β = stendhalWeight ℓ δ) (n : ℕ) :
    affineTensorProjection Λ δ (castKLR S h (-ψ n)) =
      affineTensorProjection (Q := Q) Λ δ (-ψ n) := by
  rw [map_neg, castKLR_ψ, map_neg]

theorem mixedProj_neg_psi :
    mixedProj (Q := Q) Λ ν i j (-ψ (Multiset.card σ)) = mixedBlackCrossing Λ ν i j := by
  have e₁ : (σ + {c}) + {b} = stendhalWeight ℓ δ := by
    rw [← stendhalWeight_black_cons, ← stendhalWeight_black_cons]; ac_rfl
  change _ = affineTensorProjection Λ δ (castKLR S e₁ (-ψ (Multiset.card σ)))
  exact (proj_neg_psi _ _).trans (proj_neg_psi _ _).symm

theorem mixedProj_neg_psi_rev :
    mixedProj (Q := Q) Λ ν i j (-ψ (Multiset.card σ)) =
      castTensorProductAlgebra Q Λ (mixedSwap ν i j) (mixedBlackCrossing Λ ν j i) := by
  have e₁ : (σ + {b}) + {c} = stendhalWeight ℓ ({j} + νi) := by
    rw [← stendhalWeight_black_cons, ← stendhalWeight_black_cons]; ac_rfl
  change _ = castTensorProductAlgebra Q Λ (mixedSwap ν i j)
    (affineTensorProjection Λ _ (castKLR S e₁ (-ψ (Multiset.card σ))))
  rw [castTPA_proj, castKLR_castKLR]
  exact (proj_neg_psi _ _).trans (proj_neg_psi _ _).symm

/-- `D(-t)D' · D'(-t)D = t² D` for idempotents `D, D'` intertwined by `t`. -/
theorem intertwined_idem_sq {R : Type*} [Ring R] {D D' t : R} (h₁ : D * t = t * D')
    (h₂ : D' * t = t * D) (h₃ : D' * D' = D') (h₄ : D * D = D) :
    D * -t * D' * (D' * -t * D) = t * t * D := by
  calc D * -t * D' * (D' * -t * D) = (D * t) * (D' * D') * t * D := by noncomm_ring
    _ = t * D' * D' * t * D := by rw [h₁, h₃]
    _ = t * (D' * D') * t * D := by noncomm_ring
    _ = t * (D' * t) * D := by rw [h₃]; noncomm_ring
    _ = t * t * (D * D) := by rw [h₂]; noncomm_ring
    _ = t * t * D := by rw [h₄]

theorem mixedCrossRevElem_eq :
    mixedCrossRevElem Λ ν i j = r (fi 1) *
      castTensorProductAlgebra Q Λ (mixedSwap ν i j) (mixedBlackCrossing Λ ν j i) * p (fj 1) := by
  unfold mixedCrossRevElem mixedCrossElem
  rw [map_mul, map_mul, cast_appendBlack_mixed, cast_appendBlackAt_mixed]

/-- **The quadratic relation for distinct colours** (KL I, §2.1): for `i ≠ j`, the composite
of the two mixed crossings is `Q_{ji}` evaluated at the dots on the strands appended first
(`j`) and second (`i`), cut by `p(f_j 1)`. -/
theorem mixedCrossElem_mul_mixedCrossRevElem (hij : i ≠ j) :
    mixedCrossElem Λ ν i j * mixedCrossRevElem Λ ν i j =
      ncEval ![mixedProj Λ ν i j (x ⟨Multiset.card σ, by rw [card_double]; omega⟩),
        mixedProj Λ ν i j (x ⟨Multiset.card σ + 1, by rw [card_double]; omega⟩)] (Q j i) *
        p (fj 1) := by
  have hp : p (fj 1) = mixedProj Λ ν i j (doubleLast S σ b c 1) := by
    rw [← map_one (affineTensorProjection (Q := Q) Λ ν), mixedProj_doubleLast]
  have hr : r (fi 1) = mixedProj Λ ν i j (castKLR S (square σ b c) (doubleLast S σ c b 1)) := by
    rw [← map_one (affineTensorProjection (Q := Q) Λ ν), mixedProj_cast_doubleLast]
  rw [mixedCrossRevElem_eq, mixedCrossElem, ← mixedProj_neg_psi, ← mixedProj_neg_psi_rev, hp, hr]
  have hD' : castKLR S (square σ b c) (doubleLast S σ c b 1) *
      castKLR S (square σ b c) (doubleLast S σ c b 1) =
      castKLR S (square σ b c) (doubleLast S σ c b 1) := by
    rw [← map_mul, doubleLast_one_mul_self]
  have key := intertwined_idem_sq (doubleLast_one_intertwine S σ b c)
    (cast_doubleLast_one_mul_psi S σ b c) hD' (doubleLast_one_mul_self S σ b c)
  rw [psi_sq_mul_doubleLast_one S σ b c (Sum.inl_injective.ne hij)] at key
  have key' := congrArg (mixedProj (Q := Q) Λ ν i j) key
  simp only [map_mul] at key'
  rw [key', ncEval_map]
  rfl


/-! ### The dots on the appended strands -/

omit [DecidableEq I] in
theorem card_stendhalWeight_cons (a : I) (μ : Multiset I) :
    Multiset.card (stendhalWeight ℓ (({a} : Multiset I) + μ)) =
      Multiset.card (stendhalWeight ℓ μ) + 1 := by
  rw [← stendhalWeight_black_cons, Multiset.card_add, Multiset.card_singleton]
  omega

/-- The dot on the appended strand is the image of the last KLR dot, cut by `ν_a(1)`. -/
theorem appendedDot_eq (a : I) (μ : Multiset I) :
    appendedDot Q Λ a μ = affineTensorProjection Λ (({a} : Multiset I) + μ)
      (x ⟨Multiset.card (stendhalWeight ℓ μ), by rw [card_stendhalWeight_cons]; omega⟩) *
      appendBlack Q Λ a μ 1 := by
  have h1 : appendBlack Q Λ a μ 1 = TensorProductAlgebra.mk Q Λ _
      ⟨appendBlackValue Q Λ a μ (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ μ),
        E1_mem Q Λ a μ⟩ := rfl
  rw [h1]
  change _ = TensorProductAlgebra.mk Q Λ _ (orderProjection Q Λ _ (affineCover Q Λ _ (x _))) * _
  rw [← map_mul]
  apply congrArg
  apply Subtype.ext
  change _ = affineCover Q Λ _ (x _) * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ _ *
    appendBlackValue Q Λ a μ (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ μ)
  rw [affineCover_x, mul_assoc, ((Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp (E1_mem Q Λ a μ)).1]
  rfl

end Categorification.Stendhal
