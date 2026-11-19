/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorRescale
import Categorification.WeightedKLR.RedStrands.AffineCoverGrading
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverQuotient

/-!
# The projection to `T^λ` on free-algebra elements

Two auxiliary facts about the projection `affineTensorProjection` from the affine cover to the
tensor-product algebra `T^λ` of Webster, arXiv:1309.3796v3, §4.

* `tensorProjection_mk_eq_zero_iff`: when two families of black parameters `Q`, `Q'` agree off the
  diagonal, the identity rescaling `tensorRescale` (all scalars `1`) identifies `T^λ(Q)` with
  `T^λ(Q')` compatibly with the free-algebra presentations. Hence an element of the free algebra
  on the KLR generators projects to zero in one of them exactly when it does in the other.
* `affineTensorProjection_mk`: on the image of the free algebra, the projection agrees with the
  projection `cyclotomicCoverToTensor` from the cyclotomic quotient of the cover.

These are used in the proof of Lemma 4.29 to compare the downward block, which carries the
Cautis–Lauda dual parameters, with the vacuum evaluation, which is built from a Rouquier family.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLR.KLRAlgebra MvPolynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q Q' : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

/-- With all crossing scalars equal to one, the rescaling of the free algebra is the quotient
map. -/
theorem rescaleFree_eq_mk {J : Type*} [DecidableEq J] {R : J → J → MvPolynomial (Fin 2) k}
    {ν' : Multiset J} {s : J → J → kˣ} (hs : ∀ a b, s a b = 1) :
    rescaleFree ν' R s = mk k R ν' := by
  have hc (j : ℕ) (i : Seq ν') : crossScale s j i = 1 := by
    unfold crossScale
    split_ifs
    · rw [hs, Units.val_one]
    · rfl
  refine FreeAlgebra.hom_ext (funext fun g => ?_)
  cases g with
  | idem i => exact FreeAlgebra.lift_ι_apply _ _
  | dot a => exact FreeAlgebra.lift_ι_apply _ _
  | cross j =>
    change rescaleFree ν' R s (fψ k ν' j) = ψ j
    rw [rescaleFree_fψ, rescaleψ, scaleE]
    simp only [hc, one_smul, sum_e, mul_one]

omit [DecidableEq I] in
theorem stendhalScale_one : ∀ a b : I ⊕ Fin ℓ, stendhalScale (1 : I → I → kˣ) a b = 1
  | .inl _, .inl _ => rfl
  | .inl _, .inr _ => rfl
  | .inr _, .inl _ => rfl
  | .inr _, .inr _ => rfl

omit [DecidableEq I] in
theorem rescale_one_hQ (hQ : ∀ a b, a ≠ b → Q a b = Q' a b) :
    ∀ a b, a ≠ b → Q a b = C (((1 : I → I → kˣ) a b * (1 : I → I → kˣ) b a : kˣ) : k) * Q' a b :=
  fun a b h => by simp [hQ a b h]

/-- The identity rescaling `T^λ(Q) ≅ T^λ(Q')` maps the projection of a free-algebra element
to its projection. -/
theorem tensorRescale_one_mk (hQ : ∀ a b, a ≠ b → Q a b = Q' a b)
    (u : FreeAlgebra k (Gen (stendhalWeight ℓ ν))) :
    tensorRescale Λ ν (s := 1) (fun _ => rfl) (rescale_one_hQ hQ)
        (affineTensorProjection (Q := Q) Λ ν (mk k _ _ u)) =
      affineTensorProjection (Q := Q') Λ ν (mk k _ _ u) := by
  rw [tensorRescale_projection, rescaleHom_mk, rescaleFree_eq_mk (stendhalScale_one)]

/-- **The projection to `T^λ` does not see the diagonal parameters.** If `Q` and `Q'` agree off
the diagonal, a free-algebra element projects to zero in `T^λ(Q)` exactly when it does in
`T^λ(Q')`. -/
theorem tensorProjection_mk_eq_zero_iff (hQ : ∀ a b, a ≠ b → Q a b = Q' a b)
    (u : FreeAlgebra k (Gen (stendhalWeight ℓ ν))) :
    affineTensorProjection (Q := Q) Λ ν (mk k _ _ u) = 0 ↔
      affineTensorProjection (Q := Q') Λ ν (mk k _ _ u) = 0 := by
  rw [← tensorRescale_one_mk Λ ν hQ u, map_eq_zero_iff _ (AlgEquiv.injective _)]

variable (C : QuantumGroup.CartanDatum I)

/-- On free-algebra elements, the projection from the affine cover to `T^λ` agrees with the
projection from the cyclotomic quotient of the cover. -/
theorem affineTensorProjection_mk (v : FreeAlgebra k (Gen (stendhalWeight ℓ ν))) :
    affineTensorProjection (Q := Q) Λ ν (mk k _ _ v) =
      cyclotomicCoverToTensor (Q := Q) Λ ν C
        (CycKLR.mk k _ (cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)) _ (mk k _ _ v)) := by
  rw [cyclotomicCoverToTensor_mk]
  change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν _)) = _
  rw [affineCover_mk]
  rfl

end Categorification.Stendhal
