/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationBasis
import Categorification.Algebra.CornerTensorFactor

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners

Webster, arXiv:1309.3796v2, Lemma 6.5: if `ℓ(ww') = ℓ(w) + ℓ(w')`, multiplication
`B̃_w ⊗ B̃_{w'} → B̃_{ww'}` is an isomorphism. In the red-word model, `B̃_{w'}` is the corner
`B̃(κ₁, κ₀)` and `B̃_w` the corner `B̃(κ₂, κ₁)`. The length condition says that every pair of
red strands crossed on the way from `κ₀` to `κ₁` is still crossed in `κ₂`; we state it as a
path of adjacent red crossings from `κ₀` to `κ₁`, each crossing a pair `a, b` that both `κ₁`
and `κ₂` read in the order `b, a` (`RedCrossingPath`).

The proof is by induction along the path. The first crossing `κ₀ → κ'` is the one-crossing case
(`tensorMult_bijective`), both for `B̃(κ₁, κ') ⊗ B̃(κ', κ₀)` and `B̃(κ₂, κ') ⊗ B̃(κ', κ₀)`; the
induction hypothesis handles `B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ')`, and the refinement lemma for corner
tensor products (`CornerTensor.mult_injective_of_factor`) combines the three.

## Main results

* `BraidedStendhalAlgebra.tensorMult_bijective_of_path` : Lemma 6.5.
* `BraidedStendhalAlgebra.tensorMultEquivOfPath` : the same as a linear isomorphism.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

namespace BraidedStendhalAlgebra

/-- A path of adjacent red crossings from `κ₀` to `κ₁`, each exchanging a pair `a, b` of
neighbouring red strands that `κ₁` and `κ₂` both read in the order `b, a`. This is the length
condition `ℓ(ww') = ℓ(w) + ℓ(w')` of Webster's Lemma 6.5 for `κ₁ = w' κ₀`, `κ₂ = w κ₁`. -/
inductive RedCrossingPath (κ₂ κ₁ : List (Fin ℓ)) : List (Fin ℓ) → Prop
  | refl : RedCrossingPath κ₂ κ₁ κ₁
  | cross {κ' κ₀ L M : List (Fin ℓ)} {a b : Fin ℓ} (h0 : κ₀ = L ++ a :: b :: M)
      (h' : κ' = L ++ b :: a :: M) (h1 : [b, a].Sublist κ₁) (h2 : [b, a].Sublist κ₂)
      (p : RedCrossingPath κ₂ κ₁ κ') : RedCrossingPath κ₂ κ₁ κ₀

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)}

theorem tensorMult_injective_iff :
    Function.Injective (tensorMult k Q Λ ν κ₂ κ₁ κ₀) ↔
      Function.Injective (CornerTensor.mult (k := k) (isIdempotentElem_redProj (k := k) (Q := Q)
        (Λ := Λ) (ν := ν) κ₂) (isIdempotentElem_redProj κ₁) (isIdempotentElem_redProj κ₀)) :=
  ⟨fun h _ _ e => h (Subtype.ext e), fun h _ _ e => h (congrArg Subtype.val e)⟩

theorem tensorMult_surjective_iff :
    Function.Surjective (tensorMult k Q Λ ν κ₂ κ₁ κ₀) ↔
      ∀ y, ∃ t, CornerTensor.mult (k := k) (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ)
        (ν := ν) κ₂) (isIdempotentElem_redProj κ₁) (isIdempotentElem_redProj κ₀) t =
          redProj k Q Λ ν κ₂ * y * redProj k Q Λ ν κ₀ := by
  refine ⟨fun h y => ?_, fun h => ?_⟩
  · obtain ⟨t, ht⟩ := h ⟨redProj k Q Λ ν κ₂ * y * redProj k Q Λ ν κ₀, y, by
      simp [redProj, mul_assoc]⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  · rintro ⟨_, y, rfl⟩
    obtain ⟨t, ht⟩ := h y
    refine ⟨t, Subtype.ext ?_⟩
    change CornerTensor.mult _ _ _ t = _
    rw [ht]
    simp [redProj, mul_assoc]

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)

include hρ hQ in
/-- **Webster, Lemma 6.5** (arXiv:1309.3796v2): multiplication
`B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) → B̃(κ₂, κ₀)` over the middle corner is bijective when `κ₁` is
reached from `κ₀` by red crossings that are still present in `κ₂`. -/
theorem tensorMult_bijective_of_path (p : RedCrossingPath κ₂ κ₁ κ₀) :
    Function.Bijective (tensorMult k Q Λ ν κ₂ κ₁ κ₀) := by
  induction p with
  | refl =>
    refine ⟨tensorMult_injective_iff.2 (CornerTensor.mult_injective_self _ _),
      tensorMult_surjective_iff.2 fun y => ⟨_, CornerTensor.mult_tmul_self _ _ y⟩⟩
  | @cross κ' κ₀ L M a b h0 h' h1 h2 p ih =>
    have b10 := tensorMult_bijective (Λ := Λ) hρ hQ h0 h' h1
    have b20 := tensorMult_bijective (Λ := Λ) hρ hQ h0 h' h2
    set e := LinearEquiv.ofBijective _ ih
    let proj : BraidedStendhalAlgebra k Q Λ ν →ₗ[k] cornerSpace k Q Λ ν κ₂ κ' :=
      LinearMap.codRestrict _ (LinearMap.mulLeft k (redProj k Q Λ ν κ₂) ∘ₗ
        LinearMap.mulRight k (redProj k Q Λ ν κ')) fun y => ⟨y, rfl⟩
    let s := e.symm.toLinearMap ∘ₗ proj
    have hs : ∀ x, CornerTensor.mult (k := k) (isIdempotentElem_redProj κ₂)
        (isIdempotentElem_redProj κ₁) (isIdempotentElem_redProj κ') (s x) =
          redProj k Q Λ ν κ₂ * x * redProj k Q Λ ν κ' := fun x => by
      have := congrArg Subtype.val (e.apply_symm_apply (proj x))
      rw [mul_assoc]
      exact this
    have hinj := tensorMult_injective_iff.1 ih.1
    refine ⟨tensorMult_injective_iff.2 (CornerTensor.mult_injective_of_factor _ _ _ _ s hs hinj
      (tensorMult_surjective_iff.1 b10.2) (tensorMult_injective_iff.1 b20.1)),
      tensorMult_surjective_iff.2 (CornerTensor.exists_mult_eq_of_factor _ _ _ _ s hs hinj
        (tensorMult_surjective_iff.1 b20.2))⟩

/-- **Webster, Lemma 6.5**, as a linear isomorphism `B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) ≃ B̃(κ₂, κ₀)`. -/
noncomputable def tensorMultEquivOfPath (p : RedCrossingPath κ₂ κ₁ κ₀) :
    CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂) (redProj k Q Λ ν κ₁)
      (redProj k Q Λ ν κ₀) ≃ₗ[k] cornerSpace k Q Λ ν κ₂ κ₀ :=
  LinearEquiv.ofBijective _ (tensorMult_bijective_of_path hρ hQ p)

end BraidedStendhalAlgebra

end Categorification.Stendhal
