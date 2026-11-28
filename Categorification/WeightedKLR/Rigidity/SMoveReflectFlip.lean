/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTensorReflection
import Categorification.WeightedKLR.RedStrands.RightStandardReflection
import Categorification.WeightedKLR.RedStrands.BraidedIdentityGrading

/-!
# The corner flip at the trivial braid is the horizontal reflection

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. Two anti-automorphisms of `T = T^λ` are in use: the reflection
`tensorFlip` (through `tensorFlipRingEquiv`), which defines the duals `M^⋆` of the last term of
the resolution of Proposition 7.8, and the corner flip transported to `T`
(`cornerFlipTensorEquiv`), which defines the reflection of left modules used in the Tor
lemmas. At the trivial braid they agree (`cornerFlipTensorEquiv_one_apply`).

The identification `violCornerEquiv` of the identity corner with `T` intertwines the two flips
(`violCornerEquiv_violFlip`): every element of the corner is the sandwich of a KLR diagram,
and both flips reflect the diagram.

## Main results

* `violCornerEquiv_violFlip`: `violCornerEquiv` intertwines the corner flip with `tensorFlip`.
* `cornerFlipTensorEquiv_one_apply`: `cornerFlipTensorEquiv 1 x = tensorFlip x.unop`.
* `cornerFlipTensorEquiv_one_eq`: `cornerFlipTensorEquiv 1 = tensorFlipRingEquiv.symm`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite CornerEndomorphism

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

include hρ hQ in
/-- **The identity-corner identification intertwines the flips** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22): if `d₂` is the corner flip of `d`, then
`violCornerEquiv d₂ = tensorFlip (violCornerEquiv d)`. -/
theorem violCornerEquiv_violFlip (d d₂ : (isIdempotentElem_violRedProj k Q Λ ν).Corner)
    (h : d₂.1 = violFlip d.1) :
    violCornerEquiv hρ hQ d₂ = tensorFlip (violCornerEquiv hρ hQ d) := by
  obtain ⟨a, ha⟩ := stendhalTensorProjection_surjective (Q := Q) (Λ := Λ) (ν := ν)
    (violCornerEquiv hρ hQ d)
  have hd : affineDiagramInIdentityCorner (Q := Q) (Λ := Λ) (ν := ν) a = d :=
    (violCornerEquiv hρ hQ).injective ((violCornerEquiv_diagonal hρ hQ a).trans ha)
  have hd₂ : affineDiagramInIdentityCorner (Q := Q) (Λ := Λ) (ν := ν) (KLRAlgebra.hflip a) =
      d₂ := by
    apply Subtype.ext
    rw [h, ← hd]
    change violMk k Q Λ ν (redProj k Q Λ ν (List.finRange ℓ) *
        ofKLR k Q Λ ν (KLRAlgebra.hflip a) * redProj k Q Λ ν (List.finRange ℓ)) =
      violFlip (violMk k Q Λ ν (redProj k Q Λ ν (List.finRange ℓ) * ofKLR k Q Λ ν a *
        redProj k Q Λ ν (List.finRange ℓ)))
    rw [violFlip_violMk, flip_mul, flip_mul, flip_redProj, flip_ofKLR, mul_assoc]
  rw [← hd₂, violCornerEquiv_diagonal, ← tensorFlip_projection, ha]

include hρ hQ in
/-- **The corner flip at the trivial braid is the reflection** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22): `cornerFlipTensorEquiv 1 x = tensorFlip x.unop`. So the
reflection of left modules in the Tor lemmas (`tensorReflectFunctor` at `σ = 1`) is
restriction of scalars along the anti-automorphism `tensorFlipRingEquiv` of the star duals. -/
theorem cornerFlipTensorEquiv_one_apply
    (x : (TensorProductAlgebra k Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) ν)ᵐᵒᵖ) :
    cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1 x = tensorFlip x.unop := by
  let φ := reflectedLeftCoefficientEquiv (Λ := Λ) hρ hQ 1
  let F := cornerFlipEquiv (Q := Q) (Λ := Λ) ν (List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ))
  let c := φ.symm x.unop
  have hx : x.unop = φ c := (φ.apply_symm_apply x.unop).symm
  -- `cornerFlipTensorEquiv (op (φ c)) = φ (cornerFlip c) = leftCoefficientEquiv (op c)`.
  have h₁ : cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1 x =
      leftCoefficientEquiv (Λ := Λ) hρ hQ 1 (op c) := by
    change φ (F (op c)) = _
    change leftCoefficientEquiv (Λ := Λ) hρ hQ 1 (F.symm (F (op c))) = _
    rw [RingEquiv.symm_apply_apply]
  -- `φ c = leftCoefficientEquiv (op (cornerFlip c))`.
  have h₂ : φ c = leftCoefficientEquiv (Λ := Λ) hρ hQ 1 (op (cornerFlip c)) := rfl
  have hl : List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ) = List.finRange ℓ := by simp
  have hm : ∀ v : ViolQuotient k Q Λ ν, v ∈ Subsemigroup.corner (violMk k Q Λ ν
      (redProj k Q Λ ν (List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ)))) →
      v ∈ Subsemigroup.corner (violMk k Q Λ ν (redProj k Q Λ ν (List.finRange ℓ))) := by
    rw [hl]
    exact fun v hv => hv
  let d : (isIdempotentElem_violRedProj k Q Λ ν).Corner := ⟨c.1, hm _ c.2⟩
  let d₂ : (isIdempotentElem_violRedProj k Q Λ ν).Corner :=
    ⟨violFlip c.1, hm _ (cornerFlip c).2⟩
  have e₁ := leftCoefficientEquiv_one_op (Λ := Λ) hρ hQ (c := c) (d := d) rfl
  have e₂ := leftCoefficientEquiv_one_op (Λ := Λ) hρ hQ (c := cornerFlip c) (d := d₂) rfl
  rw [h₁, hx, h₂, e₁, e₂, violCornerEquiv_violFlip hρ hQ d d₂ rfl, tensorFlip_tensorFlip]
  rfl

include hρ hQ in
/-- **The two flips agree** at the trivial braid, as ring isomorphisms `Tᵐᵒᵖ ≃ T`. -/
theorem cornerFlipTensorEquiv_one_eq :
    cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1 =
      (tensorFlipRingEquiv (Q := Q) (Λ := Λ ∘ ⇑(1 : Perm (Fin ℓ))) ν).symm :=
  RingEquiv.ext fun x => cornerFlipTensorEquiv_one_apply hρ hQ x

end Categorification.Stendhal.BraidedStendhalAlgebra
