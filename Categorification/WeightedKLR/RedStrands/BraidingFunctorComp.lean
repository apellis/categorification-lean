/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient
import Categorification.Algebra.CornerTensorDerived

set_option backward.isDefEq.respectTransparency false

/-!
# Composites of the derived braiding functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 6.12,
second clause: if `w > ws_i` then `𝔅_w ≅ 𝔅_{ws_i} ⊗ᴸ 𝔅_i`. In the red-order form of the
braiding bimodules `B(κ', κ) = e_{κ'} T e_κ` of one algebra: when the inversions of the red
orders `κ₂, κ₁, κ₀` add (Lemma 6.5, `violMk_mult_injective`, `violMk_mult_surjective`) and the
higher `Tor` of `B(κ₂, κ₁) ⊗ B(κ₁, κ₀)` vanish, the derived braiding functors compose:
`𝔅(κ₂, κ₁) ⋙ 𝔅(κ₁, κ₀) ≅ 𝔅(κ₂, κ₀)` on the whole derived category
(`braidingFunctorCompIso`). Webster's proof of the vanishing of the higher `Tor` (from the
standard filtrations of the step `f_n`) is the hypothesis `hv` here.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA CategoryTheory Limits DG DG.DerivedCategory
open scoped DG.DegreeZero List

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}

local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν

/-- **Webster, Lemma 6.12, second clause** (arXiv:1309.3796v3), red-order form: when the
inversions of `κ₂, κ₁, κ₀` add and `Tor_{>0}(B(κ₂, κ₁), B(κ₁, κ₀)) = 0`, the derived braiding
functors compose, `𝔅(κ₂, κ₁) ⋙ 𝔅(κ₁, κ₀) ≅ 𝔅(κ₂, κ₀)`. -/
def braidingFunctorCompIso (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) {κ₂ κ₁ κ₀ : List (Fin ℓ)}
    (h0 : κ₀.Nodup) (hp : κ₀.Perm κ₁)
    (H : ∀ x y, [x, y] <+ κ₀ → [y, x] <+ κ₁ → [y, x] <+ κ₂)
    [HasDerivedCategory.{0} (hE κ₂).Cornerᵐᵒᵖ] [HasDerivedCategory.{0} (hE κ₁).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{0} (hE κ₀).Cornerᵐᵒᵖ]
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := (hE κ₀).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor.{0} k Q Λ ν κ₁ κ₀).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (hE κ₁).Cornerᵐᵒᵖ (cornerOpDZ (hE κ₂) (violMk k Q Λ ν
          (redProj k Q Λ ν κ₁)))))))) :
    braidingFunctor.{0} k Q Λ ν κ₂ κ₁ ⋙ braidingFunctor.{0} k Q Λ ν κ₁ κ₀ ≅
      braidingFunctor.{0} k Q Λ ν κ₂ κ₀ :=
  derivedRightTensorCornerCompIso (k := k) (hE κ₂) (hE κ₁) (hE κ₀)
    (violMk_mult_injective hρ hQ h0 hp H) (violMk_mult_surjective hρ hQ h0 hp H) hv

end Categorification.Stendhal.BraidedStendhalAlgebra
