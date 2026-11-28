/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZero

/-!
# The diagonal `Tor₀` of the S-move: the count against a sum of copies

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. On the left module side the
diagonal term is the summand `S(T e(t) ⊠ Y₀)` of the standardization `S(T e(t) ⊠ R e(u))` of the
projective `R e(u) ≅ Y₀^{⊕ J}` (`tensorStdBiconeIsBilimit`), and the standard module `S_s` of the
loading `s = (red₁ red₂ u red₃)` is the three-strand form of the latter
(`SMove.nonempty_diagonal_standard_equiv`). Since `Tor₀` against a reflection is additive in the
module (`finrank_tensorProductOver_reflectOne`: `dim (W^r ⊗_T Y) = dim Hom(Y, W^⋆)`),

  `dim (W^r ⊗_T Y') = |J| · dim (W^r ⊗_T Y)`  for `Y' ≅ Y^{⊕ J}`

(`finrank_tensorProductOver_reflectOne_bicone`). With `Tor₀(W^r, S_s) ≅ Fix(e(s), W)`
(`leftStandardTensorEquivFixed`, for `W` killed by the loading idempotents strictly above `s`),
the diagonal `Tor₀` of the S-move is `dim Fix(e(s), W) / |J|`, not `dim Fix(e(s), W)`: it is
one-dimensional exactly when `dim e(s) W = |J|`, the expanded-word form of Webster's
normalization that the divided-power
idempotent `e(𝐢_λ)` has one-dimensional image. This is the same normalization as the hypothesis
`htop` of the second clause of Proposition 7.8 (`exists_stdResolution_last`), where
`dim Ext^{|ν|}(S(T e(t) ⊠ R e(u)), X) = |J|` is equivalent to the one-dimensionality for `Y₀`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite BraidedStendhalAlgebra DG

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

local notation "T" => TensorProductAlgebra k Q Λ ν

/-- **`Tor₀` against a reflection counts copies** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, `Tor₀` on the diagonal): if `Y'` is the sum of `|J|` copies of `Y` (a bilimit
bicone on the constant family `Y`), then `dim (W^r ⊗_T Y') = |J| · dim (W^r ⊗_T Y)`, `W^r` the
reflection of `W`. -/
theorem finrank_tensorProductOver_reflectOne_bicone (W Y : ModuleCat.{0} T) {J : Type}
    [Fintype J] [DecidableEq J] {b : Bicone (fun _ : J => Y)} (hb : b.IsBilimit) :
    Module.finrank k (TensorProductOver T ((reflectOne Q Λ hQ hρ).obj W) b.pt) =
      Fintype.card J *
        Module.finrank k (TensorProductOver T ((reflectOne Q Λ hQ hρ).obj W) Y) := by
  rw [finrank_tensorProductOver_reflectOne, finrank_tensorProductOver_reflectOne,
    (Bicone.homLinearEquiv (R := k) hb _).finrank_eq, finrank_fun_eq_card_mul]

end Categorification.Stendhal
