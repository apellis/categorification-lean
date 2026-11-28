/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdResolutionCorner

/-!
# The `Tor₀` of the diagonal pair is a corner of the coefficient

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. The standard module
`SMove.rightStd S(T^{λ_1} e(t) ⊠ R^{λ_2} e(𝐮))` is `S_s` for the diagonal loading
`s = (red₁ red₂ 𝐮' red₃)`, of the form `t' λ_3 ∅` (`SMove.diagonalTwoPiece`)
(`SMove.nonempty_diagonal_rightStd_tensorStd_cycWord_equiv`, the explicit form of
`SMove.exists_rightStd_tensorStd_cycWord_equiv`). With the count against `Y₀^{⊕ J}` and
`dim (W^r ⊗_T S_s) = dim e(s) W` for `W = SMove.leftStd N`
(`SMove.finrank_tensorProductOver_reflectOne_leftStd_leftStandard`), this gives

  `|J| · dim (W^r ⊗_T SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀)) = dim e(s) W`

(`SMove.card_mul_finrank_tensorProductOver_diagonal`, stated for every coefficient `W`). No
route hypotheses.

## Main results

* `SMove.nonempty_diagonal_rightStd_tensorStd_cycWord_equiv`.
* `SMove.card_mul_finrank_tensorProductOver_diagonal`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite BraidedStendhalAlgebra DG

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}

local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)
local notation "T₃" => TensorProductAlgebra k Q Λ₃ ν

/-- The loading `(red₁ red₂ 𝐮')` of the first two red strands, `𝐮'` the reverse of `𝐮`, for a
loading `t` of the first red strand without black strands. -/
abbrev diagonalInnerLoading (u : List I) (h₀ : 0 + wordWt u 0 = ν)
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    {t : Seq (stendhalWeight (1 + 1) ν) // IsRedOrdered t} :=
  twoPieceLabel h₀ (KLRAlgebra.Seq.ofList u.reverse (coe_reverse_eq_wordWt u)) ⟨t, ht⟩

/-- **The diagonal standard, explicit loading** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): `SMove.rightStd S(T^{λ_1} e(t) ⊠ R^{λ_2} e(𝐮)) ≅ S_s` for a diagonal loading
`s = (red₁ red₂ 𝐮' red₃)`. -/
theorem nonempty_diagonal_rightStd_tensorStd_cycWord_equiv (u : List I) (h₀ : 0 + wordWt u 0 = ν)
    (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t) :
    Nonempty ((rightStd Q hQ Λ₃ ν).obj
          (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht)
            (cycWord Q (rightLabels Λ) u)) ≃ₗ[T₃]
        ModuleCat.of T₃ (leftStandard Q Λ₃ (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).1
          (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).2)) := by
  obtain ⟨g⟩ := nonempty_cycWord_equiv_cycProj Q (rightLabels Λ) u
  let u' := KLRAlgebra.Seq.ofList u.reverse (coe_reverse_eq_wordWt u)
  obtain ⟨g₂⟩ := nonempty_stdLayerModule_twoPiece_equiv Q (rightLabels Λ) hQ h₀ ht u'
  let f := (stdLayerEquiv Q (rightLabels Λ) hQ h₀
    (tensorFactorCongr Q (rightLabels Λ)
      (oldProjZeroStandardEquiv Q (rightLabels Λ) t ht) g)).trans g₂
  obtain ⟨g₃⟩ := nonempty_rightStd_equiv_of_equiv Q hQ Λ₃ ν _ _ default f
  exact ⟨g₃⟩

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

include hρ in
/-- **`Tor₀` of the diagonal pair against the explicit diagonal standard** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, `Tor₀` of the diagonal pair): for a
summand decomposition `R^{λ_2} e(𝐮) ≅ Y₀^{⊕ J}` and the diagonal loading
`s = (red₁ red₂ 𝐮' red₃)`,
`|J| · dim (W^r ⊗_T SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀)) = dim (W^r ⊗_T S_s)` for every
coefficient `W`. With `SMove.finrank_tensorProductOver_reflectOne_leftStd_leftStandard`, the
right side is `dim e(s) W` for `W = SMove.leftStd N`. No route hypotheses. -/
theorem card_mul_finrank_tensorProductOver_diagonal
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt u 0)))
    {J : Type} [Fintype J] [DecidableEq J]
    (ι : J → (Y₀ →ₗ[rightCyc Q Λ (wordWt u 0)] cycWord Q (rightLabels Λ) u))
    (π : J → (cycWord Q (rightLabels Λ) u →ₗ[rightCyc Q Λ (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id) :
    ∀ W : ModuleCat.{0} T₃,
      Fintype.card J * Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
          ((rightStd Q hQ Λ₃ ν).obj
            (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀))) =
        Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
          (ModuleCat.of T₃ (leftStandard Q Λ₃
            (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).1
            (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).2))) := by
  intro W
  let d := diagonalInnerLoading u h₀ t ht
  obtain ⟨e⟩ := nonempty_diagonal_rightStd_tensorStd_cycWord_equiv Q hQ Λ u h₀ t ht
  let X := oldProj Q (rightLabels Λ) 0 t ht
  have h₁ := finrank_tensorProductOver_reflectOne_rightStd_bicone Q hQ Λ₃ hρ W
    (tensorStd Q (rightLabels Λ) hQ h₀ X Y₀)
    (tensorStdBiconeIsBilimit Q (rightLabels Λ) hQ h₀ X ι π hιπ htot)
  have h₂ : Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
        ((rightStd Q hQ Λ₃ ν).obj (tensorStd Q (rightLabels Λ) hQ h₀ X
          (cycWord Q (rightLabels Λ) u)))) =
      Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
        (ModuleCat.of T₃ (leftStandard Q Λ₃ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2))) := by
    rw [finrank_tensorProductOver_reflectOne, finrank_tensorProductOver_reflectOne]
    exact (Linear.homCongr k e.toModuleIso (Iso.refl _)).finrank_eq
  exact h₁.symm.trans h₂

end Categorification.Stendhal.SMove
