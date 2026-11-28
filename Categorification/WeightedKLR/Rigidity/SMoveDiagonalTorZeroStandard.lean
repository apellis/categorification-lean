/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalPairHigherTor
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZeroSummand

/-!
# The `Tor₀` of the diagonal pair against the diagonal standard

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. The module of the diagonal pair
is `Y = SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀)` with `R^{λ_2} e(𝐮) ≅ Y₀^{⊕ J}`
(`tensorStdBiconeIsBilimit`), and `SMove.rightStd S(T^{λ_1} e(t) ⊠ R^{λ_2} e(𝐮)) ≅ S_s`
(`SMove.exists_rightStd_tensorStd_cycWord_equiv`). Since `Tor₀` against a reflection is
`dim Hom(−, W^⋆)` (`finrank_tensorProductOver_reflectOne`), it is invariant under isomorphism
of the module and additive (`SMove.finrank_tensorProductOver_reflectOne_rightStd_bicone`), so

  `|J| · dim (W^r ⊗_T Y) = dim (W^r ⊗_T S_s)`

for every coefficient `W` (`SMove.card_mul_finrank_tensorProductOver_reflect_rightStd_tensorStd`).
With `W^r ⊗_T S_s ≅ W e(s)` for `W = SMove.leftStd N`
(`SMove.leftStdReflectTensorEquivFixed`), the `Tor₀` of the diagonal pair is
`dim e(s) W / |J|`. No route hypotheses.

## Main results

* `SMove.card_mul_finrank_tensorProductOver_reflect_rightStd_tensorStd`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite BraidedStendhalAlgebra DG

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)
local notation "T₃" => TensorProductAlgebra k Q Λ₃ ν

include hρ in
/-- **`Tor₀` of the diagonal pair counts against the diagonal standard** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, `Tor₀` of the diagonal pair): for a summand
decomposition `R^{λ_2} e(𝐮) ≅ Y₀^{⊕ J}` and every coefficient `W` over `T^{λ_1, λ_2, λ_3}(ν)`,
there is a loading `s` with every black strand left of the last red strand such that
`|J| · dim (W^r ⊗_T SMove.rightStd S(T^{λ_1} e(t) ⊠ Y₀)) = dim (W^r ⊗_T S_s)`. -/
theorem card_mul_finrank_tensorProductOver_reflect_rightStd_tensorStd
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt u 0)))
    {J : Type} [Fintype J] [DecidableEq J]
    (ι : J → (Y₀ →ₗ[rightCyc Q Λ (wordWt u 0)] cycWord Q (rightLabels Λ) u))
    (π : J → (cycWord Q (rightLabels Λ) u →ₗ[rightCyc Q Λ (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id) (W : ModuleCat.{0} T₃) :
    ∃ (s : Seq (stendhalWeight (1 + 1 + 1) ν)) (hs : IsRedOrdered s),
      (∀ i, blackCount s (Fin.last 2) i = ν.count i) ∧
      Fintype.card J * Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
          ((rightStd Q hQ Λ₃ ν).obj
            (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀))) =
        Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
          (ModuleCat.of T₃ (leftStandard Q Λ₃ s hs))) := by
  obtain ⟨s, hs, hlast, ⟨e⟩⟩ := exists_rightStd_tensorStd_cycWord_equiv Q hQ Λ u h₀ t ht
  refine ⟨s, hs, hlast, ?_⟩
  let X := oldProj Q (rightLabels Λ) 0 t ht
  have h₁ := finrank_tensorProductOver_reflectOne_rightStd_bicone Q hQ Λ₃ hρ W
    (tensorStd Q (rightLabels Λ) hQ h₀ X Y₀)
    (tensorStdBiconeIsBilimit Q (rightLabels Λ) hQ h₀ X ι π hιπ htot)
  have h₂ : Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
        ((rightStd Q hQ Λ₃ ν).obj (tensorStd Q (rightLabels Λ) hQ h₀ X
          (cycWord Q (rightLabels Λ) u)))) =
      Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)
        (ModuleCat.of T₃ (leftStandard Q Λ₃ s hs))) := by
    rw [finrank_tensorProductOver_reflectOne, finrank_tensorProductOver_reflectOne]
    exact (Linear.homCongr k e.toModuleIso (Iso.refl _)).finrank_eq
  exact h₁.symm.trans h₂

end Categorification.Stendhal.SMove
