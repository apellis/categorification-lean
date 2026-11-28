/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdAssoc
import Categorification.WeightedKLR.Rigidity.SMoveFactorCutTransfer
import Categorification.WeightedKLR.RedStrands.Prop55DimensionFinite

/-!
# Finite-dimensionality of the factor modules of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), with the finiteness of standardization from the proof of
Proposition 5.5. The Tor lemmas for standard layers (`torAcyclic_reflect_stdLayer_of_ne`) take
finite-dimensional factor modules. The two S-move modules enter them as standard layers of
factor modules of the last red strand:

* on the left, `SMove.leftStd (𝕊^{λ_2; λ_3}(M)) ≅ S(𝕊^{λ_1; λ_2}(P_∅ ⊠ M))`
  (`SMove.leftStdCutLayerIso`), with factor module `𝕊^{λ_1; λ_2}(P_∅ ⊠ M)`
  (`SMove.leftStdMidModule`);
* on the right, `SMove.rightStd W ≅ S(W ⊠ P_∅)` (`SMove.rightStdLayerIso`).

Both factor modules are finite-dimensional when `M` and `W` are, for Rouquier parameters
(`IsRouquierQ`): `𝕊^{λ_1; λ_2}(−)` at the last cut of the first two red strands is the
standardization of the last red strand there (`parabolicCutStandardEquiv`), which preserves
finite-dimensionality (`finiteDimensional_parabolicStandard_of_finiteDimensional`), and
`P_∅ = T^{λ}(0)` is the ground field.

The `k`-structure of a factor module built from an object of `ModuleCat` is restriction along
the algebra map (`moduleCatScalars`); it agrees with the `k`-structure of the underlying type
up to `algebraMap_smul`, and the identity transfers finite-dimensionality.

## Main results

* `finiteDimensional_cutOfFactorModule`: the cut restriction `cutOfFactorModule M` of a
  finite-dimensional factor module is finite-dimensional.
* `SMove.finiteDimensional_leftStdMidL`: `𝕊^{λ_1; λ_2}(P_∅ ⊠ M)` is finite-dimensional.
* `SMove.finiteDimensional_leftStdMidFactor`: the same for the factor module of
  `SMove.leftStdCutLayerIso`.
* `SMove.finiteDimensional_emptyRightFactor`: the factor module `W ⊠ P_∅` of
  `SMove.rightStdLayerIso` is finite-dimensional.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

section Cut

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- **The cut restriction of a finite-dimensional factor module is finite-dimensional**
(`cutOfFactorModule`, with the `k`-structure by restriction along the algebra map). -/
theorem finiteDimensional_cutOfFactorModule {θ β : Multiset I} (M : FactorModule Q Λ θ β)
    [FiniteDimensional k M.carrier] : FiniteDimensional k (cutOfFactorModule Q Λ M) := by
  let e : M.carrier ≃ₗ[k] cutOfFactorModule Q Λ M :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change c • x = (parabolicCutFactorEquiv Q Λ θ β).symm
          (algebraMap k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) c) • x
        rw [AlgEquiv.commutes, algebraMap_smul] }
  exact LinearEquiv.finiteDimensional e

end Cut

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)

section Left

variable (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β₁ β₂ : Multiset I)
  (M : ModuleCat.{0} (cutFactorAlgebra (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ β₂))

/-- `P_∅ ⊠ M` is finite-dimensional when `M` is. -/
instance finiteDimensional_emptyBlocksInput [FiniteDimensional k M] :
    FiniteDimensional k (EmptyBlocksInput Q Λ β₁ β₂ M) :=
  haveI : FiniteDimensional k (blocksHeadAlgebra (a := 1) (m := 1) (r := 1) Q Λ 0) :=
    LinearEquiv.finiteDimensional (emptyAug Q Λ).symm.toLinearEquiv
  inferInstanceAs (FiniteDimensional k
    (blocksHeadAlgebra (a := 1) (m := 1) (r := 1) Q Λ 0 ⊗[k] M))

include hR in
/-- **`𝕊^{λ_1; λ_2}(P_∅ ⊠ M)` is finite-dimensional** when `M` is, for Rouquier parameters
(Webster, arXiv:1309.3796v3, proof of Proposition 5.5, applied in §7.3, proof of
Proposition 7.22), with its own `k`-structure. -/
theorem finiteDimensional_leftStdMidL [FiniteDimensional k M] :
    FiniteDimensional k (LeftStdMidL Q hQ Λ β₁ β₂ M) := by
  let N := BlocksInnerL Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) 0 β₁ β₂
    (BlocksAssocInput (a := 1) (m := 1) (r := 1) Q Λ 0 β₁ β₂ (EmptyBlocksInput Q Λ β₁ β₂ M))
  have : FiniteDimensional k
      (ParabolicOfCut Q (blocksLeftLabels (a := 1) (m := 1) (r := 1)
        (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) 0 β₁ N) :=
    inferInstanceAs (FiniteDimensional k (EmptyBlocksInput Q Λ β₁ β₂ M))
  have := finiteDimensional_parabolicStandard_of_finiteDimensional hR
    (Λ := blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) hQ 0 β₁
    (ParabolicOfCut Q (blocksLeftLabels (a := 1) (m := 1) (r := 1)
      (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) 0 β₁ N)
  exact LinearEquiv.finiteDimensional (parabolicCutStandardEquiv Q
    (blocksLeftLabels (a := 1) (m := 1) (r := 1) (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))) 0 β₁ N)

include hR in
/-- **The factor module of `SMove.leftStdCutLayerIso` is finite-dimensional** when `M` is, for
Rouquier parameters: the hypothesis on the left module of `torAcyclic_reflect_stdLayer_of_ne`
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22). -/
theorem finiteDimensional_leftStdMidFactor [FiniteDimensional k M] :
    FiniteDimensional k (parabolicOfCutModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
      (leftStdMidModule Q hQ Λ β₁ β₂ M)).carrier := by
  have := finiteDimensional_leftStdMidL Q hQ hR Λ β₁ β₂ M
  let e : LeftStdMidL Q hQ Λ β₁ β₂ M ≃ₗ[k] (parabolicOfCutModule Q
      (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (leftStdMidModule Q hQ Λ β₁ β₂ M)).carrier :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => (algebraMap_smul (cutFactorAlgebra (a := 1 + 1) (r := 1) Q
        (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (0 + β₁) β₂) c x).symm }
  exact LinearEquiv.finiteDimensional e

end Left

section Right

variable (Λ₃ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)
  (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ₃ ∘ Fin.castAdd 1) β))

/-- **The factor module `W ⊠ P_∅` of `SMove.rightStdLayerIso` is finite-dimensional** when `W`
is (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): `P_∅ = T^{λ_3}(0)` is the
ground field. -/
theorem finiteDimensional_emptyRightFactor [FiniteDimensional k W] :
    FiniteDimensional k (parabolicOfCutModule Q Λ₃ ((emptyRightTensor Q Λ₃ β).obj W)).carrier := by
  have : FiniteDimensional k (TensorProductAlgebra k Q (Λ₃ ∘ Fin.natAdd 2) 0) :=
    LinearEquiv.finiteDimensional
      (tensorProductAlgebraZeroEquiv Q (Λ₃ ∘ Fin.natAdd 2)).symm.toLinearEquiv
  have : FiniteDimensional k
      (ExtTensor k W (TensorProductAlgebra k Q (Λ₃ ∘ Fin.natAdd 2) 0)) :=
    inferInstanceAs (FiniteDimensional k
      (W ⊗[k] TensorProductAlgebra k Q (Λ₃ ∘ Fin.natAdd 2) 0))
  let X := ExtTensor k W (TensorProductAlgebra k Q (Λ₃ ∘ Fin.natAdd 2) 0)
  let e : X ≃ₗ[k] (parabolicOfCutModule Q Λ₃ ((emptyRightTensor Q Λ₃ β).obj W)).carrier :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => (algebraMap_smul (cutFactorAlgebra Q Λ₃ β 0) c x).symm }
  exact LinearEquiv.finiteDimensional e

end Right

end SMove

end Categorification.Stendhal
