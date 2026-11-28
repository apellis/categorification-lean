/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdTensorLayer
import Categorification.WeightedKLR.Rigidity.SMoveTensorLayerSeparation

/-!
# S-move pairs separated at the middle red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the off-diagonal `E²` terms with equal black counts at the last red strand.
The left module `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M))`, with `M` over
`T^{λ_2}(β_1) ⊗ T^{λ_3}(0)`, is `S(Z ⊠ R e(∅))` with `Z` a standardization over the split
`0 + β_1` at the second red strand (`SMove.leftStdTensorLayerIso`). The right module
`𝕊^{λ_1, λ_2; λ_3}(W ⊠ P_∅)` is `S(W ⊠ R e(∅))` (`SMove.rightStdTensorLayerIso`). When `W` is
a standardization over a split `θ' + β'` at the second red strand with `θ' ≠ 0`, the two are
separated by the black count at the first red strand, and
`torAcyclic_reflect_tensorLayer_stdLayer_of_ne` (at `m = 1`) gives the vanishing of Tor.

The three red labels are indexed by `Fin (1 + 1 + 1)` (the form `Λ ∘ Fin.cast _` produced by the
associativity of the cuts), which is definitionally the `Fin (2 + 1)` of `SMove.rightStd`.

## Main results

* `SMove.torAcyclic_reflect_leftStd_rightStd_of_ne`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped TensorProduct DG.DegreeZero

universe w

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β₁ : Multiset I)

/-- `P_∅ ⊠ M` is finite-dimensional when `M` is. -/
instance finiteDimensional_leftStdInnerFactor
    (M : ModuleCat.{0} (cutFactorAlgebra (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ 0))
    [FiniteDimensional k M] : FiniteDimensional k (leftStdInnerFactor Q Λ β₁ M).carrier :=
  haveI : FiniteDimensional k (blocksHeadAlgebra (a := 1) (m := 1) (r := 1) Q Λ 0) :=
    LinearEquiv.finiteDimensional (emptyAug Q Λ).symm.toLinearEquiv
  inferInstanceAs (FiniteDimensional k
    (blocksHeadAlgebra (a := 1) (m := 1) (r := 1) Q Λ 0 ⊗[k] M))

local notation "Λ₂" => Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) (β₁ + 0)))) → List ℕ}
  (hρ₂ : TypeA.IsReducedChoice ρ₂)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := β₁ + 0)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0}
    (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (β₁ + 0))]
  [HasDerivedCategory.{w, 0} ℤ]

include hρ₂ in
/-- **Off-diagonal Tor vanishing for S-move pairs separated at the middle red strand**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22). Let `M` be a
finite-dimensional module over `T^{λ_2}(β_1) ⊗ T^{λ_3}(0)` and `M'` a finite-dimensional factor
module over `T^{λ_1}(θ') ⊗ R^{λ_2}(β')` with `θ' + β' = β_1` and `θ' ≠ 0`. For Rouquier
parameters, the reflection of `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ 𝕊^{λ_2; λ_3}(M))` has no Tor against
`𝕊^{λ_1, λ_2; λ_3}(S_{λ_1 λ_2}(M') ⊠ P_∅)`. Hypotheses: `DC` (ordered covers of the left
standards, as in `isZero_derivedTensorHomology_tensor_of_standardFiltrations`) and the
standard filtrations of the first red strand (`hold`). -/
theorem torAcyclic_reflect_leftStd_rightStd_of_ne {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q)
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (1 + 1 + 1) (β₁ + 0)) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q (Λ₂) (β₁ + 0)) (leftStandard Q (Λ₂) s.1 s.2))
      (fun s => seqIdem Q (Λ₂) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (((Λ₂) ∘ Fin.castSucc) ∘ Fin.castSucc))
    (M : ModuleCat.{0} (cutFactorAlgebra (a := 1) (r := 1) Q (Λ ∘ Fin.natAdd 1) β₁ 0))
    [FiniteDimensional k M]
    {θ' β' : Multiset I} (h' : θ' + β' = β₁ + 0) (hne : θ' ≠ 0)
    (M' : FactorModule Q ((Λ₂) ∘ Fin.castSucc) θ' β') [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q (Λ₂) hQ hρ₂).obj
        ((leftStd Q hQ Λ (β₁ + 0)).obj (innerStd Q hQ Λ β₁ 0 M)))
      ((rightStd Q hQ (Λ₂) (β₁ + 0)).obj
        (stdLayerModule Q ((Λ₂) ∘ Fin.castSucc) hQ ⟨θ', β', h', M'⟩)) := by
  have h := torAcyclic_reflect_tensorLayer_stdLayer_of_ne (m := 1) Q hQ (Λ₂) hρ₂ hR DC hold
    (leftStdSplit β₁ 0) (add_zero (β₁ + 0)) default default (rfl : 0 + β₁ = 0 + β₁) h' (Ne.symm hne)
    (leftStdInnerFactor Q Λ β₁ M) M'
  refine TorAcyclic.of_iso _ (rightStdTensorLayerIso Q hQ (Λ₂) (β₁ + 0) _ default).symm ?_
  exact TorAcyclic.of_coefficient_iso _
    ((reflectOne Q (Λ₂) hQ hρ₂).mapIso (leftStdTensorLayerIso Q hQ Λ β₁ M default).symm) h

end Categorification.Stendhal.SMove
