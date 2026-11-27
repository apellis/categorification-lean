/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.LabelledStandardFiltration
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCountQ

/-!
# The layers of `T^λ e(s)` for Rouquier parameters

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.21 (printed form), for Rouquier parameters `Q`:
the route hypothesis `AllFiniteDeltaInjective` of `phiLayerEquiv` is discharged by the dimension
count of Proposition 5.5 (`allFiniteDeltaInjective_of_rouquier`).

## Main results

* `phiLayerEquiv_of_rouquier`, `phiLayerEquiv_std_unit`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLRAlgebra TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram ModuleFiltration

open scoped Classical

variable {I : Type} {C : CartanDatum I} {k : Type} [Field k]

/-- **Webster, arXiv:1309.3796v3, Proposition 5.21 (printed form), for Rouquier parameters**: `P_{≥φ}/P_{>φ} ≅ S_{φ • s}` for every block assignment `φ` of a
red-ordered loading `s` and every choice `ρ` of reduced words, sending `[e(φ • s)]` to
`[x_φ]`. -/
def phiLayerEquiv_of_rouquier
    {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
    (hQs : KLRSymm Q)
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ)
    (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      TypeA.wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (g : PhiIndex s) :
    leftStandard Q Λ (phiBottom s g.1)
        (g.isRedOrdered hs) ≃ₗ[TensorProductAlgebra k
          Q Λ ν]
      phiLayer Q Λ ρ hs g :=
  phiLayerEquiv _ hQs hR (fun _ _ => allFiniteDeltaInjective_of_rouquier hR hQs) Λ ρ hρ hs g

theorem phiLayerEquiv_std_unit
    {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
    (hQs : KLRSymm Q)
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ)
    (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      TypeA.wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (g : PhiIndex s) :
    phiLayerEquiv_of_rouquier hR hQs Λ ρ hρ hs g
        (leftStandardUnit Q Λ _
          (g.isRedOrdered hs)) =
      phiLayerGen Q Λ ρ hs g :=
  phiLayerEquiv_unit _ hQs hR (fun _ _ => allFiniteDeltaInjective_of_rouquier hR hQs) Λ ρ hρ hs g

end Categorification.Stendhal
