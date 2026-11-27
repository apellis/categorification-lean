/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.LabelledStandardFiltration
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

/-!
# The layers of `T^λ e(s)` at the standard Khovanov–Lauda scalars

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.21 (printed form), at the standard Khovanov–Lauda parameters `Q = CL.qCL KL`:
the route hypothesis `AllFiniteDeltaInjective` of `phiLayerEquiv` is discharged by the dimension
count of Proposition 5.5 (`allFiniteDeltaInjective_std`).

## Main results

* `phiLayerEquiv_std`, `phiLayerEquiv_std_unit`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLRAlgebra TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram ModuleFiltration

open scoped Classical

variable {I : Type} {C : CartanDatum I} {k : Type} [Field k]

/-- **Webster, arXiv:1309.3796v3, Proposition 5.21 (printed form), at the standard
Khovanov–Lauda parameters**: `P_{≥φ}/P_{>φ} ≅ S_{φ • s}` for every block assignment `φ` of a
red-ordered loading `s` and every choice `ρ` of reduced words, sending `[e(φ • s)]` to
`[x_φ]`. -/
def phiLayerEquiv_std
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ)
    (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      TypeA.wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (g : PhiIndex s) :
    leftStandard (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ (phiBottom s g.1)
        (g.isRedOrdered hs) ≃ₗ[TensorProductAlgebra k
          (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν]
      phiLayer (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ρ hs g :=
  phiLayerEquiv _ hQs hR (fun _ _ => allFiniteDeltaInjective_std hR hQs) Λ ρ hρ hs g

theorem phiLayerEquiv_std_unit
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ)
    (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      TypeA.wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (g : PhiIndex s) :
    phiLayerEquiv_std hR hQs Λ ρ hρ hs g
        (leftStandardUnit (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ _
          (g.isRedOrdered hs)) =
      phiLayerGen (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ρ hs g :=
  phiLayerEquiv_unit _ hQs hR (fun _ _ => allFiniteDeltaInjective_std hR hQs) Λ ρ hρ hs g

end Categorification.Stendhal
