/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiFiltration
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

/-!
# The `Fᵢ` filtration of standardizations of finite-dimensional modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5, `F`-part, for finite-dimensional modules, which is Webster's setting: the
categories `𝒜^{λ₁;…;λ_m}` of the proposition consist of finite-dimensional modules. For
Rouquier parameters the input module `X_M` of the last-strand sequence is finite-dimensional
when `M` is (`finiteDimensional_twoPieceInput`), so the filtration needs injectivity of `δ₁`
only for finite-dimensional modules (`fiFiltration_finite`, route hypothesis
`AllFiniteDeltaInjective`). At the standard Khovanov–Lauda parameters that hypothesis is
Webster's dimension count (`allFiniteDeltaInjective_std`), and the filtration holds with no
route hypothesis (`fiFiltration_finite_std`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong ModuleFiltration KL3.Diagram
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k}

/-- **`X_M = M|_{B'} ⊗_{B'} S^L_{α'}` is finite-dimensional when `M` is**, for Rouquier
parameters. -/
theorem finiteDimensional_twoPieceInput (hR : IsRouquierQ C Q) {ℓ : ℕ}
    (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I)
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [FiniteDimensional k M]
    (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b))) :
    FiniteDimensional k (TwoPieceInput Q Λ b M hα₁) := by
  have := tensorProductAlgebra_finite (Q := Q) (Λ ∘ Fin.castSucc) (initWeight b) hR
  have : Module.Finite k (LeftRootStandard (ν := initWeight b) Q (Λ ∘ Fin.castSucc)
      (blockRoot (initBlocks b))) := by
    unfold LeftRootStandard
    exact Module.Finite.pi
  have : Module.Finite k (BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα₁) := this
  have : Module.Finite k (InitRestrict Q Λ b M) := inferInstanceAs (Module.Finite k M)
  exact Module.Finite.quotient k _

variable (Q) (i : I)

/-- **Webster's Proposition 5.5, `F`-part, for finite-dimensional modules**
(arXiv:1309.3796v3), with a commuting action: for Rouquier parameters and every
finite-dimensional `M`, `Fᵢ(M ⊗_B S^L_α)` is filtered by the `ₖFᵢ M ⊗_{B'} S^L_{α'}`, each red
strand once. Route hypothesis: `AllFiniteDeltaInjective` (injectivity of the first map of the
last-strand sequence for finite-dimensional modules, which Webster obtains by a dimension count),
tracked for removal in the roadmap; it holds at the standard Khovanov–Lauda parameters
(`fiFiltration_finite_std`). -/
theorem fiFiltration_finite (hR : IsRouquierQ C Q) (hQ : KLRSymm Q)
    (hδ : ∀ (ℓ : ℕ) (Λ : Fin (ℓ + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ) :
    ∀ ℓ, FiFiltrationFor (k := k) Q i (fun M _ _ => FiniteDimensional k M) ℓ
  | 0 => fiFiltrationFor_zero Q i _
  | ℓ + 1 => by
    intro Λ b ν h00 hb hα b' h0 hr hκ hb' hα' C' _ _ M _ _ _ _ hM ρ
    obtain rfl : ν = initWeight b + lastBlock b := hb.symm.trans (blockPrefix_last b)
    have : FiniteDimensional k (TwoPieceInput Q Λ b M (rootNonViolated_initBlocks h00)) :=
      finiteDimensional_twoPieceInput hR Λ b M _
    exact fiFiltrationFor_step Q i hQ (fun M _ _ => FiniteDimensional k M)
      (fiFiltration_finite hR hQ hδ ℓ) Λ b h00 hb hα b' h0 hr hκ hb' hα' C' M
      (inferInstanceAs (FiniteDimensional k M))
      (hδ ℓ Λ i _ _ ⟨TwoPieceInput Q Λ b M (rootNonViolated_initBlocks h00)⟩ this) ρ

end StendhalAlgebra

section Standard

open scoped Classical

namespace StendhalAlgebra

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I} (i : I)

/-- **Webster's Proposition 5.5, `F`-part, at the standard Khovanov–Lauda parameters**
(arXiv:1309.3796v3), for finite-dimensional modules and with a commuting action, with no
route hypothesis: `fiFiltration_finite` with Webster's dimension count
(`allFiniteDeltaInjective_std`). -/
theorem fiFiltration_finite_std
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) (ℓ : ℕ) :
    FiFiltrationFor (k := k) (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) i
      (fun M _ _ => FiniteDimensional k M) ℓ :=
  fiFiltration_finite _ i hR hQs (fun _ _ => allFiniteDeltaInjective_std hR hQs) ℓ

end StendhalAlgebra

end Standard

end Categorification.Stendhal
