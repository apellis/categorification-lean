/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCapBasisApply

/-!
# The one-sided Mackey decomposition at the maximum

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19. Take no red strands besides the window (`ℓ = 0`, `j = 0`) and `r` black strands.
Then the window sits at the right end of every top loading (`midPos_eq_card_of_zero`), so in
the corner `e T̃^{(μ,μ*)+r}` of the maximum every extra strand enters the window from the left.
The corner decomposition `midIdemSum_bijective` specializes to the one-sided Mackey
decomposition: `L ⊗_{T̃^{(μ,μ*)}} e T̃^{(μ,μ*)+r} ≅ ⨁_g L e(t_g)` over the generators
`g = (s, t, d, u)`, `u` a shuffle of the extra strands into the window (`leftMackeyEquiv`), with
the basis of generators `b′ γ_g` (`leftMackeyBasis`, `leftMackeyBasis_apply`).

## Main definitions

* `CupCap.leftMackeyEquiv`: the one-sided Mackey decomposition, as `k`-modules.
* `CupCap.leftMackeyBasis`: its basis from bases of the pieces `L e(t)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 0 → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))

omit [DecidableEq I] in
/-- With no red strands besides the window, the window sits at the right end of the top
loading: every extra strand enters it from the left. -/
theorem midPos_eq_card_of_zero (s : Seq (stendhalWeight 0 ν)) :
    midPos 0 s = Multiset.card (stendhalWeight 0 ν) := by
  simp [midPos]

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}

/-- **The one-sided Mackey decomposition at the maximum** (`ℓ = 0`, symmetric `Q`):
`L ⊗_{T̃^{(μ,μ*)}} e T̃^{(μ,μ*)+r} ≅ ⨁_g L e(t_g)` over the generators `g = (s, t, d, u)`, with `u`
a shuffle of the extra strands, which all enter the window from the left. -/
def leftMackeyEquiv (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    [DecidableEq (MidGen 0 le_rfl ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    MidModel 0 le_rfl Q Λ Λc ν ν₀ L ≃ₗ[k]
      Π₀ g : MidGen 0 le_rfl ν ν₀, BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g) :=
  midModelEquivₖ 0 le_rfl Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃

/-- **The basis of the one-sided Mackey decomposition**: bases `B′_t` of the pieces `L e(t)`
give the basis `b′ γ_g` of `L ⊗_{T̃^{(μ,μ*)}} e T̃^{(μ,μ*)+r}` (`ℓ = 0`, symmetric `Q`). -/
def leftMackeyBasis (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    [DecidableEq (MidGen 0 le_rfl ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2)))) :
    Module.Basis (Σ g : MidGen 0 le_rfl ν ν₀, ι ⟨g.t, g.ht⟩) k
      (MidModel 0 le_rfl Q Λ Λc ν ν₀ L) :=
  midModelBasis 0 le_rfl Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ B'

theorem leftMackeyBasis_apply (L : Type*) [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    [DecidableEq (MidGen 0 le_rfl ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2))))
    (x : Σ g : MidGen 0 le_rfl ν ν₀, ι ⟨g.t, g.ht⟩) :
    leftMackeyBasis L hQ hρ₂ hρ₃ B' x =
      Ind.tmul (midGenCorner Q Λ Λc ρ₃ x.1) (B' ⟨x.1.t, x.1.ht⟩ x.2 : L) :=
  midModelBasis_apply hQ hρ₂ hρ₃ B' x


end Categorification.Stendhal.CupCap
