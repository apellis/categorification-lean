/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndBasis
import Categorification.WeightedKLR.Rigidity.CupCapCoevaluation

/-!
# The basis `B″` of `K̃^{λ⁺}_λ` at Webster's coefficient module `L_μ`

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.17, in the case `j = ℓ`, for the module Webster uses:
the simple head `L_μ` of the coevaluation projective (Lemma 7.3, `Stendhal.coevaluationHead`),
over a field. A right module over `T̃^{(μ,μ*)}` is a `k`-module through the scalars of
`T̃^{(μ,μ*)}` (`CupCap.ScalarModule`); the pieces `L_μ e(j)` are vector spaces, and with any
choice of their bases `capBasis` gives a basis of `K̃^{λ⁺}_λ`. The support hypothesis of
`capBasis` holds for `L_μ` (`CupCap.coevaluationHead_smul_cutIdem`); what remains are the
(max1) scalars being units and the mirror of Lemma 7.16 (`PullOffLeft`) for `L_μ`.

## Main definitions

* `CupCap.ScalarModule`: the `k`-module structure of a right `T̃^{(μ,μ*)}`-module.
* `CupCap.capBasis_coevaluationHead`: Lemma 7.17 at `L = L_μ`, `j = ℓ`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section ScalarModule

variable {I : Type} [DecidableEq I] (k : Type*) [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (L : Type*) [AddCommGroup L]
  [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- A right `T̃^{(μ,μ*)}`-module, with the `k`-module structure through the scalars of
`T̃^{(μ,μ*)}`. -/
@[nolint unusedArguments]
def ScalarModule (k : Type*) [CommRing k] (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λc : Fin 2 → I →₀ ℕ) (_ν₀ : Multiset I) (L : Type*) : Type _ := L

instance : AddCommGroup (ScalarModule k Q Λc ν₀ L) := ‹AddCommGroup L›

instance : Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ (ScalarModule k Q Λc ν₀ L) :=
  ‹Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L›

instance : Module k (ScalarModule k Q Λc ν₀ L) :=
  Module.compHom L (algebraMap k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ)

instance : IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ (ScalarModule k Q Λc ν₀ L) where
  smul_assoc c a v := by
    rw [show c • a = algebraMap k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ c * a from
      Algebra.smul_def c a, mul_smul]
    rfl

end ScalarModule

section Coevaluation

open CycKLR KLRAlgebra QuantumGroup QuantumGroup.UDot TypeA Equiv

variable {I : Type} [Fintype I] [DecidableEq I] {k : Type*} [Field k] {C : CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : I → ℕ)
  {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
  (d : List (I × ℕ)) {ℓ : ℕ} (Λ' : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

/-- Webster's `L_μ` as a right `T̃^{(μ,μ*)}`-module and a `k`-module. -/
abbrev CoevaluationCoefficient : Type _ :=
  ScalarModule k Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
    (ViaQuotient k Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
      (coevaluationHead Q Λ RD highest d))

/-- **Lemma 7.17 at Webster's `L_μ`** (arXiv:1309.3796v3, §7.3, for the cap at the right end,
`j = ℓ`, over a field, for symmetric `Q`): with fixed reduced words and bases of the pieces
`L_μ e(j)`, the triples `((b, j, u), b′)` index a basis `B″` of `K̃^{λ⁺}_λ` with coefficient module
`L_μ`. The support of `L_μ` on the loadings `μ ⋯ μ*` is proved
(`coevaluationHead_smul_cutIdem`). Route hypotheses (tracked): `hκ`, the (max1) scalars are
units (they are `±∏ t_{i'i}`, units for Webster's parameters), and `hP`, the mirror of
Lemma 7.16 for `L_μ`. -/
def capBasis_coevaluationHead
    {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 (expandDiv d : Multiset I)))) → List ℕ}
    {ρ₃ : Perm (Fin (Multiset.card
      (stendhalWeight (ℓ + 2) (ν + (expandDiv d : Multiset I))))) → List ℕ}
    [DecidableEq (EndGen (expandDiv d : Multiset I) ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 (expandDiv d : Multiset I))) (ρ₂ b) ∧
      wordProd (Multiset.card (stendhalWeight 2 (expandDiv d : Multiset I))) (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced (Multiset.card
        (stendhalWeight (ℓ + 2) (ν + (expandDiv d : Multiset I)))) (ρ₃ w) ∧
      wordProd (Multiset.card
        (stendhalWeight (ℓ + 2) (ν + (expandDiv d : Multiset I)))) (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q (expandDiv d : Multiset I) i))
    (hP : PullOffLeft k Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
      (CoevaluationCoefficient Q Λ RD highest d)) :
    Module.Basis
      (Σ g : EndGen (expandDiv d : Multiset I) ρ₁, Module.Free.ChooseBasisIndex k
        (BalancedTensor.idemPart k (CoevaluationCoefficient Q Λ RD highest d)
          (op (StendhalAlgebra.e (k := k) (Q := Q)
            (Λ := coevaluationLabels Λ RD highest (expandDiv d)) g.1.2.1 g.2.1))))
      k (CapTilde k Q Λ' (coevaluationLabels Λ RD highest (expandDiv d)) ℓ le_rfl ν
        (expandDiv d) (CoevaluationCoefficient Q Λ RD highest d)) :=
  capBasis Q Λ' (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
    (CoevaluationCoefficient Q Λ RD highest d) ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ
    (fun w v hw =>
      smul_e_eq_zero_of_not_isCapGood (coevaluationHead_smul_cutIdem Q Λ RD highest d) w v hw)
    hP (fun _ => Module.Free.chooseBasis k _)

end Coevaluation

end Categorification.Stendhal.CupCap
