/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerFree
import Categorification.WeightedKLR.Rigidity.CupCapMidGenerators
import Categorification.WeightedKLR.Rigidity.CupCapEndBasis

/-!
# A basis of the model of `K̃^{λ⁺}_λ` for a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap after the red strand `λ_j`
(any `j`). For symmetric `Q`, the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` is `⨁_g L e(t_g)` as
`k`-modules, the sum over the generators `g = (s, t, d, u)` (`MidGen`): a red-ordered loading `s`
of `λ`, a red-ordered loading `t` at the maximum, dots `x^d` on the black strands of `λ` and a
window shuffle `u` (`midModelEquivₖ`). Given bases `B′_t` of the pieces `L e(t)`, the elements
`b′ γ_g` form a basis of the model indexed by the pairs `(g, b′)` with `b′ ∈ B′_{t_g}`
(`midModelBasis`). Reduced words are fixed arbitrarily (`ρ₂`, `ρ₃`), as in the source; those of
`T̃^{λ⁺}` are adapted to the window (`midWord`).

## Main definitions

* `CupCap.midModelEquivₖ`: the model is `⨁_g L e(t_g)` as `k`-modules.
* `CupCap.midModelBasis`: the basis of the model.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

-- the `ℤ`-algebra structures used by the balanced tensor products of `InductionAlong`
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- Scalars pass from the corner to `L` in the model. -/
theorem smul_tmul_midModel (c : k) (z : Corner (midOp j hj Q Λ Λc ν ν₀)) (v : L) :
    c • (Ind.tmul z v : MidModel j hj Q Λ Λc ν ν₀ L) = Ind.tmul z (c • v) := by
  have hz : z.1 * midOp j hj Q Λ Λc ν ν₀ 1 = z.1 := z.2
  have h : algebraMap k Tpᵐᵒᵖ c • z = op (algebraMap k Tcᵐᵒᵖ c) • z := by
    apply Subtype.ext
    change algebraMap k Tpᵐᵒᵖ c * z.1 = z.1 * midOp j hj Q Λ Λc ν ν₀ (algebraMap k Tcᵐᵒᵖ c)
    have e1 : midOp j hj Q Λ Λc ν ν₀ (algebraMap k Tcᵐᵒᵖ c) = c • midOp j hj Q Λ Λc ν ν₀ 1 := by
      rw [midOp_apply, midOp_apply, Algebra.algebraMap_eq_smul_one, unop_smul, unop_one,
        map_smul, op_smul]
    rw [e1, mul_smul_comm, hz, ← Algebra.smul_def]
  rw [midModel_algebraMap_smul, Ind.smul_tmul, h, Ind.op_smul_tmul, _root_.algebraMap_smul]

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem midModelEquiv_tmul [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (z : Corner (midOp j hj Q Λ Λc ν ν₀)) (v : L) (g : MidGen j hj ν ν₀) :
    ((midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃ (Ind.tmul z v) g : L)) =
      (BalancedTensor.idemCoord (midIdemSum_bijective hQ hρ₂ hρ₃) z g : Tcᵐᵒᵖ) • v :=
  BalancedTensor.idemEquiv_tmul _ _ _ z v g

variable (j hj Q Λ Λc ν ν₀ ρ₃) in
/-- **The model of `K̃` for a cap after `λ_j` is `⨁_g L e(t_g)` as `k`-modules**
(arXiv:1309.3796v3, proof of Lemma 7.17, for symmetric `Q`). -/
def midModelEquivₖ [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    MidModel j hj Q Λ Λc ν ν₀ L ≃ₗ[k]
      Π₀ g : MidGen j hj ν ν₀, BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g) :=
  { (midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃).toAddEquiv.trans
      (DFinsupp.mapRange.addEquiv fun g => idemPartEquiv L (midGenIdem (k := k) Q Λc g)) with
    map_smul' := fun c y => by
      induction y using Ind.induction_on with
      | zero => simp only [smul_zero, AddEquiv.toFun_eq_coe, map_zero]
      | add y y' hy hy' =>
        simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply] at hy hy' ⊢
        rw [smul_add, map_add, hy, hy', map_add, smul_add]
      | tmul z v =>
        rw [smul_tmul_midModel]
        refine DFinsupp.ext fun g => Subtype.ext ?_
        change ((midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃ (Ind.tmul z (c • v)) g : L)) =
          c • ((midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃ (Ind.tmul z v) g : L))
        rw [midModelEquiv_tmul, midModelEquiv_tmul, smul_comm] }

variable (j hj Q Λ Λc ν ν₀ ρ₃) in
/-- **A basis of the model of `K̃^{λ⁺}_λ` for a cap after `λ_j`** (arXiv:1309.3796v3, proof of
Lemma 7.17, for symmetric `Q`). Fix reduced words `ρ₂`, `ρ₃` and, for each red-ordered loading
`t` at the maximum, a basis `B′_t` of `L e(t)`. Then the elements indexed by the pairs
`((s, t, d, u), b′)` with `b′ ∈ B′_t` form a basis of `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}`; the element of
index `(g, b′)` is `b′ γ_g`. -/
def midModelBasis [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2)))) :
    Module.Basis (Σ g : MidGen j hj ν ν₀, ι ⟨g.t, g.ht⟩) k (MidModel j hj Q Λ Λc ν ν₀ L) :=
  (DFinsupp.basis fun g : MidGen j hj ν ν₀ => B' ⟨g.t, g.ht⟩).map
    (midModelEquivₖ j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃).symm

end Categorification.Stendhal.CupCap
