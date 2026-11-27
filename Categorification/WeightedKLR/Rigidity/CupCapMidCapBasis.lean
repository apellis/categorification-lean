/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndBasis
import Categorification.WeightedKLR.Rigidity.CupCapMidKLRAll
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMapEquiv
import Categorification.WeightedKLR.Rigidity.CupCapMidTripleBasis

/-!
# The basis `B″` of `K̃^{λ⁺}_λ` for a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.17, for a cap inserted after the red strand `λ_j`,
any `j ≤ ℓ`. The bimodule `K̃^{λ⁺}_λ` is the model with the maximum before `λ_{j+1}`
(`midCapModelEquiv`), as `k`-modules through the right scalars of `T̃^{λ⁺}`
(`midCapModelEquivₖ`). For symmetric `Q`, the model has a basis indexed by Webster's set `B″`
(`midTripleBasis`), so `K̃^{λ⁺}_λ` has a basis indexed by `B″` (`midCapBasis`).

The element of index `(τ, b′)` is Webster's diagram of `B″`: the maximum at its canonical
position at the top carrying `b′`, followed by `γ_g`, in which every strand passes under the cap
(`midCapBasis_apply`).

Route hypotheses (tracked, see the README): `PullOff L` (Lemma 7.16) and `PullOffLeft L` (its
mirror), the scalars of (max1) are units, and `L` is supported on the loadings `μ ⋯ μ*`.

## Main definitions

* `midCapModelEquivₖ`: `K̃^{λ⁺}_λ` is the model, as `k`-modules.
* `midCapBasis`: **Lemma 7.17** for a cap after `λ_j`, a basis of `K̃^{λ⁺}_λ` indexed by `B″`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- The right scalars of `T̃^{λ⁺}` act on the model through its `k`-module structure. -/
theorem envScalar_smul_midBimod
    {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (c : k) (y : MidBimod L hL hR) :
    (ofMidBimod L hL hR (envScalar k Q Λ Λc j hj ν ν₀ c • y) : MidModel j hj Q Λ Λc ν ν₀ L) =
      c • ofMidBimod L hL hR y := by
  change midEnvAlg L hL hR (envScalar k Q Λ Λc j hj ν ν₀ c) y = _
  rw [envScalar_apply, midEnvAlg_mk, map_one, Module.End.one_apply]
  rfl

/-- **`K̃^{λ⁺}_λ` is the model, as `k`-modules**, for a cap after `λ_j`. -/
def midCapModelEquivₖ
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) :
    CapTilde k Q Λ Λc j hj ν ν₀ L ≃ₗ[k] MidModel j hj Q Λ Λc ν ν₀ L where
  toFun z := ofMidBimod L hL (midKLRRel hκ hP hPL)
    (midCapModelEquiv hP hPL hκ (midKLRRel hκ hP hPL) z)
  invFun y := (midCapModelEquiv hP hPL hκ (midKLRRel hκ hP hPL)).symm
    (toMidBimod L hL (midKLRRel hκ hP hPL) y)
  map_add' z z' := by rw [map_add]; rfl
  map_smul' c z := by
    rw [capTilde_smul_def, LinearEquiv.map_smul, envScalar_smul_midBimod]
    rfl
  left_inv z := (midCapModelEquiv hP hPL hκ (midKLRRel hκ hP hPL)).symm_apply_apply z
  right_inv y := (midCapModelEquiv hP hPL hκ (midKLRRel hκ hP hPL)).apply_symm_apply _

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **Lemma 7.17** (Webster, arXiv:1309.3796v3, §7.3) for a cap after `λ_j`, symmetric `Q`.
Fix reduced words `ρ₂`, `ρ₃` and, for each red-ordered loading `t` at the maximum, a basis `B′_t`
of `L e(t)`. Then `K̃^{λ⁺}_λ` has a basis indexed by the pairs `(τ, b′)` of a triple `τ` of
`B″` (a basis term of `T̃^λ`, a cap-good loading `t` at the maximum, a shuffle of `t` with the
`j`-th black block) and `b′ ∈ B′_t`. The element of index `(τ, b′)` is the cap at its canonical
position at the top carrying `b′`, followed by the diagram `γ_g` of the triple
(`midCapBasis_apply`).

Route hypotheses (tracked, see the README): `hκ` (the scalars of (max1) are units), `hL` (`L` is
supported on the loadings `μ ⋯ μ*`), `hP` (Lemma 7.16) and `hPL` (its mirror). -/
def midCapBasis [DecidableEq (MidGen j hj ν ν₀)] [Nontrivial k] (hQ : KLRSymm Q)
    {ρ₂ : Equiv.Perm (Fin N) → List ℕ} {ρ₃ : Equiv.Perm (Fin M) → List ℕ}
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2)))) :
    Module.Basis (Σ τ : MidTriple ℓ j ν ν₀, ι ⟨τ.t, τ.ht⟩) k (CapTilde k Q Λ Λc j hj ν ν₀ L) :=
  (midTripleBasis j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ hL B').map
    (midCapModelEquivₖ hL hP hPL hκ).symm

end Categorification.Stendhal.CupCap
