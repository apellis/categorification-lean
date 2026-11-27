/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndFree

/-!
# The basis `B″` of `K̃^{λ⁺}_λ` for a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.17, in the case `j = ℓ` (the cap inserted right of all
red strands of `λ`). The bimodule `K̃^{λ⁺}_λ` is a `k`-module through the right action of the
scalars of `T̃^{λ⁺}`. For symmetric `Q`, with (max1) scalars that are units, a right
`T̃^{(μ,μ*)}`-module `L` supported on the loadings `μ ⋯ μ*`, and the pull-off identity
`PullOffLeft` (the mirror of Lemma 7.16), `K̃^{λ⁺}_λ ≅ ⨁_g L e(j_g)` as `k`-modules, the sum over
the generators `g = (b, j, u)`: a basis term `b` of `T̃^λ` with dots on top, a red-ordered
loading `j` at the maximum and a shuffle `u` (`capEquiv`). Given bases `B′_j` of the pieces
`L e(j)`, the elements `b · cap · b′ · ψ_u` form a basis of `K̃^{λ⁺}_λ` indexed by the triples
`(g, b′)` with `b′ ∈ B′_{j_g}` (`capBasis`): this is the set `B″` of Lemma 7.17. Reduced words
are fixed arbitrarily (`ρ₁`, `ρ₂`, `ρ₃`), as in the source.

## Main definitions

* `capEquiv`: `K̃^{λ⁺}_λ ≅ ⨁_g L e(j_g)` as `k`-modules.
* `capBasis`: **Lemma 7.17** for `j = ℓ`, the basis `B″` of `K̃^{λ⁺}_λ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

-- the `ℤ`-algebra structures used by the balanced tensor products of `InductionAlong`
attribute [local instance 1200] Ring.toIntAlgebra

/-! ### Scalars on `K̃^{λ⁺}_λ` -/

section Scalars

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

variable (k Q Λ Λc j hj ν ν₀) in
/-- The scalars of `k`, acting on the right through `T̃^{λ⁺}`. -/
def envScalar : k →+* Env k Q Λ Λc j hj ν ν₀ :=
  ((Algebra.TensorProduct.includeRight (R := k) (A := StendhalAlgebra k Q Λ ν)
      (B := (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)).toRingHom.comp
    (algebraMap k _) :
    k →+* StendhalAlgebra k Q Λ ν ⊗[k] (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)

theorem envScalar_apply (c : k) :
    envScalar k Q Λ Λc j hj ν ν₀ c =
      Env.mk 1 (algebraMap k (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) c) :=
  rfl

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- `K̃^{λ⁺}_λ` is a `k`-module through the right action of the scalars of `T̃^{λ⁺}`. -/
instance : Module k (CapTilde k Q Λ Λc j hj ν ν₀ L) :=
  Module.compHom _ (envScalar k Q Λ Λc j hj ν ν₀)

theorem capTilde_smul_def (c : k) (z : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    c • z = envScalar k Q Λ Λc j hj ν ν₀ c • z :=
  rfl

end Scalars

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-! ### The model as a `k`-module -/

/-- The right scalars of `T̃^{λ⁺}` on the model are its scalars. -/
theorem envScalar_smul_endModel (c : k) (y : EndModel Q Λ Λc ν ν₀ L) :
    envScalar k Q Λ Λc ℓ le_rfl ν ν₀ c • y = c • y := by
  rw [envScalar_apply, envMk_smul, leftAct_one, LinearMap.id_apply]
  rfl

variable (Q Λ Λc ν₀) in
/-- **`K̃^{λ⁺}_λ` is the model, as `k`-modules.** -/
def capModelEquivₖ (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) :
    CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L ≃ₗ[k] EndModel Q Λ Λc ν ν₀ L where
  toFun := capModelEquiv Q Λ Λc ν₀ L hκ hL hP
  invFun := (capModelEquiv Q Λ Λc ν₀ L hκ hL hP).symm
  map_add' := map_add _
  map_smul' c z := by
    rw [capTilde_smul_def, LinearEquiv.map_smul, envScalar_smul_endModel]
    rfl
  left_inv := (capModelEquiv Q Λ Λc ν₀ L hκ hL hP).left_inv
  right_inv := (capModelEquiv Q Λ Λc ν₀ L hκ hL hP).right_inv

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- Scalars pass from the corner to `L` in the model. -/
theorem smul_tmul_endModel (c : k) (z : Corner (endOp Q Λ Λc ν ν₀)) (v : L) :
    c • (Ind.tmul z v : EndModel Q Λ Λc ν ν₀ L) = Ind.tmul z (c • v) := by
  have hz : z.1 * endOp Q Λ Λc ν ν₀ 1 = z.1 := z.2
  have h : algebraMap k Tpᵐᵒᵖ c • z = op (algebraMap k Tcᵐᵒᵖ c) • z := by
    apply Subtype.ext
    change algebraMap k Tpᵐᵒᵖ c * z.1 = z.1 * endOp Q Λ Λc ν ν₀ (algebraMap k Tcᵐᵒᵖ c)
    have e1 : endOp Q Λ Λc ν ν₀ (algebraMap k Tcᵐᵒᵖ c) = c • endOp Q Λ Λc ν ν₀ 1 := by
      rw [endOp_apply, endOp_apply, Algebra.algebraMap_eq_smul_one, unop_smul, unop_one,
        map_smul, op_smul]
    rw [e1, mul_smul_comm, hz, ← Algebra.smul_def]
  rw [algebraMap_smul, Ind.smul_tmul, h, Ind.op_smul_tmul, _root_.algebraMap_smul]

/-- The pieces `L e(j)`, as `k`-modules and as abelian groups. -/
def idemPartEquiv (e : Tcᵐᵒᵖ) :
    BalancedTensor.idemPart ℤ L e ≃+ BalancedTensor.idemPart k L e where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem endModelEquiv_tmul [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (z : Corner (endOp Q Λ Λc ν ν₀)) (v : L) (g : EndGen ν₀ ρ₁) :
    ((endModelEquiv Q Λ Λc ν ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ (Ind.tmul z v) g : L)) =
      (BalancedTensor.idemCoord (endIdemSum_bijective hQ hρ₁ hρ₂ hρ₃) z g : Tcᵐᵒᵖ) • v :=
  BalancedTensor.idemEquiv_tmul _ _ _ z v g

variable (Q Λ Λc ν ν₀ ρ₁ ρ₃) in
/-- **The model of `K̃` for a cap at the right end is `⨁_g L e(j_g)` as `k`-modules.** -/
def endModelEquivₖ [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    EndModel Q Λ Λc ν ν₀ L ≃ₗ[k]
      Π₀ g : EndGen ν₀ ρ₁, BalancedTensor.idemPart k L (genIdem (k := k) Q Λc g) :=
  { (endModelEquiv Q Λ Λc ν ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃).toAddEquiv.trans
      (DFinsupp.mapRange.addEquiv fun g => idemPartEquiv L (genIdem (k := k) Q Λc g)) with
    map_smul' := fun c y => by
      induction y using Ind.induction_on with
      | zero => simp only [smul_zero, AddEquiv.toFun_eq_coe, map_zero]
      | add y y' hy hy' =>
        simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply] at hy hy' ⊢
        rw [smul_add, map_add, hy, hy', map_add, smul_add]
      | tmul z v =>
        rw [smul_tmul_endModel]
        refine DFinsupp.ext fun g => Subtype.ext ?_
        change ((endModelEquiv Q Λ Λc ν ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ (Ind.tmul z (c • v)) g : L)) =
          c • ((endModelEquiv Q Λ Λc ν ν₀ ρ₁ ρ₃ L hQ hρ₁ hρ₂ hρ₃ (Ind.tmul z v) g : L))
        rw [endModelEquiv_tmul, endModelEquiv_tmul, smul_comm] }

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **`K̃^{λ⁺}_λ ≅ ⨁_g L e(j_g)`** (arXiv:1309.3796v3, proof of Lemma 7.17, `j = ℓ`), as
`k`-modules, over the generators `g = (b, j, u)`. -/
def capEquiv [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) :
    CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L ≃ₗ[k]
      Π₀ g : EndGen ν₀ ρ₁, BalancedTensor.idemPart k L (genIdem (k := k) Q Λc g) :=
  (capModelEquivₖ Q Λ Λc ν₀ L hκ hL hP).trans
    (endModelEquivₖ Q Λ Λc ν ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃)

variable (Q Λ Λc ν₀ ρ₁ ρ₃) in
/-- **The basis `B″` of `K̃^{λ⁺}_λ`** (arXiv:1309.3796v3, Lemma 7.17, for the cap at the right
end, `j = ℓ`, and symmetric `Q`). Fix reduced words `ρ₁`, `ρ₂`, `ρ₃` and, for each red-ordered
loading `j` at the maximum, a basis `B′_j` of `L e(j)`. Then the elements indexed by the triples
`((b, j, u), b′)` with `b` a basis term of `T̃^λ` with dots on top, `u` a shuffle and
`b′ ∈ B′_j` form a basis of `K̃^{λ⁺}_λ`; the element of index `((b, j, u), b′)` corresponds to
`b′ γ_{(b, j, u)}` in the model.

Route hypotheses (tracked, see the README): `hκ` (the scalars of (max1) are units, as in
Webster's (7.27), which divides by them), `hL` (`L` is supported on the loadings `μ ⋯ μ*`, which
holds for `L_μ`, `span_canonical_coevaluationHead`) and `hP` (the mirror of Lemma 7.16). -/
def capBasis [DecidableEq (EndGen ν₀ ρ₁)] (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L)
    {ι : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j} → Type*}
    (B' : ∀ j, Module.Basis (ι j) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) j.1 j.2)))) :
    Module.Basis (Σ g : EndGen ν₀ ρ₁, ι ⟨g.1.2.1, g.2.1⟩) k (CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L) :=
  (DFinsupp.basis fun g : EndGen ν₀ ρ₁ => B' ⟨g.1.2.1, g.2.1⟩).map
    (capEquiv Q Λ Λc ν₀ L ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ hκ hL hP).symm

end Categorification.Stendhal.CupCap
