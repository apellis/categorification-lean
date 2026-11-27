/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocks

/-!
# Partial standardization with three blocks, first cut first

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+r}}` defined
after Definition 5.4, in the second order of the two cuts. A module `N` over
`(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)` is first standardized at the cut between the first two blocks,
the action of the last factor `T^R(γ)` passing to the result by functoriality
(`cutStandardEnd`), and the result, a module over `T^{AM}(θ + β) ⊗ T^R(γ)`, is standardized at
the cut before the last block. `PartialStandardizationBlocks` takes the cuts in the other
order.

## Main definitions

* `Stendhal.blocksFactorAlgebraL`: the algebra `(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`.
* `Stendhal.BlocksMidL`: the standardization at the first cut, a module over
  `T^{AM}(θ + β) ⊗ T^R(γ)`.
* `Stendhal.BlocksStandardL`: the partial standardization with three blocks, first cut first.
* `Stendhal.blocksStandardActionL`: the action of `T^λ((θ + β) + γ)` on it.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ((a + m) + r) → I →₀ ℕ) (θ β γ : Multiset I)

/-- The red labels of the first two blocks. -/
abbrev blocksLeftLabels : Fin (a + m) → I →₀ ℕ := Λ ∘ Fin.castAdd r

/-- The tensor product algebra of the last block. -/
abbrev blocksLastAlgebra := TensorProductAlgebra k Q (Λ ∘ Fin.natAdd (a + m)) γ

/-- **The algebra of three consecutive blocks**, `(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`. -/
abbrev blocksFactorAlgebraL :=
  cutFactorAlgebra Q (blocksLeftLabels Λ) θ β ⊗[k] blocksLastAlgebra Q Λ γ

local notation "A₀" => blocksLastAlgebra Q Λ γ
local notation "D₃" => blocksFactorAlgebraL Q Λ θ β γ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksLeftLabels Λ) θ β

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebraL Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N]

/-- A module over the three blocks, as a module over the first two. -/
@[nolint unusedArguments]
def BlocksInnerL (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin ((a + m) + r) → I →₀ ℕ)
    (_θ _β _γ : Multiset I) (N : Type*) : Type _ := N

instance : AddCommGroup (BlocksInnerL Q Λ θ β γ N) := inferInstanceAs (AddCommGroup N)
instance : Module k (BlocksInnerL Q Λ θ β γ N) := inferInstanceAs (Module k N)
instance : Module (blocksFactorAlgebraL Q Λ θ β γ) (BlocksInnerL Q Λ θ β γ N) :=
  inferInstanceAs (Module (blocksFactorAlgebraL Q Λ θ β γ) N)
instance : IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) (BlocksInnerL Q Λ θ β γ N) :=
  inferInstanceAs (IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N)
instance : Module (cutFactorAlgebra Q (blocksLeftLabels Λ) θ β) (BlocksInnerL Q Λ θ β γ N) :=
  Module.compHom N (Algebra.TensorProduct.includeLeft : Dᵢ →ₐ[k] D₃).toRingHom

omit [Module k N] [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] in
theorem blocksInnerL_smul (d : Dᵢ) (n : BlocksInnerL Q Λ θ β γ N) :
    d • n = (d ⊗ₜ[k] (1 : A₀) : D₃) • n := rfl

instance : IsScalarTower k (cutFactorAlgebra Q (blocksLeftLabels Λ) θ β)
    (BlocksInnerL Q Λ θ β γ N) where
  smul_assoc c d n := by
    change ((c • d) ⊗ₜ[k] (1 : A₀) : D₃) • (n : N) = c • (d ⊗ₜ[k] (1 : A₀) : D₃) • (n : N)
    rw [← TensorProduct.smul_tmul', smul_assoc]

/-- The action of `t ∈ T^R(γ)` on a module over the three blocks, linear over the first two. -/
def blocksLastEnd (t : A₀) :
    Module.End (cutFactorAlgebra Q (blocksLeftLabels Λ) θ β) (BlocksInnerL Q Λ θ β γ N) where
  toFun n := ((1 : Dᵢ) ⊗ₜ[k] t : D₃) • n
  map_add' := smul_add _
  map_smul' d n := by
    change ((1 : Dᵢ) ⊗ₜ[k] t : D₃) • (d ⊗ₜ[k] (1 : A₀) : D₃) • (n : N) =
      (d ⊗ₜ[k] (1 : A₀) : D₃) • ((1 : Dᵢ) ⊗ₜ[k] t : D₃) • (n : N)
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, one_mul]

omit [Module k N] [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N] in
theorem blocksLastEnd_apply (t : A₀) (n : BlocksInnerL Q Λ θ β γ N) :
    blocksLastEnd Q Λ θ β γ N t n = ((1 : Dᵢ) ⊗ₜ[k] t : D₃) • n := rfl

/-- The action of `T^R(γ)` on a module over the three blocks, by maps linear over the first
two. -/
def blocksLastRingHom :
    A₀ →+* Module.End (cutFactorAlgebra Q (blocksLeftLabels Λ) θ β)
      (BlocksInnerL Q Λ θ β γ N) :=
  RingHom.mk'
    { toFun := blocksLastEnd Q Λ θ β γ N
      map_one' := LinearMap.ext fun n => by
        change ((1 : Dᵢ) ⊗ₜ[k] (1 : A₀) : D₃) • (n : N) = (n : N)
        exact one_smul D₃ (show N from n)
      map_mul' t t' := LinearMap.ext fun n => by
        change ((1 : Dᵢ) ⊗ₜ[k] (t * t') : D₃) • (n : N) =
          ((1 : Dᵢ) ⊗ₜ[k] t : D₃) • ((1 : Dᵢ) ⊗ₜ[k] t' : D₃) • (n : N)
        rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one] }
  fun t t' => LinearMap.ext fun n => by
    change ((1 : Dᵢ) ⊗ₜ[k] (t + t') : D₃) • (n : N) =
      ((1 : Dᵢ) ⊗ₜ[k] t : D₃) • (n : N) + ((1 : Dᵢ) ⊗ₜ[k] t' : D₃) • (n : N)
    exact (congrArg (fun x : D₃ => x • (show N from n)) (TensorProduct.tmul_add _ _ _)).trans
      (add_smul _ _ (show N from n))

/-- **The action of the last block on the inner standardization**: `T^R(γ)` acts on the
partial standardization at the first cut by functoriality. -/
def blocksLastAction :
    A₀ →ₐ[k] Module.End k
      (CutStandard Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)) where
  __ := (cutStandardEnd Q (blocksLeftLabels Λ) θ β).comp (blocksLastRingHom Q Λ θ β γ N)
  commutes' c := by
    refine LinearMap.ext fun z => ?_
    change cutStandardMap Q (blocksLeftLabels Λ) θ β (blocksLastEnd Q Λ θ β γ N _) z = c • z
    have h : blocksLastEnd Q Λ θ β γ N (algebraMap k A₀ c) =
        c • (LinearMap.id : Module.End Dᵢ (BlocksInnerL Q Λ θ β γ N)) :=
      LinearMap.ext fun n => by
        change ((1 : Dᵢ) ⊗ₜ[k] (algebraMap k A₀ c) : D₃) • (n : N) = c • (n : N)
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, smul_assoc]
        exact congrArg (c • ·) (one_smul D₃ (show N from n))
    rw [h, cutStandardMap_smul_id]

theorem blocksLastAction_apply (t : A₀)
    (z : CutStandard Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)) :
    blocksLastAction Q Λ θ β γ N t z =
      cutStandardMap Q (blocksLeftLabels Λ) θ β (blocksLastEnd Q Λ θ β γ N t) z := rfl

variable (hQ : KLRSymm Q)

/-- The action of `T^{AM}(θ + β)` commutes with the action of `T^R(γ)`. -/
theorem commute_blocksLastAction
    (u : TensorProductAlgebra k Q (blocksLeftLabels Λ) (θ + β)) (t : A₀) :
    Commute (cutStandardAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N) hQ u)
      (blocksLastAction Q Λ θ β γ N t) :=
  (LinearMap.ext fun z =>
    cutStandardMap_action Q (blocksLeftLabels Λ) θ β hQ (blocksLastEnd Q Λ θ β γ N t) u z).symm

/-- The action of `T^{AM}(θ + β) ⊗ T^R(γ)` on the standardization at the first cut. -/
def blocksMidActionL :
    cutFactorAlgebra Q Λ (θ + β) γ →ₐ[k] Module.End k
      (CutStandard Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)) :=
  Algebra.TensorProduct.lift
    (cutStandardAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N) hQ)
    (blocksLastAction Q Λ θ β γ N)
    (commute_blocksLastAction Q Λ θ β γ N hQ)

/-- **The standardization at the first cut**, as a module over `T^{AM}(θ + β) ⊗ T^R(γ)`. -/
@[nolint unusedArguments]
def BlocksMidL (_hQ : KLRSymm Q) : Type _ :=
  CutStandard Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)

instance : AddCommGroup (BlocksMidL Q Λ θ β γ N hQ) :=
  inferInstanceAs (AddCommGroup (CutStandard Q (blocksLeftLabels Λ) θ β _))
instance : Module k (BlocksMidL Q Λ θ β γ N hQ) :=
  inferInstanceAs (Module k (CutStandard Q (blocksLeftLabels Λ) θ β _))
instance : Module (cutFactorAlgebra Q Λ (θ + β) γ) (BlocksMidL Q Λ θ β γ N hQ) :=
  Module.compHom (CutStandard Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N))
    (blocksMidActionL Q Λ θ β γ N hQ).toRingHom

theorem blocksMidL_smul (d : cutFactorAlgebra Q Λ (θ + β) γ) (z : BlocksMidL Q Λ θ β γ N hQ) :
    d • z = blocksMidActionL Q Λ θ β γ N hQ d z := rfl

instance : IsScalarTower k (cutFactorAlgebra Q Λ (θ + β) γ) (BlocksMidL Q Λ θ β γ N hQ) where
  smul_assoc c d z := by
    rw [blocksMidL_smul, blocksMidL_smul, map_smul]
    rfl

/-- **The partial standardization with three blocks, first cut first**, of a module `N` over
`(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`. -/
abbrev BlocksStandardL : Type _ := CutStandard Q Λ (θ + β) γ (BlocksMidL Q Λ θ β γ N hQ)

/-- **The action of `T^λ((θ + β) + γ)` on the partial standardization with three blocks, first
cut first.** -/
def blocksStandardActionL :
    TensorProductAlgebra k Q Λ ((θ + β) + γ) →ₐ[k]
      Module.End k (BlocksStandardL Q Λ θ β γ N hQ) :=
  cutStandardAction Q Λ (θ + β) γ (BlocksMidL Q Λ θ β γ N hQ) hQ

end Categorification.Stendhal
