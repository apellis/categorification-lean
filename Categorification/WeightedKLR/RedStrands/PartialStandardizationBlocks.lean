/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationExact

/-!
# Partial standardization with three consecutive blocks

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+r}}` defined
after Definition 5.4, for three consecutive blocks of red strands. The module is built by
iterating the partial standardization at a cut (`CutStandard`): a module `N` over
`T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))` is first standardized at the cut between the last two blocks,
the action of the first factor `T^A(θ)` passing to the result by functoriality
(`cutStandardEnd`), and the result, a module over `T^A(θ) ⊗ T^{MR}(β + γ)`, is standardized at
the cut after the first block.

Webster defines the partial standardization with any number of blocks in one step and uses
without proof that it agrees with iterated partial standardization; here the iterated form is
the definition.

## Main definitions

* `Stendhal.cutStandardEnd`: partial standardization at a cut on endomorphisms, a ring map.
* `Stendhal.blocksFactorAlgebra`: the algebra `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))` of the three blocks.
* `Stendhal.BlocksMid`: the standardization at the inner cut, a module over
  `T^A(θ) ⊗ T^{MR}(β + γ)`.
* `Stendhal.BlocksStandard`: the partial standardization with three blocks.
* `Stendhal.blocksStandardAction`: the action of `T^λ(θ + (β + γ))` on it.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-! ### Functoriality of the partial standardization at a cut -/

section Functorial

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (cutFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N']
  [AddCommGroup N''] [Module k N''] [Module (cutFactorAlgebra Q Λ θ β) N'']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N'']

theorem cutStandardMap_id :
    cutStandardMap Q Λ θ β (LinearMap.id : N →ₗ[cutFactorAlgebra Q Λ θ β] N) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  refine (cutStandardMap_mk Q Λ θ β _ y).trans (congrArg Submodule.Quotient.mk ?_)
  induction y using BalancedTensor.induction_on with
  | zero => exact map_zero _
  | tmul m n => rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem cutStandardMap_comp (g : N →ₗ[cutFactorAlgebra Q Λ θ β] N')
    (g' : N' →ₗ[cutFactorAlgebra Q Λ θ β] N'') (z : CutStandard Q Λ θ β N) :
    cutStandardMap Q Λ θ β (g' ∘ₗ g) z =
      cutStandardMap Q Λ θ β g' (cutStandardMap Q Λ θ β g z) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  refine (cutStandardMap_mk Q Λ θ β _ y).trans (congrArg Submodule.Quotient.mk ?_)
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul m n => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem cutStandardMap_add (g g' : N →ₗ[cutFactorAlgebra Q Λ θ β] N')
    (z : CutStandard Q Λ θ β N) :
    cutStandardMap Q Λ θ β (g + g') z =
      cutStandardMap Q Λ θ β g z + cutStandardMap Q Λ θ β g' z := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  refine (cutStandardMap_mk Q Λ θ β _ y).trans ?_
  rw [Submodule.mkQ_apply, cutStandardMap_mk, cutStandardMap_mk, ← Submodule.Quotient.mk_add]
  refine congrArg Submodule.Quotient.mk ?_
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul m n => exact BalancedTensor.tmul_add _ _ _
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]; abel

theorem cutStandardMap_smul_id (c : k) (z : CutStandard Q Λ θ β N) :
    cutStandardMap Q Λ θ β
      (c • (LinearMap.id : N →ₗ[cutFactorAlgebra Q Λ θ β] N)) z = c • z := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  refine (cutStandardMap_mk Q Λ θ β _ y).trans ?_
  rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul]
  refine congrArg Submodule.Quotient.mk ?_
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul m n => exact BalancedTensor.tmul_smul _ _ _
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-- **Partial standardization at a cut on endomorphisms**: the ring map
`End_D(N) → End_k(𝕊(N))`, by functoriality. -/
def cutStandardEnd :
    Module.End (cutFactorAlgebra Q Λ θ β) N →+* Module.End k (CutStandard Q Λ θ β N) where
  toFun g := cutStandardMap Q Λ θ β g
  map_one' := cutStandardMap_id Q Λ θ β
  map_mul' g g' := LinearMap.ext (cutStandardMap_comp Q Λ θ β g' g)
  map_zero' := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    refine (cutStandardMap_mk Q Λ θ β _ y).trans ?_
    rw [LinearMap.zero_apply, ← Submodule.Quotient.mk_zero]
    refine congrArg Submodule.Quotient.mk ?_
    induction y using BalancedTensor.induction_on with
    | zero => exact map_zero _
    | tmul m n => exact BalancedTensor.tmul_zero _
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  map_add' g g' := LinearMap.ext (cutStandardMap_add Q Λ θ β g g')

theorem cutStandardEnd_apply (g : Module.End (cutFactorAlgebra Q Λ θ β) N) :
    cutStandardEnd Q Λ θ β g = cutStandardMap Q Λ θ β g := rfl

/-- A map of modules commuting with two endomorphisms gives a map of partial standardizations
commuting with their standardizations. -/
theorem cutStandardMap_comm (g : N →ₗ[cutFactorAlgebra Q Λ θ β] N')
    (u : Module.End (cutFactorAlgebra Q Λ θ β) N) (u' : Module.End (cutFactorAlgebra Q Λ θ β) N')
    (h : ∀ n, g (u n) = u' (g n)) (z : CutStandard Q Λ θ β N) :
    cutStandardMap Q Λ θ β g (cutStandardEnd Q Λ θ β u z) =
      cutStandardEnd Q Λ θ β u' (cutStandardMap Q Λ θ β g z) := by
  rw [cutStandardEnd_apply, cutStandardEnd_apply, ← cutStandardMap_comp,
    ← cutStandardMap_comp]
  exact congrArg (fun f => cutStandardMap Q Λ θ β f z) (LinearMap.ext h)

end Functorial

/-! ### Three consecutive blocks -/

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)

/-- The red labels of the last two blocks. -/
abbrev blocksTailLabels : Fin (m + r) → I →₀ ℕ := Λ ∘ Fin.natAdd a

/-- The tensor product algebra of the first block. -/
abbrev blocksHeadAlgebra := TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (m + r)) θ

/-- **The algebra of three consecutive blocks**, `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`. -/
abbrev blocksFactorAlgebra :=
  blocksHeadAlgebra Q Λ θ ⊗[k] cutFactorAlgebra Q (blocksTailLabels Λ) β γ

local notation "A₀" => blocksHeadAlgebra Q Λ θ
local notation "D₃" => blocksFactorAlgebra Q Λ θ β γ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksTailLabels Λ) β γ

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]

/-- A module over the three blocks, as a module over the last two. -/
@[nolint unusedArguments]
def BlocksInner (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (a + (m + r)) → I →₀ ℕ)
    (_θ _β _γ : Multiset I) (N : Type*) : Type _ := N

instance : AddCommGroup (BlocksInner Q Λ θ β γ N) := inferInstanceAs (AddCommGroup N)
instance : Module k (BlocksInner Q Λ θ β γ N) := inferInstanceAs (Module k N)
instance : Module (blocksFactorAlgebra Q Λ θ β γ) (BlocksInner Q Λ θ β γ N) :=
  inferInstanceAs (Module (blocksFactorAlgebra Q Λ θ β γ) N)
instance : IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) (BlocksInner Q Λ θ β γ N) :=
  inferInstanceAs (IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N)
instance : Module (cutFactorAlgebra Q (blocksTailLabels Λ) β γ) (BlocksInner Q Λ θ β γ N) :=
  Module.compHom N (Algebra.TensorProduct.includeRight : Dᵢ →ₐ[k] D₃).toRingHom

omit [Module k N] [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksInner_smul (d : Dᵢ) (n : BlocksInner Q Λ θ β γ N) :
    d • n = ((1 : A₀) ⊗ₜ[k] d : D₃) • n := rfl

instance : IsScalarTower k (cutFactorAlgebra Q (blocksTailLabels Λ) β γ)
    (BlocksInner Q Λ θ β γ N) where
  smul_assoc c d n := by
    change ((1 : A₀) ⊗ₜ[k] (c • d) : D₃) • (n : N) = c • ((1 : A₀) ⊗ₜ[k] d : D₃) • (n : N)
    rw [TensorProduct.tmul_smul, smul_assoc]

/-- The action of `t ∈ T^A(θ)` on a module over the three blocks, linear over the last two. -/
def blocksHeadEnd (t : A₀) :
    Module.End (cutFactorAlgebra Q (blocksTailLabels Λ) β γ) (BlocksInner Q Λ θ β γ N) where
  toFun n := (t ⊗ₜ[k] (1 : Dᵢ) : D₃) • n
  map_add' := smul_add _
  map_smul' d n := by
    change (t ⊗ₜ[k] (1 : Dᵢ) : D₃) • ((1 : A₀) ⊗ₜ[k] d : D₃) • (n : N) =
      ((1 : A₀) ⊗ₜ[k] d : D₃) • (t ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N)
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, one_mul]

omit [Module k N] [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksHeadEnd_apply (t : A₀) (n : BlocksInner Q Λ θ β γ N) :
    blocksHeadEnd Q Λ θ β γ N t n = (t ⊗ₜ[k] (1 : Dᵢ) : D₃) • n := rfl

/-- The action of `T^A(θ)` on a module over the three blocks, by maps linear over the last
two. -/
def blocksHeadRingHom :
    A₀ →+* Module.End (cutFactorAlgebra Q (blocksTailLabels Λ) β γ) (BlocksInner Q Λ θ β γ N) :=
  RingHom.mk'
    { toFun := blocksHeadEnd Q Λ θ β γ N
      map_one' := LinearMap.ext fun n => by
        change ((1 : A₀) ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N) = (n : N)
        exact one_smul D₃ (show N from n)
      map_mul' t t' := LinearMap.ext fun n => by
        change ((t * t') ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N) =
          (t ⊗ₜ[k] (1 : Dᵢ) : D₃) • (t' ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N)
        rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one] }
  fun t t' => LinearMap.ext fun n => by
    change ((t + t') ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N) =
      (t ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N) + (t' ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N)
    exact (congrArg (fun x : D₃ => x • (show N from n)) (TensorProduct.add_tmul _ _ _)).trans
      (add_smul _ _ (show N from n))

/-- **The action of the first block on the inner standardization**: `T^A(θ)` acts on the
partial standardization at the inner cut by functoriality. -/
def blocksHeadAction :
    A₀ →ₐ[k] Module.End k
      (CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)) where
  __ := (cutStandardEnd Q (blocksTailLabels Λ) β γ).comp (blocksHeadRingHom Q Λ θ β γ N)
  commutes' c := by
    refine LinearMap.ext fun z => ?_
    change cutStandardMap Q (blocksTailLabels Λ) β γ (blocksHeadEnd Q Λ θ β γ N _) z = c • z
    have h : blocksHeadEnd Q Λ θ β γ N (algebraMap k A₀ c) =
        c • (LinearMap.id : Module.End Dᵢ (BlocksInner Q Λ θ β γ N)) := LinearMap.ext fun n => by
      change ((algebraMap k A₀ c) ⊗ₜ[k] (1 : Dᵢ) : D₃) • (n : N) = c • (n : N)
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', smul_assoc]
      exact congrArg (c • ·) (one_smul D₃ (show N from n))
    rw [h, cutStandardMap_smul_id]

theorem blocksHeadAction_apply (t : A₀)
    (z : CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)) :
    blocksHeadAction Q Λ θ β γ N t z =
      cutStandardMap Q (blocksTailLabels Λ) β γ (blocksHeadEnd Q Λ θ β γ N t) z := rfl

variable (hQ : KLRSymm Q)

/-- The action of `T^A(θ)` commutes with the action of `T^{MR}(β + γ)`. -/
theorem commute_blocksHeadAction (t : A₀)
    (u : TensorProductAlgebra k Q (blocksTailLabels Λ) (β + γ)) :
    Commute (blocksHeadAction Q Λ θ β γ N t)
      (cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ u) :=
  LinearMap.ext fun z =>
    cutStandardMap_action Q (blocksTailLabels Λ) β γ hQ (blocksHeadEnd Q Λ θ β γ N t) u z

/-- The action of `T^A(θ) ⊗ T^{MR}(β + γ)` on the inner standardization. -/
def blocksMidAction :
    cutFactorAlgebra Q Λ θ (β + γ) →ₐ[k] Module.End k
      (CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)) :=
  Algebra.TensorProduct.lift (blocksHeadAction Q Λ θ β γ N)
    (cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ)
    (commute_blocksHeadAction Q Λ θ β γ N hQ)

/-- **The standardization at the inner cut**, as a module over `T^A(θ) ⊗ T^{MR}(β + γ)`. -/
@[nolint unusedArguments]
def BlocksMid (_hQ : KLRSymm Q) : Type _ :=
  CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)

instance : AddCommGroup (BlocksMid Q Λ θ β γ N hQ) :=
  inferInstanceAs (AddCommGroup (CutStandard Q (blocksTailLabels Λ) β γ _))
instance : Module k (BlocksMid Q Λ θ β γ N hQ) :=
  inferInstanceAs (Module k (CutStandard Q (blocksTailLabels Λ) β γ _))
instance : Module (cutFactorAlgebra Q Λ θ (β + γ)) (BlocksMid Q Λ θ β γ N hQ) :=
  Module.compHom (CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N))
    (blocksMidAction Q Λ θ β γ N hQ).toRingHom

theorem blocksMid_smul (d : cutFactorAlgebra Q Λ θ (β + γ)) (z : BlocksMid Q Λ θ β γ N hQ) :
    d • z = blocksMidAction Q Λ θ β γ N hQ d z := rfl

instance : IsScalarTower k (cutFactorAlgebra Q Λ θ (β + γ)) (BlocksMid Q Λ θ β γ N hQ) where
  smul_assoc c d z := by
    rw [blocksMid_smul, blocksMid_smul, map_smul]
    rfl

/-- **The partial standardization with three blocks**
`𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+r}}(N)` of a module `N` over
`T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`. -/
abbrev BlocksStandard : Type _ := CutStandard Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)

/-- **The action of `T^λ(θ + (β + γ))` on the partial standardization with three blocks.** -/
def blocksStandardAction :
    TensorProductAlgebra k Q Λ (θ + (β + γ)) →ₐ[k]
      Module.End k (BlocksStandard Q Λ θ β γ N hQ) :=
  cutStandardAction Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ) hQ

end Categorification.Stendhal
