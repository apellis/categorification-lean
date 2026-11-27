/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocks

/-!
# Partial standardization at a cut with a spectator algebra

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4. To standardize some blocks of a module
over the algebra of several blocks while the other blocks are left alone, the remaining
blocks are carried along as a *spectator* algebra `E`: for a module `N` over
`(T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)) ⊗ E`, the partial standardization at the cut of
`N`, as a module over the first factor, is a module over `T^λ(θ + β) ⊗ E`, the action of `E`
passing to it by functoriality (`CutSpectStandard`). This generalizes the action of the first
block on the inner standardization in `PartialStandardizationBlocks` (`BlocksMid`), whose
spectator is the algebra of the first block. Partial standardization with a spectator is
exact (`cutSpectStandardMap_exact`), by Proposition 5.7 for the partial standardization at a
cut.

## Main definitions

* `Stendhal.CutSpectInput`: a module over `D ⊗ E`, as a module over the factor algebra `D`.
* `Stendhal.cutSpectAction`: the action of `E` on its partial standardization.
* `Stendhal.CutSpectStandard`: the partial standardization, a module over `T^λ(θ + β) ⊗ E`.
* `Stendhal.cutSpectStandardMap`: its action on maps of modules over `D ⊗ E`.

## Main results

* `Stendhal.cutSpectStandardMap_exact`, `cutSpectStandardMap_injective`,
  `cutSpectStandardMap_surjective`: partial standardization with a spectator is exact.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  (E : Type*) [Ring E] [Algebra k E]

local notation "D" => cutFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

/-- The algebra `D ⊗ E` of the factor algebra of the cut and the spectator. -/
def cutSpectAlgebra : Type _ := cutFactorAlgebra Q Λ θ β ⊗[k] E

instance : Ring (cutSpectAlgebra Q Λ θ β E) := Algebra.TensorProduct.instRing
instance : Algebra k (cutSpectAlgebra Q Λ θ β E) := Algebra.TensorProduct.instAlgebra

local notation "DE" => cutSpectAlgebra Q Λ θ β E

/-- The pure tensor `d ⊗ e` in `D ⊗ E`. -/
def cutSpectTmul (d : cutFactorAlgebra Q Λ θ β) (e : E) : cutSpectAlgebra Q Λ θ β E :=
  d ⊗ₜ[k] e

local notation "ι" => cutSpectTmul Q Λ θ β E

theorem cutSpectTmul_mul (d d' : D) (e e' : E) : ι d e * ι d' e' = ι (d * d') (e * e') :=
  Algebra.TensorProduct.tmul_mul_tmul d d' e e'

theorem cutSpectTmul_one : ι 1 1 = 1 := rfl

theorem cutSpectTmul_add_right (d : D) (e e' : E) : ι d (e + e') = ι d e + ι d e' :=
  TensorProduct.tmul_add d e e'

theorem cutSpectTmul_smul_left (c : k) (d : D) (e : E) : ι (c • d) e = c • ι d e :=
  (TensorProduct.smul_tmul' c d e).symm

theorem cutSpectTmul_smul_right (c : k) (d : D) (e : E) : ι d (c • e) = c • ι d e :=
  TensorProduct.tmul_smul c d e

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutSpectAlgebra Q Λ θ β E) N]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N]

/-- A module over `D ⊗ E`, as a module over the factor algebra `D` of the cut. -/
@[nolint unusedArguments]
def CutSpectInput (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (a + r) → I →₀ ℕ)
    (_θ _β : Multiset I) (_E : Type*) (N : Type*) : Type _ := N

instance : AddCommGroup (CutSpectInput Q Λ θ β E N) := inferInstanceAs (AddCommGroup N)
instance : Module k (CutSpectInput Q Λ θ β E N) := inferInstanceAs (Module k N)
instance : Module (cutFactorAlgebra Q Λ θ β) (CutSpectInput Q Λ θ β E N) :=
  Module.compHom N (show D →+* DE from
    (Algebra.TensorProduct.includeLeft : D →ₐ[k] D ⊗[k] E).toRingHom)

omit [Module k N] [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N] in
theorem cutSpectInput_smul (d : D) (n : CutSpectInput Q Λ θ β E N) :
    d • n = (ι d 1) • (show N from n) := rfl

instance : IsScalarTower k (cutFactorAlgebra Q Λ θ β) (CutSpectInput Q Λ θ β E N) where
  smul_assoc c d n := by
    change (ι (c • d) 1) • (show N from n) =
      c • (ι d 1) • (show N from n)
    rw [cutSpectTmul_smul_left, smul_assoc]

/-- The action of `e ∈ E` on a module over `D ⊗ E`, linear over `D`. -/
def cutSpectEnd (e : E) : Module.End (cutFactorAlgebra Q Λ θ β) (CutSpectInput Q Λ θ β E N) where
  toFun n := (ι 1 e) • (show N from n)
  map_add' n n' := smul_add (ι 1 e) (show N from n) (show N from n')
  map_smul' d n := by
    change (ι 1 e) • (ι d 1) • (show N from n) =
      (ι d 1) • (ι 1 e) • (show N from n)
    rw [← mul_smul, ← mul_smul, cutSpectTmul_mul, cutSpectTmul_mul, mul_one, one_mul, mul_one,
      one_mul]

omit [Module k N] [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N] in
theorem cutSpectEnd_apply (e : E) (n : CutSpectInput Q Λ θ β E N) :
    cutSpectEnd Q Λ θ β E N e n = (ι 1 e) • (show N from n) := rfl

/-- The action of `E` on a module over `D ⊗ E`, by maps linear over `D`. -/
def cutSpectRingHom : E →+* Module.End (cutFactorAlgebra Q Λ θ β) (CutSpectInput Q Λ θ β E N) :=
  RingHom.mk'
    { toFun := cutSpectEnd Q Λ θ β E N
      map_one' := LinearMap.ext fun n => by
        change (ι 1 (1 : E)) • (show N from n) = (show N from n)
        rw [cutSpectTmul_one, one_smul]
      map_mul' e e' := LinearMap.ext fun n => by
        change (ι 1 (e * e')) • (show N from n) =
          (ι 1 e) • (ι 1 e') • (show N from n)
        rw [← mul_smul, cutSpectTmul_mul, mul_one] }
  fun e e' => LinearMap.ext fun n => by
    change (ι 1 (e + e')) • (show N from n) =
      (ι 1 e) • (show N from n) +
        (ι 1 e') • (show N from n)
    rw [cutSpectTmul_add_right, add_smul]

/-- **The action of the spectator on the partial standardization**, by functoriality. -/
def cutSpectAction : E →ₐ[k] Module.End k (CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E N)) where
  __ := (cutStandardEnd Q Λ θ β).comp (cutSpectRingHom Q Λ θ β E N)
  commutes' c := by
    refine LinearMap.ext fun z => ?_
    change cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E N _) z = c • z
    have h : cutSpectEnd Q Λ θ β E N (algebraMap k E c) =
        c • (LinearMap.id : Module.End D (CutSpectInput Q Λ θ β E N)) :=
      LinearMap.ext fun n => by
        change (ι 1 (algebraMap k E c)) • (show N from n) =
          c • (show N from n)
        rw [Algebra.algebraMap_eq_smul_one, cutSpectTmul_smul_right, smul_assoc]
        rw [cutSpectTmul_one, one_smul]
    rw [h, cutStandardMap_smul_id]

theorem cutSpectAction_apply (e : E) (z : CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E N)) :
    cutSpectAction Q Λ θ β E N e z = cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E N e) z :=
  rfl

variable (hQ : KLRSymm Q)

/-- The action of the spectator commutes with the action of `T^λ(θ + β)`. -/
theorem commute_cutSpectAction (e : E) (t : T) :
    Commute (cutSpectAction Q Λ θ β E N e)
      (cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E N) hQ t) :=
  LinearMap.ext fun z => cutStandardMap_action Q Λ θ β hQ (cutSpectEnd Q Λ θ β E N e) t z

/-- The action of `T^λ(θ + β) ⊗ E` on the partial standardization. -/
def cutSpectStandardAction :
    TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E →ₐ[k]
      Module.End k (CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E N)) :=
  Algebra.TensorProduct.lift (cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E N) hQ)
    (cutSpectAction Q Λ θ β E N) fun t e => (commute_cutSpectAction Q Λ θ β E N hQ e t).symm

theorem cutSpectStandardAction_tmul (t : T) (e : E)
    (z : CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E N)) :
    cutSpectStandardAction Q Λ θ β E N hQ (t ⊗ₜ[k] e) z =
      cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E N) hQ t
        (cutSpectAction Q Λ θ β E N e z) :=
  rfl

/-- **The partial standardization at a cut with a spectator** `E`, a module over
`T^λ(θ + β) ⊗ E`. -/
@[nolint unusedArguments]
def CutSpectStandard (_hQ : KLRSymm Q) : Type _ :=
  CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E N)

instance : AddCommGroup (CutSpectStandard Q Λ θ β E N hQ) :=
  inferInstanceAs (AddCommGroup (CutStandard Q Λ θ β _))
instance : Module k (CutSpectStandard Q Λ θ β E N hQ) :=
  inferInstanceAs (Module k (CutStandard Q Λ θ β _))
instance : Module (TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E) (CutSpectStandard Q Λ θ β E N hQ) :=
  Module.compHom (CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E N))
    (cutSpectStandardAction Q Λ θ β E N hQ).toRingHom

theorem cutSpectStandard_smul (d : T ⊗[k] E) (z : CutSpectStandard Q Λ θ β E N hQ) :
    d • z = cutSpectStandardAction Q Λ θ β E N hQ d z := rfl

instance : IsScalarTower k (TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E)
    (CutSpectStandard Q Λ θ β E N hQ) where
  smul_assoc c d z := by
    rw [cutSpectStandard_smul, cutSpectStandard_smul, map_smul]
    rfl

/-! ### Maps -/

variable {E} {N}
variable {N' N'' : Type*}
  [AddCommGroup N'] [Module k N'] [Module (cutSpectAlgebra Q Λ θ β E) N']
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N']
  [AddCommGroup N''] [Module k N''] [Module (cutSpectAlgebra Q Λ θ β E) N'']
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N'']

/-- A map of modules over `D ⊗ E`, as a map of modules over `D`. -/
def cutSpectInputHom (g : N →ₗ[DE] N') :
    CutSpectInput Q Λ θ β E N →ₗ[D] CutSpectInput Q Λ θ β E N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' d n := g.map_smul (ι d 1) n

omit [Module k N] [Module k N'] [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β E) N'] in
theorem cutSpectInputHom_spectEnd (g : N →ₗ[DE] N') (e : E)
    (n : CutSpectInput Q Λ θ β E N) :
    cutSpectInputHom Q Λ θ β g (cutSpectEnd Q Λ θ β E N e n) =
      cutSpectEnd Q Λ θ β E N' e (cutSpectInputHom Q Λ θ β g n) :=
  g.map_smul _ (show N from n)

/-- **The partial standardization with a spectator of a map** of modules over `D ⊗ E`, linear
over `T^λ(θ + β) ⊗ E`. -/
def cutSpectStandardMap (g : N →ₗ[DE] N') :
    CutSpectStandard Q Λ θ β E N hQ →ₗ[T ⊗[k] E] CutSpectStandard Q Λ θ β E N' hQ where
  toFun := cutStandardMap Q Λ θ β (cutSpectInputHom Q Λ θ β g)
  map_add' := map_add _
  map_smul' d z := by
    change cutStandardMap Q Λ θ β (cutSpectInputHom Q Λ θ β g)
        (cutSpectStandardAction Q Λ θ β E N hQ d z) =
      cutSpectStandardAction Q Λ θ β E N' hQ d
        (cutStandardMap Q Λ θ β (cutSpectInputHom Q Λ θ β g) z)
    induction d using TensorProduct.inductionOn generalizing z with
    | tmul t e =>
      change cutStandardMap Q Λ θ β (cutSpectInputHom Q Λ θ β g)
          (cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E N) hQ t
            (cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E N e) z)) =
        cutStandardAction Q Λ θ β (CutSpectInput Q Λ θ β E N') hQ t
          (cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E N' e)
            (cutStandardMap Q Λ θ β (cutSpectInputHom Q Λ θ β g) z))
      rw [cutStandardMap_action]
      exact congrArg _ (cutStandardMap_comm Q Λ θ β _ _ _
        (cutSpectInputHom_spectEnd Q Λ θ β g e) z)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact (congrArg _ (LinearMap.add_apply _ _ z)).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) (hx z) (hy z)).trans (LinearMap.add_apply _ _ _).symm))

theorem cutSpectStandardMap_apply (g : N →ₗ[DE] N') (z : CutSpectStandard Q Λ θ β E N hQ) :
    cutSpectStandardMap Q Λ θ β hQ g z = cutStandardMap Q Λ θ β (cutSpectInputHom Q Λ θ β g) z :=
  rfl

/-- **Partial standardization with a spectator is exact.** -/
theorem cutSpectStandardMap_exact (f : N →ₗ[DE] N') (g : N' →ₗ[DE] N'')
    (h : Function.Exact f g) :
    Function.Exact (cutSpectStandardMap Q Λ θ β hQ f) (cutSpectStandardMap Q Λ θ β hQ g) :=
  cutStandardMap_exact Q Λ θ β hQ (cutSpectInputHom Q Λ θ β f) (cutSpectInputHom Q Λ θ β g) h

/-- Partial standardization with a spectator preserves injections. -/
theorem cutSpectStandardMap_injective (f : N →ₗ[DE] N') (hf : Function.Injective f) :
    Function.Injective (cutSpectStandardMap Q Λ θ β hQ f) :=
  cutStandardMap_injective Q Λ θ β hQ (cutSpectInputHom Q Λ θ β f) hf

/-- Partial standardization with a spectator preserves surjections. -/
theorem cutSpectStandardMap_surjective (f : N →ₗ[DE] N') (hf : Function.Surjective f) :
    Function.Surjective (cutSpectStandardMap Q Λ θ β hQ f) :=
  cutStandardMap_surjective Q Λ θ β hQ (cutSpectInputHom Q Λ θ β f) hf

end Categorification.Stendhal
