/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons
import Categorification.WeightedKLR.RedStrands.PartialStandardizationDerived
import Categorification.Algebra.TensorRepresentedFunctor

/-!
# Partial standardization at a cut is tensoring with a bimodule

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1: the
partial standardization at a cut with a spectator `E` (`cutSpectFunctor`) is induction
followed by the quotient by the loadings whose red strands are out of order. Both steps are
compatible with tensor products, so the functor is tensoring with its value on the regular
module: `𝕊(Z) ≅ 𝕊(D ⊗ E) ⊗_{D ⊗ E} Z` naturally in `Z`
(`isTensorRepresented_cutSpectFunctor`).

The inverse of the Eilenberg–Watts map sends the class of `m ⊗ n` to `[m ⊗ 1] ⊗ n`; it
descends to the quotient since the class of `y` equals that of `P y`, `P` the idempotent of
the ordered loadings.

## Main results

* `Stendhal.isTensorRepresented_cutSpectFunctor`: it is represented by tensoring.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory DG KLR KLRAlgebra TypeA MulOpposite TensorRepresented
open scoped TensorProduct

section Idempotent

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- The class of `y` in the partial standardization is that of `P y`, for `P` the idempotent
of the loadings with the red strands in order. -/
theorem cutStandard_mk_eSum_smul (y : CutShuffle Q Λ θ β N) :
    (Submodule.Quotient.mk
        ((eSum (stendhalQ Q Λ) (cutOrderedLoadings (a := a) (r := r) θ β) :
          KLRAlgebra k (stendhalQ Q Λ) _) • y) : CutStandard Q Λ θ β N) =
      Submodule.Quotient.mk y := by
  refine (Submodule.Quotient.eq _).2 ?_
  change (eSum (stendhalQ Q Λ) (cutOrderedLoadings (a := a) (r := r) θ β) :
      KLRAlgebra k (stendhalQ Q Λ) _) • (_ - y) = 0
  rw [smul_sub, smul_smul, (eSum_idem _).eq, sub_self]

end Idempotent

variable {I k : Type u} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ)
  (θ β : Multiset I) (E : AlgCat.{u} k) (hQ : KLRSymm Q)

/-- The regular module of a ring. -/
abbrev regularModule (R : Type u) [Ring R] : ModuleCat.{u} R := ModuleCat.of R R

/-- The regular module of `D ⊗ E`, as an object whose `k`-structure is the one of a module
over a `k`-algebra. -/
def cutSpectRegular : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E) :=
  regularModule (cutSpectAlgebra Q Λ θ β E)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

local notation "DE" => cutSpectAlgebra Q Λ θ β E
local notation "TE" => TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E
local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "𝔽" => cutSpectFunctor Q Λ θ β E hQ
local notation "X" => cutSpectRegular Q Λ θ β E

/-- The unit of `D ⊗ E`, as an element of the input of the induction. -/
def cutSpectOne : CutInput Q Λ θ β (CutSpectInput Q Λ θ β E X) := (1 : DE)

/-- An element `d ∈ D ⊗ E`, as an element of the input of the induction. -/
def cutSpectElt (d : DE) : CutInput Q Λ θ β (CutSpectInput Q Λ θ β E X) := d

/-- The class in `𝕊(D ⊗ E)` of an element of the induced module. -/
def cutSpectClass (y : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E X)) : Bimod 𝔽 :=
  (Submodule.Quotient.mk y : CutSpectStandard Q Λ θ β E X hQ)

/-- The generator `[m ⊗ 1]` of `𝕊(D ⊗ E)`. -/
def cutSpectGen (m : IndBimod S α δ) : Bimod 𝔽 :=
  cutSpectClass Q Λ θ β E hQ (BalancedTensor.tmul m (cutSpectOne Q Λ θ β E))

theorem cutSpectGen_op_smul (m : IndBimod S α δ) (d : DE) :
    op d • cutSpectGen Q Λ θ β E hQ m =
      cutSpectClass Q Λ θ β E hQ (BalancedTensor.tmul m (cutSpectElt Q Λ θ β E d)) :=
  Eq.trans rfl (congrArg (fun x => cutSpectClass Q Λ θ β E hQ
    (BalancedTensor.tmul m (cutSpectElt Q Λ θ β E x))) (one_mul d))

local notation "P" => (eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ))

theorem cutSpectClass_add (y y' : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E X)) :
    cutSpectClass Q Λ θ β E hQ (y + y') =
      cutSpectClass Q Λ θ β E hQ y + cutSpectClass Q Λ θ β E hQ y' :=
  Submodule.Quotient.mk_add _

theorem cutSpectClass_smul (c : k) (y : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E X)) :
    cutSpectClass Q Λ θ β E hQ (c • y) = algebraMap k TE c • cutSpectClass Q Λ θ β E hQ y := by
  change (Submodule.Quotient.mk (c • y) : CutSpectStandard Q Λ θ β E X hQ) =
    cutSpectStandardAction Q Λ θ β E X hQ (algebraMap k _ c) (Submodule.Quotient.mk y)
  rw [AlgHom.commutes, Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]

theorem cutSpectClass_eSum (y : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E X)) :
    cutSpectClass Q Λ θ β E hQ (P • y) = cutSpectClass Q Λ θ β E hQ y :=
  cutStandard_mk_eSum_smul Q Λ θ β _ y

theorem cutSpectGen_add (m m' : IndBimod S α δ) :
    cutSpectGen Q Λ θ β E hQ (m + m') =
      cutSpectGen Q Λ θ β E hQ m + cutSpectGen Q Λ θ β E hQ m' := by
  rw [cutSpectGen, BalancedTensor.add_tmul, cutSpectClass_add]; rfl

theorem cutSpectGen_smul (c : k) (m : IndBimod S α δ) :
    cutSpectGen Q Λ θ β E hQ (c • m) = algebraMap k TE c • cutSpectGen Q Λ θ β E hQ m := by
  rw [cutSpectGen, BalancedTensor.smul_tmul, cutSpectClass_smul]; rfl

theorem cutSpectGen_eSum (m : IndBimod S α δ) :
    cutSpectGen Q Λ θ β E hQ (P • m) = cutSpectGen Q Λ θ β E hQ m := by
  rw [cutSpectGen, ← BalancedTensor.smul_tmul', cutSpectClass_eSum]; rfl

/-- The scalars of `k` act on `𝕊(D ⊗ E)` in the same way from both sides. -/
theorem cutSpectGen_op_algebraMap (c : k) (m : IndBimod S α δ) :
    op (algebraMap k DE c) • cutSpectGen Q Λ θ β E hQ m =
      algebraMap k TE c • cutSpectGen Q Λ θ β E hQ m := by
  rw [cutSpectGen_op_smul, ← cutSpectGen_smul, cutSpectGen, BalancedTensor.smul_tmul,
    ← BalancedTensor.tmul_smul]
  exact congrArg (fun x => cutSpectClass Q Λ θ β E hQ
    (BalancedTensor.tmul m (cutSpectElt Q Λ θ β E x))) (mul_one _).symm

/-- The right action of the affine algebra of the two blocks on the generators. -/
theorem cutSpectGen_balanced (m : IndBimod S α δ) (b : TensorKLR S α δ) :
    cutSpectGen Q Λ θ β E hQ (op b • m) =
      op (cutSpectTmul Q Λ θ β E (cutInputMap Q Λ θ β b) 1) • cutSpectGen Q Λ θ β E hQ m := by
  rw [cutSpectGen, BalancedTensor.op_smul_tmul, cutSpectGen_op_smul]
  exact congrArg (fun x => cutSpectClass Q Λ θ β E hQ
    (BalancedTensor.tmul m (cutSpectElt Q Λ θ β E x))) (mul_one _)

/-! ### The inverse of the Eilenberg–Watts map -/

variable (Z : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E))

/-- The `k`-structure of `𝕊(D ⊗ E) ⊗_{D ⊗ E} Z`, through the left action of `T^λ ⊗ E`. -/
abbrev cutSpectTensorScalars : Module k (TensorProductOver DE (Bimod 𝔽) Z) :=
  Module.compHom _ (algebraMap k TE)

attribute [local instance] cutSpectTensorScalars

/-- The bilinear map `(m, n) ↦ [m ⊗ 1] ⊗ n`. -/
def cutSpectInvBil : IndBimod S α δ →ₗ[k] CutInput Q Λ θ β (CutSpectInput Q Λ θ β E Z) →ₗ[k]
    TensorProductOver DE (Bimod 𝔽) Z :=
  LinearMap.mk₂ k (fun m n => TensorProductOver.tmul DE (cutSpectGen Q Λ θ β E hQ m)
      (show Z from n))
    (fun m m' n => by rw [cutSpectGen_add, TensorProductOver.add_tmul])
    (fun c m n => by rw [cutSpectGen_smul]; rfl)
    (fun m n n' => TensorProductOver.tmul_add (A := DE) _ (show Z from n) (show Z from n'))
    (fun c m n => by
      change TensorProductOver.tmul DE _ (algebraMap k DE c • (show Z from n)) = _
      rw [← TensorProductOver.op_smul_tmul, cutSpectGen_op_algebraMap]; rfl)

theorem cutSpectInvBil_balanced (m : IndBimod S α δ) (b : TensorKLR S α δ)
    (n : CutInput Q Λ θ β (CutSpectInput Q Λ θ β E Z)) :
    cutSpectInvBil Q Λ θ β E hQ Z (op b • m) n = cutSpectInvBil Q Λ θ β E hQ Z m (b • n) := by
  change TensorProductOver.tmul DE (cutSpectGen Q Λ θ β E hQ (op b • m)) (show Z from n) =
    TensorProductOver.tmul DE (cutSpectGen Q Λ θ β E hQ m)
      (cutSpectTmul Q Λ θ β E (cutInputMap Q Λ θ β b) 1 • (show Z from n))
  rw [cutSpectGen_balanced, TensorProductOver.op_smul_tmul]

/-- The inverse of the Eilenberg–Watts map on the induced module: `m ⊗ n ↦ [m ⊗ 1] ⊗ n`. -/
def cutSpectInv : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E Z) →ₗ[k]
    TensorProductOver DE (Bimod 𝔽) Z :=
  BalancedTensor.lift (cutSpectInvBil Q Λ θ β E hQ Z) (cutSpectInvBil_balanced Q Λ θ β E hQ Z)

theorem cutSpectInv_eSum (y : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E Z)) :
    cutSpectInv Q Λ θ β E hQ Z (P • y) = cutSpectInv Q Λ θ β E hQ Z y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [smul_zero]
  | tmul m n =>
    rw [BalancedTensor.smul_tmul']
    change TensorProductOver.tmul DE (cutSpectGen Q Λ θ β E hQ (P • m)) (show Z from n) = _
    rw [cutSpectGen_eSum]; rfl
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy']

/-- The map `d ↦ d z` out of the regular module. -/
def cutSpectRmul (z : Z) : X ⟶ Z := rmul Z z

theorem ewMap_cutSpectInv (y : CutShuffle Q Λ θ β (CutSpectInput Q Λ θ β E Z)) :
    ewMap 𝔽 Z (cutSpectInv Q Λ θ β E hQ Z y) =
      (Submodule.Quotient.mk y : CutSpectStandard Q Λ θ β E Z hQ) := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]; exact (Submodule.Quotient.mk_zero _).symm
  | tmul m n =>
    exact Eq.trans rfl (congrArg (fun x : Z => (Submodule.Quotient.mk (BalancedTensor.tmul m
      (show CutInput Q Λ θ β (CutSpectInput Q Λ θ β E Z) from x)) :
        CutSpectStandard Q Λ θ β E Z hQ)) (one_smul DE (show Z from n)))
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy']
    exact (Submodule.Quotient.mk_add _).symm

/-- Every tensor has a representative in the induced module on which the inverse map takes the
value of the tensor. -/
theorem cutSpect_exists_rep (t : TensorProductOver DE (Bimod 𝔽) Z) :
    ∃ y, (Submodule.Quotient.mk y : CutSpectStandard Q Λ θ β E Z hQ) = ewMap 𝔽 Z t ∧
      cutSpectInv Q Λ θ β E hQ Z y = t := by
  induction t using TensorProductOver.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; exact Submodule.Quotient.mk_zero _, map_zero _⟩
  | tmul p z =>
    have hp : ∃ y₁, cutSpectClass Q Λ θ β E hQ y₁ = p :=
      Submodule.Quotient.mk_surjective _ (show CutSpectStandard Q Λ θ β E X hQ from p)
    obtain ⟨y₁, rfl⟩ := hp
    refine ⟨cutShuffleMap Q Λ θ β (cutSpectInputHom Q Λ θ β (cutSpectRmul Q Λ θ β E Z z).hom) y₁,
      rfl, ?_⟩
    induction y₁ using BalancedTensor.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact (TensorProductOver.zero_tmul (A := DE) (M := Bimod 𝔽) z).symm
    | tmul m d =>
      change TensorProductOver.tmul DE (cutSpectGen Q Λ θ β E hQ m) ((show DE from d) • z) =
        TensorProductOver.tmul DE
          (cutSpectClass Q Λ θ β E hQ (BalancedTensor.tmul m (cutSpectElt Q Λ θ β E d))) z
      rw [← TensorProductOver.op_smul_tmul, cutSpectGen_op_smul]
    | add y y' hy hy' =>
      rw [map_add, map_add, hy, hy']
      exact (TensorProductOver.add_tmul (A := DE) _ _ z).symm
  | add t t' ht ht' =>
    obtain ⟨y, hy, hy'⟩ := ht
    obtain ⟨y', hz, hz'⟩ := ht'
    exact ⟨y + y', by rw [Submodule.Quotient.mk_add, hy, hz, map_add]; rfl,
      by rw [map_add, hy', hz']⟩

/-- **Partial standardization at a cut is tensoring with a bimodule**: the partial
standardization with a spectator `E` is represented by tensoring with its value
`𝕊(D ⊗ E)` on the regular module (Webster, arXiv:1309.3796v3, §5.1). -/
theorem isTensorRepresented_cutSpectFunctor : IsTensorRepresented 𝔽 := by
  intro Z
  refine ⟨fun t t' h => ?_, fun v => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := cutSpect_exists_rep Q Λ θ β E hQ Z t
    obtain ⟨y', hy', rfl⟩ := cutSpect_exists_rep Q Λ θ β E hQ Z t'
    have hyy : P • (y - y') = 0 := (Submodule.Quotient.eq _).1 (hy.trans (h.trans hy'.symm))
    rw [← sub_eq_zero, ← map_sub, ← cutSpectInv_eSum, hyy, map_zero]
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨_, ewMap_cutSpectInv Q Λ θ β E hQ Z y⟩

end Categorification.Stendhal
