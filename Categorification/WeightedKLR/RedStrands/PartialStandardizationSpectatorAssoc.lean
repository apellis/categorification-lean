/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocOrdersMap
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons

/-!
# One-step associativity of the partial standardizations with a spectator

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4, and §7.3 (proof of Lemma 7.19, where the
standardization is computed in stages). Let `N` be a module over
`T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ)) ⊗ E`, for three consecutive blocks of red strands, the last of
them a single red strand, and a spectator algebra `E`. Standardizing first at the cut between
the first two blocks, with `T^R(γ)` moved into the spectator, and then at the cut before the
last red strand (`spectAssocLeft`) gives the same module, along the weight associator
`T^λ((θ + β) + γ) ≅ T^λ(θ + (β + γ))`, as standardizing first at the cut between the last two
blocks, with `T^A(θ)` moved into the spectator, and then at the first cut (`spectAssocRight`)
(`spectAssocIso`). This is `blocksStandardAssocEquiv` with the spectator carried along: each
side is identified with an iteration of partial standardization with three blocks by the
partial standardization of carrier identities (`spectLeftMidEquiv`, `spectRightMidEquiv`), the
weights by `blocksStandardAssocEquiv_action_one`, and the spectator by the naturality
`blocksStandardAssocEquiv_map` applied to the action of `E` (`spectBlocksEnd`).

## Main definitions

* `Stendhal.cutStandardMapEquiv`: the partial standardization of an isomorphism.
* `Stendhal.blocksSpectAlgebra`: the algebra of three blocks and a spectator.
* `Stendhal.spectAssocLeft`, `Stendhal.spectAssocRight`: the two iterations.
* `Stendhal.spectAssocIso`: the one-step associativity isomorphism.

## Main results

* `Stendhal.blocksStandardAssocEquiv_action_one`: the two orders of the cuts intertwine the
  actions of all strands, when the last block is a single red strand.
* `Stendhal.spectAssocAddEquiv_smul`: the one-step associativity intertwines the actions.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-- **A relabelling along the transport of sequences is the identification of KLR algebras**:
a relabelling of the sequences of a weight `μ` to an equal weight `μ'` that acts on sequences as
their transport gives the cast `KLRAlgebra P μ ≃ KLRAlgebra P μ'`. -/
theorem relabelEquiv_eq_castKLR {J k : Type*} [DecidableEq J] [CommRing k]
    {P : J → J → MvPolynomial (Fin 2) k} {μ μ' : Multiset J} (R : SeqRelabel k P P μ μ')
    (h : μ = μ') (hR : ∀ s, R.equiv s = Seq.cast h s) (u : KLRAlgebra k P μ) :
    relabelEquiv R u = castKLR P h u := by
  subst h
  have : relabelHom R = AlgHom.id k (KLRAlgebra k P μ) := by
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext g
    cases g with
    | idem i =>
      change relabelHom R (e i) = e i
      rw [relabelHom_e, hR, Seq.cast_rfl]
    | dot a =>
      change relabelHom R (x a) = x a
      rw [relabelHom_x]
      rfl
    | cross j =>
      change relabelHom R (ψ j) = ψ j
      rw [relabelHom_ψ]
  exact (congrArg (fun f => f u) this : _)

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section One

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + 1)) → I →₀ ℕ) (θ β γ : Multiset I)

local notation "ΛL" => Λ ∘ Fin.cast (Nat.add_assoc a m 1)
local notation "S" => stendhalQ Q Λ

omit [DecidableEq I] in
/-- With a last block of one red strand, the relabelling of the red strands along the
associativity of `(a + m) + 1 = a + (m + 1)` is the identity on weights. -/
theorem sumMap_cast_self (μ : Multiset (I ⊕ Fin ((a + m) + 1))) :
    μ.map (Sum.map (id : I → I) (Fin.cast (Nat.add_assoc a m 1))) = μ := by
  conv_rhs => rw [← Multiset.map_id μ]
  congr 1
  funext y
  cases y <;> rfl

/-- With a last block of one red strand, the relabelling `blocksAssocKLR` of the affine KLR
algebras along the two nestings is a cast of weights. -/
theorem blocksAssocKLR_one
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ Fin.cast (Nat.add_assoc a m 1)))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd m)) (stendhalWeight a θ)) +
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight m β)) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd (a + m))) (stendhalWeight 1 γ)))) :
    blocksAssocKLR (a := a) (m := m) (r := 1) Q Λ θ β γ z =
      castKLR S ((sumMap_cast_self _).symm.trans
        (blocksAssocWeight (a := a) (m := m) (r := 1) θ β γ)) z := by
  change castKLR S _ (relabelEquiv (stendhalRelabel Q Λ _ _ _) z) = _
  refine (congrArg (castKLR S _) (relabelEquiv_eq_castKLR (P := S) (stendhalRelabel Q Λ
    (Fin.cast (Nat.add_assoc a m 1)) (Fin.cast_injective _) _) (sumMap_cast_self _).symm
    (fun s => ?_) z)).trans (castKLR_castKLR _ _ z)
  apply Subtype.ext
  funext p
  change Sum.map (id : I → I) (Fin.cast (Nat.add_assoc a m 1)) (s.1 _) = s.1 _
  cases s.1 _ <;> rfl

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ) N] (hQ : KLRSymm Q)

/-- **The two iterations of partial standardization with three blocks, the last of one red
strand, intertwine the actions of all strands**, along the identification
`T^λ((θ + β) + γ) ≃ T^λ(θ + (β + γ))` of the weights. -/
theorem blocksStandardAssocEquiv_action_one
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) ((θ + β) + γ))
    (x : BlocksStandardL Q (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) θ β γ
      (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ N) hQ) :
    blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ N hQ
        (blocksStandardActionL Q (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) θ β γ _ hQ t x) =
      blocksStandardAction (a := a) (m := m) (r := 1) Q Λ θ β γ N hQ
        (castTensorProductAlgebra Q Λ (add_assoc θ β γ) t)
        (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ N hQ x) := by
  obtain ⟨zL, rfl⟩ := cutStandardAffine_surjective (a := a + m) (r := 1) Q
    (Λ ∘ Fin.cast (Nat.add_assoc a m 1)) (θ + β) γ t
  have H := (blocksWeightL_add_eq (a := a) (m := m) (r := 1) θ β γ).trans
    (((sumMap_cast_self _).symm.trans (blocksAssocWeight (a := a) (m := m) (r := 1) θ β γ)).trans
      (add_eq_add_of_eq rfl (blocksWeight_eq (a := a) (m := m) (r := 1) β γ)).symm)
  refine (blocksStandardAssocEquiv_action Q Λ θ β γ N hQ zL (castKLR S H zL) ?_ x).trans ?_
  · rw [blocksAssocKLR_one]
    exact (castKLR_castKLR (P := S) _ _ zL).trans (castKLR_castKLR (P := S) _ _ zL).symm
  · refine congrArg (fun u => blocksStandardAction (a := a) (m := m) (r := 1) Q Λ θ β γ N hQ u
      (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ N hQ x)) ?_
    refine Eq.trans ?_ (castTensorProductAlgebra_mk Q Λ (add_assoc θ β γ) _).symm
    exact congrArg (tensorOfKLR Q Λ _)
      ((castKLR_castKLR (P := S) _ _ zL).trans (castKLR_castKLR (P := S) _ _ zL).symm)

end One

end Categorification.Stendhal

universe u

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

section MapEquiv

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  {N N' : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (cutFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N']

/-- **The partial standardization of an isomorphism** of modules over the factor algebras. -/
def cutStandardMapEquiv (g : N ≃ₗ[cutFactorAlgebra Q Λ θ β] N') :
    CutStandard Q Λ θ β N ≃ₗ[k] CutStandard Q Λ θ β N' where
  __ := cutStandardMap Q Λ θ β g.toLinearMap
  invFun := cutStandardMap Q Λ θ β g.symm.toLinearMap
  left_inv z := by
    refine (cutStandardMap_comp Q Λ θ β _ _ z).symm.trans ?_
    refine Eq.trans ?_ (LinearMap.congr_fun (cutStandardMap_id Q Λ θ β) z)
    exact congrArg (fun f => cutStandardMap Q Λ θ β f z) (LinearMap.ext g.symm_apply_apply)
  right_inv z := by
    refine (cutStandardMap_comp Q Λ θ β _ _ z).symm.trans ?_
    refine Eq.trans ?_ (LinearMap.congr_fun (cutStandardMap_id Q Λ θ β) z)
    exact congrArg (fun f => cutStandardMap Q Λ θ β f z) (LinearMap.ext g.apply_symm_apply)

theorem cutStandardMapEquiv_apply (g : N ≃ₗ[cutFactorAlgebra Q Λ θ β] N')
    (z : CutStandard Q Λ θ β N) :
    cutStandardMapEquiv Q Λ θ β g z = cutStandardMap Q Λ θ β g.toLinearMap z := rfl

theorem cutStandardMapEquiv_symm_apply (g : N ≃ₗ[cutFactorAlgebra Q Λ θ β] N')
    (z : CutStandard Q Λ θ β N') :
    (cutStandardMapEquiv Q Λ θ β g).symm z = cutStandardMap Q Λ θ β g.symm.toLinearMap z := rfl

end MapEquiv

section Spect

variable {I k : Type u} [DecidableEq I] [CommRing k] {a m : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + 1)) → I →₀ ℕ) (θ β γ : Multiset I)
  (E : AlgCat.{u} k)

/-- **The algebra of three blocks** `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`, as a type with its ring
structure (so that its tensor products elaborate). -/
def blocksTotalAlgebra : Type u := blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ

instance : Ring (blocksTotalAlgebra Q Λ θ β γ) :=
  inferInstanceAs (Ring (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ))
instance : Algebra k (blocksTotalAlgebra Q Λ θ β γ) :=
  inferInstanceAs (Algebra k (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ))

/-- **The algebra of three blocks and a spectator**, `(T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))) ⊗ E`. -/
def blocksSpectAlgebra : Type u := blocksTotalAlgebra Q Λ θ β γ ⊗[k] E

instance : Ring (blocksSpectAlgebra Q Λ θ β γ E) := Algebra.TensorProduct.instRing
instance : Algebra k (blocksSpectAlgebra Q Λ θ β γ E) := Algebra.TensorProduct.instAlgebra

/-- The inclusion `x ↦ x ⊗ 1` of the three blocks. -/
def blocksSpectIncl : blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ →ₐ[k]
    blocksSpectAlgebra Q Λ θ β γ E :=
  (Algebra.TensorProduct.includeLeft : blocksTotalAlgebra Q Λ θ β γ →ₐ[k] _ ⊗[k] E)

/-- The labels of the red strands, for the nesting with the first cut first. -/
local notation "ΛL" => Λ ∘ Fin.cast (Nat.add_assoc a m 1)
/-- The labels of the first two blocks. -/
local notation "ΛA" => blocksLeftLabels (a := a) (m := m) (r := 1) ΛL
/-- The last block `T^R(γ)`, labelled by the last red strand. -/
local notation "Lst" => blocksLastAlgebra (a := a) (m := m) (r := 1) Q ΛL γ
/-- The first block `T^A(θ)`. -/
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (m + 1)) θ

/-- The algebra map `(T^A ⊗ T^M) ⊗ (T^R ⊗ E) → (T^A ⊗ (T^M ⊗ T^R)) ⊗ E` along which a module
over the three blocks and `E` is a module for the first cut with the last block in the
spectator. -/
def spectAssocLeftAlg :
    cutSpectAlgebra (a := a) (r := m) Q (ΛA) θ β
        (AlgCat.of k (Lst ⊗[k] E) : AlgCat.{u} k) →ₐ[k]
      blocksSpectAlgebra Q Λ θ β γ E :=
  (Algebra.TensorProduct.map
      ((blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ).toAlgHom :
        _ →ₐ[k] blocksTotalAlgebra Q Λ θ β γ)
      (AlgHom.id k E)).comp
    (Algebra.TensorProduct.assoc k k k (cutFactorAlgebra Q (ΛA) θ β) Lst
      E).symm.toAlgHom

/-- The algebra map `(T^M ⊗ T^R) ⊗ (T^A ⊗ E) → (T^A ⊗ (T^M ⊗ T^R)) ⊗ E` along which a module
over the three blocks and `E` is a module for the second cut with the first block in the
spectator. -/
def spectAssocRightAlg :
    cutSpectAlgebra (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ
        (AlgCat.of k (Hd ⊗[k] E) : AlgCat.{u} k) →ₐ[k]
      blocksSpectAlgebra Q Λ θ β γ E :=
  (Algebra.TensorProduct.map
      ((Algebra.TensorProduct.comm k (cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ) Hd).toAlgHom :
        _ →ₐ[k] blocksTotalAlgebra Q Λ θ β γ)
      (AlgHom.id k E)).comp
    (Algebra.TensorProduct.assoc k k k
      (cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ) Hd E).symm.toAlgHom

/-- The algebra map `(T^A ⊗ T^{MR}) ⊗ E → T^{MR} ⊗ (T^A ⊗ E)` moving the first block into the
spectator. -/
def spectHeadAlg :
    cutSpectAlgebra (a := a) (r := m + 1) Q Λ θ (β + γ) E →ₐ[k]
      TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) (β + γ) ⊗[k]
        (AlgCat.of k (Hd ⊗[k] E) : AlgCat.{u} k) :=
  (Algebra.TensorProduct.assoc k k k _ Hd E).toAlgHom.comp
    (Algebra.TensorProduct.map (Algebra.TensorProduct.comm k Hd _).toAlgHom (AlgHom.id k E))

/-- The associator `(T^{AM} ⊗ T^R) ⊗ E → T^{AM} ⊗ (T^R ⊗ E)`. -/
def spectLastAlg :
    cutSpectAlgebra (a := a + m) (r := 1) Q ΛL (θ + β) γ E →ₐ[k]
      TensorProductAlgebra k Q (ΛA) (θ + β) ⊗[k]
        (AlgCat.of k (Lst ⊗[k] E) : AlgCat.{u} k) :=
  (Algebra.TensorProduct.assoc k k k _ Lst E).toAlgHom

variable (hQ : KLRSymm Q) (N : ModuleCat.{u} (blocksSpectAlgebra Q Λ θ β γ E))

/-- A module over the three blocks and `E`, for the first cut with the last block in the
spectator. -/
abbrev spectLeftInput :
    ModuleCat.{u} (cutSpectAlgebra (a := a) (r := m) Q (ΛA) θ β
      (AlgCat.of k (Lst ⊗[k] E) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (spectAssocLeftAlg Q Λ θ β γ E).toRingHom).obj N

/-- A module over the three blocks and `E`, for the second cut with the first block in the
spectator. -/
abbrev spectRightInput :
    ModuleCat.{u} (cutSpectAlgebra (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ
      (AlgCat.of k (Hd ⊗[k] E) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ β γ E).toRingHom).obj N

/-- **The left side of the one-step associativity**: standardize at the first cut, with the
last block in the spectator, then at the second cut. -/
abbrev spectAssocLeft : ModuleCat.{u} (TensorProductAlgebra k Q ΛL ((θ + β) + γ) ⊗[k] E) :=
  (cutSpectFunctor (a := a + m) (r := 1) Q ΛL (θ + β) γ E hQ).obj
    ((ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ β γ E).toRingHom).obj
      ((cutSpectFunctor (a := a) (r := m) Q (ΛA) θ β
          (AlgCat.of k (Lst ⊗[k] E)) hQ).obj
        (spectLeftInput Q Λ θ β γ E N)))

/-- **The right side of the one-step associativity**: standardize at the second cut, with the
first block in the spectator, then at the first cut. -/
abbrev spectAssocRight : ModuleCat.{u} (TensorProductAlgebra k Q Λ (θ + (β + γ)) ⊗[k] E) :=
  (cutSpectFunctor (a := a) (r := m + 1) Q Λ θ (β + γ) E hQ).obj
    ((ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ β γ E).toRingHom).obj
      ((cutSpectFunctor (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ
          (AlgCat.of k (Hd ⊗[k] E)) hQ).obj
        (spectRightInput Q Λ θ β γ E N)))

/-- The semiring structure of the algebra of three blocks, through its ring structure (so that
linear maps over it elaborate). -/
private abbrev blocksNonAssocSemiringE :
    NonAssocSemiring (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] blocksNonAssocSemiringE

/-- The module over the three blocks underlying a module over the three blocks and `E`. -/
@[nolint unusedArguments]
def SpectBlocks (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (a + (m + 1)) → I →₀ ℕ)
    (_θ _β _γ : Multiset I) (_E : AlgCat.{u} k) (N : Type u) : Type u := N

instance : AddCommGroup (SpectBlocks Q Λ θ β γ E N) := inferInstanceAs (AddCommGroup N)
instance : Module k (SpectBlocks Q Λ θ β γ E N) := inferInstanceAs (Module k N)
instance : Module (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ)
    (SpectBlocks Q Λ θ β γ E N) :=
  Module.compHom N (blocksSpectIncl Q Λ θ β γ E).toRingHom

instance : IsScalarTower k (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ)
    (SpectBlocks Q Λ θ β γ E N) where
  smul_assoc c x n :=
    (congrArg (fun y : blocksSpectAlgebra Q Λ θ β γ E => y • (show N from n))
      ((blocksSpectIncl Q Λ θ β γ E).toLinearMap.map_smul c x)).trans
      (smul_assoc c (blocksSpectIncl Q Λ θ β γ E x) (show N from n))

/-- The first two blocks act through the first cut. -/
theorem spectAssocLeftAlg_factor (d : cutFactorAlgebra Q (ΛA) θ β) :
    spectAssocLeftAlg Q Λ θ β γ E (cutSpectTmul Q (ΛA) θ β _ d 1) =
      blocksSpectIncl Q Λ θ β γ E (blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ
        (d ⊗ₜ[k] (1 : Lst))) := rfl

/-- The last block acts, from the spectator, through the third block. -/
theorem spectAssocLeftAlg_last (l : Lst) :
    spectAssocLeftAlg Q Λ θ β γ E (cutSpectTmul Q (ΛA) θ β _ 1 (l ⊗ₜ[k] 1)) =
      blocksSpectIncl Q Λ θ β γ E (blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ
        ((1 : cutFactorAlgebra Q (ΛA) θ β) ⊗ₜ[k] l)) := rfl

/-- The spectator `E` acts through itself. -/
theorem spectAssocLeftAlg_spect (e : E) :
    spectAssocLeftAlg Q Λ θ β γ E (cutSpectTmul Q (ΛA) θ β _ 1 (1 ⊗ₜ[k] e)) =
      ((1 : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E) := by
  show ((blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ
      ((1 : cutFactorAlgebra Q (ΛA) θ β) ⊗ₜ[k] (1 : Lst)) : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e :
        blocksSpectAlgebra Q Λ θ β γ E) = _
  exact congrArg (fun x : blocksTotalAlgebra Q Λ θ β γ =>
    (x ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E))
    ((blocksAssocFactorEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ).toAlgHom.map_one)

/-- The last two blocks act through the second cut. -/
theorem spectAssocRightAlg_factor (d : cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ) :
    spectAssocRightAlg Q Λ θ β γ E (cutSpectTmul Q (Λ ∘ Fin.natAdd a) β γ _ d 1) =
      blocksSpectIncl Q Λ θ β γ E ((1 : Hd) ⊗ₜ[k] d) := rfl

/-- The first block acts, from the spectator, through the first block. -/
theorem spectAssocRightAlg_head (h : Hd) :
    spectAssocRightAlg Q Λ θ β γ E (cutSpectTmul Q (Λ ∘ Fin.natAdd a) β γ _ 1 (h ⊗ₜ[k] 1)) =
      blocksSpectIncl Q Λ θ β γ E
        (h ⊗ₜ[k] (1 : cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ)) := rfl

/-- The spectator `E` acts through itself. -/
theorem spectAssocRightAlg_spect (e : E) :
    spectAssocRightAlg Q Λ θ β γ E (cutSpectTmul Q (Λ ∘ Fin.natAdd a) β γ _ 1 (1 ⊗ₜ[k] e)) =
      ((1 : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E) := rfl

local notation "X" => spectLeftInput Q Λ θ β γ E N
local notation "X'" => spectRightInput Q Λ θ β γ E N
local notation "N₀" => SpectBlocks Q Λ θ β γ E N
/-- A module over the three blocks and `E`, at the first cut with the last block in the
spectator, is the module over the three blocks for the first cut. -/
def spectLeftInputEquiv :
    CutSpectInput Q (ΛA) θ β (AlgCat.of k (Lst ⊗[k] E)) X ≃ₗ[
      cutFactorAlgebra Q (ΛA) θ β]
      BlocksInnerL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ N₀) where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' d n := congrArg (fun x : blocksSpectAlgebra Q Λ θ β γ E => x • (show N from n))
    (spectAssocLeftAlg_factor Q Λ θ β γ E d)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A module over the three blocks and `E`, at the second cut with the first block in the
spectator, is the module over the three blocks for the second cut. -/
def spectRightInputEquiv :
    CutSpectInput Q (Λ ∘ Fin.natAdd a) β γ (AlgCat.of k (Hd ⊗[k] E)) X' ≃ₗ[
      cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ]
      BlocksInner (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' d n := congrArg (fun x : blocksSpectAlgebra Q Λ θ β γ E => x • (show N from n))
    (spectAssocRightAlg_factor Q Λ θ β γ E d)
  left_inv _ := rfl
  right_inv _ := rfl

variable {Q Λ θ β γ E} in
/-- The partial standardization at the first cut, as a module over the second cut. -/
abbrev spectLeftMid : ModuleCat.{u} (cutSpectAlgebra (a := a + m) (r := 1) Q ΛL (θ + β) γ E) :=
  (ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ β γ E).toRingHom).obj
    ((cutSpectFunctor (a := a) (r := m) Q (ΛA) θ β (AlgCat.of k (Lst ⊗[k] E)) hQ).obj X)

local notation "κL" => LinearEquiv.toLinearMap (spectLeftInputEquiv Q Λ θ β γ E N)

/-- `spectLeftMidEquiv` intertwines the actions of `t ⊗ l ∈ T^{AM}(θ + β) ⊗ T^R(γ)`. -/
theorem spectLeftMid_smul_tmul (t : TensorProductAlgebra k Q (ΛA) (θ + β)) (l : Lst)
    (y : CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N)) :
    cutStandardMap Q (ΛA) θ β κL ((t ⊗ₜ[k] l : cutFactorAlgebra Q ΛL (θ + β) γ) • y) =
      blocksMidActionL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ N₀) hQ (t ⊗ₜ[k] l)
        (cutStandardMap Q (ΛA) θ β κL y) := by
  change cutStandardMap Q (ΛA) θ β κL
      (cutStandardAction Q (ΛA) θ β _ hQ t (cutStandardMap Q (ΛA) θ β
        (cutSpectEnd Q (ΛA) θ β (AlgCat.of k (Lst ⊗[k] E)) X (l ⊗ₜ[k] 1)) y)) =
    cutStandardAction Q (ΛA) θ β _ hQ t (cutStandardMap Q (ΛA) θ β
      (blocksLastEnd (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ N₀) l)
      (cutStandardMap Q (ΛA) θ β κL y))
  refine (cutStandardMap_action Q (ΛA) θ β hQ κL t _).trans (congrArg _ ?_)
  refine (cutStandardMap_comp Q (ΛA) θ β _ _ y).symm.trans (Eq.trans ?_
    (cutStandardMap_comp Q (ΛA) θ β _ _ y))
  exact congrArg (fun g => cutStandardMap Q (ΛA) θ β g y) (LinearMap.ext fun _ => rfl)

local notation "MidL" => BlocksMidL (a := a) (m := m) (r := 1) Q ΛL θ β γ
  (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ N₀) hQ

/-- `spectLeftMidEquiv` is linear over `T^{AM}(θ + β) ⊗ T^R(γ)`. -/
theorem spectLeftMid_smul (d : cutFactorAlgebra Q ΛL (θ + β) γ)
    (y : CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N)) :
    cutStandardMap Q (ΛA) θ β κL (d • y) = d • (show MidL from cutStandardMap Q (ΛA) θ β κL y) := by
  induction d using TensorProduct.inductionOn with
  | tmul t l => exact spectLeftMid_smul_tmul Q Λ θ β γ E hQ N t l y
  | add d d' hd hd' =>
    exact (congrArg (cutStandardMap Q (ΛA) θ β κL) (add_smul d d' y)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hd hd').trans
        (add_smul d d' (show MidL from cutStandardMap Q (ΛA) θ β κL y)).symm))

/-- **The standardization at the first cut, with the last block in the spectator, is the
standardization at the first cut of the three-block module.** -/
def spectLeftMidEquiv :
    CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N) ≃ₗ[cutFactorAlgebra Q ΛL (θ + β) γ]
      MidL where
  toFun y := cutStandardMap Q (ΛA) θ β κL y
  invFun z := cutStandardMap Q (ΛA) θ β
    (LinearEquiv.toLinearMap (spectLeftInputEquiv Q Λ θ β γ E N).symm) z
  map_add' := map_add _
  map_smul' := spectLeftMid_smul Q Λ θ β γ E hQ N
  left_inv := (cutStandardMapEquiv Q (ΛA) θ β (spectLeftInputEquiv Q Λ θ β γ E N)).left_inv
  right_inv := (cutStandardMapEquiv Q (ΛA) θ β (spectLeftInputEquiv Q Λ θ β γ E N)).right_inv

variable {Q Λ θ β γ E} in
/-- The partial standardization at the second cut, as a module over the first cut. -/
abbrev spectRightMid : ModuleCat.{u} (cutSpectAlgebra (a := a) (r := m + 1) Q Λ θ (β + γ) E) :=
  (ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ β γ E).toRingHom).obj
    ((cutSpectFunctor (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ (AlgCat.of k (Hd ⊗[k] E)) hQ).obj
      X')

local notation "κR" => LinearEquiv.toLinearMap (spectRightInputEquiv Q Λ θ β γ E N)
local notation "Mid" => BlocksMid (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ

/-- `spectRightMidEquiv` intertwines the actions of `h ⊗ t ∈ T^A(θ) ⊗ T^{MR}(β + γ)`. -/
theorem spectRightMid_smul_tmul (h : Hd)
    (t : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) (β + γ))
    (y : CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N)) :
    cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR ((h ⊗ₜ[k] t : cutFactorAlgebra Q Λ θ (β + γ)) • y) =
      blocksMidAction (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ (h ⊗ₜ[k] t)
        (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR y) := by
  change cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR
      (cutStandardAction Q (Λ ∘ Fin.natAdd a) β γ _ hQ t (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ
        (cutSpectEnd Q (Λ ∘ Fin.natAdd a) β γ (AlgCat.of k (Hd ⊗[k] E)) X' (h ⊗ₜ[k] 1)) y)) =
    cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ
      (blocksHeadEnd (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ h)
      (cutStandardAction Q (Λ ∘ Fin.natAdd a) β γ _ hQ t
        (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR y))
  refine (cutStandardMap_action Q (Λ ∘ Fin.natAdd a) β γ hQ κR t _).trans (Eq.trans ?_
    (cutStandardMap_action Q (Λ ∘ Fin.natAdd a) β γ hQ _ t _).symm)
  refine congrArg _ ((cutStandardMap_comp Q (Λ ∘ Fin.natAdd a) β γ _ _ y).symm.trans (Eq.trans ?_
    (cutStandardMap_comp Q (Λ ∘ Fin.natAdd a) β γ _ _ y)))
  exact congrArg (fun g => cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ g y)
    (LinearMap.ext fun _ => rfl)

/-- `spectRightMidEquiv` is linear over `T^A(θ) ⊗ T^{MR}(β + γ)`. -/
theorem spectRightMid_smul (d : cutFactorAlgebra Q Λ θ (β + γ))
    (y : CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N)) :
    cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR (d • y) =
      d • (show Mid from cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR y) := by
  induction d using TensorProduct.inductionOn with
  | tmul h t => exact spectRightMid_smul_tmul Q Λ θ β γ E hQ N h t y
  | add d d' hd hd' =>
    exact (congrArg (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR) (add_smul d d' y)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hd hd').trans
        (add_smul d d' (show Mid from cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR y)).symm))

/-- **The standardization at the second cut, with the first block in the spectator, is the
standardization at the second cut of the three-block module.** -/
def spectRightMidEquiv :
    CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N) ≃ₗ[cutFactorAlgebra Q Λ θ (β + γ)] Mid where
  toFun y := cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR y
  invFun z := cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ
    (LinearEquiv.toLinearMap (spectRightInputEquiv Q Λ θ β γ E N).symm) z
  map_add' := map_add _
  map_smul' := spectRightMid_smul Q Λ θ β γ E hQ N
  left_inv := (cutStandardMapEquiv Q (Λ ∘ Fin.natAdd a) β γ
    (spectRightInputEquiv Q Λ θ β γ E N)).left_inv
  right_inv := (cutStandardMapEquiv Q (Λ ∘ Fin.natAdd a) β γ
    (spectRightInputEquiv Q Λ θ β γ E N)).right_inv

/-- The action of `e ∈ E` on a module over the three blocks and `E`, linear over the three
blocks. -/
def spectBlocksEnd (e : E) :
    N₀ →ₗ[blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ] N₀ where
  toFun n := ((1 : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E) •
    (show N from n)
  map_add' n n' := smul_add
    ((1 : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E)
    (show N from n) (show N from n')
  map_smul' x n := by
    change ((1 : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E) •
        ((x : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] (1 : E) : blocksSpectAlgebra Q Λ θ β γ E) •
          (show N from n) =
      ((x : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] (1 : E) : blocksSpectAlgebra Q Λ θ β γ E) •
        ((1 : blocksTotalAlgebra Q Λ θ β γ) ⊗ₜ[k] e : blocksSpectAlgebra Q Λ θ β γ E) •
          (show N from n)
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, one_mul]

local notation "μL" => LinearEquiv.toLinearMap (spectLeftMidEquiv Q Λ θ β γ E hQ N)
local notation "μR" => LinearEquiv.toLinearMap (spectRightMidEquiv Q Λ θ β γ E hQ N)
local notation "μR'" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (spectRightMidEquiv Q Λ θ β γ E hQ N))

/-- The identification of the left side intertwines the spectator with the map induced by the
spectator on the three-block module. -/
theorem spectLeft_spect (e : E)
    (z : CutStandard Q ΛL (θ + β) γ (CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N))) :
    cutStandardMap Q ΛL (θ + β) γ μL
        (cutStandardMap Q ΛL (θ + β) γ (cutSpectEnd Q ΛL (θ + β) γ E (spectLeftMid hQ N) e) z) =
      blocksStandardMapL (a := a) (m := m) (r := 1) Q ΛL θ β γ hQ
        (blocksAssocInputHom (a := a) (m := m) (r := 1) Q Λ θ β γ (spectBlocksEnd Q Λ θ β γ E N e))
        (cutStandardMap Q ΛL (θ + β) γ μL z) := by
  refine (cutStandardMap_comp Q ΛL (θ + β) γ _ _ z).symm.trans (Eq.trans
    (congrArg (fun g => cutStandardMap Q ΛL (θ + β) γ g z) (LinearMap.ext fun w => ?_))
    (cutStandardMap_comp Q ΛL (θ + β) γ _ _ z))
  change cutStandardMap Q (ΛA) θ β κL (cutStandardAction Q (ΛA) θ β _ hQ 1
      (cutStandardMap Q (ΛA) θ β
        (cutSpectEnd Q (ΛA) θ β (AlgCat.of k (Lst ⊗[k] E)) X (1 ⊗ₜ[k] e)) w)) =
    cutStandardMap Q (ΛA) θ β
      (blocksInnerHomL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (blocksAssocInputHom (a := a) (m := m) (r := 1) Q Λ θ β γ
          (spectBlocksEnd Q Λ θ β γ E N e)))
      (cutStandardMap Q (ΛA) θ β κL w)
  refine (congrArg (cutStandardMap Q (ΛA) θ β κL)
    (LinearMap.congr_fun (map_one (cutStandardAction Q (ΛA) θ β _ hQ)) _)).trans ?_
  refine (cutStandardMap_comp Q (ΛA) θ β _ _ w).symm.trans (Eq.trans
    (congrArg (fun g => cutStandardMap Q (ΛA) θ β g w) (LinearMap.ext fun n => ?_))
    (cutStandardMap_comp Q (ΛA) θ β _ _ w))
  exact congrArg (fun x : blocksSpectAlgebra Q Λ θ β γ E => x • (show N from n))
    (spectAssocLeftAlg_spect Q Λ θ β γ E e)

local notation "κR'" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (spectRightInputEquiv Q Λ θ β γ E N))

/-- The inverse identification of the right side intertwines the map induced by the spectator
on the three-block module with the spectator. -/
theorem spectRight_spect (e : E) (w : BlocksStandard (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ) :
    cutStandardMap Q Λ θ (β + γ) μR'
        (blocksStandardMap (a := a) (m := m) (r := 1) Q Λ θ β γ hQ
          (spectBlocksEnd Q Λ θ β γ E N e) w) =
      cutStandardMap Q Λ θ (β + γ) (cutSpectEnd Q Λ θ (β + γ) E (spectRightMid hQ N) e)
        (cutStandardMap Q Λ θ (β + γ) μR' w) := by
  refine (cutStandardMap_comp Q Λ θ (β + γ) _ _ w).symm.trans (Eq.trans
    (congrArg (fun g => cutStandardMap Q Λ θ (β + γ) g w) (LinearMap.ext fun v => ?_))
    (cutStandardMap_comp Q Λ θ (β + γ) _ _ w))
  change cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR'
      (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ
        (blocksInnerHom (a := a) (m := m) (r := 1) Q Λ θ β γ (spectBlocksEnd Q Λ θ β γ E N e)) v) =
    cutStandardAction Q (Λ ∘ Fin.natAdd a) β γ _ hQ 1
      (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ
        (cutSpectEnd Q (Λ ∘ Fin.natAdd a) β γ (AlgCat.of k (Hd ⊗[k] E)) X' (1 ⊗ₜ[k] e))
        (cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ κR' v))
  refine Eq.trans ?_ (LinearMap.congr_fun
    (map_one (cutStandardAction Q (Λ ∘ Fin.natAdd a) β γ _ hQ)) _).symm
  refine (cutStandardMap_comp Q (Λ ∘ Fin.natAdd a) β γ _ _ v).symm.trans (Eq.trans
    (congrArg (fun g => cutStandardMap Q (Λ ∘ Fin.natAdd a) β γ g v) (LinearMap.ext fun n => ?_))
    (cutStandardMap_comp Q (Λ ∘ Fin.natAdd a) β γ _ _ v))
  exact congrArg (fun x : blocksSpectAlgebra Q Λ θ β γ E => x • (show N from n))
    (spectAssocRightAlg_spect Q Λ θ β γ E e).symm

/-- **One-step associativity of the partial standardizations with a spectator**, as an
additive isomorphism: standardizing at the first cut (with the last block in the spectator) and
then at the second agrees with standardizing at the second cut (with the first block in the
spectator) and then at the first. -/
def spectAssocAddEquiv :
    CutSpectStandard Q ΛL (θ + β) γ E (spectLeftMid hQ N) hQ ≃+
      CutSpectStandard Q Λ θ (β + γ) E (spectRightMid hQ N) hQ :=
  ((cutStandardMapEquiv Q ΛL (θ + β) γ (spectLeftMidEquiv Q Λ θ β γ E hQ N)).trans
    ((blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ).trans
      (cutStandardMapEquiv Q Λ θ (β + γ) (spectRightMidEquiv Q Λ θ β γ E hQ N)).symm)).toAddEquiv

theorem spectAssocAddEquiv_apply
    (z : CutSpectStandard Q ΛL (θ + β) γ E (spectLeftMid hQ N) hQ) :
    spectAssocAddEquiv Q Λ θ β γ E hQ N z =
      cutStandardMap Q Λ θ (β + γ) μR'
        (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ
          (cutStandardMap Q ΛL (θ + β) γ μL z)) := rfl

/-- The weight associator `T^λ((θ + β) + γ) ⊗ E ≅ T^λ(θ + (β + γ)) ⊗ E`. -/
abbrev spectWeightAssoc :
    TensorProductAlgebra k Q ΛL ((θ + β) + γ) ⊗[k] E →ₐ[k]
      TensorProductAlgebra k Q Λ (θ + (β + γ)) ⊗[k] E :=
  Algebra.TensorProduct.map (castTensorProductAlgebra Q Λ (add_assoc θ β γ)).toAlgHom
    (AlgHom.id k E)

/-- The one-step associativity intertwines the actions of `t ⊗ e`. -/
theorem spectAssocAddEquiv_smul_tmul (t : TensorProductAlgebra k Q ΛL ((θ + β) + γ)) (e : E)
    (z : CutSpectStandard Q ΛL (θ + β) γ E (spectLeftMid hQ N) hQ) :
    spectAssocAddEquiv Q Λ θ β γ E hQ N ((t ⊗ₜ[k] e) • z) =
      ((castTensorProductAlgebra Q Λ (add_assoc θ β γ) t ⊗ₜ[k] e :
        TensorProductAlgebra k Q Λ (θ + (β + γ)) ⊗[k] E) •
        spectAssocAddEquiv Q Λ θ β γ E hQ N z) := by
  refine (congrArg (spectAssocAddEquiv Q Λ θ β γ E hQ N)
    ((cutSpectStandard_smul Q ΛL (θ + β) γ E _ hQ _ z).trans
      (cutSpectStandardAction_tmul Q ΛL (θ + β) γ E _ hQ t e z))).trans (Eq.trans ?_
    ((cutSpectStandard_smul Q Λ θ (β + γ) E _ hQ _ _).trans
      (cutSpectStandardAction_tmul Q Λ θ (β + γ) E _ hQ _ e _)).symm)
  refine (spectAssocAddEquiv_apply Q Λ θ β γ E hQ N _).trans ?_
  refine (congrArg (fun w => cutStandardMap Q Λ θ (β + γ) μR'
      (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ w))
    ((cutStandardMap_action Q ΛL (θ + β) γ hQ μL t _).trans
      (congrArg (cutStandardAction Q ΛL (θ + β) γ _ hQ t)
        (spectLeft_spect Q Λ θ β γ E hQ N e z)))).trans ?_
  refine (congrArg (cutStandardMap Q Λ θ (β + γ) μR')
    ((blocksStandardAssocEquiv_action_one Q Λ θ β γ N₀ hQ t _).trans
      (congrArg (blocksStandardAction (a := a) (m := m) (r := 1) Q Λ θ β γ N₀ hQ
          (castTensorProductAlgebra Q Λ (add_assoc θ β γ) t))
        (blocksStandardAssocEquiv_map (a := a) (m := m) (r := 1) Q Λ θ β γ hQ
          (spectBlocksEnd Q Λ θ β γ E N e) _)))).trans ?_
  refine (cutStandardMap_action Q Λ θ (β + γ) hQ μR' _ _).trans
    (congrArg (cutStandardAction Q Λ θ (β + γ) _ hQ _)
      ((spectRight_spect Q Λ θ β γ E hQ N e _).trans ?_))
  exact (congrArg (cutStandardMap Q Λ θ (β + γ)
      (cutSpectEnd Q Λ θ (β + γ) E (spectRightMid hQ N) e))
    (spectAssocAddEquiv_apply Q Λ θ β γ E hQ N z).symm).trans
    (cutSpectAction_apply Q Λ θ (β + γ) E _ e _).symm

/-- **The one-step associativity intertwines the actions** along the weight associator. -/
theorem spectAssocAddEquiv_smul (x : TensorProductAlgebra k Q ΛL ((θ + β) + γ) ⊗[k] E)
    (z : CutSpectStandard Q ΛL (θ + β) γ E (spectLeftMid hQ N) hQ) :
    spectAssocAddEquiv Q Λ θ β γ E hQ N (x • z) =
      spectWeightAssoc Q Λ θ β γ E x • spectAssocAddEquiv Q Λ θ β γ E hQ N z := by
  induction x using TensorProduct.inductionOn with
  | tmul t e =>
    exact spectAssocAddEquiv_smul_tmul Q Λ θ β γ E hQ N t e z
  | add x y hx hy =>
    exact (congrArg (spectAssocAddEquiv Q Λ θ β γ E hQ N) (add_smul x y z)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
        ((add_smul _ _ (spectAssocAddEquiv Q Λ θ β γ E hQ N z)).symm.trans
          (congrArg (· • spectAssocAddEquiv Q Λ θ β γ E hQ N z) (map_add _ x y).symm))))

/-- The one-step associativity, as an isomorphism of modules over `T^λ((θ + β) + γ) ⊗ E`. -/
def spectAssocLinearEquiv :
    spectAssocLeft Q Λ θ β γ E hQ N ≃ₗ[TensorProductAlgebra k Q ΛL ((θ + β) + γ) ⊗[k] E]
      (ModuleCat.restrictScalars.{u} (spectWeightAssoc Q Λ θ β γ E).toRingHom).obj
        (spectAssocRight Q Λ θ β γ E hQ N) where
  toFun := spectAssocAddEquiv Q Λ θ β γ E hQ N
  invFun := (spectAssocAddEquiv Q Λ θ β γ E hQ N).symm
  map_add' := map_add _
  map_smul' := spectAssocAddEquiv_smul Q Λ θ β γ E hQ N
  left_inv := (spectAssocAddEquiv Q Λ θ β γ E hQ N).left_inv
  right_inv := (spectAssocAddEquiv Q Λ θ β γ E hQ N).right_inv

/-- **One-step associativity of the partial standardizations with a spectator**
(Webster, arXiv:1309.3796v3, §5.1): for a module `N` over `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ)) ⊗ E`,
standardizing at the first cut (with `T^R(γ)` in the spectator) and then at the second cut is
isomorphic, along the weight associator, to standardizing at the second cut (with `T^A(θ)` in
the spectator) and then at the first cut. -/
def spectAssocIso :
    spectAssocLeft Q Λ θ β γ E hQ N ≅
      (ModuleCat.restrictScalars.{u} (spectWeightAssoc Q Λ θ β γ E).toRingHom).obj
        (spectAssocRight Q Λ θ β γ E hQ N) :=
  (spectAssocLinearEquiv Q Λ θ β γ E hQ N).toModuleIso

theorem spectAssocIso_hom_apply (z : spectAssocLeft Q Λ θ β γ E hQ N) :
    (spectAssocIso Q Λ θ β γ E hQ N).hom.hom z = spectAssocAddEquiv Q Λ θ β γ E hQ N z := rfl

end Spect

end Categorification.Stendhal
