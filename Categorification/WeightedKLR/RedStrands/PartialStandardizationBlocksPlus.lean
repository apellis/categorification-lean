/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksExact
import Categorification.WeightedKLR.Rigidity.CupCapDiagrams

/-!
# Partial standardization of `λ⁺` with the cap labels as one block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 (the
partial standardization functors after Definition 5.4) and §7.3 (proof of Lemma 7.19). For the
red labels `λ⁺` (`plusLabels`), `λ` with `μ, μ*` inserted after its first `j` labels, the
partial standardization `𝕊^{λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ}` has three blocks: the first `j`
labels of `λ`, the pair `(μ, μ*)`, and the last `ℓ - j` labels of `λ`.

The model of three blocks (`BlocksStandard`) has red labels `Fin (j + (2 + (ℓ - j)))`. We
reindex `λ⁺` along `Fin.cast` to these labels (`plusBlockLabels`) and identify the three blocks
of labels with `λ_1…λ_j`, `(μ, μ*)` and `λ_{j+1}…λ_ℓ` (`plusBlockLabels_head`,
`plusBlockLabels_cup`, `plusBlockLabels_tail`). Through these identifications the partial
standardization takes modules over `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))` to
modules over `T^{λ⁺}(θ + (β + γ))` (`PlusStandard`, `plusStandardAction`), and it is exact
(`plusStandardMap_exact`).

In Webster's `S_+` every red strand other than the pair is a block of its own; that functor is
`PlusStandard` applied after the standardizations of the first and last blocks, which Webster
uses without proof (associativity of standardization); that comparison is not made here.

## Main definitions

* `Stendhal.CupCap.plusBlockLabels`: the labels `λ⁺` on `Fin (j + (2 + (ℓ - j)))`.
* `Stendhal.CupCap.plusFactorEquiv`: the algebra of the three blocks of `λ⁺` is
  `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))`.
* `Stendhal.CupCap.PlusStandard`, `plusStandardAction`: the partial standardization of `λ⁺`
  with blocks `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ`, a module over `T^{λ⁺}(θ + (β + γ))`.
* `Stendhal.CupCap.plusStandardMap`: its action on maps.

## Main results

* `Stendhal.CupCap.plusBlockLabels_cup`: the middle block is `(μ, μ*)`.
* `Stendhal.CupCap.plusStandardMap_action`, `plusStandardMap_exact`,
  `plusStandardMap_injective`, `plusStandardMap_surjective`: Proposition 5.7 for it.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The tensor product algebras of equal red labels. -/
def relabelTensorProductAlgebra {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂)
    (ν : Multiset I) : TensorProductAlgebra k Q Λ₁ ν ≃ₐ[k] TensorProductAlgebra k Q Λ₂ ν := by
  subst h
  exact AlgEquiv.refl

/-- The tensor product algebra of red labels reindexed along `Fin.cast`. -/
def castLabelsTensorProductAlgebra {n n' : ℕ} (h : n = n') (Λ : Fin n' → I →₀ ℕ)
    (ν : Multiset I) :
    TensorProductAlgebra k Q (Λ ∘ Fin.cast h) ν ≃ₐ[k] TensorProductAlgebra k Q Λ ν := by
  subst h
  exact AlgEquiv.refl

namespace CupCap

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)

include hj in
theorem plusBlock_card : j + (2 + (ℓ - j)) = ℓ + 2 := by omega

/-- **The labels `λ⁺` as three blocks**: `λ⁺` reindexed to `Fin (j + (2 + (ℓ - j)))`. -/
def plusBlockLabels : Fin (j + (2 + (ℓ - j))) → I →₀ ℕ :=
  plusLabels Λ Λc j hj ∘ Fin.cast (plusBlock_card j hj)

/-- The labels `λ_{j+1}…λ_ℓ` of the last block. -/
def plusTailLabels : Fin (ℓ - j) → I →₀ ℕ := fun r => Λ ⟨j + r, by omega⟩

omit [DecidableEq I] in
/-- The first block of `λ⁺` is `λ_1…λ_j`. -/
theorem plusBlockLabels_head :
    plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j)) = Λ ∘ Fin.castLE hj := by
  funext r
  have h : Fin.cast (plusBlock_card j hj) (Fin.castAdd (2 + (ℓ - j)) r) =
      oldRed j hj (Fin.castLE hj r) := by
    ext
    simp [oldRed, r.2]
  simp only [Function.comp_apply, plusBlockLabels, h, plusLabels_oldRed]

omit [DecidableEq I] in
/-- **The middle block of `λ⁺` is the pair `(μ, μ*)`.** -/
theorem plusBlockLabels_cup :
    blocksTailLabels (plusBlockLabels Λ Λc j hj) ∘ Fin.castAdd (ℓ - j) = Λc := by
  funext r
  have h : Fin.cast (plusBlock_card j hj) (Fin.natAdd j (Fin.castAdd (ℓ - j) r)) =
      cupRed j hj r := by
    ext
    simp [cupRed]
  simp only [Function.comp_apply, blocksTailLabels, plusBlockLabels, h, plusLabels_cupRed]

omit [DecidableEq I] in
/-- The last block of `λ⁺` is `λ_{j+1}…λ_ℓ`. -/
theorem plusBlockLabels_tail :
    blocksTailLabels (plusBlockLabels Λ Λc j hj) ∘ Fin.natAdd 2 = plusTailLabels Λ j hj := by
  funext r
  have h : Fin.cast (plusBlock_card j hj) (Fin.natAdd j (Fin.natAdd 2 r)) =
      oldRed j hj ⟨j + r, by omega⟩ := by
    ext
    simp only [Fin.val_cast, Fin.val_natAdd, oldRed, insertPos_inl_val]
    have hlt : ¬ (j + r.val < j) := by omega
    simp only [hlt, ↓reduceIte]
    omega
  simp only [Function.comp_apply, blocksTailLabels, plusBlockLabels, h, plusLabels_oldRed,
    plusTailLabels]

variable (θ β γ : Multiset I)

/-- **The algebra of the three blocks of `λ⁺`** is
`T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))`. -/
def plusFactorEquiv :
    blocksFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ β γ ≃ₐ[k]
      TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ ⊗[k]
        (TensorProductAlgebra k Q Λc β ⊗[k] TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ) :=
  Algebra.TensorProduct.congr (relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ)
    (Algebra.TensorProduct.congr (relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) β)
      (relabelTensorProductAlgebra Q (plusBlockLabels_tail Λ Λc j hj) γ))

/-- The algebra `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))` of the three blocks
of `λ⁺`. -/
abbrev PlusFactorAlgebra :=
  TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ ⊗[k]
    (TensorProductAlgebra k Q Λc β ⊗[k] TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev plusNonAssocSemiring : NonAssocSemiring (PlusFactorAlgebra Q Λ Λc j hj θ β γ) :=
  Semiring.toNonAssocSemiring

/-- The semiring structure of the algebra of the model, through its ring structure. -/
private abbrev plusBlocksNonAssocSemiring :
    NonAssocSemiring (blocksFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] plusNonAssocSemiring plusBlocksNonAssocSemiring

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]

/-- A module over the three blocks of `λ⁺`, as a module over the algebra of the model. -/
@[nolint unusedArguments]
def PlusInput (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin ℓ → I →₀ ℕ)
    (_Λc : Fin 2 → I →₀ ℕ) (_j : ℕ) (_hj : _j ≤ ℓ) (_θ _β _γ : Multiset I) (N : Type*) :
    Type _ := N

instance : AddCommGroup (PlusInput Q Λ Λc j hj θ β γ N) := inferInstanceAs (AddCommGroup N)
instance : Module k (PlusInput Q Λ Λc j hj θ β γ N) := inferInstanceAs (Module k N)
instance : Module (blocksFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ β γ)
    (PlusInput Q Λ Λc j hj θ β γ N) :=
  Module.compHom N (plusFactorEquiv Q Λ Λc j hj θ β γ).toRingEquiv.toRingHom

omit [Module k N] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N] in
theorem plusInput_smul (d : blocksFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ β γ)
    (n : PlusInput Q Λ Λc j hj θ β γ N) :
    d • n = (plusFactorEquiv Q Λ Λc j hj θ β γ d • (show N from n) : N) := rfl

instance : IsScalarTower k (blocksFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ β γ)
    (PlusInput Q Λ Λc j hj θ β γ N) where
  smul_assoc c d n := by
    rw [plusInput_smul, plusInput_smul, show plusFactorEquiv Q Λ Λc j hj θ β γ (c • d) =
      c • plusFactorEquiv Q Λ Λc j hj θ β γ d from
      map_smul (plusFactorEquiv Q Λ Λc j hj θ β γ).toAlgHom.toLinearMap c d]
    exact smul_assoc c _ (show N from n)

variable (hQ : KLRSymm Q)

/-- **The partial standardization of `λ⁺` with blocks `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ`** of a
module `N` over `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))`. -/
abbrev PlusStandard : Type _ :=
  BlocksStandard Q (plusBlockLabels Λ Λc j hj) θ β γ (PlusInput Q Λ Λc j hj θ β γ N) hQ

/-- **The action of `T^{λ⁺}(θ + (β + γ))`** on the partial standardization of `λ⁺`. -/
def plusStandardAction :
    TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)) →ₐ[k]
      Module.End k (PlusStandard Q Λ Λc j hj θ β γ N hQ) :=
  (blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ β γ _ hQ).comp
    (castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
      (θ + (β + γ))).symm.toAlgHom

variable {N} {N' N'' : Type*}
  [AddCommGroup N'] [Module k N'] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N']
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N']
  [AddCommGroup N''] [Module k N''] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N'']
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N'']

/-- A map of modules over the three blocks of `λ⁺`, over the algebra of the model. -/
def plusInputHom (g : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N') :
    PlusInput Q Λ Λc j hj θ β γ N →ₗ[blocksFactorAlgebra Q (plusBlockLabels Λ Λc j hj) θ β γ]
      PlusInput Q Λ Λc j hj θ β γ N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' d n := g.map_smul (plusFactorEquiv Q Λ Λc j hj θ β γ d) n

/-- The map of partial standardizations of `λ⁺` induced by a module map. -/
def plusStandardMap (g : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N') :
    PlusStandard Q Λ Λc j hj θ β γ N hQ →ₗ[k] PlusStandard Q Λ Λc j hj θ β γ N' hQ :=
  blocksStandardMap Q (plusBlockLabels Λ Λc j hj) θ β γ hQ (plusInputHom Q Λ Λc j hj θ β γ g)

/-- The map of partial standardizations of `λ⁺` is linear over `T^{λ⁺}(θ + (β + γ))`. -/
theorem plusStandardMap_action (g : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)))
    (z : PlusStandard Q Λ Λc j hj θ β γ N hQ) :
    plusStandardMap Q Λ Λc j hj θ β γ hQ g (plusStandardAction Q Λ Λc j hj θ β γ N hQ t z) =
      plusStandardAction Q Λ Λc j hj θ β γ N' hQ t (plusStandardMap Q Λ Λc j hj θ β γ hQ g z) :=
  blocksStandardMap_action Q (plusBlockLabels Λ Λc j hj) θ β γ hQ _ _ z

/-- **Partial standardization of `λ⁺` with blocks `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ` is exact**
(Webster, arXiv:1309.3796v3, Proposition 5.7, for this partial standardization). -/
theorem plusStandardMap_exact (f : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (g : N' →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N'') (h : Function.Exact f g) :
    Function.Exact (plusStandardMap Q Λ Λc j hj θ β γ hQ f)
      (plusStandardMap Q Λ Λc j hj θ β γ hQ g) :=
  blocksStandardMap_exact Q (plusBlockLabels Λ Λc j hj) θ β γ hQ _ _ h

/-- Partial standardization of `λ⁺` preserves injections. -/
theorem plusStandardMap_injective (f : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (hf : Function.Injective f) : Function.Injective (plusStandardMap Q Λ Λc j hj θ β γ hQ f) :=
  blocksStandardMap_injective Q (plusBlockLabels Λ Λc j hj) θ β γ hQ _ hf

/-- Partial standardization of `λ⁺` preserves surjections. -/
theorem plusStandardMap_surjective (f : N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ] N')
    (hf : Function.Surjective f) :
    Function.Surjective (plusStandardMap Q Λ Λc j hj θ β γ hQ f) :=
  blocksStandardMap_surjective Q (plusBlockLabels Λ Λc j hj) θ β γ hQ _ hf

end CupCap

end Categorification.Stendhal
