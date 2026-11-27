/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksPlus
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons

/-!
# The partial standardization `S_+` of `λ⁺`, in stages

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 (the
partial standardization functors after Definition 5.4) and §7.3 (proof of Lemma 7.19). The
partial standardization `S_+ = 𝕊^{λ_1; …; λ_j; μ μ*; λ_{j+1}; …; λ_ℓ}` of `λ⁺` has one block for
each red strand of `λ` and one block for the pair `(μ, μ*)`. Following Webster's description of
`S_+`, it is the partial standardization with the three blocks `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ`
(`PlusStandard`) applied after the standardizations of the first and of the last block: for a
module over `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_j}(θ_j) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}}(θ'_1) ⊗ ⋯)`, the
first `j` blocks are standardized in stages with the rest as a spectator, then the last
`ℓ - j` blocks with the rest as a spectator (`plusOuterStd`), and the result is standardized
with the three blocks (`plusStagedStd`). All stages are exact, and so is `S_+`
(`moduleExactFunctor_plusStagedStd`). The standardization `S` of `λ` is the standardization
with singleton blocks in stages (`singStandard`).

## Main definitions

* `Stendhal.singStandard`: the standardization with singleton blocks, in stages.
* `Stendhal.CupCap.plusStandardFunctor`: `PlusStandard` as a functor.
* `Stendhal.CupCap.plusOuterStd`: the standardizations of the first and the last block.
* `Stendhal.CupCap.plusStagedStd`: the partial standardization `S_+`.

## Main results

* `Stendhal.moduleExactFunctor_singStandard`, `Stendhal.CupCap.moduleExactFunctor_plusStagedStd`:
  both are exact (Proposition 5.7).
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- **The standardization with singleton blocks, in stages**: modules over
`T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n)` to modules over `T^λ(θ_1 + ⋯ + θ_n)`. -/
def singStandard (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) :
    ModuleCat.{u} (singAlg Q n Λ θ) ⥤ ModuleCat.{u} (TensorProductAlgebra k Q Λ (singWeight n θ)) :=
  ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.rid k k (singAlg Q n Λ θ)).toAlgHom.toRingHom ⋙
    singStd Q hQ n Λ θ (AlgCat.of k k) ⋙
    ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.includeLeft :
      TensorProductAlgebra k Q Λ (singWeight n θ) →ₐ[k]
        TensorProductAlgebra k Q Λ (singWeight n θ) ⊗[k] k).toRingHom

/-- **The standardization with singleton blocks is exact.** -/
theorem moduleExactFunctor_singStandard (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) :
    ModuleExactFunctor (singStandard Q hQ n Λ θ) :=
  (ModuleExactFunctor.restrictScalars _).comp ((moduleExactFunctor_singStd Q hQ n Λ θ _).comp
    (ModuleExactFunctor.restrictScalars _))

/-- The rotation `A ⊗ (B ⊗ C) ≃ B ⊗ (C ⊗ A)` of a triple tensor product of algebras. -/
def tensorRotate (A B C : Type u) [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C]
    [Algebra k C] : A ⊗[k] (B ⊗[k] C) ≃ₐ[k] B ⊗[k] (C ⊗[k] A) :=
  (Algebra.TensorProduct.comm k A (B ⊗[k] C)).trans (Algebra.TensorProduct.assoc k k k B C A)

namespace CupCap

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)
  (θ β γ : Multiset I)

/-- The algebra `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))` of the three blocks of
`λ⁺`, bundled. -/
abbrev plusFactorAlgCat : AlgCat.{u} k := AlgCat.of k (PlusFactorAlgebra Q Λ Λc j hj θ β γ)

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev plusNonAssocSemiring' : NonAssocSemiring (PlusFactorAlgebra Q Λ Λc j hj θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] plusNonAssocSemiring'

/-- A module over the bundled algebra of the three blocks of `λ⁺`, as a module over
`PlusFactorAlgebra`. -/
@[nolint unusedArguments]
def PlusWrap (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)) : Type u := N

variable (N : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ))

instance : AddCommGroup (PlusWrap Q Λ Λc j hj θ β γ N) := inferInstanceAs (AddCommGroup N)
instance : Module k (PlusWrap Q Λ Λc j hj θ β γ N) := inferInstanceAs (Module k N)
instance : Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) (PlusWrap Q Λ Λc j hj θ β γ N) :=
  Module.compHom N (show PlusFactorAlgebra Q Λ Λc j hj θ β γ →+* plusFactorAlgCat Q Λ Λc j hj θ β γ
    from RingHom.id _)

instance : IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ)
    (PlusWrap Q Λ Λc j hj θ β γ N) where
  smul_assoc c d n :=
    (moduleCatScalars_isScalarTower N).smul_assoc c (show plusFactorAlgCat Q Λ Λc j hj θ β γ from d)
      (show N from n)

variable {N} in
/-- A map of modules over the bundled algebra, over `PlusFactorAlgebra`. -/
def plusWrapHom {N' : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)} (g : N ⟶ N') :
    PlusWrap Q Λ Λc j hj θ β γ N →ₗ[PlusFactorAlgebra Q Λ Λc j hj θ β γ]
      PlusWrap Q Λ Λc j hj θ β γ N' where
  toFun n := g.hom n
  map_add' := g.hom.map_add
  map_smul' d n := g.hom.map_smul d n

/-- The partial standardization of `λ⁺` with three blocks, as a module over
`T^{λ⁺}(θ + (β + γ))`. -/
@[nolint unusedArguments]
def PlusStandardModule : Type u :=
  PlusStandard Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ

instance : AddCommGroup (PlusStandardModule Q hQ Λ Λc j hj θ β γ N) :=
  inferInstanceAs (AddCommGroup (PlusStandard Q Λ Λc j hj θ β γ _ hQ))

instance : Module (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)))
    (PlusStandardModule Q hQ Λ Λc j hj θ β γ N) :=
  Module.compHom (PlusStandard Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ)
    (plusStandardAction Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ).toRingHom

theorem plusStandardMap_wrap_id :
    plusStandardMap Q Λ Λc j hj θ β γ hQ (plusWrapHom Q Λ Λc j hj θ β γ (𝟙 N)) =
      LinearMap.id := by
  have h : blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
      (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ (𝟙 N))) = LinearMap.id :=
    LinearMap.ext fun z => LinearMap.congr_fun (cutStandardMap_id Q _ β γ) z
  exact (congrArg (cutStandardMap Q _ θ (β + γ)) h).trans (cutStandardMap_id Q _ θ (β + γ))

variable {N} in
theorem plusStandardMap_wrap_comp {N' N'' : ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ)}
    (g : N ⟶ N') (g' : N' ⟶ N'')
    (z : PlusStandard Q Λ Λc j hj θ β γ (PlusWrap Q Λ Λc j hj θ β γ N) hQ) :
    plusStandardMap Q Λ Λc j hj θ β γ hQ (plusWrapHom Q Λ Λc j hj θ β γ (g ≫ g')) z =
      plusStandardMap Q Λ Λc j hj θ β γ hQ (plusWrapHom Q Λ Λc j hj θ β γ g')
        (plusStandardMap Q Λ Λc j hj θ β γ hQ (plusWrapHom Q Λ Λc j hj θ β γ g) z) := by
  have h : blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
      (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ (g ≫ g'))) =
      blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
          (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g')) ∘ₗ
        blocksMidHom Q (plusBlockLabels Λ Λc j hj) θ β γ hQ
          (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)) :=
    LinearMap.ext fun w => cutStandardMap_comp Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β γ
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
        (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g)))
      (blocksInnerHom Q (plusBlockLabels Λ Λc j hj) θ β γ
        (plusInputHom Q Λ Λc j hj θ β γ (plusWrapHom Q Λ Λc j hj θ β γ g'))) w
  exact (congrArg (fun f => cutStandardMap Q (plusBlockLabels Λ Λc j hj) θ (β + γ) f z) h).trans
    (cutStandardMap_comp Q (plusBlockLabels Λ Λc j hj) θ (β + γ) _ _ z)

/-- **The partial standardization of `λ⁺` with three blocks, as a functor.** -/
def plusStandardFunctor :
    ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj θ β γ) ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ))) where
  obj N := ModuleCat.of _ (PlusStandardModule Q hQ Λ Λc j hj θ β γ N)
  map g := ModuleCat.ofHom
    { toFun := plusStandardMap Q Λ Λc j hj θ β γ hQ (plusWrapHom Q Λ Λc j hj θ β γ g)
      map_add' := map_add _
      map_smul' t z := plusStandardMap_action Q Λ Λc j hj θ β γ hQ
        (plusWrapHom Q Λ Λc j hj θ β γ g) t z }
  map_id N := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (plusStandardMap_wrap_id Q hQ Λ Λc j hj θ β γ N) z)
  map_comp g g' := ModuleCat.hom_ext (LinearMap.ext fun z =>
    plusStandardMap_wrap_comp Q hQ Λ Λc j hj θ β γ g g' z)

/-- The partial standardization of `λ⁺` with three blocks is exact. -/
theorem moduleExactFunctor_plusStandardFunctor :
    ModuleExactFunctor (plusStandardFunctor Q hQ Λ Λc j hj θ β γ) :=
  ⟨fun _ _ h => plusStandardMap_exact Q Λ Λc j hj θ β γ hQ _ _ h,
    fun _ h => plusStandardMap_injective Q Λ Λc j hj θ β γ hQ _ h,
    fun _ h => plusStandardMap_surjective Q Λ Λc j hj θ β γ hQ _ h⟩

/-! ### The outer standardizations and `S_+` -/

variable (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

/-- The algebra of the blocks of `S_+`: the singleton blocks `λ_1, …, λ_j`, then the pair
`(μ, μ*)` and the singleton blocks `λ_{j+1}, …, λ_ℓ`. -/
abbrev plusSingAlg : Type u :=
  singAlg Q j (Λ ∘ Fin.castLE hj) θh ⊗[k]
    (AlgCat.of k (TensorProductAlgebra k Q Λc β ⊗[k] singAlg Q (ℓ - j) (plusTailLabels Λ j hj) θt) :
      AlgCat.{u} k)

/-- The algebra of the first block after its standardization. -/
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) (singWeight j θh)
/-- The algebra of the last block after its standardization. -/
local notation "Tl" => TensorProductAlgebra k Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt)
local notation "Cp" => TensorProductAlgebra k Q Λc β
local notation "St" => singAlg Q (ℓ - j) (plusTailLabels Λ j hj) θt

/-- **The standardizations of the first and of the last block of `S_+`**: the singleton blocks
`λ_1, …, λ_j` are standardized in stages with the pair and the last blocks as a spectator,
then the singleton blocks `λ_{j+1}, …, λ_ℓ` with the first block and the pair as a spectator.
The result is a module over `T^{λ_1…λ_j}(θ) ⊗ (T^{μ μ*}(β) ⊗ T^{λ_{j+1}…λ_ℓ}(γ))`. -/
def plusOuterStd :
    ModuleCat.{u} (plusSingAlg Q Λ Λc j hj β θh θt) ⥤
      ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)) :=
  singStd Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) ⋙
    ModuleCat.restrictScalars.{u} (show St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k) →+*
        Hd ⊗[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k) from
      (tensorRotate (k := k) St Hd Cp).toAlgHom.toRingHom) ⋙
    singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp)) ⋙
    ModuleCat.restrictScalars.{u}
      (show plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt) →+*
        Tl ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k) from
      (tensorRotate (k := k) Tl Hd Cp).symm.toAlgHom.toRingHom)

/-- The standardizations of the first and of the last block of `S_+` are exact. -/
theorem moduleExactFunctor_plusOuterStd :
    ModuleExactFunctor (plusOuterStd Q hQ Λ Λc j hj β θh θt) :=
  (moduleExactFunctor_singStd Q hQ _ _ _ _).comp ((ModuleExactFunctor.restrictScalars _).comp
    ((moduleExactFunctor_singStd Q hQ _ _ _ _).comp (ModuleExactFunctor.restrictScalars _)))

/-- **The partial standardization `S_+ = 𝕊^{λ_1; …; λ_j; μ μ*; λ_{j+1}; …; λ_ℓ}`**, in Webster's
description: the partial standardization with the three blocks `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ`
applied after the standardizations of the first and the last block. -/
def plusStagedStd :
    ModuleCat.{u} (plusSingAlg Q Λ Λc j hj β θh θt) ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
        (singWeight j θh + (β + singWeight (ℓ - j) θt))) :=
  plusOuterStd Q hQ Λ Λc j hj β θh θt ⋙
    plusStandardFunctor Q hQ Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)

/-- **`S_+` is exact** (Webster, arXiv:1309.3796v3, Proposition 5.7, for this partial
standardization). -/
theorem moduleExactFunctor_plusStagedStd :
    ModuleExactFunctor (plusStagedStd Q hQ Λ Λc j hj β θh θt) :=
  (moduleExactFunctor_plusOuterStd Q hQ Λ Λc j hj β θh θt).comp
    (moduleExactFunctor_plusStandardFunctor Q hQ Λ Λc j hj _ β _)

end CupCap

end Categorification.Stendhal
