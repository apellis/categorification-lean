/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectator
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Standardization with singleton blocks, in stages

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. The
standardization of Definition 5.4 has one block for each red strand. Here it is built in
stages from the partial standardization at a cut: for red labels `λ_1, …, λ_n` and weights
`θ_1, …, θ_n`, a module over `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n)` (`singAlg`, nested to the
left, starting from the algebra `T^∅(0)` of no strands) is standardized over the first `n - 1`
blocks, the last block carried along as a spectator, and the result is standardized at the cut
before the last red strand (`singStd`). Every stage allows a
further spectator algebra `E`, so that the construction applies to some of the blocks of a
larger family. Each stage is exact, and so is the standardization in stages
(`moduleExactFunctor_singStd`).

## Main definitions

* `Stendhal.ModuleExactFunctor`: a functor of module categories preserving exact pairs,
  injections and surjections.
* `Stendhal.cutSpectFunctor`: partial standardization at a cut with a spectator, as a functor.
* `Stendhal.singAlg`: the algebra `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n)` of the singleton blocks.
* `Stendhal.singStd`: the standardization in stages, with a spectator, a functor from modules
  over `singAlg ⊗ E` to modules over `T^λ(θ_1 + ⋯ + θ_n) ⊗ E`.

## Main results

* `Stendhal.moduleExactFunctor_cutSpectFunctor`, `Stendhal.moduleExactFunctor_singStd`: both
  are exact.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

/-! ### Exact functors of module categories -/

/-- A functor of module categories that preserves exact pairs, injections and surjections. -/
structure ModuleExactFunctor {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) : Prop where
  exact {X Y Z : ModuleCat.{u} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Function.Exact f.hom g.hom → Function.Exact (F.map f).hom (F.map g).hom
  injective {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    Function.Injective f.hom → Function.Injective (F.map f).hom
  surjective {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    Function.Surjective f.hom → Function.Surjective (F.map f).hom

namespace ModuleExactFunctor

variable {R S U : Type u} [Ring R] [Ring S] [Ring U]

theorem id : ModuleExactFunctor (𝟭 (ModuleCat.{u} R)) :=
  ⟨fun _ _ h => h, fun _ h => h, fun _ h => h⟩

theorem comp {F : ModuleCat.{u} R ⥤ ModuleCat.{u} S} {G : ModuleCat.{u} S ⥤ ModuleCat.{u} U}
    (hF : ModuleExactFunctor F) (hG : ModuleExactFunctor G) : ModuleExactFunctor (F ⋙ G) :=
  ⟨fun f g h => hG.exact _ _ (hF.exact f g h), fun f h => hG.injective _ (hF.injective f h),
    fun f h => hG.surjective _ (hF.surjective f h)⟩

theorem restrictScalars (f : R →+* S) : ModuleExactFunctor (ModuleCat.restrictScalars.{u} f) :=
  ⟨fun _ _ h => h, fun _ h => h, fun _ h => h⟩

end ModuleExactFunctor

/-! ### Partial standardization at a cut with a spectator, as a functor -/

section Functor

variable {I k : Type u} [DecidableEq I] [CommRing k]

/-- A module over a `k`-algebra, as a `k`-module. -/
abbrev moduleCatScalars {R : Type u} [Ring R] [Algebra k R] (M : ModuleCat.{u} R) : Module k M :=
  Module.compHom M (algebraMap k R)

attribute [local instance] moduleCatScalars

theorem moduleCatScalars_isScalarTower {R : Type u} [Ring R] [Algebra k R]
    (M : ModuleCat.{u} R) : IsScalarTower k R M where
  smul_assoc c x m := by
    change (c • x) • m = (algebraMap k R c) • x • m
    rw [Algebra.smul_def, mul_smul]

attribute [local instance] moduleCatScalars_isScalarTower

variable {a r : ℕ} (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ)
  (θ β : Multiset I) (E : AlgCat.{u} k) (hQ : KLRSymm Q)

/-- **Partial standardization at a cut with a spectator `E`**, as a functor from modules over
`(T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)) ⊗ E` to modules over `T^λ(θ + β) ⊗ E`. -/
def cutSpectFunctor :
    ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E) ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q Λ (θ + β) ⊗[k] E) where
  obj M := ModuleCat.of _ (CutSpectStandard Q Λ θ β E M hQ)
  map g := ModuleCat.ofHom (cutSpectStandardMap Q Λ θ β hQ g.hom)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun z =>
    LinearMap.congr_fun (cutStandardMap_id Q Λ θ β) z)
  map_comp g g' := ModuleCat.hom_ext (LinearMap.ext fun z =>
    cutStandardMap_comp Q Λ θ β (cutSpectInputHom Q Λ θ β g.hom)
      (cutSpectInputHom Q Λ θ β g'.hom) z)

/-- Partial standardization at a cut with a spectator is exact. -/
theorem moduleExactFunctor_cutSpectFunctor :
    ModuleExactFunctor (cutSpectFunctor Q Λ θ β E hQ) :=
  ⟨fun f g h => cutSpectStandardMap_exact Q Λ θ β hQ f.hom g.hom h,
    fun f h => cutSpectStandardMap_injective Q Λ θ β hQ f.hom h,
    fun f h => cutSpectStandardMap_surjective Q Λ θ β hQ f.hom h⟩

end Functor

/-! ### Singleton blocks -/

section Singletons

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The tensor product algebra of the last red strand. -/
abbrev singLast {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I) :=
  TensorProductAlgebra k Q (Λ ∘ Fin.natAdd n) (θ (Fin.last n))

/-- **The algebra of the singleton blocks** `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n)`, nested to the
left and starting from the tensor product algebra `T^∅(0)` of no red strands. -/
def singAlg : (n : ℕ) → (Fin n → I →₀ ℕ) → (Fin n → Multiset I) → AlgCat.{u} k
  | 0, Λ, _ => AlgCat.of k (TensorProductAlgebra k Q Λ 0)
  | n + 1, Λ, θ => AlgCat.of k
      (singAlg n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k] singLast Q Λ θ)

/-- The total weight `θ_1 + ⋯ + θ_n` of the singleton blocks. -/
def singWeight : (n : ℕ) → (Fin n → Multiset I) → Multiset I
  | 0, _ => 0
  | n + 1, θ => singWeight n (θ ∘ Fin.castSucc) + θ (Fin.last n)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable (hQ : KLRSymm Q)

/-- The associator `A ⊗ (B ⊗ E) → (A ⊗ B) ⊗ E` of the first stage. -/
def singAssocIn (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) :
    (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k]
      (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) →+*
      (singAlg Q (n + 1) Λ θ ⊗[k] E) :=
  (Algebra.TensorProduct.assoc k k k (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc))
    (singLast Q Λ θ) E).symm.toAlgHom.toRingHom

/-- The associator `(A ⊗ B) ⊗ E → A ⊗ (B ⊗ E)` of the last stage. -/
def singAssocOut (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) :
    cutSpectAlgebra (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E →+*
      (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
        (AlgCat.of k (singLast Q Λ θ ⊗[k] E) : AlgCat.{u} k)) :=
  (Algebra.TensorProduct.assoc k k k
    (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)))
    (singLast Q Λ θ) E).toAlgHom.toRingHom

/-- **The standardization with singleton blocks, in stages**, with a spectator `E`: a functor
from modules over `T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_n}(θ_n) ⊗ E` to modules over
`T^λ(θ_1 + ⋯ + θ_n) ⊗ E`. The first `n - 1` blocks are standardized with the last block as
a further spectator, and the result is standardized at the cut before the last red strand. -/
def singStd : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) →
    ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E) ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q Λ (singWeight n θ) ⊗[k] E)
  | 0, _, _, _ => 𝟭 _
  | n + 1, Λ, θ, E =>
    ModuleCat.restrictScalars.{u} (singAssocIn Q n Λ θ E) ⋙
      singStd n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (AlgCat.of k (singLast Q Λ θ ⊗[k] E)) ⋙
      ModuleCat.restrictScalars.{u} (singAssocOut Q n Λ θ E) ⋙
      cutSpectFunctor (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ

/-- **The standardization in stages is exact.** -/
theorem moduleExactFunctor_singStd : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) →
    (θ : Fin n → Multiset I) → (E : AlgCat.{u} k) →
    ModuleExactFunctor (singStd Q hQ n Λ θ E)
  | 0, _, _, _ => ModuleExactFunctor.id
  | n + 1, _, _, _ =>
    (ModuleExactFunctor.restrictScalars _).comp
      ((moduleExactFunctor_singStd n _ _ _).comp
        ((ModuleExactFunctor.restrictScalars _).comp
          (moduleExactFunctor_cutSpectFunctor _ _ _ _ _ hQ)))

end Singletons

end Categorification.Stendhal
