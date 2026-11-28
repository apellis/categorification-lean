/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TriangleChainHomology
import Categorification.Algebra.DerivedTensorCoefficientExact
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.DerivedTensorTriangulated
import Categorification.Algebra.OrdinaryProjectiveResolutionDG
import Categorification.Algebra.ProjectiveResolutionDGProjective
import Categorification.Algebra.DerivedTensorOrdinaryLinear

/-!
# Derived tensor products of two modules with finite resolutions

Let `X` be a right `B`-module (a `(k, B)`-bimodule, the coefficient) with a finite resolution
`0 → M_N → ⋯ → M_0 → X → 0`, and `Y` a left `B`-module with a finite resolution
`0 → N_{N'} → ⋯ → N_0 → Y → 0`, both given through their syzygies
(`CoefficientSyzygyChain`, `ModuleSyzygyChain`). If every `M_i ⊗ᴸ_B N_j` vanishes except
`M_{i₀} ⊗ᴸ_B N_{j₀}`, then
`Hⁿ(X ⊗ᴸ_B Y) ≅ H^{n + i₀ + j₀}(M_{i₀} ⊗ᴸ_B N_{j₀})`
(`nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`).

This is the dévissage that replaces the spectral sequence of the tensor product of two
resolutions in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22: there both factors are resolved by
Proposition 7.8 and all but one term of the `E²` page vanish. The resolutions are inputs here,
so that Proposition 7.8 can be supplied later.

## Main definitions and results

* `CoefficientModule`: a bundled `(k, B)`-bimodule, the coefficient of `- ⊗ᴸ_B -`.
* `ModuleSyzygyChain`, `ModuleSyzygyChain.toTriangleChain`: a finite resolution of a left
  module through its syzygies, and its chain of triangles in `D(B)`.
* `CoefficientSyzygyChain`, `CoefficientSyzygyChain.toTriangleChain`: the same for a
  coefficient, and the chain of triangles in `D(k)` obtained by tensoring with a K-projective
  resolution of a fixed left module.
* `nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`,
  `isZero_derivedTensorHomology_of_syzygyChains`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

/-- A bundled `(A, B)`-bimodule: the coefficient `M` of the derived tensor product
`M ⊗ᴸ_B - : D(B) ⥤ D(A)`. -/
structure CoefficientModule (A B : Type) [Ring A] [Ring B] where
  /-- The underlying type. -/
  carrier : Type
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  [isModuleOp : Module Bᵐᵒᵖ carrier]
  [isSMulCommClass : SMulCommClass A Bᵐᵒᵖ carrier]

attribute [instance] CoefficientModule.isAddCommGroup CoefficientModule.isModule
  CoefficientModule.isModuleOp CoefficientModule.isSMulCommClass

instance {A B : Type} [Ring A] [Ring B] : CoeSort (CoefficientModule A B) Type :=
  ⟨CoefficientModule.carrier⟩

/-- A finite resolution `0 → M_N → ⋯ → M_0 → Ω_0 → 0` of a left `B`-module, through its
syzygies: short exact sequences `0 → Ω_{i+1} → M_i → Ω_i → 0` for `i ≤ N`, with
`Ω_{N+1} = 0`. -/
structure ModuleSyzygyChain (B : Type) [Ring B] where
  /-- The length `N`. -/
  length : ℕ
  /-- The terms `M_i`. -/
  term : ℕ → ModuleCat.{0} B
  /-- The syzygies `Ω_i`; `Ω_0` is the resolved module. -/
  syz : ℕ → ModuleCat.{0} B
  /-- The inclusion `Ω_{i+1} → M_i`. -/
  ι : ∀ i, syz (i + 1) →ₗ[B] term i
  /-- The projection `M_i → Ω_i`. -/
  π : ∀ i, term i →ₗ[B] syz i
  injective : ∀ i ≤ length, Function.Injective (ι i)
  exact : ∀ i ≤ length, Function.Exact (ι i) (π i)
  surjective : ∀ i ≤ length, Function.Surjective (π i)
  subsingleton_syz : Subsingleton (syz (length + 1))

/-- A finite resolution of a coefficient `(A, B)`-bimodule through its syzygies, as in
`ModuleSyzygyChain`; the maps are `A`-linear and commute with the right action of `B`. -/
structure CoefficientSyzygyChain (A B : Type) [Ring A] [Ring B] where
  /-- The length `N`. -/
  length : ℕ
  /-- The terms `M_i`. -/
  term : ℕ → CoefficientModule A B
  /-- The syzygies `Ω_i`; `Ω_0` is the resolved coefficient. -/
  syz : ℕ → CoefficientModule A B
  /-- The inclusion `Ω_{i+1} → M_i`. -/
  ι : ∀ i, syz (i + 1) →ₗ[A] term i
  /-- The projection `M_i → Ω_i`. -/
  π : ∀ i, term i →ₗ[A] syz i
  ι_op : ∀ i (b : B) (m : syz (i + 1)), ι i (op b • m) = op b • ι i m
  π_op : ∀ i (b : B) (m : term i), π i (op b • m) = op b • π i m
  injective : ∀ i ≤ length, Function.Injective (ι i)
  exact : ∀ i ≤ length, Function.Exact (ι i) (π i)
  surjective : ∀ i ≤ length, Function.Surjective (π i)
  subsingleton_syz : Subsingleton (syz (length + 1))

namespace ModuleSyzygyChain

variable {B : Type} [Ring B] (c : ModuleSyzygyChain B)

/-- The short complex `Ω_{i+1} → M_i → Ω_i`. -/
def shortComplex (i : ℕ) (hi : i ≤ c.length) : ShortComplex (ModuleCat.{0} B) :=
  ShortComplex.mk (ModuleCat.ofHom (c.ι i)) (ModuleCat.ofHom (c.π i)) (by
    ext x
    exact (c.exact i hi).apply_apply_eq_zero x)

theorem shortComplex_shortExact (i : ℕ) (hi : i ≤ c.length) :
    (c.shortComplex i hi).ShortExact := by
  let : Mono (c.shortComplex i hi).f := (ModuleCat.mono_iff_injective _).mpr (c.injective i hi)
  let : Epi (c.shortComplex i hi).g := (ModuleCat.epi_iff_surjective _).mpr (c.surjective i hi)
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (c.exact i hi)⟩

variable [HasDerivedCategory.{w, 0} B]

theorem exists_distinguished (i : ℕ) (hi : i ≤ c.length) :
    ∃ δ : Q.obj ((degreeZeroModuleFunctor B).obj (c.syz i)) ⟶
        (Q.obj ((degreeZeroModuleFunctor B).obj (c.syz (i + 1))))⟦(1 : ℤ)⟧,
      Triangle.mk (Q.map ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom (c.ι i))))
        (Q.map ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom (c.π i)))) δ ∈
        distTriang (DerivedCategory.{w, 0} B) :=
  exists_distinguished_of_shortExact ((c.shortComplex i hi).map (degreeZeroModuleFunctor B))
    (degreeZeroModuleFunctor_shortExact _ (c.shortComplex_shortExact i hi))

/-- The chain of distinguished triangles in `D(B)` of the syzygies, modules in degree zero. -/
def toTriangleChain : TriangleChain (DerivedCategory.{w, 0} B) where
  length := c.length
  term i := Q.obj ((degreeZeroModuleFunctor B).obj (c.term i))
  syz i := Q.obj ((degreeZeroModuleFunctor B).obj (c.syz i))
  ι i := Q.map ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom (c.ι i)))
  π i := Q.map ((degreeZeroModuleFunctor B).map (ModuleCat.ofHom (c.π i)))
  δ i := if hi : i ≤ c.length then (c.exists_distinguished i hi).choose else 0
  dist i hi := by
    split_ifs
    exact (c.exists_distinguished i hi).choose_spec
  isZero_syz := Q.map_isZero ((degreeZeroModuleFunctor B).map_isZero
    (ModuleCat.isZero_iff_subsingleton.mpr c.subsingleton_syz))

@[simp] theorem toTriangleChain_length : (c.toTriangleChain.{w}).length = c.length := rfl

end ModuleSyzygyChain

namespace CoefficientSyzygyChain

variable {A B : Type} [Ring A] [Ring B] (c : CoefficientSyzygyChain A B)
  {P : DGModuleCat.{0} B} [Module.Projective B P]

/-- The short exact sequence `Ω_{i+1} ⊗_B P → M_i ⊗_B P → Ω_i ⊗_B P` of dg `A`-modules, for a
dg module `P` with projective underlying module. -/
def shortComplex (P : DGModuleCat.{0} B) (i : ℕ) (hi : i ≤ c.length) :
    ShortComplex (DGModuleCat.{0} A) :=
  coefficientTensorComplex (c.ι i) (c.ι_op i) (c.π i) (c.π_op i)
    (LinearMap.ext fun x => (c.exact i hi).apply_apply_eq_zero x) P

theorem shortComplex_shortExact (i : ℕ) (hi : i ≤ c.length) :
    (c.shortComplex P i hi).ShortExact :=
  coefficientTensor_shortExact _ _ _ _ _ (c.injective i hi) (c.exact i hi)
    (c.surjective i hi) P

variable [HasDerivedCategory.{w, 0} A]

variable (P) in
theorem exists_distinguished (i : ℕ) (hi : i ≤ c.length) :
    ∃ δ : Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero (c.syz i))).obj P) ⟶
        (Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero (c.syz (i + 1)))).obj P))⟦(1 : ℤ)⟧,
      Triangle.mk (Q.map ((ordinaryTensorCoefficientMap (c.ι i) (c.ι_op i)).app P))
        (Q.map ((ordinaryTensorCoefficientMap (c.π i) (c.π_op i)).app P)) δ ∈
        distTriang (DerivedCategory.{w, 0} A) :=
  exists_distinguished_of_shortExact _ (c.shortComplex_shortExact i hi)

variable (P) in
/-- The chain of distinguished triangles in `D(A)` of the dg modules `Ω_i ⊗_B P`, `M_i ⊗_B P`,
for a dg module `P` with projective underlying module. -/
def toTriangleChain : TriangleChain (DerivedCategory.{w, 0} A) where
  length := c.length
  term i := Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero (c.term i))).obj P)
  syz i := Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero (c.syz i))).obj P)
  ι i := Q.map ((ordinaryTensorCoefficientMap (c.ι i) (c.ι_op i)).app P)
  π i := Q.map ((ordinaryTensorCoefficientMap (c.π i) (c.π_op i)).app P)
  δ i := if hi : i ≤ c.length then (c.exists_distinguished P i hi).choose else 0
  dist i hi := by
    split_ifs
    exact (c.exists_distinguished P i hi).choose_spec
  isZero_syz := by
    have hs : Subsingleton (c.syz (c.length + 1)) := c.subsingleton_syz
    have hz : ∀ z : TensorProductOver B (InDegreeZero (c.syz (c.length + 1))) P, z = 0 :=
      fun z => by
        induction z using TensorProductOver.induction_on with
        | zero => rfl
        | tmul m n =>
          rw [show m = 0 from hs.elim _ _, TensorProductOver.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
    have : Subsingleton ((DGModuleCat.tensorFunctor A
        (InDegreeZero (c.syz (c.length + 1)))).obj P) :=
      ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact Q.map_isZero (DGModuleCat.isZero_of_subsingleton _)

end CoefficientSyzygyChain

/-! ### Dévissage of the derived tensor product -/

section Devissage

variable {k B : Type} [CommRing k] [Ring B] [HasDerivedCategory.{w, 0} k]
  [HasDerivedCategory.{w, 0} B]

namespace ModuleSyzygyChain

variable (c : ModuleSyzygyChain B) (M : Type) [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M]
  [SMulCommClass k Bᵐᵒᵖ M]

/-- If `M ⊗ᴸ_B M_j` has no cohomology for every term, neither has `M ⊗ᴸ_B Ω_0`. -/
theorem isZero_derivedTensorHomology
    (h : ∀ j ≤ c.length, ∀ n : ℤ, IsZero ((homologyFunctor (A := k) k n).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj (c.term j))))))
    (n : ℤ) :
    IsZero ((homologyFunctor (A := k) k n).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj (c.syz 0))))) :=
  (c.toTriangleChain.{w}.map (derivedTensor.{w} k B M)).isZero_homology_syz (a := 0)
    (Nat.zero_le _) (fun j _ hj => h j hj) n

/-- **Dimension shift along a resolution of the module**: if `M ⊗ᴸ_B M_j` has no cohomology
for `j ≠ j₀`, then `Hⁿ(M ⊗ᴸ_B Ω_0) ≅ H^{n + j₀}(M ⊗ᴸ_B M_{j₀})`. -/
theorem nonempty_linearEquiv_derivedTensorHomology {j₀ : ℕ} (hj₀ : j₀ ≤ c.length)
    (h : ∀ j ≤ c.length, j ≠ j₀ → ∀ n : ℤ, IsZero ((homologyFunctor (A := k) k n).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj (c.term j))))))
    (n : ℤ) :
    Nonempty ((homologyFunctor (A := k) k n).obj
        ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj (c.syz 0)))) ≃ₗ[k]
      (homologyFunctor (A := k) k (n + j₀)).obj
        ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj (c.term j₀))))) :=
  (c.toTriangleChain.{w}.map (derivedTensor.{w} k B M)).nonempty_linearEquiv_homology hj₀ h n

end ModuleSyzygyChain

/-- The derived tensor cohomology of a coefficient against a K-projective resolution of `Y`,
compared with the derived tensor cohomology against `Y`. -/
def derivedTensorHomologyResolutionIso (M : CoefficientModule k B) (Y : ModuleCat.{0} B)
    (n : ℤ) :
    (homologyFunctor (A := k) k n).obj (Q.obj ((DGModuleCat.tensorFunctor k (InDegreeZero M)).obj
        (projectiveResolutionDGModel (projectiveResolution Y)))) ≅
      (homologyFunctor (A := k) k n).obj
        ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y))) := by
  let R := projectiveResolution Y
  exact (homologyFunctor (A := k) k n).mapIso
    ((derivedTensorObjIso (projectiveResolutionDGModel_kProjective R)).symm ≪≫
      (derivedTensor.{w} k B M).mapIso
        (@asIso _ _ _ _ (Q.map (projectiveResolutionDGAugToOrdinary R))
        ((isIso_Q_map_iff _).mpr (projectiveResolutionDGAugToOrdinary_quasiIso R))))

/-- **Dévissage of `X ⊗ᴸ_B Y` along two finite resolutions** (the single nonzero `E²` term of
the spectral sequence in B. Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): let
`X = Ω_0` have a resolution by coefficients `M_i` and `Y = Ω'_0` one by modules `N_j`. If
`M_i ⊗ᴸ_B N_j` has no cohomology unless `(i, j) = (i₀, j₀)`, then
`Hⁿ(X ⊗ᴸ_B Y) ≅ H^{n + i₀ + j₀}(M_{i₀} ⊗ᴸ_B N_{j₀})`. -/
theorem nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains
    (X : CoefficientSyzygyChain k B) (Y : ModuleSyzygyChain B) {i₀ j₀ : ℕ}
    (hi₀ : i₀ ≤ X.length) (hj₀ : j₀ ≤ Y.length)
    (h : ∀ i ≤ X.length, ∀ j ≤ Y.length, (i ≠ i₀ ∨ j ≠ j₀) → ∀ n : ℤ,
      IsZero ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.term i)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.term j))))))
    (n : ℤ) :
    Nonempty ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.syz 0)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.syz 0)))) ≃ₗ[k]
      (homologyFunctor (A := k) k (n + i₀ + j₀)).obj ((derivedTensor.{w} k B (X.term i₀)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.term j₀))))) := by
  let P := projectiveResolutionDGModel (projectiveResolution (Y.syz 0))
  let cX := X.toTriangleChain.{w} P
  have hterm : ∀ i ≤ cX.length, i ≠ i₀ → ∀ m : ℤ,
      IsZero ((homologyFunctor (A := k) k m).obj (cX.term i)) := fun i hi hii m =>
    (Y.isZero_derivedTensorHomology (X.term i) (fun j hj => h i hi j hj (Or.inl hii)) m).of_iso
      (derivedTensorHomologyResolutionIso (X.term i) (Y.syz 0) m)
  obtain ⟨e₁⟩ := cX.nonempty_linearEquiv_homology hi₀ hterm n
  obtain ⟨e₂⟩ := Y.nonempty_linearEquiv_derivedTensorHomology (X.term i₀) hj₀
    (fun j hj hjj => h i₀ hi₀ j hj (Or.inr hjj)) (n + i₀)
  exact ⟨(derivedTensorHomologyResolutionIso (X.syz 0) (Y.syz 0) n).toLinearEquiv.symm.trans
    (e₁.trans
      ((derivedTensorHomologyResolutionIso (X.term i₀) (Y.syz 0) (n + i₀)).toLinearEquiv.trans
        e₂))⟩

/-- **Concentration of `X ⊗ᴸ_B Y`**: under the hypotheses of
`nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`, if moreover the higher Tor of
`M_{i₀}` and `N_{j₀}` vanish, then `X ⊗ᴸ_B Y` has cohomology only in degree `-(i₀ + j₀)`, where
it is `M_{i₀} ⊗_B N_{j₀}`. -/
theorem isZero_derivedTensorHomology_of_syzygyChains
    (X : CoefficientSyzygyChain k B) (Y : ModuleSyzygyChain B) {i₀ j₀ : ℕ}
    (hi₀ : i₀ ≤ X.length) (hj₀ : j₀ ≤ Y.length)
    (h : ∀ i ≤ X.length, ∀ j ≤ Y.length, (i ≠ i₀ ∨ j ≠ j₀) → ∀ n : ℤ,
      IsZero ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.term i)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.term j))))))
    (h₀ : ∀ n : ℤ, n ≠ 0 →
      IsZero ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.term i₀)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.term j₀))))))
    (n : ℤ) (hn : n ≠ -((i₀ + j₀ : ℕ) : ℤ)) :
    IsZero ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.syz 0)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.syz 0))))) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains X Y hi₀ hj₀ h n
  exact (h₀ _ (by push_cast at hn ⊢; lia)).of_iso (LinearEquiv.toModuleIso e)

/-- The top degree of `nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`:
`H^{-(i₀+j₀)}(X ⊗ᴸ_B Y) ≅ M_{i₀} ⊗_B N_{j₀}`, the ordinary tensor product. -/
theorem nonempty_linearEquiv_tensorProductOver_of_syzygyChains
    (X : CoefficientSyzygyChain k B) (Y : ModuleSyzygyChain B) {i₀ j₀ : ℕ}
    (hi₀ : i₀ ≤ X.length) (hj₀ : j₀ ≤ Y.length)
    (h : ∀ i ≤ X.length, ∀ j ≤ Y.length, (i ≠ i₀ ∨ j ≠ j₀) → ∀ n : ℤ,
      IsZero ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.term i)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.term j)))))) :
    Nonempty ((homologyFunctor (A := k) k (-((i₀ + j₀ : ℕ) : ℤ))).obj
        ((derivedTensor.{w} k B (X.syz 0)).obj
          (Q.obj ((degreeZeroModuleFunctor B).obj (Y.syz 0)))) ≃ₗ[k]
      TensorProductOver B (X.term i₀) (Y.term j₀)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains X Y hi₀ hj₀ h
    (-((i₀ + j₀ : ℕ) : ℤ))
  have h0 : -((i₀ + j₀ : ℕ) : ℤ) + i₀ + j₀ = 0 := by push_cast; ring
  rw [h0] at e
  exact ⟨e.trans (ambientDerivedTensorH0Equiv (k := k) (A := B) (N := X.term i₀) (Y.term j₀))⟩

/-- The additive form of `nonempty_linearEquiv_tensorProductOver_of_syzygyChains`, which does not
mention the `k`-module structure of the tensor product (useful for `k = ℤ`, where that structure
is not definitionally the canonical one). -/
theorem nonempty_addEquiv_tensorProductOver_of_syzygyChains
    (X : CoefficientSyzygyChain k B) (Y : ModuleSyzygyChain B) {i₀ j₀ : ℕ}
    (hi₀ : i₀ ≤ X.length) (hj₀ : j₀ ≤ Y.length)
    (h : ∀ i ≤ X.length, ∀ j ≤ Y.length, (i ≠ i₀ ∨ j ≠ j₀) → ∀ n : ℤ,
      IsZero ((homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B (X.term i)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (Y.term j)))))) :
    Nonempty ((homologyFunctor (A := k) k (-((i₀ + j₀ : ℕ) : ℤ))).obj
        ((derivedTensor.{w} k B (X.syz 0)).obj
          (Q.obj ((degreeZeroModuleFunctor B).obj (Y.syz 0)))) ≃+
      TensorProductOver B (X.term i₀) (Y.term j₀)) :=
  (nonempty_linearEquiv_tensorProductOver_of_syzygyChains X Y hi₀ hj₀ h).map
    LinearEquiv.toAddEquiv

end Devissage

end Categorification
