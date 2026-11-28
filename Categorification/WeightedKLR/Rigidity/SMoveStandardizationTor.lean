/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorAcyclicCover
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorFiltration
import Categorification.WeightedKLR.RedStrands.Prop55DimensionFirstFactor

/-!
# Tor against standardizations of finite-dimensional modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. The resolutions of Proposition 7.8 have as terms sums of standardizations
`S(N)` of finite-dimensional modules `N` over the factor algebra `D_{θ,β}` of a split
`θ + β = ν` (not sums of standard modules). The vanishing of the `E²` terms needs Tor against
such `S(N)`. Here it is reduced to the single module `S(D_{θ,β})`: standardization is exact
(Proposition 5.7, `parabolicStandardMap_exact`), every finite-dimensional `N` is a quotient of
a free module `D^{n+1}` with finite-dimensional kernel, and Tor-acyclicity passes to extensions,
so the dimension shift of `torAcyclic_of_acyclicCovers` applies.

## Main results

* `stdLayer_shortExact`: standardization of a short exact sequence of factor modules.
* `torAcyclic_stdLayer_free`: `S(D^{n+1})` is Tor-acyclic if `S(D)` is.
* `torAcyclic_stdLayer_of_finiteDimensional`: `S(N)` is Tor-acyclic for every
  finite-dimensional `N` if `S(D)` is.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated KLR
open DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

section Extension

variable {k B : Type} [CommRing k] [Ring B] [HasDerivedCategory.{w, 0} k]
  [HasDerivedCategory.{w, 0} B]
  (N : Type) [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [SMulCommClass k Bᵐᵒᵖ N]

/-- Tor-acyclicity is invariant under isomorphism. -/
theorem TorAcyclic.of_iso {Y Y' : ModuleCat.{0} B} (e : Y ≅ Y')
    (h : TorAcyclic.{w} (k := k) N Y) : TorAcyclic.{w} (k := k) N Y' := fun n =>
  (h n).of_iso ((homologyFunctor (A := k) k n).mapIso
    ((derivedTensor.{w} k B N).mapIso (Q.mapIso ((degreeZeroModuleFunctor B).mapIso e)))).symm

/-- **Tor-acyclicity passes to extensions.** -/
theorem TorAcyclic.of_shortExact {S : ShortComplex (ModuleCat.{0} B)} (hS : S.ShortExact)
    (h₁ : TorAcyclic.{w} (k := k) N S.X₁) (h₃ : TorAcyclic.{w} (k := k) N S.X₃) :
    TorAcyclic.{w} (k := k) N S.X₂ := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact
    (S.map (degreeZeroModuleFunctor B)) (degreeZeroModuleFunctor_shortExact _ hS)
  let T := (derivedTensor.{w} k B N).mapTriangle.obj
    (Triangle.mk (Q.map (S.map (degreeZeroModuleFunctor B)).f)
      (Q.map (S.map (degreeZeroModuleFunctor B)).g) δ)
  have hT' : T ∈ distTriang _ := (derivedTensor.{w} k B N).map_distinguished _ hT
  intro n
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_obj₂_of_isZero_obj₁ T hT' h₁ n
  have : Subsingleton ((homologyFunctor (A := k) k n).obj T.obj₃) :=
    ModuleCat.isZero_iff_subsingleton.mp (h₃ n)
  exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton

end Extension

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  {θ β ν : Multiset I} (h : θ + β = ν)

local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- The factor module of a module over the factor algebra. -/
abbrev factorOf (X : Type) [AddCommGroup X] [Module k X] [Module D X] [IsScalarTower k D X] :
    FactorModule Q Λ θ β :=
  ⟨X⟩

/-- **Standardization of a short exact sequence** (Webster, arXiv:1309.3796v3,
Proposition 5.7, for the induced model). -/
theorem stdLayer_shortExact {M₁ M₂ M₃ : FactorModule Q Λ θ β}
    (f : M₁.carrier →ₗ[D] M₂.carrier) (g : M₂.carrier →ₗ[D] M₃.carrier)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (ShortComplex.mk (ModuleCat.ofHom (stdLayerMap Q Λ hQ h f))
      (ModuleCat.ofHom (stdLayerMap Q Λ hQ h g)) (by
        ext x
        exact (parabolicStandardMap_exact Q Λ θ β hQ f g hfg).apply_apply_eq_zero x)
      ).ShortExact := by
  let S := ShortComplex.mk (ModuleCat.ofHom (stdLayerMap Q Λ hQ h f))
    (ModuleCat.ofHom (stdLayerMap Q Λ hQ h g)) (by
      ext x
      exact (parabolicStandardMap_exact Q Λ θ β hQ f g hfg).apply_apply_eq_zero x)
  have : Mono S.f := (ModuleCat.mono_iff_injective _).mpr
    (parabolicStandardMap_injective Q Λ θ β hQ f hf)
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr
    (parabolicStandardMap_surjective Q Λ θ β hQ g hg)
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (parabolicStandardMap_exact Q Λ θ β hQ f g hfg)⟩

/-- A finite-dimensional factor module is a quotient of a free module `D^{n+1}`. -/
theorem exists_free_surjective (M : FactorModule Q Λ θ β) [FiniteDimensional k M.carrier] :
    ∃ (n : ℕ) (π : (Fin (n + 1) → D) →ₗ[D] M.carrier), Function.Surjective π := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := k) (M := M.carrier)
  let s' : Fin (n + 1) → M.carrier := Fin.cons 0 s
  refine ⟨n, Fintype.linearCombination D s', ?_⟩
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span k (Set.range s) := hs ▸ Submodule.mem_top
  have hle : Submodule.span k (Set.range s) ≤
      (Submodule.span D (Set.range s')).restrictScalars k := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.succ, by simp [s']⟩
  exact hle hx

/-- Standardization of an isomorphism of factor modules, as an isomorphism of modules. -/
def stdLayerIso {M M' : FactorModule Q Λ θ β}
    (e : M.carrier ≃ₗ[D] M'.carrier) :
    stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩ ≅ stdLayerModule Q Λ hQ ⟨θ, β, h, M'⟩ where
  hom :=
    letI := StdLayer.instModule Q Λ hQ ⟨θ, β, h, M⟩
    letI := StdLayer.instModule Q Λ hQ ⟨θ, β, h, M'⟩
    ModuleCat.ofHom (stdLayerEquiv Q Λ hQ h e).toLinearMap
  inv :=
    letI := StdLayer.instModule Q Λ hQ ⟨θ, β, h, M⟩
    letI := StdLayer.instModule Q Λ hQ ⟨θ, β, h, M'⟩
    ModuleCat.ofHom (stdLayerEquiv Q Λ hQ h e).symm.toLinearMap
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (stdLayerEquiv Q Λ hQ h e).symm_apply_apply x)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (stdLayerEquiv Q Λ hQ h e).apply_symm_apply x)

section Tor

variable [HasDerivedCategory.{w, 0} k]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)]
  (N : Type) [AddCommGroup N] [Module k N] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ N]

/-- The standardization `S(X)` of a module over the factor algebra. -/
abbrev stdOf (X : Type) [AddCommGroup X] [Module k X] [Module D X] [IsScalarTower k D X] :
    ModuleCat.{0} T :=
  stdLayerModule Q Λ hQ ⟨θ, β, h, factorOf Q Λ X⟩

include hQ in
/-- **Standardizations of free factor modules**: if `S(D)` is Tor-acyclic, so is
`S(D^{n+1})`. -/
theorem torAcyclic_stdLayer_free (hD : TorAcyclic.{w} (k := k) N (stdOf Q Λ hQ h D)) :
    ∀ n : ℕ, TorAcyclic.{w} (k := k) N (stdOf Q Λ hQ h (Fin (n + 1) → D)) := by
  intro n
  induction n with
  | zero =>
    exact TorAcyclic.of_iso N
      (stdLayerIso Q Λ hQ h (M := factorOf Q Λ D) (M' := factorOf Q Λ (Fin 1 → D))
        (LinearEquiv.funUnique (Fin 1) D D).symm) hD
  | succ n ih =>
    let F := Fin (n + 1) → D
    have hS := stdLayer_shortExact Q Λ hQ h (M₁ := factorOf Q Λ F)
      (M₂ := factorOf Q Λ (D × F)) (M₃ := factorOf Q Λ D)
      (LinearMap.inr D D F) (LinearMap.fst D D F) LinearMap.inr_injective
      Function.Exact.inr_fst LinearMap.fst_surjective
    have hmid := TorAcyclic.of_shortExact N hS ih hD
    exact TorAcyclic.of_iso N
      (stdLayerIso Q Λ hQ h (M := factorOf Q Λ (D × F))
        (M' := factorOf Q Λ (Fin (n + 1 + 1) → D))
        (Fin.consLinearEquiv D (fun _ : Fin (n + 1 + 1) => D))) hmid

include hQ in
/-- **Tor against standardizations of finite-dimensional modules** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the `E²` terms for resolutions by
standardizations): for Rouquier parameters, if `S(D_{θ,β})` is Tor-acyclic against `N`, so is
`S(M)` for every finite-dimensional module `M` over `D_{θ,β}`. -/
theorem torAcyclic_stdLayer_of_finiteDimensional {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q) (hD : TorAcyclic.{w} (k := k) N (stdOf Q Λ hQ h D))
    (M : FactorModule Q Λ θ β) [FiniteDimensional k M.carrier] :
    TorAcyclic.{w} (k := k) N (stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩) := by
  have hDf : Module.Finite k D :=
    Subsingleton.elim (fun a b => Classical.propDecidable (a = b)) ‹DecidableEq I› ▸
      module_finite_parabolicFactorAlgebra_of_rouquier (Λ := Λ) hR θ β
  let 𝒞 : ModuleCat.{0} T → Prop := fun Y => ∃ M : FactorModule Q Λ θ β,
    FiniteDimensional k M.carrier ∧ Nonempty (Y ≅ stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩)
  refine torAcyclic_of_acyclicCovers N 𝒞 ?_ _ ⟨M, inferInstance, ⟨Iso.refl _⟩⟩
  rintro Y ⟨M, hM, ⟨i⟩⟩
  obtain ⟨n, π, hπ⟩ := exists_free_surjective Q Λ M
  let K := LinearMap.ker π
  have : Module.Finite k (Fin (n + 1) → D) := Module.Finite.pi (h := fun _ => hDf)
  have hKfin : FiniteDimensional k K :=
    FiniteDimensional.finiteDimensional_submodule (K.restrictScalars k)
  have hS := stdLayer_shortExact Q Λ hQ h (M₁ := factorOf Q Λ K)
    (M₂ := factorOf Q Λ (Fin (n + 1) → D)) (M₃ := M) K.subtype π Subtype.val_injective
    (LinearMap.exact_subtype_ker_map π) hπ
  exact ⟨_, hS, ⟨factorOf Q Λ K, hKfin, ⟨Iso.refl _⟩⟩,
    torAcyclic_stdLayer_free Q Λ hQ h N hD n, ⟨i.symm⟩⟩

end Tor

end Categorification.Stendhal
