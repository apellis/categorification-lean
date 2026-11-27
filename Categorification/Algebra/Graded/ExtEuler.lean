/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.EulerCharacteristic
import Categorification.Algebra.ExtShortExact
import Categorification.Algebra.Graded.Duality
import Categorification.KLR.Crystal.Thm317Graded

set_option backward.isDefEq.respectTransparency false

/-!
# Hom dimensions from a projective resolution when higher Ext vanish

Let `N` have a finite projective resolution `0 → P_n → ⋯ → P_0 → N → 0` by graded projectives
over `A` (`GFin.Resolution`), and let `Ext^{n}(N, N') = 0` for `n > 0`, computed in the derived
category of a ring `R ≅ A`. Then `dim Hom(N, N') = Σ_j (-1)^j dim Hom(P_j, N')`
(`finrank_hom_eq_altSum`), and each `dim Hom(P_j, N')` is a graded dimension at `q = 1`
(`finrank_hom_eq_evalOne_gdimPoly`). This is the Euler-characteristic count in Webster,
arXiv:1309.3796v3, proof of Theorem 6.15: the dimension of `Hom` between tilting modules is
read off their classes.
-/

noncomputable section

namespace Categorification.Graded

open CategoryTheory DG DG.DerivedCategory Module
open scoped DG.DegreeZero

variable {k : Type} [Field k] {A : Type} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  {R : Type} [Ring R] (φ : A ≃+* R)

/-- A module over `A` as a module over `R` along `φ : A ≃ R`. -/
abbrev resModule (M : GFin 𝒜) : ModuleCat.{0} R :=
  (ModuleCat.restrictScalars φ.symm.toRingHom).obj (ModuleCat.of A M.carrier)

/-- Restriction along `φ⁻¹`, an equivalence `ModuleCat A ≌ ModuleCat R`. -/
abbrev resFunctor : ModuleCat.{0} A ⥤ ModuleCat.{0} R :=
  ModuleCat.restrictScalars φ.symm.toRingHom

/-- An `A`-linear map as an `R`-linear map. -/
abbrev resHom {M N : GFin 𝒜} (f : M.carrier →ₗ[A] N.carrier) : resModule φ M ⟶ resModule φ N :=
  (resFunctor φ).map (ModuleCat.ofHom f)

theorem projective_resModule (P : GFin 𝒜) [Module.Projective A P.carrier] :
    Module.Projective R (resModule φ P) := by
  have : Projective (ModuleCat.of A P.carrier) := inferInstance
  have : Projective (resModule φ P) := (resFunctor φ).projective_obj_of_projective this
  exact ModuleCat.projective_of_module_projective _

/-- A short exact sequence over `A` as a short complex. -/
abbrev toShortComplex {K P N : GFin 𝒜} (S : GFin.ShortExact K P N) : ShortComplex (ModuleCat.{0} A) :=
  ShortComplex.mk (ModuleCat.ofHom S.f) (ModuleCat.ofHom S.g) (by
    ext x
    exact S.exact.apply_apply_eq_zero x)

theorem toShortComplex_shortExact {K P N : GFin 𝒜} (S : GFin.ShortExact K P N) :
    (toShortComplex S).ShortExact := by
  have : Mono (toShortComplex S).f := (ModuleCat.mono_iff_injective _).mpr S.injective
  have : Epi (toShortComplex S).g := (ModuleCat.epi_iff_surjective _).mpr S.surjective
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr S.exact⟩

instance finiteDimensional_hom (M N : GFin 𝒜) : FiniteDimensional k (M.carrier →ₗ[A] N.carrier) :=
  let ρ : (M.carrier →ₗ[A] N.carrier) →ₗ[k] (M.carrier →ₗ[k] N.carrier) :=
    { toFun := fun f => f.restrictScalars k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  Module.Finite.of_injective ρ fun _ _ h => LinearMap.restrictScalars_injective k h

/-- `Hom(N, N') ≅ Hom(P, N')` along an isomorphism `N ≅ P`. -/
theorem finrank_hom_congr {N P : GFin 𝒜} (e : N.Iso P) (N' : GFin 𝒜) :
    finrank k (N.carrier →ₗ[A] N'.carrier) = finrank k (P.carrier →ₗ[A] N'.carrier) := by
  let E : N.carrier ≃ₗ[A] P.carrier := e.toLinearEquiv
  exact LinearEquiv.finrank_eq
    { toFun := fun f => f ∘ₗ E.symm.toLinearMap
      invFun := fun f => f ∘ₗ E.toLinearMap
      left_inv := fun f => LinearMap.ext fun x => by simp
      right_inv := fun f => LinearMap.ext fun x => by simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [Ring R] in
/-- **`dim Hom_A(P, N)` is the graded dimension of `HOM(P, N)` at `q = 1`** for `P` finitely
generated and `N` finite-dimensional over a finite-dimensional graded algebra. -/
theorem finrank_hom_eq_evalOne_gdimPoly [GradedAlgebra 𝒜] [Module.Finite k A] (P : GProj 𝒜)
    (N : GFin 𝒜) :
    (finrank k (P.carrier →ₗ[A] N.carrier) : ℤ) =
      evalOne (gdimPoly (homGrade A P.grading N.grading)) := by
  have : FiniteDimensional k P.carrier := Module.Finite.trans A P.carrier
  let := (isInternal_homGrade 𝒜 P.grading N.grading).chooseDecomposition
  have : FiniteDimensional k (P.carrier →ₗ[A] N.carrier) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A P.carrier N.carrier k)
      fun _ _ h => LinearMap.restrictScalars_injective k h
  rw [evalOne_gdimPoly]

variable [HasDerivedCategory.{0, 0} R]

/-- **Hom dimensions from a resolution** (Webster, arXiv:1309.3796v3, proof of Theorem 6.15): if
`N` has a resolution by projectives `l` and `Ext^{n+1}(N, N') = 0` for all `n ≥ 0` over
`R ≅ A`, then `dim Hom(N, N') = Σ_j (-1)^j dim Hom(l_j, N')`. -/
theorem finrank_hom_eq_altSum (N' : GFin 𝒜) :
    ∀ {N : GFin 𝒜} {l : List (GFin 𝒜)}, GFin.Resolution N l →
      (∀ P ∈ l, Module.Projective A P.carrier) →
      (∀ n : ℕ, ∀ f : Q.obj ((degreeZeroModuleFunctor R).obj (resModule φ N)) ⟶
        (Q.obj ((degreeZeroModuleFunctor R).obj (resModule φ N')))⟦(n : ℤ) + 1⟧, f = 0) →
      (finrank k (N.carrier →ₗ[A] N'.carrier) : ℤ) =
        altSum (l.map fun P => (finrank k (P.carrier →ₗ[A] N'.carrier) : ℤ))
  | _, _, .single e, _, _ => by
    rw [List.map_singleton, altSum_cons, altSum_nil, sub_zero, finrank_hom_congr e]
  | N, _, .cons (K := K) (P := P) (l := l) S r, hl, hext => by
    have hP : Module.Projective A P.carrier := hl P List.mem_cons_self
    let S' := (toShortComplex S).map (resFunctor φ)
    have : Module.Projective R S'.X₂ := projective_resModule φ P
    have hS : S'.ShortExact := (toShortComplex_shortExact S).map_of_exact (resFunctor φ)
    -- `Ext^{n+1}(K, N') = 0`.
    have hK : ∀ n : ℕ, ∀ f : Q.obj ((degreeZeroModuleFunctor R).obj (resModule φ K)) ⟶
        (Q.obj ((degreeZeroModuleFunctor R).obj (resModule φ N')))⟦(n : ℤ) + 1⟧, f = 0 :=
      fun n f => hom_shift_eq_zero_of_shortExact hS (resModule φ N') (by omega)
        (fun g => hext (n + 1) g) f
    have ih := finrank_hom_eq_altSum N' r (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)) hK
    -- `dim Hom(P, N') = dim Hom(N, N') + dim Hom(K, N')`.
    have hext' : ∀ u : K.carrier →ₗ[A] N'.carrier, ∃ h : P.carrier →ₗ[A] N'.carrier,
        h ∘ₗ S.f = u := fun u => by
      obtain ⟨h, hh⟩ := exists_comp_eq_of_shortExact hS (resModule φ N')
        (fun f => hext 0 f) (resHom φ u)
      let F := Functor.FullyFaithful.ofFullyFaithful (resFunctor φ)
      refine ⟨(F.preimage h).hom, ?_⟩
      have e : ModuleCat.ofHom S.f ≫ F.preimage h = ModuleCat.ofHom u :=
        F.map_injective (by rw [Functor.map_comp, F.map_preimage]; exact hh)
      exact congrArg ModuleCat.Hom.hom e
    have hdim := finrank_hom_eq_add_of_exact (k := k) S.f S.g S.surjective S.exact hext'
    rw [List.map_cons, altSum_cons, ← ih, hdim]
    push_cast
    ring

end Categorification.Graded
