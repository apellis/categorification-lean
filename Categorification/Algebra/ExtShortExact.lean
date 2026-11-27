/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DegreeZeroHeart
import Categorification.Algebra.ProjectiveKProjective
import DG.Derived.ConnectedK0
import DG.Derived.ShortExactTriangle

set_option backward.isDefEq.respectTransparency false

/-!
# Ext of modules in degree `0` along short exact sequences

For modules over a ring `R`, placed in degree `0` of the derived category `D(R)`, write
`Ext^n(X, Y) = Hom_{D(R)}(X, Y⟦n⟧)`. For a projective `P`, `Ext^n(P, Y) = 0` for `n ≠ 0`
(`hom_shift_eq_zero_of_projective`). For a short exact sequence `0 → K → P → X → 0` with `P`
projective:

* if `Ext^1(X, Y) = 0`, every map `K → Y` extends along `K → P` (`exists_comp_eq_of_shortExact`);
* if `Ext^{n+1}(X, Y) = 0` with `n ≥ 1`, then `Ext^n(K, Y) = 0` (`hom_shift_eq_zero_of_shortExact`).

Over a `k`-algebra, the first gives `dim Hom(P, Y) = dim Hom(X, Y) + dim Hom(K, Y)`
(`finrank_hom_eq_add_of_shortExact`). These are the dimension shifts behind the
Euler-characteristic count in Webster, arXiv:1309.3796v3, proof of Theorem 6.15.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

variable {R : Type} [Ring R]

/-- A cochain of nonzero degree between modules concentrated in degree `0` vanishes. -/
theorem cochain_inDegreeZero_eq_zero (X Y : ModuleCat.{0} R) {n : ℤ} (hn : n ≠ 0)
    (z : Cochain R (InDegreeZero X) (InDegreeZero Y) n) : z = 0 := Cochain.ext fun y => by
  have hy : y ∈ grading (M := InDegreeZero X) 0 := InDegreeZero.mem_grading_zero y
  have := (InDegreeZero.mem_grading_iff _).1 (z.map_mem hy)
  rcases this with h | h
  · omega
  · exact h

variable [HasDerivedCategory.{0, 0} R]

/-- **`Ext^n(P, Y) = 0` for `P` projective and `n ≠ 0`.** -/
theorem hom_shift_eq_zero_of_projective (P Y : ModuleCat.{0} R) [Module.Projective R P] {n : ℤ}
    (hn : n ≠ 0)
    (f : Q.obj ((degreeZeroModuleFunctor R).obj P) ⟶
      (Q.obj ((degreeZeroModuleFunctor R).obj Y))⟦n⟧) : f = 0 := by
  have hP : IsKProjective.{0} R ((degreeZeroModuleFunctor R).obj P) :=
    show IsKProjective R (InDegreeZero P) from InDegreeZero.isKProjective
  have : Subsingleton (cohomology (DGModule.HOM R ((degreeZeroModuleFunctor R).obj P)
      ((degreeZeroModuleFunctor R).obj Y)) n) := by
    refine ⟨fun a b => ?_⟩
    suffices ∀ a : cohomology (DGModule.HOM R ((degreeZeroModuleFunctor R).obj P)
        ((degreeZeroModuleFunctor R).obj Y)) n, a = 0 by
      rw [this a, this b]
    intro a
    induction a using cohomology.induction_on with
    | h x =>
      rw [cohomology.mk_eq_zero_iff]
      obtain ⟨⟨z, hz'⟩, -⟩ := x.2
      refine ⟨0, zero_mem _, ?_⟩
      rw [map_zero, ← hz', cochain_inDegreeZero_eq_zero P Y hn z, map_zero]
  exact (homShiftAddEquivOfIsKProjective hP ((degreeZeroModuleFunctor R).obj Y) n).injective
    (Subsingleton.elim _ _)

/-- A short exact sequence of modules gives a distinguished triangle in `D(R)`. -/
theorem exists_distinguished_of_shortExact_module (S : ShortComplex (ModuleCat.{0} R))
    (hS : S.ShortExact) :
    ∃ δ : Q.obj ((degreeZeroModuleFunctor R).obj S.X₃) ⟶
        (Q.obj ((degreeZeroModuleFunctor R).obj S.X₁))⟦(1 : ℤ)⟧,
      Triangle.mk (Q.map ((degreeZeroModuleFunctor R).map S.f))
        (Q.map ((degreeZeroModuleFunctor R).map S.g)) δ ∈ distTriang (DerivedCategory R) :=
  exists_distinguished_of_shortExact _ (degreeZeroModuleFunctor_shortExact S hS)

/-- In a distinguished triangle `T₁ → T₂ → T₃ → T₁⟦1⟧`, a map `T₁ → W` extends along `T₁ → T₂`
when every map `T₃ → W⟦1⟧` is zero. -/
theorem Triangle.exists_comp_eq_of_subsingleton {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {W : C} (h : ∀ a : T.obj₃ ⟶ W⟦(1 : ℤ)⟧, a = 0)
    (f : T.obj₁ ⟶ W) : ∃ g : T.obj₂ ⟶ W, T.mor₁ ≫ g = f := by
  let e := (shiftEquiv C (1 : ℤ)).symm.toAdjunction.homEquiv T.obj₃ W
  have hz : ∀ a : T.invRotate.obj₁ ⟶ W, a = 0 := fun a =>
    e.injective ((h (e a)).trans (h (e 0)).symm)
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) f (hz _)
  exact ⟨g, hg.symm⟩

variable {S : ShortComplex (ModuleCat.{0} R)}

/-- **Extension along `K → P`**: for `0 → K → P → X → 0` exact with `Ext^1(X, Y) = 0`, every
map `K → Y` extends to `P`. -/
theorem exists_comp_eq_of_shortExact (hS : S.ShortExact) (Y : ModuleCat.{0} R)
    (hext : ∀ f : Q.obj ((degreeZeroModuleFunctor R).obj S.X₃) ⟶
      (Q.obj ((degreeZeroModuleFunctor R).obj Y))⟦(1 : ℤ)⟧, f = 0)
    (u : S.X₁ ⟶ Y) : ∃ h : S.X₂ ⟶ Y, S.f ≫ h = u := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact_module S hS
  obtain ⟨g, hg⟩ := Triangle.exists_comp_eq_of_subsingleton _ hT hext
    ((degreeZeroModuleFunctor R ⋙ Q).map u)
  let F := Functor.FullyFaithful.ofFullyFaithful (degreeZeroModuleFunctor R ⋙ Q)
  refine ⟨F.preimage g, F.map_injective ?_⟩
  rw [Functor.map_comp, F.map_preimage]
  exact hg

/-- **Dimension shift**: for `0 → K → P → X → 0` exact with `P` projective, `n ≠ 0` and
`Ext^{n+1}(X, Y) = 0`, also `Ext^n(K, Y) = 0`. -/
theorem hom_shift_eq_zero_of_shortExact (hS : S.ShortExact) [Module.Projective R S.X₂]
    (Y : ModuleCat.{0} R) {n : ℤ} (hn : n ≠ 0)
    (hext : ∀ f : Q.obj ((degreeZeroModuleFunctor R).obj S.X₃) ⟶
      (Q.obj ((degreeZeroModuleFunctor R).obj Y))⟦n + 1⟧, f = 0)
    (f : Q.obj ((degreeZeroModuleFunctor R).obj S.X₁) ⟶
      (Q.obj ((degreeZeroModuleFunctor R).obj Y))⟦n⟧) : f = 0 := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact_module S hS
  let e := (shiftFunctorAdd' (DerivedCategory R) n 1 (n + 1) rfl).app
    (Q.obj ((degreeZeroModuleFunctor R).obj Y))
  have h0 : ∀ a : Q.obj ((degreeZeroModuleFunctor R).obj S.X₃) ⟶
      ((Q.obj ((degreeZeroModuleFunctor R).obj Y))⟦n⟧)⟦(1 : ℤ)⟧, a = 0 := fun a =>
    (Iso.homCongr (Iso.refl _) e.symm).injective (by
      rw [hext (Iso.homCongr (Iso.refl _) e.symm a), hext (Iso.homCongr (Iso.refl _) e.symm 0)])
  obtain ⟨g, hg⟩ := Triangle.exists_comp_eq_of_subsingleton _ hT h0 f
  rw [← hg, hom_shift_eq_zero_of_projective S.X₂ Y hn g, comp_zero]

/-! ### Dimensions -/

section Dimension

omit [HasDerivedCategory.{0, 0} R]

variable {k : Type} [Field k] [Algebra k R]
  {X₁ X₂ X₃ Y : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃] [AddCommGroup Y]
  [Module R X₁] [Module R X₂] [Module R X₃] [Module R Y] [Module k Y] [IsScalarTower k R Y]

/-- **Dimension count along a short exact sequence**: for `0 → X₁ → X₂ → X₃ → 0` exact such that
every map `X₁ → Y` extends to `X₂`, `dim Hom(X₂, Y) = dim Hom(X₃, Y) + dim Hom(X₁, Y)`. -/
theorem finrank_hom_eq_add_of_exact (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hext : ∀ u : X₁ →ₗ[R] Y, ∃ h : X₂ →ₗ[R] Y, h ∘ₗ f = u)
    [FiniteDimensional k (X₂ →ₗ[R] Y)] :
    Module.finrank k (X₂ →ₗ[R] Y) =
      Module.finrank k (X₃ →ₗ[R] Y) + Module.finrank k (X₁ →ₗ[R] Y) := by
  let Φ : (X₂ →ₗ[R] Y) →ₗ[k] (X₁ →ₗ[R] Y) :=
    { toFun := fun h => h ∘ₗ f
      map_add' := fun _ _ => LinearMap.add_comp _ _ _
      map_smul' := fun _ _ => rfl }
  let Ψ : (X₃ →ₗ[R] Y) →ₗ[k] (X₂ →ₗ[R] Y) :=
    { toFun := fun u => u ∘ₗ g
      map_add' := fun _ _ => LinearMap.add_comp _ _ _
      map_smul' := fun _ _ => rfl }
  have hΦ : Function.Surjective Φ := fun u => (hext u).imp fun _ h => h
  have hΨ : Function.Injective Ψ := fun u v huv => LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := hg x
    exact LinearMap.congr_fun huv y
  have hrange : LinearMap.range Ψ = LinearMap.ker Φ := by
    ext h
    constructor
    · rintro ⟨u, rfl⟩
      exact LinearMap.ext fun x => by
        change u (g (f x)) = 0
        rw [hex.apply_apply_eq_zero, map_zero]
    · intro hh
      have hker : LinearMap.ker g ≤ LinearMap.ker h := fun x hx => by
        obtain ⟨y, rfl⟩ := (hex x).1 hx
        exact LinearMap.congr_fun hh y
      let e := g.quotKerEquivOfSurjective hg
      refine ⟨((LinearMap.ker g).liftQ h hker) ∘ₗ e.symm.toLinearMap, LinearMap.ext fun x => ?_⟩
      change (LinearMap.ker g).liftQ h hker (e.symm (g x)) = h x
      rw [show e.symm (g x) = Submodule.Quotient.mk x from
        e.symm_apply_eq.2 rfl, Submodule.liftQ_apply]
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hΦ, finrank_top, ← hrange,
    LinearMap.finrank_range_of_inj hΨ] at h1
  have : FiniteDimensional k (X₃ →ₗ[R] Y) := Module.Finite.of_injective Ψ hΨ
  omega

end Dimension

end Categorification
