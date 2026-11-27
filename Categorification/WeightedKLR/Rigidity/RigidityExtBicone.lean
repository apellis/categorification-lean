/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Linear Ext and Hom out of a sum of copies of one object

Input for B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
§7.1, Corollary 7.7, where the standard module of a divided-power word is a summand of the
standard module of its expansion, which is a sum of copies of it.

* `Limits.Bicone.ofConst`: a bicone over a constant family `Y` with point `X` from maps
  `ι_j : Y → X`, `π_j : X → Y` with `ι_i ≫ π_j = δ_{ij}` and `∑ π_j ≫ ι_j = 1`.
* `ProjectiveResolution.extLinearEquivHom`: the `R`-linear form of
  `ProjectiveResolution.extAddEquivHom`.
* `Ext.biproductLinearEquiv`, `Limits.Bicone.homLinearEquiv`: Ext and Hom out of a biproduct.
* `finrank_eq_of_linearEquiv_fun`: `V^J ≅ W^J` with `J` nonempty and `W` finite-dimensional gives
  `dim V = dim W`.
-/

universe w

open CategoryTheory Abelian Limits

namespace CategoryTheory

section Bicone

variable {C : Type*} [Category C] [Preadditive C] {J : Type*} [Fintype J] [DecidableEq J]

/-- A bicone over the constant family `Y` with point `X`, from maps `ι_j : Y → X` and
`π_j : X → Y` with `ι_i ≫ π_j = δ_{ij}`. -/
def Limits.Bicone.ofConst {X Y : C} (ι : J → (Y ⟶ X)) (π : J → (X ⟶ Y))
    (h : ∀ i j, ι i ≫ π j = if i = j then 𝟙 Y else 0) : Bicone (fun _ : J => Y) where
  pt := X
  π := π
  ι := ι
  ι_π i j := by
    rw [h]
    split_ifs <;> simp

/-- `Bicone.ofConst` is a bilimit when `∑ π_j ≫ ι_j = 1`. -/
def Limits.Bicone.ofConstIsBilimit {X Y : C} (ι : J → (Y ⟶ X)) (π : J → (X ⟶ Y))
    (h : ∀ i j, ι i ≫ π j = if i = j then 𝟙 Y else 0) (htot : ∑ j, π j ≫ ι j = 𝟙 X) :
    (Bicone.ofConst ι π h).IsBilimit :=
  isBilimitOfTotal _ htot

variable {R : Type*} [Ring R] [Linear R C]

/-- Hom out of a bilimit bicone: `Hom(⊕ X_j, Y) ≅ ∏ Hom(X_j, Y)`. -/
def Limits.Bicone.homLinearEquiv {F : J → C} {c : Bicone F} (hc : c.IsBilimit) (Y : C) :
    (c.pt ⟶ Y) ≃ₗ[R] (∀ j, F j ⟶ Y) where
  toFun f j := c.ι j ≫ f
  invFun g := ∑ j, c.π j ≫ g j
  left_inv f := by
    simp only [← Preadditive.sum_comp, ← Category.assoc]
    rw [IsBilimit.total hc, Category.id_comp]
  right_inv g := by
    funext i
    simp only [Preadditive.comp_sum, ← Category.assoc, c.ι_π]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  map_add' f g := by
    funext j
    simp
  map_smul' r f := by
    funext j
    simp

end Bicone

namespace ProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (P : ProjectiveResolution X) {R : Type*} [Ring R] [Linear R C]

theorem smul_extMk (r : R) {n : ℕ} (f : P.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : P.complex.d m n ≫ f = 0) :
    r • P.extMk f m hm hf = P.extMk (r • f) m hm (by simp [hf]) := by
  rw [Ext.smul_eq_comp_mk₀, extMk_comp_mk₀]
  congr 1
  simp

/-- The `R`-linear form of `extAddEquivHom`: `Extⁿ(X, Y) ≅ Hom(P_n, Y)` when `P_{n+1} = 0` and
`P_{n-1}` has no nonzero maps to `Y`. -/
noncomputable def extLinearEquivHom (p n : ℕ) (hp : p + 1 = n) (hz : IsZero (P.complex.X (n + 1)))
    [Subsingleton (P.complex.X p ⟶ Y)] : Ext X Y n ≃ₗ[R] (P.complex.X n ⟶ Y) :=
  { P.extAddEquivHom p n hp hz with
    map_smul' := fun r x => by
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective x (n + 1) rfl
      have h1 : (P.extAddEquivHom p n hp hz) (P.extMk f (n + 1) rfl hf) = f :=
        (P.extAddEquivHom p n hp hz).apply_symm_apply f
      have h2 : (P.extAddEquivHom p n hp hz) (P.extMk (r • f) (n + 1) rfl (by simp [hf])) =
          r • f :=
        (P.extAddEquivHom p n hp hz).apply_symm_apply (r • f)
      change (P.extAddEquivHom p n hp hz) (r • P.extMk f (n + 1) rfl hf) =
        r • (P.extAddEquivHom p n hp hz) (P.extMk f (n + 1) rfl hf)
      rw [smul_extMk, h1, h2] }

end ProjectiveResolution

namespace Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {R : Type*} [Ring R] [Linear R C]
  {J : Type*} [Fintype J]

/-- `Ext` out of a biproduct, `R`-linearly. -/
noncomputable def biproductLinearEquiv {X : J → C} {c : Limits.Bicone X} (hc : c.IsBilimit) (Y : C)
    (n : ℕ) : Ext c.pt Y n ≃ₗ[R] Π i, Ext (X i) Y n :=
  { Ext.biproductAddEquiv hc Y n with
    map_smul' := fun r x => by
      funext i
      change (Ext.mk₀ (c.ι i)).comp (r • x) (zero_add n) =
        r • (Ext.mk₀ (c.ι i)).comp x (zero_add n)
      rw [Ext.comp_smul] }

end Abelian.Ext

end CategoryTheory

/-- If `V^J ≅ W^J` for a nonempty finite `J` and `W` is finite-dimensional, then `V` and `W`
have the same dimension. -/
theorem finrank_eq_of_linearEquiv_fun {k : Type*} [Field k] {V W : Type*} [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W] {J : Type*} [Fintype J]
    [Nonempty J] (e : (J → V) ≃ₗ[k] (J → W)) : Module.finrank k V = Module.finrank k W := by
  classical
  obtain ⟨j⟩ := ‹Nonempty J›
  have : FiniteDimensional k (J → V) := LinearEquiv.finiteDimensional e.symm
  have : FiniteDimensional k V :=
    Module.Finite.of_injective (LinearMap.single k (fun _ => V) j)
      (fun x y h => Pi.single_injective (M := fun _ => V) j h)
  have h := e.finrank_eq
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul] at h
  exact Nat.eq_of_mul_eq_mul_left (Finset.card_pos.2 ⟨j, Finset.mem_univ _⟩) h
