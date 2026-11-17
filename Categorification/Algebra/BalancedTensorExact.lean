/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor
import Categorification.Algebra.ProjK0

/-!
# Exactness of tensoring with a projective module, and additivity of classes in `K₀`

For a left `A`-module `N`, the balanced tensor product `M ↦ M ⊗_A N` is a functor on
`(B, A)`-bimodules (`BalancedTensor.mapLeft`). When `N` is projective it is exact: it preserves
injections (`BalancedTensor.mapLeft_injective`), surjections (`BalancedTensor.mapLeft_surjective`,
for any `N`) and exactness in the middle (`BalancedTensor.mapLeft_exact`). The proof reduces to
free modules `X →₀ A`, where `M ⊗_A (X →₀ A) ≅ X →₀ M` naturally in `M`
(`BalancedTensor.finsuppRight_mapLeft`), via a retraction of `N` onto a free module.

In `K₀`, a short exact sequence of finitely generated projective modules splits, so the class of
the middle term is the sum of the classes of the outer terms (`ProjK0.of_eq_add_of_exact`).

These are the formal inputs of the Mackey argument of Webster, *Weighted Khovanov–Lauda–Rouquier
algebras* (arXiv:1209.2463v4), proof of Theorem 2.19, and of Khovanov–Lauda I
(arXiv:0803.4121v2), proof of Proposition 3.18: the restriction of an induced module
`Res Ind (P ⊠ Q) = (e W e) ⊗ (P ⊠ Q)` inherits the bimodule filtration of `e W e`, with
successive quotients the tensor products of the subquotients with `P ⊠ Q`, and its class is the
sum of their classes.
-/

namespace Categorification

open scoped TensorProduct
open MulOpposite

noncomputable section

namespace BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]

section MapLeft

variable {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M]
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M']
  [Module Aᵐᵒᵖ M'] [SMulCommClass B Aᵐᵒᵖ M']
  {M'' : Type*} [AddCommGroup M''] [Module k M''] [Module B M''] [IsScalarTower k B M'']
  [Module Aᵐᵒᵖ M''] [SMulCommClass B Aᵐᵒᵖ M'']
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N]

/-- A morphism of `(B, A)`-bimodules: a `B`-linear map commuting with the right `A`-action. -/
def IsBimoduleHom (f : M →ₗ[B] M') : Prop := ∀ (a : A) (m : M), f (op a • m) = op a • f m

variable (k N) in
/-- The map `M ⊗_A N → M' ⊗_A N` induced by a morphism of `(B, A)`-bimodules `f : M → M'`. -/
def mapLeft (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) :
    BalancedTensor k B A M N →ₗ[B] BalancedTensor k B A M' N :=
  liftB ((mkBil k B A M' N).comp (f.restrictScalars k))
    (fun m a n => by simp [hf a m, op_smul_tmul]) (fun b m n => by simp [smul_tmul'])

omit [SMulCommClass B Aᵐᵒᵖ M'] in
@[simp] theorem mapLeft_tmul (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (m : M) (n : N) :
    mapLeft k N f hf (tmul m n) = tmul (f m) n := rfl

omit [SMulCommClass B Aᵐᵒᵖ M''] in
theorem mapLeft_comp (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (g : M' →ₗ[B] M'')
    (hg : IsBimoduleHom (A := A) g) :
    mapLeft k N (g.comp f) (fun a m => by simp [hf a m, hg a (f m)]) =
      (mapLeft k N g hg).comp (mapLeft k N f hf) :=
  extB fun _ _ => rfl

omit [SMulCommClass B Aᵐᵒᵖ M'] in
theorem mapLeft_surjective {f : M →ₗ[B] M'} (hf : IsBimoduleHom (A := A) f)
    (hs : Function.Surjective f) : Function.Surjective (mapLeft k N f hf) := by
  intro x
  induction x using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m n =>
    obtain ⟨m, rfl⟩ := hs m
    exact ⟨tmul m n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

variable [Algebra k A] [IsScalarTower k A N]
  {N' : Type*} [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- `mapLeft` commutes with `mapRight`. -/
theorem mapLeft_mapRight (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (g : N →ₗ[A] N')
    (x : BalancedTensor k B A M N) :
    mapLeft k N' f hf (mapRight g x) = mapRight g (mapLeft k N f hf x) := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']

/-- Naturality of `M ⊗_A (X →₀ A) ≅ X →₀ M` in the bimodule `M`. -/
theorem finsuppRight_mapLeft (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (X : Type*)
    (x : BalancedTensor k B A M (X →₀ A)) :
    finsuppRight k B A M' X (mapLeft k (X →₀ A) f hf x) =
      Finsupp.mapRange.linearMap f (finsuppRight k B A M X x) := by
  induction x using induction_on with
  | zero => simp
  | tmul m g =>
    ext y
    simp only [finsuppRight, finsuppBil]
    simp [(hf _ _).symm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- For a projective `N`, tensoring with `N` preserves injections of bimodules. -/
theorem mapLeft_injective [Module.Projective A N] {f : M →ₗ[B] M'} (hf : IsBimoduleHom (A := A) f)
    (hi : Function.Injective f) : Function.Injective (mapLeft k N f hf) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A N›
  have hfree : Function.Injective (mapLeft k (N →₀ A) f hf) := by
    intro x y hxy
    apply (finsuppRight k B A M N).injective
    have := congrArg (finsuppRight k B A M' N) hxy
    rw [finsuppRight_mapLeft, finsuppRight_mapLeft] at this
    exact Finsupp.mapRange_injective _ (map_zero f) hi this
  have hret : ∀ x : BalancedTensor k B A M N,
      mapRight (Finsupp.linearCombination A id) (mapRight s x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← mapRight_comp, hs, mapRight_id, LinearMap.id_apply]
  intro x y hxy
  rw [← hret x, ← hret y]
  congr 1
  apply hfree
  rw [mapLeft_mapRight, mapLeft_mapRight, hxy]

/-- For a projective `N`, tensoring with `N` is exact in the middle: if `M → M' → M''` is exact,
so is `M ⊗_A N → M' ⊗_A N → M'' ⊗_A N`. -/
theorem mapLeft_exact [Module.Projective A N] [IsScalarTower k Aᵐᵒᵖ M'']
    {f : M →ₗ[B] M'} (hf : IsBimoduleHom (A := A) f)
    {g : M' →ₗ[B] M''} (hg : IsBimoduleHom (A := A) g) (hfg : Function.Exact f g) :
    Function.Exact (mapLeft k N f hf) (mapLeft k N g hg) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A N›
  have hret : ∀ x : BalancedTensor k B A M' N,
      mapRight (Finsupp.linearCombination A id) (mapRight s x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← mapRight_comp, hs, mapRight_id, LinearMap.id_apply]
  intro x
  constructor
  · intro hx
    have h0 : finsuppRight k B A M'' N (mapLeft k (N →₀ A) g hg (mapRight s x)) = 0 := by
      rw [mapLeft_mapRight, hx, map_zero, map_zero]
    rw [finsuppRight_mapLeft] at h0
    have hmem : ∀ y, finsuppRight k B A M' N (mapRight s x) y ∈ Set.range f := fun y => by
      rw [← hfg]
      have := DFunLike.congr_fun h0 y
      simpa using this
    choose c hc using hmem
    set v := finsuppRight k B A M' N (mapRight s x) with hv
    classical
    let u : N →₀ M :=
      Finsupp.onFinset v.support (fun y => if v y = 0 then 0 else c y) fun y hy => by
        rw [Finsupp.mem_support_iff]
        intro h
        exact hy (by simp [h])
    refine ⟨mapRight (Finsupp.linearCombination A id) ((finsuppRight k B A M N).symm u), ?_⟩
    rw [mapLeft_mapRight]
    conv_rhs => rw [← hret x]
    congr 1
    apply (finsuppRight k B A M' N).injective
    rw [finsuppRight_mapLeft, LinearEquiv.apply_symm_apply]
    ext y
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, u,
      Finsupp.onFinset_apply]
    split_ifs with h
    · rw [h, map_zero]
    · exact hc y
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← mapLeft_comp]
    have : g.comp f = 0 := LinearMap.ext fun m => hfg.apply_apply_eq_zero m
    induction y using induction_on with
    | zero => simp
    | tmul m n => simp [this]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end MapLeft

end BalancedTensor

namespace ProjK0

universe u v

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A]

/-- **Additivity on short exact sequences.** A short exact sequence `0 → P₁ → P₂ → P₃ → 0` of
finitely generated projective modules splits, so `[P₂] = [P₁] + [P₃]` in `K₀`. -/
theorem of_eq_add_of_exact (P₁ P₂ P₃ : FGProj k A) (f : P₁ →ₗ[A] P₂) (g : P₂ →ₗ[A] P₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    of P₂ = of P₁ + of P₃ := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g LinearMap.id hg
  let e : P₁.carrier × P₃.carrier →ₗ[A] P₂.carrier := LinearMap.coprod f h
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hxy
      simp only [e, LinearMap.coprod_apply] at hxy
      have hy : y₁ = y₂ := by
        have := congrArg g hxy
        simp only [map_add, hfg.apply_apply_eq_zero, zero_add] at this
        have h1 := LinearMap.congr_fun hh y₁
        have h2 := LinearMap.congr_fun hh y₂
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
        rw [← h1, ← h2, this]
      subst hy
      rw [add_left_inj] at hxy
      rw [hf hxy]
    · intro z
      obtain ⟨x, hx⟩ := (hfg (z - h (g z))).1 (by
        have := LinearMap.congr_fun hh (g z)
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [map_sub, this, sub_self])
      exact ⟨(x, g z), by simp [e, hx]⟩
  rw [← of_prod]
  exact (of_eq_of_iso (LinearEquiv.ofBijective e he)).symm

end ProjK0

end

end Categorification
