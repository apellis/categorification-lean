/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor
import Categorification.Algebra.ProjK0

/-!
# Exactness of tensoring with a projective module, and additivity of classes in `K₀`

For a left `A`-module `N`, the balanced tensor product `M ↦ M ⊗_A N` is a functor on
`(B, A)`-bimodules (`BalancedTensor.mapLeftBimodule`). When `N` is projective it is exact: it preserves
injections (`BalancedTensor.mapLeftBimodule_injective`), surjections (`BalancedTensor.mapLeftBimodule_surjective`,
for any `N`) and exactness in the middle (`BalancedTensor.mapLeftBimodule_exact`). The proof reduces to
free modules `X →₀ A`, where `M ⊗_A (X →₀ A) ≅ X →₀ M` naturally in `M`
(`BalancedTensor.finsuppRight_mapLeftBimodule`), via a retraction of `N` onto a free module.

A short exact sequence with projective cokernel splits (`ProjK0.nonempty_prod_equiv_of_exact`),
so in `K₀` the class of the middle term is the sum of the classes of the outer terms
(`ProjK0.of_eq_add_of_exact`). Along a finite chain of submodules with finitely generated
projective successive quotients, the module is finitely generated projective and its class is
the sum of the classes of the quotients (`ProjK0.exists_of_eq_sum_of_chain`).

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
def mapLeftBimodule (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) :
    BalancedTensor k B A M N →ₗ[B] BalancedTensor k B A M' N :=
  liftB ((mkBil k B A M' N).comp (f.restrictScalars k))
    (fun m a n => by simp [hf a m, op_smul_tmul]) (fun b m n => by simp [smul_tmul'])

omit [SMulCommClass B Aᵐᵒᵖ M'] in
@[simp] theorem mapLeftBimodule_tmul (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (m : M) (n : N) :
    mapLeftBimodule k N f hf (tmul m n) = tmul (f m) n := rfl

omit [SMulCommClass B Aᵐᵒᵖ M''] in
theorem mapLeftBimodule_comp (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (g : M' →ₗ[B] M'')
    (hg : IsBimoduleHom (A := A) g) :
    mapLeftBimodule k N (g.comp f) (fun a m => by simp [hf a m, hg a (f m)]) =
      (mapLeftBimodule k N g hg).comp (mapLeftBimodule k N f hf) :=
  extB fun _ _ => rfl

omit [SMulCommClass B Aᵐᵒᵖ M'] in
theorem mapLeftBimodule_surjective {f : M →ₗ[B] M'} (hf : IsBimoduleHom (A := A) f)
    (hs : Function.Surjective f) : Function.Surjective (mapLeftBimodule k N f hf) := by
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

/-- `mapLeftBimodule` commutes with `mapRight`. -/
theorem mapLeftBimodule_mapRight (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (g : N →ₗ[A] N')
    (x : BalancedTensor k B A M N) :
    mapLeftBimodule k N' f hf (mapRight g x) = mapRight g (mapLeftBimodule k N f hf x) := by
  induction x using induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']

/-- Naturality of `M ⊗_A (X →₀ A) ≅ X →₀ M` in the bimodule `M`. -/
theorem finsuppRight_mapLeftBimodule (f : M →ₗ[B] M') (hf : IsBimoduleHom (A := A) f) (X : Type*)
    (x : BalancedTensor k B A M (X →₀ A)) :
    finsuppRight k B A M' X (mapLeftBimodule k (X →₀ A) f hf x) =
      Finsupp.mapRange.linearMap f (finsuppRight k B A M X x) := by
  induction x using induction_on with
  | zero => simp
  | tmul m g =>
    ext y
    simp only [finsuppRight, finsuppBil]
    simp [(hf _ _).symm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- For a projective `N`, tensoring with `N` preserves injections of bimodules. -/
theorem mapLeftBimodule_injective [Module.Projective A N] {f : M →ₗ[B] M'} (hf : IsBimoduleHom (A := A) f)
    (hi : Function.Injective f) : Function.Injective (mapLeftBimodule k N f hf) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A N›
  have hfree : Function.Injective (mapLeftBimodule k (N →₀ A) f hf) := by
    intro x y hxy
    apply (finsuppRight k B A M N).injective
    have := congrArg (finsuppRight k B A M' N) hxy
    rw [finsuppRight_mapLeftBimodule, finsuppRight_mapLeftBimodule] at this
    exact Finsupp.mapRange_injective _ (map_zero f) hi this
  have hret : ∀ x : BalancedTensor k B A M N,
      mapRight (Finsupp.linearCombination A id) (mapRight s x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← mapRight_comp, hs, mapRight_id, LinearMap.id_apply]
  intro x y hxy
  rw [← hret x, ← hret y]
  congr 1
  apply hfree
  rw [mapLeftBimodule_mapRight, mapLeftBimodule_mapRight, hxy]

/-- For a projective `N`, tensoring with `N` is exact in the middle: if `M → M' → M''` is exact,
so is `M ⊗_A N → M' ⊗_A N → M'' ⊗_A N`. -/
theorem mapLeftBimodule_exact [Module.Projective A N] [IsScalarTower k Aᵐᵒᵖ M'']
    {f : M →ₗ[B] M'} (hf : IsBimoduleHom (A := A) f)
    {g : M' →ₗ[B] M''} (hg : IsBimoduleHom (A := A) g) (hfg : Function.Exact f g) :
    Function.Exact (mapLeftBimodule k N f hf) (mapLeftBimodule k N g hg) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A N›
  have hret : ∀ x : BalancedTensor k B A M' N,
      mapRight (Finsupp.linearCombination A id) (mapRight s x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← mapRight_comp, hs, mapRight_id, LinearMap.id_apply]
  intro x
  constructor
  · intro hx
    have h0 : finsuppRight k B A M'' N (mapLeftBimodule k (N →₀ A) g hg (mapRight s x)) = 0 := by
      rw [mapLeftBimodule_mapRight, hx, map_zero, map_zero]
    rw [finsuppRight_mapLeftBimodule] at h0
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
    rw [mapLeftBimodule_mapRight]
    conv_rhs => rw [← hret x]
    congr 1
    apply (finsuppRight k B A M' N).injective
    rw [finsuppRight_mapLeftBimodule, LinearEquiv.apply_symm_apply]
    ext y
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, u,
      Finsupp.onFinset_apply]
    split_ifs with h
    · rw [h, map_zero]
    · exact hc y
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← mapLeftBimodule_comp]
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

/-- A short exact sequence `0 → P₁ → P₂ → P₃ → 0` with `P₃` projective splits:
`P₁ × P₃ ≅ P₂`. -/
theorem nonempty_prod_equiv_of_exact {P₁ P₂ P₃ : Type*} [AddCommGroup P₁] [Module A P₁]
    [AddCommGroup P₂] [Module A P₂] [AddCommGroup P₃] [Module A P₃] [Module.Projective A P₃]
    (f : P₁ →ₗ[A] P₂) (g : P₂ →ₗ[A] P₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Nonempty ((P₁ × P₃) ≃ₗ[A] P₂) := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g LinearMap.id hg
  let e : P₁ × P₃ →ₗ[A] P₂ := LinearMap.coprod f h
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
  exact ⟨LinearEquiv.ofBijective e he⟩

/-- **Additivity on short exact sequences.** A short exact sequence `0 → P₁ → P₂ → P₃ → 0` of
finitely generated projective modules splits, so `[P₂] = [P₁] + [P₃]` in `K₀`. -/
theorem of_eq_add_of_exact (P₁ P₂ P₃ : FGProj k A) (f : P₁ →ₗ[A] P₂) (g : P₂ →ₗ[A] P₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    of P₂ = of P₁ + of P₃ := by
  obtain ⟨e⟩ := nonempty_prod_equiv_of_exact f g hf hg hfg
  rw [← of_prod]
  exact (of_eq_of_iso e).symm

/-- **Additivity along a filtration.** Let `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M` be a chain of
submodules of `M` whose successive quotients `F (i + 1) / F i` are isomorphic to finitely
generated projective modules `Q i`. Then `M` is finitely generated projective, and
`[M] = ∑_{i < n} [Q i]` in `K₀`. -/
theorem exists_of_eq_sum_of_chain {M : Type u} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (n : ℕ) (F : ℕ → Submodule A M) (hF : Monotone F) (h0 : F 0 = ⊥)
    (hn : F n = ⊤) (Q : ℕ → FGProj k A)
    (e : ∀ i, (F (i + 1) ⧸ (F i).comap (F (i + 1)).subtype) ≃ₗ[A] Q i) :
    ∃ (_ : Module.Finite A M) (_ : Module.Projective A M),
      of (FGProj.of (k := k) (A := A) M) = ∑ i ∈ Finset.range n, of (Q i) := by
  have key : ∀ m, ∃ (_ : Module.Finite A (F m)) (_ : Module.Projective A (F m)),
      of (FGProj.of (k := k) (A := A) (F m)) = ∑ i ∈ Finset.range m, of (Q i) := by
    intro m
    induction m with
    | zero =>
      rw [h0]
      have : Module.Free A (⊥ : Submodule A M) := Module.Free.of_subsingleton _ _
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [Finset.range_zero, Finset.sum_empty]
      let Z := FGProj.of (k := k) (A := A) (⊥ : Submodule A M)
      have e0 : Z.Iso (Z.prod Z) :=
        LinearEquiv.ofSubsingleton (⊥ : Submodule A M) ((⊥ : Submodule A M) × (⊥ : Submodule A M))
      have := of_eq_of_iso e0
      rw [of_prod] at this
      exact left_eq_add.1 this
    | succ m ih =>
      obtain ⟨_, _, hm⟩ := ih
      let f : F m →ₗ[A] F (m + 1) := Submodule.inclusion (hF (Nat.le_succ m))
      let g : F (m + 1) →ₗ[A] Q m :=
        (e m).toLinearMap ∘ₗ ((F m).comap (F (m + 1)).subtype).mkQ
      have hf : Function.Injective f := Submodule.inclusion_injective _
      have hg : Function.Surjective g :=
        (e m).surjective.comp (Submodule.mkQ_surjective _)
      have hfg : Function.Exact f g := by
        intro x
        simp only [g, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
          Submodule.mem_comap, Submodule.coe_subtype]
        constructor
        · intro hx
          exact ⟨⟨x.1, hx⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact y.2
      obtain ⟨eq⟩ := nonempty_prod_equiv_of_exact f g hf hg hfg
      have : Module.Finite A (F (m + 1)) := Module.Finite.equiv eq
      have : Module.Projective A (F (m + 1)) := Module.Projective.of_equiv eq
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [of_eq_add_of_exact (FGProj.of (k := k) (A := A) (F m))
        (FGProj.of (k := k) (A := A) (F (m + 1))) (Q m) f g hf hg hfg, hm, Finset.sum_range_succ]
  obtain ⟨_, _, h⟩ := key n
  let eT : (F n) ≃ₗ[A] M := (LinearEquiv.ofEq _ _ hn).trans Submodule.topEquiv
  have : Module.Finite A M := Module.Finite.equiv eT
  have : Module.Projective A M := Module.Projective.of_equiv eT
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [← h]
  exact (of_eq_of_iso (P := FGProj.of (k := k) (A := A) (F n))
    (Q := FGProj.of (k := k) (A := A) M) eT).symm

end ProjK0

end

end Categorification
