/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.Graded.K0Exact
import Categorification.Algebra.Graded.Tensor
import Categorification.Algebra.BalancedTensorFiltration

/-!
# Graded `K₀` along filtrations

The graded analogues of `ProjK0.exists_of_eq_sum_of_chain_surj_fin` and
`ProjK0.exists_of_balancedTensor_eq_sum`, for a graded algebra over a field.

Let `M` be a graded `A`-module with a chain `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M` of homogeneous
submodules, and let `g i : F (i + 1) → Q i` be degree-preserving surjections onto finitely
generated graded projective modules with kernels `F i`. Then `M` is finitely generated projective
and `[M] = ∑_{i < n} [Q i]` in the graded `K₀` (`Graded.K0.exists_of_eq_sum_of_chain`). The
proof applies `Graded.K0.of_eq_add_of_exact` to each step of the chain.

For a graded `(B, A)`-bimodule `M` with a chain of homogeneous sub-bimodules whose successive
quotients are graded bimodules `Y i` (by degree-preserving surjective bimodule maps), and a graded
projective left `A`-module `N`, `[M ⊗_A N] = ∑_{i < n} [Y i ⊗_A N]` in the graded `K₀` of `B`
(`Graded.K0.exists_of_balancedTensor_eq_sum`). The grading shifts of the subquotients are carried
by the gradings of the `Y i`.

This is the passage from the graded Mackey filtration of B. Webster, *Weighted
Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of Theorem 2.19, to graded `K₀`.

## Main results

* `Graded.K0.exists_of_eq_sum_of_chain`: additivity of graded `K₀` along a homogeneous chain.
* `Graded.K0.exists_of_balancedTensor_eq_sum`: the class of a tensored filtered graded bimodule.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Function

namespace K0

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- The homogeneous submodule `p` of a graded module, as a graded projective module. -/
@[reducible] def submoduleGProj {M : Type u} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (p : Submodule A M) (hp : p.IsHomogeneous ℳ) [Module.Finite A p] [Module.Projective A p] :
    GProj 𝒜 :=
  { carrier := p
    grading := submodule ℳ p
    decomposition := submoduleDecomposition ℳ hp }

/-- **Additivity of graded `K₀` along a homogeneous filtration.** Let
`0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M` be a chain of homogeneous submodules of a graded module `M`, and
`g i : F (i + 1) → Q i` (`i < n`) degree-preserving surjections onto finitely generated graded
projective modules with kernels `F i`. Then `M` is finitely generated projective and
`[M] = ∑_{i < n} [Q i]` in the graded `K₀`. -/
theorem exists_of_eq_sum_of_chain {M : Type u} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (n : ℕ) (F : ℕ → Submodule A M) (hF : Monotone F) (hFh : ∀ i, (F i).IsHomogeneous ℳ)
    (h0 : F 0 = ⊥) (hn : F n = ⊤) (Q : Fin n → GProj 𝒜)
    (g : ∀ i : Fin n, F ((i : ℕ) + 1) →ₗ[A] (Q i).carrier)
    (hgr : ∀ i : Fin n, PreservesGrading (submodule ℳ (F ((i : ℕ) + 1))) (Q i).grading (g i))
    (hg : ∀ i, Surjective (g i))
    (hker : ∀ (i : Fin n) (x : F ((i : ℕ) + 1)), g i x = 0 ↔ (x : M) ∈ F (i : ℕ)) :
    ∃ (_ : Module.Finite A M) (_ : Module.Projective A M),
      of ({ carrier := M, grading := ℳ } : GProj 𝒜) = ∑ i, of (Q i) := by
  classical
  let c : ℕ → K0 𝒜 := fun i => if h : i < n then of (Q ⟨i, h⟩) else 0
  have key : ∀ m, m ≤ n → ∃ (_ : Module.Finite A (F m)) (_ : Module.Projective A (F m)),
      of (submoduleGProj (𝒜 := 𝒜) ℳ (F m) (hFh m)) = ∑ i ∈ Finset.range m, c i := by
    intro m
    induction m with
    | zero =>
      intro _
      have hsub : Subsingleton (F 0) := by rw [h0]; infer_instance
      have : Module.Free A (F 0) := Module.Free.of_subsingleton _ _
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [Finset.range_zero, Finset.sum_empty]
      let Z := submoduleGProj (𝒜 := 𝒜) ℳ (F 0) (hFh 0)
      have e0 : Z.Iso (Z.prod Z) :=
        GradedEquiv.ofLinearMaps 0 0 (fun x => Subsingleton.elim (α := F 0) _ _)
          (fun x => Subsingleton.elim (α := F 0 × F 0) _ _) (fun _ _ _ => zero_mem _) (fun _ _ _ => zero_mem _)
      have := of_eq_of_iso e0
      rw [of_prod] at this
      exact left_eq_add.1 this
    | succ m ih =>
      intro hm
      obtain ⟨_, _, hm'⟩ := ih (Nat.le_of_succ_le hm)
      let i : Fin n := ⟨m, hm⟩
      let f : F m →ₗ[A] F (m + 1) := Submodule.inclusion (hF (Nat.le_succ m))
      have hf : Injective f := Submodule.inclusion_injective _
      have hfg : Exact f (g i) := by
        intro x
        rw [hker i x]
        constructor
        · intro hx
          exact ⟨⟨x.1, hx⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact y.2
      obtain ⟨eq⟩ := ProjK0.nonempty_prod_equiv_of_exact f (g i) hf (hg i) hfg
      have : Module.Finite A (F (m + 1)) := Module.Finite.equiv eq
      have : Module.Projective A (F (m + 1)) := Module.Projective.of_equiv eq
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [of_eq_add_of_exact (submoduleGProj ℳ (F m) (hFh m))
        (submoduleGProj ℳ (F (m + 1)) (hFh (m + 1))) (Q i) f (g i) (fun _ _ hx => hx) (hgr i)
        hf (hg i) hfg, hm', Finset.sum_range_succ]
      simp only [c, show m < n from hm, dite_true]
      rfl
  obtain ⟨_, _, h⟩ := key n le_rfl
  let eT : (F n) ≃ₗ[A] M := (LinearEquiv.ofEq _ _ hn).trans Submodule.topEquiv
  have : Module.Finite A M := Module.Finite.equiv eT
  have : Module.Projective A M := Module.Projective.of_equiv eT
  refine ⟨inferInstance, inferInstance, ?_⟩
  have iso : (submoduleGProj ℳ (F n) (hFh n)).Iso ({ carrier := M, grading := ℳ } : GProj 𝒜) :=
    GradedEquiv.ofLinearMaps eT.toLinearMap eT.symm.toLinearMap (fun x => eT.symm_apply_apply x)
      (fun y => eT.apply_symm_apply y) (fun _ _ hx => hx) (fun _ _ hy => hy)
  rw [← of_eq_of_iso iso, h, Finset.sum_range (fun i => c i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [c, i.2, dite_true]

end K0

/-! ### Tensoring a filtered graded bimodule -/

section Balanced

open BalancedTensor MulOpposite

variable {k : Type v} [Field k] {B : Type u} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B}
  [GradedAlgebra ℬ] {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]
  {N : Type u} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]

variable (ℬ) in
/-- The balanced tensor product `M ⊗_A N` of a graded `(B, A)`-bimodule and a graded left
`A`-module, as a graded `B`-module, when it is finitely generated projective. -/
@[reducible] def balancedTensorGProj (M : Type u) [AddCommGroup M] [Module k M] [Module B M]
    [IsScalarTower k B M] [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
    (hM : ∀ ⦃i l : ℤ⦄ ⦃m : M⦄ ⦃a : A⦄, m ∈ ℳ i → a ∈ 𝒜 l → op a • m ∈ ℳ (i + l))
    [Module.Finite B (BalancedTensor k B A M N)]
    [Module.Projective B (BalancedTensor k B A M N)] : GProj ℬ :=
  { carrier := BalancedTensor k B A M N
    grading := balancedGrading B A ℳ 𝒩
    decomposition := balancedDecomposition 𝒜 hM
    gradedSMul := gradedSMul_balanced ℬ }

variable {𝒜 𝒩}

omit [Algebra k A] [IsScalarTower k A N] [Decomposition 𝒩] in
/-- `f ⊗_A N` is degree-preserving if the bimodule map `f` is. -/
theorem mapLeftBimodule_mem_balancedGrading {M M' : Type*} [AddCommGroup M] [Module k M]
    [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M]
    [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M'] [Module Aᵐᵒᵖ M']
    {ℳ : ℤ → Submodule k M} {ℳ' : ℤ → Submodule k M'} {f : M →ₗ[B] M'}
    (hf : IsBimoduleHom (A := A) f) (hfg : PreservesGrading ℳ ℳ' f) :
    PreservesGrading (balancedGrading B A ℳ 𝒩) (balancedGrading B A ℳ' 𝒩)
      (mapLeftBimodule k N f hf) := fun _ _ hy =>
  balancedGrading_map_mem _ ((mapLeftBimodule k N f hf).restrictScalars k)
    (fun _ _ _ _ hm hn => tmul_mem_balancedGrading (hfg hm) hn) hy

variable (ℬ 𝒜 𝒩) in
/-- **The class of a tensored filtered graded bimodule.** Let `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M` be a
chain of homogeneous sub-bimodules of a graded `(B, A)`-bimodule `M`, and `π i : F (i + 1) → Y i`
(`i < n`) degree-preserving surjective bimodule maps onto graded bimodules, with kernels `F i`.
For a graded projective left `A`-module `N` such that every `Y i ⊗_A N` is finitely generated
projective, `M ⊗_A N` is finitely generated projective and
`[M ⊗_A N] = ∑_{i < n} [Y i ⊗_A N]` in the graded `K₀` of `B`. -/
theorem K0.exists_of_balancedTensor_eq_sum [Module.Projective A N]
    {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
    [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
    (hM : ∀ ⦃i l : ℤ⦄ ⦃m : M⦄ ⦃a : A⦄, m ∈ ℳ i → a ∈ 𝒜 l → op a • m ∈ ℳ (i + l))
    {n : ℕ} {Y : Fin n → Type u} [∀ i, AddCommGroup (Y i)] [∀ i, Module k (Y i)]
    [∀ i, Module B (Y i)] [∀ i, IsScalarTower k B (Y i)] [∀ i, Module Aᵐᵒᵖ (Y i)]
    [∀ i, SMulCommClass B Aᵐᵒᵖ (Y i)] [∀ i, IsScalarTower k Aᵐᵒᵖ (Y i)]
    (𝒴 : ∀ i, ℤ → Submodule k (Y i)) [∀ i, Decomposition (𝒴 i)]
    [∀ i, SetLike.GradedSMul ℬ (𝒴 i)]
    (hY : ∀ i ⦃j l : ℤ⦄ ⦃y : Y i⦄ ⦃a : A⦄, y ∈ 𝒴 i j → a ∈ 𝒜 l → op a • y ∈ 𝒴 i (j + l))
    (F : ℕ → SubBimodule B A M) (hF : Monotone fun i => (F i).toSubmodule)
    (hFh : ∀ i, (F i).toSubmodule.IsHomogeneous ℳ)
    (h0 : (F 0).toSubmodule = ⊥) (hn : (F n).toSubmodule = ⊤)
    (π : ∀ i : Fin n, (F ((i : ℕ) + 1)).toSubmodule →ₗ[B] Y i)
    (hπ : ∀ i, IsBimoduleHom (A := A) (π i))
    (hπg : ∀ i : Fin n,
      PreservesGrading (submodule ℳ (F ((i : ℕ) + 1)).toSubmodule) (𝒴 i) (π i))
    (hπs : ∀ i, Surjective (π i))
    (hπk : ∀ (i : Fin n) (x : (F ((i : ℕ) + 1)).toSubmodule),
      π i x = 0 ↔ (x : M) ∈ (F (i : ℕ)).toSubmodule)
    [∀ i, Module.Finite B (BalancedTensor k B A (Y i) N)]
    [∀ i, Module.Projective B (BalancedTensor k B A (Y i) N)] :
    ∃ (_ : Module.Finite B (BalancedTensor k B A M N))
      (_ : Module.Projective B (BalancedTensor k B A M N)),
      K0.of (balancedTensorGProj ℬ 𝒜 𝒩 M ℳ hM) =
        ∑ i, K0.of (balancedTensorGProj ℬ 𝒜 𝒩 (Y i) (𝒴 i) (hY i)) := by
  classical
  let : Decomposition (balancedGrading B A ℳ 𝒩) := balancedDecomposition 𝒜 hM
  let : SetLike.GradedSMul ℬ (balancedGrading B A ℳ 𝒩) := gradedSMul_balanced ℬ
  -- The gradings of the sub-bimodules and of their tensor products with `N`.
  let dF : ∀ i, Decomposition (submodule ℳ (F i).toSubmodule) := fun i =>
    submoduleDecomposition ℳ (hFh i)
  let dFN : ∀ i, Decomposition (balancedGrading B A (submodule ℳ (F i).toSubmodule) 𝒩) :=
    fun i => letI := dF i; balancedDecomposition 𝒜 fun _ _ _ _ hm ha => hM hm ha
  have hsub : ∀ i, PreservesGrading (balancedGrading B A (submodule ℳ (F i).toSubmodule) 𝒩)
      (balancedGrading B A ℳ 𝒩) (subBimoduleMap k N (F i)) := fun i =>
    mapLeftBimodule_mem_balancedGrading _ fun _ _ hx => hx
  set G : ℕ → Submodule B (BalancedTensor k B A M N) :=
    fun i => LinearMap.range (subBimoduleMap k N (F i)) with hG
  have hGh : ∀ i, (G i).IsHomogeneous (balancedGrading B A ℳ 𝒩) := by
    rintro i d _ ⟨x, rfl⟩
    let := dFN i
    exact decompose_mem_range (hsub i) x d
  let eG : ∀ i, BalancedTensor k B A (F i).toSubmodule N ≃ₗ[B] G i := fun i =>
    LinearEquiv.ofInjective _ (subBimoduleMap_injective (F i))
  let ι : ∀ i, BalancedTensor k B A (F i).toSubmodule N →ₗ[B]
      BalancedTensor k B A (F (i + 1)).toSubmodule N := fun i =>
    mapLeftBimodule k N (Submodule.inclusion (hF (Nat.le_succ i)))
      (SubBimodule.isBimoduleHom_inclusion (hF (Nat.le_succ i)))
  let p : ∀ i : Fin n, BalancedTensor k B A (F ((i : ℕ) + 1)).toSubmodule N →ₗ[B]
      BalancedTensor k B A (Y i) N := fun i => mapLeftBimodule k N (π i) (hπ i)
  have hex : ∀ i : Fin n, Exact (ι i) (p i) := fun i => by
    refine mapLeftBimodule_exact _ _ fun x => ?_
    rw [hπk]
    constructor
    · intro hx
      exact ⟨⟨x.1, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  refine K0.exists_of_eq_sum_of_chain (balancedGrading B A ℳ 𝒩) n G
    (fun i j hij => range_subBimoduleMap_mono (hF hij)) hGh (range_subBimoduleMap_of_eq_bot h0)
    (range_subBimoduleMap_of_eq_top hn)
    (fun i => balancedTensorGProj ℬ 𝒜 𝒩 (Y i) (𝒴 i) (hY i))
    (fun i => (p i).comp (eG ((i : ℕ) + 1)).symm.toLinearMap) (fun i => ?_)
    (fun i => (mapLeftBimodule_surjective (hπ i) (hπs i)).comp
      (eG ((i : ℕ) + 1)).symm.surjective)
    (fun i x => ?_)
  · -- The successive quotient maps are degree-preserving.
    intro d y hy
    let := dFN ((i : ℕ) + 1)
    have hx : subBimoduleMap k N (F ((i : ℕ) + 1)) ((eG ((i : ℕ) + 1)).symm y) = y :=
      congrArg Subtype.val ((eG ((i : ℕ) + 1)).apply_symm_apply y)
    have hxd : (eG ((i : ℕ) + 1)).symm y ∈
        balancedGrading B A (submodule ℳ (F ((i : ℕ) + 1)).toSubmodule) 𝒩 d :=
      mem_of_injective_of_mem (hsub _) (subBimoduleMap_injective _) (by rw [hx]; exact hy)
    exact mapLeftBimodule_mem_balancedGrading (hπ i) (hπg i) hxd
  · obtain ⟨t, rfl⟩ := (eG ((i : ℕ) + 1)).surjective x
    change p i ((eG ((i : ℕ) + 1)).symm (eG ((i : ℕ) + 1) t)) = 0 ↔ _
    rw [LinearEquiv.symm_apply_apply, hex i t]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      change subBimoduleMap k N (F i) s = subBimoduleMap k N (F ((i : ℕ) + 1)) (ι i s)
      rw [← LinearMap.comp_apply, subBimoduleMap_comp_inclusion]
    · rintro ⟨s, hs⟩
      refine ⟨s, subBimoduleMap_injective (F ((i : ℕ) + 1)) ?_⟩
      rw [← LinearMap.comp_apply, subBimoduleMap_comp_inclusion, hs]
      rfl

end Balanced

end Categorification.Graded
