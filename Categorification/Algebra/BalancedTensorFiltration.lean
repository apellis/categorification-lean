/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorExact

/-!
# Tensoring a filtered bimodule with a projective module, and classes in `K₀`

Let `M` be a `(B, A)`-bimodule with a finite chain of sub-bimodules
`0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M`, and let `N` be a projective left `A`-module. If each successive
quotient `F (i + 1) / F i` is identified with a bimodule `Y i` by a surjective bimodule map
`π i : F (i + 1) → Y i` with kernel `F i`, and each `Y i ⊗_A N` is a finitely generated
projective `B`-module, then `M ⊗_A N` is a finitely generated projective `B`-module and

`[M ⊗_A N] = ∑_{i < n} [Y i ⊗_A N]` in `K₀(B)`

(`ProjK0.exists_of_balancedTensor_eq_sum`). The chain `F i ⊗_A N` of submodules of `M ⊗_A N`
is formed with the exactness of `- ⊗_A N` (`BalancedTensor.mapLeftBimodule_injective`,
`BalancedTensor.mapLeftBimodule_exact`).

This is the passage from a bimodule filtration to `K₀` in the Mackey argument of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of Theorem 2.19, and of
Khovanov–Lauda I, arXiv:0803.4121v2, proof of Proposition 3.18: `Res Ind (P ⊠ Q)` is
`(e W e) ⊗ (P ⊠ Q)`, and the Mackey filtration of the bimodule `e W e` gives the class of
`Res Ind (P ⊠ Q)` as the sum of the classes of the subquotients tensored with `P ⊠ Q`.

## Main definitions and results

* `SubBimodule B A M`: a `B`-submodule of `M` stable under the right `A`-action, with its
  bimodule structure.
* `ProjK0.exists_of_eq_sum_of_chain_surj`: additivity in `K₀` along a chain of submodules whose
  successive quotients are given by surjections with prescribed kernels.
* `ProjK0.exists_of_balancedTensor_eq_sum`: the class of `M ⊗_A N` is the sum of the classes of
  the tensored subquotients.
-/

namespace Categorification

open scoped TensorProduct
open MulOpposite

noncomputable section

universe u

variable {k : Type*} [CommRing k] {B : Type u} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  [Algebra k A]

/-! ### Sub-bimodules -/

variable (B A) in
/-- A `B`-submodule of a `(B, A)`-bimodule `M` stable under the right `A`-action. -/
structure SubBimodule (M : Type*) [AddCommGroup M] [Module B M] [Module Aᵐᵒᵖ M] where
  /-- The underlying `B`-submodule. -/
  toSubmodule : Submodule B M
  /-- Stability under the right action. -/
  op_smul_mem : ∀ (a : A) (m : M), m ∈ toSubmodule → op a • m ∈ toSubmodule

namespace SubBimodule

variable {M : Type*} [AddCommGroup M] [Module B M] [Module Aᵐᵒᵖ M] (S : SubBimodule B A M)

instance : SMul Aᵐᵒᵖ S.toSubmodule :=
  ⟨fun a x => ⟨a • x.1, S.op_smul_mem a.unop x.1 x.2⟩⟩

@[simp] theorem coe_op_smul (a : Aᵐᵒᵖ) (x : S.toSubmodule) :
    ((a • x : S.toSubmodule) : M) = a • (x : M) := rfl

instance : Module Aᵐᵒᵖ S.toSubmodule :=
  Subtype.val_injective.module Aᵐᵒᵖ S.toSubmodule.subtype.toAddMonoidHom fun _ _ => rfl

instance [SMulCommClass B Aᵐᵒᵖ M] : SMulCommClass B Aᵐᵒᵖ S.toSubmodule where
  smul_comm b a x := Subtype.ext (smul_comm b a (x : M))

instance [Module k M] [IsScalarTower k B M] [IsScalarTower k Aᵐᵒᵖ M] :
    IsScalarTower k Aᵐᵒᵖ S.toSubmodule where
  smul_assoc c a x := Subtype.ext (smul_assoc c a (x : M))

/-- The inclusion of a sub-bimodule is a bimodule map. -/
theorem isBimoduleHom_subtype :
    BalancedTensor.IsBimoduleHom (A := A) S.toSubmodule.subtype := fun _ _ => rfl

/-- The inclusion `S ≤ T` of sub-bimodules is a bimodule map. -/
theorem isBimoduleHom_inclusion {S T : SubBimodule B A M} (h : S.toSubmodule ≤ T.toSubmodule) :
    BalancedTensor.IsBimoduleHom (A := A) (Submodule.inclusion h) := fun _ _ => rfl

end SubBimodule

/-! ### Additivity in `K₀` along a chain given by surjections -/

namespace ProjK0

/-- **Additivity along a filtration, with the successive quotients given by surjections.** Let
`0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M` be a chain of submodules of `M`, and `g i : F (i + 1) → Q i`
surjections onto finitely generated projective modules whose kernels are `F i`. Then `M` is
finitely generated projective and `[M] = ∑_{i < n} [Q i]` in `K₀`. -/
theorem exists_of_eq_sum_of_chain_surj {M : Type u} [AddCommGroup M] [Module B M] [Module k M]
    [IsScalarTower k B M] (n : ℕ) (F : ℕ → Submodule B M) (hF : Monotone F) (h0 : F 0 = ⊥)
    (hn : F n = ⊤) (Q : ℕ → FGProj k B) (g : ∀ i, F (i + 1) →ₗ[B] Q i)
    (hg : ∀ i, Function.Surjective (g i))
    (hker : ∀ i (x : F (i + 1)), g i x = 0 ↔ (x : M) ∈ F i) :
    ∃ (_ : Module.Finite B M) (_ : Module.Projective B M),
      of (FGProj.of (k := k) (A := B) M) = ∑ i ∈ Finset.range n, of (Q i) := by
  refine exists_of_eq_sum_of_chain n F hF h0 hn Q fun i => ?_
  have hk : (F i).comap (F (i + 1)).subtype = LinearMap.ker (g i) := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, hker]
    rfl
  exact (Submodule.quotEquivOfEq _ _ hk).trans ((g i).quotKerEquivOfSurjective (hg i))

end ProjK0

/-! ### The class of a tensored filtered bimodule -/

namespace BalancedTensor

variable {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  {N : Type u} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

variable (k N) in
/-- The map `S ⊗_A N → M ⊗_A N` induced by the inclusion of a sub-bimodule. -/
def subBimoduleMap (S : SubBimodule B A M) :
    BalancedTensor k B A S.toSubmodule N →ₗ[B] BalancedTensor k B A M N :=
  mapLeftBimodule k N S.toSubmodule.subtype S.isBimoduleHom_subtype

theorem subBimoduleMap_injective [Module.Projective A N] (S : SubBimodule B A M) :
    Function.Injective (subBimoduleMap k N S) :=
  mapLeftBimodule_injective _ Subtype.val_injective

omit [Algebra k A] [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N] in
theorem subBimoduleMap_comp_inclusion {S T : SubBimodule B A M}
    (h : S.toSubmodule ≤ T.toSubmodule) :
    (subBimoduleMap k N T).comp
        (mapLeftBimodule k N (Submodule.inclusion h) (SubBimodule.isBimoduleHom_inclusion h)) =
      subBimoduleMap k N S :=
  extB fun _ _ => rfl

omit [Algebra k A] [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N] in
/-- `range (S ⊗_A N → M ⊗_A N)` is monotone in `S`. -/
theorem range_subBimoduleMap_mono {S T : SubBimodule B A M}
    (h : S.toSubmodule ≤ T.toSubmodule) :
    LinearMap.range (subBimoduleMap k N S) ≤ LinearMap.range (subBimoduleMap k N T) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨mapLeftBimodule k N (Submodule.inclusion h) (SubBimodule.isBimoduleHom_inclusion h) x,
    by rw [← LinearMap.comp_apply, subBimoduleMap_comp_inclusion]⟩

omit [Algebra k A] [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N] in
theorem range_subBimoduleMap_of_eq_bot {S : SubBimodule B A M} (h : S.toSubmodule = ⊥) :
    LinearMap.range (subBimoduleMap k N S) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro _ ⟨x, rfl⟩
  have hx : ∀ y : S.toSubmodule, y = 0 := fun y => Subtype.ext (by
    have h2 : (y : M) ∈ (⊥ : Submodule B M) := h ▸ y.2
    exact (Submodule.mem_bot B).1 h2)
  induction x using induction_on with
  | zero => exact map_zero _
  | tmul m n => rw [hx m, subBimoduleMap, mapLeftBimodule_tmul, map_zero, zero_tmul]
  | add x y hx' hy' => rw [map_add, hx', hy', add_zero]

omit [Algebra k A] [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N] in
theorem range_subBimoduleMap_of_eq_top {S : SubBimodule B A M} (h : S.toSubmodule = ⊤) :
    LinearMap.range (subBimoduleMap k N S) = ⊤ := by
  refine LinearMap.range_eq_top.2 (mapLeftBimodule_surjective _ fun m => ?_)
  exact ⟨⟨m, h ▸ Submodule.mem_top⟩, rfl⟩

end BalancedTensor

namespace ProjK0

open BalancedTensor

variable {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  {N : Type u} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [Module.Projective A N]
  {Y : ℕ → Type u} [∀ i, AddCommGroup (Y i)] [∀ i, Module k (Y i)] [∀ i, Module B (Y i)]
  [∀ i, IsScalarTower k B (Y i)] [∀ i, Module Aᵐᵒᵖ (Y i)] [∀ i, SMulCommClass B Aᵐᵒᵖ (Y i)]
  [∀ i, IsScalarTower k Aᵐᵒᵖ (Y i)]

/-- **The class of a tensored filtered bimodule.** Let `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = M` be a chain
of sub-bimodules of a `(B, A)`-bimodule `M`, and `π i : F (i + 1) → Y i` surjective bimodule maps
with kernel `F i`. For a projective left `A`-module `N` such that every `Y i ⊗_A N` is a finitely
generated projective `B`-module, `M ⊗_A N` is finitely generated projective and
`[M ⊗_A N] = ∑_{i < n} [Y i ⊗_A N]` in `K₀(B)`. -/
theorem exists_of_balancedTensor_eq_sum (n : ℕ) (F : ℕ → SubBimodule B A M)
    (hF : Monotone fun i => (F i).toSubmodule) (h0 : (F 0).toSubmodule = ⊥)
    (hn : (F n).toSubmodule = ⊤) (π : ∀ i, (F (i + 1)).toSubmodule →ₗ[B] Y i)
    (hπ : ∀ i, IsBimoduleHom (A := A) (π i)) (hπs : ∀ i, Function.Surjective (π i))
    (hπk : ∀ i (x : (F (i + 1)).toSubmodule), π i x = 0 ↔ (x : M) ∈ (F i).toSubmodule)
    [∀ i, Module.Finite B (BalancedTensor k B A (Y i) N)]
    [∀ i, Module.Projective B (BalancedTensor k B A (Y i) N)] :
    ∃ (_ : Module.Finite B (BalancedTensor k B A M N))
      (_ : Module.Projective B (BalancedTensor k B A M N)),
      of (FGProj.of (k := k) (A := B) (BalancedTensor k B A M N)) =
        ∑ i ∈ Finset.range n, of (FGProj.of (k := k) (A := B) (BalancedTensor k B A (Y i) N)) := by
  set G : ℕ → Submodule B (BalancedTensor k B A M N) :=
    fun i => LinearMap.range (subBimoduleMap k N (F i)) with hG
  -- `F (i + 1) ⊗_A N ≃ G (i + 1)`.
  let eG : ∀ i, BalancedTensor k B A (F i).toSubmodule N ≃ₗ[B] G i := fun i =>
    LinearEquiv.ofInjective _ (subBimoduleMap_injective (F i))
  -- The tensored inclusion and projection.
  let ι : ∀ i, BalancedTensor k B A (F i).toSubmodule N →ₗ[B]
      BalancedTensor k B A (F (i + 1)).toSubmodule N := fun i =>
    mapLeftBimodule k N (Submodule.inclusion (hF (Nat.le_succ i)))
      (SubBimodule.isBimoduleHom_inclusion (hF (Nat.le_succ i)))
  let p : ∀ i, BalancedTensor k B A (F (i + 1)).toSubmodule N →ₗ[B]
      BalancedTensor k B A (Y i) N := fun i => mapLeftBimodule k N (π i) (hπ i)
  have hex : ∀ i, Function.Exact (ι i) (p i) := fun i => by
    refine mapLeftBimodule_exact _ _ fun x => ?_
    rw [hπk]
    constructor
    · intro hx
      exact ⟨⟨x.1, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  refine exists_of_eq_sum_of_chain_surj n G
    (fun i j hij => range_subBimoduleMap_mono (hF hij)) (range_subBimoduleMap_of_eq_bot h0)
    (range_subBimoduleMap_of_eq_top hn)
    (fun i => FGProj.of (k := k) (A := B) (BalancedTensor k B A (Y i) N))
    (fun i => (p i).comp (eG (i + 1)).symm.toLinearMap)
    (fun i => (mapLeftBimodule_surjective (hπ i) (hπs i)).comp (eG (i + 1)).symm.surjective)
    (fun i x => ?_)
  obtain ⟨t, rfl⟩ := (eG (i + 1)).surjective x
  change p i ((eG (i + 1)).symm (eG (i + 1) t)) = 0 ↔ _
  rw [LinearEquiv.symm_apply_apply, hex i t]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    change subBimoduleMap k N (F i) s = subBimoduleMap k N (F (i + 1)) (ι i s)
    rw [← LinearMap.comp_apply, subBimoduleMap_comp_inclusion]
  · rintro ⟨s, hs⟩
    refine ⟨s, subBimoduleMap_injective (F (i + 1)) ?_⟩
    rw [← LinearMap.comp_apply, subBimoduleMap_comp_inclusion, hs]
    rfl

end ProjK0

end

end Categorification
