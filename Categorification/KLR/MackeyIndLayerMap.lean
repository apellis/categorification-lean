/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndAssoc

/-!
# Functoriality of the Mackey layers of an induced module

For a module map `g : N → N'` over `R(ν) ⊗ R(ν')`, `Ind g = 1 ⊗ g` preserves the Mackey
filtration of `Ind N` (`mapRight_mem_indMackeyStep`), so it induces maps on the layers
(`indMackeyLayerMap`). These commute with the action of elements preserving the filtration
(`indMackeyLayerMap_act`), compose (`indMackeyLayerMap_comp`), and are intertwined by the maps
`Ξ_λ` with `1 ⊗ (1 ⊗ g)` (`indMackeyLeftMap_mapRight`).

This is used in Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5, to
let the window idempotent `ε_{e(w)}` act on the layers of the induced model of `S_cut(Res X)`.
Webster's proof does not spell this out.

## Main definitions

* `KLR.KLRAlgebra.indMackeyLayerMap`.

## Main results

* `KLR.KLRAlgebra.indMackeyLayerMap_act`, `KLR.KLRAlgebra.indMackeyLayerMap_comp`,
  `KLR.KLRAlgebra.indMackeyLeftMap_mapRight`.
-/

noncomputable section

namespace Categorification.KLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

section Steps

variable {ν ν' : Multiset I} {N N' N'' : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν ν') N] [IsScalarTower k (TensorKLR Q ν ν') N]
  [AddCommGroup N'] [Module k N'] [Module (TensorKLR Q ν ν') N']
  [IsScalarTower k (TensorKLR Q ν ν') N']
  [AddCommGroup N''] [Module k N''] [Module (TensorKLR Q ν ν') N'']
  [IsScalarTower k (TensorKLR Q ν ν') N'']

/-- `Ind g` preserves the steps of the Mackey filtration. -/
theorem mapRight_mem_indMackeyStep (g : N →ₗ[TensorKLR Q ν ν'] N') {n c : ℕ}
    {y : Ind Q ν ν' N} (hy : y ∈ indMackeyStep Q ν ν' N n c) :
    BalancedTensor.mapRight g y ∈ indMackeyStep Q ν ν' N' n c := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, x, hw, rfl⟩ := hy
    rw [BalancedTensor.mapRight_tmul]
    exact Submodule.subset_span ⟨w, g x, hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul a y _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a h

theorem mapRight_mem_indMackeyLower (g : N →ₗ[TensorKLR Q ν ν'] N') {n c : ℕ}
    {y : Ind Q ν ν' N} (hy : y ∈ indMackeyLower Q ν ν' N n c) :
    BalancedTensor.mapRight g y ∈ indMackeyLower Q ν ν' N' n c := by
  cases c with
  | zero =>
    rw [indMackeyLower, Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  | succ c => exact mapRight_mem_indMackeyStep g hy

/-- **The map of Mackey layers induced by a module map** `g : N → N'`. -/
def indMackeyLayerMap (g : N →ₗ[TensorKLR Q ν ν'] N') (n c : ℕ) :
    IndMackeyLayer Q ν ν' N n c →ₗ[k] IndMackeyLayer Q ν ν' N' n c :=
  Submodule.mapQ _ _
    ((((BalancedTensor.mapRight g).restrictScalars k).comp
      (indMackeyStep Q ν ν' N n c).subtype).codRestrict _ fun y =>
        mapRight_mem_indMackeyStep g y.2)
    fun _ hy => mapRight_mem_indMackeyLower g hy

theorem indMackeyLayerMap_mk (g : N →ₗ[TensorKLR Q ν ν'] N') {n c : ℕ}
    (y : indMackeyStep Q ν ν' N n c) :
    indMackeyLayerMap g n c (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨BalancedTensor.mapRight g (y : Ind Q ν ν' N),
        mapRight_mem_indMackeyStep g y.2⟩ :=
  rfl

/-- The layer maps commute with the action of elements preserving the Mackey filtration. -/
theorem indMackeyLayerMap_act (g : N →ₗ[TensorKLR Q ν ν'] N') {n : ℕ}
    (z : KLRAlgebra k Q (ν + ν'))
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c →
      z * y ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c) (c : ℕ)
    (y : IndMackeyLayer Q ν ν' N n c) :
    indMackeyLayerMap g n c (indMackeyLayerAct N z hz c y) =
      indMackeyLayerAct N' z hz c (indMackeyLayerMap g n c y) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [indMackeyLayerAct_mk, indMackeyLayerMap_mk, indMackeyLayerMap_mk, indMackeyLayerAct_mk]
  congr 1
  exact Subtype.ext (map_smul (BalancedTensor.mapRight g) z (y : Ind Q ν ν' N))

/-- The layer maps compose. -/
theorem indMackeyLayerMap_comp (g : N →ₗ[TensorKLR Q ν ν'] N')
    (g' : N' →ₗ[TensorKLR Q ν ν'] N'') (n c : ℕ) (y : IndMackeyLayer Q ν ν' N n c) :
    indMackeyLayerMap g' n c (indMackeyLayerMap g n c y) = indMackeyLayerMap (g' ∘ₗ g) n c y := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [indMackeyLayerMap_mk, indMackeyLayerMap_mk, indMackeyLayerMap_mk]
  congr 1
  apply Subtype.ext
  change _ = BalancedTensor.mapRight (g' ∘ₗ g) (y : Ind Q ν ν' N)
  rw [BalancedTensor.mapRight_comp]
  rfl

/-- The layer map of an idempotent is an idempotent. -/
theorem indMackeyLayerMap_idem (g : N →ₗ[TensorKLR Q ν ν'] N) (hg : g ∘ₗ g = g) (n c : ℕ)
    (y : IndMackeyLayer Q ν ν' N n c) :
    indMackeyLayerMap g n c (indMackeyLayerMap g n c y) = indMackeyLayerMap g n c y := by
  rw [indMackeyLayerMap_comp, hg]

end Steps

section Xi

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')
  {N N' : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]
  [AddCommGroup N'] [Module k N'] [Module (TensorKLR Q ν'' ν''') N']
  [IsScalarTower k (TensorKLR Q ν'' ν''') N']

theorem indSubquotBil_map (g : N →ₗ[TensorKLR Q ν'' ν'''] N') {c : ℕ}
    (z : MackeySubquot Q h c) (x : N) :
    indSubquotBil h N' c z (g x) =
      indMackeyLayerMap g (Multiset.card ν) c (indSubquotBil h N c z x) := by
  obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
  rw [indSubquotBil_of, indSubquotBil_of, indMackeyLayerMap_mk]
  rfl

/-- **`Ξ_λ` intertwines `1 ⊗ (1 ⊗ g)` with the layer map of `g`.** -/
theorem indMackeyLeftMap_mapRight (g : N →ₗ[TensorKLR Q ν'' ν'''] N')
    (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hc : Multiset.card q.β = c)
    (w : MackeyLeftInd Q N q) :
    indMackeyLeftMap h N' q hc (BalancedTensor.mapRight (BalancedTensor.mapRight g) w) =
      indMackeyLayerMap g (Multiset.card ν) c (indMackeyLeftMap h N q hc w) := by
  induction w using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul t u =>
    rw [BalancedTensor.mapRight_tmul]
    induction u using BalancedTensor.induction_on with
    | zero => simp only [map_zero, BalancedTensor.tmul_zero]
    | tmul b x =>
      rw [BalancedTensor.mapRight_tmul, indMackeyLeftMap_tmul, indMackeyLeftMap_tmul,
        indSubquotBil_map]
    | add u u' hu hu' =>
      rw [map_add, BalancedTensor.tmul_add, BalancedTensor.tmul_add, map_add, map_add, map_add,
        hu, hu']
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', map_add]

end Xi

end KLRAlgebra

end Categorification.KLR
