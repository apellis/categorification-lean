/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NegativeTensor
import Categorification.WeightedKLR.RedStrands.TensorWordWeights

/-!
# `𝔮_N` is injective in bounded weights

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 4.39. The vector `p̃_w` of a word of black content `β` lies in
`(⊕_{γ ≤ β} U⁻_γ) ⊗ V^λ` (`negWordVector_mem_negTensorBelow`). Once `⟨α_i^∨, λ₀⟩ ≥ |β|` for
all `i`, the evaluation `u ↦ u v_{λ₀}` is injective on `⊕_{γ ≤ β} U⁻_γ`, so `𝔮_N` is injective
on this subspace (`negTensorMap_injective_below`).

## Main definitions

* `negBelow β` : the subspace `⊕_{γ ≤ β} U⁻_γ` of `U⁻`.
* `negTensorBelow wt β` : the subspace `(⊕_{γ ≤ β} U⁻_γ) ⊗ V^λ`.

## Main results

* `evq_injective_negBelow`, `negTensorMap_injective_below`, `negWordVector_mem_negTensorBelow`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩
local notation "hvt" => transcendental_ratFuncX

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "ρ" => tensorRepresentation

variable (D) in
/-- The subspace `⊕_{γ ≤ β} U⁻_γ` of `U⁻`. -/
def negBelow (β : I →₀ ℕ) : Submodule 𝕂 (Um D 𝕍) := ⨆ γ ∈ Finset.Iic β, Uw D 𝕍 γ

theorem Uw_le_negBelow {γ β : I →₀ ℕ} (h : γ ≤ β) : Uw D 𝕍 γ ≤ negBelow D β :=
  le_biSup (fun γ => Uw D 𝕍 γ) (Finset.mem_Iic.mpr h)

theorem negBelow_mono {γ β : I →₀ ℕ} (h : γ ≤ β) : negBelow D γ ≤ negBelow D β :=
  iSup₂_le fun _ hδ => Uw_le_negBelow ((Finset.mem_Iic.mp hδ).trans h)

omit [DecidableEq I] in
/-- `F_i U⁻_γ ⊆ U⁻_{γ + i}`. -/
theorem negF_mem_Uw (i : I) {γ : I →₀ ℕ} {u : Um D 𝕍} (hu : u ∈ Uw D 𝕍 γ) :
    negF D i u ∈ Uw D 𝕍 (γ + Finsupp.single i 1) := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨FreeAlgebra.ι 𝕂 i * y, ?_, rfl⟩
  rw [add_comm]
  exact LusztigF.mul_mem_weightSpace (LusztigF.θ_mem_weightSpace i) hy

theorem negF_mem_negBelow (i : I) {β : I →₀ ℕ} {u : Um D 𝕍} (hu : u ∈ negBelow D β) :
    negF D i u ∈ negBelow D (β + Finsupp.single i 1) := by
  have h : negBelow D β ≤ (negBelow D (β + Finsupp.single i 1)).comap (negF D i) :=
    iSup₂_le fun γ hγ x hx => Submodule.mem_comap.mpr
      (Uw_le_negBelow (γ := γ + Finsupp.single i 1) (β := β + Finsupp.single i 1)
        (add_le_add_left (Finset.mem_Iic.mp hγ) _) (negF_mem_Uw i hx))
  exact h hu

/-- **`u ↦ u v_λ` is injective on `⊕_{γ ≤ β} U⁻_γ`** once `⟨α_i^∨, λ⟩ ≥ |β|` for all `i`. -/
theorem evq_injective_negBelow (hR : R.IsXRegular) {Λ : Dom R} {β : I →₀ ℕ} [Finite I]
    (hΛ : ∀ i, (β.degree : ℤ) ≤ Λ.1 (R.coroot i)) :
    Function.Injective ((evq hvt Λ).comp (negBelow D β).subtype) := by
  classical
  have hv' := pow_ne_one_of_transcendental' (k := 𝕂) hvt
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨u, hu⟩ h0
  obtain ⟨c, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hu
  change evq hvt Λ (∑ γ ∈ Finset.Iic β, (c γ : Um D 𝕍)) = 0 at h0
  rw [map_sum] at h0
  have hind : iSupIndep fun γ : I →₀ ℕ =>
      weightSpace R 𝕍 (IrreducibleModule R 𝕍 Λ.1) (Λ.1 - R.rootSum γ) := by
    refine (iSupIndep_weightSpace hv').comp fun γ γ' h => ?_
    by_contra hne
    obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
    have := congrArg (fun f : Y →+ ℤ => f μ) h
    simp only [AddMonoidHom.sub_apply, sub_right_inj] at this
    exact hμ this
  have hmem : ∀ γ ∈ Finset.Iic β, evq hvt Λ (c γ : Um D 𝕍) ∈
      weightSpace R 𝕍 (IrreducibleModule R 𝕍 Λ.1) (Λ.1 - R.rootSum γ) := by
    intro γ _
    obtain ⟨y, hy, hyc⟩ := (c γ).2
    rw [← hyc]
    exact ev_mem_weightSpace hv' hR Λ.1 hy
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind _ _ hmem h0
  refine Subtype.ext (Finset.sum_eq_zero fun γ hγ => ?_)
  have hγΛ : ∀ i, (γ.degree : ℤ) ≤ Λ.1 (R.coroot i) := fun i =>
    le_trans (by exact_mod_cast Finsupp.degree_mono (Finset.mem_Iic.mp hγ)) (hΛ i)
  have hinj : Function.Injective ((evq hvt Λ).comp (Uw D 𝕍 γ).subtype) :=
    evq_injective (hR := hR) hγΛ
  have := @hinj (c γ) 0 (by
    change evq hvt Λ (c γ : Um D 𝕍) = evq hvt Λ ((0 : Uw D 𝕍 γ) : Um D 𝕍)
    rw [Submodule.coe_zero, map_zero]
    exact hz γ hγ)
  exact congrArg Subtype.val this

variable (D) in
/-- The subspace `(⊕_{γ ≤ β} U⁻_γ) ⊗ V^λ` of `U⁻ ⊗ V^λ`. -/
def negTensorBelow {ℓ : ℕ} (wt : Fin ℓ → Dom R) (β : I →₀ ℕ) : Submodule 𝕂 (NegTensor D wt) :=
  LinearMap.range (TensorProduct.map (negBelow D β).subtype (LinearMap.id (M := TensorSpace wt)))

theorem negTensorBelow_mono {ℓ : ℕ} (wt : Fin ℓ → Dom R) {γ β : I →₀ ℕ} (h : γ ≤ β) :
    negTensorBelow D wt γ ≤ negTensorBelow D wt β := by
  have he : TensorProduct.map (negBelow D γ).subtype (LinearMap.id (M := TensorSpace wt)) =
      TensorProduct.map (negBelow D β).subtype LinearMap.id ∘ₗ
        TensorProduct.map (Submodule.inclusion (negBelow_mono h)) LinearMap.id := by
    rw [← TensorProduct.map_comp, Submodule.subtype_comp_inclusion, LinearMap.id_comp]
  rw [negTensorBelow, negTensorBelow, he]
  exact LinearMap.range_comp_le_range _ _

theorem tmul_mem_negTensorBelow {ℓ : ℕ} (wt : Fin ℓ → Dom R) {β : I →₀ ℕ} {u : Um D 𝕍}
    (hu : u ∈ negBelow D β) (x : TensorSpace wt) : u ⊗ₜ[𝕂] x ∈ negTensorBelow D wt β :=
  ⟨(⟨u, hu⟩ : negBelow D β) ⊗ₜ[𝕂] x, rfl⟩

/-- A submodule of a tensor product spanned by the pure tensors it contains. -/
private theorem mem_negTensorBelow_of {ℓ : ℕ} (wt : Fin ℓ → Dom R) (β β' : I →₀ ℕ)
    (f : NegTensor D wt →ₗ[𝕂] NegTensor D wt)
    (hf : ∀ (u : Um D 𝕍), u ∈ negBelow D β → ∀ x, f (u ⊗ₜ[𝕂] x) ∈ negTensorBelow D wt β')
    {z : NegTensor D wt} (hz : z ∈ negTensorBelow D wt β) : f z ∈ negTensorBelow D wt β' := by
  obtain ⟨z, rfl⟩ := hz
  induction z using TensorProduct.inductionOn with
  | tmul u x => exact hf u u.2 x
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

theorem negTensorF_mem {ℓ : ℕ} (wt : Fin ℓ → Dom R) (i : I) {β : I →₀ ℕ}
    {z : NegTensor D wt} (hz : z ∈ negTensorBelow D wt β) :
    negTensorF D wt i z ∈ negTensorBelow D wt (β + Finsupp.single i 1) := by
  refine mem_negTensorBelow_of wt β _ _ (fun u hu x => ?_) hz
  simp only [negTensorF, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  exact add_mem (tmul_mem_negTensorBelow wt (negF_mem_negBelow i hu) _)
    (tmul_mem_negTensorBelow wt (negBelow_mono le_self_add hu) _)

theorem negTensorDivF_mem {ℓ : ℕ} (wt : Fin ℓ → Dom R) (i : I) (a : ℕ) {β : I →₀ ℕ}
    {z : NegTensor D wt} (hz : z ∈ negTensorBelow D wt β) :
    negTensorDivF D wt i a z ∈ negTensorBelow D wt (β + Finsupp.single i a) := by
  have hpow : ∀ m : ℕ, ∀ z ∈ negTensorBelow D wt β,
      ((negTensorF D wt i) ^ m) z ∈ negTensorBelow D wt (β + Finsupp.single i m) := by
    intro m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ', Module.End.mul_apply, Finsupp.single_add, ← add_assoc]
      exact negTensorF_mem wt i (ih z hz)
  rw [negTensorDivF, qDivPow, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (hpow a z hz)

theorem appendHighest_mem {n : ℕ} (wt : Fin (n + 1) → Dom R) {β : I →₀ ℕ}
    {z : NegTensor D (fun j : Fin n => wt j.castSucc)} (hz : z ∈ negTensorBelow D _ β) :
    TensorProduct.map LinearMap.id (appendHighest wt) z ∈ negTensorBelow D wt β := by
  obtain ⟨z, rfl⟩ := hz
  refine ⟨TensorProduct.map LinearMap.id (appendHighest wt) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp]
  simp only [LinearMap.id_comp, LinearMap.comp_id]

/-- **`p̃_w ∈ (⊕_{γ ≤ β} U⁻_γ) ⊗ V^λ`** for a word of black content `β`. -/
theorem negWordVector_mem_negTensorBelow : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin n → Dom R),
    negWordVector D w wt ∈ negTensorBelow D wt w.content
  | _, .empty, wt => by
    refine tmul_mem_negTensorBelow wt (Uw_le_negBelow le_rfl ?_) _
    exact ⟨1, LusztigF.one_mem_weightSpace, rfl⟩
  | _, .red w, wt => appendHighest_mem wt (negWordVector_mem_negTensorBelow w _)
  | _, .black w i a, wt => negTensorDivF_mem wt i a (negWordVector_mem_negTensorBelow w wt)

/-- **`𝔮_N` is injective on `(⊕_{γ ≤ β} U⁻_γ) ⊗ V^λ`** once `⟨α_i^∨, λ₀⟩ ≥ |β|` for all `i`
(Webster, arXiv:1309.3796v3, proof of Proposition 4.39). -/
theorem negTensorMap_injective_below (hR : R.IsXRegular) [Finite I] {n : ℕ}
    (wt : Fin (n + 1) → Dom R) {β : I →₀ ℕ} (hΛ : ∀ i, (β.degree : ℤ) ≤ (wt 0).1 (R.coroot i))
    {x y : NegTensor D (fun j : Fin n => wt j.succ)} (hx : x ∈ negTensorBelow D _ β)
    (hy : y ∈ negTensorBelow D _ β) (h : negTensorMap D wt x = negTensorMap D wt y) : x = y := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  have hinj : Function.Injective (negTensorMap D wt ∘ₗ
      TensorProduct.map (negBelow D β).subtype LinearMap.id) := by
    have he : negTensorMap D wt ∘ₗ TensorProduct.map (negBelow D β).subtype LinearMap.id =
        (tensorSplitFirst wt).symm.toLinearMap ∘ₗ
          ((evq hvt (wt 0)).comp (negBelow D β).subtype).rTensor _ := by
      apply TensorProduct.ext'
      intro u x
      rfl
    rw [he]
    exact (tensorSplitFirst wt).symm.injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (evq_injective_negBelow hR hΛ))
  exact congrArg _ (hinj h)

end Categorification.Stendhal.FirstWeight
