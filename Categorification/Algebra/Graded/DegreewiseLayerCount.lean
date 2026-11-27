/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.HomogeneousLayerCount

/-!
# Layer counts in one degree of a locally finite graded space

The dimension count of Webster, arXiv:1309.3796v3, proof of Proposition 5.21, in a fixed
degree `n` of a graded space `V` that need not be finite-dimensional: only the degree-`n`
piece `ℳ n` (and, for a generator of degree `d`, the piece `ℳ (n - d)`) must be.

* `finrank_iSup_le_sum_layerRank_of_le`: subspaces inside a finite-dimensional subspace satisfy
  the filtration inequality `dim Σ N_φ ≤ Σ dim (N_{≥φ}/N_{>φ})`.
* `finrank_inf_grade_le_sum`: its degree-`n` form for a filtration by homogeneous subspaces.
* `layerRank_grade_le_of_generator`: if `P_{≥φ} = μ(X) + P_{>φ}` for `μ` of degree `d` and
  `μ(U) ⊆ P_{>φ}`, then the degree-`n` layer has dimension at most
  `dim X_{n-d} - dim U_{n-d}`; with equality, `μ x ∈ P_{>φ}` forces `x ∈ U` in degree `n - d`.
-/

namespace Categorification.Graded

open DirectSum Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (rel : ι → ι → Prop)

private theorem finrankK_self' (X : Submodule k V) : Submodule.finrankK k X = finrank k X := by
  rw [Submodule.finrankK, Submodule.restrictScalars_self]

/-- **The filtration inequality inside a finite-dimensional subspace** `F`. -/
theorem finrank_iSup_le_sum_layerRank_of_le (F : Submodule k V) [FiniteDimensional k F]
    (hirr : ∀ φ, ¬ rel φ φ) (htr : ∀ a b c, rel a b → rel b c → rel a c)
    (N : ι → Submodule k V) (hN : ∀ g, N g ≤ F) :
    finrank k (⨆ g, N g :) ≤ ∑ g, Submodule.layerRank (k := k) rel N g := by
  classical
  let N' : ι → Submodule k F := fun g => (N g).comap F.subtype
  have hN' : ∀ g, (N' g).map F.subtype = N g := fun g => by
    change ((N g).comap F.subtype).map F.subtype = N g
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (hN g)]
  have hfr : ∀ X : Submodule k F,
      Submodule.finrankK k (X.map F.subtype) = Submodule.finrankK k X := fun X => by
    rw [finrankK_self', finrankK_self']
    exact (Submodule.equivMapOfInjective F.subtype Subtype.val_injective X).finrank_eq.symm
  have habove : ∀ g, Submodule.above rel N g = (Submodule.above rel N' g).map F.subtype :=
    fun g => by simp only [Submodule.above, Submodule.map_iSup, hN']
  have hlayer : ∀ g, Submodule.layerRank (k := k) rel N g =
      Submodule.layerRank (k := k) rel N' g := fun g => by
    unfold Submodule.layerRank
    rw [habove, ← hN' g, ← Submodule.map_sup, hfr, hfr]
  have h := Submodule.finrankK_iSup_le (k := k) rel N' hirr htr Finset.univ (by simp)
  simp only [Finset.mem_univ, iSup_pos] at h
  have hsup : (⨆ g, N g) = (⨆ g, N' g).map F.subtype := by
    rw [Submodule.map_iSup]
    simp only [hN']
  rw [← finrankK_self', hsup, hfr]
  simpa only [hlayer] using h

variable (ℳ : ℤ → Submodule k V) [Decomposition ℳ]

variable {ℳ} in
/-- **The filtration inequality in degree `n`**, for a filtration by homogeneous subspaces of a
space whose degree-`n` piece is finite-dimensional. -/
theorem finrank_inf_grade_le_sum (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) {N : ι → Submodule k V}
    (hN : ∀ g, IsHomogeneousSubspace ℳ (N g)) {W : Submodule k V} (hspan : (⨆ g, N g) = W)
    (n : ℤ) [FiniteDimensional k (ℳ n)] :
    finrank k (W ⊓ ℳ n :) ≤ ∑ g, Submodule.layerRank (k := k) rel (fun g => N g ⊓ ℳ n) g := by
  rw [← hspan, iSup_inf_grade hN n]
  exact finrank_iSup_le_sum_layerRank_of_le rel (ℳ n) hirr htr _ fun _ => inf_le_right

omit [Fintype ι] [DecidableEq ι] in
variable {ℳ} in
/-- **A layer in a fixed degree, bounded by a generator.** Suppose `P_{≥φ} = μ(X) + P_{>φ}` for a
homogeneous `X` and `μ` of degree `d`, and `μ(U) ⊆ P_{>φ}` for some `U ≤ X`. If `ℳ n` and
`ℳ (n - d)` are finite-dimensional, the degree-`n` layer plus `dim U_{n-d}` is at most
`dim X_{n-d}`, and when they are equal every `x ∈ X_{n-d}` with `μ x ∈ P_{>φ}` lies in `U`. -/
theorem layerRank_grade_le_of_generator {N : ι → Submodule k V}
    (hN : ∀ g, IsHomogeneousSubspace ℳ (N g)) (g : ι) {μ : V →ₗ[k] V} {d : ℤ}
    (hμ : ∀ m, ∀ x ∈ ℳ m, μ x ∈ ℳ (m + d)) {X U : Submodule k V}
    (hX : IsHomogeneousSubspace ℳ X) (hUX : U ≤ X)
    (hgen : N g ⊔ Submodule.above rel N g = X.map μ ⊔ Submodule.above rel N g)
    (hU : ∀ x ∈ U, μ x ∈ Submodule.above rel N g) (n : ℤ) [FiniteDimensional k (ℳ n)]
    [FiniteDimensional k (ℳ (n - d))] :
    Submodule.layerRank (k := k) rel (fun g => N g ⊓ ℳ n) g + finrank k (U ⊓ ℳ (n - d) :) ≤
        finrank k (X ⊓ ℳ (n - d) :) ∧
      (Submodule.layerRank (k := k) rel (fun g => N g ⊓ ℳ n) g +
          finrank k (U ⊓ ℳ (n - d) :) = finrank k (X ⊓ ℳ (n - d) :) →
        ∀ x ∈ X ⊓ ℳ (n - d), μ x ∈ Submodule.above rel N g → x ∈ U) := by
  classical
  set P := Submodule.above rel N g
  have hP : IsHomogeneousSubspace ℳ P :=
    IsHomogeneousSubspace.iSup fun _ => IsHomogeneousSubspace.iSup fun _ => hN _
  rw [layerRank_grade_eq rel hN g n]
  set Z := (N g ⊔ P) ⊓ ℳ n
  set Zb := P ⊓ ℳ n
  set Y := X ⊓ ℳ (n - d)
  set U' := U ⊓ ℳ (n - d)
  have hZf : FiniteDimensional k Z := Submodule.finiteDimensional_of_le inf_le_right
  have hYf : FiniteDimensional k Y := Submodule.finiteDimensional_of_le inf_le_right
  have hZb : Zb ≤ Z := inf_le_inf_right _ le_sup_right
  have hU' : U' ≤ Y := inf_le_inf_right _ hUX
  have hμY : ∀ y : Y, μ y ∈ Z := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [hgen]
      exact Submodule.mem_sup_left ⟨y, y.2.1, rfl⟩
    · have := hμ _ _ y.2.2
      rwa [sub_add_cancel] at this
  let W := Zb.comap Z.subtype
  let f : Y →ₗ[k] Z ⧸ W := W.mkQ ∘ₗ (μ.domRestrict Y).codRestrict Z hμY
  have hf_apply (y : Y) : f y = W.mkQ ⟨μ y, hμY y⟩ := rfl
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨z, rfl⟩ := W.mkQ_surjective z
    have hz : (z : V) ∈ X.map μ ⊔ P := hgen ▸ z.2.1
    obtain ⟨a, ⟨x, hx, rfl⟩, p, hp, hap⟩ := Submodule.mem_sup.1 hz
    let y : Y := ⟨decompose ℳ x (n - d), hX _ x hx, (decompose ℳ x (n - d)).2⟩
    refine ⟨y, ?_⟩
    rw [hf_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change (μ y - z : V) ∈ Zb
    have hzn : (z : V) = decompose ℳ (z : V) n := (decompose_of_mem_same ℳ z.2.2).symm
    have hcomp : (μ y - z : V) = -(decompose ℳ p n : V) := by
      rw [hzn, ← hap, decompose_add, DirectSum.add_apply, Submodule.coe_add,
        decompose_map_of_shift hμ]
      abel
    rw [hcomp]
    exact neg_mem ⟨hP n p hp, (decompose ℳ p n).2⟩
  have hker_iff : ∀ y : Y, f y = 0 ↔ μ y ∈ P := by
    intro y
    rw [hf_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact ⟨fun h => h.1, fun h => ⟨h, (hμY y).2⟩⟩
  have hUker : U'.comap Y.subtype ≤ LinearMap.ker f := fun y hy =>
    (hker_iff y).2 (hU y hy.1)
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
  have h2 := Submodule.finrank_quotient_add_finrank W
  rw [show finrank k W = finrank k Zb from (Submodule.comapSubtypeEquivOfLe hZb).finrank_eq] at h2
  have h3 := Submodule.finrank_mono hUker
  rw [(Submodule.comapSubtypeEquivOfLe hU').finrank_eq] at h3
  have hZbZ := Submodule.finrank_mono hZb
  refine ⟨by omega, fun heq x hx hμx => ?_⟩
  have hkeq : U'.comap Y.subtype = LinearMap.ker f := by
    refine Submodule.eq_of_le_of_finrank_eq hUker ?_
    rw [(Submodule.comapSubtypeEquivOfLe hU').finrank_eq]
    omega
  have hmem : (⟨x, hx⟩ : Y) ∈ LinearMap.ker f := (hker_iff _).2 hμx
  rw [← hkeq] at hmem
  exact hmem.1

end Categorification.Graded
