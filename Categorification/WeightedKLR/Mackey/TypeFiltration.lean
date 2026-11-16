/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.TypeShuffle

/-!
# The maps of shuffle types into the subquotients of the Mackey filtration

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). For a shuffle type `μ` (the shuffle type of some
relabelling) and the set `Z = blockLeft ν' ν₁ μ`, every four-block shuffle element
`fourShuffle Z B` is a shuffle element `ψ^W_y` of a relabelling `y` of shuffle type `μ`, with
bottom end `B` itself (`GalleryAlgebra.fourShuffle_eq_rankShuffleElt`): `y` is obtained from any
relabelling of type `μ` by relabelling inside the blocks of `ν'`, and the block sort of the
rank-ordered chamber `B` is trivial. Hence `fourShuffle Z B` lies in the step of the filtration of
every lower set containing `μ`, and so does `x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C` for the sum `ψ_μ` of
these elements (`GalleryAlgebra.typeInductionAux_mem_mackeyFilt`). This gives one map into the
subquotient per shuffle type (`GalleryAlgebra.typeInductionMap`), and these maps, over the
shuffle types in `S` but not in `S'`, are jointly surjective
(`GalleryAlgebra.iSup_range_typeInductionMap`).

## Main definitions

* `GalleryAlgebra.typeInductionMap`: `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` into the subquotient.

## Main results

* `GalleryAlgebra.fourShuffle_eq_rankShuffleElt`: a four-block shuffle element of type `μ` is a
  shuffle element of a relabelling of type `μ`.
* `GalleryAlgebra.typeInductionAux_mem_mackeyFilt`: the map of `μ` lands in the step `S`.
* `GalleryAlgebra.iSup_range_typeInductionMap`: the subquotient is spanned by the images of the
  maps of the shuffle types.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

namespace Juxtapose

/-- The block sort of a rank-ordered separated chamber is trivial. -/
theorem blockSort_eq_one_of_isRankOrdered (hν : ν₁ + ν₂ = ν) {B : FullChamber Γ ν}
    (hB : B.IsRankOrdered) (hBs : IsSeparated (fun t => decide (t.IsLeft ν₁)) B) :
    blockSort hν B = 1 :=
  eq_one_of_isRankOrdered_smul hB (blockSort_spec hν hBs).1

end Juxtapose

namespace GalleryAlgebra

/-- **A relabelling of a given shuffle type realizing a set of four blocks.** For `B` separated
by the strands of `ν'` and any relabelling `g`, there is a relabelling `y` of the same shuffle
type `μ` as `g` sending exactly the strands of `blockLeft ν' ν₁ μ` into the first block of
`ν₁`. -/
theorem exists_colPerm_isLeft_eq_blockLeft (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (g : ColPerm ν) {B : FullChamber Γ ν}
    (hBs : IsSeparated (fun t => decide (t.IsLeft ν')) B) :
    ∃ y : ColPerm ν, (fun t => decide ((y.1 t).IsLeft ν₁)) =
        blockLeft ν' ν₁ (shuffleType ν' ν₁ g) ∧
      shuffleType ν' ν₁ y = shuffleType ν' ν₁ g := by
  set v := blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
    (fun t => decide ((g.1 t).IsLeft ν₁)) B)
  refine ⟨g * v⁻¹, rankShuffleSet_eq_blockLeft hν' hν₁ g hBs, ?_⟩
  have e2 := shuffleType_mul_of_image_right ν' ν₁ (y := v)
    (fun i => image_rightStrands_of_mem (blockSort_mem_leftBlockStab (Γ := Γ) hν' _) i)
    (g * v⁻¹)
  rw [inv_mul_cancel_right] at e2
  exact e2.symm

/-- **A four-block shuffle element is a shuffle element.** If `B` is a four-block chamber for the
strands of `ν'` and the set `{t | y t ∈ ν₁}` of a relabelling `y`, then
`fourShuffle {t | y t ∈ ν₁} B = ψ^W_y` computed from `B`, and the bottom end of `ψ^W_y` is `B`. -/
theorem fourShuffle_eq_rankShuffleElt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (y : ColPerm ν) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (fun t => decide ((y.1 t).IsLeft ν₁)) B) :
    rankShuffleBot hν' ν₁ y B = B ∧
      fourShuffle k hD hZ (fun t => decide ((y.1 t).IsLeft ν₁)) B =
        rankShuffleElt k hν' hν₁ hD hZ y B := by
  have hBs := hB.isSeparated
  have hv : blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
      (fun t => decide ((y.1 t).IsLeft ν₁)) B) = 1 := by
    rw [hB.2]
    exact blockSort_eq_one_of_isRankOrdered hν' hB.1 hBs
  have hbot : rankShuffleBot hν' ν₁ y B = B := by
    rw [rankShuffleBot, hv, one_smul, hB.2]
  have hset : rankShuffleSet hν' ν₁ y B = fun t => decide ((y.1 t).IsLeft ν₁) := by
    funext t
    rw [rankShuffleSet, hv]
    rfl
  refine ⟨hbot, ?_⟩
  rw [rankShuffleElt_eq_fourShuffle hν' hν₁ hD hZ y hBs, hset, hbot]

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **The four-block shuffle elements of a shuffle type lie in the filtration.** Let `μ` be the
shuffle type of some relabelling and `S` a lower set containing `μ`. For every four-block
chamber `B` for the strands of `ν'` and `blockLeft ν' ν₁ μ`, the element
`fourShuffle (blockLeft ν' ν₁ μ) B` lies in the step `S` of the filtration of `e T * A * e B`
for a rank-ordered chamber `T` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem exists_fourShuffle_mem_mackeyFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B) :
    ∃ T : FullChamber Γ ν, T.IsRankOrdered ∧
      fourShuffle k hD hZ (blockLeft ν' ν₁ μ) B ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ T B S := by
  obtain ⟨g, rfl⟩ := hμ
  obtain ⟨y, hy, hty⟩ := exists_colPerm_isLeft_eq_blockLeft hν' hν₁ g hB.isSeparated
  rw [← hy] at hB ⊢
  obtain ⟨hbot, heq⟩ := fourShuffle_eq_rankShuffleElt (k := k) hν' hν₁ hD hZ y hB
  refine ⟨rankShuffleTop hν₁ y B, isRankOrdered_rankShuffleTop hν₁ y B, ?_⟩
  have hmem := rankShuffleElt_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hS (hty ▸ hμS) B
  rw [hbot] at hmem
  rw [heq]
  exact hmem

/-- **The map of a shuffle type lands in the filtration.** For rank-ordered `C`, `D`, a lower set
`S` of shuffle types and a shuffle type `μ ∈ S` of some relabelling, the map
`x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C` takes values in the step `S` of the filtration of
`e D * A * e C` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem typeInductionAux_mem_mackeyFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered) {S : Set (I → ℕ)}
    (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁))
    (z : (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')) :
    typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ μ) z ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [typeInductionAux_tmul, typeShuffle, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun B hB => ?_
    have hB' := (Finset.mem_filter.1 hB).2
    obtain ⟨T, hT, hmem⟩ := exists_fourShuffle_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hS hμS
      hμ hB'
    exact inductionMap_mul_mul_mem_mackeyFilt hP hD hZ hΓ hW hL hν₁ hν' hB'.1 hC hT hD' hS x y
      hmem
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb

variable (k) in
/-- **The map of a shuffle type to the subquotient.** For a shuffle type `μ` of some relabelling
lying in the lower set `S`, the `k`-linear map `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` from
`(W_{ν₁} ⊗ W_{ν₂}) ⊗ (W_{ν'} ⊗ W_{ν''})` to the quotient of the step `S` of the filtration of
`e D * A * e C` by the step `S'` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
noncomputable def typeInductionMap (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (S' : Set (I → ℕ)) {S : Set (I → ℕ)} (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) :
    (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') →ₗ[k]
      MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _
    (typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ μ))
    (typeInductionAux_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hC hD' hS hμS hμ)

theorem typeInductionMap_apply (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (S' : Set (I → ℕ)) {S : Set (I → ℕ)} (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁))
    (z : (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')) :
    typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ z =
      Submodule.Quotient.mk ⟨typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ μ) z,
        typeInductionAux_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hC hD' hS hμS hμ z⟩ := rfl

/-- The image of the map of `g` lies in the image of the map of the shuffle type of `g`, for `C`
separated by the strands of `ν'`. -/
theorem range_shuffleInductionMap_le (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) (S' : Set (I → ℕ))
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) :
    LinearMap.range (shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hg) ≤
      LinearMap.range (typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hg
        (Set.mem_range_self g)) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨z', hz'⟩ := range_shuffleInductionAux_le (k := k) hD hZ hν' hν₁ D C g hCs ⟨z, rfl⟩
  refine ⟨z', ?_⟩
  rw [shuffleInductionMap_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hz')

/-- **The subquotients are spanned by the images of the maps of the shuffle types** (the
surjectivity half of the identification of the subquotients of the Mackey filtration with induced
modules in the proof of B. Webster, arXiv:1209.2463v4, Theorem 2.19). Let `C`, `D` be
rank-ordered, with the strands of `ν'` to the left in `C` and those of `ν₁` to the left in `D`,
and let `S` be a lower set of shuffle types. The quotient of the step `S` of the filtration of
`e D * A * e C` by the step `S'` is the sum of the images of the maps
`x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]`, over the shuffle types `μ` of relabellings with `μ ∈ S` and
`μ ∉ S'`. -/
theorem iSup_range_typeInductionMap (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) (S' : Set (I → ℕ)) {S : Set (I → ℕ)}
    (hS : IsLowerSet S) :
    ⨆ μ : {μ : I → ℕ // μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁) ∧ μ ∈ S ∧ μ ∉ S'},
        LinearMap.range
          (typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS μ.2.2.1 μ.2.1) =
      ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← iSup_range_shuffleInductionMap hP hD hZ hΓ hW hL hν' hν₁ hC hD' hCs hDs S' hS]
  refine iSup_le fun g => (range_shuffleInductionMap_le hP hD hZ hΓ hW hL hν' hν₁ hC hD' hCs S'
    hS g.2.1).trans ?_
  exact le_iSup (fun μ : {μ : I → ℕ // μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁) ∧ μ ∈ S ∧
      μ ∉ S'} => LinearMap.range
        (typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS μ.2.2.1 μ.2.1))
    ⟨shuffleType ν' ν₁ g.1, ⟨g.1, rfl⟩, g.2.1, g.2.2⟩

end GalleryAlgebra

end Categorification.WeightedKLR
