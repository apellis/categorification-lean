/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ShuffleElement
import Categorification.WeightedKLR.RedStrands.ViolatingComparison

/-!
# The factorization `b(g, m) ≡ ι(x) ψ_g ι(y)` through Webster's algebras

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). The factorization
`b(g, m) ≡ ι(x) * ψ_g * ι(y)` of `GalleryAlgebra.exists_cornerBasis_sub_shuffleElt_mem` has `x`,
`y` in tensor products of gallery algebras, because the ends `g • shuffleTop Y C` and
`shuffleBot X Y C` of the shuffle element are separated but not rank-ordered. Here the pieces are
moved into Webster's algebras `W_{ν₁} ⊗ W_{ν₂}` and `W_{ν'} ⊗ W_{ν''}` (corners at the rank-ordered
chambers), with `ι` Webster's map `Juxtapose.inductionMap`.

The ends are sorted inside each block: a separated chamber `E` is a juxtaposition `E' ∘ E''`,
and relabelling `E'` and `E''` into rank order (`FullChamber.exists_smul_isRankOrdered`) gives a
block-preserving relabelling `u = blockSort` with `u • E` rank-ordered and separated. Relabellings
inside the blocks are juxtapositions (`Juxtapose.galleryTensorHom_r_tmul_r`), so
`ψ_g = r u⁻¹ (u • E) * ψ^W_g * r v F` with `ψ^W_g = r u E * ψ_g * r v⁻¹ (v • F)`
(`GalleryAlgebra.rankShuffleElt`), and the outer factors are absorbed into `x` and `y`. On both
sides `ψ^W_g` is fixed by Webster's idempotents `e_{ν₁;ν₂}`, `e_{ν';ν''}` (`splitIdem`), and so are
`b(g, m)` and the basis elements of the error term; compressing by these idempotents turns `ι(x)`
of the gallery algebras into `ι` of Webster's algebras
(`Juxtapose.exists_splitIdem_mul_mul_splitIdem`).

## Main definitions

* `Juxtapose.blockSort`: a relabelling inside the two blocks sorting a chamber into rank order.
* `GalleryAlgebra.rankShuffleElt`: the shuffle element `ψ^W_g` between rank-ordered chambers.

## Main results

* `GalleryAlgebra.shuffleElt_eq_r_mul_rankShuffleElt_mul_r`: `ψ_g = r u⁻¹ (u • E) ψ^W_g r v F`.
* `GalleryAlgebra.splitIdem_mul_rankShuffleElt`, `GalleryAlgebra.rankShuffleElt_mul_splitIdem`:
  `ψ^W_g` lies in `e_{ν₁;ν₂} * A * e_{ν';ν''}`.
* `GalleryAlgebra.exists_cornerBasis_sub_rankShuffleElt_mem`: **factorization**
  `b(g, m) ≡ ι(x) * ψ^W_g * ι(y)` with `x ∈ W_{ν₁} ⊗ W_{ν₂}`, `y ∈ W_{ν'} ⊗ W_{ν''}` and `ι` Webster's
  map, modulo basis elements of shuffle type in `S` and shorter chosen gallery.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise GalleryAlgebra

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace FullChamber

omit [DecidableEq I] in
/-- Every full chamber can be relabelled, colour by colour, into a rank-ordered one. -/
theorem exists_smul_isRankOrdered (A : FullChamber Γ ν) :
    ∃ u : ColPerm ν, (u • A).IsRankOrdered := by
  obtain ⟨p, hp, rfl⟩ := A.exists_eq_ofPoint
  obtain ⟨u, hu⟩ := exists_act_rankOrdered hp
  refine ⟨u, fun d => ?_⟩
  rw [smul_ofPoint]
  exact decide_eq_true (hu d)

end FullChamber

theorem castGallery_rfl (x : GalleryAlgebra k Γ ν) : castGallery k Γ (rfl : ν = ν) x = x := rfl

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

/-- A juxtaposition of relabellings is the relabelling by the product permutation. -/
theorem galleryTensorHom_r_tmul_r (g' : ColPerm ν') (g'' : ColPerm ν'') (A' : FullChamber Γ ν')
    (A'' : FullChamber Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (r g' A' ⊗ₜ r g'' A'')).1 =
      r (colPermProd ν' ν'' (g', g'')) (chamber A' A'') := by
  rw [galleryTensorHom_tmul]
  show (leftHom k Γ ν' ν'' (r g' A')).1 * (rightHom k Γ ν' ν'' (r g'' A'')).1 = _
  rw [leftHom_r, rightHom_r, sum_mul_sum_eq _ _ (fun C'' => e (chamber A' C''))
    (fun C' => e (chamber C' (g'' • A''))) (g'' • A'') A'
    (fun _ => r_mul_e _ _) (fun C' => by rw [← smul_chamber_right, e_smul_mul_r])
    (fun i j h => by rw [e_mul_e_chamber, ite_eq_right fun hh => h ⟨hh.2, hh.1.symm⟩]),
    ← smul_chamber_right, r_mul_r]
  congr 1
  simp only [leftPerm, rightPerm, MonoidHom.comp_apply, ← map_mul, MonoidHom.inl_apply,
    MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one, one_mul]

variable {ν₁ ν₂ : I →₀ ℕ}

/-- A relabelling inside the two blocks of `ν = ν₁ + ν₂` sorting the restrictions of `E` to the
two blocks into rank order. -/
noncomputable def blockSort : ν₁ + ν₂ = ν → FullChamber Γ ν → ColPerm ν := by
  rintro rfl E
  exact colPermProd ν₁ ν₂
    ((exists_smul_isRankOrdered ((leftEmb ν₁ ν₂).restrict E)).choose,
      (exists_smul_isRankOrdered ((rightEmb ν₁ ν₂).restrict E)).choose)

/-- **Sorting a separated chamber inside the blocks.** For `E` separated by the strands of `ν₁`,
`blockSort hν E • E` is rank-ordered and separated, and the relabellings between `E` and it are
juxtapositions. -/
theorem blockSort_spec (hν : ν₁ + ν₂ = ν) {E : FullChamber Γ ν}
    (hE : IsSeparated (fun t => decide (t.IsLeft ν₁)) E) :
    (blockSort hν E • E).IsRankOrdered ∧
      IsSeparated (fun t => decide (t.IsLeft ν₁)) (blockSort hν E • E) ∧
      (∃ z : GalleryAlgebra k Γ ν₁ ⊗[k] GalleryAlgebra k Γ ν₂,
        r (blockSort hν E)⁻¹ (blockSort hν E • E) =
          castGallery k Γ hν (galleryTensorHom k Γ ν₁ ν₂ z).1) ∧
      ∃ z : GalleryAlgebra k Γ ν₁ ⊗[k] GalleryAlgebra k Γ ν₂,
        r (blockSort hν E) E = castGallery k Γ hν (galleryTensorHom k Γ ν₁ ν₂ z).1 := by
  subst hν
  set E' := (leftEmb ν₁ ν₂).restrict E
  set E'' := (rightEmb ν₁ ν₂).restrict E
  have hu : blockSort rfl E = colPermProd ν₁ ν₂
      ((exists_smul_isRankOrdered E').choose, (exists_smul_isRankOrdered E'').choose) := rfl
  have h₁ := (exists_smul_isRankOrdered E').choose_spec
  have h₂ := (exists_smul_isRankOrdered E'').choose_spec
  set u₁ := (exists_smul_isRankOrdered E').choose
  set u₂ := (exists_smul_isRankOrdered E'').choose
  have hEq : E = chamber E' E'' := eq_chamber_of_isSeparated hE
  have huE : blockSort rfl E • E = chamber (u₁ • E') (u₂ • E'') := by
    rw [hu]
    conv_lhs => rw [hEq]
    exact colPermProd_smul_chamber _ _ _
  refine ⟨?_, ?_, ⟨r u₁⁻¹ (u₁ • E') ⊗ₜ r u₂⁻¹ (u₂ • E''), ?_⟩,
    ⟨r u₁ E' ⊗ₜ r u₂ E'', ?_⟩⟩
  · rw [huE]
    exact (isRankOrdered_chamber_iff _ _).2 ⟨h₁, h₂⟩
  · rw [huE]
    exact isSeparated_chamber _ _
  · rw [castGallery_rfl, galleryTensorHom_r_tmul_r, huE, hu, ← map_inv]
    rfl
  · rw [castGallery_rfl, galleryTensorHom_r_tmul_r, hu]
    conv_lhs => rw [hEq]

/-- `e_{ν₁;ν₂} * e D = e D` for `D` rank-ordered and separated by the strands of `ν₁`. -/
theorem castGallery_splitIdem_mul_e (hν : ν₁ + ν₂ = ν) {D : FullChamber Γ ν}
    (hD : D.IsRankOrdered) (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) :
    castGallery k Γ hν (splitIdem k Γ ν₁ ν₂) * e D = e D := by
  subst hν
  rw [castGallery_rfl]
  set D' := (leftEmb ν₁ ν₂).restrict D
  set D'' := (rightEmb ν₁ ν₂).restrict D
  have hEq : D = chamber D' D'' := eq_chamber_of_isSeparated hDs
  rw [hEq] at hD ⊢
  obtain ⟨h', h''⟩ := (isRankOrdered_chamber_iff _ _).1 hD
  have hz : ∀ C' ∈ Finset.univ.filter FullChamber.IsRankOrdered, C' ≠ D' →
      ∑ C'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
        (e (chamber C' C'') * e (chamber D' D'') : GalleryAlgebra k Γ (ν₁ + ν₂)) = 0 :=
    fun C' _ hne => Finset.sum_eq_zero fun C'' _ => by
      rw [e_mul_e_chamber, ite_eq_right fun h => hne h.1]
  rw [splitIdem, Finset.sum_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_eq_single_of_mem D' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩) hz,
    Finset.sum_eq_single_of_mem D'' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h''⟩)
      fun C'' _ hne => by rw [e_mul_e_chamber, ite_eq_right fun h => hne h.2],
    e_mul_e_chamber, ite_eq_left ⟨rfl, rfl⟩]

/-- `e D * e_{ν₁;ν₂} = e D` for `D` rank-ordered and separated by the strands of `ν₁`. -/
theorem e_mul_castGallery_splitIdem (hν : ν₁ + ν₂ = ν) {D : FullChamber Γ ν}
    (hD : D.IsRankOrdered) (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) :
    e D * castGallery k Γ hν (splitIdem k Γ ν₁ ν₂) = e D := by
  subst hν
  rw [castGallery_rfl]
  set D' := (leftEmb ν₁ ν₂).restrict D
  set D'' := (rightEmb ν₁ ν₂).restrict D
  have hEq : D = chamber D' D'' := eq_chamber_of_isSeparated hDs
  rw [hEq] at hD ⊢
  obtain ⟨h', h''⟩ := (isRankOrdered_chamber_iff _ _).1 hD
  have hz : ∀ C' ∈ Finset.univ.filter FullChamber.IsRankOrdered, C' ≠ D' →
      ∑ C'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
        (e (chamber D' D'') * e (chamber C' C'') : GalleryAlgebra k Γ (ν₁ + ν₂)) = 0 :=
    fun C' _ hne => Finset.sum_eq_zero fun C'' _ => by
      rw [e_mul_e_chamber, ite_eq_right fun h => hne h.1.symm]
  rw [splitIdem, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_eq_single_of_mem D' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩) hz,
    Finset.sum_eq_single_of_mem D'' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h''⟩)
      fun C'' _ hne => by rw [e_mul_e_chamber, ite_eq_right fun h => hne h.2.symm],
    e_mul_e_chamber, ite_eq_left ⟨rfl, rfl⟩]

/-- **Compression into Webster's algebras.** `e_{ν';ν''} * ι(z) * e_{ν';ν''}`, for `z` in the
tensor product of the gallery algebras, is `ι(w)` for some `w ∈ W_{ν'} ⊗ W_{ν''}`, with `ι`
Webster's map `inductionMap`. -/
theorem exists_splitIdem_mul_mul_splitIdem
    (z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'') :
    ∃ w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'',
      splitIdem k Γ ν' ν'' * (galleryTensorHom k Γ ν' ν'' z).1 * splitIdem k Γ ν' ν'' =
        (inductionMap k Γ ν' ν'' w).1 := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    refine ⟨(⟨rankIdem k Γ ν' * a * rankIdem k Γ ν', a, rfl⟩ : WeightedKLRAlgebra k Γ ν') ⊗ₜ
      (⟨rankIdem k Γ ν'' * b * rankIdem k Γ ν'', b, rfl⟩ : WeightedKLRAlgebra k Γ ν''), ?_⟩
    change _ = (galleryTensorHom k Γ ν' ν''
      ((rankIdem k Γ ν' * a * rankIdem k Γ ν') ⊗ₜ (rankIdem k Γ ν'' * b * rankIdem k Γ ν''))).1
    rw [← Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.tmul_mul_tmul,
      galleryTensorHom_mul_val, galleryTensorHom_mul_val, galleryTensorHom_rankIdem]
  | add a b ha hb =>
    obtain ⟨w₁, h₁⟩ := ha
    obtain ⟨w₂, h₂⟩ := hb
    refine ⟨w₁ + w₂, ?_⟩
    rw [map_add, map_add]
    change _ * ((galleryTensorHom k Γ ν' ν'' a).1 + (galleryTensorHom k Γ ν' ν'' b).1) * _ =
      (inductionMap k Γ ν' ν'' w₁).1 + (inductionMap k Γ ν' ν'' w₂).1
    rw [mul_add, add_mul, h₁, h₂]

/-- `exists_splitIdem_mul_mul_splitIdem` along `ν' + ν'' = ν`. -/
theorem exists_castGallery_splitIdem_mul_mul (hν : ν' + ν'' = ν)
    (z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'') :
    ∃ w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'',
      castGallery k Γ hν (splitIdem k Γ ν' ν'') *
          castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z).1 *
          castGallery k Γ hν (splitIdem k Γ ν' ν'') =
        castGallery k Γ hν (inductionMap k Γ ν' ν'' w).1 := by
  obtain ⟨w, hw⟩ := exists_splitIdem_mul_mul_splitIdem z
  exact ⟨w, by rw [← map_mul, ← map_mul, hw]⟩

end Juxtapose

namespace GalleryAlgebra

open Juxtapose

attribute [local instance] ColPerm.fintype

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

omit [DecidableEq I] in
theorem isSeparated_smul_shuffleTop (g : ColPerm ν) (C : FullChamber Γ ν) :
    IsSeparated (fun t => decide (t.IsLeft ν₁))
      (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) := by
  have h0 : IsSeparated (fun t => decide ((g.1 t).IsLeft ν₁))
      (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) := isSeparated_sep _ C C
  have := h0.smul g
  simpa using this

omit [DecidableEq I] in
theorem isSeparated_shuffleBot (Y : Strand ν → Bool) (C : FullChamber Γ ν) :
    IsSeparated (fun t => decide (t.IsLeft ν')) (shuffleBot (fun t => decide (t.IsLeft ν')) Y C) :=
  isSeparated_sep _ _ _

variable (k) in
/-- **The shuffle element between rank-ordered chambers** `ψ^W_g = r u E * ψ_g * r v⁻¹ (v • F)`,
where `ψ_g = shuffleElt k hD hZ ν' ν₁ g C` goes from `F = shuffleBot X Y C` to
`E = g • shuffleTop Y C`, and `u = blockSort hν₁ E`, `v = blockSort hν' F` sort `E` and `F` into
rank order inside the blocks of `ν = ν₁ + ν₂` and `ν = ν' + ν''`. -/
noncomputable def rankShuffleElt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (C : FullChamber Γ ν) : GalleryAlgebra k Γ ν :=
  r (blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C))
      (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
    shuffleElt k hD hZ ν' ν₁ g C *
    r (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
        (fun t => decide ((g.1 t).IsLeft ν₁)) C))⁻¹
      (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
          (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
        shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C)

theorem e_mul_shuffleElt (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν)
    (C : FullChamber Γ ν) :
    e (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
        shuffleElt k hD hZ ν' ν₁ g C = shuffleElt k hD hZ ν' ν₁ g C := by
  rw [shuffleElt, ← mul_assoc, e_smul_mul_r]

theorem shuffleElt_mul_e (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν)
    (C : FullChamber Γ ν) :
    shuffleElt k hD hZ ν' ν₁ g C *
        e (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C) =
      shuffleElt k hD hZ ν' ν₁ g C := by
  rw [shuffleElt, mul_assoc, galList_mul_e]

/-- `ψ_g = r u⁻¹ (u • E) * ψ^W_g * r v F`. -/
theorem shuffleElt_eq_r_mul_rankShuffleElt_mul_r (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (C : FullChamber Γ ν) :
    shuffleElt k hD hZ ν' ν₁ g C =
      r (blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C))⁻¹
          (blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
            g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
        rankShuffleElt k hν' hν₁ hD hZ g C *
        r (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
            (fun t => decide ((g.1 t).IsLeft ν₁)) C))
          (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C) := by
  rw [rankShuffleElt, ← mul_assoc, ← mul_assoc, r_mul_r, inv_mul_cancel, r_one, e_mul_shuffleElt,
    mul_assoc, r_mul_r, inv_mul_cancel, r_one, shuffleElt_mul_e]

/-- `e_{ν₁;ν₂} * ψ^W_g = ψ^W_g`. -/
theorem splitIdem_mul_rankShuffleElt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (C : FullChamber Γ ν) :
    castGallery k Γ hν₁ (splitIdem k Γ ν₁ ν₂) * rankShuffleElt k hν' hν₁ hD hZ g C =
      rankShuffleElt k hν' hν₁ hD hZ g C := by
  obtain ⟨h₁, h₂, -⟩ := blockSort_spec (k := k) hν₁ (isSeparated_smul_shuffleTop g C)
  rw [rankShuffleElt, ← e_smul_mul_r, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    castGallery_splitIdem_mul_e hν₁ h₁ h₂]

/-- `ψ^W_g * e_{ν';ν''} = ψ^W_g`. -/
theorem rankShuffleElt_mul_splitIdem (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (C : FullChamber Γ ν) :
    rankShuffleElt k hν' hν₁ hD hZ g C * castGallery k Γ hν' (splitIdem k Γ ν' ν'') =
      rankShuffleElt k hν' hν₁ hD hZ g C := by
  obtain ⟨h₁, h₂, -⟩ := blockSort_spec (k := k) hν' (isSeparated_shuffleBot
    (fun t => decide ((g.1 t).IsLeft ν₁)) C)
  have key : ∀ {A : FullChamber Γ ν} (u : ColPerm ν), A.IsRankOrdered →
      IsSeparated (fun t => decide (t.IsLeft ν')) A →
      r u A * castGallery k Γ hν' (splitIdem k Γ ν' ν'') = r u A := fun u hA hAs => by
    rw [← r_mul_e, mul_assoc, e_mul_castGallery_splitIdem hν' hA hAs]
  rw [rankShuffleElt, mul_assoc, key _ h₁ h₂]

/-- Elements of `e D * A * e C` are fixed by `e_{ν₁;ν₂}` on the left and `e_{ν';ν''}` on the
right, for `D`, `C` rank-ordered and separated by the strands of `ν₁`, `ν'`. -/
theorem splitIdem_mul_mul_splitIdem_of_mem (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {x : GalleryAlgebra k Γ ν}
    (hx : x ∈ cornerSpace k D C) :
    castGallery k Γ hν₁ (splitIdem k Γ ν₁ ν₂) * x * castGallery k Γ hν' (splitIdem k Γ ν' ν'') =
      x := by
  rw [← mem_cornerSpace_iff.1 hx, ← mul_assoc, ← mul_assoc, castGallery_splitIdem_mul_e hν₁ hD' hDs,
    mul_assoc, e_mul_castGallery_splitIdem hν' hC hCs]

theorem sandwich_sub_eq {R : Type*} [Ring R] (s₁ s₂ A B ψ b : R) (h₁ : s₁ * ψ = ψ)
    (h₂ : ψ * s₂ = ψ) (hb : s₁ * b * s₂ = b) :
    s₁ * (A * ψ * B - b) * s₂ = s₁ * A * s₁ * ψ * (s₂ * B * s₂) - b := by
  rw [mul_sub, sub_mul, hb]
  congr 1
  calc s₁ * (A * ψ * B) * s₂ = s₁ * A * (s₁ * (ψ * s₂)) * B * s₂ := by
        rw [h₂, h₁]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **Factorization of a basis element through Webster's algebras.** Let `C`, `D` be
rank-ordered, with the strands of `ν'` to the left in `C` and those of `ν₁` to the left in `D`,
`ν = ν' + ν'' = ν₁ + ν₂`, and let `S` be a lower set of shuffle types containing that of `g`.
Then `b(g, m) ≡ ι(x) * ψ^W_g * ι(y)` modulo basis elements of shuffle type in `S` and shorter
chosen gallery, for some `x ∈ W_{ν₁} ⊗ W_{ν₂}` and `y ∈ W_{ν'} ⊗ W_{ν''}`, where `ι` is Webster's
map `inductionMap` and `ψ^W_g = rankShuffleElt k hν' hν₁ hD hZ g C`. -/
theorem exists_cornerBasis_sub_rankShuffleElt_mem (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) (m : Strand ν →₀ ℕ) :
    ∃ (x : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (y : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''),
      castGallery k Γ hν₁ (inductionMap k Γ ν₁ ν₂ x).1 * rankShuffleElt k hν' hν₁ hD hZ g C *
          castGallery k Γ hν' (inductionMap k Γ ν' ν'' y).1 -
        (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  obtain ⟨x, y, h⟩ := exists_cornerBasis_sub_shuffleElt_mem hP hD hZ hΓ hW hL hν' hν₁ hC hD' hCs
    hDs hS hg m
  obtain ⟨-, -, ⟨z₁, hz₁⟩, -⟩ := blockSort_spec (k := k) hν₁ (isSeparated_smul_shuffleTop g C)
  obtain ⟨-, -, -, ⟨z₂, hz₂⟩⟩ := blockSort_spec (k := k) hν' (isSeparated_shuffleBot
    (fun t => decide ((g.1 t).IsLeft ν₁)) C)
  rw [shuffleElt_eq_r_mul_rankShuffleElt_mul_r hν' hν₁, hz₁, hz₂] at h
  set s₁ := castGallery k Γ hν₁ (splitIdem k Γ ν₁ ν₂)
  set s₂ := castGallery k Γ hν' (splitIdem k Γ ν' ν'')
  set L := Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν))
  have hfix : ∀ z : cornerSpace k D C, s₁ * (z : GalleryAlgebra k Γ ν) * s₂ = z := fun z =>
    splitIdem_mul_mul_splitIdem_of_mem hν' hν₁ hC hD' hCs hDs z.2
  have hLs : ∀ z ∈ L, s₁ * z * s₂ ∈ L := fun z hz => by
    have := Submodule.mem_map_of_mem (f := sandwich k s₁ s₂) hz
    rw [Submodule.map_span, ← Set.range_comp, sandwich_apply] at this
    have hset : Set.range (sandwich k s₁ s₂ ∘ fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) =
        Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
          shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
            (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν) := by
      congr 1
      funext i
      rw [Function.comp_apply, sandwich_apply, hfix]
    rwa [hset] at this
  have hm : ∀ {μ μ' μ'' : I →₀ ℕ} (hμ : μ' + μ'' = μ)
      (a b : GalleryAlgebra k Γ μ' ⊗[k] GalleryAlgebra k Γ μ''),
      castGallery k Γ hμ (galleryTensorHom k Γ μ' μ'' a).1 *
          castGallery k Γ hμ (galleryTensorHom k Γ μ' μ'' b).1 =
        castGallery k Γ hμ (galleryTensorHom k Γ μ' μ'' (a * b)).1 := fun hμ a b => by
    rw [galleryTensorHom_mul_val, map_mul]
  have h0 : castGallery k Γ hν₁ (galleryTensorHom k Γ ν₁ ν₂ (x * z₁)).1 *
        rankShuffleElt k hν' hν₁ hD hZ g C *
        castGallery k Γ hν' (galleryTensorHom k Γ ν' ν'' (z₂ * y)).1 -
      (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈ L := by
    rw [← hm, ← hm]
    convert h using 2
    simp only [mul_assoc]
  have h' := hLs _ h0
  rw [sandwich_sub_eq _ _ _ _ _ _ (splitIdem_mul_rankShuffleElt hν' hν₁ hD hZ g C)
      (rankShuffleElt_mul_splitIdem hν' hν₁ hD hZ g C) (hfix _)] at h'
  obtain ⟨x', hx'⟩ := exists_castGallery_splitIdem_mul_mul hν₁ (x * z₁)
  obtain ⟨y', hy'⟩ := exists_castGallery_splitIdem_mul_mul hν' (z₂ * y)
  rw [hx', hy'] at h'
  exact ⟨x', y', h'⟩

end GalleryAlgebra

end Categorification.WeightedKLR
