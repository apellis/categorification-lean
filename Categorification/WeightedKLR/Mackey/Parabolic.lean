/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Filtration
import Categorification.WeightedKLR.Mackey.Dominance
import Categorification.WeightedKLR.Induction.Monoidal

/-!
# Juxtaposed diagrams have parabolic relabellings

Module structure of the Mackey filtration of B. Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, §2.4 (proof of Theorem 2.19, which follows Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18): the steps of the filtration of
`e_{ν₁;ν₂} W_ν e_{ν';ν''}` are sub-bimodules for `ι_{ν₁;ν₂}(W_{ν₁} ⊗ W_{ν₂})` acting on the left
and `ι_{ν';ν''}(W_{ν'} ⊗ W_{ν''})` acting on the right.

An element `z` of the gallery algebra is *block-supported* in a submonoid `S` of relabellings
(`IsBlockSupported`) if each of its block operators in the polynomial representation is
supported in `S`. Block support is closed under sums, scalar multiples and products
(`IsBlockSupported.mul`), and the generators `e C`, polynomials and steps are block-supported in
any submonoid containing the reflections of the diagonal hyperplanes they cross. Consequently
the image of a chamber embedding is block-supported in the image of its extension of
relabellings (`ChamberEmbedding.isBlockSupported_galleryHom`), and juxtaposed diagrams
`ι_{ν';ν''}(a ⊗ b)` are block-supported in the relabellings preserving the first `ν'` strands
of each colour (`Juxtapose.isBlockSupported_inductionMap`).

## Main definitions

* `leftBlockStab ν ν₁`: the relabellings sending strands of rank less than `ν₁` to such strands.
* `GalleryAlgebra.IsBlockSupported hΓ S z`: every block operator of `z` is supported in `S`.

## Main results

* `ChamberEmbedding.isBlockSupported_galleryHom`.
* `Juxtapose.isBlockSupported_inductionMap`.
* `GalleryAlgebra.mul_mem_mackeyFilt_of_isBlockSupported`,
  `GalleryAlgebra.mackeyFilt_mul_mem_of_isBlockSupported`: block-supported elements act on the
  steps of the filtration on the left and on the right.
* `GalleryAlgebra.inductionMap_mul_mul_mem_mackeyFilt`: the steps are sub-bimodules for the
  juxtaposed diagrams.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Pointwise GalleryAlgebra TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-! ### The parabolic relabellings -/

variable (ν) in
/-- The relabellings of `ν` that send the strands of rank less than `ν₁` (of each colour) to
strands of rank less than `ν₁`. -/
def leftBlockStab (ν₁ : I →₀ ℕ) : Submonoid (ColPerm ν) where
  carrier := {y | ∀ t : Strand ν, (y.1 t).IsLeft ν₁ ↔ t.IsLeft ν₁}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {_ b} ha hb t => (ha (b.1 t)).trans (hb t)

omit [DecidableEq I] in
theorem mem_leftBlockStab {ν₁ : I →₀ ℕ} {y : ColPerm ν} :
    y ∈ leftBlockStab ν ν₁ ↔ ∀ t : Strand ν, (y.1 t).IsLeft ν₁ ↔ t.IsLeft ν₁ := Iff.rfl

theorem image_leftStrands_of_mem {ν₁ : I →₀ ℕ} {y : ColPerm ν} (hy : y ∈ leftBlockStab ν ν₁) :
    (leftStrands ν₁).image y.1 = leftStrands (ν := ν) ν₁ := by
  ext t
  simp only [leftStrands, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (hy s).2 hs
  · intro ht
    refine ⟨y.1.symm t, (hy _).1 ?_, y.1.apply_symm_apply t⟩
    rwa [y.1.apply_symm_apply]

theorem image_rightStrands_of_mem {ν₁ : I →₀ ℕ} {y : ColPerm ν} (hy : y ∈ leftBlockStab ν ν₁)
    (i : I) : (rightStrands ν₁ i).image y.1 = rightStrands (ν := ν) ν₁ i := by
  ext t
  simp only [rightStrands, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
    refine ⟨?_, fun h => hs' ((hy s).1 h)⟩
    rw [colPerm_apply_fst]
    exact hs
  · rintro ⟨ht, ht'⟩
    refine ⟨y.1.symm t, ⟨?_, fun h => ht' ?_⟩, y.1.apply_symm_apply t⟩
    · have := colPerm_apply_fst y (y.1.symm t)
      rw [y.1.apply_symm_apply] at this
      rw [← this]
      exact ht
    · have := (hy (y.1.symm t)).2 h
      rwa [y.1.apply_symm_apply] at this

/-! ### Supports of steps -/

omit [IsStrictOrderedRing 𝕜] in
/-- The operator of a step from `A` to `B` is supported in the identity and the reflection of
the diagonal hyperplane separating `A` and `B`, if any. -/
theorem isSupported_stepOp (A B : FullChamber Γ ν) {S : Set (ColPerm ν)} (h1 : 1 ∈ S)
    (hS : ∀ d : Diag ν, A.Adjacent B (.inr d) → d.refl ∈ S) :
    IsSupported (stepOp (k := k) Γ A B) S := by
  classical
  by_cases hadj : ∃ h, A.Adjacent B h
  · obtain ⟨h, hh⟩ := hadj
    rcases h with w | d
    · rw [stepOp_inl hh, wallOp_eq_mulLeft, ← LinearMap.comp_id (LinearMap.mulLeft k _)]
      exact (IsSupported.id.mulLeft _).mono (Set.singleton_subset_iff.2 h1)
    · set l := d.left A
      set r := d.right A
      have hlr : l ≠ r := Diag.left_ne_right A d
      have hs : (rename ⇑d.refl.1 : PolyRing ν k →ₐ[k] PolyRing ν k) = rename (swap l r) := by
        rw [Diag.swap_left_right A d]
        rfl
      obtain ⟨c, α, β, hc, hstep⟩ : ∃ c α β : PolyRing ν k, IsRegular c ∧
          ∀ u, c * stepOp Γ A B u = α * u + β * rename ⇑d.refl.1 u := by
        rw [stepOp_inr hh, hs]
        rcases hloop : Γ.loop l.1 with _ | P
        · refine ⟨X l - X r, 1, -1, isRegular_X_sub_X hlr, fun u => ?_⟩
          rw [psiOp_of_none hloop, ddiff_spec hlr]
          ring
        · refine ⟨1, loopFactor P l r, -loopFactor P l r, isRegular_one, fun u => ?_⟩
          rw [psiOp_of_some hloop]
          ring
      have := IsSupported.id.step d.refl hc hstep
      rw [LinearMap.comp_id] at this
      refine this.mono ?_
      rintro x (hx | ⟨y, hy, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hx]
        exact h1
      · rw [Set.mem_singleton_iff.1 hy]
        simpa using hS d hh
  · rw [stepOp_of_not (not_exists.1 hadj)]
    exact IsSupported.zero _

namespace GalleryAlgebra

section BlockSupport

variable (hΓ : Γ.PSymm)

/-- The block operators of a product: `(a z)_{D,C} = ∑_E a_{D,E} ∘ z_{E,C}`. -/
theorem blockOp_mul_eq_sum (D C : FullChamber Γ ν) (a z : GalleryAlgebra k Γ ν) :
    blockOp k hΓ D C (a * z) = ∑ E, blockOp k hΓ D E a ∘ₗ blockOp k hΓ E C z := by
  refine _root_.LinearMap.ext fun f => ?_
  rw [blockOp_apply, map_mul, Module.End.mul_apply,
    ← Finset.univ_sum_single (galleryRep k hΓ z (Pi.single C f)), map_sum, Finset.sum_apply,
    LinearMap.sum_apply]
  rfl

variable (S : Submonoid (ColPerm ν))

/-- **Block support.** Every block operator of `z` in the polynomial representation is
supported in the submonoid `S` of relabellings. -/
def IsBlockSupported (z : GalleryAlgebra k Γ ν) : Prop :=
  ∀ D C : FullChamber Γ ν, IsSupported (blockOp k hΓ D C z) S

namespace IsBlockSupported

variable {hΓ S}

theorem zero : IsBlockSupported hΓ S (0 : GalleryAlgebra k Γ ν) := fun D C => by
  rw [blockOp_zero]
  exact IsSupported.zero _

theorem add {z z' : GalleryAlgebra k Γ ν} (h : IsBlockSupported hΓ S z)
    (h' : IsBlockSupported hΓ S z') : IsBlockSupported hΓ S (z + z') := fun D C => by
  rw [blockOp_add]
  simpa using (h D C).add (h' D C)

theorem smul {z : GalleryAlgebra k Γ ν} (h : IsBlockSupported hΓ S z) (c : k) :
    IsBlockSupported hΓ S (c • z) := fun D C => by
  rw [blockOp_smul]
  exact (h D C).smul c

theorem sum {ι : Type*} (s : Finset ι) {z : ι → GalleryAlgebra k Γ ν}
    (h : ∀ i ∈ s, IsBlockSupported hΓ S (z i)) : IsBlockSupported hΓ S (∑ i ∈ s, z i) :=
  fun D C => by
    rw [blockOp_sum]
    exact IsSupported.sum s fun i hi => h i hi D C

theorem mul {a z : GalleryAlgebra k Γ ν} (ha : IsBlockSupported hΓ S a)
    (hz : IsBlockSupported hΓ S z) : IsBlockSupported hΓ S (a * z) := fun D C => by
  rw [blockOp_mul_eq_sum]
  refine IsSupported.sum _ fun E _ => ((ha D E).comp (hz E C)).mono ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact S.mul_mem hx hy

theorem of_galleryRep_eq_blk {z : GalleryAlgebra k Γ ν} {A B : FullChamber Γ ν}
    {a : PolyRing ν k →ₗ[k] PolyRing ν k} (h : galleryRep k hΓ z = blk k A B a)
    (ha : IsSupported a S) : IsBlockSupported hΓ S z := by
  intro D C
  by_cases hAC : C = A
  · subst hAC
    by_cases hBD : D = B
    · subst hBD
      rw [blockOp_of_galleryRep_eq_blk hΓ h]
      exact ha
    · have : blockOp k hΓ D C z = 0 := _root_.LinearMap.ext fun f => by
        simp [blockOp_apply, h, blk_apply, hBD]
      rw [this]
      exact IsSupported.zero _
  · have : blockOp k hΓ D C z = 0 := _root_.LinearMap.ext fun f => by
      simp [blockOp_apply, h, blk_apply, Pi.single_apply, Ne.symm hAC]
    rw [this]
    exact IsSupported.zero _

theorem e (C : FullChamber Γ ν) : IsBlockSupported hΓ S (e C : GalleryAlgebra k Γ ν) :=
  of_galleryRep_eq_blk (galleryRep_e hΓ C)
    (IsSupported.id.mono (Set.singleton_subset_iff.2 S.one_mem))

theorem poly (f : PolyRing ν k) :
    IsBlockSupported hΓ S (GalleryAlgebra.poly f : GalleryAlgebra k Γ ν) := by
  intro D C
  by_cases hDC : D = C
  · subst hDC
    have : blockOp k hΓ D D (GalleryAlgebra.poly f : GalleryAlgebra k Γ ν) =
        LinearMap.mulLeft k f ∘ₗ LinearMap.id := _root_.LinearMap.ext fun g => by
      simp [blockOp_apply, galleryRep_poly]
    rw [this]
    exact (IsSupported.id.mulLeft f).mono (Set.singleton_subset_iff.2 S.one_mem)
  · have : blockOp k hΓ D C (GalleryAlgebra.poly f : GalleryAlgebra k Γ ν) = 0 :=
      _root_.LinearMap.ext fun g => by
        simp [blockOp_apply, galleryRep_poly, hDC]
    rw [this]
    exact IsSupported.zero _

theorem t {A B : FullChamber Γ ν} (hS : ∀ d : Diag ν, A.Adjacent B (.inr d) → d.refl ∈ S) :
    IsBlockSupported hΓ S (t A B : GalleryAlgebra k Γ ν) :=
  of_galleryRep_eq_blk (galleryRep_t hΓ A B) (isSupported_stepOp A B S.one_mem hS)

theorem r {g : ColPerm ν} (hg : g ∈ S) (C : FullChamber Γ ν) :
    IsBlockSupported hΓ S (r g C : GalleryAlgebra k Γ ν) := by
  refine of_galleryRep_eq_blk (galleryRep_r hΓ g C) ?_
  have := (IsSupported.id (k := k) (ν := ν)).rename g
  rw [LinearMap.comp_id] at this
  refine this.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_singleton_iff.1 hx]
  simpa using hg

theorem mono {S' : Submonoid (ColPerm ν)} {z : GalleryAlgebra k Γ ν}
    (h : IsBlockSupported hΓ S z) (hS : S ≤ S') : IsBlockSupported hΓ S' z :=
  fun D C => (h D C).mono hS

end IsBlockSupported

end BlockSupport

end GalleryAlgebra

/-! ### Images of chamber embeddings -/

namespace ChamberEmbedding

variable {ν₁ : I →₀ ℕ} (J : ChamberEmbedding Γ ν₁ ν) (hΓ : Γ.PSymm)

theorem isBlockSupported_idem (S : Submonoid (ColPerm ν)) :
    IsBlockSupported hΓ S (J.idem (k := k)) :=
  IsBlockSupported.sum _ fun _ _ => IsBlockSupported.e _

/-- If the extension of relabellings of a chamber embedding lands in `S`, every element of the
image of the embedding is block-supported in `S`: diagrams of `ν₁`, drawn inside `ν`, only
relabel strands through relabellings of `ν₁`. -/
theorem isBlockSupported_galleryHom {S : Submonoid (ColPerm ν)} (hS : ∀ g, J.perm g ∈ S)
    (x : GalleryAlgebra k Γ ν₁) : IsBlockSupported hΓ S (J.galleryHom x).1 := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, AlgHom.commutes, IsIdempotentElem.corner_val_algebraMap]
    exact (J.isBlockSupported_idem hΓ S).smul c
  | grade1 g =>
    cases g with
    | idem C =>
      show IsBlockSupported hΓ S (J.galleryHom (e C)).1
      rw [galleryHom_e]
      exact IsBlockSupported.e _
    | poly f =>
      show IsBlockSupported hΓ S (J.galleryHom (poly f)).1
      rw [galleryHom_poly]
      exact (IsBlockSupported.poly _).mul (J.isBlockSupported_idem hΓ S)
    | step C D =>
      show IsBlockSupported hΓ S (J.galleryHom (t C D)).1
      rw [galleryHom_t]
      refine IsBlockSupported.t fun d hd => ?_
      by_cases hCD : ∃ h, C.Adjacent D h
      · obtain ⟨h, hh⟩ := hCD
        have hJ := J.adjacent_chamber hh
        have heq : J.hyp h = .inr d := by
          by_contra hne
          exact hd.1 (hJ.2 _ (Ne.symm hne))
        rcases h with w | d₀
        · exact absurd heq (by simp [StrandEmbedding.hyp_inl])
        · have hd₀ : J.diag d₀ = d := by
            simpa [StrandEmbedding.hyp_inr] using heq
          rw [← hd₀, ← J.perm_refl]
          exact hS _
      · exact absurd hd (J.not_adjacent_chamber (not_exists.1 hCD) _)
    | relabel g C =>
      show IsBlockSupported hΓ S (J.galleryHom (r g C)).1
      rw [galleryHom_r]
      exact IsBlockSupported.r (hS g) _
  | mul a b ha hb =>
    rw [map_mul, map_mul]
    exact ha.mul hb
  | add a b ha hb =>
    rw [map_add, map_add]
    exact ha.add hb

end ChamberEmbedding

/-! ### Juxtaposed diagrams -/

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ} (hΓ : Γ.PSymm)

omit [DecidableEq I] in
theorem isLeft_inlStrand (s : Strand ν') : (inlStrand ν' ν'' s).IsLeft ν' :=
  show s.2.val < ν' s.1.1 from s.2.2

omit [DecidableEq I] in
theorem not_isLeft_inrStrand (s : Strand ν'') : ¬(inrStrand ν' ν'' s).IsLeft ν' :=
  show ¬(ν' s.1.1 + s.2.val < ν' s.1.1) by omega

omit [DecidableEq I] in
/-- Relabelling the two sides independently preserves the strands of the first side. -/
theorem colPermProd_mem_leftBlockStab (g : ColPerm ν' × ColPerm ν'') :
    colPermProd ν' ν'' g ∈ leftBlockStab (ν' + ν'') ν' := by
  intro t
  obtain ⟨x, rfl⟩ := (strandEquiv ν' ν'').surjective t
  rcases x with a | b
  · show ((colPermProd ν' ν'' g).1 (inlStrand ν' ν'' a)).IsLeft ν' ↔ _
    rw [colPermProd_inl]
    exact iff_of_true (isLeft_inlStrand _) (isLeft_inlStrand _)
  · show ((colPermProd ν' ν'' g).1 (inrStrand ν' ν'' b)).IsLeft ν' ↔ _
    rw [colPermProd_inr]
    exact iff_of_false (not_isLeft_inrStrand _) (not_isLeft_inrStrand _)

theorem isBlockSupported_leftHom (x : GalleryAlgebra k Γ ν') :
    IsBlockSupported hΓ (leftBlockStab (ν' + ν'') ν') (leftHom k Γ ν' ν'' x).1 :=
  IsBlockSupported.sum _ fun C'' _ =>
    (leftChamberEmb C'').isBlockSupported_galleryHom hΓ
      (fun g => colPermProd_mem_leftBlockStab (g, 1)) x

theorem isBlockSupported_rightHom (y : GalleryAlgebra k Γ ν'') :
    IsBlockSupported hΓ (leftBlockStab (ν' + ν'') ν') (rightHom k Γ ν' ν'' y).1 :=
  IsBlockSupported.sum _ fun C' _ =>
    (rightChamberEmb C').isBlockSupported_galleryHom hΓ
      (fun g => colPermProd_mem_leftBlockStab (1, g)) y

theorem isBlockSupported_galleryTensorHom
    (z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'') :
    IsBlockSupported hΓ (leftBlockStab (ν' + ν'') ν') (galleryTensorHom k Γ ν' ν'' z).1 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [galleryTensorHom_tmul]
    exact (isBlockSupported_leftHom hΓ x).mul (isBlockSupported_rightHom hΓ y)
  | add a b ha hb =>
    rw [map_add]
    exact ha.add hb

/-- **Juxtaposed diagrams have parabolic relabellings.** Every element of the image of
`ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}` acts, block by block, in the polynomial
representation through relabellings that keep the first `ν'` strands of each colour among
themselves. -/
theorem isBlockSupported_inductionMap
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    IsBlockSupported hΓ (leftBlockStab (ν' + ν'') ν') (inductionMap k Γ ν' ν'' w).1 :=
  isBlockSupported_galleryTensorHom hΓ _

/-- The same, transported along an equality `ν' + ν'' = ν`. -/
theorem isBlockSupported_castGallery_inductionMap (h : ν' + ν'' = ν)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    IsBlockSupported hΓ (leftBlockStab ν ν')
      (castGallery k Γ h (inductionMap k Γ ν' ν'' w).1) := by
  subst h
  exact isBlockSupported_inductionMap hΓ w

end Juxtapose

/-! ### The steps of the filtration are sub-bimodules -/

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **The steps are left submodules.** Multiplying a step of the filtration of `e D A e C` on
the left by an element relabelling the first `ν₁` strands of each colour among themselves, and
cutting down to `e D'`, stays in the corresponding step of the filtration of `e D' A e C`. -/
theorem mul_mem_mackeyFilt_of_isBlockSupported (ν' ν₁ : I →₀ ℕ) {D' D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered) (hD'' : D'.IsRankOrdered)
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {a z : GalleryAlgebra k Γ ν}
    (ha : IsBlockSupported hΓ (leftBlockStab ν ν₁) a)
    (hz : z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) :
    e D' * a * z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D' C S := by
  have hzc := mackeyFilt_le_cornerSpace hP hD hZ hΓ hW hL ν' ν₁ D C S hz
  have hze : e D * z = z := by
    rw [mem_cornerSpace_iff] at hzc
    rw [← hzc, ← mul_assoc, ← mul_assoc, e_mul_e_self]
  have key : e D' * a * z = e D' * a * e D * z := by rw [mul_assoc _ (e D), hze]
  have h1 : ∀ x : GalleryAlgebra k Γ ν, e D' * (e D' * x) = e D' * x := fun x => by
    rw [← mul_assoc, e_mul_e_self]
  rw [key]
  refine mul_mem_mackeyFilt hP hD hZ hΓ hW hL ν' ν₁ hC hD' hD'' hS ?_ ?_ hz
  · rw [mem_cornerSpace_iff]
    simp only [mul_assoc, e_mul_e_self, h1]
  · refine (((IsBlockSupported.e D').mul ha).mul (IsBlockSupported.e D) D' D).mono ?_
    intro y hy
    exact image_leftStrands_of_mem hy

/-- **The steps are right submodules.** Multiplying a step of the filtration of `e D A e C` on
the right by an element relabelling the first `ν'` strands of each colour among themselves, and
cutting down to `e C'`, stays in the corresponding step of the filtration of `e D A e C'`. -/
theorem mackeyFilt_mul_mem_of_isBlockSupported (ν' ν₁ : I →₀ ℕ) {D C C' : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hC' : C'.IsRankOrdered) (hD' : D.IsRankOrdered)
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {z b : GalleryAlgebra k Γ ν}
    (hb : IsBlockSupported hΓ (leftBlockStab ν ν') b)
    (hz : z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) :
    z * b * e C' ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C' S := by
  have hzc := mackeyFilt_le_cornerSpace hP hD hZ hΓ hW hL ν' ν₁ D C S hz
  have hzr : z * e C = z := by
    rw [mem_cornerSpace_iff] at hzc
    rw [← hzc, mul_assoc, e_mul_e_self]
  have key : z * b * e C' = z * (e C * b * e C') := by
    rw [← mul_assoc, ← mul_assoc, hzr]
  have h1 : ∀ x : GalleryAlgebra k Γ ν, e C * (e C * x) = e C * x := fun x => by
    rw [← mul_assoc, e_mul_e_self]
  rw [key]
  refine mackeyFilt_mul_mem hP hD hZ hΓ hW hL ν' ν₁ hC hC' hD' hS ?_ ?_ hz
  · rw [mem_cornerSpace_iff]
    simp only [mul_assoc, e_mul_e_self, h1]
  · refine (((IsBlockSupported.e C).mul hb).mul (IsBlockSupported.e C') C C').mono ?_
    intro y hy i
    exact image_rightStrands_of_mem hy i

/-- **The steps of the Mackey filtration are sub-bimodules** (the module structure used in the
proof of B. Webster, arXiv:1209.2463v4, Theorem 2.19, after Khovanov–Lauda, arXiv:0803.4121v2,
Proposition 2.18). For `ν₁ + ν₂ = ν = ν' + ν''`, if `z` lies in the step of shuffle types `S`
of `e D W_ν e C`, then so does `e D' ι_{ν₁;ν₂}(u) z ι_{ν';ν''}(w) e C'` in `e D' W_ν e C'`. -/
theorem inductionMap_mul_mul_mem_mackeyFilt {ν₁ ν₂ ν' ν'' : I →₀ ℕ} (h : ν₁ + ν₂ = ν)
    (h' : ν' + ν'' = ν) {D' D C C' : FullChamber Γ ν} (hC : C.IsRankOrdered)
    (hC' : C'.IsRankOrdered) (hD₀ : D.IsRankOrdered) (hD₁ : D'.IsRankOrdered)
    {S : Set (I → ℕ)} (hS : IsLowerSet S)
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    {z : GalleryAlgebra k Γ ν} (hz : z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) :
    e D' * castGallery k Γ h (Juxtapose.inductionMap k Γ ν₁ ν₂ u).1 * z *
        castGallery k Γ h' (Juxtapose.inductionMap k Γ ν' ν'' w).1 * e C' ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D' C' S :=
  mackeyFilt_mul_mem_of_isBlockSupported hP hD hZ hΓ hW hL ν' ν₁ hC hC' hD₁ hS
    (Juxtapose.isBlockSupported_castGallery_inductionMap hΓ h' w)
    (mul_mem_mackeyFilt_of_isBlockSupported hP hD hZ hΓ hW hL ν' ν₁ hC hD₀ hD₁ hS
      (Juxtapose.isBlockSupported_castGallery_inductionMap hΓ h u) hz)

end GalleryAlgebra

end Categorification.WeightedKLR
