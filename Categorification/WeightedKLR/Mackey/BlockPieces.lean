/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.SeparatedJuxtapose
import Categorification.WeightedKLR.Mackey.ShuffleFactor
import Categorification.WeightedKLR.Induction.Monoidal

/-!
# Block-preserving galleries are juxtapositions

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). In the factorization of a basis element through the shuffle
(`GalleryAlgebra.shuffle_sub_cornerBasis_mem`), the first and last pieces of the minimal gallery
cross only hyperplanes joining two strands of the same block. Such a gallery, started at a
juxtaposed chamber `C' ∘ C''`, is the juxtaposition of a gallery of `ν'` and a gallery of `ν''`
(`Juxtapose.exists_galList_eq_galleryTensorHom`): it lies in the image of the juxtaposition map
`ι = galleryTensorHom` on the tensor product of the two smaller gallery algebras. So do the dots
on a juxtaposed chamber (`Juxtapose.exists_poly_mul_e_eq_galleryTensorHom`).

## Main results

* `Juxtapose.galleryTensorHom_t_tmul_e`, `Juxtapose.galleryTensorHom_e_tmul_t`: steps of one
  side.
* `Juxtapose.eq_chamber_of_adjacent_left`, `Juxtapose.eq_chamber_of_adjacent_right`: crossing a
  hyperplane of one block from a juxtaposed chamber.
* `Juxtapose.exists_galList_eq_galleryTensorHom`: a block-preserving gallery is a juxtaposition.
* `Juxtapose.exists_poly_mul_e_eq_galleryTensorHom`: dots on a juxtaposed chamber.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv GalleryAlgebra IsIdempotentElem FullChamber

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

theorem galleryTensorHom_mul_val (x y : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (x * y)).1 =
      (galleryTensorHom k Γ ν' ν'' x).1 * (galleryTensorHom k Γ ν' ν'' y).1 := by
  rw [map_mul]
  rfl

/-- A step of the left factor, on the chamber `C''` of the right factor. -/
theorem galleryTensorHom_t_tmul_e (A' B' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (t A' B' ⊗ₜ e C'')).1 = t (chamber A' C'') (chamber B' C'') := by
  rw [galleryTensorHom_tmul]
  show (leftHom k Γ ν' ν'' (t A' B')).1 * (rightHom k Γ ν' ν'' (e C'')).1 = _
  rw [leftHom_mul_rightHom_e, ChamberEmbedding.toHom_apply, ChamberEmbedding.galleryHom_t]
  rfl

/-- A step of the right factor, on the chamber `C'` of the left factor. -/
theorem galleryTensorHom_e_tmul_t (C' : FullChamber Γ ν') (A'' B'' : FullChamber Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (e C' ⊗ₜ t A'' B'')).1 = t (chamber C' A'') (chamber C' B'') := by
  rw [galleryTensorHom_tmul]
  show (leftHom k Γ ν' ν'' (e C')).1 * (rightHom k Γ ν' ν'' (t A'' B'')).1 = _
  rw [leftHom_e_mul_rightHom, ChamberEmbedding.toHom_apply, ChamberEmbedding.galleryHom_t]
  rfl

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem leftEmb_hyp_ne_rightEmb_hyp (h' : Hyp Γ ν') (h'' : Hyp Γ ν'') :
    (leftEmb ν' ν'').hyp h' ≠ (rightEmb ν' ν'').hyp h'' := fun e => by
  have := congrArg Hyp.lo e
  rw [StrandEmbedding.lo_hyp, StrandEmbedding.lo_hyp] at this
  exact inlStrand_ne_inrStrand ν' ν'' _ _ this

omit [DecidableEq I] in
/-- A chamber obtained from a juxtaposition by crossing a hyperplane between two strands of
`ν'` is the juxtaposition of a chamber adjacent to `C'` with the same `C''`. -/
theorem eq_chamber_of_adjacent_left {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    {E : FullChamber Γ (ν' + ν'')} {h₀ : Hyp Γ ν'}
    (hE : (chamber C' C'').Adjacent E ((leftEmb ν' ν'').hyp h₀)) :
    E = chamber ((leftEmb ν' ν'').restrict E) C'' ∧
      C'.Adjacent ((leftEmb ν' ν'').restrict E) h₀ := by
  have hsame : ∀ x, x ≠ (leftEmb ν' ν'').hyp h₀ → E.1 x = (chamber C' C'').1 x :=
    fun x hx => (hE.2 x hx).symm
  have hsep : IsSeparated (fun t => decide (Strand.IsLeft ν' t)) E := by
    intro x hx
    have hne : x ≠ (leftEmb ν' ν'').hyp h₀ := by
      rintro rfl
      rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hx
      exact hx (by simp [show (leftEmb ν' ν'' : Strand ν' → _) = inlStrand ν' ν'' from rfl,
        isLeft_inlStrand])
    rw [hsame x hne]
    exact isSeparated_chamber C' C'' x hx
  have hR : (rightEmb ν' ν'').restrict E = C'' := by
    apply Subtype.ext
    funext y
    rw [StrandEmbedding.restrict_apply,
      hsame _ (leftEmb_hyp_ne_rightEmb_hyp h₀ y).symm, chamber_right]
  refine ⟨hR ▸ eq_chamber_of_isSeparated hsep, ?_, fun h' hh' => ?_⟩
  · rw [StrandEmbedding.restrict_apply, ← chamber_left C' C'' h₀]
    exact hE.1
  · rw [StrandEmbedding.restrict_apply, hsame _ fun e => hh' ((leftEmb ν' ν'').hyp_injective e),
      chamber_left]

omit [DecidableEq I] in
/-- A chamber obtained from a juxtaposition by crossing a hyperplane between two strands of
`ν''` is the juxtaposition of the same `C'` with a chamber adjacent to `C''`. -/
theorem eq_chamber_of_adjacent_right {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    {E : FullChamber Γ (ν' + ν'')} {h₀ : Hyp Γ ν''}
    (hE : (chamber C' C'').Adjacent E ((rightEmb ν' ν'').hyp h₀)) :
    E = chamber C' ((rightEmb ν' ν'').restrict E) ∧
      C''.Adjacent ((rightEmb ν' ν'').restrict E) h₀ := by
  have hsame : ∀ x, x ≠ (rightEmb ν' ν'').hyp h₀ → E.1 x = (chamber C' C'').1 x :=
    fun x hx => (hE.2 x hx).symm
  have hsep : IsSeparated (fun t => decide (Strand.IsLeft ν' t)) E := by
    intro x hx
    have hne : x ≠ (rightEmb ν' ν'').hyp h₀ := by
      rintro rfl
      rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hx
      exact hx (by simp [show (rightEmb ν' ν'' : Strand ν'' → _) = inrStrand ν' ν'' from rfl,
        not_isLeft_inrStrand])
    rw [hsame x hne]
    exact isSeparated_chamber C' C'' x hx
  have hL : (leftEmb ν' ν'').restrict E = C' := by
    apply Subtype.ext
    funext y
    rw [StrandEmbedding.restrict_apply,
      hsame _ (leftEmb_hyp_ne_rightEmb_hyp y h₀), chamber_left]
  refine ⟨hL ▸ eq_chamber_of_isSeparated hsep, ?_, fun h' hh' => ?_⟩
  · rw [StrandEmbedding.restrict_apply, ← chamber_right C' C'' h₀]
    exact hE.1
  · rw [StrandEmbedding.restrict_apply, hsame _ fun e => hh' ((rightEmb ν' ν'').hyp_injective e),
      chamber_right]

/-- **Block-preserving galleries are juxtapositions.** A minimal gallery from a juxtaposed chamber
`C' ∘ C''` crossing only hyperplanes between two strands of the same block is the image under
`ι = galleryTensorHom` of a tensor product of minimal galleries of `ν'` and `ν''`, and ends at the
juxtaposition of their ends. -/
theorem exists_galList_eq_galleryTensorHom {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    {a : List (Hyp Γ (ν' + ν''))} (ha : GoodWord (chamber C' C'').1 a)
    (hblk : ∀ x ∈ a, decide (Strand.IsLeft ν' x.lo) = decide (Strand.IsLeft ν' x.hi)) :
    ∃ a₁ a₂, GoodWord C'.1 a₁ ∧ GoodWord C''.1 a₂ ∧
      (∀ x ∈ a₁, (leftEmb ν' ν'').hyp x ∈ a) ∧ (∀ x ∈ a₂, (rightEmb ν' ν'').hyp x ∈ a) ∧
      galList k (chamber C' C'') a =
        (galleryTensorHom k Γ ν' ν'' (galList k C' a₁ ⊗ₜ galList k C'' a₂)).1 ∧
      (chamber C' C'').flips a = chamber (C'.flips a₁) (C''.flips a₂) := by
  induction a generalizing C' C'' with
  | nil =>
    exact ⟨[], [], goodWord_nil _, goodWord_nil _, by simp, by simp,
      (galleryTensorHom_e_tmul_e C' C'').symm, rfl⟩
  | cons h w ih =>
    obtain ⟨-, hadj, hw⟩ := ha.cons
    have hnd := ha.1
    rcases mem_range_of_isLeft_iff (hblk h List.mem_cons_self) with ⟨h₀, rfl⟩ | ⟨h₀, rfl⟩
    · obtain ⟨hE, hC'⟩ := eq_chamber_of_adjacent_left hadj
      rw [hE] at hw
      obtain ⟨a₁, a₂, h₁, h₂, m₁, m₂, hg, hf⟩ :=
        ih hw fun x hx => hblk x (List.mem_cons_of_mem _ hx)
      refine ⟨h₀ :: a₁, a₂, GoodWord.of_cons hC' (fun hm => (List.nodup_cons.1 hnd).1 (m₁ _ hm))
        h₁, h₂, ?_, fun x hx => List.mem_cons_of_mem _ (m₂ x hx), ?_, ?_⟩
      · rintro x (_ | ⟨_, hx⟩)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (m₁ x hx)
      · rw [galList_cons, hE, hg, galList_cons, flipH_eq_of_adjacent hC',
          ← galleryTensorHom_t_tmul_e, ← galleryTensorHom_mul_val,
          Algebra.TensorProduct.tmul_mul_tmul, galList_mul_e]
      · rw [flips_cons, hE, hf, flips_cons, flipH_eq_of_adjacent hC']
    · obtain ⟨hE, hC''⟩ := eq_chamber_of_adjacent_right hadj
      rw [hE] at hw
      obtain ⟨a₁, a₂, h₁, h₂, m₁, m₂, hg, hf⟩ :=
        ih hw fun x hx => hblk x (List.mem_cons_of_mem _ hx)
      refine ⟨a₁, h₀ :: a₂, h₁, GoodWord.of_cons hC'' (fun hm => (List.nodup_cons.1 hnd).1
        (m₂ _ hm)) h₂, fun x hx => List.mem_cons_of_mem _ (m₁ x hx), ?_, ?_, ?_⟩
      · rintro x (_ | ⟨_, hx⟩)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (m₂ x hx)
      · rw [galList_cons, hE, hg, galList_cons, flipH_eq_of_adjacent hC'',
          ← galleryTensorHom_e_tmul_t, ← galleryTensorHom_mul_val,
          Algebra.TensorProduct.tmul_mul_tmul, galList_mul_e]
      · rw [flips_cons, hE, hf, flips_cons, flipH_eq_of_adjacent hC'']


/-- A dot on a strand of `ν'`, on a juxtaposed chamber. -/
theorem poly_rename_inl_mul_e (f : PolyRing ν' k) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') :
    poly (rename (inlStrand ν' ν'') f) * e (chamber C' C'') =
      (galleryTensorHom k Γ ν' ν'' ((poly f * e C') ⊗ₜ e C'')).1 := by
  rw [galleryTensorHom_tmul]
  show _ = (leftHom k Γ ν' ν'' (poly f * e C')).1 * (rightHom k Γ ν' ν'' (e C'')).1
  rw [leftHom_mul_rightHom_e, ChamberEmbedding.toHom_apply, map_mul]
  show _ = ((leftChamberEmb C'').galleryHom (poly f)).1 * ((leftChamberEmb C'').galleryHom (e C')).1
  rw [ChamberEmbedding.galleryHom_poly, ChamberEmbedding.galleryHom_e, mul_assoc]
  congr 1
  show _ = (∑ A', e (chamber A' C'')) * e (chamber C' C'')
  rw [Finset.sum_mul, Finset.sum_eq_single C', e_mul_e, ite_eq_left rfl]
  · intro A' _ hA
    rw [e_mul_e_chamber, ite_eq_right fun h => hA h.1]
  · simp

/-- A dot on a strand of `ν''`, on a juxtaposed chamber. -/
theorem poly_rename_inr_mul_e (f : PolyRing ν'' k) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') :
    poly (rename (inrStrand ν' ν'') f) * e (chamber C' C'') =
      (galleryTensorHom k Γ ν' ν'' (e C' ⊗ₜ (poly f * e C''))).1 := by
  rw [galleryTensorHom_tmul]
  show _ = (leftHom k Γ ν' ν'' (e C')).1 * (rightHom k Γ ν' ν'' (poly f * e C'')).1
  rw [leftHom_e_mul_rightHom, ChamberEmbedding.toHom_apply, map_mul]
  show _ = ((rightChamberEmb C').galleryHom (poly f)).1 *
    ((rightChamberEmb C').galleryHom (e C'')).1
  rw [ChamberEmbedding.galleryHom_poly, ChamberEmbedding.galleryHom_e, mul_assoc]
  congr 1
  show _ = (∑ A'', e (chamber C' A'')) * e (chamber C' C'')
  rw [Finset.sum_mul, Finset.sum_eq_single C'', e_mul_e, ite_eq_left rfl]
  · intro A'' _ hA
    rw [e_mul_e_chamber, ite_eq_right fun h => hA h.2]
  · simp

/-- **Dots on a juxtaposed chamber** lie in the image of `ι = galleryTensorHom`. -/
theorem exists_poly_mul_e_eq_galleryTensorHom (f : PolyRing (ν' + ν'') k)
    (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    ∃ z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'',
      poly f * e (chamber C' C'') = (galleryTensorHom k Γ ν' ν'' z).1 := by
  have hpoly : ∀ f : PolyRing (ν' + ν'') k, (poly f : GalleryAlgebra k Γ (ν' + ν'')) =
      polyHom k Γ (ν' + ν'') f := fun _ => rfl
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a • (e C' ⊗ₜ e C''), ?_⟩
    rw [map_smul, corner_val_smul, galleryTensorHom_e_tmul_e, hpoly, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  | add p q hp hq =>
    obtain ⟨z, hz⟩ := hp
    obtain ⟨z', hz'⟩ := hq
    refine ⟨z + z', ?_⟩
    rw [map_add, corner_val_add, ← hz, ← hz', hpoly, map_add, add_mul, ← hpoly, ← hpoly]
  | mul_X p n hp =>
    obtain ⟨z, hz⟩ := hp
    have hX : ∃ w : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'',
        poly (X n) * e (chamber C' C'') = (galleryTensorHom k Γ ν' ν'' w).1 := by
      obtain ⟨s | s, rfl⟩ := (strandEquiv ν' ν'').surjective n
      · refine ⟨(poly (X s) * e C') ⊗ₜ e C'', ?_⟩
        rw [strandEquiv_inl, ← poly_rename_inl_mul_e, rename_X]
      · refine ⟨e C' ⊗ₜ (poly (X s) * e C''), ?_⟩
        rw [strandEquiv_inr, ← poly_rename_inr_mul_e, rename_X]
    obtain ⟨w, hw⟩ := hX
    refine ⟨z * w, ?_⟩
    rw [galleryTensorHom_mul_val, ← hz, ← hw, hpoly, map_mul, ← hpoly, ← hpoly, mul_assoc,
      mul_assoc, ← mul_assoc (e _), e_mul_poly, mul_assoc, e_mul_e, ite_eq_left rfl]


/-- **Block pieces with dots lie in the image of the juxtaposition map.** Let `E` be a chamber of
`ν = ν' + ν''` in which the strands of `ν'` lie to the left, and `c` a minimal gallery from `E`
crossing only hyperplanes between two strands of the same block. Then `c * y^f` is the image
under `ι = galleryTensorHom` of an element of the tensor product of the two smaller gallery
algebras. -/
theorem exists_galList_mul_poly_eq_castGallery {ν : I →₀ ℕ} (hν : ν' + ν'' = ν)
    {E : FullChamber Γ ν} (hE : IsSeparated (fun t => decide (Strand.IsLeft ν' t)) E)
    {c : List (Hyp Γ ν)} (hc : GoodWord E.1 c)
    (hblk : ∀ x ∈ c, decide (Strand.IsLeft ν' x.lo) = decide (Strand.IsLeft ν' x.hi))
    (f : PolyRing ν k) :
    ∃ z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'',
      galList k E c * poly f = castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z).1 := by
  subst hν
  obtain ⟨C', C'', rfl⟩ : ∃ C' C'', E = chamber C' C'' := ⟨_, _, eq_chamber_of_isSeparated hE⟩
  obtain ⟨a₁, a₂, -, -, -, -, hg, -⟩ := exists_galList_eq_galleryTensorHom (k := k) hc hblk
  obtain ⟨z, hz⟩ := exists_poly_mul_e_eq_galleryTensorHom f C' C''
  refine ⟨(galList k C' a₁ ⊗ₜ galList k C'' a₂) * z, ?_⟩
  show _ = (galleryTensorHom k Γ ν' ν'' _).1
  rw [galleryTensorHom_mul_val, ← hg, ← hz, ← e_mul_poly, ← mul_assoc, galList_mul_e]

/-- **Block pieces lie in the image of the juxtaposition map.** The form of
`exists_galList_mul_poly_eq_castGallery` without dots. -/
theorem exists_galList_eq_castGallery {ν : I →₀ ℕ} (hν : ν' + ν'' = ν)
    {E : FullChamber Γ ν} (hE : IsSeparated (fun t => decide (Strand.IsLeft ν' t)) E)
    {c : List (Hyp Γ ν)} (hc : GoodWord E.1 c)
    (hblk : ∀ x ∈ c, decide (Strand.IsLeft ν' x.lo) = decide (Strand.IsLeft ν' x.hi)) :
    ∃ z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'',
      galList k E c = castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z).1 := by
  obtain ⟨z, hz⟩ := exists_galList_mul_poly_eq_castGallery (k := k) (ν'' := ν'') hν hE hc hblk 1
  refine ⟨z, ?_⟩
  rw [← hz, show (poly 1 : GalleryAlgebra k Γ ν) = polyHom k Γ ν 1 from rfl, map_one, mul_one]

end Juxtapose

namespace GalleryAlgebra

variable {ν' ν'' ν : I →₀ ℕ}

/-- **The bottom piece lies in the image of `ι`.** In the factorization through the shuffle
(`shuffle_sub_cornerBasis_mem`), for `ν = ν' + ν''` and `C` separated by the strands of `ν'`, the
bottom piece `a * y^f` is `ι(z)` for some `z` in the tensor product of the gallery algebras of
`ν'` and `ν''`. -/
theorem exists_bot_mul_poly_eq_castGallery (hν : ν' + ν'' = ν) {Y : Strand ν → Bool}
    {C : FullChamber Γ ν} (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    {a : List (Hyp Γ ν)} (ha : GoodWord C.1 a)
    (hfa : C.flips a = shuffleBot (fun t => decide (t.IsLeft ν')) Y C) (f : PolyRing ν k) :
    ∃ z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'',
      galList k C a * poly f = castGallery k Γ hν (Juxtapose.galleryTensorHom k Γ ν' ν'' z).1 :=
  Juxtapose.exists_galList_mul_poly_eq_castGallery hν hCs ha
    (fun _ hx => (mem_bot_shuffle hCs ha hfa hx).1) f

/-- **The top piece lies in the image of `ι`, after the relabelling.** In the factorization
through the shuffle (`shuffle_sub_cornerBasis_mem`), for `ν = ν₁ + ν₂` and `D` separated by the
strands of `ν₁`, the top piece `r g (g⁻¹ • D) * c` equals `ι(z) * r g (shuffleTop Y C)` for some
`z` in the tensor product of the gallery algebras of `ν₁` and `ν₂`, where
`Y t = (g t).IsLeft ν₁`. -/
theorem exists_r_mul_top_eq_castGallery {ν₁ ν₂ : I →₀ ℕ} (hν : ν₁ + ν₂ = ν)
    {C D : FullChamber Γ ν} (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D)
    (g : ColPerm ν) {c : List (Hyp Γ ν)}
    (hc : GoodWord (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C).1 c)
    (hfc : (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C).flips c = g⁻¹ • D) :
    ∃ z : GalleryAlgebra k Γ ν₁ ⊗[k] GalleryAlgebra k Γ ν₂,
      r g (g⁻¹ • D) * galList k (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) c =
        castGallery k Γ hν (Juxtapose.galleryTensorHom k Γ ν₁ ν₂ z).1 *
          r g (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) := by
  set Y : Strand ν → Bool := fun t => decide ((g.1 t).IsLeft ν₁) with hYdef
  have hE : IsSeparated Y (g⁻¹ • D) := by
    have := hDs.smul g⁻¹
    simpa using this
  obtain ⟨hw, -, hg⟩ := goodWord_smul (k := k) g hc
  rw [hfc] at hg
  have hsep : IsSeparated (fun t => decide (t.IsLeft ν₁)) (g • shuffleTop Y C) := by
    have h0 : IsSeparated Y (shuffleTop Y C) := isSeparated_sep Y C C
    have := h0.smul g
    simpa [hYdef] using this
  have hblk : ∀ x ∈ c.map (Hyp.comap g⁻¹),
      decide (Strand.IsLeft ν₁ x.lo) = decide (Strand.IsLeft ν₁ x.hi) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hY : Y y.lo = Y y.hi := mem_top_shuffle hE hc hfc hy
    rw [Hyp.lo_comap, Hyp.hi_comap]
    split_ifs <;> first | simpa [hYdef] using hY | simpa [hYdef] using hY.symm
  obtain ⟨z, hz⟩ := Juxtapose.exists_galList_eq_castGallery (k := k) (ν'' := ν₂) hν hsep hw hblk
  exact ⟨z, by rw [← hg, hz]⟩

end GalleryAlgebra

end Categorification.WeightedKLR
