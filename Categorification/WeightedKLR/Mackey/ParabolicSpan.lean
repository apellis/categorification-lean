/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.JuxtaposedCorner
import Categorification.WeightedKLR.Mackey.CornerShuffle
import Categorification.WeightedKLR.Mackey.CrossingGallery
import Categorification.WeightedKLR.Mackey.FourBlockShuffle

/-!
# Corners of Webster's algebra over a parabolic subalgebra

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `ν = ν' + ν''`, `C` a rank-ordered chamber with the
strands of `ν'` to the left (so that `e C` is fixed by Webster's idempotent `e_{ν';ν''}`), and `D`
any rank-ordered chamber. The corner `e D * A * e C` is spanned, as a right module over
`W_{ν'} ⊗ W_{ν''}` acting through Webster's map `ι = inductionMap`, by the *coset elements*
`r u (u⁻¹ • D) * c_u`, one for each relabelling `u` whose chamber
`G_u = shuffleTop X (u⁻¹ • D)` is rank-ordered. Here `X` marks the strands of `ν'`,
`G_u` is the chamber closest to `u⁻¹ • D` with the strands of `ν'` to the left, and `c_u` is a
minimal gallery from `G_u` to `u⁻¹ • D`. These relabellings play the role of the minimal coset
representatives of the parabolic subgroup `S_{ν'} × S_{ν''}`.

The proof factors each basis element `b(g, m)` of Theorem 2.8 through `G = shuffleTop X (g⁻¹ • D)`:
a minimal gallery `C → G → g⁻¹ • D` is minimal (`G` lies between `C` and `g⁻¹ • D`), its piece
`C → G` does not cross the hyperplanes between the two blocks and so is a juxtaposition
(`Juxtapose.exists_galList_mul_poly_eq_castGallery`), and its piece `G → g⁻¹ • D` crosses only
those hyperplanes, so does not depend on the minimal gallery (`galList_eq_of_crossing`). Sorting
`G` inside the blocks (`Juxtapose.blockSort`) changes the relabelling to a representative `u`.
Independence of the minimal gallery (`r_mul_galList_mul_sub_cornerBasis_mem`) gives
`b(g, m) ≡ r u (u⁻¹ • D) c_u ι(y)` modulo basis elements with shorter chosen gallery, and
induction on the length gives spanning.

## Main definitions

* `GalleryAlgebra.cosetWord`: a minimal gallery from `shuffleTop X E` to `E`.
* `GalleryAlgebra.cosetElt`: the coset element `r g (g⁻¹ • D) * c_g`.

## Main results

* `GalleryAlgebra.galList_eq_cosetWord`: any minimal gallery from `shuffleTop X E` to `E` gives
  the same element.
* `GalleryAlgebra.cosetElt_eq_mul_r`: right relabelling of a coset element inside the blocks.
* `GalleryAlgebra.exists_cosetElt_mul_inductionMap_sub_cornerBasis_mem`: **factorization**
  `b(g, m) ≡ r u (u⁻¹ • D) c_u ι(y)` with `u` a representative.
* `GalleryAlgebra.cornerSpace_le_span_cosetElt`: **spanning** of the corner by coset elements
  over `W_{ν'} ⊗ W_{ν''}`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise GalleryAlgebra

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

open Juxtapose

variable {ν' ν'' : I →₀ ℕ}

omit [DecidableEq I] in
/-- A relabelling inside the blocks preserves the strands of the first block. -/
theorem isLeft_inv_apply_of_mem {v : ColPerm ν} (hv : v ∈ leftBlockStab ν ν')
    (t : Strand ν) : decide ((v.1⁻¹ t).IsLeft ν') = decide (t.IsLeft ν') := by
  have := hv (v.1⁻¹ t)
  have h2 : v.1 (v.1⁻¹ t) = t := by simp
  rw [h2] at this
  exact decide_eq_decide.2 this.symm

omit [DecidableEq I] in
theorem shuffleTop_smul_of_mem {v : ColPerm ν} (hv : v ∈ leftBlockStab ν ν')
    (E : FullChamber Γ ν) :
    v • shuffleTop (fun t => decide (t.IsLeft ν')) E =
      shuffleTop (fun t => decide (t.IsLeft ν')) (v • E) := by
  rw [shuffleTop_smul]
  congr 1
  funext t
  exact isLeft_inv_apply_of_mem hv t

omit [DecidableEq I] in
/-- The hyperplanes on which `shuffleTop X E` and `E` differ are crossing for `X`. -/
theorem isCrossing_of_shuffleTop_ne (X : Strand ν → Bool) (E : FullChamber Γ ν) {h : Hyp Γ ν}
    (hne : (shuffleTop X E).1 h ≠ E.1 h) : h.IsCrossing X := by
  intro hX
  rw [shuffleTop_apply, ite_eq_left hX] at hne
  exact hne rfl

omit [IsStrictOrderedRing 𝕜] in
/-- A minimal gallery between two chambers separated by `X` crosses no hyperplane between the two
classes of strands. -/
theorem not_isCrossing_of_mem {X : Strand ν → Bool} {C : FullChamber Γ ν} (hC : IsSeparated X C)
    {a : List (Hyp Γ ν)} (ha : GoodWord C.1 a) (hfa : IsSeparated X (C.flips a)) {x : Hyp Γ ν}
    (hx : x ∈ a) : X x.lo = X x.hi := by
  by_contra h
  exact (ha.mem_iff x).1 hx ((hfa x h).trans (hC x h).symm)

/-- A minimal gallery from `shuffleTop X E` to `E`. -/
noncomputable def cosetWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' : I →₀ ℕ)
    (E : FullChamber Γ ν) : List (Hyp Γ ν) :=
  (exists_goodWord hD hZ (shuffleTop (fun t => decide (t.IsLeft ν')) E) E).choose

theorem goodWord_cosetWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' : I →₀ ℕ)
    (E : FullChamber Γ ν) :
    GoodWord (shuffleTop (fun t => decide (t.IsLeft ν')) E).1 (cosetWord hD hZ ν' E) ∧
      (shuffleTop (fun t => decide (t.IsLeft ν')) E).flips (cosetWord hD hZ ν' E) = E :=
  (exists_goodWord hD hZ (shuffleTop (fun t => decide (t.IsLeft ν')) E) E).choose_spec

/-- **The top piece does not depend on the minimal gallery.** -/
theorem galList_eq_cosetWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' : I →₀ ℕ)
    (E : FullChamber Γ ν) {c : List (Hyp Γ ν)}
    (hc : GoodWord (shuffleTop (fun t => decide (t.IsLeft ν')) E).1 c)
    (hfc : (shuffleTop (fun t => decide (t.IsLeft ν')) E).flips c = E) :
    galList k (shuffleTop (fun t => decide (t.IsLeft ν')) E) c =
      galList k (shuffleTop (fun t => decide (t.IsLeft ν')) E) (cosetWord hD hZ ν' E) := by
  obtain ⟨hw, hfw⟩ := goodWord_cosetWord hD hZ ν' E
  refine galList_eq_of_crossing hD hZ (fun t => decide (t.IsLeft ν')) hc hw
    (hfc.trans hfw.symm) fun h hne => ?_
  rw [hfc] at hne
  exact isCrossing_of_shuffleTop_ne _ E (Ne.symm hne)

variable (k) in
/-- **The coset element** `r g (g⁻¹ • D) * c_g`, with `c_g` a minimal gallery from
`shuffleTop X (g⁻¹ • D)` to `g⁻¹ • D`, where `X` marks the strands of `ν'`. -/
noncomputable def cosetElt (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' : I →₀ ℕ) (g : ColPerm ν)
    (D : FullChamber Γ ν) : GalleryAlgebra k Γ ν :=
  r g (g⁻¹ • D) * galList k (shuffleTop (fun t => decide (t.IsLeft ν')) (g⁻¹ • D))
    (cosetWord hD hZ ν' (g⁻¹ • D))

theorem cosetElt_mul_e (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν)
    (D : FullChamber Γ ν) :
    cosetElt k hD hZ ν' g D * e (shuffleTop (fun t => decide (t.IsLeft ν')) (g⁻¹ • D)) =
      cosetElt k hD hZ ν' g D := by
  rw [cosetElt, mul_assoc, galList_mul_e]

/-- **Relabelling a coset element inside the blocks.** For `v` preserving the blocks,
`r g (g⁻¹ • D) c_g = r (g v⁻¹) (v g⁻¹ • D) c_{g v⁻¹} * r v (shuffleTop X (g⁻¹ • D))`. -/
theorem cosetElt_eq_mul_r (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν)
    (D : FullChamber Γ ν) {v : ColPerm ν} (hv : v ∈ leftBlockStab ν ν') :
    cosetElt k hD hZ ν' g D =
      cosetElt k hD hZ ν' (g * v⁻¹) D *
        r v (shuffleTop (fun t => decide (t.IsLeft ν')) (g⁻¹ • D)) := by
  set E := g⁻¹ • D
  set X : Strand ν → Bool := fun t => decide (t.IsLeft ν')
  obtain ⟨hc, hfc⟩ := goodWord_cosetWord hD hZ ν' E
  obtain ⟨hw, hfw, hg⟩ := goodWord_smul (k := k) v hc
  have hE : (g * v⁻¹)⁻¹ • D = v • E := by rw [mul_inv_rev, inv_inv, mul_smul]
  have hT : shuffleTop X (v • E) = v • shuffleTop X E := (shuffleTop_smul_of_mem hv E).symm
  rw [hfc] at hg hfw
  rw [← hT] at hw hfw hg
  rw [cosetElt, cosetElt, hE, ← galList_eq_cosetWord hD hZ ν' (v • E) hw hfw, mul_assoc, hg,
    ← mul_assoc, r_mul_r, inv_mul_cancel_right]

/-- **Choice of a representative.** Every coset element is a coset element of a relabelling `u`
with `shuffleTop X (u⁻¹ • D)` rank-ordered, times `ι(z)` on the right. -/
theorem exists_cosetElt_eq_mul_castGallery (hν : ν' + ν'' = ν) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (D : FullChamber Γ ν) :
    ∃ (u : ColPerm ν) (z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν''),
      (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)).IsRankOrdered ∧
        cosetElt k hD hZ ν' g D =
          cosetElt k hD hZ ν' u D * castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z).1 := by
  set G := shuffleTop (fun t => decide (t.IsLeft ν')) (g⁻¹ • D)
  have hG : IsSeparated (fun t => decide (t.IsLeft ν')) G := isSeparated_sep _ _ _
  obtain ⟨h₁, -, -, ⟨z, hz⟩⟩ := blockSort_spec (k := k) hν hG
  have hv := blockSort_mem_leftBlockStab hν G
  refine ⟨g * (blockSort hν G)⁻¹, z, ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv, mul_smul, ← shuffleTop_smul_of_mem hv]
    exact h₁
  · rw [← hz]
    exact cosetElt_eq_mul_r hD hZ g D hv

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **Factorization through a coset element, gallery algebras.** For `C` rank-ordered with the
strands of `ν'` to the left and `D` rank-ordered, `b(g, m) ≡ r u (u⁻¹ • D) c_u ι(z)` modulo basis
elements with shorter chosen gallery, for a representative `u` and `z` in the tensor product of the
gallery algebras of `ν'` and `ν''`. -/
theorem exists_cosetElt_mul_castGallery_sub_cornerBasis_mem (hν : ν' + ν'' = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    ∃ (u : ColPerm ν) (z : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν''),
      (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)).IsRankOrdered ∧
      cosetElt k hD hZ ν' u D * castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z).1 -
          (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
        Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
          segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
            (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  set E := g⁻¹ • D
  set X : Strand ν → Bool := fun t => decide (t.IsLeft ν')
  set G := shuffleTop X E
  obtain ⟨a, ha, hfa⟩ := exists_goodWord hD hZ C G
  obtain ⟨hc, hfc⟩ := goodWord_cosetWord hD hZ ν' E
  have hac : GoodWord C.1 (a ++ cosetWord hD hZ ν' E) := by
    refine GoodWord.append_of_between ha (hfa ▸ hc) fun x hx => ?_
    rw [hfa, hfc] at hx
    rw [hfa]
    exact (shuffleTop_between hCs x hx.symm).trans hx.symm
  have hfac : C.flips (a ++ cosetWord hD hZ ν' E) = E := by rw [flips_append, hfa, hfc]
  have h := r_mul_galList_mul_sub_cornerBasis_mem hP hD hZ hΓ hW hL ν' ν' hC hD'
    (S := Set.univ) isLowerSet_univ (Set.mem_univ _) hac hfac m
  have hblk : ∀ x ∈ a, decide (Strand.IsLeft ν' x.lo) = decide (Strand.IsLeft ν' x.hi) :=
    fun x hx => not_isCrossing_of_mem hCs ha (hfa ▸ isSeparated_sep _ _ _) hx
  obtain ⟨z₁, hz₁⟩ := exists_galList_mul_poly_eq_castGallery (k := k) hν hCs ha hblk
    (monomial m 1)
  obtain ⟨u, z₂, hu, hz₂⟩ := exists_cosetElt_eq_mul_castGallery (k := k) hν hD hZ g D
  refine ⟨u, z₂ * z₁, hu, ?_⟩
  have hm : castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' (z₂ * z₁)).1 =
      castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z₂).1 *
        castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' z₁).1 := by
    rw [galleryTensorHom_mul_val, map_mul]
  have hr : r g E * galList k C (a ++ cosetWord hD hZ ν' E) * poly (monomial m 1) =
      cosetElt k hD hZ ν' u D * castGallery k Γ hν (galleryTensorHom k Γ ν' ν'' (z₂ * z₁)).1 := by
    rw [hm, ← mul_assoc, ← hz₂, ← hz₁, galList_append, hfa, cosetElt]
    simp only [mul_assoc]
    rfl
  rw [← hr]
  refine Submodule.span_mono ?_ h
  rintro _ ⟨⟨i, -, hi⟩, rfl⟩
  exact ⟨⟨i, hi⟩, rfl⟩

/-- **Factorization through a coset element.** For `C` rank-ordered with the strands of `ν'` to
the left and `D` rank-ordered, `b(g, m) ≡ r u (u⁻¹ • D) c_u ι(y)` modulo basis elements with
shorter chosen gallery, for a representative `u` (with `shuffleTop X (u⁻¹ • D)` rank-ordered) and
`y ∈ W_{ν'} ⊗ W_{ν''}`, where `ι` is Webster's map `inductionMap`. -/
theorem exists_cosetElt_mul_inductionMap_sub_cornerBasis_mem (hν : ν' + ν'' = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    ∃ (u : ColPerm ν) (y : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''),
      (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)).IsRankOrdered ∧
      cosetElt k hD hZ ν' u D * castGallery k Γ hν (inductionMap k Γ ν' ν'' y).1 -
          (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
        Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
          segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
            (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  obtain ⟨u, z, hu, h⟩ := exists_cosetElt_mul_castGallery_sub_cornerBasis_mem hP hD hZ hΓ hW hL
    hν hC hD' hCs g m
  set s := castGallery k Γ hν (splitIdem k Γ ν' ν'')
  set L := Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
          segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
            (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν))
  have hfix : ∀ x : cornerSpace k D C, (x : GalleryAlgebra k Γ ν) * s = x := fun x => by
    rw [← mem_cornerSpace_iff.1 x.2, mul_assoc, e_mul_castGallery_splitIdem hν hC hCs]
  have hLs : ∀ x ∈ L, x * s ∈ L := fun x hx => by
    have hle : L ≤ L.comap (LinearMap.mulRight k s) := Submodule.span_le.2 <| by
      rintro _ ⟨i, rfl⟩
      show _ * s ∈ L
      rw [hfix]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact hle hx
  have hT : cosetElt k hD hZ ν' u D * s = cosetElt k hD hZ ν' u D := by
    rw [← cosetElt_mul_e, mul_assoc, e_mul_castGallery_splitIdem hν hu (isSeparated_sep _ _ _)]
  obtain ⟨y, hy⟩ := exists_castGallery_splitIdem_mul_mul hν z
  refine ⟨u, y, hu, ?_⟩
  have h' := hLs _ h
  rwa [sub_mul, hfix, mul_assoc, ← hT, mul_assoc, ← mul_assoc s, hy] at h'

include hP hΓ hW hL in
/-- **Spanning of a corner over a parabolic subalgebra.** For `ν = ν' + ν''`, `C` rank-ordered
with the strands of `ν'` to the left and `D` rank-ordered, the corner `e D * A * e C` is spanned by
the products `r u (u⁻¹ • D) c_u * ι(y)` with `u` a representative (`shuffleTop X (u⁻¹ • D)`
rank-ordered) and `y ∈ W_{ν'} ⊗ W_{ν''}`; that is, the corner is generated as a right
`W_{ν'} ⊗ W_{ν''}`-module by the coset elements. -/
theorem cornerSpace_le_span_cosetElt (hν : ν' + ν'' = ν) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    cornerSpace k D C ≤ Submodule.span k (Set.range fun p :
      {u : ColPerm ν // (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)).IsRankOrdered} ×
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') =>
          cosetElt k hD hZ ν' p.1.1 D * castGallery k Γ hν (inductionMap k Γ ν' ν'' p.2).1) := by
  set T := Submodule.span k (Set.range fun p :
      {u : ColPerm ν // (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)).IsRankOrdered} ×
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') =>
          cosetElt k hD hZ ν' p.1.1 D * castGallery k Γ hν (inductionMap k Γ ν' ν'' p.2).1)
  have key : ∀ n, ∀ i : ColPerm ν × (Strand ν →₀ ℕ), segLength P C (i.1⁻¹ • D) = n →
      (cornerBasis hP hD hZ hΓ hW hL D C i : GalleryAlgebra k Γ ν) ∈ T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro ⟨g, m⟩ rfl
      obtain ⟨u, y, hu, h⟩ := exists_cosetElt_mul_inductionMap_sub_cornerBasis_mem hP hD hZ hΓ hW
        hL hν hC hD' hCs g m
      have hL : Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
          segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
            (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) ≤ T :=
        Submodule.span_le.2 <| by
          rintro _ ⟨⟨i, hi⟩, rfl⟩
          exact ih _ hi i rfl
      have hmem : cosetElt k hD hZ ν' u D * castGallery k Γ hν (inductionMap k Γ ν' ν'' y).1 ∈ T :=
        Submodule.subset_span ⟨(⟨u, hu⟩, y), rfl⟩
      have := T.sub_mem hmem (hL h)
      rwa [sub_sub_cancel] at this
  intro x hx
  have hspan := (Module.Basis.mem_span_range_iff (cornerBasis hP hD hZ hΓ hW hL D C)
    (fun _ => True) ⟨x, hx⟩).2 (fun _ _ => trivial)
  refine Submodule.span_le.2 ?_ hspan
  rintro _ ⟨⟨i, -⟩, rfl⟩
  exact key _ i rfl

end GalleryAlgebra

end Categorification.WeightedKLR
