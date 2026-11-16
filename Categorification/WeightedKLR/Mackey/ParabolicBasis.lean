/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ParabolicSpan

/-!
# Corners of Webster's algebra are free over a parabolic subalgebra

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `ν = ν' + ν''`, `C = C' ∘ C''` a juxtaposition of
rank-ordered chambers and `D` a rank-ordered chamber. For each representative `u` (a relabelling
with `G_u = shuffleTop X (u⁻¹ • D)` rank-ordered, `X` marking the strands of `ν'`), write
`G_u = G'_u ∘ G''_u`. Then the elements
`r u (u⁻¹ • D) c_u * ι(b'(h', m') ⊗ b''(h'', m''))`, for `b'` and `b''` the bases of
Theorem 2.8 of the corners `e G'_u * A_{ν'} * e C'` and `e G''_u * A_{ν''} * e C''`, form a
`k`-basis of the corner `e D * A_ν * e C` (`GalleryAlgebra.parabolicCornerBasis`). Equivalently,
the corner is the direct sum over the representatives `u` of the tensor products of the corners of
`ν'` and `ν''`, embedded by `x ↦ r u (u⁻¹ • D) c_u * ι(x)` (`GalleryAlgebra.parabolicCornerEquiv`,
`GalleryAlgebra.parabolicCornerEquiv_single`). This is the corner form of the freeness of the
algebra as a right module over the parabolic subalgebra on the coset elements.

The proof is a triangularity argument. The element indexed by `(u, (h', m'), (h'', m''))` is the
element along the minimal gallery `w ++ c_{u h}` (`w` the juxtaposition of the two chosen
galleries, `h = colPermProd (h', h'')`) with relabelling `u h` and dots `m' ∘ m''`
(`Juxtapose.galList_map_append_map`, `cosetElt_eq_mul_r`), so it is congruent to the basis element
`b(u h, m' ∘ m'')` modulo basis elements with shorter chosen gallery
(`r_mul_galList_mul_sub_cornerBasis_mem`). The leading index `(u h, m' ∘ m'')` is a bijection of
the index sets: `g = u h` is the unique factorization of `existsUnique_rep`, the relabellings
inside the blocks are exactly the products `colPermProd (h', h'')`
(`Juxtapose.exists_colPermProd_eq`), and dots split along the two blocks (`juxtDots_bijective`).

## Main results

* `Module.Basis.ofTriangular`: a family congruent to a basis modulo shorter basis vectors, with
  bijective leading index, is a basis.
* `Juxtapose.colPermProd_injective`, `Juxtapose.exists_colPermProd_eq`: the relabellings inside
  the blocks are exactly the products of relabellings of the two sides.
* `Juxtapose.galList_map_append_map`: the juxtaposition of two minimal galleries is a minimal
  gallery, whose element is the image of the tensor product under `ι = galleryTensorHom`.
* `GalleryAlgebra.parabolicCornerBasis`: the basis of the corner adapted to the parabolic
  subalgebra.
* `GalleryAlgebra.parabolicCornerEquiv`: **freeness** of the corner over the parabolic
  subalgebra.
-/

namespace Module.Basis

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Triangular families are bases.** Let `b` be a basis indexed by `ι`, `ℓ : ι → ℕ` a length,
and `x` a family indexed by `κ` with a bijective leading index `e : κ ≃ ι`, such that `x j`
differs from `b (e j)` by a combination of basis vectors of smaller length. Then `x` is a basis.
-/
noncomputable def ofTriangular (b : Module.Basis ι R M) (ℓ : ι → ℕ) (e : κ ≃ ι) (x : κ → M)
    (hx : ∀ j, x j - b (e j) ∈ Submodule.span R (b '' {i | ℓ i < ℓ (e j)})) :
    Module.Basis κ R M :=
  Module.Basis.mk (v := x)
    (by
      rw [linearIndependent_iff']
      intro s g hg j hj
      classical
      by_contra hne
      obtain ⟨j₀, hj₀, hmax⟩ : ∃ j ∈ s.filter (fun j => g j ≠ 0),
          ∀ j' ∈ s.filter (fun j => g j ≠ 0), ℓ (e j') ≤ ℓ (e j) :=
        Finset.exists_max_image _ (fun j => ℓ (e j)) ⟨j, Finset.mem_filter.2 ⟨hj, hne⟩⟩
      obtain ⟨hj₀s, hj₀g⟩ := Finset.mem_filter.1 hj₀
      have hterm : ∀ j' ∈ s, g j' * b.repr (x j') (e j₀) = if j' = j₀ then g j₀ else 0 := by
        intro j' hj'
        by_cases hg' : g j' = 0
        · rw [hg', zero_mul]
          split_ifs with h
          · rw [← h, hg']
          · rfl
        have hle : ℓ (e j') ≤ ℓ (e j₀) := hmax j' (Finset.mem_filter.2 ⟨hj', hg'⟩)
        have hz : b.repr (x j' - b (e j')) (e j₀) = 0 := by
          rw [← Finsupp.notMem_support_iff]
          intro hmem
          have := b.mem_span_image.1 (hx j') hmem
          exact absurd hle (not_le.2 this)
        rw [map_sub, Finsupp.sub_apply, b.repr_self, sub_eq_zero] at hz
        rw [hz, Finsupp.single_apply, e.injective.eq_iff]
        split_ifs with h
        · rw [h, mul_one]
        · exact mul_zero _
      have h0 := congrArg (fun y => b.repr y (e j₀)) hg
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h0
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j₀] at h0
      simp only [hj₀s, ↓reduceIte] at h0
      exact hj₀g h0)
    (by
      have key : ∀ n, ∀ i, ℓ i = n → b i ∈ Submodule.span R (Set.range x) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro i hi
          have hsub : Submodule.span R (b '' {i' | ℓ i' < ℓ i}) ≤
              Submodule.span R (Set.range x) := by
            rw [Submodule.span_le]
            rintro _ ⟨i', hi', rfl⟩
            exact ih _ (hi ▸ hi') i' rfl
          have h := hx (e.symm i)
          rw [e.apply_symm_apply] at h
          replace h := hsub h
          have hxi : x (e.symm i) ∈ Submodule.span R (Set.range x) :=
            Submodule.subset_span ⟨_, rfl⟩
          simpa using Submodule.sub_mem _ hxi h
      rw [← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact key _ i rfl)

theorem ofTriangular_apply (b : Module.Basis ι R M) (ℓ : ι → ℕ) (e : κ ≃ ι) (x : κ → M)
    (hx : ∀ j, x j - b (e j) ∈ Submodule.span R (b '' {i | ℓ i < ℓ (e j)})) (j : κ) :
    ofTriangular b ℓ e x hx j = x j :=
  Module.Basis.mk_apply _ _ _

theorem mem_span_image_of_coe_mem {G : Type*} [AddCommGroup G] [Module R G] {N : Submodule R G}
    (b : Module.Basis ι R N) (p : ι → Prop) {y : N}
    (hy : (y : G) ∈ Submodule.span R (Set.range fun i : {i // p i} => (b i : G))) :
    y ∈ Submodule.span R (b '' {i | p i}) := by
  have hy' : (y : G) ∈ Submodule.span R (N.subtype '' (b '' {i | p i})) := by
    convert hy using 2
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨b i, ⟨i, hi, rfl⟩, rfl⟩
  rw [← Submodule.map_span] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  rwa [N.injective_subtype hzy] at hz

end Module.Basis

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise GalleryAlgebra

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

omit [DecidableEq I] in
/-- Relabellings of the two sides are determined by their product. -/
theorem colPermProd_injective : Function.Injective (colPermProd ν' ν'') := by
  intro g g' h
  have h1 : ∀ s, g.1.1 s = g'.1.1 s := fun s => inlStrand_injective ν' ν'' (by
    rw [← colPermProd_inl, ← colPermProd_inl, h])
  have h2 : ∀ s, g.2.1 s = g'.2.1 s := fun s => inrStrand_injective ν' ν'' (by
    rw [← colPermProd_inr, ← colPermProd_inr, h])
  exact Prod.ext (Subtype.ext (Equiv.ext h1)) (Subtype.ext (Equiv.ext h2))

omit [DecidableEq I] in
/-- **The relabellings inside the blocks are products.** Every relabelling of `ν' + ν''` preserving
the strands of `ν'` is the product of a relabelling of `ν'` and one of `ν''`. -/
theorem exists_colPermProd_eq {v : ColPerm (ν' + ν'')} (hv : v ∈ leftBlockStab (ν' + ν'') ν') :
    ∃ g, colPermProd ν' ν'' g = v := by
  set σ : Perm (Strand ν' ⊕ Strand ν'') := (strandEquiv ν' ν'').symm.permCongr v.1
  have hσ : ∀ x, strandEquiv ν' ν'' (σ x) = v.1 (strandEquiv ν' ν'' x) := fun x => by
    simp [σ, Equiv.permCongr_apply]
  have hmaps : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨s, rfl⟩
    rcases hx : σ (.inl s) with a | b
    · exact ⟨a, rfl⟩
    · exfalso
      have := hσ (.inl s)
      rw [hx, strandEquiv_inr, strandEquiv_inl] at this
      exact not_isLeft_inrStrand (ν' := ν') b (this ▸ (hv _).2 (isLeft_inlStrand s))
  obtain ⟨⟨a, b⟩, hab⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  have ha : ∀ s, inlStrand ν' ν'' (a s) = v.1 (inlStrand ν' ν'' s) := fun s => by
    have := hσ (.inl s)
    rw [← hab] at this
    simpa using this
  have hb : ∀ s, inrStrand ν' ν'' (b s) = v.1 (inrStrand ν' ν'' s) := fun s => by
    have := hσ (.inr s)
    rw [← hab] at this
    simpa using this
  have ca : ∀ s, (a s).1 = s.1 := fun s => by
    have := v.2 (inlStrand ν' ν'' s)
    rw [← ha] at this
    exact Subtype.ext (congrArg (fun x => (x.1 : I)) this)
  have cb : ∀ s, (b s).1 = s.1 := fun s => by
    have := v.2 (inrStrand ν' ν'' s)
    rw [← hb] at this
    exact Subtype.ext (congrArg (fun x => (x.1 : I)) this)
  refine ⟨(⟨a, ca⟩, ⟨b, cb⟩), Subtype.ext (Equiv.ext fun t => ?_)⟩
  obtain ⟨x | x, rfl⟩ := (strandEquiv ν' ν'').surjective t
  · exact (colPermProd_inl _ x).trans (ha x)
  · exact (colPermProd_inr _ x).trans (hb x)

/-- An element of the left factor on the chamber `C''` of the right factor is its image under the
chamber embedding `C' ↦ C' ∘ C''`. -/
theorem galleryTensorHom_tmul_e_val (x : GalleryAlgebra k Γ ν') (C'' : FullChamber Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (x ⊗ₜ e C'')).1 = ((leftChamberEmb C'').galleryHom x).1 := by
  rw [galleryTensorHom_tmul]
  show (leftHom k Γ ν' ν'' x).1 * (rightHom k Γ ν' ν'' (e C'')).1 = _
  rw [leftHom_mul_rightHom_e, ChamberEmbedding.toHom_apply]

/-- An element of the right factor on the chamber `C'` of the left factor is its image under the
chamber embedding `C'' ↦ C' ∘ C''`. -/
theorem galleryTensorHom_e_tmul_val (C' : FullChamber Γ ν') (y : GalleryAlgebra k Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (e C' ⊗ₜ y)).1 = ((rightChamberEmb C').galleryHom y).1 := by
  rw [galleryTensorHom_tmul]
  show (leftHom k Γ ν' ν'' (e C')).1 * (rightHom k Γ ν' ν'' y).1 = _
  rw [leftHom_e_mul_rightHom, ChamberEmbedding.toHom_apply]

/-- **Juxtaposition of minimal galleries.** For minimal galleries `a₁` from `C'` and `a₂` from
`C''`, the word crossing first the images of the hyperplanes of `a₁`, then those of `a₂`, is a
minimal gallery from `C' ∘ C''` to `(C'.flips a₁) ∘ (C''.flips a₂)`, and its element is the image
of `a₁ ⊗ a₂` under `ι = galleryTensorHom`. -/
theorem galList_map_append_map {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    {a₁ : List (Hyp Γ ν')} {a₂ : List (Hyp Γ ν'')} (h₁ : GoodWord C'.1 a₁)
    (h₂ : GoodWord C''.1 a₂) :
    GoodWord (chamber C' C'').1
        (a₁.map (leftEmb ν' ν'').hyp ++ a₂.map (rightEmb ν' ν'').hyp) ∧
      (chamber C' C'').flips (a₁.map (leftEmb ν' ν'').hyp ++ a₂.map (rightEmb ν' ν'').hyp) =
        chamber (C'.flips a₁) (C''.flips a₂) ∧
      galList k (chamber C' C'') (a₁.map (leftEmb ν' ν'').hyp ++ a₂.map (rightEmb ν' ν'').hyp) =
        (galleryTensorHom k Γ ν' ν'' (galList k C' a₁ ⊗ₜ galList k C'' a₂)).1 := by
  obtain ⟨g₁, f₁⟩ := (leftChamberEmb (Γ := Γ) C'').goodWord_map h₁
  obtain ⟨g₂, f₂⟩ := (rightChamberEmb (Γ := Γ) (C'.flips a₁)).goodWord_map h₂
  change GoodWord (chamber C' C'').1 (a₁.map (leftEmb ν' ν'').hyp) at g₁
  change (chamber C' C'').flips (a₁.map (leftEmb ν' ν'').hyp) = chamber (C'.flips a₁) C'' at f₁
  change GoodWord (chamber (C'.flips a₁) C'').1 (a₂.map (rightEmb ν' ν'').hyp) at g₂
  change (chamber (C'.flips a₁) C'').flips (a₂.map (rightEmb ν' ν'').hyp) =
    chamber (C'.flips a₁) (C''.flips a₂) at f₂
  refine ⟨GoodWord.append_of g₁ (f₁ ▸ g₂) fun x hx hx' => ?_, ?_, ?_⟩
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨z, -, hz⟩ := List.mem_map.1 hx'
    exact leftEmb_hyp_ne_rightEmb_hyp y z hz.symm
  · rw [flips_append, f₁, f₂]
  · have ht : galList k C' a₁ ⊗ₜ[k] galList k C'' a₂ =
        (e (C'.flips a₁) ⊗ₜ[k] galList k C'' a₂) * (galList k C' a₁ ⊗ₜ[k] e C'') := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, e_mul_galList, galList_mul_e]
    rw [galList_append, f₁, ht, galleryTensorHom_mul_val, galleryTensorHom_tmul_e_val,
      galleryTensorHom_e_tmul_val, (rightChamberEmb (C'.flips a₁)).galleryHom_galList h₂,
      (leftChamberEmb C'').galleryHom_galList h₁]
    rfl

end Juxtapose

namespace GalleryAlgebra

open Juxtapose

attribute [local instance] ColPerm.fintype

variable {ν' ν'' : I →₀ ℕ}

theorem isRegular_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {x : R} (h : IsRegular (φ x)) : IsRegular x :=
  ⟨fun a b hab => hφ (h.1 (by simpa only [map_mul] using congrArg φ hab)),
    fun a b hab => hφ (h.2 (by simpa only [map_mul] using congrArg φ hab))⟩

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Regularity of the wall factors passes to a smaller dimension vector along a strand
embedding. -/
theorem isRegular_factor_of_embedding {ν₁ ν : I →₀ ℕ} (j : StrandEmbedding ν₁ ν)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k))) (w : Wall Γ ν₁) :
    IsRegular (w.factor (k := k)) :=
  isRegular_of_ringHom (rename j : PolyRing ν₁ k →ₐ[k] PolyRing ν k).toRingHom
    (rename_injective _ j.injective) (by
      show IsRegular (rename j w.factor)
      rw [← j.factor_wall]
      exact hW _)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Regularity of the loop factors passes to a smaller dimension vector along a strand
embedding. -/
theorem isRegular_loopFactor_of_embedding {ν₁ ν : I →₀ ℕ} (j : StrandEmbedding ν₁ ν)
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b))
    (Q : MvPolynomial (Fin 2) k) (a b : Strand ν₁) (hQ : Γ.loop a.1 = some Q) (hab : a ≠ b)
    (hc : a.1 = b.1) : IsRegular (loopFactor Q a b) :=
  isRegular_of_ringHom (rename j : PolyRing ν₁ k →ₐ[k] PolyRing ν k).toRingHom
    (rename_injective _ j.injective) (by
      show IsRegular (rename j (loopFactor Q a b))
      rw [← j.loopFactor_map]
      exact hL Q (j a) (j b) (by rw [j.loop_eq]; exact hQ) (j.injective.ne hab) (j.fst_eq hc))


variable {P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
    (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜)}
  {P' : FullChamber Γ ν' → FullChamber Γ ν' → (Strand ν' → 𝕜) × (Strand ν' → 𝕜)}
  {P'' : FullChamber Γ ν'' → FullChamber Γ ν'' → (Strand ν'' → 𝕜) × (Strand ν'' → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hP' : ∀ C E, IsChamberSegment C E (P' C E))
  (hP'' : ∀ C E, IsChamberSegment C E (P'' C E))
  (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
  (hW : ∀ w : Wall Γ (ν' + ν''), IsRegular (w.factor (k := k)))
  (hW' : ∀ w : Wall Γ ν', IsRegular (w.factor (k := k)))
  (hW'' : ∀ w : Wall Γ ν'', IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand (ν' + ν'')), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hL' : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν'), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hL'' : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν''), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- The dots of the two sides, as dots of `ν' + ν''`. -/
noncomputable def juxtDots (m' : Strand ν' →₀ ℕ) (m'' : Strand ν'' →₀ ℕ) :
    Strand (ν' + ν'') →₀ ℕ :=
  m'.mapDomain (inlStrand ν' ν'') + m''.mapDomain (inrStrand ν' ν'')

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem rename_monomial_mul_rename_monomial (m' : Strand ν' →₀ ℕ) (m'' : Strand ν'' →₀ ℕ) :
    rename (inlStrand ν' ν'') (monomial m' (1 : k)) * rename (inrStrand ν' ν'') (monomial m'' 1) =
      monomial (juxtDots m' m'') 1 := by
  rw [rename_monomial, rename_monomial, monomial_mul_monomial, mul_one]
  rfl

omit [DecidableEq I] in
theorem juxtDots_eq (m' : Strand ν' →₀ ℕ) (m'' : Strand ν'' →₀ ℕ) :
    juxtDots m' m'' = Finsupp.equivMapDomain (strandEquiv ν' ν'')
      (Finsupp.sumFinsuppEquivProdFinsupp.symm (m', m'')) := by
  have hne : ∀ (x : Strand ν') (y : Strand ν''), inrStrand ν' ν'' y ≠ inlStrand ν' ν'' x :=
    fun x y hy => not_isLeft_inrStrand y (hy ▸ isLeft_inlStrand x)
  have hinr : Function.Injective (inrStrand ν' ν'') :=
    (strandEquiv ν' ν'').injective.comp Sum.inr_injective
  ext t
  obtain ⟨x | x, rfl⟩ := (strandEquiv ν' ν'').surjective t
  · have h0 : Finsupp.mapDomain (inrStrand ν' ν'') m'' (inlStrand ν' ν'' x) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ fun ⟨y, hy⟩ => hne x y hy
    simp only [juxtDots, Finsupp.equivMapDomain_apply,
      Finsupp.sumFinsuppEquivProdFinsupp_symm_inl, Finsupp.add_apply, strandEquiv_inl,
      Finsupp.mapDomain_apply_of_injective (inlStrand_injective ν' ν''), h0,
      strandEquiv_symm_inl, add_zero]
  · have h0 : Finsupp.mapDomain (inlStrand ν' ν'') m' (inrStrand ν' ν'' x) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ fun ⟨y, hy⟩ => hne y x hy.symm
    simp only [juxtDots, Finsupp.equivMapDomain_apply,
      Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, Finsupp.add_apply, strandEquiv_inr,
      Finsupp.mapDomain_apply_of_injective hinr, h0, zero_add,
      strandEquiv_symm_inr]

omit [DecidableEq I] in
/-- The dots of `ν' + ν''` are exactly the juxtapositions of dots of the two sides. -/
theorem juxtDots_bijective :
    Function.Bijective fun p : (Strand ν' →₀ ℕ) × (Strand ν'' →₀ ℕ) => juxtDots p.1 p.2 := by
  have : (fun p : (Strand ν' →₀ ℕ) × (Strand ν'' →₀ ℕ) => juxtDots p.1 p.2) =
      (Finsupp.sumFinsuppEquivProdFinsupp.symm.trans
        (Finsupp.equivCongrLeft (strandEquiv ν' ν'')) :
        (Strand ν' →₀ ℕ) × (Strand ν'' →₀ ℕ) ≃ _) := by
    funext p
    exact juxtDots_eq p.1 p.2
  rw [this]
  exact Equiv.bijective _

include hP hP' hP'' in
/-- **Leading term of a coset element times a juxtaposed basis element.** Let `C' ∘ C''` be
rank-ordered, `D` rank-ordered, `u` a relabelling, `G = shuffleTop X (u⁻¹ • D)` with `X` marking
the strands of `ν'`, and `G'`, `G''` its restrictions to the two blocks. For basis elements
`b'(h', m')` of `e G' * A_{ν'} * e C'` and `b''(h'', m'')` of `e G'' * A_{ν''} * e C''`
(Webster, Theorem 2.8), the product `r u (u⁻¹ • D) c_u * ι(b' ⊗ b'')` is congruent to the basis
element `b(u h, m' ∘ m'')` of `e D * A * e (C' ∘ C'')`, `h = colPermProd (h', h'')`, modulo basis
elements with shorter chosen gallery. -/
theorem cosetElt_mul_galleryTensorHom_sub_cornerBasis_mem {C' : FullChamber Γ ν'}
    {C'' : FullChamber Γ ν''} (hC : (chamber C' C'').IsRankOrdered)
    {D : FullChamber Γ (ν' + ν'')} (hD' : D.IsRankOrdered) (u : ColPerm (ν' + ν''))
    (h' : ColPerm ν') (m' : Strand ν' →₀ ℕ) (h'' : ColPerm ν'') (m'' : Strand ν'' →₀ ℕ) :
    cosetElt k hD hZ ν' u D * (galleryTensorHom k Γ ν' ν''
        ((cornerBasis hP' hD hZ hΓ hW' hL' ((leftEmb ν' ν'').restrict
            (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D))) C' (h', m') :
            GalleryAlgebra k Γ ν') ⊗ₜ
          (cornerBasis hP'' hD hZ hΓ hW'' hL'' ((rightEmb ν' ν'').restrict
            (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D))) C'' (h'', m'') :
            GalleryAlgebra k Γ ν''))).1 -
      (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'')
        (u * colPermProd ν' ν'' (h', h''), juxtDots m' m'') : GalleryAlgebra k Γ (ν' + ν'')) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm (ν' + ν'') × (Strand (ν' + ν'') →₀ ℕ) //
        segLength P (chamber C' C'') (i.1⁻¹ • D) <
          segLength P (chamber C' C'') ((u * colPermProd ν' ν'' (h', h''))⁻¹ • D)} =>
        (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') i.1 :
          GalleryAlgebra k Γ (ν' + ν''))) := by
  set X : Strand (ν' + ν'') → Bool := fun t => decide (t.IsLeft ν')
  set G := shuffleTop X (u⁻¹ • D)
  set G' := (leftEmb ν' ν'').restrict G
  set G'' := (rightEmb ν' ν'').restrict G
  set h := colPermProd ν' ν'' (h', h'')
  have hh : h ∈ leftBlockStab (ν' + ν'') ν' := colPermProd_mem_leftBlockStab (h', h'')
  set A' := h'⁻¹ • G'
  set A'' := h''⁻¹ • G''
  set w₁ := word (hypAff (Γ := Γ)) (P' C' A').1 (P' C' A').2
  set w₂ := word (hypAff (Γ := Γ)) (P'' C'' A'').1 (P'' C'' A'').2
  obtain ⟨hW12, hf12, hg12⟩ := galList_map_append_map (k := k) (goodWord_segWord hP' C' A')
    (goodWord_segWord hP'' C'' A'')
  rw [flips_segWord_eq hP' C' A', flips_segWord_eq hP'' C'' A''] at hf12
  set W := w₁.map (leftEmb ν' ν'').hyp ++ w₂.map (rightEmb ν' ν'').hyp
  have hG : G = chamber G' G'' := eq_chamber_of_isSeparated (isSeparated_sep _ _ _)
  have hA : chamber A' A'' = h⁻¹ • G := by
    rw [hG, ← map_inv, colPermProd_smul_chamber]
    rfl
  set E := (u * h)⁻¹ • D
  have hE : shuffleTop X E = h⁻¹ • G := by
    show shuffleTop X ((u * h)⁻¹ • D) = _
    rw [mul_inv_rev, mul_smul, shuffleTop_smul_of_mem (inv_mem_leftBlockStab hh)]
  have hcos : cosetElt k hD hZ ν' u D * r h (h⁻¹ • G) = cosetElt k hD hZ ν' (u * h) D := by
    rw [cosetElt_eq_mul_r hD hZ (u * h) D hh, mul_inv_cancel_right, hE]
  have hb' : (cornerBasis hP' hD hZ hΓ hW' hL' G' C' (h', m') : GalleryAlgebra k Γ ν') =
      r h' A' * galList k C' w₁ * (poly (monomial m' 1) * e C') := by
    rw [cornerBasis_apply, ← e_mul_poly, ← mul_assoc, mul_assoc (r h' A') _ (e C'),
      galList_mul_e]
    rfl
  have hb'' : (cornerBasis hP'' hD hZ hΓ hW'' hL'' G'' C'' (h'', m'') : GalleryAlgebra k Γ ν'') =
      r h'' A'' * galList k C'' w₂ * (poly (monomial m'' 1) * e C'') := by
    rw [cornerBasis_apply, ← e_mul_poly, ← mul_assoc, mul_assoc (r h'' A'') _ (e C''),
      galList_mul_e]
    rfl
  have ht : (cornerBasis hP' hD hZ hΓ hW' hL' G' C' (h', m') : GalleryAlgebra k Γ ν') ⊗ₜ[k]
      (cornerBasis hP'' hD hZ hΓ hW'' hL'' G'' C'' (h'', m'') : GalleryAlgebra k Γ ν'') =
      (r h' A' ⊗ₜ r h'' A'') * (galList k C' w₁ ⊗ₜ galList k C'' w₂) *
        ((poly (monomial m' 1) * e C') ⊗ₜ e C'') *
        (e C' ⊗ₜ (poly (monomial m'' 1) * e C'')) := by
    rw [hb', hb'', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    · rw [mul_assoc _ (poly _ * e C') (e C'), mul_assoc (poly _) (e C') (e C'), e_mul_e,
        ite_eq_left rfl]
    · rw [mul_assoc (r h'' A'') (galList k C'' w₂) (e C''), galList_mul_e]
  have hpoly : galList k (chamber C' C'') W *
      ((poly (rename (inlStrand ν' ν'') (monomial m' 1)) * e (chamber C' C'')) *
      (poly (rename (inrStrand ν' ν'') (monomial m'' 1)) * e (chamber C' C''))) =
      galList k (chamber C' C'') W * poly (monomial (juxtDots m' m'') 1) := by
    have he : ∀ (C : FullChamber Γ (ν' + ν'')) (a b : PolyRing (ν' + ν'') k),
        (poly a * e C : GalleryAlgebra k Γ (ν' + ν'')) * (poly b * e C) = e C * poly (a * b) := by
      intro C a b
      rw [mul_assoc, ← mul_assoc (e C) (poly b), e_mul_poly, mul_assoc (poly b), e_mul_e,
        ite_eq_left rfl, ← mul_assoc, poly_mul_poly, e_mul_poly]
    rw [he, ← mul_assoc, galList_mul_e, rename_monomial_mul_rename_monomial]
  -- the product as an element along the minimal gallery `W ++ cosetWord E`
  obtain ⟨hc, hfc⟩ := goodWord_cosetWord hD hZ ν' E
  have hCs : IsSeparated X (chamber C' C'') := isSeparated_chamber C' C''
  have hfa : (chamber C' C'').flips W = shuffleTop X E := by rw [hf12, hA, hE]
  have hac : GoodWord (chamber C' C'').1 (W ++ cosetWord hD hZ ν' E) := by
    refine GoodWord.append_of_between hW12 (hfa ▸ hc) fun x hx => ?_
    rw [hfa, hfc] at hx
    rw [hfa]
    exact (shuffleTop_between hCs x hx.symm).trans hx.symm
  have hfac : (chamber C' C'').flips (W ++ cosetWord hD hZ ν' E) = E := by
    rw [flips_append, hfa, hfc]
  have key := r_mul_galList_mul_sub_cornerBasis_mem hP hD hZ hΓ hW hL ν' ν' hC hD'
    (S := Set.univ) isLowerSet_univ (Set.mem_univ _) hac hfac (juxtDots m' m'')
  have hprod : cosetElt k hD hZ ν' u D * (galleryTensorHom k Γ ν' ν''
      ((cornerBasis hP' hD hZ hΓ hW' hL' G' C' (h', m') : GalleryAlgebra k Γ ν') ⊗ₜ
        (cornerBasis hP'' hD hZ hΓ hW'' hL'' G'' C'' (h'', m'') : GalleryAlgebra k Γ ν''))).1 =
      r (u * h) E * galList k (chamber C' C'') (W ++ cosetWord hD hZ ν' E) *
        poly (monomial (juxtDots m' m'') 1) := by
    rw [ht, galleryTensorHom_mul_val, galleryTensorHom_mul_val, galleryTensorHom_mul_val,
      galleryTensorHom_r_tmul_r, ← hg12, ← poly_rename_inl_mul_e, ← poly_rename_inr_mul_e, hA,
      mul_assoc (r h _ * _), mul_assoc (r h _), hpoly, ← mul_assoc, ← mul_assoc, hcos,
      galList_append (chamber C' C'') W (cosetWord hD hZ ν' E), hfa, cosetElt]
    simp only [mul_assoc]
    rfl
  rw [hprod]
  refine Submodule.span_mono ?_ key
  rintro _ ⟨⟨i, -, hi⟩, rfl⟩
  exact ⟨⟨i, hi⟩, rfl⟩

variable (ν') in
/-- The representatives for `D`: relabellings `u` with `shuffleTop X (u⁻¹ • D)` rank-ordered, where
`X` marks the strands of `ν'`. They play the role of the minimal coset representatives of
`S_{ν'} × S_{ν''}`. -/
abbrev ParabolicRep (D : FullChamber Γ (ν' + ν'')) : Type _ :=
  {u : ColPerm (ν' + ν'') //
    (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)).IsRankOrdered}

variable (ν' ν'') in
/-- The index set of the basis of a corner adapted to the parabolic subalgebra: a representative
and basis indices of the two sides. -/
abbrev ParabolicIndex (D : FullChamber Γ (ν' + ν'')) : Type _ :=
  ParabolicRep ν' D × ((ColPerm ν' × (Strand ν' →₀ ℕ)) × (ColPerm ν'' × (Strand ν'' →₀ ℕ)))

/-- The leading index `(u * (h' × h''), m' ∘ m'')` of an index of the parabolic basis. -/
noncomputable def parabolicLead (D : FullChamber Γ (ν' + ν'')) (p : ParabolicIndex ν' ν'' D) :
    ColPerm (ν' + ν'') × (Strand (ν' + ν'') →₀ ℕ) :=
  (p.1.1 * colPermProd ν' ν'' (p.2.1.1, p.2.2.1), juxtDots p.2.1.2 p.2.2.2)

/-- The leading index is a bijection: every relabelling is uniquely `u * (h' × h'')` with `u` a
representative (`existsUnique_rep`), and every monomial is uniquely a juxtaposition. -/
theorem parabolicLead_bijective (D : FullChamber Γ (ν' + ν'')) :
    Function.Bijective (parabolicLead D) := by
  constructor
  · rintro ⟨u₁, ⟨h₁', m₁'⟩, ⟨h₁'', m₁''⟩⟩ ⟨u₂, ⟨h₂', m₂'⟩, ⟨h₂'', m₂''⟩⟩ hp
    obtain ⟨hg, hm⟩ := Prod.mk.inj hp
    have hu : u₁ = u₂ := by
      refine Subtype.ext (eq_of_inv_mul_mem_leftBlockStab u₁.2 u₂.2 ?_)
      have : u₁.1⁻¹ * u₂.1 = colPermProd ν' ν'' (h₁', h₁'') *
          (colPermProd ν' ν'' (h₂', h₂''))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hg, inv_mul_cancel_left]
      rw [this]
      exact (leftBlockStab (ν' + ν'') ν').mul_mem (colPermProd_mem_leftBlockStab _)
        (inv_mem_leftBlockStab (colPermProd_mem_leftBlockStab _))
    subst hu
    have hh := Juxtapose.colPermProd_injective (mul_left_cancel hg)
    have hmm := juxtDots_bijective.1 (a₁ := (m₁', m₁'')) (a₂ := (m₂', m₂'')) hm
    simp only [Prod.mk.injEq] at hh hmm
    obtain ⟨rfl, rfl⟩ := hh
    obtain ⟨rfl, rfl⟩ := hmm
    rfl
  · rintro ⟨g, m⟩
    obtain ⟨u, ⟨hu, hv⟩, -⟩ := existsUnique_rep (k := k) (ν'' := ν'') rfl g D
    obtain ⟨⟨h', h''⟩, hh⟩ := Juxtapose.exists_colPermProd_eq hv
    obtain ⟨⟨m', m''⟩, hm⟩ := juxtDots_bijective.2 m
    refine ⟨(⟨u, hu⟩, (h', m'), (h'', m'')), ?_⟩
    simp only [parabolicLead, hh, mul_inv_cancel_left]
    exact congrArg _ hm

/-- **The parabolic family**: the product `r u (u⁻¹ • D) c_u * ι(b'(h', m') ⊗ b''(h'', m''))` of a
coset element of a representative `u` with the image of a pair of basis elements (Webster,
Theorem 2.8) of the corners `e G' * A_{ν'} * e C'` and `e G'' * A_{ν''} * e C''`, where `G'`, `G''`
are the restrictions of `shuffleTop X (u⁻¹ • D)` to the two blocks. -/
noncomputable def parabolicCornerElt (D : FullChamber Γ (ν' + ν'')) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') (p : ParabolicIndex ν' ν'' D) : GalleryAlgebra k Γ (ν' + ν'') :=
  cosetElt k hD hZ ν' p.1.1 D * (galleryTensorHom k Γ ν' ν''
    ((cornerBasis hP' hD hZ hΓ hW' hL' ((leftEmb ν' ν'').restrict
        (shuffleTop (fun t => decide (t.IsLeft ν')) (p.1.1⁻¹ • D))) C' p.2.1 :
        GalleryAlgebra k Γ ν') ⊗ₜ
      (cornerBasis hP'' hD hZ hΓ hW'' hL'' ((rightEmb ν' ν'').restrict
        (shuffleTop (fun t => decide (t.IsLeft ν')) (p.1.1⁻¹ • D))) C'' p.2.2 :
        GalleryAlgebra k Γ ν''))).1

include hP hP' hP'' hΓ hW hW' hW'' hL hL' hL'' in
/-- The parabolic family is congruent to the corner basis at its leading index, modulo basis
elements with shorter chosen gallery. -/
theorem parabolicCornerElt_sub_mem {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) (p : ParabolicIndex ν' ν'' D) :
    parabolicCornerElt hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' p -
      (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') (parabolicLead D p) :
        GalleryAlgebra k Γ (ν' + ν'')) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm (ν' + ν'') × (Strand (ν' + ν'') →₀ ℕ) //
        segLength P (chamber C' C'') (i.1⁻¹ • D) <
          segLength P (chamber C' C'') ((parabolicLead D p).1⁻¹ • D)} =>
        (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') i.1 : GalleryAlgebra k Γ (ν' + ν''))) :=
  cosetElt_mul_galleryTensorHom_sub_cornerBasis_mem hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL''
    hC hD' p.1.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

include hP hP' hP'' hΓ hW hW' hW'' hL hL' hL'' in
theorem parabolicCornerElt_mem {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) (p : ParabolicIndex ν' ν'' D) :
    parabolicCornerElt hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' p ∈
      cornerSpace k D (chamber C' C'') := by
  have h := parabolicCornerElt_sub_mem hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD' p
  have hle : Submodule.span k (Set.range fun i : {i : ColPerm (ν' + ν'') ×
      (Strand (ν' + ν'') →₀ ℕ) // segLength P (chamber C' C'') (i.1⁻¹ • D) <
        segLength P (chamber C' C'') ((parabolicLead D p).1⁻¹ • D)} =>
      (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') i.1 : GalleryAlgebra k Γ (ν' + ν''))) ≤
      cornerSpace k D (chamber C' C'') :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (cornerBasis hP hD hZ hΓ hW hL D _ i.1).2)
  have := (cornerSpace k D (chamber C' C'')).add_mem (hle h)
    (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') (parabolicLead D p)).2
  rwa [sub_add_cancel] at this

include hP hP' hP'' hΓ hW hW' hW'' hL hL' hL'' in
/-- `parabolicCornerElt_sub_mem` inside the corner. -/
theorem parabolicCornerElt_sub_mem_span {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) (p : ParabolicIndex ν' ν'' D) :
    (⟨parabolicCornerElt hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' p,
        parabolicCornerElt_mem hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD' p⟩ :
        cornerSpace k D (chamber C' C'')) -
      cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') (parabolicLead D p) ∈
      Submodule.span k (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C'') ''
        {i | segLength P (chamber C' C'') (i.1⁻¹ • D) <
          segLength P (chamber C' C'') ((parabolicLead D p).1⁻¹ • D)}) := by
  have h := parabolicCornerElt_sub_mem hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD' p
  exact Module.Basis.mem_span_image_of_coe_mem (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C''))
    (fun i => segLength P (chamber C' C'') (i.1⁻¹ • D) <
      segLength P (chamber C' C'') ((parabolicLead D p).1⁻¹ • D)) h

/-- **The corner basis adapted to the parabolic subalgebra.** For `C' ∘ C''` and `D`
rank-ordered, the products `r u (u⁻¹ • D) c_u * ι(b'(h', m') ⊗ b''(h'', m''))`, for `u` a
representative and `b'`, `b''` the bases of Webster, Theorem 2.8 of the corners
`e G' * A_{ν'} * e C'` and `e G'' * A_{ν''} * e C''`, form a basis of `e D * A * e (C' ∘ C'')`.
They are unitriangular with respect to the basis of Theorem 2.8 for the length of the chosen
gallery (`parabolicCornerElt_sub_mem`), with bijective leading index (`parabolicLead_bijective`).
This is the freeness step in the proof of Webster, Theorem 2.19. -/
noncomputable def parabolicCornerBasis {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) :
    Module.Basis (ParabolicIndex ν' ν'' D) k (cornerSpace k D (chamber C' C'')) :=
  Module.Basis.ofTriangular (cornerBasis hP hD hZ hΓ hW hL D (chamber C' C''))
    (fun i => segLength P (chamber C' C'') (i.1⁻¹ • D))
    (Equiv.ofBijective _ (parabolicLead_bijective D))
    (fun p => ⟨parabolicCornerElt hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' p,
      parabolicCornerElt_mem hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD' p⟩)
    (parabolicCornerElt_sub_mem_span hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD')

theorem parabolicCornerBasis_apply {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) (p : ParabolicIndex ν' ν'' D) :
    (parabolicCornerBasis hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD' p :
      GalleryAlgebra k Γ (ν' + ν'')) =
      parabolicCornerElt hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' p := by
  exact congrArg Subtype.val (Module.Basis.ofTriangular_apply _ _ _ _ _ p)

variable (k) in
/-- The piece `e G' * A_{ν'} * e C' ⊗ e G'' * A_{ν''} * e C''` attached to a representative `u`,
where `G'`, `G''` are the restrictions of `shuffleTop X (u⁻¹ • D)` to the two blocks. -/
abbrev ParabolicPiece (D : FullChamber Γ (ν' + ν'')) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') (u : ParabolicRep ν' D) : Type _ :=
  cornerSpace k ((leftEmb ν' ν'').restrict
      (shuffleTop (fun t => decide (t.IsLeft ν')) (u.1⁻¹ • D))) C' ⊗[k]
    cornerSpace k ((rightEmb ν' ν'').restrict
      (shuffleTop (fun t => decide (t.IsLeft ν')) (u.1⁻¹ • D))) C''

/-- The tensor product of the bases of Webster, Theorem 2.8 of the two corners of a piece. -/
noncomputable def parabolicPieceBasis (D : FullChamber Γ (ν' + ν'')) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') (u : ParabolicRep ν' D) :
    Module.Basis ((ColPerm ν' × (Strand ν' →₀ ℕ)) × (ColPerm ν'' × (Strand ν'' →₀ ℕ))) k
      (ParabolicPiece k D C' C'' u) :=
  (cornerBasis hP' hD hZ hΓ hW' hL' _ C').tensorProduct (cornerBasis hP'' hD hZ hΓ hW'' hL'' _ C'')

open scoped Classical in
/-- **Freeness of a corner over the parabolic subalgebra** (the freeness step in the proof of
Webster, *Weighted KLR algebras*, arXiv:1209.2463v4, Theorem 2.19, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). For `C' ∘ C''` and `D` rank-ordered, the corner
`e D * A_{ν' + ν''} * e (C' ∘ C'')` is the direct sum, over the representatives `u`, of the images
of `e G'_u * A_{ν'} * e C' ⊗ e G''_u * A_{ν''} * e C''` under `x ↦ r u (u⁻¹ • D) c_u * ι(x)`
(`parabolicCornerEquiv_single`), and these maps are injective. -/
noncomputable def parabolicCornerEquiv {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) :
    (∀ u : ParabolicRep ν' D, ParabolicPiece k D C' C'' u) ≃ₗ[k]
      cornerSpace k D (chamber C' C'') :=
  ((Pi.basis (parabolicPieceBasis hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'')).reindex
      (Equiv.sigmaEquivProd _ _)).equiv
    (parabolicCornerBasis hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD') (Equiv.refl _)

open scoped Classical in
theorem parabolicCornerEquiv_single {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {D : FullChamber Γ (ν' + ν'')}
    (hD' : D.IsRankOrdered) (u : ParabolicRep ν' D) (x : ParabolicPiece k D C' C'' u) :
    (parabolicCornerEquiv hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD' (Pi.single u x) :
      GalleryAlgebra k Γ (ν' + ν'')) =
      cosetElt k hD hZ ν' u.1 D * (galleryTensorHom k Γ ν' ν''
        (TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) x)).1 := by
  have key : ((cornerSpace k D (chamber C' C'')).subtype ∘ₗ
      (parabolicCornerEquiv hP hP' hP'' hD hZ hΓ hW hW' hW'' hL hL' hL'' hC hD').toLinearMap ∘ₗ
        LinearMap.single k (ParabolicPiece k D C' C'') u) =
      LinearMap.mulLeft k (cosetElt k hD hZ ν' u.1 D) ∘ₗ
        IsIdempotentElem.cornerVal (R := k) isIdempotentElem_juxtIdem ∘ₗ
          (galleryTensorHom k Γ ν' ν'').toLinearMap ∘ₗ
            TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) := by
    refine (parabolicPieceBasis hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' u).ext fun i => ?_
    have hb : Pi.single u (parabolicPieceBasis hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'' u i) =
        ((Pi.basis (parabolicPieceBasis hP' hP'' hD hZ hΓ hW' hW'' hL' hL'' D C' C'')).reindex
          (Equiv.sigmaEquivProd _ _)) (u, i) := by
      rw [Module.Basis.reindex_apply, Pi.basis_apply]
      rfl
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single,
      LinearEquiv.coe_coe]
    rw [hb, parabolicCornerEquiv, Module.Basis.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply, parabolicCornerBasis_apply, parabolicPieceBasis,
      Module.Basis.tensorProduct_apply']
    rfl
  exact congrArg (fun f => f x) key

end GalleryAlgebra

end Categorification.WeightedKLR
