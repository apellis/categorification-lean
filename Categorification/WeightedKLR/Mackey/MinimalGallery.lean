/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Filtration
import Categorification.WeightedKLR.KLR.SpacedSurjective

/-!
# Basis elements along arbitrary minimal galleries

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). The element `b(g, m)` of the basis of Theorem 2.8 of
`e D * A * e C` is built from one chosen minimal gallery from `C` to `g⁻¹ • D`. Replacing that
gallery by any other minimal gallery `w` (a good word from `C` ending in `g⁻¹ • D`) changes
`b(g, m)` only by basis elements whose chosen gallery is strictly shorter and whose relabelling
has shuffle type in any lower set `S` containing the shuffle type of `g`
(`GalleryAlgebra.r_mul_galList_mul_sub_cornerBasis_mem`). This is the form in which the
factorization of a basis element through the shuffle diagram is used: the factored diagram is
the element along another minimal gallery.

## Main results

* `Module.Basis.mem_span_range_inter`: for a basis of a submodule, the spans of two sets of basis
  vectors meet in the span of their intersection.
* `GalleryAlgebra.e_mul_mul_e_mem_span_cornerBasis`: an element with at most `n` steps, cut down
  to `e D * A * e C`, is a combination of basis elements with at most `n` steps.
* `GalleryAlgebra.r_mul_galList_mul_mem_mackeyFilt`: the element along any minimal gallery lies
  in the step of the filtration of its shuffle type.
* `GalleryAlgebra.r_mul_galList_mul_sub_cornerBasis_mem`: independence of the minimal gallery
  modulo shorter basis elements of the same step.
-/

namespace Module.Basis

variable {R G ι : Type*} [CommRing R] [AddCommGroup G] [Module R G] {N : Submodule R G}

theorem range_subtype_eq_image (b : Module.Basis ι R N) (p : ι → Prop) :
    (Set.range fun i : {i // p i} => (b i : G)) = N.subtype '' (b '' {i | p i}) := by
  ext x
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    exact ⟨b i, ⟨i, hi, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem mem_span_range_iff (b : Module.Basis ι R N) (p : ι → Prop) (y : N) :
    (y : G) ∈ Submodule.span R (Set.range fun i : {i // p i} => (b i : G)) ↔
      ↑(b.repr y).support ⊆ {i | p i} := by
  rw [range_subtype_eq_image, ← Submodule.map_span, ← b.mem_span_image]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [N.injective_subtype hzy] at hz
  · intro h
    exact ⟨y, h, rfl⟩

/-- For a basis of a submodule, an element in the span of the basis vectors indexed by `p` and in
the span of those indexed by `q` is in the span of those indexed by `p ∧ q`. -/
theorem mem_span_range_inter (b : Module.Basis ι R N) {p q : ι → Prop} {z : G}
    (hp : z ∈ Submodule.span R (Set.range fun i : {i // p i} => (b i : G)))
    (hq : z ∈ Submodule.span R (Set.range fun i : {i // q i} => (b i : G))) :
    z ∈ Submodule.span R (Set.range fun i : {i // p i ∧ q i} => (b i : G)) := by
  have hzN : z ∈ N := by
    refine Submodule.span_le.2 ?_ hp
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  lift z to N using hzN
  rw [mem_span_range_iff] at hp hq ⊢
  exact fun i hi => ⟨hp hi, hq hi⟩

end Module.Basis

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- An element with at most `n` steps, cut down to `e D * A * e C`, is a combination of the
basis elements `b(g, m)` whose chosen gallery from `C` to `g⁻¹ • D` has at most `n` steps. -/
theorem e_mul_mul_e_mem_span_cornerBasis (D C : FullChamber Γ ν) {n : ℕ}
    {x : GalleryAlgebra k Γ ν} (hx : x ∈ stepFilt k Γ ν n) :
    e D * x * e C ∈ Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
      segLength P C (i.1⁻¹ • D) ≤ n} =>
        (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  have hx' : x ∈ segSpanBottom P n := segSpan_le_segSpanBottom hP hD hZ n
    (stepFilt_le_segSpan (one_mem_segSpan hP)
      (fun m hm C E E₁ hl => t_mul_segGallery_mem hP hD hZ m hm C E E₁ hl) n hx)
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨C', E, g, f, hl, rfl⟩ := hy
    rw [f.as_sum, ← polyHom_apply, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [show MvPolynomial.monomial m (f.coeff m) = f.coeff m • MvPolynomial.monomial m 1 by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      map_smul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, polyHom_apply]
    refine Submodule.smul_mem _ _ ?_
    have hb := e_mul_basisElt_mul_e (k := k) (P := P) D C C' E g m
    rw [basisElt] at hb
    rw [show segGallery (k := k) P C' E = galList k C' (word (hypAff (Γ := Γ)) (P C' E).1
      (P C' E).2) from rfl]
    simp only [mul_assoc] at hb ⊢
    rw [hb]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      refine Submodule.subset_span ⟨⟨(g, m), by rwa [inv_smul_smul]⟩, ?_⟩
      show (cornerBasis hP hD hZ hΓ hW hL (g • E) C (g, m) : GalleryAlgebra k Γ ν) = _
      rw [cornerBasis_apply, inv_smul_smul, mul_assoc]
      rfl
    · exact Submodule.zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add, add_mul]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hy

/-- The element `r g (g⁻¹ • D) * w * y^m` along a gallery `w` from `C` lies in `e D * A * e C`.
-/
theorem r_mul_galList_mul_mem_cornerSpace (D C : FullChamber Γ ν) (g : ColPerm ν)
    (w : List (Hyp Γ ν)) (m : Strand ν →₀ ℕ) :
    r g (g⁻¹ • D) * galList k C w * poly (monomial m 1) ∈ cornerSpace k D C := by
  rw [mem_cornerSpace_iff]
  simp only [← mul_assoc]
  rw [e_mul_r, ite_eq_left (smul_inv_smul g D).symm, mul_assoc _ (poly _) (e C), ← e_mul_poly,
    ← mul_assoc, mul_assoc (r g _) (galList k C w) (e C), galList_mul_e]

theorem galleryRep_r_mul_galList_mul {D C : FullChamber Γ ν} {g : ColPerm ν}
    {w : List (Hyp Γ ν)} (he : C.flips w = g⁻¹ • D) (m : Strand ν →₀ ℕ) :
    galleryRep k hΓ (r g (g⁻¹ • D) * galList k C w * poly (monomial m 1)) =
      blk k C D (ren g ∘ₗ opList k Γ C w ∘ₗ LinearMap.mulLeft k (monomial m 1)) := by
  rw [map_mul, map_mul, galleryRep_r, galleryRep_galList, he, galleryRep_poly,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, blk_comp_blk, blk_comp_diagOp,
    LinearMap.comp_assoc, smul_inv_smul]

/-- The element along any minimal gallery from `C` to `g⁻¹ • D` lies in the step `S` of the
filtration, for every lower set `S` containing the shuffle type of `g`. -/
theorem r_mul_galList_mul_mem_mackeyFilt (ν' ν₁ : I →₀ ℕ) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) (he : C.flips w = g⁻¹ • D) (m : Strand ν →₀ ℕ) :
    r g (g⁻¹ • D) * galList k C w * poly (monomial m 1) ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S := by
  rw [mem_mackeyFilt_iff hP hD hZ hΓ hW hL ν' ν₁ hC hD' hS
    (r_mul_galList_mul_mem_cornerSpace D C g w m),
    blockOp_of_galleryRep_eq_blk hΓ (galleryRep_r_mul_galList_mul hΓ he m)]
  have h1 := isSupported_opList_isDominated (k := k) hC hw
  rw [he] at h1
  have h0 : IsSupported (LinearMap.mulLeft k (monomial m 1) : PolyRing ν k →ₗ[k] PolyRing ν k)
      {1} := by
    simpa using (IsSupported.id (k := k) (ν := ν)).mulLeft (monomial m 1)
  refine ((h1.comp h0).rename g).mono fun y hy => ?_
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.1 hy
  obtain ⟨x, hx, b, hb, rfl⟩ := Set.mem_mul.1 hz
  rw [Set.mem_singleton_iff.1 hb, mul_one]
  exact hS (fun i => shuffleType_mul_le ν' ν₁ hD' hx i) hg

/-- **Independence of the minimal gallery.** Let `C`, `D` be rank-ordered and `S` a lower set of
shuffle types containing the shuffle type of `g`. For any minimal gallery `w` from `C` to
`g⁻¹ • D` (a good word ending there), the element `r g (g⁻¹ • D) * w * y^m` differs from the
basis element `b(g, m)` by a combination of basis elements `b(g', m')` of shuffle type in `S`
whose chosen gallery is shorter than that of `g`. -/
theorem r_mul_galList_mul_sub_cornerBasis_mem (ν' ν₁ : I →₀ ℕ) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) (he : C.flips w = g⁻¹ • D) (m : Strand ν →₀ ℕ) :
    r g (g⁻¹ • D) * galList k C w * poly (monomial m 1) -
        (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  set E := g⁻¹ • D with hEdef
  set ws := word (hypAff (Γ := Γ)) (P C E).1 (P C E).2 with hwsdef
  have hseg : GoodWord C.1 ws := goodWord_segWord hP C E
  obtain ⟨hlen, hshort, hdiff⟩ := galList_sub_of_flips_eq (k := k) hD hZ hw hseg
    (he.trans (flips_segWord_eq hP C E).symm)
  have hsub : r g E * galList k C w * poly (monomial m 1) -
      (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) =
        r g E * (galList k C w - galList k C ws) * poly (monomial m 1) := by
    rw [cornerBasis_apply, mul_sub, sub_mul]
    rfl
  refine Module.Basis.mem_span_range_inter (cornerBasis hP hD hZ hΓ hW hL D C)
    (p := fun i => shuffleType ν' ν₁ i.1 ∈ S)
    (q := fun i => segLength P C (i.1⁻¹ • D) < segLength P C E) ?_ ?_
  · exact Submodule.sub_mem _ (r_mul_galList_mul_mem_mackeyFilt hP hD hZ hΓ hW hL ν' ν₁ hC hD'
      hS hg hw he m) (Submodule.subset_span ⟨⟨(g, m), hg⟩, rfl⟩)
  · by_cases h2 : w.length < 2
    · rw [hsub, hshort h2, sub_self, mul_zero, zero_mul]
      exact Submodule.zero_mem _
    · have hz : r g E * (galList k C w - galList k C ws) * poly (monomial m 1) ∈
          stepFilt k Γ ν (w.length - 2) := by
        simpa using mul_mem_stepFilt (mul_mem_stepFilt (r_mem_stepFilt g E 0) hdiff)
          (poly_mem_stepFilt (monomial m 1) 0)
      have hcorner : r g E * galList k C w * poly (monomial m 1) -
          (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
            cornerSpace k D C :=
        Submodule.sub_mem _ (r_mul_galList_mul_mem_cornerSpace D C g w m)
          (cornerBasis hP hD hZ hΓ hW hL D C (g, m)).2
      have hmem := e_mul_mul_e_mem_span_cornerBasis hP hD hZ hΓ hW hL D C hz
      rw [← hsub, mem_cornerSpace_iff.1 hcorner] at hmem
      refine Submodule.span_mono ?_ hmem
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      have hl : segLength P C E = w.length := hlen.symm
      exact ⟨⟨i, by omega⟩, rfl⟩

end GalleryAlgebra

end Categorification.WeightedKLR
