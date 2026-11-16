/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Independence
import Categorification.WeightedKLR.GallerySpan.Spanning
import Categorification.WeightedKLR.Steadied
import Categorification.WeightedKLR.Mackey.Dominance

/-!
# Shuffle types and triangularity of the gallery basis

The Mackey filtration of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, §2.4 (proof of Theorem 2.19, which follows Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18) is indexed by shuffle types. Split the strands of colour
`i` at the bottom into the first `ν' i` and the rest, and at the top into the first `ν₁ i` and
the rest. The *shuffle type* of a relabelling `y` at `i` is the number of strands of colour `i`
from the second part at the bottom that `y` sends to the first part at the top
(`shuffleType ν' ν₁ y i`).

The basis element `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)` of Theorem 2.8 between
rank-ordered full chambers `C`, `D` acts in the polynomial representation by an operator whose
relabellings all have shuffle type at most that of `g`, colour by colour
(`isSupported_basisOp_shuffleLE`). This is the triangularity of the gallery basis with respect
to shuffle types; it holds over every commutative ring and needs no hypothesis on the weighted
graph. It is the dominance of the relabellings of a gallery
(`isSupported_opList_isDominated`) for the set of strands ending in the first part at the top
and the set of strands starting in the second part at the bottom.

## Main definitions

* `shuffleType ν' ν₁ y i`: the shuffle type of the relabelling `y` at the colour `i`.
* `ShuffleLE ν' ν₁ y g`: the shuffle type of `y` is at most that of `g` at every colour.

## Main results

* `shuffleType_mul_le`: a relabelling `x` dominated by `g⁻¹ • D`, for `D` rank-ordered, has
  `shuffleType (g * x) ≤ shuffleType g`.
* `GalleryAlgebra.isSupported_basisOp_shuffleLE`: triangularity of the gallery basis.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-! ### Strand order under relabelling and in rank-ordered chambers -/

namespace FullChamber

omit [DecidableEq I] in
theorem colPerm_apply_fst (g : ColPerm ν) (s : Strand ν) : (g.1 s).1 = s.1 :=
  (g.2 : ∀ s, (g.1 s).1 = s.1) s

omit [DecidableEq I] in
/-- Relabelling a chamber relabels the order of its strands. -/
theorem strandLt_smul (g : ColPerm ν) (B : FullChamber Γ ν) (s t : Strand ν) :
    (g • B).StrandLt (g.1 s) (g.1 t) ↔ B.StrandLt s t := by
  obtain ⟨p, hp, hs⟩ := B.2
  have hs' : fullSigns (act g p) = (g • B).1 := by
    rw [fullSigns_act hp, hs]
    rfl
  have hc : (g.1 s).1 = (g.1 t).1 ↔ s.1 = t.1 := by rw [colPerm_apply_fst, colPerm_apply_fst]
  have ha : ∀ u, act g p (g.1 u) = p u := fun u => by simp [act]
  constructor
  · intro H
    rw [strandLt_iff hp hs (hc.1 H.1), ← ha s, ← ha t]
    exact (strandLt_iff (hp.act g) hs' H.1).1 H
  · intro H
    rw [strandLt_iff (hp.act g) hs' (hc.2 H.1), ha, ha]
    exact (strandLt_iff hp hs H.1).1 H

omit [DecidableEq I] in
/-- In a rank-ordered chamber the strands of one colour are ordered by rank. -/
theorem strandLt_iff_of_isRankOrdered {B : FullChamber Γ ν} (hB : B.IsRankOrdered)
    {s t : Strand ν} : B.StrandLt s t ↔ s.1 = t.1 ∧ s.2.val < t.2.val := by
  constructor
  · intro H
    refine ⟨H.1, ?_⟩
    rcases lt_trichotomy s.2.val t.2.val with h | h | h
    · exact h
    · exact absurd (Strand.ext_of H.1 h ▸ H) (StrandLt.irrefl B t)
    · exact absurd ((strandLt_fst_snd B ⟨(t, s), H.1.symm, h⟩).2 (hB _)) H.asymm
  · rintro ⟨hc, h⟩
    exact (strandLt_fst_snd B ⟨(s, t), hc, h⟩).2 (hB _)

theorem IsLeftClosed.smul {B : FullChamber Γ ν} {L : Finset (Strand ν)} (hL : B.IsLeftClosed L)
    (g : ColPerm ν) : (g • B).IsLeftClosed (L.image g.1) := by
  intro s t hst ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
  have e : g.1 (g.1⁻¹ s) = s := g.1.apply_symm_apply s
  rw [← e] at hst ⊢
  exact Finset.mem_image_of_mem _ (hL _ _ ((strandLt_smul g B _ _).1 hst) ht')

end FullChamber

/-! ### Shuffle types -/

/-- The shuffle type of the relabelling `y` at the colour `i`: the number of strands of colour
`i` and rank at least `ν' i` that `y` sends to strands of rank less than `ν₁ i`. -/
def shuffleType (ν' ν₁ : I →₀ ℕ) (y : ColPerm ν) (i : I) : ℕ :=
  (Finset.univ.filter fun t : Strand ν => t.1.1 = i ∧ ¬ t.IsLeft ν' ∧ (y.1 t).IsLeft ν₁).card

/-- The shuffle type of `y` is at most that of `g` at every colour. -/
def ShuffleLE (ν' ν₁ : I →₀ ℕ) (y g : ColPerm ν) : Prop :=
  ∀ i, shuffleType ν' ν₁ y i ≤ shuffleType ν' ν₁ g i

section Sets

variable (ν' ν₁ : I →₀ ℕ)

/-- The strands of colour `i` from the second part at the bottom. -/
def rightStrands (i : I) : Finset (Strand ν) :=
  Finset.univ.filter fun t : Strand ν => t.1.1 = i ∧ ¬ t.IsLeft ν'

/-- The strands from the first part at the top. -/
def leftStrands : Finset (Strand ν) := Finset.univ.filter fun t : Strand ν => t.IsLeft ν₁

theorem isRankUpper_rightStrands (i : I) : IsRankUpper (rightStrands (ν := ν) ν' i) := by
  intro s t hc hlt hs
  simp only [rightStrands, Finset.mem_filter, Finset.mem_univ, true_and, Strand.IsLeft,
    not_lt] at hs ⊢
  have e : (s.1 : I) = t.1 := congrArg Subtype.val hc
  have h1 : ν' s.1 = ν' t.1 := congrArg ν' e
  exact ⟨e.symm.trans hs.1, h1.symm.le.trans (hs.2.trans hlt.le)⟩

omit [DecidableEq I] in
theorem isLeftClosed_leftStrands {B : FullChamber Γ ν} (hB : B.IsRankOrdered) :
    B.IsLeftClosed (leftStrands (ν := ν) ν₁) := by
  intro s t hst ht
  rw [strandLt_iff_of_isRankOrdered hB] at hst
  rw [leftStrands, Finset.mem_filter] at ht ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have ht' := ht.2
  unfold Strand.IsLeft at ht' ⊢
  have h1 : ν₁ s.1 = ν₁ t.1 := congrArg (fun c : ν.support => ν₁ c) hst.1
  exact (hst.2.trans ht').trans_eq h1.symm

theorem shuffleType_eq_card (y : ColPerm ν) (i : I) :
    shuffleType ν' ν₁ y i = (leftStrands ν₁ ∩ (rightStrands ν' i).image y.1).card := by
  rw [shuffleType, ← Finset.card_image_of_injective _ y.1.injective]
  congr 1
  ext s
  simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    leftStrands, rightStrands]
  constructor
  · rintro ⟨t, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨h3, t, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨h3, t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, ⟨h1, h2, h3⟩, rfl⟩

end Sets

theorem card_inter_image_colPerm (g : ColPerm ν) (A B : Finset (Strand ν)) :
    (A ∩ B.image g.1).card = (A.image (g⁻¹).1 ∩ B).card := by
  rw [← Finset.card_image_of_injective _ (g⁻¹).1.injective,
    Finset.image_inter _ _ (g⁻¹).1.injective, Finset.image_image]
  congr 2
  convert Finset.image_id (s := B)
  funext t
  exact g.1.symm_apply_apply t

/-- **Shuffle types along dominated relabellings.** If `D` is rank-ordered and `x` is dominated
by `g⁻¹ • D`, then `g * x` has shuffle type at most that of `g` at every colour. -/
theorem shuffleType_mul_le (ν' ν₁ : I →₀ ℕ) {D : FullChamber Γ ν} (hD : D.IsRankOrdered)
    {g x : ColPerm ν} (hx : IsDominated (g⁻¹ • D) x) : ShuffleLE ν' ν₁ (g * x) g := by
  intro i
  rw [shuffleType_eq_card, shuffleType_eq_card]
  have hL := (isLeftClosed_leftStrands ν₁ hD).smul g⁻¹
  have h := hx _ _ hL (isRankUpper_rightStrands ν' i)
  have e : (rightStrands ν' i).image (g * x).1 =
      ((rightStrands ν' i).image x.1).image g.1 := by
    rw [Finset.image_image]
    rfl
  rw [e, card_inter_image_colPerm g, card_inter_image_colPerm g]
  exact h

/-! ### Triangularity of the gallery basis -/

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}

variable (k) in
/-- The operator by which the basis element `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * y^m`
acts in the polynomial representation, from the copy of `C` to the copy of `D`. -/
noncomputable def basisOp
    (P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜))
    (C D : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    PolyRing ν k →ₗ[k] PolyRing ν k :=
  ren g ∘ₗ opList k Γ C (word (hypAff (Γ := Γ)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2) ∘ₗ
    LinearMap.mulLeft k (monomial m 1)

theorem galleryRep_basisElt_eq_blk (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
    (C D : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    galleryRep k hΓ (basisElt k P C (g⁻¹ • D) g m) = blk k C D (basisOp k P C D g m) := by
  rw [galleryRep_basisElt hP, smul_inv_smul]
  rfl

/-- **Triangularity of the gallery basis with respect to shuffle types.** For rank-ordered
full chambers `C`, `D`, the basis element of Theorem 2.8 indexed by the relabelling `g` and the
monomial `y^m` acts from `C` to `D` by an operator all of whose relabellings have shuffle type
at most that of `g`. -/
theorem isSupported_basisOp_shuffleLE (hP : ∀ C E, IsChamberSegment C E (P C E))
    (ν' ν₁ : I →₀ ℕ) {C D : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD : D.IsRankOrdered) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    IsSupported (basisOp k P C D g m) {y | ShuffleLE ν' ν₁ y g} := by
  have h1 := isSupported_opList_isDominated (k := k) hC (goodWord_segWord hP C (g⁻¹ • D))
  rw [flips_segWord_eq hP] at h1
  have h0 : IsSupported (LinearMap.mulLeft k (monomial m 1) : PolyRing ν k →ₗ[k] PolyRing ν k)
      {1} := by
    simpa using (IsSupported.id (k := k) (ν := ν)).mulLeft (monomial m 1)
  have h2 := (h1.comp h0).rename g
  refine h2.mono fun y hy => ?_
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.1 hy
  obtain ⟨x, hx, b, hb, rfl⟩ := Set.mem_mul.1 hz
  rw [Set.mem_singleton_iff.1 hb, mul_one]
  exact shuffleType_mul_le ν' ν₁ hD hx

end GalleryAlgebra

end Categorification.WeightedKLR
