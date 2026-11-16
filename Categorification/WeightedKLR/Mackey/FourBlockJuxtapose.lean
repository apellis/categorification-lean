/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockConj

/-!
# Local conjugacy of the juxtapositions in the two layouts

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. The juxtaposition `(x_a x_b)(x_c x_d)` of four diagrams in the
layout `a b c d` and the juxtaposition `(x_a x_c)(x_b x_d)` of the same diagrams in the layout
`a c b d` are locally conjugate along the middle swap, on the families of four-block chambers
`(A B)(C D)` and `(A C)(B D)`.

## Main definitions

* `Juxtapose.fourChamber`, `Juxtapose.fourChamberSwap`: the chambers `(A B)(C D)` and
  `(A C)(B D)` of `(a + b) + (c + d)`.

## Main results

* `Juxtapose.isLocalConj_galleryTensorHom_fourBlock`: the two juxtapositions are locally
  conjugate along `middleSwap a b c d`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra ChamberEmbedding TensorProduct IsIdempotentElem

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

attribute [local instance] ColPerm.fintype

namespace Juxtapose

variable (a b c d : I →₀ ℕ)

/-- The four-block chamber `(A B)(C D)` of `(a + b) + (c + d)`. -/
noncomputable def fourChamber
    (q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d) :
    FullChamber Γ (a + b + (c + d)) :=
  chamber (chamber q.1 q.2.1) (chamber q.2.2.1 q.2.2.2)

/-- The four-block chamber `(A C)(B D)` of `(a + c) + (b + d)`, read in `(a + b) + (c + d)`. -/
noncomputable def fourChamberSwap
    (q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d) :
    FullChamber Γ (a + b + (c + d)) :=
  castChamber (layout_eq a b c d) (chamber (chamber q.1 q.2.2.1) (chamber q.2.1 q.2.2.2))

variable {a b c d}

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem castChamber_injective {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) :
    Function.Injective (castChamber (Γ := Γ) h) := by
  subst h
  exact fun _ _ e => e

omit [DecidableEq I] in
theorem fourChamber_eq_iff
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    {A : FullChamber Γ a} {B : FullChamber Γ b} {C : FullChamber Γ c} {D : FullChamber Γ d} :
    fourChamber a b c d q = chamber (chamber A B) (chamber C D) ↔ q = (A, B, C, D) := by
  obtain ⟨A', B', C', D'⟩ := q
  simp only [fourChamber, chamber_inj, Prod.mk.injEq, and_assoc]

omit [DecidableEq I] in
theorem fourChamberSwap_eq_iff
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    {A : FullChamber Γ a} {B : FullChamber Γ b} {C : FullChamber Γ c} {D : FullChamber Γ d} :
    fourChamberSwap a b c d q =
        castChamber (layout_eq a b c d) (chamber (chamber A C) (chamber B D)) ↔
      q = (A, B, C, D) := by
  obtain ⟨A', B', C', D'⟩ := q
  simp only [fourChamberSwap, (castChamber_injective _).eq_iff, chamber_inj, Prod.mk.injEq]
  tauto

omit [DecidableEq I] in
theorem fourChamber_injective : Function.Injective (fourChamber (Γ := Γ) a b c d) :=
  fun _ _ h => (fourChamber_eq_iff.1 h).symm ▸ rfl

omit [DecidableEq I] in
theorem fourChamberSwap_injective : Function.Injective (fourChamberSwap (Γ := Γ) a b c d) :=
  fun _ _ h => (fourChamberSwap_eq_iff.1 h).symm ▸ rfl

variable (hΓ : Γ.PSymm)

/-- The factor `x_a`: `(x_a ∘ 1) ∘ 1` in both layouts. -/
theorem isLocalConj_leftHom_leftHom (x : GalleryAlgebra k Γ a) :
    IsLocalConj k hΓ (fourChamber a b c d) (fourChamberSwap a b c d) (middleSwap a b c d)
      (castGallery k Γ (layout_eq a b c d)
        (leftHom k Γ (a + c) (b + d) (leftHom k Γ a c x).1).1)
      (leftHom k Γ (a + b) (c + d) (leftHom k Γ a b x).1).1 := by
  have h1 : (leftHom k Γ (a + b) (c + d) (leftHom k Γ a b x).1).1 =
      ∑ u : FullChamber Γ b × FullChamber Γ (c + d),
        ((leftChamberEmb u.1).comp (leftChamberEmb u.2)).toHom x := by
    rw [leftHom_val (ν'' := c + d) (leftHom k Γ a b x).1, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [leftHom_val (ν'' := b) x, map_sum]
    exact Finset.sum_congr rfl fun B _ => by
      rw [toHom_comp, NonUnitalAlgHom.comp_apply]
  have h2 : castGallery k Γ (layout_eq a b c d)
        (leftHom k Γ (a + c) (b + d) (leftHom k Γ a c x).1).1 =
      ∑ u : FullChamber Γ c × FullChamber Γ (b + d),
        ((leftChamberEmb u.1).comp ((leftChamberEmb u.2).comp
          (castEmb (layout_eq a b c d)))).toHom x := by
    rw [leftHom_val (ν'' := b + d) (leftHom k Γ a c x).1, map_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [leftHom_val (ν'' := c) x, map_sum, map_sum]
    exact Finset.sum_congr rfl fun C _ => by
      rw [castGallery_toHom, ← NonUnitalAlgHom.comp_apply, ← toHom_comp]
  rw [h1, h2]
  refine isLocalConj_sum_toHom_of_injective hΓ
    (ι := fun v : FullChamber Γ b × FullChamber Γ c × FullChamber Γ d =>
      (v.1, chamber v.2.1 v.2.2))
    (ι' := fun v => (v.2.1, chamber v.1 v.2.2)) ?_ ?_ (fun v s => ?_) (fun v q A => ?_)
    (fun v A A' _ => ⟨(A', v.1, v.2.1, v.2.2), rfl⟩) (fun u hu q A hq => ?_)
    (fun u hu q A hq => ?_) x
  · rintro ⟨B, C, D⟩ ⟨B', C', D'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · rintro ⟨B, C, D⟩ ⟨B', C', D'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [comp_toFun, castEmb_toFun]
    exact (middleSwap_inl_inl a b c d s).symm
  · simp only [comp_chamber, castEmb_chamber]
    exact fourChamber_eq_iff.trans fourChamberSwap_eq_iff.symm
  · have hq' : chamber (chamber q.1 q.2.1) (chamber q.2.2.1 q.2.2.2) =
        chamber (chamber A u.1) u.2 := hq
    exact hu ⟨(u.1, q.2.2.1, q.2.2.2), Prod.ext rfl (chamber_inj.1 hq').2⟩
  · simp only [comp_chamber, castEmb_chamber] at hq
    have hq' := castChamber_injective _ (show fourChamberSwap a b c d q =
        castChamber (layout_eq a b c d) (chamber (chamber A u.1) u.2) from hq)
    exact hu ⟨(q.2.1, u.1, q.2.2.2), Prod.ext rfl (chamber_inj.1 hq').2⟩

/-- The factor `x_b`: `(1 ∘ x_b) ∘ 1` in the layout `a b c d`, `1 ∘ (x_b ∘ 1)` in `a c b d`. -/
theorem isLocalConj_rightHom_leftHom (y : GalleryAlgebra k Γ b) :
    IsLocalConj k hΓ (fourChamber a b c d) (fourChamberSwap a b c d) (middleSwap a b c d)
      (castGallery k Γ (layout_eq a b c d)
        (rightHom k Γ (a + c) (b + d) (leftHom k Γ b d y).1).1)
      (leftHom k Γ (a + b) (c + d) (rightHom k Γ a b y).1).1 := by
  have h1 : (leftHom k Γ (a + b) (c + d) (rightHom k Γ a b y).1).1 =
      ∑ u : FullChamber Γ a × FullChamber Γ (c + d),
        ((rightChamberEmb u.1).comp (leftChamberEmb u.2)).toHom y := by
    rw [leftHom_val (ν'' := c + d) (rightHom k Γ a b y).1, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [rightHom_val (ν' := a) y, map_sum]
    exact Finset.sum_congr rfl fun A _ => by
      rw [toHom_comp, NonUnitalAlgHom.comp_apply]
  have h2 : castGallery k Γ (layout_eq a b c d)
        (rightHom k Γ (a + c) (b + d) (leftHom k Γ b d y).1).1 =
      ∑ u : FullChamber Γ d × FullChamber Γ (a + c),
        ((leftChamberEmb u.1).comp ((rightChamberEmb u.2).comp
          (castEmb (layout_eq a b c d)))).toHom y := by
    rw [rightHom_val (ν' := a + c) (leftHom k Γ b d y).1, map_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [leftHom_val (ν'' := d) y, map_sum, map_sum]
    exact Finset.sum_congr rfl fun D _ => by
      rw [castGallery_toHom, ← NonUnitalAlgHom.comp_apply, ← toHom_comp]
  rw [h1, h2]
  refine isLocalConj_sum_toHom_of_injective hΓ
    (ι := fun v : FullChamber Γ a × FullChamber Γ c × FullChamber Γ d =>
      (v.1, chamber v.2.1 v.2.2))
    (ι' := fun v => (v.2.2, chamber v.1 v.2.1)) ?_ ?_ (fun v s => ?_) (fun v q B => ?_)
    (fun v B B' _ => ⟨(v.1, B', v.2.1, v.2.2), rfl⟩) (fun u hu q B hq => ?_)
    (fun u hu q B hq => ?_) y
  · rintro ⟨A, C, D⟩ ⟨A', C', D'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · rintro ⟨A, C, D⟩ ⟨A', C', D'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [comp_toFun, castEmb_toFun]
    exact (middleSwap_inl_inr a b c d s).symm
  · simp only [comp_chamber, castEmb_chamber]
    exact fourChamber_eq_iff.trans fourChamberSwap_eq_iff.symm
  · have hq' : chamber (chamber q.1 q.2.1) (chamber q.2.2.1 q.2.2.2) =
        chamber (chamber u.1 B) u.2 := hq
    exact hu ⟨(u.1, q.2.2.1, q.2.2.2), Prod.ext rfl (chamber_inj.1 hq').2⟩
  · simp only [comp_chamber, castEmb_chamber] at hq
    have hq' := castChamber_injective _ (show fourChamberSwap a b c d q =
        castChamber (layout_eq a b c d) (chamber u.2 (chamber B u.1)) from hq)
    exact hu ⟨(q.1, q.2.2.1, u.1), Prod.ext rfl (chamber_inj.1 hq').1⟩

/-- The factor `x_c`: `1 ∘ (x_c ∘ 1)` in the layout `a b c d`, `(1 ∘ x_c) ∘ 1` in `a c b d`. -/
theorem isLocalConj_leftHom_rightHom (y : GalleryAlgebra k Γ c) :
    IsLocalConj k hΓ (fourChamber a b c d) (fourChamberSwap a b c d) (middleSwap a b c d)
      (castGallery k Γ (layout_eq a b c d)
        (leftHom k Γ (a + c) (b + d) (rightHom k Γ a c y).1).1)
      (rightHom k Γ (a + b) (c + d) (leftHom k Γ c d y).1).1 := by
  have h1 : (rightHom k Γ (a + b) (c + d) (leftHom k Γ c d y).1).1 =
      ∑ u : FullChamber Γ d × FullChamber Γ (a + b),
        ((leftChamberEmb u.1).comp (rightChamberEmb u.2)).toHom y := by
    rw [rightHom_val (ν' := a + b) (leftHom k Γ c d y).1, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [leftHom_val (ν'' := d) y, map_sum]
    exact Finset.sum_congr rfl fun D _ => by
      rw [toHom_comp, NonUnitalAlgHom.comp_apply]
  have h2 : castGallery k Γ (layout_eq a b c d)
        (leftHom k Γ (a + c) (b + d) (rightHom k Γ a c y).1).1 =
      ∑ u : FullChamber Γ a × FullChamber Γ (b + d),
        ((rightChamberEmb u.1).comp ((leftChamberEmb u.2).comp
          (castEmb (layout_eq a b c d)))).toHom y := by
    rw [leftHom_val (ν'' := b + d) (rightHom k Γ a c y).1, map_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [rightHom_val (ν' := a) y, map_sum, map_sum]
    exact Finset.sum_congr rfl fun A _ => by
      rw [castGallery_toHom, ← NonUnitalAlgHom.comp_apply, ← toHom_comp]
  rw [h1, h2]
  refine isLocalConj_sum_toHom_of_injective hΓ
    (ι := fun v : FullChamber Γ a × FullChamber Γ b × FullChamber Γ d =>
      (v.2.2, chamber v.1 v.2.1))
    (ι' := fun v => (v.1, chamber v.2.1 v.2.2)) ?_ ?_ (fun v s => ?_) (fun v q C => ?_)
    (fun v C C' _ => ⟨(v.1, v.2.1, C', v.2.2), rfl⟩) (fun u hu q C hq => ?_)
    (fun u hu q C hq => ?_) y
  · rintro ⟨A, B, D⟩ ⟨A', B', D'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · rintro ⟨A, B, D⟩ ⟨A', B', D'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [comp_toFun, castEmb_toFun]
    exact (middleSwap_inr_inl a b c d s).symm
  · simp only [comp_chamber, castEmb_chamber]
    exact fourChamber_eq_iff.trans fourChamberSwap_eq_iff.symm
  · have hq' : chamber (chamber q.1 q.2.1) (chamber q.2.2.1 q.2.2.2) =
        chamber u.2 (chamber C u.1) := hq
    exact hu ⟨(q.1, q.2.1, u.1), Prod.ext rfl (chamber_inj.1 hq').1⟩
  · simp only [comp_chamber, castEmb_chamber] at hq
    have hq' := castChamber_injective _ (show fourChamberSwap a b c d q =
        castChamber (layout_eq a b c d) (chamber (chamber u.1 C) u.2) from hq)
    exact hu ⟨(u.1, q.2.1, q.2.2.2), Prod.ext rfl (chamber_inj.1 hq').2⟩

/-- The factor `x_d`: `1 ∘ (1 ∘ x_d)` in both layouts. -/
theorem isLocalConj_rightHom_rightHom (y : GalleryAlgebra k Γ d) :
    IsLocalConj k hΓ (fourChamber a b c d) (fourChamberSwap a b c d) (middleSwap a b c d)
      (castGallery k Γ (layout_eq a b c d)
        (rightHom k Γ (a + c) (b + d) (rightHom k Γ b d y).1).1)
      (rightHom k Γ (a + b) (c + d) (rightHom k Γ c d y).1).1 := by
  have h1 : (rightHom k Γ (a + b) (c + d) (rightHom k Γ c d y).1).1 =
      ∑ u : FullChamber Γ c × FullChamber Γ (a + b),
        ((rightChamberEmb u.1).comp (rightChamberEmb u.2)).toHom y := by
    rw [rightHom_val (ν' := a + b) (rightHom k Γ c d y).1, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [rightHom_val (ν' := c) y, map_sum]
    exact Finset.sum_congr rfl fun C _ => by
      rw [toHom_comp, NonUnitalAlgHom.comp_apply]
  have h2 : castGallery k Γ (layout_eq a b c d)
        (rightHom k Γ (a + c) (b + d) (rightHom k Γ b d y).1).1 =
      ∑ u : FullChamber Γ b × FullChamber Γ (a + c),
        ((rightChamberEmb u.1).comp ((rightChamberEmb u.2).comp
          (castEmb (layout_eq a b c d)))).toHom y := by
    rw [rightHom_val (ν' := a + c) (rightHom k Γ b d y).1, map_sum, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [rightHom_val (ν' := b) y, map_sum, map_sum]
    exact Finset.sum_congr rfl fun B _ => by
      rw [castGallery_toHom, ← NonUnitalAlgHom.comp_apply, ← toHom_comp]
  rw [h1, h2]
  refine isLocalConj_sum_toHom_of_injective hΓ
    (ι := fun v : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c =>
      (v.2.2, chamber v.1 v.2.1))
    (ι' := fun v => (v.2.1, chamber v.1 v.2.2)) ?_ ?_ (fun v s => ?_) (fun v q D => ?_)
    (fun v D D' _ => ⟨(v.1, v.2.1, v.2.2, D'), rfl⟩) (fun u hu q D hq => ?_)
    (fun u hu q D hq => ?_) y
  · rintro ⟨A, B, C⟩ ⟨A', B', C'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · rintro ⟨A, B, C⟩ ⟨A', B', C'⟩ h
    simp only [Prod.mk.injEq, chamber_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only [comp_toFun, castEmb_toFun]
    exact (middleSwap_inr_inr a b c d s).symm
  · simp only [comp_chamber, castEmb_chamber]
    exact fourChamber_eq_iff.trans fourChamberSwap_eq_iff.symm
  · have hq' : chamber (chamber q.1 q.2.1) (chamber q.2.2.1 q.2.2.2) =
        chamber u.2 (chamber u.1 D) := hq
    obtain ⟨h₁, h₂⟩ := chamber_inj.1 hq'
    exact hu ⟨(q.1, q.2.1, q.2.2.1), Prod.ext (chamber_inj.1 h₂).1 h₁⟩
  · simp only [comp_chamber, castEmb_chamber] at hq
    have hq' := castChamber_injective _ (show fourChamberSwap a b c d q =
        castChamber (layout_eq a b c d) (chamber u.2 (chamber u.1 D)) from hq)
    obtain ⟨h₁, h₂⟩ := chamber_inj.1 hq'
    exact hu ⟨(q.1, q.2.1, q.2.2.1), Prod.ext (chamber_inj.1 h₂).1 h₁⟩

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem mul_mul_mul_swap_middle {R : Type*} [Semigroup R] {x y z w : R} (h : y * z = z * y) :
    x * y * (z * w) = x * z * (y * w) := by
  rw [mul_assoc, ← mul_assoc y, h, mul_assoc, ← mul_assoc]

/-- **The juxtapositions in the two layouts are locally conjugate.** The juxtaposition
`(x_a x_b)(x_c x_d)` in the layout `a b c d` and the juxtaposition `(x_a x_c)(x_b x_d)` in the
layout `a c b d`, read in `(a + b) + (c + d)`, are locally conjugate along the middle swap on the
four-block chambers `(A B)(C D)` and `(A C)(B D)`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem isLocalConj_galleryTensorHom_fourBlock (xa : GalleryAlgebra k Γ a)
    (xb : GalleryAlgebra k Γ b) (xc : GalleryAlgebra k Γ c) (xd : GalleryAlgebra k Γ d) :
    IsLocalConj k hΓ (fourChamber a b c d) (fourChamberSwap a b c d) (middleSwap a b c d)
      (castGallery k Γ (layout_eq a b c d) (galleryTensorHom k Γ (a + c) (b + d)
        ((galleryTensorHom k Γ a c (xa ⊗ₜ xc)).1 ⊗ₜ
          (galleryTensorHom k Γ b d (xb ⊗ₜ xd)).1)).1)
      (galleryTensorHom k Γ (a + b) (c + d)
        ((galleryTensorHom k Γ a b (xa ⊗ₜ xb)).1 ⊗ₜ
          (galleryTensorHom k Γ c d (xc ⊗ₜ xd)).1)).1 := by
  have hcomm : (leftHom k Γ (a + c) (b + d) (rightHom k Γ a c xc).1).1 *
      (rightHom k Γ (a + c) (b + d) (leftHom k Γ b d xb).1).1 =
      (rightHom k Γ (a + c) (b + d) (leftHom k Γ b d xb).1).1 *
        (leftHom k Γ (a + c) (b + d) (rightHom k Γ a c xc).1).1 := by
    rw [← corner_val_mul, ← corner_val_mul, (commute_leftHom_rightHom _ _).eq]
  simp only [galleryTensorHom_tmul, corner_val_mul, map_mul]
  rw [mul_mul_mul_swap_middle (by rw [← map_mul, ← map_mul, hcomm])]
  exact ((isLocalConj_leftHom_leftHom hΓ xa).mul fourChamber_injective
      fourChamberSwap_injective (isLocalConj_rightHom_leftHom hΓ xb)).mul fourChamber_injective
    fourChamberSwap_injective ((isLocalConj_leftHom_rightHom hΓ xc).mul fourChamber_injective
      fourChamberSwap_injective (isLocalConj_rightHom_rightHom hΓ xd))

end Juxtapose

end Categorification.WeightedKLR
