/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.TensorMap
import Categorification.WeightedKLR.Induction.Associativity

/-!
# Associativity and unit of the juxtaposition map

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Proposition
2.18 (monoidality of induction), at the level of algebras. The monoidal structure on
`⊕_ν W^ϑ_ν`-modules given by induction rests on the associativity and unit of Webster's map
`ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}` placing two diagrams side by side. This file proves
them, after the identifications `(ν₁ + ν₂) + ν₃ = ν₁ + (ν₂ + ν₃)`, `ν + 0 = ν` and `0 + ν = ν`.

The proof works with chamber embeddings: they compose (`ChamberEmbedding.comp`), the algebra map
of a composite is the composite of the algebra maps (`ChamberEmbedding.toHom_comp`), and a chamber
embedding is determined by its maps of strands and of chambers (`ChamberEmbedding.ext_of`). Each
side of the associativity law is then a sum of the algebra maps of chamber embeddings, which agree
term by term by `castChamber_chamber_assoc`.

## Main definitions and results

* `ChamberEmbedding.toHom`, `ChamberEmbedding.comp`, `ChamberEmbedding.toHom_comp`.
* `castGallery`, `castW`: the gallery and weighted KLR algebras along an equality of dimension
  vectors.
* `Juxtapose.galleryTensorHom_assoc`, `Juxtapose.inductionMap_assoc`: associativity of
  juxtaposition.
* `Juxtapose.inductionMap_tmul_one`, `Juxtapose.inductionMap_one_tmul`: the unit `1 ∈ W_0` is a
  unit for juxtaposition.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv GalleryAlgebra IsIdempotentElem

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

/-! ### Non-unital algebra maps out of the gallery algebra -/

/-- A non-unital algebra map out of the gallery algebra is determined by its values on the
generators `e C`, `poly f`, `t C D` and `r g C`. -/
theorem GalleryAlgebra.nonUnitalAlgHom_ext {ν : I →₀ ℕ} {B : Type*} [Ring B] [Algebra k B]
    {f g : GalleryAlgebra k Γ ν →ₙₐ[k] B} (he : ∀ C, f (e C) = g (e C))
    (hp : ∀ p, f (poly p) = g (poly p)) (ht : ∀ C D, f (t C D) = g (t C D))
    (hr : ∀ σ C, f (r σ C) = g (r σ C)) : f = g := by
  have h1 : f 1 = g 1 := by
    rw [← sum_e, map_sum, map_sum]
    exact Finset.sum_congr rfl fun C _ => he C
  ext x
  obtain ⟨y, rfl⟩ := mk_surjective x
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1]
  | grade1 a =>
    cases a with
    | idem C => exact he C
    | poly p => exact hp p
    | step C D => exact ht C D
    | relabel σ C => exact hr σ C
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-! ### Composition of chamber embeddings -/

namespace StrandEmbedding

variable {ν₁ ν₂ ν : I →₀ ℕ}

/-- The composite of two strand embeddings. -/
def comp (j : StrandEmbedding ν₁ ν₂) (j' : StrandEmbedding ν₂ ν) : StrandEmbedding ν₁ ν where
  toFun := j' ∘ j
  injective := j'.injective.comp j.injective
  colour s := (j'.colour (j s)).trans (j.colour s)
  rank_lt s t h hlt := j'.rank_lt _ _ (j.fst_eq h) (j.rank_lt s t h hlt)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hyp_comp (j : StrandEmbedding ν₁ ν₂) (j' : StrandEmbedding ν₂ ν) (h : Hyp Γ ν₁) :
    (j.comp j').hyp h = j'.hyp (j.hyp h) := by
  rcases h with _ | _ <;> rfl

end StrandEmbedding

namespace ChamberEmbedding

variable {ν₁ ν₂ ν : I →₀ ℕ}

/-- The algebra map of a chamber embedding, with values in the gallery algebra of `ν`. -/
noncomputable def toHom (J : ChamberEmbedding Γ ν₁ ν) :
    GalleryAlgebra k Γ ν₁ →ₙₐ[k] GalleryAlgebra k Γ ν where
  toFun x := (J.galleryHom x).1
  map_smul' c x := by rw [map_smul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl
  map_mul' x y := by rw [map_mul]; rfl

theorem toHom_apply (J : ChamberEmbedding Γ ν₁ ν) (x : GalleryAlgebra k Γ ν₁) :
    J.toHom x = (J.galleryHom x).1 := rfl

/-- The composite of two chamber embeddings. -/
def comp (J : ChamberEmbedding Γ ν₁ ν₂) (J' : ChamberEmbedding Γ ν₂ ν) :
    ChamberEmbedding Γ ν₁ ν where
  toStrandEmbedding := J.toStrandEmbedding.comp J'.toStrandEmbedding
  chamber := J'.chamber ∘ J.chamber
  chamber_hyp C h := by
    show (J'.chamber (J.chamber C)).1 _ = _
    rw [StrandEmbedding.hyp_comp, J'.chamber_hyp, J.chamber_hyp]
  chamber_of_not_mem C D h hn := by
    show (J'.chamber (J.chamber C)).1 h = (J'.chamber (J.chamber D)).1 h
    by_cases hr : h ∈ Set.range (J'.hyp (Γ := Γ))
    · obtain ⟨h', rfl⟩ := hr
      rw [J'.chamber_hyp, J'.chamber_hyp]
      refine J.chamber_of_not_mem C D h' fun ⟨h'', he⟩ => hn ⟨h'', ?_⟩
      rw [StrandEmbedding.hyp_comp, he]
    · exact J'.chamber_of_not_mem _ _ h hr
  perm := J'.perm.comp J.perm
  perm_apply g s := by
    show (J'.perm (J.perm g)).1 (J'.toFun (J.toFun s)) = J'.toFun (J.toFun (g.1 s))
    rw [J'.perm_apply, J.perm_apply]
  perm_apply_of_not_mem g t ht := by
    show (J'.perm (J.perm g)).1 t = t
    by_cases hr : t ∈ Set.range J'.toFun
    · obtain ⟨u, rfl⟩ := hr
      rw [J'.perm_apply, J.perm_apply_of_not_mem g u fun ⟨s, hs⟩ => ht ⟨s, by
        show J'.toFun (J.toFun s) = _
        rw [hs]⟩]
    · exact J'.perm_apply_of_not_mem _ t hr
  smul_chamber g C := by
    show J'.perm (J.perm g) • J'.chamber (J.chamber C) = J'.chamber (J.chamber (g • C))
    rw [J'.smul_chamber, J.smul_chamber]

@[simp] theorem comp_toFun (J : ChamberEmbedding Γ ν₁ ν₂) (J' : ChamberEmbedding Γ ν₂ ν)
    (s : Strand ν₁) : (J.comp J').toFun s = J'.toFun (J.toFun s) := rfl

@[simp] theorem comp_chamber (J : ChamberEmbedding Γ ν₁ ν₂) (J' : ChamberEmbedding Γ ν₂ ν)
    (C : FullChamber Γ ν₁) : (J.comp J').chamber C = J'.chamber (J.chamber C) := rfl

/-- The algebra map of a composite is the composite of the algebra maps. -/
theorem toHom_comp (J : ChamberEmbedding Γ ν₁ ν₂) (J' : ChamberEmbedding Γ ν₂ ν) :
    (J.comp J').toHom (k := k) = J'.toHom.comp J.toHom := by
  refine nonUnitalAlgHom_ext (fun C => ?_) (fun p => ?_) (fun C D => ?_) (fun σ C => ?_)
  · simp only [NonUnitalAlgHom.comp_apply, toHom_apply, galleryHom_e]
    rfl
  · simp only [NonUnitalAlgHom.comp_apply, toHom_apply, galleryHom_poly]
    rw [← toHom_apply, map_mul, toHom_apply, toHom_apply, galleryHom_poly, rename_rename]
    have hJ : J'.toHom (k := k) J.idem = (J.comp J').idem := by
      rw [idem, map_sum]
      exact Finset.sum_congr rfl fun C _ => by rw [toHom_apply, galleryHom_e]; rfl
    show poly (rename (J'.toFun ∘ J.toFun) p) * (J.comp J').idem =
      poly (rename (J'.toFun ∘ J.toFun) p) * J'.idem * J'.toHom J.idem
    rw [hJ, mul_assoc]
    congr 1
    rw [idem, Finset.mul_sum]
    exact Finset.sum_congr rfl fun C _ => (J'.idem_mul_e (J.chamber C)).symm
  · simp only [NonUnitalAlgHom.comp_apply, toHom_apply, galleryHom_t]
    rfl
  · simp only [NonUnitalAlgHom.comp_apply, toHom_apply, galleryHom_r]
    rfl

/-- A chamber embedding is determined by its maps of strands and of chambers: the extension of
relabellings is forced by `perm_apply` and `perm_apply_of_not_mem`. -/
theorem ext_of {J J' : ChamberEmbedding Γ ν₁ ν} (hf : ∀ s, J.toFun s = J'.toFun s)
    (hc : ∀ C, J.chamber C = J'.chamber C) : J = J' := by
  have hf' : J.toFun = J'.toFun := funext hf
  have hp : J.perm = J'.perm := by
    refine MonoidHom.ext fun g => Subtype.ext (Equiv.ext fun t => ?_)
    by_cases ht : t ∈ Set.range J.toFun
    · obtain ⟨s, rfl⟩ := ht
      rw [J.perm_apply, hf, hf s, J'.perm_apply]
    · rw [J.perm_apply_of_not_mem g t ht, J'.perm_apply_of_not_mem g t (hf' ▸ ht)]
  obtain ⟨⟨f, _, _, _⟩, c, _, _, p, _, _, _⟩ := J
  obtain ⟨⟨f', _, _, _⟩, c', _, _, p', _, _, _⟩ := J'
  have hc' : c = c' := funext hc
  simp only at hf' hc' hp
  subst hf' hc' hp
  rfl

/-- The identity chamber embedding. -/
def id (ν : I →₀ ℕ) : ChamberEmbedding Γ ν ν where
  toFun := _root_.id
  injective := Function.injective_id
  colour _ := rfl
  rank_lt _ _ _ h := h
  chamber := _root_.id
  chamber_hyp C h := by rcases h with _ | _ <;> rfl
  chamber_of_not_mem C D h hn := absurd ⟨h, by rcases h with _ | _ <;> rfl⟩ hn
  perm := MonoidHom.id _
  perm_apply _ _ := rfl
  perm_apply_of_not_mem _ t ht := absurd ⟨t, rfl⟩ ht
  smul_chamber _ _ := rfl

theorem toHom_id (ν : I →₀ ℕ) (x : GalleryAlgebra k Γ ν) : (id (Γ := Γ) ν).toHom x = x := by
  have := nonUnitalAlgHom_ext (f := (id (Γ := Γ) ν).toHom (k := k)) (g := NonUnitalAlgHom.id k _)
    (fun C => by rw [toHom_apply, galleryHom_e]; rfl)
    (fun p => by
      rw [toHom_apply, galleryHom_poly]
      show poly (rename _root_.id p) * ∑ C, e C = poly p
      rw [rename_id, sum_e, mul_one]; rfl)
    (fun C D => by rw [toHom_apply, galleryHom_t]; rfl)
    (fun σ C => by rw [toHom_apply, galleryHom_r]; rfl)
  exact DFunLike.congr_fun this x

end ChamberEmbedding

/-! ### Transport along an equality of dimension vectors -/

section Cast

variable {ν μ : I →₀ ℕ}

open Juxtapose in
/-- The identity of the arrangement of `ν`, as a chamber embedding into that of `μ = ν`. -/
def ChamberEmbedding.castEmb (h : ν = μ) : ChamberEmbedding Γ ν μ :=
  h ▸ ChamberEmbedding.id ν

omit [DecidableEq I] in
@[simp] theorem ChamberEmbedding.castEmb_toFun (h : ν = μ) (s : Strand ν) :
    (ChamberEmbedding.castEmb (Γ := Γ) h).toFun s = Juxtapose.castStrand h s := by
  subst h
  rfl

omit [DecidableEq I] in
@[simp] theorem ChamberEmbedding.castEmb_chamber (h : ν = μ) (C : FullChamber Γ ν) :
    (ChamberEmbedding.castEmb h).chamber C = Juxtapose.castChamber h C := by
  subst h
  rfl

variable (k Γ) in
/-- The gallery algebra of `ν` as that of `μ`, along `ν = μ`. -/
noncomputable def castGallery (h : ν = μ) : GalleryAlgebra k Γ ν ≃ₐ[k] GalleryAlgebra k Γ μ :=
  h ▸ AlgEquiv.refl

variable (k Γ) in
/-- Webster's algebra `W_ν` as `W_μ`, along `ν = μ`. -/
noncomputable def castW (h : ν = μ) :
    WeightedKLRAlgebra k Γ ν ≃ₐ[k] WeightedKLRAlgebra k Γ μ :=
  h ▸ AlgEquiv.refl

theorem castW_val (h : ν = μ) (a : WeightedKLRAlgebra k Γ ν) :
    (castW k Γ h a).1 = castGallery k Γ h a.1 := by
  subst h
  rfl

theorem ChamberEmbedding.toHom_castEmb (h : ν = μ) (x : GalleryAlgebra k Γ ν) :
    (ChamberEmbedding.castEmb (Γ := Γ) h).toHom x = castGallery k Γ h x := by
  subst h
  exact ChamberEmbedding.toHom_id ν x

/-- Transporting the algebra map of a chamber embedding along an equality of the target. -/
theorem castGallery_toHom {ν₁ : I →₀ ℕ} (h : ν = μ) (J : ChamberEmbedding Γ ν₁ ν)
    (x : GalleryAlgebra k Γ ν₁) :
    castGallery k Γ h (J.toHom x) = (J.comp (ChamberEmbedding.castEmb h)).toHom x := by
  rw [ChamberEmbedding.toHom_comp, NonUnitalAlgHom.comp_apply, ChamberEmbedding.toHom_castEmb]

end Cast

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

/-! ### The two sides as sums over chamber embeddings -/

theorem leftHom_val (x : GalleryAlgebra k Γ ν') :
    (leftHom k Γ ν' ν'' x).1 = ∑ C'', (leftChamberEmb C'').toHom x := rfl

theorem rightHom_val (y : GalleryAlgebra k Γ ν'') :
    (rightHom k Γ ν' ν'' y).1 = ∑ C', (rightChamberEmb C').toHom y := rfl

theorem leftHom_mul_val (x x' : GalleryAlgebra k Γ ν') :
    (leftHom k Γ ν' ν'' (x * x')).1 = (leftHom k Γ ν' ν'' x).1 * (leftHom k Γ ν' ν'' x').1 := by
  rw [map_mul]
  rfl

theorem rightHom_mul_val (y y' : GalleryAlgebra k Γ ν'') :
    (rightHom k Γ ν' ν'' (y * y')).1 =
      (rightHom k Γ ν' ν'' y).1 * (rightHom k Γ ν' ν'' y').1 := by
  rw [map_mul]
  rfl

theorem mem_corner_idem {ν₁ ν : I →₀ ℕ} (J : ChamberEmbedding Γ ν₁ ν) :
    J.idem (k := k) ∈ Subsemigroup.corner J.idem :=
  (Subsemigroup.mem_corner_iff J.isIdempotentElem_idem).2
    ⟨J.isIdempotentElem_idem.eq, J.isIdempotentElem_idem.eq⟩

/-- Restricting the left action to the chamber `D` on the right. -/
theorem leftHom_mul_rightHom_e (x : GalleryAlgebra k Γ ν') (D : FullChamber Γ ν'') :
    (leftHom k Γ ν' ν'' x).1 * (rightHom k Γ ν' ν'' (e D)).1 = (leftChamberEmb D).toHom x := by
  rw [rightHom_e, leftHom_val, Finset.sum_mul, Finset.sum_eq_single D]
  · exact ((Subsemigroup.mem_corner_iff (leftChamberEmb D).isIdempotentElem_idem).1
      ((leftChamberEmb D).galleryHom x).2).2
  · intro C'' _ hne
    exact mul_eq_zero_of_mem_corner (leftChamberEmb C'').isIdempotentElem_idem
      (leftChamberEmb D).isIdempotentElem_idem (leftIdem_orth C'' D hne)
      ((leftChamberEmb C'').galleryHom x).2 (mem_corner_idem (leftChamberEmb D))
  · simp

/-- Restricting the right action to the chamber `C` on the left. -/
theorem leftHom_e_mul_rightHom (C : FullChamber Γ ν') (y : GalleryAlgebra k Γ ν'') :
    (leftHom k Γ ν' ν'' (e C)).1 * (rightHom k Γ ν' ν'' y).1 = (rightChamberEmb C).toHom y := by
  rw [leftHom_e, rightHom_val, Finset.mul_sum, Finset.sum_eq_single C]
  · exact ((Subsemigroup.mem_corner_iff (rightChamberEmb C).isIdempotentElem_idem).1
      ((rightChamberEmb C).galleryHom y).2).1
  · intro C' _ hne
    exact mul_eq_zero_of_mem_corner (rightChamberEmb C).isIdempotentElem_idem
      (rightChamberEmb C').isIdempotentElem_idem (rightIdem_orth C C' (Ne.symm hne))
      (mem_corner_idem (rightChamberEmb C)) ((rightChamberEmb C').galleryHom y).2
  · simp

/-! ### Associativity -/

section Assoc

variable {ν₁ ν₂ ν₃ : I →₀ ℕ}

omit [DecidableEq I] in
theorem castStrand_assoc_inl_inl (s : Strand ν₁) :
    castStrand (add_assoc ν₁ ν₂ ν₃) (inlStrand (ν₁ + ν₂) ν₃ (inlStrand ν₁ ν₂ s)) =
      inlStrand ν₁ (ν₂ + ν₃) s :=
  Strand.ext_of (Subtype.ext (castStrand_colour _ _)) (castStrand_rank _ _)

omit [DecidableEq I] in
theorem castStrand_assoc_inl_inr (s : Strand ν₂) :
    castStrand (add_assoc ν₁ ν₂ ν₃) (inlStrand (ν₁ + ν₂) ν₃ (inrStrand ν₁ ν₂ s)) =
      inrStrand ν₁ (ν₂ + ν₃) (inlStrand ν₂ ν₃ s) :=
  Strand.ext_of (Subtype.ext (castStrand_colour _ _)) (castStrand_rank _ _)

omit [DecidableEq I] in
theorem castStrand_assoc_inr (s : Strand ν₃) :
    castStrand (add_assoc ν₁ ν₂ ν₃) (inrStrand (ν₁ + ν₂) ν₃ s) =
      inrStrand ν₁ (ν₂ + ν₃) (inrStrand ν₂ ν₃ s) := by
  refine Strand.ext_of (Subtype.ext (castStrand_colour _ _)) ?_
  rw [castStrand_rank]
  show (ν₁ + ν₂) (s.1 : I) + s.2.val = ν₁ (s.1 : I) + (ν₂ (s.1 : I) + s.2.val)
  rw [Finsupp.add_apply]
  omega

theorem comp_leftChamberEmb_assoc (C₂ : FullChamber Γ ν₂) (C₃ : FullChamber Γ ν₃) :
    (leftChamberEmb (ν' := ν₁) C₂).comp ((leftChamberEmb (ν' := ν₁ + ν₂) C₃).comp
      (ChamberEmbedding.castEmb (add_assoc ν₁ ν₂ ν₃))) = leftChamberEmb (chamber C₂ C₃) :=
  ChamberEmbedding.ext_of (fun s => by
      simp only [ChamberEmbedding.comp_toFun, ChamberEmbedding.castEmb_toFun]
      exact castStrand_assoc_inl_inl s)
    (fun C₁ => by
      simp only [ChamberEmbedding.comp_chamber, ChamberEmbedding.castEmb_chamber]
      exact castChamber_chamber_assoc C₁ C₂ C₃)

theorem comp_rightChamberEmb_leftChamberEmb_assoc (C₁ : FullChamber Γ ν₁)
    (C₃ : FullChamber Γ ν₃) :
    (rightChamberEmb (ν'' := ν₂) C₁).comp ((leftChamberEmb (ν' := ν₁ + ν₂) C₃).comp
      (ChamberEmbedding.castEmb (add_assoc ν₁ ν₂ ν₃))) =
      (leftChamberEmb C₃).comp (rightChamberEmb (ν'' := ν₂ + ν₃) C₁) :=
  ChamberEmbedding.ext_of (fun s => by
      simp only [ChamberEmbedding.comp_toFun, ChamberEmbedding.castEmb_toFun]
      exact castStrand_assoc_inl_inr s)
    (fun C₂ => by
      simp only [ChamberEmbedding.comp_chamber, ChamberEmbedding.castEmb_chamber]
      exact castChamber_chamber_assoc C₁ C₂ C₃)

theorem comp_rightChamberEmb_assoc (C₁ : FullChamber Γ ν₁) (C₂ : FullChamber Γ ν₂) :
    (rightChamberEmb (ν'' := ν₃) (chamber C₁ C₂)).comp
      (ChamberEmbedding.castEmb (add_assoc ν₁ ν₂ ν₃)) =
      (rightChamberEmb C₂).comp (rightChamberEmb (ν'' := ν₂ + ν₃) C₁) :=
  ChamberEmbedding.ext_of (fun s => by
      simp only [ChamberEmbedding.comp_toFun, ChamberEmbedding.castEmb_toFun]
      exact castStrand_assoc_inr s)
    (fun C₃ => by
      simp only [ChamberEmbedding.comp_chamber, ChamberEmbedding.castEmb_chamber]
      exact castChamber_chamber_assoc C₁ C₂ C₃)

theorem castGallery_leftHom_leftHom (x : GalleryAlgebra k Γ ν₁) :
    castGallery k Γ (add_assoc ν₁ ν₂ ν₃)
        (leftHom k Γ (ν₁ + ν₂) ν₃ (leftHom k Γ ν₁ ν₂ x).1).1 =
      ∑ C₂, ∑ C₃, (leftChamberEmb (chamber C₂ C₃)).toHom x := by
  rw [leftHom_val, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun C₃ _ => ?_
  rw [leftHom_val, map_sum, map_sum]
  refine Finset.sum_congr rfl fun C₂ _ => ?_
  rw [castGallery_toHom, ← NonUnitalAlgHom.comp_apply, ← ChamberEmbedding.toHom_comp,
    comp_leftChamberEmb_assoc]

theorem leftHom_mul_rightHom_juxtIdem (x : GalleryAlgebra k Γ ν₁) :
    (leftHom k Γ ν₁ (ν₂ + ν₃) x).1 * (rightHom k Γ ν₁ (ν₂ + ν₃) (juxtIdem k Γ ν₂ ν₃)).1 =
      ∑ C₂, ∑ C₃, (leftChamberEmb (chamber C₂ C₃)).toHom x := by
  have hJ : juxtIdem k Γ ν₂ ν₃ = ∑ C₂, ∑ C₃, e (chamber C₂ C₃) := rfl
  rw [hJ, map_sum, corner_val_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C₂ _ => ?_
  rw [map_sum, corner_val_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun C₃ _ => leftHom_mul_rightHom_e x _

theorem castGallery_leftHom_rightHom (y : GalleryAlgebra k Γ ν₂) :
    castGallery k Γ (add_assoc ν₁ ν₂ ν₃)
        (leftHom k Γ (ν₁ + ν₂) ν₃ (rightHom k Γ ν₁ ν₂ y).1).1 =
      (rightHom k Γ ν₁ (ν₂ + ν₃) (leftHom k Γ ν₂ ν₃ y).1).1 := by
  rw [leftHom_val (ν'' := ν₃) (rightHom k Γ ν₁ ν₂ y).1, rightHom_val (ν' := ν₁) y,
    rightHom_val (ν' := ν₁) (leftHom k Γ ν₂ ν₃ y).1, leftHom_val (ν'' := ν₃) y]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C₁ _ => Finset.sum_congr rfl fun C₃ _ => ?_
  rw [castGallery_toHom, ← NonUnitalAlgHom.comp_apply, ← ChamberEmbedding.toHom_comp,
    comp_rightChamberEmb_leftChamberEmb_assoc, ChamberEmbedding.toHom_comp,
    NonUnitalAlgHom.comp_apply]

theorem castGallery_juxtIdem_mul_rightHom (z : GalleryAlgebra k Γ ν₃) :
    castGallery k Γ (add_assoc ν₁ ν₂ ν₃)
        ((leftHom k Γ (ν₁ + ν₂) ν₃ (juxtIdem k Γ ν₁ ν₂)).1 * (rightHom k Γ (ν₁ + ν₂) ν₃ z).1) =
      (rightHom k Γ ν₁ (ν₂ + ν₃) (rightHom k Γ ν₂ ν₃ z).1).1 := by
  have hJ : juxtIdem k Γ ν₁ ν₂ = ∑ C₁, ∑ C₂, e (chamber C₁ C₂) := rfl
  have hL : (leftHom k Γ (ν₁ + ν₂) ν₃ (juxtIdem k Γ ν₁ ν₂)).1 =
      ∑ C₁, ∑ C₂, (leftHom k Γ (ν₁ + ν₂) ν₃ (e (chamber C₁ C₂))).1 := by
    rw [hJ, map_sum, corner_val_sum]
    exact Finset.sum_congr rfl fun C₁ _ => by rw [map_sum, corner_val_sum]
  rw [hL, rightHom_val (ν' := ν₁) (rightHom k Γ ν₂ ν₃ z).1, rightHom_val (ν' := ν₂) z]
  simp only [Finset.sum_mul, leftHom_e_mul_rightHom, map_sum]
  refine Finset.sum_congr rfl fun C₁ _ => Finset.sum_congr rfl fun C₂ _ => ?_
  rw [castGallery_toHom, comp_rightChamberEmb_assoc, ChamberEmbedding.toHom_comp,
    NonUnitalAlgHom.comp_apply]

variable (ν₁ ν₂ ν₃) in
/-- **Associativity of juxtaposition** (Webster, arXiv:1209.2463v4, §2.4, Proposition 2.18), on
the gallery algebras: `(x ∘ y) ∘ z = x ∘ (y ∘ z)` along `(ν₁ + ν₂) + ν₃ = ν₁ + (ν₂ + ν₃)`. -/
theorem galleryTensorHom_assoc (x : GalleryAlgebra k Γ ν₁) (y : GalleryAlgebra k Γ ν₂)
    (z : GalleryAlgebra k Γ ν₃) :
    castGallery k Γ (add_assoc ν₁ ν₂ ν₃)
        (galleryTensorHom k Γ (ν₁ + ν₂) ν₃ ((galleryTensorHom k Γ ν₁ ν₂ (x ⊗ₜ y)).1 ⊗ₜ z)).1 =
      (galleryTensorHom k Γ ν₁ (ν₂ + ν₃) (x ⊗ₜ (galleryTensorHom k Γ ν₂ ν₃ (y ⊗ₜ z)).1)).1 := by
  have hy : (rightHom k Γ ν₁ ν₂ y).1 = (rightHom k Γ ν₁ ν₂ y).1 * juxtIdem k Γ ν₁ ν₂ :=
    ((Subsemigroup.mem_corner_iff isIdempotentElem_juxtIdem).1 (rightHom k Γ ν₁ ν₂ y).2).2.symm
  have hy' : (leftHom k Γ ν₂ ν₃ y).1 = juxtIdem k Γ ν₂ ν₃ * (leftHom k Γ ν₂ ν₃ y).1 :=
    ((Subsemigroup.mem_corner_iff isIdempotentElem_juxtIdem).1 (leftHom k Γ ν₂ ν₃ y).2).1.symm
  simp only [galleryTensorHom_tmul, corner_val_mul]
  rw [hy, hy', leftHom_mul_val, leftHom_mul_val, rightHom_mul_val, rightHom_mul_val,
    mul_assoc, map_mul, map_mul]
  have key : ∀ a b c : GalleryAlgebra k Γ (ν₁ + ν₂ + ν₃),
      castGallery k Γ (add_assoc ν₁ ν₂ ν₃) (a * b) * castGallery k Γ (add_assoc ν₁ ν₂ ν₃) c =
        castGallery k Γ (add_assoc ν₁ ν₂ ν₃) a *
          castGallery k Γ (add_assoc ν₁ ν₂ ν₃) (b * c) := fun a b c => by
    rw [← map_mul, ← map_mul, mul_assoc]
  rw [key, castGallery_juxtIdem_mul_rightHom, castGallery_leftHom_rightHom,
    castGallery_leftHom_leftHom, ← leftHom_mul_rightHom_juxtIdem]
  simp only [mul_assoc]

variable (ν₁ ν₂ ν₃) in
/-- **Associativity of Webster's map `ι`** (arXiv:1209.2463v4, §2.4, Proposition 2.18):
`ι(ι(a ⊗ b) ⊗ c) = ι(a ⊗ ι(b ⊗ c))` along `(ν₁ + ν₂) + ν₃ = ν₁ + (ν₂ + ν₃)`. -/
theorem inductionMap_assoc (a : WeightedKLRAlgebra k Γ ν₁) (b : WeightedKLRAlgebra k Γ ν₂)
    (c : WeightedKLRAlgebra k Γ ν₃) :
    castW k Γ (add_assoc ν₁ ν₂ ν₃)
        (inductionMap k Γ (ν₁ + ν₂) ν₃ (inductionMap k Γ ν₁ ν₂ (a ⊗ₜ b) ⊗ₜ c)) =
      inductionMap k Γ ν₁ (ν₂ + ν₃) (a ⊗ₜ inductionMap k Γ ν₂ ν₃ (b ⊗ₜ c)) := by
  apply Subtype.ext
  rw [castW_val, inductionMap_tmul, inductionMap_tmul, inductionMap_tmul, inductionMap_tmul]
  exact galleryTensorHom_assoc ν₁ ν₂ ν₃ _ _ _

end Assoc

/-! ### Unit -/

section Unit

variable {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- There are no strands of dimension vector `0`. -/
theorem isEmpty_strand_zero : IsEmpty (Strand (0 : I →₀ ℕ)) :=
  ⟨fun s => absurd s.2.2 (by simp)⟩

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- There are no walls and no diagonals for the dimension vector `0`. -/
theorem isEmpty_hyp_zero : IsEmpty (Hyp Γ 0) := by
  have := isEmpty_strand_zero (I := I)
  refine ⟨fun h => ?_⟩
  rcases h with w | d
  · exact isEmptyElim w.1.2.1
  · exact isEmptyElim d.1.1

omit [DecidableEq I] in
/-- The arrangement of `0` has exactly one full chamber. -/
noncomputable instance : Unique (FullChamber Γ 0) where
  default := FullChamber.ofPoint (fun s => (isEmpty_strand_zero.false s).elim)
    (fun h => (isEmpty_hyp_zero.false h).elim)
  uniq _ := Subtype.ext (funext fun h => (isEmpty_hyp_zero.false h).elim)

/-- The idempotent of `W_0` is the unit of the gallery algebra. -/
theorem rankIdem_zero : rankIdem k Γ 0 = 1 := by
  rw [rankIdem, ← sum_e]
  congr 1
  exact Finset.filter_true_of_mem fun _ _ d => ((isEmpty_hyp_zero (Γ := Γ)).false (.inr d)).elim

omit [DecidableEq I] in
theorem castStrand_inl_zero (s : Strand ν) : castStrand (add_zero ν) (inlStrand ν 0 s) = s :=
  Strand.ext_of (Subtype.ext (castStrand_colour _ _)) (castStrand_rank _ _)

omit [DecidableEq I] in
theorem castStrand_inr_zero (s : Strand ν) : castStrand (zero_add ν) (inrStrand 0 ν s) = s := by
  refine Strand.ext_of (Subtype.ext (castStrand_colour _ _)) ?_
  rw [castStrand_rank]
  show (0 : I →₀ ℕ) (s.1 : I) + s.2.val = s.2.val
  rw [Finsupp.zero_apply, zero_add]

theorem comp_leftChamberEmb_zero (C₀ : FullChamber Γ 0) :
    (leftChamberEmb (ν' := ν) C₀).comp (ChamberEmbedding.castEmb (add_zero ν)) =
      ChamberEmbedding.id ν :=
  ChamberEmbedding.ext_of (fun s => by
      simp only [ChamberEmbedding.comp_toFun, ChamberEmbedding.castEmb_toFun]
      exact castStrand_inl_zero s)
    (fun C => by
      simp only [ChamberEmbedding.comp_chamber, ChamberEmbedding.castEmb_chamber]
      exact castChamber_chamber_zero_right C C₀)

theorem comp_rightChamberEmb_zero (C₀ : FullChamber Γ 0) :
    (rightChamberEmb (ν'' := ν) C₀).comp (ChamberEmbedding.castEmb (zero_add ν)) =
      ChamberEmbedding.id ν :=
  ChamberEmbedding.ext_of (fun s => by
      simp only [ChamberEmbedding.comp_toFun, ChamberEmbedding.castEmb_toFun]
      exact castStrand_inr_zero s)
    (fun C => by
      simp only [ChamberEmbedding.comp_chamber, ChamberEmbedding.castEmb_chamber]
      exact castChamber_chamber_zero_left C₀ C)

theorem castGallery_leftHom_zero (x : GalleryAlgebra k Γ ν) :
    castGallery k Γ (add_zero ν) (leftHom k Γ ν 0 x).1 = x := by
  rw [leftHom_val, Fintype.sum_unique, castGallery_toHom, comp_leftChamberEmb_zero,
    ChamberEmbedding.toHom_id]

theorem castGallery_rightHom_zero (y : GalleryAlgebra k Γ ν) :
    castGallery k Γ (zero_add ν) (rightHom k Γ 0 ν y).1 = y := by
  rw [rightHom_val, Fintype.sum_unique, castGallery_toHom, comp_rightChamberEmb_zero,
    ChamberEmbedding.toHom_id]

/-- **Right unit of juxtaposition** on the gallery algebras (Webster, arXiv:1209.2463v4, §2.4,
Proposition 2.18): `ι(x ⊗ 1) = x` along `ν + 0 = ν`. -/
theorem galleryTensorHom_tmul_one (x : GalleryAlgebra k Γ ν) :
    castGallery k Γ (add_zero ν) (galleryTensorHom k Γ ν 0 (x ⊗ₜ 1)).1 = x := by
  rw [galleryTensorHom_tmul, map_one, mul_one, castGallery_leftHom_zero]

/-- **Left unit of juxtaposition** on the gallery algebras (Webster, arXiv:1209.2463v4, §2.4,
Proposition 2.18): `ι(1 ⊗ y) = y` along `0 + ν = ν`. -/
theorem galleryTensorHom_one_tmul (y : GalleryAlgebra k Γ ν) :
    castGallery k Γ (zero_add ν) (galleryTensorHom k Γ 0 ν (1 ⊗ₜ y)).1 = y := by
  rw [galleryTensorHom_tmul, map_one, one_mul, castGallery_rightHom_zero]

theorem one_val_zero : (1 : WeightedKLRAlgebra k Γ 0).1 = 1 := rankIdem_zero

/-- **Right unit of Webster's map `ι`** (arXiv:1209.2463v4, §2.4, Proposition 2.18):
`ι(a ⊗ 1) = a` along `ν + 0 = ν`, with `1` the unit of `W_0`. -/
theorem inductionMap_tmul_one (a : WeightedKLRAlgebra k Γ ν) :
    castW k Γ (add_zero ν) (inductionMap k Γ ν 0 (a ⊗ₜ 1)) = a := by
  apply Subtype.ext
  rw [castW_val, inductionMap_tmul, one_val_zero]
  exact galleryTensorHom_tmul_one a.1

/-- **Left unit of Webster's map `ι`** (arXiv:1209.2463v4, §2.4, Proposition 2.18):
`ι(1 ⊗ a) = a` along `0 + ν = ν`, with `1` the unit of `W_0`. -/
theorem inductionMap_one_tmul (a : WeightedKLRAlgebra k Γ ν) :
    castW k Γ (zero_add ν) (inductionMap k Γ 0 ν (1 ⊗ₜ a)) = a := by
  apply Subtype.ext
  rw [castW_val, inductionMap_tmul, one_val_zero]
  exact galleryTensorHom_one_tmul a.1

end Unit

end Juxtapose

end Categorification.WeightedKLR
