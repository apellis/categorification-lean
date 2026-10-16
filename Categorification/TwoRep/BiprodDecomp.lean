/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Decompositions into biproducts, and monomial matrices

Two elementary facts about biproducts in a preadditive category, used to identify the composite
`F_i E_i` of the furled action `g` on a block with a sum of `F_a E_b` (Webster,
arXiv:1603.06311v3, §2.3):

* `isoOfDecomp`: maps `sᵢ : Yᵢ ⟶ X`, `rᵢ : X ⟶ Yᵢ` with `sᵢ ≫ rᵢ = 1`, `sᵢ ≫ rⱼ = 0` for
  `i ≠ j` and `∑ᵢ rᵢ ≫ sᵢ = 1` give `X ≅ ⨁ᵢ Yᵢ`; `isoOfDecomp₂` for two families.
* `isIso_matrix_of_monomial`: a matrix `matrixW M : ⨁ᵢ Yᵢ ⟶ ⨁ⱼ Zⱼ` whose entries vanish off
  the graph of a bijection between `{i | P i}` and `{j | Q j}`, with invertible entries on the
  graph and zero objects off `P` and `Q`, is invertible.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

universe w w' v u

variable {D : Type u} [Category.{v} D] [Preadditive D]

section General

variable {J : Type w} [Fintype J] [DecidableEq J] {f : J → D} [HasBiproduct f]

/-- `biproduct.total` for index types in any universe. -/
theorem biproduct_total' : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) := by
  ext j j'
  simp [Preadditive.sum_comp, biproduct.ι_π, comp_dite]

/-- `biproduct.lift_desc` for index types in any universe. -/
theorem biproduct_lift_desc' {T U : D} (g : ∀ j, T ⟶ f j) (h : ∀ j, f j ⟶ U) :
    biproduct.lift g ≫ biproduct.desc h = ∑ j, g j ≫ h j := by
  conv_lhs => rw [← Category.id_comp (biproduct.desc h), ← biproduct_total' (f := f)]
  simp [Preadditive.comp_sum, Preadditive.sum_comp]

end General

section Decomp

variable {ι : Type w} [Fintype ι] [DecidableEq ι] {X : D} {Y : ι → D} [HasBiproduct Y]
  (s : ∀ i, Y i ⟶ X) (r : ∀ i, X ⟶ Y i)

/-- **A decomposition into a biproduct**: `X ≅ ⨁ᵢ Yᵢ` from an orthogonal family of retracts
summing to the identity. -/
@[simps]
def isoOfDecomp (hsr : ∀ i, s i ≫ r i = 𝟙 _) (hsr' : ∀ i j, i ≠ j → s i ≫ r j = 0)
    (htot : ∑ i, r i ≫ s i = 𝟙 X) : X ≅ ⨁ Y where
  hom := biproduct.lift r
  inv := biproduct.desc s
  hom_inv_id := by rw [biproduct_lift_desc', htot]
  inv_hom_id := by
    ext i j
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.id_comp]
    by_cases hij : i = j
    · subst hij; simp [hsr]
    · rw [hsr' j i (Ne.symm hij), biproduct.ι_π_ne _ (Ne.symm hij)]

end Decomp

section Decomp₂

variable [HasBinaryBiproducts D] {ι : Type w} {κ : Type w'} [Fintype ι]
  [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {X : D} {Y : ι → D} {Z : κ → D} [HasBiproduct Y] [HasBiproduct Z]
  (s : ∀ i, Y i ⟶ X) (r : ∀ i, X ⟶ Y i) (s' : ∀ j, Z j ⟶ X) (r' : ∀ j, X ⟶ Z j)

/-- **A decomposition into two biproducts**: `X ≅ (⨁ᵢ Yᵢ) ⊞ (⨁ⱼ Zⱼ)` from an orthogonal family
of retracts summing to the identity. -/
@[simps]
def isoOfDecomp₂ (hsr : ∀ i, s i ≫ r i = 𝟙 _) (hsr' : ∀ i i', i ≠ i' → s i ≫ r i' = 0)
    (hs'r' : ∀ j, s' j ≫ r' j = 𝟙 _) (hs'r'' : ∀ j j', j ≠ j' → s' j ≫ r' j' = 0)
    (hsr₂ : ∀ i j, s i ≫ r' j = 0) (hs'r₂ : ∀ j i, s' j ≫ r i = 0)
    (htot : ∑ i, r i ≫ s i + ∑ j, r' j ≫ s' j = 𝟙 X) : X ≅ (⨁ Y) ⊞ (⨁ Z) where
  hom := biprod.lift (biproduct.lift r) (biproduct.lift r')
  inv := biprod.desc (biproduct.desc s) (biproduct.desc s')
  hom_inv_id := by rw [biprod.lift_desc, biproduct_lift_desc', biproduct_lift_desc', htot]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · ext i j
      simp only [biprod.inl_desc_assoc, biprod.lift_fst, biproduct.ι_desc_assoc,
        biproduct.lift_π, Category.id_comp, biprod.inl_fst, Category.assoc]
      by_cases hij : i = j
      · subst hij; simp [hsr]
      · rw [hsr' j i (Ne.symm hij), biproduct.ι_π_ne _ (Ne.symm hij)]
    · ext i j
      simp [hsr₂]
    · ext j i
      simp [hs'r₂]
    · ext j j'
      simp only [biprod.inr_desc_assoc, biprod.lift_snd, biproduct.ι_desc_assoc,
        biproduct.lift_π, Category.id_comp, biprod.inr_snd, Category.assoc]
      by_cases hjj : j = j'
      · subst hjj; simp [hs'r']
      · rw [hs'r'' j' j (Ne.symm hjj), biproduct.ι_π_ne _ (Ne.symm hjj)]

end Decomp₂

section Monomial

variable {ι : Type w} {κ : Type w'} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {Y : ι → D} {Z : κ → D} [HasBiproduct Y] [HasBiproduct Z]

/-- The morphism `⨁ᵢ Yᵢ ⟶ ⨁ⱼ Zⱼ` with entries `M i j` (`biproduct.matrix`, for index types
in any universe). -/
def matrixW (M : ∀ i j, Y i ⟶ Z j) : ⨁ Y ⟶ ⨁ Z :=
  biproduct.desc fun i => biproduct.lift fun j => M i j

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[reassoc (attr := simp)]
theorem ι_matrixW_π (M : ∀ i j, Y i ⟶ Z j) (i : ι) (j : κ) :
    biproduct.ι Y i ≫ matrixW M ≫ biproduct.π Z j = M i j := by
  simp [matrixW]

omit [Fintype ι] [DecidableEq ι] in
theorem ι_matrixW_comp_π {W : ι → D} [HasBiproduct W] (M : ∀ i j, Y i ⟶ Z j)
    (N : ∀ j i, Z j ⟶ W i) (i : ι) (i' : ι) :
    biproduct.ι Y i ≫ matrixW M ≫ matrixW N ≫ biproduct.π W i' = ∑ j, M i j ≫ N j i' := by
  rw [← Category.id_comp (matrixW N), ← biproduct_total' (f := Z)]
  simp [Preadditive.comp_sum, Preadditive.sum_comp]

omit [Fintype κ] [DecidableEq κ] in
theorem ι_matrixW_comp_π' {W : κ → D} [HasBiproduct W] (N : ∀ j i, Z j ⟶ Y i)
    (M : ∀ i j, Y i ⟶ W j) (j j' : κ) :
    biproduct.ι Z j ≫ matrixW N ≫ matrixW M ≫ biproduct.π W j' = ∑ i, N j i ≫ M i j' := by
  rw [← Category.id_comp (matrixW M), ← biproduct_total' (f := Y)]
  simp [Preadditive.comp_sum, Preadditive.sum_comp]

/-- **A monomial matrix is invertible**: if the entries of `M : ⨁ᵢ Yᵢ ⟶ ⨁ⱼ Zⱼ` vanish off the
graph of a bijection `e` between `{i | P i}` and `{j | Q j}`, are invertible on it, and `Yᵢ`,
`Zⱼ` are zero off `P`, `Q`, then `M` is invertible. -/
theorem isIso_matrix_of_monomial (M : ∀ i j, Y i ⟶ Z j) {P : ι → Prop} {Q : κ → Prop}
    (e : {i // P i} ≃ {j // Q j}) (hM : ∀ i j, (hi : P i) → (hj : Q j) →
      (e ⟨i, hi⟩).1 ≠ j → M i j = 0)
    (hiso : ∀ i (hi : P i), IsIso (M i (e ⟨i, hi⟩).1))
    (hY : ∀ i, ¬ P i → IsZero (Y i)) (hZ : ∀ j, ¬ Q j → IsZero (Z j)) :
    IsIso (matrixW M) := by
  classical
  let N : ∀ j i, Z j ⟶ Y i := fun j i =>
    if h : ∃ (hi : P i) (_ : Q j), (e ⟨i, hi⟩).1 = j then
      have := hiso i h.1
      eqToHom (by rw [h.2.2]) ≫ inv (M i (e ⟨i, h.1⟩).1)
    else 0
  refine ⟨⟨matrixW N, ?_, ?_⟩⟩
  · ext i' i
    rw [Category.assoc, ι_matrixW_comp_π]
    simp only [Category.id_comp, biproduct.ι_π]
    by_cases hi : P i
    · rw [Finset.sum_eq_single (e ⟨i, hi⟩).1]
      · by_cases hii : i = i'
        · subst hii
          simp only [N]
          split_ifs with h
          · simp
          · exact absurd ⟨hi, (e ⟨i, hi⟩).2, trivial⟩ h
        · simp only [N, hii, dite_false]
          split_ifs with h
          · obtain ⟨hi', -, he⟩ := h
            exact absurd (congrArg Subtype.val (e.injective (Subtype.ext he))).symm hii
          · rw [Limits.comp_zero]
      · intro j _ hj
        by_cases hQ : Q j
        · rw [hM i j hi hQ (Ne.symm hj), Limits.zero_comp]
        · rw [(hZ j hQ).eq_of_tgt (M i j) 0, Limits.zero_comp]
      · simp
    · exact (hY i hi).eq_of_src _ _
  · ext j' j
    rw [Category.assoc, ι_matrixW_comp_π']
    simp only [Category.id_comp, biproduct.ι_π]
    by_cases hj : Q j
    · set i₀ := (e.symm ⟨j, hj⟩).1 with hi₀
      have hP : P i₀ := (e.symm ⟨j, hj⟩).2
      have hej : (e ⟨i₀, hP⟩).1 = j := by simp [i₀]
      rw [Finset.sum_eq_single i₀]
      · by_cases hjj : j = j'
        · subst hjj
          simp only [N]
          split_ifs with h
          swap; · exact absurd ⟨hP, hj, hej⟩ h
          have key : ∀ (j₀ : κ) (h : j₀ = j) [IsIso (M i₀ j₀)],
              eqToHom (congrArg Z h.symm) ≫ inv (M i₀ j₀) ≫ M i₀ j = 𝟙 _ := by
            rintro _ rfl _; simp
          simpa using key _ hej
        · simp only [hjj, dite_false]
          by_cases hQ : Q j'
          · rw [hM i₀ j' hP hQ (by rw [hej]; exact hjj), Limits.comp_zero]
          · rw [(hZ j' hQ).eq_of_tgt (M i₀ j') 0, Limits.comp_zero]
      · intro i _ hi
        simp only [N]
        split_ifs with h
        · obtain ⟨hi', -, he⟩ := h
          refine absurd ?_ hi
          rw [hi₀, show (⟨j, hj⟩ : {j // Q j}) = e ⟨i, hi'⟩ from Subtype.ext he.symm,
            Equiv.symm_apply_apply]
        · rw [Limits.zero_comp]
      · simp
    · exact (hZ j hj).eq_of_src _ _

end Monomial

end Categorification.TwoRep
