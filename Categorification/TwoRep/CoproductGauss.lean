/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Gaussian elimination and nilpotent matrices

Matrix lemmas in a preadditive category, used in the proof that Rouquier's map of a direct sum
of `sl₂` data with separated dots is invertible (B. Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3, Theorem `th:coproduct`; `Categorification.TwoRep.RouqCoproduct`).

* `isIso_id_add_of_isNilpotent`: `𝟙 + f` is invertible if `f` is nilpotent;
* `isIso_ofComponents_of_isIso_schur`: Gaussian elimination: a `2 × 2` block matrix with an
  invertible `(1,1)` entry is invertible if its Schur complement is;
* `isIso_lift_of_isIso_ofComponents`: a map `X ⟶ Y ⊞ T` is invertible if its extension by an
  identity block `X ⊞ S ⟶ Y ⊞ (T ⊞ S)` is;
* `Mat_` objects `oMat o ι` all of whose entries are a fixed object `o` with commutative
  endomorphisms: morphisms between them are matrices over `End o`, composition is matrix
  multiplication (`oMat_comp_apply`), and an endomorphism whose entries are nilpotent is
  nilpotent (`oMat_isNilpotent_of_entries`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

/-! ## Nilpotent matrices over a commutative ring -/

section Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_pow_apply_mem (M : Matrix ι ι R) (I : Ideal R) (hM : ∀ i j, M i j ∈ I) :
    ∀ (K : ℕ) (i j : ι), (M ^ K) i j ∈ I ^ K
  | 0, i, j => by simp
  | K + 1, i, j => by
    rw [pow_succ M, Matrix.mul_apply, pow_succ I]
    exact Submodule.sum_mem _ fun l _ =>
      Ideal.mul_mem_mul (matrix_pow_apply_mem M I hM K i l) (hM l j)

/-- A square matrix over a commutative ring whose entries are nilpotent is nilpotent. -/
theorem matrix_isNilpotent_of_entries (M : Matrix ι ι R) (hM : ∀ i j, IsNilpotent (M i j)) :
    IsNilpotent M := by
  set I : Ideal R := Ideal.span (Set.range fun p : ι × ι => M p.1 p.2)
  have hfg : I.FG := Submodule.fg_span (Set.finite_range _)
  have hle : I ≤ nilradical R := by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact mem_nilradical.mpr (hM p.1 p.2)
  obtain ⟨K, hK⟩ := (hfg.isNilpotent_iff_le_nilradical).mpr hle
  refine ⟨K, ?_⟩
  ext i j
  have := matrix_pow_apply_mem M I (fun i j => Ideal.subset_span ⟨(i, j), rfl⟩) K i j
  rw [hK, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  rw [this, Matrix.zero_apply]

end Matrix

/-! ## Gaussian elimination -/

section Biprod

variable {D : Type*} [Category D] [Preadditive D]

/-- `𝟙 + f` is invertible if `f` is nilpotent. -/
theorem isIso_id_add_of_isNilpotent {X : D} (f : X ⟶ X) (hf : IsNilpotent (R := End X) f) :
    IsIso (𝟙 X + f) :=
  (isUnit_iff_isIso (𝟙 X + f : End X)).mp hf.isUnit_one_add

variable [HasBinaryBiproducts D]

/-- **Gaussian elimination**: a block matrix with invertible `(1,1)` entry is invertible if its
Schur complement is. -/
theorem isIso_ofComponents_of_isIso_schur {X₁ X₂ Y₁ Y₂ : D} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)
    (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) [IsIso f₁₁] (h : IsIso (f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂)) :
    IsIso (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂) := by
  have w := (Biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂).2.2.2
  change (Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁)).hom ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫
    (Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂)).hom =
      biprod.map f₁₁ (f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂) at w
  have e : Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ =
      (Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁)).inv ≫ biprod.map f₁₁ (f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂) ≫
        (Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂)).inv := by
    rw [← w]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have : IsIso (biprod.map f₁₁ (f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂)) :=
    (biprod.mapIso (asIso f₁₁) (asIso (f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂))).isIso_hom
  rw [e]
  infer_instance

/-- A map `(f, c) : X ⟶ Y ⊞ T` is invertible if its extension
`[[f, c], [g, 1]] : X ⊞ S ⟶ Y ⊞ (T ⊞ S)` is. -/
theorem isIso_lift_of_isIso_ofComponents {X S Y T : D} (f : X ⟶ Y) (c : X ⟶ T) (g : S ⟶ Y)
    (h : IsIso (Biprod.ofComponents f (c ≫ biprod.inl) g (biprod.inr : S ⟶ T ⊞ S))) :
    IsIso (biprod.lift f c) := by
  set Mh := Biprod.ofComponents f (c ≫ biprod.inl) g (biprod.inr : S ⟶ T ⊞ S)
  have h1 : biprod.lift f c ≫ biprod.map (𝟙 Y) (biprod.inl : T ⟶ T ⊞ S) = biprod.inl ≫ Mh := by
    ext <;> simp [Mh]
  have h2 : Mh ≫ biprod.snd ≫ biprod.snd = biprod.snd := by
    ext <;> simp only [Mh, ← Category.assoc, Biprod.inl_ofComponents,
      Biprod.inr_ofComponents] <;> simp
  have h3 : inv Mh ≫ biprod.snd = biprod.snd ≫ biprod.snd := by
    rw [← h2, IsIso.inv_hom_id_assoc]
  set J : Y ⊞ T ⟶ Y ⊞ (T ⊞ S) := biprod.map (𝟙 Y) biprod.inl
  have hr : J ≫ biprod.map (𝟙 Y) biprod.fst = 𝟙 _ := by
    ext <;> simp [J]
  have h0 : J ≫ inv Mh ≫ biprod.snd = 0 := by
    rw [h3]; ext <;> simp [J]
  have hJ : J ≫ inv Mh = (J ≫ inv Mh ≫ biprod.fst) ≫ biprod.inl := by
    have e : J ≫ inv Mh = J ≫ inv Mh ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by
      rw [biprod.total, Category.comp_id]
    rw [e]
    simp only [Preadditive.comp_add, reassoc_of% h0, zero_comp, add_zero, Category.assoc]
  refine ⟨⟨J ≫ inv Mh ≫ biprod.fst, ?_, ?_⟩⟩
  · rw [reassoc_of% h1, IsIso.hom_inv_id_assoc, biprod.inl_fst]
  · have key : J = (J ≫ inv Mh ≫ biprod.fst) ≫ biprod.lift f c ≫ J := by
      rw [h1, ← Category.assoc, ← hJ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have := congrArg (· ≫ biprod.map (𝟙 Y) (biprod.fst : T ⊞ S ⟶ T)) key
    simp only [Category.assoc, hr] at this
    simpa using this.symm

end Biprod

/-! ## Matrices over the endomorphisms of one object -/

section OMat

variable {D : Type*} [Category D] [Preadditive D] (o : D)

/-- The object `o^{⊕ ι}` of the additive envelope. -/
abbrev oMat (ι : Type) [Fintype ι] : Mat_ D := ⟨ι, fun _ => o⟩

variable {o} (hcomm : ∀ f g : o ⟶ o, f ≫ g = g ≫ f)

/-- The commutative ring `End o`. -/
@[reducible]
def endCommRing : CommRing (End o) :=
  { (inferInstance : Ring (End o)) with mul_comm := fun f g => hcomm g f }

/-- A morphism between objects `o^{⊕ ι}` as a matrix over `End o`. -/
def oMat.toMatrix {ι κ : Type} [Fintype ι] [Fintype κ] (f : oMat o ι ⟶ oMat o κ) :
    Matrix ι κ (End o) := fun i j => f i j

include hcomm in
/-- Composition is matrix multiplication. -/
theorem oMat_comp_toMatrix {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (f : oMat o ι ⟶ oMat o κ) (g : oMat o κ ⟶ oMat o μ) :
    oMat.toMatrix (f ≫ g) = oMat.toMatrix f * oMat.toMatrix g := by
  ext i m
  exact (Mat_.comp_apply f g i m).trans (Finset.sum_congr rfl fun j _ => hcomm _ _)

include hcomm in
theorem oMat_pow_toMatrix {ι : Type} [Fintype ι] [DecidableEq ι] (f : End (oMat o ι))
    (K : ℕ) : oMat.toMatrix (f ^ K) = oMat.toMatrix f ^ K := by
  induction K with
  | zero =>
    ext i j
    rw [pow_zero, pow_zero, oMat.toMatrix, Matrix.one_apply]
    change (𝟙 (oMat o ι) : oMat o ι ⟶ oMat o ι) i j = _
    by_cases hij : i = j
    · subst hij; rw [Mat_.id_apply_self, ite_eq_left rfl]; rfl
    · rw [Mat_.id_apply_of_ne _ _ _ hij, ite_eq_right hij]
  | succ K ih =>
    rw [pow_succ, End.mul_def, oMat_comp_toMatrix hcomm, ih, pow_succ']

include hcomm in
/-- An endomorphism of `o^{⊕ ι}` whose entries are nilpotent is nilpotent. -/
theorem oMat_isNilpotent_of_entries {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : End (oMat o ι)) (hf : ∀ i j, IsNilpotent (R := End o) (oMat.toMatrix f i j)) :
    IsNilpotent f := by
  let := endCommRing hcomm
  obtain ⟨K, hK⟩ := matrix_isNilpotent_of_entries (oMat.toMatrix f) hf
  refine ⟨K, ?_⟩
  have := oMat_pow_toMatrix hcomm f K
  rw [hK] at this
  refine Mat_.hom_ext _ _ fun i j => ?_
  exact congrFun (congrFun this i) j

end OMat

end Categorification.TwoRep
