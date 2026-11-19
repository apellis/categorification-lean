/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigmaPresented
import Categorification.Diagrams.KLR.Comparison
import Categorification.Diagrams.KL3.Upward

/-!
# The signed reflection of diagrams is the vertical flip `σ`

Khovanov–Lauda, arXiv:0803.4121v2 (KL I), end of §2.1. On the diagrammatic KLR algebra
`DiagR = ⨁_{i, j} Hom(word i, word j)`, the signed reflection of the presented KLR category
(`KSig.ksP`), with the sequences reindexed by `Seq.rev`, is the vertical flip `σ` of the KLR
algebra (`KLRAlgebra.sigma`) under the identification `diagREquiv`
(`KSig.ksMat_comp_toDiagFree`). It is used in the proof of Webster, arXiv:1309.3796v3,
Lemma 4.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams Presentation KLR.Diagram MatEnd

universe w u

section Reindex

variable (k : Type*) [CommRing k] {𝒞 𝒟 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  [Category 𝒟] [Preadditive 𝒟] [Linear k 𝒟] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear functor and a reindexing of the summands induce an algebra homomorphism of
matrix algebras of morphisms: `(f i j) ↦ (F (f (σ i) (σ j)))`, up to the given identifications
of objects. -/
def matEndReindex (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞) (Z' : ι → 𝒟)
    (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) : MatEnd Z →ₐ[k] MatEnd Z' where
  toFun f i j := eqToHom (h i).symm ≫ F.map (f (σ i) (σ j)) ≫ eqToHom (h j)
  map_one' := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_of_ne hij, one_apply_of_ne (σ.injective.ne hij)]
  map_mul' f g := by
    ext i l
    simp only [mul_apply, Functor.map_sum, Functor.map_comp, Preadditive.sum_comp,
      Preadditive.comp_sum]
    rw [← σ.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, MatEnd.smul_apply, Functor.map_smul,
      Linear.smul_comp, Linear.comp_smul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_of_ne hij, one_apply_of_ne (σ.injective.ne hij)]

theorem matEndReindex_apply (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞) (Z' : ι → 𝒟)
    (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) (f : MatEnd Z) (i j : ι) :
    matEndReindex k F Z Z' σ h f i j = eqToHom (h i).symm ≫ F.map (f (σ i) (σ j)) ≫
      eqToHom (h j) := rfl

theorem matEndReindex_single (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞)
    (Z' : ι → 𝒟) (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) (a c : ι)
    (f : Z (σ a) ⟶ Z (σ c)) :
    matEndReindex k F Z Z' σ h (single (σ a) (σ c) f) =
      single a c (eqToHom (h a).symm ≫ F.map f ≫ eqToHom (h c)) := by
  ext i j
  rw [matEndReindex_apply]
  by_cases hij : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := hij; simp
  · rw [single_apply_of_ne _ hij, single_apply_of_ne, F.map_zero, Limits.zero_comp,
      Limits.comp_zero]
    exact fun h' => hij ⟨σ.injective h'.1, σ.injective h'.2⟩

theorem matEndReindex_single' (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞)
    (Z' : ι → 𝒟) (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) (a c : ι) {b : ι}
    (hc : σ c = b) (f : Z (σ a) ⟶ Z b) :
    matEndReindex k F Z Z' σ h (single (σ a) b f) =
      single a c (eqToHom (h a).symm ≫ F.map f ≫
        eqToHom ((congrArg (fun t => F.obj (Z t)) hc).symm.trans (h c))) := by
  subst hc; exact matEndReindex_single k F Z Z' σ h a c f

end Reindex

namespace KSig

variable {I : Type u} [DecidableEq I] {k : Type w} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

omit [DecidableEq I] in
theorem word_rev (i : KLR.Seq ν) : word i.rev = (word i).reverse := by
  apply List.ext_getElem
  · simp
  · intro t h₁ h₂
    simp only [getElem_word, List.getElem_reverse, length_word, KLR.Seq.rev_apply]
    refine congrArg i.1 (Fin.ext ?_)
    simp only [Fin.val_rev]
    simp at h₁
    omega

/-- The reversal of sequences as a permutation. -/
def revPerm : KLR.Seq ν ≃ KLR.Seq ν :=
  ⟨KLR.Seq.rev, KLR.Seq.rev, KLR.Seq.rev_rev, KLR.Seq.rev_rev⟩

theorem ksP_obj_word (hQ : KLR.KLRSymm Q) (i : KLR.Seq ν) :
    (ksP Q hQ).obj ((KLR.Diagram.pres k Q).obj (KLR.Diagram.ob (word (revPerm i)))) =
      (KLR.Diagram.pres k Q).obj (KLR.Diagram.ob (word i)) := by
  rw [ksP_obj]
  exact congrArg _ (KLR.Diagram.obj_ext (by simp [kobj, revPerm, word_rev]))

variable (k Q ν) in
/-- **The signed reflection on the diagrammatic KLR algebra**: `ksP` applied entrywise,
with the sequences reversed. -/
def ksMat (hQ : KLR.KLRSymm Q) : DiagR k Q ν →ₐ[k] DiagR k Q ν :=
  matEndReindex k (ksP Q hQ) _ _ revPerm (ksP_obj_word hQ)

end KSig

end Categorification.KL3.Diagram

end
