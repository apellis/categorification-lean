/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Monoidal
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The weighted KLR algebra of zero strands

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, proof of Theorem 2.19, p. 12. The only chamber at weight zero has
no strands and its algebra consists of scalars.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

private def zeroGalleryEval : GalleryAlgebra k Γ 0 →ₐ[k] k := by
  letI := isEmpty_strand_zero (I := I)
  letI := isEmpty_hyp_zero (Γ := Γ)
  let f : FreeAlgebra k (Gen k Γ 0) →ₐ[k] k :=
    FreeAlgebra.lift k fun
      | .idem _ => 1
      | .poly p => MvPolynomial.isEmptyAlgEquiv k (Strand (0 : I →₀ ℕ)) p
      | .step _ _ => 0
      | .relabel _ _ => 1
  refine RingQuot.liftAlgHom k ⟨f, fun x y h => ?_⟩
  cases h with
  | wall_bigon _ _ w _ => exact isEmptyElim (Sum.inl w : Hyp Γ 0)
  | diag_bigon _ _ d _ => exact isEmptyElim (Sum.inr d : Hyp Γ 0)
  | wall_poly _ _ w _ _ => exact isEmptyElim (Sum.inl w : Hyp Γ 0)
  | diag_poly _ _ d _ _ => exact isEmptyElim (Sum.inr d : Hyp Γ 0)
  | square _ _ _ _ h _ _ _ _ _ _ _ => exact isEmptyElim h
  | hex_walls H _ _ _ => exact isEmptyElim H.h₁
  | hex_mid_diag H _ _ _ _ _ _ _ => exact isEmptyElim H.h₁
  | hex_end_diag H _ _ _ _ _ => exact isEmptyElim H.h₁
  | hex_diags H _ _ _ _ _ _ _ _ _ _ _ _ _ => exact isEmptyElim H.h₁
  | relabel_poly g C p =>
    have hg : g = 1 := Subtype.ext (Equiv.ext fun s => isEmptyElim s)
    subst g
    simp [f, fr, fp]
  | idem_mul C D => simp [f, fe, Subsingleton.elim C D]
  | idem_sum => simp [f, fe]
  | poly_C c => simp [f, fp]
  | poly_mul p q => simp only [f, fp, map_mul, FreeAlgebra.lift_ι_apply]
  | _ => simp [f, fe, fp, ft, fr]

private theorem gallery_algebraMap_zero_surjective :
    Function.Surjective (algebraMap k (GalleryAlgebra k Γ 0)) := by
  let := isEmpty_strand_zero (I := I)
  let := isEmpty_hyp_zero (Γ := Γ)
  intro a
  obtain ⟨x, rfl⟩ := mk_surjective a
  have he (C : FullChamber Γ 0) : (e C : GalleryAlgebra k Γ 0) = 1 := by
    rw [Subsingleton.elim C default, ← Fintype.sum_unique (fun C => e C), sum_e]
  induction x using FreeAlgebra.induction with
  | grade0 c => exact ⟨c, (AlgHom.commutes _ _).symm⟩
  | grade1 g =>
    cases g with
    | idem C => exact ⟨1, (map_one _).trans (he C).symm⟩
    | poly p =>
      obtain ⟨c, rfl⟩ :=
        (MvPolynomial.isEmptyAlgEquiv k (Strand (0 : I →₀ ℕ))).symm.surjective p
      refine ⟨c, ?_⟩
      rw [MvPolynomial.isEmptyAlgEquiv_symm_apply]
      exact (AlgHom.commutes (polyHom k Γ 0) c).symm
    | step C D =>
      exact ⟨0, (map_zero _).trans (t_eq_zero (fun h => isEmptyElim h)).symm⟩
    | relabel g C =>
      have hg : g = 1 := Subtype.ext (Equiv.ext fun s => isEmptyElim s)
      subst g
      exact ⟨1, (map_one _).trans ((r_one C).trans (he C)).symm⟩
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

/-- The zero-strand weighted KLR algebra consists of scalars. -/
def weightedKLRZeroEquiv : k ≃ₐ[k] WeightedKLRAlgebra k Γ 0 := by
  let i := IsIdempotentElem.cornerVal (R := k) (isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := 0))
  have hi (c : k) :
      i (algebraMap k (WeightedKLRAlgebra k Γ 0) c) = algebraMap k (GalleryAlgebra k Γ 0) c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Algebra.algebraMap_eq_smul_one]
    exact congrArg (c • ·) one_val_zero
  refine AlgEquiv.ofBijective (Algebra.ofId k (WeightedKLRAlgebra k Γ 0)) ⟨?_, ?_⟩
  · intro x y h
    have hh := congrArg i h
    change i (algebraMap k (WeightedKLRAlgebra k Γ 0) x) =
      i (algebraMap k (WeightedKLRAlgebra k Γ 0) y) at hh
    rw [hi, hi] at hh
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      congrArg (zeroGalleryEval (Γ := Γ)) hh
  · intro x
    obtain ⟨c, hc⟩ := gallery_algebraMap_zero_surjective (i x)
    exact ⟨c, Subtype.ext ((hi c).trans hc)⟩

@[simp] theorem weightedKLRZeroEquiv_apply (c : k) :
    weightedKLRZeroEquiv (Γ := Γ) c = algebraMap k (WeightedKLRAlgebra k Γ 0) c := rfl

end Categorification.WeightedKLR
