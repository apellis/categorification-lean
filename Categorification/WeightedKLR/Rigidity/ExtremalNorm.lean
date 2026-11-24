/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Duality
import Categorification.Algebra.Graded.KrullSchmidtUnique

/-!
# Projectives of norm one in a rank-one block

Webster, arXiv:1309.3796v2, §7.1, proof of Proposition 7.2, p. 70.
The graded Hom norm determines all endomorphisms after forgetting the
grading. In a rank-one block, the regular projective is a finite direct
sum of shifts of the unique indecomposable. Together these facts imply
simplicity for a norm-one projective. A mixed Hom in degree zero fixes
the grading in a comparison of two such projectives.
-/

noncomputable section


namespace Categorification.Graded.GProj

open Module DirectSum

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜] (P : GProj 𝒜)

private theorem endGrade_finrank_of_norm_one (hn : homGdim P P = 1) (d : ℤ) :
    finrank k (homGrade A P.grading P.grading d) = if d = 0 then 1 else 0 := by
  have h := congrArg (fun z : LaurentSeries ℤ => z.coeff d) hn
  change (gdim _).coeff d = (1 : LaurentSeries ℤ).coeff d at h
  rw [coeff_gdim, HahnSeries.coeff_one] at h
  split at h <;> simp_all

private theorem nontrivial_of_norm_one (hn : homGdim P P = 1) : Nontrivial P.carrier := by
  by_contra! hs
  let := hs
  have h := endGrade_finrank_of_norm_one P hn 0
  have hsub : Subsingleton (homGrade A P.grading P.grading 0) :=
    ⟨fun f g => Subtype.ext (LinearMap.ext fun _ => Subsingleton.elim _ _)⟩
  rw [Module.finrank_zero_iff.mpr hsub] at h
  simp at h

/-- A norm-one projective has only scalar endomorphisms after forgetting the grading. -/
theorem exists_scalar_of_homGdim_eq_one (hn : homGdim P P = 1) (f : P.carrier →ₗ[A] P.carrier) :
    ∃ c : k, f = c • (LinearMap.id : P.carrier →ₗ[A] P.carrier) := by
  let := nontrivial_of_norm_one P hn
  let H := homGrade A P.grading P.grading
  let := (isInternal_homGrade 𝒜 P.grading P.grading).chooseDecomposition
  have hId : (LinearMap.id : P.carrier →ₗ[A] P.carrier) ∈ H 0 := by
    intro d x hx
    simpa only [LinearMap.id_apply, add_zero] using hx
  let i : H 0 := ⟨LinearMap.id, hId⟩
  have hi : i ≠ 0 := fun h => one_ne_zero (α := Module.End A P.carrier) (congrArg Subtype.val h)
  induction f using Decomposition.inductionOn H with
  | zero => exact ⟨0, (zero_smul _ _).symm⟩
  | add f g hf hg =>
    obtain ⟨c, rfl⟩ := hf
    obtain ⟨d, rfl⟩ := hg
    exact ⟨c + d, (add_smul ..).symm⟩
  | @homogeneous d f =>
    by_cases hd : d = 0
    · subst d
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' i hi).1
        (by simpa [H] using endGrade_finrank_of_norm_one P hn 0) f
      exact ⟨c, congrArg Subtype.val hc.symm⟩
    · have hz : finrank k (H d) = 0 := by simpa [hd] using endGrade_finrank_of_norm_one P hn d
      have : Subsingleton (H d) := Module.finrank_zero_iff.mp hz
      exact ⟨0, (congrArg Subtype.val (Subsingleton.elim f 0)).trans (zero_smul _ _).symm⟩

/-- A projective with graded endomorphism series one is indecomposable. -/
theorem isIndec_of_norm_one (hn : homGdim P P = 1) : P.IsIndec A := by
  refine ⟨nontrivial_of_norm_one P hn, fun e _ he => ?_⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_homGdim_eq_one P hn e
  by_cases h0 : c = 0
  · left
    simpa [h0] using hc
  · right
    have hsurj : Function.Surjective e := fun y => ⟨c⁻¹ • y, by simp [hc, smul_smul, h0]⟩
    ext x
    obtain ⟨v, rfl⟩ := hsurj x
    exact LinearMap.congr_fun he v

omit [HasGdim 𝒜] in
private theorem comp_eq_zero_of_sumList
    (allIso : ∀ b : IndecClass 𝒜, Nonempty (P.carrier ≃ₗ[A] b.rep.carrier))
    {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A M]
    (g : M →ₗ[A] N) (hg : ∀ f : P.carrier →ₗ[A] M, g.comp f = 0)
    (l : List (IndecClass 𝒜 × ℤ)) (u : (sumList l).carrier →ₗ[A] M) : g.comp u = 0 := by
  induction l with
  | nil =>
    ext x
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  | cons a l ih =>
    change (g.comp u : (a.1.rep.carrier × (sumList l).carrier) →ₗ[A] N) = 0
    apply LinearMap.prod_ext
    · obtain ⟨e⟩ := allIso a.1
      let f := u.comp (LinearMap.inl A a.1.rep.carrier (sumList l).carrier)
      ext x
      have h := LinearMap.congr_fun (hg (f.comp e.toLinearMap)) (e.symm x)
      change g (u (e (e.symm x), 0)) = 0 at h
      rw [e.apply_symm_apply] at h
      exact h
    · exact ih (u.comp (LinearMap.inr A a.1.rep.carrier (sumList l).carrier))

/-- In a block with a unique indecomposable up to shift, a projective of
graded Hom norm one is simple even after forgetting its grading. -/
theorem isSimpleModule_of_homGdim_eq_one
    (rank_one : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 1)
    (hn : homGdim P P = 1) : IsSimpleModule A P.carrier := by
  have hcard : Nat.card (IndecClass 𝒜) = 1 :=
    (Module.finrank_eq_nat_card_basis (K0.indecBasis 𝒜)).symm.trans rank_one
  have := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨b, a, ⟨e⟩⟩ := IndecClass.exists_iso_rep_shift (isIndec_of_norm_one P hn)
  have allIso (b' : IndecClass 𝒜) : Nonempty (P.carrier ≃ₗ[A] b'.rep.carrier) := by
    obtain rfl := Subsingleton.elim b b'
    exact ⟨e.toLinearEquiv⟩
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨nontrivial_of_norm_one P hn, ?_⟩
  intro x hx
  let g := LinearMap.toSpanSingleton A P.carrier x
  have witness : ∃ f : P.carrier →ₗ[A] A, g.comp f ≠ 0 := by
    by_contra! hall
    obtain ⟨l, ⟨u⟩⟩ := (regular 𝒜).exists_iso_sumList
    have hz := comp_eq_zero_of_sumList P allIso g hall l u.symm.toLinearEquiv.toLinearMap
    have h := LinearMap.congr_fun hz (u (1 : A))
    let v : A ≃ₗ[A] (sumList l).carrier := u.toLinearEquiv
    have h1 : g (1 : A) = 0 := (congrArg g (v.symm_apply_apply (1 : A))).symm.trans h
    exact hx (by simpa [g] using h1)
  obtain ⟨f, hf⟩ := witness
  obtain ⟨c, hc⟩ := exists_scalar_of_homGdim_eq_one P hn (g.comp f)
  have hc0 : c ≠ 0 := fun hz => hf (by simpa [hz] using hc)
  intro y
  exact ⟨f (c⁻¹ • y), by simpa [g, smul_smul, hc0] using LinearMap.congr_fun hc (c⁻¹ • y)⟩

/-- A nonzero degree-zero coefficient of the mixed Hom pairing identifies the
graded lifts of two norm-one projectives in a rank-one block. -/
theorem nonempty_iso_of_homGdim_coeff_zero (Q : GProj 𝒜)
    (rank_one : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 1)
    (hP : homGdim P P = 1) (hQ : homGdim Q Q = 1) (hPQ : (homGdim P Q).coeff 0 ≠ 0) :
    Nonempty (P.Iso Q) := by
  have := isSimpleModule_of_homGdim_eq_one P rank_one hP
  have := isSimpleModule_of_homGdim_eq_one Q rank_one hQ
  change (gdim (homGrade A P.grading Q.grading)).coeff 0 ≠ 0 at hPQ
  rw [coeff_gdim] at hPQ
  have pos : 0 < finrank k (homGrade A P.grading Q.grading 0) := by omega
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp pos
  refine ⟨GradedEquiv.ofBijective (f := f.val) ?_ (LinearMap.bijective_of_ne_zero ?_)⟩
  · intro d x hx
    simpa only [add_zero] using f.property hx
  · exact fun h => hf (Subtype.ext h)

end Categorification.Graded.GProj
