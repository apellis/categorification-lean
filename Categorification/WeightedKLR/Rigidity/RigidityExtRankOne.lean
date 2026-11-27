/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ExtremalNorm
import Categorification.WeightedKLR.RedStrands.SimpleTopGrading

/-!
# Rank-one blocks with a projective of norm one

Webster, arXiv:1309.3796v3, §7.1, Proposition 7.2 and Lemma 7.3. Let `A` be a graded algebra over
a field whose split Grothendieck group has rank one, and let `P = A e` be a graded projective with
graded endomorphism series one. Then

* every central element of `A` is a scalar (`exists_algebraMap_of_commute`), and
* every nonzero element `x` of the right ideal `e A` generates `e`: `x b = e` for some `b`
  (`exists_mul_eq_of_homGdim_eq_one`).

A finite-dimensional graded algebra whose split Grothendieck group has rank zero is zero
(`subsingleton_of_finrank_K0_eq_zero`).

Both follow from the decomposition of the regular module into shifts of the one indecomposable.
-/

noncomputable section

namespace Categorification.Graded.GProj

open Module DirectSum

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜] (P : GProj 𝒜)

omit [HasGdim 𝒜] in
private theorem comp_eq_zero_of_sumList'
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

omit [HasGdim 𝒜] in
private theorem eq_zero_of_comp_sumList
    (allIso : ∀ b : IndecClass 𝒜, Nonempty (P.carrier ≃ₗ[A] b.rep.carrier))
    {M : Type*} [AddCommGroup M] [Module A M]
    (l : List (IndecClass 𝒜 × ℤ)) (h : M →ₗ[A] (sumList l).carrier)
    (hh : ∀ f : (sumList l).carrier →ₗ[A] P.carrier, f.comp h = 0) : h = 0 := by
  induction l with
  | nil =>
    ext x
    exact Subsingleton.elim _ _
  | cons a l ih =>
    obtain ⟨e⟩ := allIso a.1
    let h' : M →ₗ[A] (a.1.rep.carrier × (sumList l).carrier) := h
    have h1 : (LinearMap.fst A a.1.rep.carrier (sumList l).carrier).comp h' = 0 := by
      have hz := hh (e.symm.toLinearMap.comp (LinearMap.fst A a.1.rep.carrier (sumList l).carrier))
      ext x
      have := LinearMap.congr_fun hz x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
      exact (LinearEquiv.map_eq_zero_iff e.symm).mp this
    have h2 : (LinearMap.snd A a.1.rep.carrier (sumList l).carrier).comp h' = 0 :=
      ih _ fun f => hh (f.comp (LinearMap.snd A a.1.rep.carrier (sumList l).carrier))
    ext x
    change h' x = 0
    exact Prod.ext (LinearMap.congr_fun h1 x) (LinearMap.congr_fun h2 x)

private theorem allIso_of_rank_one
    (rank_one : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 1)
    (hn : homGdim P P = 1) (b' : IndecClass 𝒜) :
    Nonempty (P.carrier ≃ₗ[A] b'.rep.carrier) := by
  have hcard : Nat.card (IndecClass 𝒜) = 1 :=
    (Module.finrank_eq_nat_card_basis (K0.indecBasis 𝒜)).symm.trans rank_one
  have := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨b, a, ⟨e⟩⟩ := IndecClass.exists_iso_rep_shift (isIndec_of_norm_one P hn)
  obtain rfl := Subsingleton.elim b b'
  exact ⟨e.toLinearEquiv⟩

/-- In a rank-one block with a projective of norm one, every central element is a scalar
(Webster, arXiv:1309.3796v3, §7.1, proof of Lemma 7.3). -/
theorem exists_algebraMap_of_commute
    (rank_one : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 1)
    (hn : homGdim P P = 1) (z : A) (hz : ∀ y : A, z * y = y * z) :
    ∃ c : k, z = algebraMap k A c := by
  let m : P.carrier →ₗ[A] P.carrier :=
    { toFun p := z • p
      map_add' p q := smul_add z p q
      map_smul' a p := by
        change z • a • p = a • z • p
        rw [smul_smul, smul_smul, hz a] }
  obtain ⟨c, hc⟩ := exists_scalar_of_homGdim_eq_one P hn m
  refine ⟨c, ?_⟩
  let g : A →ₗ[A] A := LinearMap.toSpanSingleton A A (z - algebraMap k A c)
  have hg : ∀ f : P.carrier →ₗ[A] A, g.comp f = 0 := by
    intro f
    ext p
    change f p * (z - algebraMap k A c) = 0
    have hmp : z • p = c • p := LinearMap.congr_fun hc p
    have hcomm : f p * (z - algebraMap k A c) = (z - algebraMap k A c) * f p := by
      rw [mul_sub, sub_mul, hz, Algebra.commutes]
    rw [hcomm, ← smul_eq_mul, ← f.map_smul, sub_smul, hmp, algebraMap_smul, sub_self, map_zero]
  obtain ⟨l, ⟨u⟩⟩ := (regular 𝒜).exists_iso_sumList
  have hz0 := comp_eq_zero_of_sumList' P (allIso_of_rank_one P rank_one hn) g hg l
    u.symm.toLinearEquiv.toLinearMap
  have h := LinearMap.congr_fun hz0 (u (1 : A))
  let v : A ≃ₗ[A] (sumList l).carrier := u.toLinearEquiv
  have h1 : g (1 : A) = 0 := (congrArg g (v.symm_apply_apply (1 : A))).symm.trans h
  simpa [g, sub_eq_zero] using h1

/-- In a rank-one block, every nonzero element of the right ideal `e A` of a norm-one projective
`A e` generates `e` on the right (Webster, arXiv:1309.3796v3, §7.1, proof of Lemma 7.3). -/
theorem exists_mul_eq_of_homGdim_eq_one {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
    (a : ℤ) (rank_one : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 1)
    (hn : homGdim ((ofIdempotent e he he0).shift a) ((ofIdempotent e he he0).shift a) = 1)
    (x : A) (hx : e * x = x) (hx0 : x ≠ 0) : ∃ b : A, x * b = e := by
  let P := (ofIdempotent e he he0).shift a
  let val : P.carrier → A := fun p => ((show leftIdeal e from p) : A)
  have hval_smul (c : A) (p : P.carrier) : val (c • p) = c * val p := rfl
  have hval_add (p q : P.carrier) : val (p + q) = val p + val q := rfl
  let ge : P.carrier := show leftIdeal e from ⟨e, he.eq⟩
  have hge : val ge = e := rfl
  let g : P.carrier →ₗ[A] A :=
    { toFun p := val p * x
      map_add' p q := by rw [hval_add, add_mul]
      map_smul' c p := by rw [hval_smul, mul_assoc]; rfl }
  have hg : g ≠ 0 := by
    intro h
    have h1 := LinearMap.congr_fun h ge
    change val ge * x = 0 at h1
    rw [hge, hx] at h1
    exact hx0 h1
  obtain ⟨l, ⟨u⟩⟩ := (regular 𝒜).exists_iso_sumList
  let v : A ≃ₗ[A] (sumList l).carrier := u.toLinearEquiv
  have hex : ∃ f : (sumList l).carrier →ₗ[A] P.carrier, f.comp (v.toLinearMap.comp g) ≠ 0 := by
    by_contra! hall
    have := eq_zero_of_comp_sumList P (allIso_of_rank_one P rank_one hn) l _ hall
    apply hg
    ext p
    have h := LinearMap.congr_fun this p
    change v (g p) = 0 at h
    simpa using h
  obtain ⟨f, hf⟩ := hex
  obtain ⟨c, hc⟩ := exists_scalar_of_homGdim_eq_one P hn (f.comp (v.toLinearMap.comp g))
  have hc0 : c ≠ 0 := fun hz => hf (by simpa [hz] using hc)
  let F : A →ₗ[A] P.carrier := f.comp v.toLinearMap
  have hF (y : A) : val (F y) = y * val (F 1) := by
    have : F y = y • F 1 := by rw [← F.map_smul, smul_eq_mul, mul_one]
    rw [this, hval_smul]
  refine ⟨c⁻¹ • val (F 1), ?_⟩
  have h := LinearMap.congr_fun hc ge
  change F (val ge * x) = c • ge at h
  have h' := congrArg val h
  rw [hF, hge, hx] at h'
  have hcs : val (c • ge) = c • e := by
    rw [← hge, ← algebraMap_smul A c ge, hval_smul, Algebra.smul_def]
  rw [hcs] at h'
  rw [mul_smul_comm, h', smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- A finite-dimensional graded algebra whose split Grothendieck group has rank zero is zero. -/
theorem subsingleton_of_finrank_K0_eq_zero [Module.Finite k A]
    (h : finrank (LaurentPolynomial ℤ) (K0 𝒜) = 0) : Subsingleton A := by
  have := Stendhal.finite_indec (𝒜 := 𝒜)
  have hcard : Nat.card (IndecClass 𝒜) = 0 :=
    (Module.finrank_eq_nat_card_basis (K0.indecBasis 𝒜)).symm.trans h
  have hempty : IsEmpty (IndecClass 𝒜) := (Finite.card_eq_zero_iff).mp hcard
  obtain ⟨l, ⟨u⟩⟩ := (regular 𝒜).exists_iso_sumList
  cases l with
  | nil =>
    let v : A ≃ₗ[A] (sumList ([] : List (IndecClass 𝒜 × ℤ))).carrier := u.toLinearEquiv
    exact v.injective.subsingleton
  | cons a l => exact hempty.elim a.1

end Categorification.Graded.GProj
