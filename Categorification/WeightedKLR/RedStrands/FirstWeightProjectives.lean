/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BoundaryCharacters
import Categorification.WeightedKLR.RedStrands.Projectives
import Categorification.KLR.Examples.NonInteracting
import Categorification.KLR.Concat
import Categorification.Algebra.Graded.KrullSchmidt

/-!
# Projectives in the first black weight

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36 and Theorem 4.38, restricted to
one black strand. With positive red multiplicities at its colour, each surviving
ordered boundary gives an indecomposable graded projective.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded TypeA Equiv StendhalAlgebraAllOrders
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ} {i : I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "𝕋" => TensorProductAlgebra k Q Λ (Singleton.singleton i : Multiset I)
local notation "𝒜" => tensorProductGrade G (Singleton.singleton i : Multiset I)
local notation "ρ" => canWord (Multiset.card μ)
local notation "S" => {s : Seq μ // IsRedOrdered s ∧ ¬ IsViolated s}

omit [DecidableEq I] in
private theorem word_spec (w : Perm (Fin (Multiset.card μ))) :
    IsReduced (Multiset.card μ) (ρ w) ∧ wordProd _ (ρ w) = w :=
  ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

private theorem first_hasGdim (hX : ∀ a, 0 < G.degX a) : HasGdim 𝒜 := by
  let B := tensorProductBasis (ν := {i}) word_spec Q Λ
  let deg := fun b : tensorProductBasisIndices (ν := {i}) word_spec Q Λ => G.stdDeg ρ b.1.1
  have hb : ∀ b, B b ∈ 𝒜 (deg b) := fun b => by
    rw [show B b = tensorProductTerm word_spec Q Λ b.1 from tensorProductBasis_apply ..]
    exact tensorProductTerm_mem_grade word_spec G b.1
  have h := hasGdim_inf_span 𝒜 deg hb Set.univ (fun d => by
    simpa [deg] using ((G.finite_stdDeg_eq ρ hX d).preimage Subtype.val_injective.injOn).preimage
      Subtype.val_injective.injOn) (by
      rw [Set.image_univ]
      exact (G.bddBelow_stdDeg ρ (fun a => (hX a).le) Set.univ).mono
        (by rintro _ ⟨b, rfl⟩; exact ⟨b.1.1, Set.mem_univ _, rfl⟩))
  simpa [Set.image_univ, B.span_eq] using h

private abbrev E (s : Seq μ) (hs : IsRedOrdered s) : 𝕋 :=
  TensorProductAlgebra.mk Q Λ {i} (StendhalAlgebra.e s hs)

private theorem idem (s : Seq μ) (hs : IsRedOrdered s) : IsIdempotentElem (E (Q := Q) (Λ := Λ) s hs) := by
  apply IsIdempotentElem.map
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.e s =
    (StendhalAlgebraAllOrders.e s : StendhalAlgebraAllOrders k Q Λ {i})
  simp [e_mul_e]

private theorem nontrivial_proj (hΛ : ∀ r, 0 < Λ r i) (s : S) :
    Nontrivial (sequenceProj G s.1 s.2.1).carrier := by
  let e : 𝕋 := E s.1 s.2.1
  have he : e ≠ 0 := by
    intro h
    have heval := congrArg (boundaryCharacter Q Λ hΛ s.1 s.2.1 s.2.2) h
    simp [e, E] at heval
  exact ⟨⟨(⟨e, (idem s.1 s.2.1).eq⟩ : leftIdeal e), 0, fun h => he (congrArg Subtype.val h)⟩⟩

private theorem diagonal_hom_le (hX : ∀ a, 0 < G.degX a) (s : S) :
    Module.finrank k (homGrade 𝕋 (sequenceProj G s.1 s.2.1).grading
      (sequenceProj G s.1 s.2.1).grading 0) ≤ 1 := by
  rw [finrank_homGrade_sequenceProj G word_spec hX]
  suffices h : Subsingleton {b : tensorProductBasisIndices (ν := {i}) word_spec Q Λ |
      hasEndpoints word_spec s.1 s.1 b ∧ G.stdDeg ρ b.1.1 = 0} by
    let := h
    exact Finite.card_le_one_iff_subsingleton.2 h
  have index_eq (b : tensorProductBasisIndices (ν := {i}) word_spec Q Λ)
      (hb : hasEndpoints word_spec s.1 s.1 b ∧ G.stdDeg ρ b.1.1 = 0) :
      b.1.1 = (s.1, 1, 0) := by
    obtain ⟨⟨hs, hw⟩, hd⟩ := hb
    have hnodup : Multiset.Nodup μ := by simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
    have hperm : b.1.1.2.1 = 1 :=
      NonInteracting.smul_left_injective hnodup b.1.1.1 (by rw [one_smul, hw, hs])
    have hnil : ρ 1 = [] := List.length_eq_zero_iff.mp (by rw [length_canWord, length_one])
    simp only [GradingDatum.stdDeg, hperm, hnil, GradingDatum.degW, zero_add] at hd
    refine Prod.ext hs (Prod.ext hperm (Finsupp.ext fun a => ?_))
    by_contra h
    have hn : b.1.1.2.2 a ≠ 0 := h
    have hle := Finsupp.le_weight_of_ne_zero (fun u => (hX (b.1.1.1.lbl u)).le) hn
    rw [hd] at hle
    exact (hX _).not_ge hle
  exact ⟨fun x y => Subtype.ext (Subtype.ext (Subtype.ext ((index_eq x.1 x.2).trans (index_eq y.1 y.2).symm)))⟩

/-- The degree-zero endomorphism algebra of a surviving sequence projective has
dimension one. This is the diagonal first-black-weight case of the diagram
calculation in Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36. -/
theorem finrank_endZero_sequenceProj (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i) (s : S) :
    Module.finrank k (endZero 𝕋 (sequenceProj G s.1 s.2.1).grading) = 1 := by
  let := first_hasGdim G hX (i := i)
  let := nontrivial_proj G hΛ s
  have h₁ := GProj.finrank_endZero_pos (P := sequenceProj G s.1 s.2.1)
  have h₂ := LinearMap.finrank_le_finrank_of_injective
    (endZeroToHomGrade_injective (A := 𝕋) (sequenceProj G s.1 s.2.1).grading)
  exact le_antisymm (h₂.trans (diagonal_hom_le G hX s)) h₁

/-- With positive red multiplicities at the black colour, each nonviolated
principal projective is indecomposable (Webster, arXiv:1309.3796v2,
§4.7, first-weight consequence of Lemma 4.36). -/
theorem sequenceProj_isIndec (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i) (s : S) :
    (sequenceProj G s.1 s.2.1).IsIndec 𝕋 := by
  let := nontrivial_proj G hΛ s
  let R := endZero 𝕋 (sequenceProj G s.1 s.2.1).grading
  have hsurj : Function.Surjective (algebraMap k R) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : R) one_ne_zero).1
      (finrank_endZero_sequenceProj G hX hΛ s) x
    exact ⟨c, by rwa [Algebra.algebraMap_eq_smul_one]⟩
  refine ⟨inferInstance, fun f hf hid => ?_⟩
  obtain ⟨c, hc⟩ := hsurj ⟨f, hf⟩
  have hc' : IsIdempotentElem c := (algebraMap k R).injective (by
    rw [map_mul, hc]
    exact Subtype.ext hid.eq)
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hc' with rfl | rfl
  · exact Or.inl (congrArg Subtype.val ((map_zero _).symm.trans hc)).symm
  · exact Or.inr (congrArg Subtype.val ((map_one _).symm.trans hc)).symm

private abbrev Ordered := {s : Seq μ // IsRedOrdered s}

open Classical in
private theorem sum_boundary :
    ∑ s : Ordered (ℓ := ℓ) (i := i), (E s.1 s.2 : 𝕋) = 1 := by
  have h : (∑ s : Ordered (ℓ := ℓ) (i := i), StendhalAlgebra.e s.1 s.2 :
      StendhalAlgebra k Q Λ {i}) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : Ordered (ℓ := ℓ) (i := i), StendhalAlgebraAllOrders.e s.1) =
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ {i}
    exact (Finset.sum_subtype _ (fun s => by simp) _).symm
  simpa only [map_sum, map_one] using congrArg (TensorProductAlgebra.mk Q Λ {i}) h

private theorem boundary_zero (s : Ordered (ℓ := ℓ) (i := i)) (hv : IsViolated s.1) :
    (E s.1 s.2 : 𝕋) = 0 := by
  change (StendhalAlgebra.violatedIdeal k Q Λ {i}).ringCon.mk' _ = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span ⟨s.1, s.2, hv, rfl⟩

/-- Each indecomposable in the first lowering block is a shift of a surviving
principal projective. A simple quotient has a nonzero boundary-idempotent
component because the ordered idempotents sum to one. -/
theorem exists_iso_sequenceProj_shift (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i)
    (P : GProj 𝒜) (hP : P.IsIndec 𝕋) :
    ∃ (s : S) (d : ℤ), Nonempty (P.Iso ((sequenceProj G s.1 s.2.1).shift d)) := by
  classical
  let := first_hasGdim G hX (i := i)
  let := hP.nontrivial
  obtain ⟨N, f, hN, hf, hf0, _⟩ := P.exists_isGradedSimple_quotient
  let := hN.nontrivial
  let := N.gradedSMul
  obtain ⟨d, v, hv, hv0⟩ := exists_mem_ne_zero N.grading
  obtain ⟨s, hs⟩ : ∃ s : Ordered (ℓ := ℓ) (i := i), (E s.1 s.2 : 𝕋) • v ≠ 0 := by
    by_contra! h
    apply hv0
    calc
      v = (1 : 𝕋) • v := (one_smul _ _).symm
      _ = _ := by rw [← sum_boundary (Q := Q) (Λ := Λ) (i := i), Finset.sum_smul, Finset.sum_eq_zero (fun j _ => h j)]
  have hnv : ¬ IsViolated s.1 := fun h => hs (by rw [boundary_zero _ h, zero_smul])
  let t : S := ⟨s.1, s.2, hnv⟩
  let e : 𝕋 := E s.1 s.2
  let g : (leftIdeal e) →ₗ[𝕋] N.carrier := (LinearMap.toSpanSingleton 𝕋 N.carrier v).comp (leftIdeal e).subtype
  have hg : PreservesGrading ((sequenceProj G t.1 t.2.1).shift d).grading N.grading g := by
    intro n x hx
    let y : leftIdeal e := x
    have hx' : (y : 𝕋) ∈ 𝒜 (n-d) := hx
    have hm : (y : 𝕋) • v ∈ N.grading (n - d + d) := SetLike.GradedSMul.smul_mem hx' hv
    change (y : 𝕋) • v ∈ N.grading n
    simpa only [sub_add_cancel] using hm
  have hg0 : g ≠ 0 := fun h => hs (LinearMap.congr_fun h (⟨e, (idem s.1 s.2).eq⟩ : leftIdeal e))
  exact ⟨t, d, hP.nonempty_iso ((sequenceProj_isIndec G hX hΛ t).shift d) hN hf hf0 hg hg0⟩

/-- Distinct surviving words give nonisomorphic principal projectives even after a grading shift.
Their scalar boundary characters distinguish the underlying ungraded projectives. -/
theorem eq_of_sequenceProj_iso_shift (hΛ : ∀ r, 0 < Λ r i) (s t : S) {d : ℤ}
    (F : (sequenceProj G s.1 s.2.1).Iso ((sequenceProj G t.1 t.2.1).shift d)) : s = t := by
  classical
  by_contra hst
  let e : 𝕋 := E s.1 s.2.1
  let f : 𝕋 := E t.1 t.2.1
  let x : leftIdeal e := ⟨e, (idem s.1 s.2.1).eq⟩
  let y : leftIdeal f := ⟨f, (idem t.1 t.2.1).eq⟩
  let U : leftIdeal e ≃ₗ[𝕋] leftIdeal f := F.toLinearEquiv
  let χ := boundaryCharacter Q Λ hΛ s.1 s.2.1 s.2.2
  have hχe : χ e = 1 := by simp [χ, e, E]
  have hχf : χ f = 0 := by
    simp [χ, f, E, show t.1 ≠ s.1 from fun h => hst (Subtype.ext h.symm)]
  have hx : χ (U x : 𝕋) = 0 := by
    have hm : (U x : 𝕋) * f = (U x : 𝕋) := (U x).2
    rw [← hm, map_mul, hχf, mul_zero]
  have hy : (U x : 𝕋) • y = U x := Subtype.ext (U x).2
  have hh := congrArg (fun z : leftIdeal e => χ (z : 𝕋)) (U.symm.map_smul (U x : 𝕋) y)
  rw [hy, U.symm_apply_apply] at hh
  change χ e = χ ((U x : 𝕋) * (U.symm y : 𝕋)) at hh
  rw [map_mul, hx, zero_mul, hχe] at hh
  exact one_ne_zero hh

/-- For positive multiplicities at the one black colour, the surviving ordered
words index the indecomposables up to shift in Webster's projective category
(arXiv:1309.3796v2, §4.7, first-weight case of Theorem 4.38). -/
def sequenceProjIndecEquiv (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i) :
    S ≃ GProj.IndecClass 𝒜 :=
  Equiv.ofBijective (fun s => Quotient.mk (GProj.indecSetoid 𝒜)
    ⟨sequenceProj G s.1 s.2.1, sequenceProj_isIndec G hX hΛ s⟩) (by
    constructor
    · intro s t h
      obtain ⟨d, ⟨F⟩⟩ := Quotient.exact h
      exact eq_of_sequenceProj_iso_shift G hΛ s t F
    · intro b
      obtain ⟨s, d, ⟨F⟩⟩ := exists_iso_sequenceProj_shift G hX hΛ b.rep b.isIndec_rep
      refine ⟨s, ?_⟩
      rw [← Quotient.out_eq b]
      exact (Quotient.sound (s := GProj.indecSetoid 𝒜) (a := b.out)
        (b := ⟨sequenceProj G s.1 s.2.1, sequenceProj_isIndec G hX hΛ s⟩) ⟨d, ⟨F⟩⟩).symm)

private theorem exists_sequenceProjBasis (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i) :
    ∃ B : Module.Basis S (LaurentPolynomial ℤ) (K0 𝒜),
      ∀ s, B s = K0.of (sequenceProj G s.1 s.2.1) := by
  let := first_hasGdim G hX (i := i)
  let e := sequenceProjIndecEquiv G hX hΛ
  have hs (s : S) : ∃ d : ℤ, Nonempty ((sequenceProj G s.1 s.2.1).Iso ((e s).rep.shift d)) :=
    (GProj.indecSetoid 𝒜).symm (Quotient.mk_out (s := GProj.indecSetoid 𝒜)
      ⟨sequenceProj G s.1 s.2.1, sequenceProj_isIndec G hX hΛ s⟩)
  choose d hd using hs
  let u (s : S) : (LaurentPolynomial ℤ)ˣ := (LaurentPolynomial.isUnit_T (R := ℤ) (d s)).unit
  refine ⟨((K0.indecBasis 𝒜).reindex e.symm).unitsSMul u, fun s => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, Equiv.symm_symm, K0.indecBasis_apply]
  change (↑(u s) : LaurentPolynomial ℤ) • K0.of (e s).rep = _
  rw [(LaurentPolynomial.isUnit_T (R := ℤ) (d s)).unit_spec, K0.T_smul_of]
  exact (K0.of_eq_of_iso (hd s).some).symm

/-- The classes of the principal projectives are a Laurent-polynomial
basis in the first lowering block of Webster, arXiv:1309.3796v2, Theorem 4.38,
when every red multiplicity at the black colour is positive. -/
def sequenceProjBasis (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i) :
    Module.Basis S (LaurentPolynomial ℤ) (K0 𝒜) :=
  (exists_sequenceProjBasis G hX hΛ).choose

@[simp] theorem sequenceProjBasis_apply (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i) (s : S) :
    sequenceProjBasis G hX hΛ s = K0.of (sequenceProj G s.1 s.2.1) :=
  (exists_sequenceProjBasis G hX hΛ).choose_spec s

end Categorification.Stendhal.FirstWeight
