/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.KLR.CyclotomicSplit
import Mathlib.Order.Preorder.Finite

/-!
# The highest weight block of Webster's tensor product algebra

In the vacuum step of the proof of Lemma 4.36 in B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4.7,
the block with no black strands is the coefficient field. We compute this
block from Definitions 4.5–4.7 over any commutative ring. Its only red-ordered
word is the identity ordering, all dots and crossings vanish, and there are
no violated words.
-/

namespace Categorification.Stendhal

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open KLR StendhalAlgebraAllOrders

variable {I : Type*} {k : Type*} [CommRing k] {ℓ : ℕ}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ (0 : Multiset I)
local notation "A" => StendhalAlgebraAllOrders k Q Λ (0 : Multiset I)
local notation "B" => StendhalAlgebra k Q Λ (0 : Multiset I)

private theorem card_vacuum : Multiset.card μ = ℓ := by simp [stendhalWeight]

private def vacuumPos : Fin (Multiset.card μ) ≃ Fin ℓ := finCongr card_vacuum

/-- The sequence of red strands in their prescribed order, with no black strands. -/
def vacuumSeq : Seq μ :=
  ⟨Sum.inr ∘ vacuumPos, by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    simp [stendhalWeight]⟩

/-- The vacuum sequence is red ordered. -/
theorem vacuumSeq_ordered : IsRedOrdered (vacuumSeq (I := I) (ℓ := ℓ)) := by
  rintro a b r s hab ha hb
  change Sum.inr (vacuumPos a) = (Sum.inr r : I ⊕ Fin ℓ) at ha
  change Sum.inr (vacuumPos b) = (Sum.inr s : I ⊕ Fin ℓ) at hb
  rw [← Sum.inr.inj ha, ← Sum.inr.inj hb]
  exact hab

private theorem exists_red_label (s : Seq μ) (a : Fin (Multiset.card μ)) :
    ∃ r, s.lbl a = .inr r := by
  have h := s.mem a
  simpa [stendhalWeight, eq_comm] using h

private theorem vacuum_label_right (s : Seq μ) (a : Fin (Multiset.card μ)) :
    (s.lbl a).isRight := by
  obtain ⟨r, hr⟩ := exists_red_label s a
  simp [hr]

private theorem vacuum_label_injective (s : Seq μ) : Function.Injective s.lbl := by
  have hn : (Finset.univ.val.map s.lbl).Nodup := by
    rw [show Finset.univ.val.map s.lbl = μ from s.2]
    simpa [stendhalWeight] using
      (Finset.univ.nodup.map (Sum.inr_injective (α := I) (β := Fin ℓ)))
  intro a b h
  exact Multiset.inj_on_of_nodup_map hn _ (Finset.mem_univ_val _) _ (Finset.mem_univ_val _) h

private theorem eq_vacuumSeq (s : Seq μ) (hs : IsRedOrdered s) : s = vacuumSeq := by
  classical
  choose f hf using exists_red_label s
  have hm : StrictMono (f ∘ (vacuumPos (I := I) (ℓ := ℓ)).symm) := by
    intro a b hab
    exact hs _ _ _ _ hab (hf _) (hf _)
  apply Subtype.ext
  funext a
  rw [show s.1 a = Sum.inr (f a) from hf a]
  exact congrArg Sum.inr (by simpa using hm.apply_eq (x := vacuumPos a))

variable [DecidableEq I]

private theorem redOrderedIdem_zeroWeight :
    redOrderedIdem k Q Λ (0 : Multiset I) = e vacuumSeq := by
  classical
  unfold redOrderedIdem
  refine Finset.sum_eq_single vacuumSeq (fun s hs hne => ?_) (fun h => ?_)
  · exact (hne (eq_vacuumSeq s (Finset.mem_filter.1 hs).2)).elim
  · exact (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, vacuumSeq_ordered⟩)).elim

/-- The unique ordered vacuum idempotent is the unit of the vacuum block. -/
theorem vacuumSeq_mk_e :
    TensorProductAlgebra.mk Q Λ (0 : Multiset I) (StendhalAlgebra.e vacuumSeq vacuumSeq_ordered) =
      1 := by
  rw [← map_one (TensorProductAlgebra.mk Q Λ (0 : Multiset I))]
  apply congrArg (TensorProductAlgebra.mk Q Λ (0 : Multiset I))
  apply Subtype.ext
  exact (redOrderedIdem_zeroWeight Q Λ).symm

/-- There are no violated idempotents when all strands are red. -/
theorem violatedIdeal_zeroWeight : StendhalAlgebra.violatedIdeal k Q Λ (0 : Multiset I) = ⊥ := by
  apply le_antisymm _ bot_le
  apply TwoSidedIdeal.span_le.2
  rintro y ⟨s, _, ⟨h, hv⟩, _⟩
  obtain ⟨r, hr⟩ := exists_red_label s ⟨0, h⟩
  simp [hr] at hv

/-- Evaluation on the vector corresponding to the prescribed red ordering. -/
private noncomputable def vacuumGen : Gen μ → k
  | .idem s => if s = vacuumSeq then 1 else 0
  | .dot _ | .cross _ => 0

omit [DecidableEq I] in
private theorem vacuumQ (s : Seq μ) (a b : Fin (Multiset.card μ)) :
    stendhalQ Q Λ (s.lbl a) (s.lbl b) = 0 := by
  obtain ⟨r, hr⟩ := exists_red_label s a
  obtain ⟨r', hr'⟩ := exists_red_label s b
  rw [hr, hr']
  rfl

private theorem vacuumEval_rel {x y : FreeAlgebra k (Gen μ)}
    (h : Rel k Q Λ 0 x y) :
    FreeAlgebra.lift k (vacuumGen (k := k)) x = FreeAlgebra.lift k (vacuumGen (k := k)) y := by
  classical
  have hdiff (s : Seq μ) (a b : Fin (Multiset.card μ)) (h : a.val ≠ b.val) :
      s.lbl a ≠ s.lbl b := fun e => h (congrArg Fin.val (vacuum_label_injective s e))
  cases h with
  | red_dot | red_cross => simp [fx, fe, fψ, vacuumGen]
  | klr h =>
    cases h with
    | idem_mul s t =>
      by_cases hst : s = t <;> by_cases hs : s = vacuumSeq <;>
        by_cases ht : t = vacuumSeq <;> simp_all [fe, vacuumGen]
    | idem_sum => simp [fe, vacuumGen]
    | dot_idem | cross_idem | cross_zero | dot_dot | cross_cross | dot_cross =>
      simp [fx, fe, fψ, vacuumGen]
    | dot_cross_left j h s | dot_cross_right j h s =>
      simp [fx, fe, fψ, vacuumGen, hdiff s ⟨j, by omega⟩ ⟨j + 1, h⟩ (by simp)]
    | cross_sq j h s =>
      simp [fx, fe, fψ, vacuumGen, vacuumQ, ncEval]
    | braid j h s =>
      simp [fe, fψ, vacuumGen, hdiff s ⟨j, by omega⟩ ⟨j + 2, h⟩ (by simp)]

private noncomputable def vacuumEval : A →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (vacuumGen (k := k)), fun _ _ h => vacuumEval_rel Q Λ h⟩

private theorem vacuumEval_e :
    vacuumEval Q Λ (e (vacuumSeq (I := I) (ℓ := ℓ))) = 1 := by
  rw [e, KLRAlgebra.e, ofKLR_mk]
  trans FreeAlgebra.lift k (vacuumGen (k := k)) (fe k μ vacuumSeq)
  · exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
  simp [fe, vacuumGen]

private theorem mul_vacuum (z : A) :
    ∃ c : k, z * e vacuumSeq = c • (e vacuumSeq : A) := by
  classical
  obtain ⟨w, rfl⟩ := ofKLR_surjective z
  induction w using KLRAlgebra.klr_induction with
  | hr c =>
    exact ⟨c, by rw [AlgHom.commutes, Algebra.smul_def]⟩
  | he s =>
    change ∃ c : k, e s * e vacuumSeq = c • (e vacuumSeq : A)
    rw [e_mul_e]
    split_ifs with h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp⟩
  | hx a =>
    exact ⟨0, by rw [zero_smul]; exact x_mul_e_of_red _ _ (vacuum_label_right _ _)⟩
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card μ
    · exact ⟨0, by rw [zero_smul]
                   exact ψ_mul_e_of_red _ hj _ (vacuum_label_right _ _) (vacuum_label_right _ _)⟩
    · refine ⟨0, ?_⟩
      simp [KLRAlgebra.ψ_eq_zero j (by omega : Multiset.card μ ≤ j + 1)]
  | hadd u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, by rw [map_add, add_mul, ha, hb, add_smul]⟩
  | hmul u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨b * a, by rw [map_mul, mul_assoc, hb, mul_smul_comm, ha, smul_smul]⟩

private theorem vacuumScalars_bijective : Function.Bijective (algebraMap k B) := by
  constructor
  · intro c d h
    have h' := congrArg (fun z : B => vacuumEval Q Λ z.1) h
    change vacuumEval Q Λ (c • redOrderedIdem k Q Λ 0) =
      vacuumEval Q Λ (d • redOrderedIdem k Q Λ 0) at h'
    simpa only [redOrderedIdem_zeroWeight, map_smul, vacuumEval_e, smul_eq_mul, mul_one] using h'
  · intro z
    obtain ⟨c, hc⟩ := mul_vacuum Q Λ z.1
    use c
    apply Subtype.ext
    change c • redOrderedIdem k Q Λ 0 = z.1
    have hE := ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 z.2).2
    calc
      _ = c • (e vacuumSeq : A) := congrArg (c • ·) (redOrderedIdem_zeroWeight Q Λ)
      _ = z.1 * e vacuumSeq := hc.symm
      _ = z.1 * redOrderedIdem k Q Λ 0 := congrArg (z.1 * ·) (redOrderedIdem_zeroWeight Q Λ).symm
      _ = z.1 := hE

/-- **Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.36**.
With no black strands the tensor product algebra is the coefficient ring. -/
noncomputable def tensorProductAlgebraZeroEquiv :
    TensorProductAlgebra k Q Λ (0 : Multiset I) ≃ₐ[k] k := by
  let f := TensorProductAlgebra.mk (k := k) Q Λ (0 : Multiset I)
  have hf : Function.Bijective f := by
    refine ⟨?_, RingCon.mkₐ_surjective _⟩
    intro a b h
    have hr := (StendhalAlgebra.violatedIdeal k Q Λ 0).ringCon.eq.1 h
    rw [violatedIdeal_zeroWeight] at hr
    exact hr
  exact (AlgEquiv.ofBijective f hf).symm.trans
    (AlgEquiv.ofBijective (Algebra.ofId k B) (vacuumScalars_bijective Q Λ)).symm

end Categorification.Stendhal
