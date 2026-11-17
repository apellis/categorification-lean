/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineCover
import Categorification.KLR.GradeTransfer
import Categorification.QuantumGroup.RootDatumSum

/-!
# Grading on the affine cover of red diagrams

Webster, arXiv:1309.3796v2, Definitions 4.4–4.7 and Lemma 4.37.
Distinct red colours have crossing degree one in the affine cover, making
the parameter `u + v` homogeneous. Their crossings vanish in the Stendhal
algebra, so the map to that algebra preserves all diagram degrees.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR MvPolynomial StendhalAlgebraAllOrders QuantumGroup

variable {I k : Type*} [CommRing k] {ℓ : ℕ} {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (G : GradingDatum Q) (d : I → ℤ) (hd : ∀ i, G.degX i = 2 * d i)

/-- Symmetry of the affine-cover parameters, including exchange of the two red dot variables. -/
theorem affineCoverQ_symm (hs : KLRSymm Q) : KLRSymm (affineCoverQ Q Λ) := by
  rintro (i | r) (j | s) h
  · exact hs i j fun hij => h (congrArg Sum.inl hij)
  · simp [affineCoverQ, stendhalQ]
  · simp [affineCoverQ, stendhalQ]
  · simp [affineCoverQ, add_comm]

/-- Nonzero off-diagonal parameters on the affine cover. Evaluation at `(1, 0)`
distinguishes the red polynomial `u + v` from zero in every characteristic. -/
theorem affineCoverQ_ne_zero [Nontrivial k] (hQ : ∀ i j, i ≠ j → Q i j ≠ 0) :
    ∀ a b, a ≠ b → affineCoverQ Q Λ a b ≠ 0 := by
  rintro (i | r) (j | s) h
  · exact hQ i j fun hij => h (congrArg Sum.inl hij)
  · intro hz
    have hh := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) hz
    simp [affineCoverQ, stendhalQ] at hh
  · intro hz
    have hh := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) hz
    simp [affineCoverQ, stendhalQ] at hh
  · intro hz
    have hh := congrArg (MvPolynomial.eval ![(1 : k), 0]) hz
    simp [affineCoverQ] at hh

local notation "H" => stendhalGradingDatum Λ G d hd

/-- The grading on the affine cover, using symmetric degree one for crossings
of distinct red labels and Webster's degrees on black and mixed generators. -/
def affineCoverGrading : GradingDatum (affineCoverQ Q Λ) where
  degX := (H).degX
  degΨ
    | .inr r, .inr s => if r = s then -2 else 1
    | a, b => (H).degΨ a b
  degΨ_self := by rintro (i | r); exact G.degΨ_self i; simp [stendhalGradingDatum]
  isWeightedHomogeneous := by
    rintro (i | r) (j | s) h
    · exact (H).isWeightedHomogeneous (.inl i) (.inl j) h
    · exact (H).isWeightedHomogeneous (.inl i) (.inr s) h
    · exact (H).isWeightedHomogeneous (.inr r) (.inl j) h
    · have hrs : r ≠ s := fun he => h (congrArg Sum.inr he)
      change (X 0 + X 1 : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![(2 : ℤ), 2]
        ((if r = s then -2 else 1) + (if s = r then -2 else 1))
      rw [ite_eq_right hrs, ite_eq_right hrs.symm]
      exact (isWeightedHomogeneous_X k ![(2 : ℤ), 2] (0 : Fin 2)).add
        (isWeightedHomogeneous_X k ![(2 : ℤ), 2] (1 : Fin 2))

theorem affineCoverGrading_cross_symm (hs : ∀ i j, G.degΨ i j = G.degΨ j i) :
    ∀ a b, (affineCoverGrading Λ G d hd).degΨ a b = (affineCoverGrading Λ G d hd).degΨ b a := by
  rintro (i | r) (j | s)
  · exact hs i j
  · rfl
  · rfl
  · simp [affineCoverGrading, eq_comm]

/-- The dot degrees used in the divided-power shifts. The orthogonal red
summand supplies diagonal two; only the diagonal enters these shifts. -/
abbrev affineCoverCartan (C : CartanDatum I) (ℓ : ℕ) : CartanDatum (I ⊕ Fin ℓ) :=
  C.sum (CartanDatum.ofGraph (⊥ : SimpleGraph (Fin ℓ)))

theorem affineCoverGrading_dot (C : CartanDatum I) (hX : ∀ i, G.degX i = C.dot i i) :
    ∀ a, (affineCoverGrading Λ G d hd).degX a = (affineCoverCartan C ℓ).dot a a := by
  rintro (i | r)
  · exact hX i
  · exact (CartanDatum.ofGraph_dot_self (⊥ : SimpleGraph (Fin ℓ)) r).symm

variable [DecidableEq I] (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "φ" => affineCover Q Λ ν

private theorem affineCover_mk (a : FreeAlgebra k (Gen μ)) :
    φ (KLRAlgebra.mk k _ μ a) = ofKLR k Q Λ ν (KLRAlgebra.mk k _ μ a) := by
  rw [ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem affineCover_e (s : Seq μ) : φ (KLRAlgebra.e s) = e s :=
  affineCover_mk Λ ν _

@[simp] theorem affineCover_x (a : Fin (Multiset.card μ)) : φ (KLRAlgebra.x a) = x a :=
  affineCover_mk Λ ν _

@[simp] theorem affineCover_ψ (j : ℕ) : φ (KLRAlgebra.ψ j) = ψ j :=
  affineCover_mk Λ ν _

/-- The affine cover surjection preserves Webster's grading, including on
terms with red crossings (Webster, Definitions 4.4–4.7 and Lemma 4.37). -/
theorem affineCover_mem_grade {n : ℤ} {u : KLRAlgebra k (affineCoverQ Q Λ) μ}
    (hu : u ∈ (affineCoverGrading Λ G d hd).grade μ n) :
    φ u ∈ allOrdersGrade H ν n := by
  apply grade_transfer (affineCoverGrading Λ G d hd) (allOrdersGrade H ν)
    SetLike.GradedOne.one_mem (fun ha hb => SetLike.GradedMul.mul_mem ha hb) φ _ _ _ hu
  · intro s
    rw [affineCover_e]
    exact Graded.mem_map_of_mem _ _ ((H).e_mem_grade s)
  · intro a s
    rw [map_mul, affineCover_x, affineCover_e]
    rw [x, e, ← map_mul]
    exact Graded.mem_map_of_mem _ _ ((H).x_mul_e_mem_grade a s)
  · intro j s
    have ht : (ψ j * e s : StendhalAlgebraAllOrders k Q Λ ν) ∈ allOrdersGrade H ν ((H).dψ j s) := by
      rw [ψ, e, ← map_mul]
      exact Graded.mem_map_of_mem _ _ ((H).ψ_mul_e_mem_grade' j s)
    rw [map_mul, affineCover_ψ, affineCover_e]
    by_cases hj : j + 1 < (Multiset.card μ)
    · rw [GradingDatum.dψ_of_lt _ hj] at ht ⊢
      cases ha : s.lbl ⟨j, by omega⟩ with
      | inl i =>
        rw [ha] at ht
        cases hb : s.lbl ⟨j+1, hj⟩ <;> rw [hb] at ht <;> exact ht
      | inr r =>
        cases hb : s.lbl ⟨j+1, hj⟩ with
        | inl i => rw [ha, hb] at ht; exact ht
        | inr t =>
          rw [ψ_mul_e_of_red j hj s (by simp [ha]) (by simp [hb])]
          exact zero_mem _
    · simpa only [GradingDatum.dψ, dite_eq_right hj] using ht

end Categorification.Stendhal
