/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverQuotient
import Categorification.WeightedKLR.RedStrands.DividedProjectives
import Categorification.KLR.CyclotomicGrading

/-!
# Grading of the cyclotomic cover projection

The presentation comparison for Webster, arXiv:1309.3796v2, Definitions
4.4–4.7 preserves grading. The cover and Webster's algebra have matching
black and mixed crossing degrees, and the red crossings have zero image.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra QuantumGroup Categorification.Graded

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "H" => IsRouquierQ.gradingDatum (isRouquierQ_cyclotomicCoverQ C Λ Q hQ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum
  (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "Cyc" => CycKLR k S p μ
local notation "π" => CycKLR.mk k S p μ
local notation "φ" => cyclotomicCoverToTensor (Q := Q) Λ ν C
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "𝒯" => tensorProductGrade G ν

/-- The grading of the cyclotomic cover by images of homogeneous affine diagrams. -/
def cyclotomicCoverGrade : ℤ → Submodule k Cyc :=
  Graded.map ((H).grade μ) (π).toLinearMap

private theorem coverCycElt_homogeneous (s : Seq μ) :
    ∃ n, cycElt S p s ∈ (H).grade μ n := by
  by_cases h : 0 < Multiset.card μ
  · rw [cycElt_of_pos S p s h]
    cases hs : s.lbl ⟨0, h⟩ with
    | inl i =>
      change ∃ n, Polynomial.aeval _ 1 * e s ∈ (H).grade μ n
      rw [map_one, one_mul]
      exact ⟨0, (H).e_mem_grade s⟩
    | inr r =>
      change ∃ n, Polynomial.aeval _ Polynomial.X * e s ∈ (H).grade μ n
      rw [Polynomial.aeval_X]
      exact ⟨_, (H).x_mul_e_mem_grade ⟨0, h⟩ s⟩
  · exact ⟨0, by simp [cycElt, h]⟩

instance : GradedAlgebra (cyclotomicCoverGrade Λ C hQ ν) :=
  Graded.mapGradedAlgebra ((H).grade μ) _ CycKLR.mk_surjective fun x hx n =>
    (CycKLR.mk_eq_zero_iff _).2 <| by
      have h := (CycKLR.mk_eq_zero_iff x).1 hx
      unfold cycIdeal at h ⊢
      exact Graded.decompose_mem_twoSidedSpan ((H).grade μ)
        (fun y hy => by
          obtain ⟨s, rfl⟩ := Set.mem_range.mp hy
          exact coverCycElt_homogeneous Λ C hQ ν s) h n

omit [DecidableEq I] in
private theorem cover_degX (a : I ⊕ Fin ℓ) : (H).degX a = (G).degX a := by
  cases a with
  | inl i => rfl
  | inr r =>
    change (if r = r then (2 : ℤ) else -1) = 2
    rw [ite_eq_left rfl]

omit [DecidableEq I] in
private theorem cover_degΨ (a b : I ⊕ Fin ℓ) (h : a.isLeft ∨ b.isLeft) :
    (H).degΨ a b = (G).degΨ a b := by
  have hn (i : I) : ((C.dot i i / 2).toNat : ℤ) = C.dot i i / 2 := by
    exact Int.toNat_of_nonneg (Int.ediv_nonneg (C.dot_self_pos i).le (by decide))
  cases a with
  | inl i =>
    cases b with
    | inl j => rfl
    | inr r =>
      change -(-(((C.dot i i / 2).toNat * Λ r i : ℕ) : ℤ)) = _
      rw [neg_neg, Nat.cast_mul, hn]
      rfl
  | inr r =>
    cases b with
    | inl i =>
      change -(-(((C.dot i i / 2).toNat * Λ r i : ℕ) : ℤ)) = _
      rw [neg_neg, Nat.cast_mul, hn]
      rfl
    | inr s => simp at h

local notation "τ" => AlgHom.comp (TensorProductAlgebra.mk Q Λ ν)
  (AlgHom.comp (orderProjection Q Λ ν) (StendhalAlgebraAllOrders.ofKLR k Q Λ ν))

private theorem canonical_mem_grade {n : ℤ} {u : KLRAlgebra k (stendhalQ Q Λ) μ}
    (hu : u ∈ (G).grade μ n) : τ u ∈ 𝒯 n := by
  apply Graded.mem_map_of_mem
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν u *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν n
  have he : StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν 0 :=
    Submodule.sum_mem _ fun i _ => Graded.mem_map_of_mem _ _ ((G).e_mem_grade i)
  simpa only [add_zero, AlgHom.toLinearMap_apply] using SetLike.GradedMul.mul_mem (A := allOrdersGrade G ν)
    (Graded.mem_map_of_mem _ _ hu) he

private theorem cover_affine_mem_grade {n : ℤ} {u : KLRAlgebra k S μ}
    (hu : u ∈ (H).grade μ n) : φ (π u) ∈ 𝒯 n := by
  let f := (φ).comp π
  apply grade_transfer H 𝒯 SetLike.GradedOne.one_mem
    (fun ha hb => SetLike.GradedMul.mul_mem ha hb) f _ _ _ hu
  · intro s
    exact (cyclotomicCoverToTensor_mk (Q := Q) Λ ν C (fe k μ s)).symm ▸
      canonical_mem_grade Λ C hQ ν ((G).e_mem_grade s)
  · intro a s
    have hm := cyclotomicCoverToTensor_mk (Q := Q) Λ ν C (fx k μ a * fe k μ s)
    rw [map_mul (KLRAlgebra.mk k S μ), map_mul (KLRAlgebra.mk k (stendhalQ Q Λ) μ)] at hm
    change φ (π (x a * e s)) = τ (x a * e s) at hm
    change φ (π (x a * e s)) ∈ 𝒯 ((H).degX (s.lbl a))
    rw [hm, cover_degX Λ C hQ]
    exact canonical_mem_grade Λ C hQ ν ((G).x_mul_e_mem_grade a s)
  · intro j s
    have hm := cyclotomicCoverToTensor_mk (Q := Q) Λ ν C (fψ k μ j * fe k μ s)
    rw [map_mul (KLRAlgebra.mk k S μ), map_mul (KLRAlgebra.mk k (stendhalQ Q Λ) μ)] at hm
    change φ (π (ψ j * e s)) = τ (ψ j * e s) at hm
    change φ (π (ψ j * e s)) ∈ 𝒯 ((H).dψ j s)
    rw [hm]
    by_cases hj : j + 1 < Multiset.card μ
    · rw [GradingDatum.dψ_of_lt _ hj]
      by_cases h : (s.lbl ⟨j, by omega⟩).isLeft ∨ (s.lbl ⟨j + 1, hj⟩).isLeft
      · rw [cover_degΨ Λ C hQ _ _ h, ← GradingDatum.dψ_of_lt _ hj]
        exact canonical_mem_grade Λ C hQ ν ((G).ψ_mul_e_mem_grade' j s)
      · push Not at h
        have hl : (s.lbl ⟨j, by omega⟩).isRight := by
          cases hs : s.lbl ⟨j, by omega⟩ <;> simp_all
        have hr : (s.lbl ⟨j + 1, hj⟩).isRight := by
          cases hs : s.lbl ⟨j + 1, hj⟩ <;> simp_all
        rw [(tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).red_cross
          j hj s hl hr]
        exact zero_mem _
    · rw [ψ_eq_zero j (by omega), zero_mul, map_zero]
      exact zero_mem _

/-- The cyclotomic projection to the Stendhal algebra preserves the gradings
from the extended and original Cartan data. -/
theorem cyclotomicCoverToTensor_preservesGrading :
    PreservesGrading (cyclotomicCoverGrade Λ C hQ ν) 𝒯 (φ).toLinearMap := by
  rintro n z ⟨u, hu, rfl⟩
  exact cover_affine_mem_grade Λ C hQ ν hu

end Categorification.Stendhal
