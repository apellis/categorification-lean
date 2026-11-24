/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingWeightDecomposition

/-!
# Webster's grading for arbitrary red permutations

A reduced diagram has one red/red crossing for each pair of red labels
whose relative order changes. Their degree corrections depend only on
the two boundary red words. They put the actual rectangular coefficient
in a coset of the auxiliary integer grading in the complex degree group.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv TypeA QuantumGroup

section RedInversions

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- Red order can be read either from the strand positions or the indices
of the labels in the red word. -/
theorem redWord_idxOf_lt_iff (t : Seq μ) (w : Perm (Fin m))
    {a b : Fin m} {r d : Fin ℓ} (ha : t.lbl a = .inr r) (hb : t.lbl b = .inr d) :
    (redWord (w • t)).idxOf r < (redWord (w • t)).idxOf d ↔ w a < w b := by
  let L := redWord (w • t)
  let i : Fin L.length := ⟨L.idxOf r, List.idxOf_lt_length_iff.mpr (mem_redWord _ r)⟩
  let j : Fin L.length := ⟨L.idxOf d, List.idxOf_lt_length_iff.mpr (mem_redWord _ d)⟩
  have hi : L.get i = r := List.idxOf_get _
  have hj : L.get j = d := List.idxOf_get _
  constructor
  · intro h
    have h' := (redWord_pairwise t w).rel_get_of_lt (show i < j from h)
    rw [hi, hj] at h'
    exact h' a b ha hb
  · intro h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact hlt
    · have hrd : r = d := hi.symm.trans (congrArg L.get heq) |>.trans hj
      have hab := lbl_inj_of_inr t r ha (hb.trans (congrArg Sum.inr hrd.symm))
      exact False.elim ((ne_of_lt h) (congrArg w hab))
    · have h' := (redWord_pairwise t w).rel_get_of_lt hgt
      rw [hj, hi] at h'
      exact False.elim (lt_asymm h (h' b a hb ha))


/-- The pairs of red labels that change order from the lower to the upper word. -/
def redWordInversions (lower upper : List (Fin ℓ)) : Finset (Fin ℓ × Fin ℓ) :=
  Finset.univ.filter fun p =>
    lower.idxOf p.1 < lower.idxOf p.2 ∧ upper.idxOf p.2 < upper.idxOf p.1

@[simp] theorem mem_redWordInversions (lower upper : List (Fin ℓ)) (p : Fin ℓ × Fin ℓ) :
    p ∈ redWordInversions lower upper ↔
      lower.idxOf p.1 < lower.idxOf p.2 ∧ upper.idxOf p.2 < upper.idxOf p.1 := by
  simp [redWordInversions]

private noncomputable def redPosition (t : Seq μ) (r : Fin ℓ) : Fin m :=
  (exists_lbl_eq_inr t r).choose

private theorem lbl_redPosition (t : Seq μ) (r : Fin ℓ) :
    t.lbl (redPosition t r) = .inr r :=
  (exists_lbl_eq_inr t r).choose_spec

private theorem redPosition_injective (t : Seq μ) : Function.Injective (redPosition t) := by
  intro r d h
  have h' := congrArg t.lbl h
  rw [lbl_redPosition, lbl_redPosition] at h'
  exact Sum.inr.inj h'

private theorem idxOf_redWord_lt_iff (t : Seq μ) {a b : Fin m} {r d : Fin ℓ}
    (ha : t.lbl a = .inr r) (hb : t.lbl b = .inr d) :
    (redWord t).idxOf r < (redWord t).idxOf d ↔ a < b := by
  simpa using redWord_idxOf_lt_iff t (1 : Perm (Fin m)) ha hb

/-- Sum a label-pair correction over the red inversions of the two boundary
words, or equivalently over red/red inversions of any reduced diagram. -/
theorem sum_redWordInversions (t : Seq μ) (w : Perm (Fin m)) (F : Fin ℓ → Fin ℓ → ℂ) :
    (∑ p ∈ redWordInversions (redWord t) (redWord (w • t)), F p.1 p.2) =
      ∑ p ∈ invSet m w,
        (match t.lbl p.1, t.lbl p.2 with
        | .inr r, .inr d => F r d
        | _, _ => 0) := by
  classical
  let isRedPair := fun p : Fin m × Fin m => (t.lbl p.1).isRight ∧ (t.lbl p.2).isRight
  let correction := fun p : Fin m × Fin m =>
    match t.lbl p.1, t.lbl p.2 with
    | .inr r, .inr d => F r d
    | _, _ => 0
  change _ = ∑ p ∈ invSet m w, correction p
  have hfilter : ∑ p ∈ (invSet m w).filter isRedPair, correction p =
      ∑ p ∈ invSet m w, correction p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    rcases h₁ : t.lbl p.1 with i | r <;> rcases h₂ : t.lbl p.2 with j | d <;>
      simp [correction, h₁, h₂] at ⊢
    exact (hnot (Finset.mem_filter.mpr ⟨hp, by simp [isRedPair, h₁, h₂]⟩)).elim
  rw [← hfilter]
  refine Finset.sum_bij (fun p _ => (redPosition t p.1, redPosition t p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := (mem_redWordInversions _ _ _).mp hp
    have ha := lbl_redPosition t p.1
    have hb := lbl_redPosition t p.2
    exact Finset.mem_filter.mpr ⟨mem_invSet.mpr
      ⟨(idxOf_redWord_lt_iff t ha hb).mp hp'.1, (redWord_idxOf_lt_iff t w hb ha).mp hp'.2⟩,
      by simp [isRedPair, ha, hb]⟩
  · intro p _ q _ h
    exact Prod.ext (redPosition_injective t (congrArg Prod.fst h))
      (redPosition_injective t (congrArg Prod.snd h))
  · intro p hp
    obtain ⟨hinv, hred⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlt, hswap⟩ := mem_invSet.mp hinv
    rcases ha : t.lbl p.1 with i | r
    · simp [isRedPair, ha] at hred
    rcases hb : t.lbl p.2 with j | d
    · simp [isRedPair, hb] at hred
    refine ⟨(r, d), (mem_redWordInversions _ _ _).mpr
      ⟨(idxOf_redWord_lt_iff t ha hb).mpr hlt, (redWord_idxOf_lt_iff t w hb ha).mpr hswap⟩, ?_⟩
    exact Prod.ext (lbl_inj_of_inr t r (lbl_redPosition t r) ha)
      (lbl_inj_of_inr t d (lbl_redPosition t d) hb)
  · intro p _
    simp [correction, lbl_redPosition]

end RedInversions

section CrossingDegrees

variable {I : Type} {k : Type*} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {H : Type*} [AddCommGroup H] [Module ℂ H]
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
  (fun i => Eq.trans (IsRouquierQ.gradingDatum_degX hQ i) (Eq.symm (UDot.two_mul_di C i)))

/-- The translation of the auxiliary grading depends only on the inverted
red pairs of the two boundary words. -/
noncomputable def redWordOffset (lower upper : List (Fin ℓ)) : ℂ :=
  ∑ p ∈ redWordInversions lower upper, (2 - B (η p.1) (η p.2))

/-- For a reduced diagram, the sum of Webster crossing degrees is its
auxiliary degree plus the boundary red-word offset. -/
theorem redPermutation_crossingDegree {t : KLR.Seq (stendhalWeight ℓ ν)} {γ : List ℕ}
    (hγ : IsReduced m γ) :
    (∑ p ∈ invSet m (wordProd m γ),
      crossingDegree (Λ := Λ) C hQ B η (t.lbl p.1) (t.lbl p.2)) =
      ((G).degW γ t : ℂ) +
        redWordOffset B η (redWord t) (redWord (wordProd m γ • t)) := by
  rw [GradingDatum.degW_eq_sum_invSet _ hγ, Int.cast_sum, redWordOffset,
    sum_redWordInversions t (wordProd m γ) (fun r d => 2 - B (η r) (η d)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases hx : t.lbl p.1 with i | r <;> rcases hy : t.lbl p.2 with j | d
  · simp [crossingDegree]
  · simp [crossingDegree]
  · simp [crossingDegree]
  · change -B (η r) (η d) = ((-2 : ℤ) : ℂ) + (2 - B (η r) (η d))
    push_cast
    ring

variable [DecidableEq I]

local notation "q" => violMk k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
local notation "δ" lower:arg upper:arg => redWordOffset B η lower upper

private theorem intOffset_injective (c : ℂ) : Function.Injective (fun j : ℤ => (j : ℂ) + c) :=
  fun _ _ h => Int.cast_injective (add_right_cancel h)

/-- Webster's complex-valued grading of the whole red-permutation coefficient.
The coefficient ring itself is unchanged. -/
def redPermutationWeight (lower upper : List (Fin ℓ)) (z : ℂ) :
    AddSubgroup (braidingBimodule k Q Λ ν upper lower) :=
  Function.extend (fun j : ℤ => (j : ℂ) + δ lower upper)
    (diagramCornerWeight (e := q (redProj k Q Λ ν upper))
      (e' := q (redProj k Q Λ ν lower)) (violAuxiliaryGrade (ν := ν) G)) (fun _ => ⊥) z

@[simp] theorem redPermutationWeight_intAdd (lower upper : List (Fin ℓ)) (j : ℤ) :
    redPermutationWeight (Λ := Λ) (ν := ν) C hQ B η lower upper ((j : ℂ) + δ lower upper) =
      diagramCornerWeight (e := q (redProj k Q Λ ν upper))
        (e' := q (redProj k Q Λ ν lower)) (violAuxiliaryGrade (ν := ν) G) j :=
  (intOffset_injective _).extend_apply _ _ _

/-- A tensor coefficient in integer coordinates acquires Webster's degree
when the output coordinate is based at the input origin plus the red-word offset. -/
theorem redPermutationWeight_coordinate (lower upper : List (Fin ℓ)) (c : ℂ) (a b : ℤ) :
    redPermutationWeight (Λ := Λ) (ν := ν) C hQ B η lower upper
      ((c + δ lower upper + (a : ℂ)) - (c + (b : ℂ))) =
      diagramCornerWeight (e := q (redProj k Q Λ ν upper))
        (e' := q (redProj k Q Λ ν lower)) (violAuxiliaryGrade (ν := ν) G) (a - b) := by
  rw [← redPermutationWeight_intAdd C hQ B η lower upper]
  congr 1
  push_cast
  ring

theorem redPermutationWeight_eq_bot (lower upper : List (Fin ℓ)) {z : ℂ}
    (hz : ¬ ∃ j : ℤ, (j : ℂ) + δ lower upper = z) :
    redPermutationWeight (Λ := Λ) (ν := ν) C hQ B η lower upper z = ⊥ :=
  Function.extend_apply' _ _ _ hz

local notation "E" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "V" => violAuxiliaryGrade (ν := ν) G

/-- Multiplication on the left by a homogeneous corner element adds its
integer degree to the normalized coefficient degree. -/
theorem redPermutationWeight_left {lower upper : List (Fin ℓ)} {i j : ℤ} {a : (E upper).Corner}
    {x : braidingBimodule k Q Λ ν upper lower}
    (ha : a.val ∈ V i)
    (hx : x ∈ redPermutationWeight C hQ B η lower upper ((j : ℂ) + δ lower upper)) :
    a • x ∈ redPermutationWeight C hQ B η lower upper ((i : ℂ) + ((j : ℂ) + δ lower upper)) := by
  rw [← add_assoc, ← Int.cast_add, redPermutationWeight_intAdd]
  rw [redPermutationWeight_intAdd] at hx
  exact SetLike.GradedMul.mul_mem (A := V) ha hx

/-- Multiplication on the right adds the degree of the source corner element. -/
theorem redPermutationWeight_right {lower upper : List (Fin ℓ)} {i j : ℤ} {a : (E lower).Corner}
    {x : braidingBimodule k Q Λ ν upper lower}
    (ha : a.val ∈ V i)
    (hx : x ∈ redPermutationWeight C hQ B η lower upper ((j : ℂ) + δ lower upper)) :
    MulOpposite.op a • x ∈
      redPermutationWeight C hQ B η lower upper (((j : ℂ) + δ lower upper) + (i : ℂ)) := by
  rw [add_right_comm, ← Int.cast_add, redPermutationWeight_intAdd]
  rw [redPermutationWeight_intAdd] at hx
  exact SetLike.GradedMul.mul_mem (A := V) hx ha

/-- A reduced diagram from the source red order to the swapped order, with
homogeneous dots, lies in the piece prescribed by Webster's local degrees. -/
theorem redPermutation_mem_weight {t : Seq μ} {γ : List ℕ} {lower upper : List (Fin ℓ)}
    (hγ : IsReduced m γ) (ht : redWord t = lower)
    (hs : redWord (wordProd m γ • t) = upper)
    {p : MvPolynomial (Fin m) k} {N : ℤ}
    (hp : p.IsWeightedHomogeneous (fun i => (G).degX (t.lbl i)) N) :
    ∃ x : braidingBimodule k Q Λ ν upper lower,
      x.val = q (π (KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t)) ∧
      x ∈ redPermutationWeight C hQ B η lower upper
        ((∑ a ∈ invSet m (wordProd m γ),
            crossingDegree (Λ := Λ) C hQ B η (t.lbl a.1) (t.lbl a.2)) + (N : ℂ)) := by
  let y : KLRAlgebra k (stendhalQ Q Λ) μ := KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t
  have hfix : redIdem k Q Λ upper * y * redIdem k Q Λ lower = y := by
    change _ * (KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t) * _ = _
    rw [redIdem_mul_std, ite_eq_left ⟨hs, ht⟩]
  have hfix' : q (redProj k Q Λ ν upper) * q (π y) * q (redProj k Q Λ ν lower) = q (π y) := by
    simpa only [redProj, map_mul] using congrArg (fun a => q (π a)) hfix
  have hL := isIdempotentElem_violMk_redProj k Q Λ ν upper
  have hR := isIdempotentElem_violMk_redProj k Q Λ ν lower
  refine ⟨⟨q (π y), mem_cornerBimodule.mpr ⟨?_, ?_⟩⟩, rfl, ?_⟩
  · nth_rw 1 [← hfix']
    rw [← mul_assoc, ← mul_assoc, hL.eq, hfix']
  · nth_rw 1 [← hfix']
    rw [mul_assoc, hR.eq, hfix']
  · rw [redPermutation_crossingDegree (Λ := Λ) C hQ B η hγ, ht, hs]
    rw [add_right_comm, ← Int.cast_add, redPermutationWeight_intAdd]
    exact Graded.mem_map_of_mem _ (q).toLinearMap
      (Graded.mem_map_of_mem _ (π).toLinearMap
        (GradingDatum.ψw_mul_pol_mul_e_mem_grade G γ t hp))

/-- The full coefficient is the direct sum of its normalized pieces. -/
theorem redPermutationWeight_isInternal (lower upper : List (Fin ℓ)) :
    DirectSum.IsInternal (redPermutationWeight (Λ := Λ) (ν := ν) C hQ B η lower upper) := by
  exact Graded.isInternal_addSubgroup_extend_bot _ (intOffset_injective _)
    _ (diagramCornerWeight_isInternal _
      (redProj_mem_violAuxiliaryGrade G upper) (redProj_mem_violAuxiliaryGrade G lower))

end CrossingDegrees

end Categorification.Stendhal.BraidedStendhalAlgebra
