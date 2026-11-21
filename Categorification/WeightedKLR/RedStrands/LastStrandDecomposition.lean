/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastStrand
import Categorification.KLR.IndLastStrandExact
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.WeightedKLR.RedStrands.StandardBlocks
import Categorification.KLR.KL2.OrthSum
import Categorification.KLR.Crystal.Thm317

/-!
# Splitting a `T^λ`-module by its last strand

Input for the dimension count in the proof of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Proposition 5.5 (the equation for `dim` of a module
as the sum over the colour of its last strand). The loadings of `T^λ` with `λ_{ℓ+1}` last are
split according to the strand in the final position, which is either the red strand
`λ_{ℓ+1}` or a black strand of colour `j`.

## Main results

* `lastStrandIdem`: the idempotent of the loadings whose final strand has colour `b`
  (`none` for red).
* `lastStrandIdem_none`: for `b = none` it is the last-red idempotent.
* `lastStrandIdem_some`: for `b = some j` it is the idempotent `appendBlack j ν₀ 1`
  of `E_j`, transported along `{j} + ν₀ = ν`.
* `finrank_eq_lastRed_add_sum`: `dim Y = dim e_red Y + ∑_j dim e_j Y` for a
  finite-dimensional `T^λ`-module `Y`.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra

section Generic
variable {J k : Type*} [DecidableEq J] [CommRing k] (R : J → J → MvPolynomial (Fin 2) k)

/-- The loadings whose strand at position `p` has colour `c`. -/
def fiberSet {μ : Multiset J} (p : Fin (Multiset.card μ)) (c : J) : Finset (Seq μ) :=
  Finset.univ.filter fun s => s.1 p = c

/-- A finite partition of the loadings gives a decomposition of the unit. -/
theorem sum_eSum_filter_eq_one {μ : Multiset J} {β : Type*} [DecidableEq β] (g : Seq μ → β)
    (t : Finset β) (ht : ∀ s, g s ∈ t) :
    (∑ b ∈ t, eSum R (Finset.univ.filter fun s => g s = b) : KLRAlgebra k R μ) = 1 := by
  rw [← sum_e (ν := μ)]
  simp only [eSum]
  exact Finset.sum_fiberwise_of_maps_to (fun s _ => ht s) _

/-- Idempotents of distinct fibres of a function on loadings are orthogonal. -/
theorem eSum_filter_mul_eSum_filter {μ : Multiset J} {β : Type*} [DecidableEq β]
    (g : Seq μ → β) {b b' : β} (h : b ≠ b') :
    (eSum R (Finset.univ.filter fun s => g s = b) : KLRAlgebra k R μ) *
      eSum R (Finset.univ.filter fun s => g s = b') = 0 := by
  rw [eSum_mul_eSum]
  convert eSum_empty (Q := R) (k := k)
  ext s
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_and]
  rintro rfl; exact h

/-- `1_{μ₀, c}` transported to `μ` is the sum of `e(s)` over loadings with colour `c` at the
last position. -/
theorem castKLR_oneConcat_singleton {μ₀ μ : Multiset J} (c : J) (h : μ₀ + {c} = μ) :
    castKLR R h (oneConcat R μ₀ {c}) =
      eSum R (fiberSet (μ := μ) ⟨Multiset.card μ₀, by rw [← h]; simp⟩ c) := by
  rw [oneConcat]
  refine castKLR_eSum_of_mem_iff h fun s => ?_
  rw [mem_concatSet_singleton_iff]
  simp [fiberSet, Seq.cast_apply]

end Generic

section Tensor

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "S" => stendhalQ Q Λ
local notation "μ" => stendhalWeight (ℓ + 1) ν

/-- The colour of the last strand of a loading if it is black, `none` if it is red. -/
def lastBlackColour (s : Seq μ) : Option I := (s.1 (lastRedPosition ℓ ν)).getLeft?

/-- The idempotent of `T(ν)` selecting the loadings whose last strand is black of colour `j`
(`b = some j`) or red (`b = none`). -/
def lastStrandIdem (b : Option I) : TensorProductAlgebra k Q Λ ν :=
  tensorOfKLR Q Λ ν (eSum S (Finset.univ.filter fun s => lastBlackColour ν s = b))

/-- The map `R(μ) → T(ν)` is multiplicative. -/
theorem tensorOfKLR_mul (x y : KLRAlgebra k S μ) :
    tensorOfKLR Q Λ ν (x * y) = tensorOfKLR Q Λ ν x * tensorOfKLR Q Λ ν y := by
  simp only [tensorOfKLR, map_mul]

/-- The last-strand idempotents are orthogonal idempotents. -/
theorem lastStrandIdem_mul (b b' : Option I) :
    lastStrandIdem Q Λ ν b * lastStrandIdem Q Λ ν b' =
      if b = b' then lastStrandIdem Q Λ ν b else 0 := by
  rw [lastStrandIdem, lastStrandIdem, ← tensorOfKLR_mul]
  split_ifs with h
  · subst h; rw [(eSum_idem _).eq]
  · rw [eSum_filter_mul_eSum_filter _ _ h]; simp [tensorOfKLR]

/-- **The unit of `T(ν)` splits by the last strand**: red, or black of each colour of `ν`. -/
theorem lastStrandIdem_none_add_sum :
    lastStrandIdem Q Λ ν none + ∑ j ∈ ν.toFinset, lastStrandIdem Q Λ ν (some j) = 1 := by
  have h := sum_eSum_filter_eq_one (k := k) S (lastBlackColour ν)
    (insert none (ν.toFinset.image some)) fun s => by
      rcases hs : lastBlackColour ν s with _ | j
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, ?_, rfl⟩)
        have hm := Seq.mem s (lastRedPosition ℓ ν)
        simp only [lastBlackColour] at hs
        rcases hc : s.1 (lastRedPosition ℓ ν) with c | r
        · rw [hc] at hs hm
          cases hs
          simpa [stendhalWeight] using hm
        · rw [hc] at hs; cases hs
  rw [Finset.sum_insert (by simp), Finset.sum_image (by simp)] at h
  have h' := congrArg (tensorOfKLR Q Λ ν) h
  simpa only [map_add, map_sum, map_one, tensorOfKLR, lastStrandIdem] using h'

/-- The black-last idempotent of colour `j` is Webster's `E_j` idempotent `appendBlack 1`,
transported along `j + ν₀ = ν`. -/
theorem lastStrandIdem_some (j : I) (ν₀ : Multiset I)
    (h : (Singleton.singleton j) + ν₀ = ν) :
    lastStrandIdem Q Λ ν (some j) =
      castTensorProductAlgebra Q Λ h (appendBlack Q Λ j ν₀ 1) := by
  subst h
  rw [appendBlack_one_eq_oneConcat, castTensorProductAlgebra_mk, castKLR_castKLR,
    castKLR_oneConcat_singleton, lastStrandIdem]
  congr 2
  ext s
  rw [Finset.mem_filter_univ]
  simp only [fiberSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hp : (⟨Multiset.card (stendhalWeight (ℓ + 1) ν₀), by simp [stendhalWeight]⟩ :
      Fin (Multiset.card (stendhalWeight (ℓ + 1) ((Singleton.singleton j) + ν₀)))) =
      lastRedPosition ℓ _ := Fin.ext (by simp [lastRedPosition, stendhalWeight]; omega)
  rw [hp, lastBlackColour]
  generalize s.1 (lastRedPosition ℓ _) = x
  rcases x with c | r <;> simp [Sum.getLeft?]


omit [DecidableEq I] in
/-- In a red-ordered loading the final strand is black or is the red strand `λ_{ℓ+1}`. -/
theorem hasLastRed_iff_lastBlackColour_eq_none (s : Seq μ) (hs : IsRedOrdered s) :
    HasLastRed s ↔ lastBlackColour ν s = none := by
  unfold HasLastRed lastBlackColour
  constructor
  · intro h; change (s.lbl _).getLeft? = none; rw [h]; rfl
  · intro h
    change (s.lbl _).getLeft? = none at h
    rcases hc : s.lbl (lastRedPosition ℓ ν) with c | r
    · rw [hc] at h; cases h
    · obtain ⟨a, ha⟩ := exists_lbl_eq_inr s (Fin.last ℓ)
      have hle : a ≤ lastRedPosition ℓ ν := by
        rw [Fin.le_def]; have := a.2; simp [lastRedPosition, stendhalWeight] at this ⊢; omega
      rcases hle.lt_or_eq with hlt | heq
      · exact absurd (hs _ _ _ _ hlt ha hc) (not_lt.2 (Fin.le_last r))
      · rw [← hc, ← heq]; exact ha

/-- The red-last idempotent is the last-red idempotent of `T(ν)`. -/
theorem lastStrandIdem_none :
    lastStrandIdem Q Λ ν none = TensorProductAlgebra.lastRedIdem Q Λ ν := by
  classical
  rw [lastStrandIdem, tensorOfKLR, TensorProductAlgebra.lastRedIdem]
  congr 1
  apply Subtype.ext
  rw [lastRedIdem_val_eq_sum]
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν (eSum S _) *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν = _
  rw [eSum, map_sum, Finset.sum_mul]
  change ∑ s ∈ _, StendhalAlgebraAllOrders.e s *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν = _
  simp_rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
  rw [← Finset.sum_filter, Finset.sum_subtype
    (p := fun s : Seq μ => IsRedOrdered s ∧ HasLastRed s)]
  intro s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hs⟩; exact ⟨hs, (hasLastRed_iff_lastBlackColour_eq_none ν s hs).2 h⟩
  · rintro ⟨hs, h⟩; exact ⟨(hasLastRed_iff_lastBlackColour_eq_none ν s hs).1 h, hs⟩

/-- The last-strand idempotents, indexed by `none` and the colours of `ν`, are orthogonal. -/
theorem isOrthFamily_lastStrandIdem :
    IsOrthFamily (insert none (ν.toFinset.image some)) (lastStrandIdem Q Λ ν) :=
  fun a _ b _ => lastStrandIdem_mul Q Λ ν a b

/-- The last-strand idempotents sum to `1`. -/
theorem sum_lastStrandIdem :
    ∑ a ∈ insert none (ν.toFinset.image some), lastStrandIdem Q Λ ν a = 1 := by
  rw [Finset.sum_insert (by simp), Finset.sum_image (by simp)]
  exact lastStrandIdem_none_add_sum Q Λ ν

/-- **Splitting by the last strand** (arXiv:1309.3796v3, proof of Proposition 5.5): a
finite-dimensional `T^λ`-module is the sum of the part where the last strand is red and the
parts where it is black of each colour. -/
theorem finrank_eq_lastRed_add_sum {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
    (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (Y : Type*) [AddCommGroup Y] [Module K Y]
    [Module (TensorProductAlgebra K Q Λ ν) Y]
    [IsScalarTower K (TensorProductAlgebra K Q Λ ν) Y]
    [FiniteDimensional K Y] :
    Module.finrank K Y = Module.finrank K (fixSub K Y (TensorProductAlgebra.lastRedIdem Q Λ ν)) +
      ∑ j ∈ ν.toFinset, Module.finrank K (fixSub K Y (lastStrandIdem Q Λ ν (some j))) := by
  classical
  have e := fixSubSumEquiv (isOrthFamily_lastStrandIdem Q Λ ν) K Y
  rw [sum_lastStrandIdem, fixSub_one] at e
  rw [← finrank_top K Y, e.finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_coe_sort (insert none (ν.toFinset.image some))
      (fun a => Module.finrank K (fixSub K Y (lastStrandIdem Q Λ ν a))),
    Finset.sum_insert (by simp), Finset.sum_image (by simp), lastStrandIdem_none]

end Tensor
end Categorification.Stendhal
