/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedQuotient

/-!
# Splitting a red strand: the isomorphism of Proposition 4.21

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. Let `λ'` be obtained from `λ` by splitting the red strand `λ_c` into two
adjacent red strands `λ'_c`, `λ'_{c+1}` with `λ_c = λ'_c + λ'_{c+1}`. Splitting the red strand
identifies `T^λ` with the corner `e T^{λ'} e`, for `e` the sum of the idempotents of the loadings
in which the two red strands `c`, `c + 1` are adjacent.

## Main results

* `splitTensorIdem` : the idempotent `e` of `T^{λ'}`.
* `splitRed` : the splitting map `T^λ → e T^{λ'} e`.
* `splitRed_surjective` : it is onto.
* `splitRed_injective` : it is injective, for the crossing parameters of §2.2.
* `splitRedEquiv` : **Proposition 4.21**, `T^λ ≅ e T^{λ'} e`.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA

variable {I : Type} {ℓ : ℕ} (c : Fin ℓ) [DecidableEq I]
  {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ' : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "f" => splitStendhalValue c Q Λ' ν
local notation "π" => TensorProductAlgebra.mk Q Λ' ν

theorem splitStendhalValue_one_mul (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    f 1 * f z = f z := by
  rw [← map_mul, one_mul]

theorem splitStendhalValue_mul_one (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    f z * f 1 = f z := by
  rw [← map_mul, mul_one]

variable (ν) in
/-- The idempotent `e` of `T^{λ'}` of Webster, arXiv:1309.3796v3, Proposition 4.21: the sum of
the idempotents of the loadings in which the red strands `c`, `c + 1` are adjacent, the image of
the unit of `T̃^λ` under splitting. -/
def splitTensorIdem : TensorProductAlgebra k Q Λ' ν :=
  π (f 1)

theorem isIdempotentElem_splitTensorIdem :
    IsIdempotentElem (splitTensorIdem c Q Λ' ν) := by
  rw [splitTensorIdem, IsIdempotentElem, ← map_mul, splitStendhalValue_one_mul]

variable (ν) in
/-- The corner `e T^{λ'} e`. -/
abbrev splitTensorCorner : Type _ :=
  (isIdempotentElem_splitTensorIdem c Q Λ' (ν := ν)).Corner

instance (priority := 1200) splitTensorCornerAlgebra :
    Algebra k (splitTensorCorner c Q Λ' ν) :=
  KLR.cornerAlgebra _

private def splitRedBeforeQuotient :
    StendhalAlgebra k Q (mergeWeights c Λ') ν →ₐ[k] splitTensorCorner c Q Λ' ν where
  toFun z :=
    ⟨π (f z), (Subsemigroup.mem_corner_iff
      (isIdempotentElem_splitTensorIdem c Q Λ' (ν := ν))).2
      ⟨by
        change π (f 1) * π (f z) = π (f z)
        rw [← map_mul, splitStendhalValue_one_mul],
       by
        change π (f z) * π (f 1) = π (f z)
        rw [← map_mul, splitStendhalValue_mul_one]⟩⟩
  map_one' := rfl
  map_zero' := by
    apply Subtype.ext
    exact (congrArg π (map_zero f)).trans (map_zero _)
  map_add' x y := by
    apply Subtype.ext
    exact (congrArg π (map_add f x y)).trans (map_add _ _ _)
  map_mul' x y := by
    apply Subtype.ext
    exact (congrArg π (map_mul f x y)).trans (map_mul _ _ _)
  commutes' a := by
    apply Subtype.ext
    change π (f (algebraMap k _ a)) = algebraMap k _ a * splitTensorIdem c Q Λ' ν
    rw [show algebraMap k (StendhalAlgebra k Q (mergeWeights c Λ') ν) a =
        a • (1 : StendhalAlgebra k Q (mergeWeights c Λ') ν) from Algebra.algebraMap_eq_smul_one a,
      splitStendhalValue_smul]
    exact (map_smul (TensorProductAlgebra.mk Q Λ' ν).toLinearMap a _).trans (Algebra.smul_def _ _)

private theorem splitRedBeforeQuotient_val (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    (splitRedBeforeQuotient c Q Λ' z).val = π (f z) := rfl

/-- Splitting the red strand `λ_c` induces a map `T^λ → e T^{λ'} e` (Webster,
arXiv:1309.3796v3, §4.3, Proposition 4.21). -/
def splitRed :
    TensorProductAlgebra k Q (mergeWeights c Λ') ν →ₐ[k]
      splitTensorCorner c Q Λ' ν := by
  let J := StendhalAlgebra.violatedIdeal k Q (mergeWeights c Λ') ν
  let φ := splitRedBeforeQuotient c Q Λ' (ν := ν)
  refine J.ringCon.liftₐ φ ?_
  change J.ringCon ≤ (TwoSidedIdeal.ker φ).ringCon
  rw [← TwoSidedIdeal.ringCon_le_iff]
  apply TwoSidedIdeal.span_le.2
  rintro _ ⟨s, hs, hV, rfl⟩
  change StendhalAlgebra.e s hs ∈ TwoSidedIdeal.ker φ
  apply (TwoSidedIdeal.mem_ker φ).2
  apply Subtype.ext
  change π (f (StendhalAlgebra.e s hs)) = 0
  rw [splitStendhalValue_e]
  change (StendhalAlgebra.violatedIdeal k Q Λ' ν).ringCon.mk' _ = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span ⟨_, _, (isViolated_splitLoading_iff c s).2 hV, rfl⟩

theorem splitRed_mk (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    (splitRed c Q Λ' (TensorProductAlgebra.mk Q (mergeWeights c Λ') ν z)).val = π (f z) := rfl

/-- The splitting map is onto the corner `e T^{λ'} e` (Webster, arXiv:1309.3796v3,
Proposition 4.21, spanning argument). -/
theorem splitRed_surjective : Function.Surjective (splitRed c Q Λ' (ν := ν)) := by
  classical
  intro y
  obtain ⟨x, hx⟩ := (StendhalAlgebra.violatedIdeal k Q Λ' ν).ringCon.mk'_surjective y.val
  change π x = y.val at hx
  have hmem : f 1 * x * f 1 ∈
      AddMonoidHom.mrange (f : StendhalAlgebra k Q (mergeWeights c Λ') ν →ₙ+* _).toAddMonoidHom := by
    rw [splitStendhalValue_one, Finset.sum_mul, Finset.sum_mul]
    refine sum_mem fun t _ => ?_
    rw [Finset.mul_sum]
    refine sum_mem fun s _ => ?_
    obtain ⟨z, hz⟩ := e_mul_mul_e_mem_range_splitStendhalValue c Λ' s.1 t.1 s.2 t.2 x
    exact ⟨z, hz⟩
  obtain ⟨z, hz⟩ := hmem
  refine ⟨TensorProductAlgebra.mk Q (mergeWeights c Λ') ν z, Subtype.ext ?_⟩
  rw [splitRed_mk]
  change π ((f : StendhalAlgebra k Q (mergeWeights c Λ') ν →ₙ+* _).toAddMonoidHom z) = y.val
  rw [hz, map_mul, map_mul, hx]
  change splitTensorIdem c Q Λ' ν * y.val *
    splitTensorIdem c Q Λ' ν = y.val
  rw [KLR.Corner.E_mul_val, KLR.Corner.val_mul_E]

/-- Once splitting is injective before quotienting, the violating ideals match and splitting is
injective on `T^λ` (Webster, arXiv:1309.3796v3, Proposition 4.21, proof). -/
theorem splitRed_injective_of_stendhal (hf : Function.Injective f) :
    Function.Injective (splitRed c Q Λ' (ν := ν)) := by
  let J₀ := StendhalAlgebra.violatedIdeal k Q (mergeWeights c Λ') ν
  let J := StendhalAlgebra.violatedIdeal k Q Λ' ν
  intro x y hxy
  obtain ⟨b, rfl⟩ := J₀.ringCon.mk'_surjective x
  obtain ⟨b', rfl⟩ := J₀.ringCon.mk'_surjective y
  have he : J.ringCon.mk' (f b) = J.ringCon.mk' (f b') := congrArg Subtype.val hxy
  have hmem : f (b - b') ∈ J := by
    rw [map_sub]
    exact (TwoSidedIdeal.rel_iff _ _ _).1 (J.ringCon.eq.1 he)
  obtain ⟨g, hg, h⟩ := exists_violated_split c Λ' (f (b - b')) hmem
  have hh : f 1 * f (b - b') * f 1 = f (b - b') := by
    rw [splitStendhalValue_one_mul, splitStendhalValue_mul_one]
  have heq := hf (h.trans hh)
  exact J₀.ringCon.eq.2 ((TwoSidedIdeal.rel_iff _ _ _).2 (heq ▸ hg))

/-- Splitting is injective on `T^λ` for the crossing parameters of Webster, arXiv:1309.3796v3,
§2.2. -/
theorem splitRed_injective {D : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ D Q) :
    Function.Injective (splitRed c Q Λ' (ν := ν)) :=
  splitRed_injective_of_stendhal c Q Λ' (splitStendhalValue_injective c Λ' hQ)

/-- **Splitting a red strand** (Webster, arXiv:1309.3796v3, §4.3, Proposition 4.21): for the
crossing parameters of §2.2, `T^λ ≅ e T^{λ'} e`, where `λ'` splits `λ_c` into
`λ'_c + λ'_{c+1}` and `e` is the sum of the idempotents of the loadings in which the red strands
`c`, `c + 1` are adjacent. -/
def splitRedEquiv {D : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ D Q) :
    TensorProductAlgebra k Q (mergeWeights c Λ') ν ≃ₐ[k]
      splitTensorCorner c Q Λ' ν :=
  AlgEquiv.ofBijective (splitRed c Q Λ') ⟨splitRed_injective c Q Λ' hQ, splitRed_surjective c Q Λ'⟩

@[simp] theorem splitRedEquiv_apply {D : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ D Q)
    (a : TensorProductAlgebra k Q (mergeWeights c Λ') ν) :
    splitRedEquiv c Q Λ' hQ a = splitRed c Q Λ' a := rfl

end Categorification.Stendhal.SplitRed
