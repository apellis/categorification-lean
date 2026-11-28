/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyFiltration

/-!
# Block embeddings preserve the Mackey filtration

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19 (Claim A of the filtration of
`S_+(X) e_win` used for the trace half): diagrams placed on a block of consecutive strands
(`KLRAlgebra.BlockEmb`) lying on one side of the top cut at `n` preserve every step of the
Mackey filtration of that cut (`KLRAlgebra.preservesMackeyFilt_blockEmb`). The window algebra
acts in this way, at a cut at the end of the window.

## Main results

* `KLR.KLRAlgebra.preservesMackeyFilt_sum_e`, `KLR.KLRAlgebra.preservesMackeyFilt_blockEmb`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial

attribute [local instance 2000] KLR.cornerAlgebra

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]
  {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

variable {n n'' : ℕ}

theorem preservesMackeyFilt_zero : PreservesMackeyFilt n n'' (0 : KLRAlgebra k Q μ) :=
  fun _ _ _ => by rw [zero_mul]; exact zero_mem _

theorem PreservesMackeyFilt.smul {z : KLRAlgebra k Q μ} (hz : PreservesMackeyFilt n n'' z)
    (c : k) : PreservesMackeyFilt n n'' (c • z) :=
  fun c' y hy => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c (hz c' y hy)

theorem preservesMackeyFilt_sum {ι : Type*} (s : Finset ι) {z : ι → KLRAlgebra k Q μ}
    (hz : ∀ i ∈ s, PreservesMackeyFilt n n'' (z i)) :
    PreservesMackeyFilt n n'' (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact preservesMackeyFilt_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hz a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hz i (Finset.mem_insert_of_mem hi))

theorem preservesMackeyFilt_sum_e (T : Finset (Seq μ)) :
    PreservesMackeyFilt n n'' (eSum Q T : KLRAlgebra k Q μ) :=
  preservesMackeyFilt_sum T fun s _ => preservesMackeyFilt_e s

variable {μ' : Multiset I} {T : Finset (Seq μ)}

/-- **Diagrams on a block on one side of the top cut preserve the Mackey filtration**: for a
block embedding `B` of `R(μ')` on the strands `[o, o + |μ'|)`, with `o + |μ'| ≤ n` or
`n ≤ o`, every element `B(x)` preserves every step of the Mackey filtration of the top cut at
`n`. -/
theorem preservesMackeyFilt_blockEmb (B : BlockEmb μ' μ T)
    (hB : B.o + Multiset.card μ' ≤ n ∨ n ≤ B.o) (x : KLRAlgebra k Q μ') :
    PreservesMackeyFilt n n'' (B.hom Q x).val := by
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel k Q μ') x
  change PreservesMackeyFilt n n'' (B.hom Q (KLRAlgebra.mk k Q μ' a)).val
  rw [B.hom_mk]
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, Corner.val_smul]
    exact (preservesMackeyFilt_sum_e T).smul c
  | grade1 g =>
    rw [BlockEmb.freeHom, FreeAlgebra.lift_ι_apply]
    cases g with
    | idem i => exact preservesMackeyFilt_sum_e _
    | dot a =>
      change PreservesMackeyFilt n n'' (pol (X (B.pos a)) * eSum Q T)
      exact PreservesMackeyFilt.mul (preservesMackeyFilt_pol _) (preservesMackeyFilt_sum_e T)
    | cross l =>
      change PreservesMackeyFilt n n'' (B.gψ Q l).val
      by_cases hl : l + 1 < Multiset.card μ'
      · rw [B.val_gψ hl]
        refine PreservesMackeyFilt.mul (preservesMackeyFilt_ψ ?_) (preservesMackeyFilt_sum_e T)
        omega
      · rw [B.gψ_of_not_lt hl]
        exact preservesMackeyFilt_zero
  | mul a b ha hb =>
    rw [map_mul, Corner.val_mul]
    exact ha.mul hb
  | add a b ha hb =>
    rw [map_add]
    exact ha.add hb

end Categorification.KLR.KLRAlgebra
