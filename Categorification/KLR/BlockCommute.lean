/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Concat

/-!
# Block embeddings on disjoint blocks commute

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6: diagrams placed side by side commute. For two block
embeddings `B`, `B'` of `KLRAlgebra.BlockEmb` into the same corner `e_T R(ν) e_T`, with the block
of `B` to the left of the block of `B'`, and with the fibres of each stable under the crossings
of the other block, the images of `B` and `B'` commute (`KLRAlgebra.BlockEmb.commute_hom`).

## Main results

* `KLRAlgebra.BlockEmb.commute_hom`: images of block embeddings on disjoint blocks commute.
-/

namespace Categorification.KLR

namespace KLRAlgebra

open TypeA

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]
  {Q : I → I → MvPolynomial (Fin 2) k} {μ μ' ν : Multiset I} {T : Finset (Seq ν)}

local notation "M" => Multiset.card ν

/-- **Block embeddings on disjoint blocks commute**: if the block of `B` lies to the left of the
block of `B'`, and the fibres of each are stable under the crossings of the other block, then
the images of `B` and `B'` commute. -/
theorem BlockEmb.commute_hom (B : BlockEmb μ ν T) (B' : BlockEmb μ' ν T)
    (hle : B.o + Multiset.card μ ≤ B'.o)
    (hB : ∀ i l, l + 1 < Multiset.card μ' → ∀ s,
      s ∈ B.F i ↔ sadj M (B'.o + l) • s ∈ B.F i)
    (hB' : ∀ i l, l + 1 < Multiset.card μ → ∀ s,
      s ∈ B'.F i ↔ sadj M (B.o + l) • s ∈ B'.F i)
    (a : KLRAlgebra k Q μ) (b : KLRAlgebra k Q μ') : Commute (B.hom Q a) (B'.hom Q b) := by
  refine commute_of_gen _ _ (fun g g' => ?_) a b
  have hmk : ∀ {μ : Multiset I} (g : Gen μ), KLRAlgebra.mk k Q μ (FreeAlgebra.ι k g) =
      match g with
      | .idem i => e i
      | .dot a => x a
      | .cross j => ψ j := by
    intro μ g; cases g <;> rfl
  rw [hmk, hmk]
  rcases g with i | c | l <;> rcases g' with j | c' | l'
  · simp only [BlockEmb.hom_e]
    refine Corner.ext ?_
    simp only [Corner.val_mul, BlockEmb.val_gE, BlockEmb.eF, eSum_mul_eSum, Finset.inter_comm]
  · simp only [BlockEmb.hom_e, BlockEmb.hom_x]
    exact (B.polCorner_mul_gE _ i).symm
  · simp only [BlockEmb.hom_e, BlockEmb.hom_ψ]
    exact B.gE_mul_gψ B' i l' fun hl s => hB i l' hl s
  · simp only [BlockEmb.hom_e, BlockEmb.hom_x]
    exact B'.polCorner_mul_gE _ j
  · simp only [BlockEmb.hom_x]
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  · simp only [BlockEmb.hom_x, BlockEmb.hom_ψ]
    refine B'.polCorner_X_mul_gψ _ l' fun _ => ?_
    rw [B.pos_val]
    have := c.2
    omega
  · simp only [BlockEmb.hom_e, BlockEmb.hom_ψ]
    exact (B'.gE_mul_gψ B j l fun hl s => hB' j l hl s).symm
  · simp only [BlockEmb.hom_x, BlockEmb.hom_ψ]
    refine (B.polCorner_X_mul_gψ _ l fun hl => ?_).symm
    rw [B'.pos_val]
    omega
  · simp only [BlockEmb.hom_ψ]
    refine B.gψ_mul_gψ' B' l l' fun hl _ => ?_
    omega

end KLRAlgebra

end Categorification.KLR
