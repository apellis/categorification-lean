/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InterleavedMarkedColumn
import Categorification.WeightedKLR.RedStrands.BlockPairedColumnStandard

/-!
# The marked-column injection at standard parameters

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, (6.21). A single black strand
between the exchanged reds gives the two-exit presentation. For Rouquier parameters its right joint leg is injective on the supported
partially standardized corner.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA QuantumGroup KL3.Diagram

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
    (C : CartanDatum I) (Λ : Fin ℓ → I →₀ ℕ)

variable {Q : I → I → MvPolynomial (Fin 2) k}
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ

/-- The marked-column kernel inclusion for one intervening black strand, with
arbitrary exterior strands and pairings at standard parameters. -/
theorem interleaved_markedColumn_injective_standard
    (hR : IsRouquierQ C Q) (hQ : KLRSymm Q) (t s : Seq μ) (a b : Fin ℓ)
    (j : ℕ) (hj : j+2 < n) {i : I} {Lr Mr : List (Fin ℓ)}
    (ht : redWord t = Lr ++ a :: b :: Mr)
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a)
    (ho : redWord (wordProd n [j,j+1,j] • s) = redWord t) :
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s) := by
  refine interleaved_markedColumn_injective_of_right_leg Q Λ t s a b j hj hQ ht hb hi ha ho ?_
  intro x hleft hmul
  have hnd : (Lr ++ a :: b :: Mr).Nodup := ht ▸ redWord_nodup t
  have hab : a ≠ b := fun he =>
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (he ▸ List.mem_cons_self)
  let f : Fin 2 ↪ Fin ℓ := ⟨![a,b], by
    intro p q hpq
    fin_cases p <;> fin_cases q
    · rfl
    · exact (hab (by simpa using hpq)).elim
    · exact (hab (by simpa using hpq.symm)).elim
    · rfl⟩
  have hfa : f 0 = a := rfl
  have hfb : f 1 = b := rfl
  let s' := wordProd n [j,j+1] • s
  have hs' : sadj n (j+1) • s' = wordProd n [j,j+1,j] • s := by
    simpa only [s', wordProd_cons, wordProd_nil, mul_one, mul_smul] using (braid_smul hj s).symm
  have hsource : redWord (sadj n (j+1) • s') = redWord t := hs' ▸ ho
  have hblack : (sadj n (j+1) • s').lbl ⟨j+1,by omega⟩ = .inl i := by
    rw [hs']
    exact (braid_smul_apply_one hj s).trans hi
  have hred : (sadj n (j+1) • s').lbl ⟨j+2,hj⟩ = .inr (f 1) := by
    rw [hs', hfb]
    exact (braid_smul_apply_two hj s).trans hb
  refine RedBlock.mem_blockUpperIdeal_of_standard_paired_crossing C Λ f hR hQ Lr Mr
    t s' (j+1) (by omega) i ht hsource hblack hred x ?_ ?_
  · rwa [hs']
  · simpa only [s', ψw_cons, ψw_nil, mul_one, hfa, hfb] using hmul

end Categorification.Stendhal.BraidedStendhalAlgebra
