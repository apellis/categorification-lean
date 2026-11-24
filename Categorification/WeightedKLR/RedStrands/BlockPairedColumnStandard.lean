/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockPairedColumnInjection
import Categorification.WeightedKLR.RedStrands.TwoRedCrossingInjectivity

/-!
# Right crossing on the source column at standard parameters

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8, (6.21).
At standard Khovanov–Lauda parameters, the ordered two-red right crossing
supplies the internal support test for the adjacent source-order column.
-/

namespace Categorification.Stendhal.RedBlock

open KLR KLRAlgebra TypeA BraidedStendhalAlgebra QuantumGroup

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
    (C : CartanDatum I) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}

local notation "Q" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "row" => adjacentRow L M f β
local notation "μ" => stendhalWeight ℓ ν
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1)
  (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) κ
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))

/-- The supported black–second-red crossing detects zero on the source-order
column at standard parameters over a field. -/
theorem blockColumn_eq_zero_of_standard_paired_crossing
    (hR : IsRouquierQ C Q) (hQ : KLRSymm Q)
    (h : weightSum row = μ) (t s : Seq μ) (j : ℕ) (hj : j+1 < (weightSum row).card) (i : I)
    (ht : redWord t = κ) :
    let s₀ := sadj (Multiset.card μ) j • s
    let source := Seq.cast h.symm s₀
    redWord s₀ = κ → source.lbl ⟨j,by omega⟩ = .inl i → source.lbl ⟨j+1,hj⟩ = .inr (f 1) →
    ∀ x : blockColumn Q Λ L M f β h,
      π (e t) * x.1 = x.1 → x.1 * π (e s₀) = x.1 → x.1 * π (ψ j * e s) = 0 → x = 0 := by
  apply blockColumn_eq_zero_of_ordered_paired_crossing Q Λ hQ L M f β h t s j hj i _ ht
  intro r a ha hord hblack hred
  exact (IsSecondRedCrossing.eq_zero_of_mul hR hQ (Λ ∘ f)
    (isSecondRedCrossing_of_labels r hord i ha hblack hred)).2.2

end Categorification.Stendhal.RedBlock
