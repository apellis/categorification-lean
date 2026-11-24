/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelRelabel
import Categorification.WeightedKLR.RedStrands.FirstWeightBlockKernel
import Categorification.WeightedKLR.RedStrands.OneBlackAdjacentPairFiltration

/-!
# One-black higher kernel filtration in every red word

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The canonical-order construction transports to any red word with the given
adjacent pair.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ}

/-- With one black, the ordinary crossing test holds at every red position
over any commutative ring with symmetric KLR parameters. -/
theorem oneBlack_crossing_injective
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I)
    (hQ : KLRSymm Q) : OrdinaryOneBlackTests Q Λ (i := i) := by
  intro s hs j hj hb
  have word : redWord s = List.finRange ℓ := (redWord_eq_finRange_iff s).2 hs
  have order : redWord (sadj _ j • s) = redWord s :=
    redWord_sadj_smul s hj (by simp [hb])
  exact ordinary_crossing_test_of_violated_cancel Q Λ word order j rfl hQ
    (fun z hz => firstWeight_viol_exit_cross_cancel i Q Λ s j hj hQ hb z hz)

/-- The higher kernel has a finite filtration by actual partial standards for
every one-black loading and adjacent red pair, with arbitrary symmetric parameters. -/
theorem oneBlack_hasFiltration
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (hQ : KLRSymm Q)
    (a b : Fin ℓ) {κ L M : List (Fin ℓ)} (hword : κ = L ++ a :: b :: M)
    (s : {s : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord s = κ}) :
    ∃ tail : List {t : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord t = κ},
      HasFiltration (fun t => blockPartialStandardAt Q Λ t.1 a b κ t.2)
        tail (fixedOrderKernelObj Q Λ a b κ s) := by
  have canonical : CanonicalAdjacentPairKernelFiltrations Q ({i} : Multiset I) ℓ := by
    intro weights c d L₀ M₀ word source
    exact oneBlack_pair_hasFiltration_of_tests Q weights c d word hQ
      (oneBlack_crossing_injective Q weights i hQ) source
  exact blockLoadingKernel_hasFiltration_of_canonical Q canonical Λ a b hword s

/-- For the first red pair in canonical order, each spectator left of the
black gives one layer of the actual higher kernel filtration. -/
theorem oneBlack_firstPair_hasFiltration {m : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (m + 2) → I →₀ ℕ) (i : I)
    (hQ : KLRSymm Q)
    (s : {s : Seq (stendhalWeight (m + 2) ({i} : Multiset I)) // redWord s = List.finRange (m + 2)}) :
    ∃ p : Fin (stendhalWeight (m + 2) ({i} : Multiset I)).card, s.1.lbl p = .inl i ∧
      ∃ tail : List {t : Seq (stendhalWeight (m + 2) ({i} : Multiset I)) // redWord t = List.finRange (m + 2)},
        tail.length = p.val - 2 ∧
        HasFiltration (fun t => blockPartialStandardAt Q Λ t.1 0 1 (List.finRange (m + 2)) t.2)
          tail (fixedOrderKernelObj Q Λ 0 1 (List.finRange (m + 2)) s) :=
  oneBlack_firstPair_hasFiltration_of_tests Q Λ hQ
    (oneBlack_crossing_injective Q Λ i hQ) s

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration QuantumGroup KL3.Diagram
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {D : CartanDatum I}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- The one-black kernel has the actual higher partial-standard filtration at
standard parameters for any adjacent pair in any red word. -/
theorem oneBlack_hasFiltration_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (i : I) (Λ : Fin ℓ → I →₀ ℕ)
    (a b : Fin ℓ) {κ L M : List (Fin ℓ)} (hword : κ = L ++ a :: b :: M)
    (s : {s : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord s = κ}) :
    ∃ tail : List {t : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord t = κ},
      HasFiltration (fun t => blockPartialStandardAt QL Λ t.1 a b κ t.2)
        tail (fixedOrderKernelObj QL Λ a b κ s) := by
  have canonical : CanonicalAdjacentPairKernelFiltrations QL ({i} : Multiset I) ℓ := by
    intro weights c d L₀ M₀ word source
    exact oneBlack_pair_hasFiltration_standard hR hQ i weights c d word source
  exact blockLoadingKernel_hasFiltration_of_canonical QL canonical Λ a b hword s

end Categorification.Stendhal.BraidedStendhalAlgebra
