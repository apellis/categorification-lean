/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelRelabel
import Categorification.WeightedKLR.RedStrands.OneBlackAdjacentPairFiltration

/-!
# One-black higher kernel filtration in every red word

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The canonical-order construction transports to any red word with the given
adjacent pair.
-/

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
