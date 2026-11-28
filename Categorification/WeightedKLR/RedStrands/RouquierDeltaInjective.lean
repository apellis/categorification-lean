/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCountQ

/-!
# The route hypothesis of Proposition 5.5 for Rouquier parameters

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5: for Rouquier parameters `Q`, the map `δ₁` is injective on every
finite-dimensional module (`allFiniteDeltaInjective_of_rouquier`). This file restates it for an
arbitrary decidable equality on the colours, so that statements made with `[DecidableEq I]` can
discharge `AllFiniteDeltaInjective` instead of assuming it.
-/

namespace Categorification.Stendhal

open KLR QuantumGroup

/-- **`AllFiniteDeltaInjective` holds for Rouquier parameters** (Webster, arXiv:1309.3796v3,
proof of Proposition 5.5), for any decidable equality on the colours. -/
theorem allFiniteDeltaInjective_of_isRouquierQ {I : Type} [inst : DecidableEq I] {k : Type}
    [Field k] {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
    (hQs : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) : AllFiniteDeltaInjective Q Λ hQs := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  exact allFiniteDeltaInjective_of_rouquier hQ hQs

end Categorification.Stendhal
