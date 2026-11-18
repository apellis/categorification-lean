/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorShapovalov

/-!
# The one-fundamental example for the projective commutator

Webster, arXiv:1309.3796v2, §4.7, after Definition 4.34 and Lemma 4.35.
Take one red fundamental strand immediately left of a single downward black strand.
Deleting the black strand preserves the red position zero. The printed deletion
formula subtracts one there. The commutator acts on the input of the lowering,
whose coroot weight is one. The printed region after the lowering has weight minus one.
-/

noncomputable section

namespace Categorification.Stendhal.ProjectiveCommutator

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop TensorPairing LusztigF

/-- The printed deletion coordinate is outside the allowed range already for
the first black strand after a red strand, where both κ and j are zero. -/
theorem printed_deletion_out_of_range :
    ¬ ∃ k : ℕ, (k : ℤ) = (0 : ℤ) - (if (0 : ℕ) ≤ 0 + 1 then 1 else 0) := by
  simp

/-- Evaluating the fundamental and lowered weights on the simple coroot. -/
theorem fundamental_commutator_weights :
    fundamental.1 (sl2RootDatum.coroot ()) = 1 ∧
    (fundamental.1 - sl2RootDatum.root ()) (sl2RootDatum.coroot ()) = -1 := by
  decide

local notation "q" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩
local notation "h" => IrreducibleModule.hwv sl2RootDatum q (Subtype.val fundamental)
local notation "e" => E sl2RootDatum q ()
local notation "f" => F sl2RootDatum q ()

/-- The one-factor module distinguishes the two sides of the commutator:
the EF word returns the nonzero highest vector and FE vanishes. -/
theorem fundamental_commutator_on_highest :
    e • (f • h) = h ∧ f • (e • h) = 0 ∧ h ≠ 0 := by
  exact ⟨E_first, by rw [IrreducibleModule.E_smul_hwv, smul_zero],
    hwv_ne_zero sl2XRegular hvn_ratFunc _⟩

end Categorification.Stendhal.ProjectiveCommutator
