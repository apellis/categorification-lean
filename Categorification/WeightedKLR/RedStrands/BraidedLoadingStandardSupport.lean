/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardization
import Categorification.WeightedKLR.RedStrands.ConcatLoadingOrder
import Categorification.WeightedKLR.RedStrands.LeftStandardSupport

/-!
# Loading support of opposite braid standards

Webster, arXiv:1309.3796v2, proof of Lemma 6.11. A coefficient-layer label
that is not strictly above the resolved standard label is annihilated by every
higher loading idempotent of the resolution. The ordinary statement follows by
transporting the left-standard support through the coefficient equivalence.
-/

namespace Categorification.Stendhal

open KLR

variable {I : Type} [DecidableEq I] {ℓ : ℕ}

/-- A loading strictly above the argument of Lemma 6.11 is outside the lower order
ideal of every opposite label that is not strictly above that argument. -/
theorem not_stendhalLE_of_lt_of_not_lt {μ : Multiset (I ⊕ Fin ℓ)} {s d t : Seq μ}
    (hsd : StendhalLT s d) (hst : ¬ StendhalLT s t) : ¬ StendhalLE d t := by
  intro hdt
  apply hst
  exact ⟨stendhalLE_trans hsd.1 hdt, fun hts => hsd.2 (stendhalLE_trans hdt hts)⟩

namespace BraidedStendhalAlgebra

open Equiv MulOpposite TypeA

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "μ" => stendhalWeight ℓ ν

include hρ hQ in
/-- The coefficient equivalence transports the support of the left standard
to the right loading standard of the opposite braid corner. -/
theorem violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_le
    {t d : Seq μ} (ht : IsRedOrdered t) (hd : IsRedOrdered d) (hdt : ¬ StendhalLE d t)
    (m : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ) :
    op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hd)) • m = 0 := by
  let E := loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ ht
  apply E.injective
  rw [E.map_smulₛₗ, map_zero]
  change leftCoefficientEquiv (Λ := Λ) hρ hQ σ
    (op (violLoadingIdem (redWord_relabel σ hd))) • E m = 0
  rw [leftCoefficientEquiv_loadingIdem]
  exact seqIdem_smul_leftStandard_eq_zero_of_not_stendhalLE ht hd hdt (E m)

include hρ hQ in
/-- Webster, arXiv:1309.3796v2, proof of Lemma 6.11. Every higher loading of the
resolved standard annihilates an opposite layer whose label is not higher. -/
theorem violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_lt
    {s t d : Seq μ} (ht : IsRedOrdered t) (hd : IsRedOrdered d)
    (hsd : StendhalLT s d) (hst : ¬ StendhalLT s t)
    (m : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ) :
    op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hd)) • m = 0 :=
  violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_le hρ hQ σ ht hd
    (not_stendhalLE_of_lt_of_not_lt hsd hst) m

end BraidedStendhalAlgebra
end Categorification.Stendhal
