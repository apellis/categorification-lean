/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiniteHigherKernelChain
import Categorification.WeightedKLR.RedStrands.OneBlackHigherCrossing
import Categorification.WeightedKLR.RedStrands.OrdinaryRetainedCrossing

/-!
# Actual crossing steps in one-black higher-kernel chains

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
An ordinary crossing test supplies a projective identification for a strictly
higher red–black crossing. A maximal surviving loading closes the chain.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "C" => {s : Seq μ // redWord s = List.finRange ℓ}

/-- Prepend an actual higher red-black crossing to a chain at one black. -/
theorem HigherProjectiveChain.cons_of_oneBlack_ordinary_test
    {s t : C} {tail : List C} {a b r : Fin ℓ} {L M : List (Fin ℓ)}
    (hs : redWord s.1 = L ++ a :: b :: M)
    (hlt : adjacentBlockRoot a b s.1 < adjacentBlockRoot a b t.1)
    (j : ℕ) (hj : j + 1 < n) (hstep : TypeA.sadj n j • s.1 = t.1)
    (hr : s.1.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
    (hb : s.1.lbl ⟨j + 1, hj⟩ = .inl i)
    (hQ : KLRSymm Q)
    (test : ∀ x : TensorProductAlgebra k Q Λ ν,
      x * tensorOfKLR Q Λ ν (KLRAlgebra.e t.1) = x →
      x * tensorOfKLR Q Λ ν (KLRAlgebra.ψ j * KLRAlgebra.e s.1) = 0 → x = 0)
    (chain : HigherProjectiveChain Q Λ a b (List.finRange ℓ) t tail) :
    HigherProjectiveChain Q Λ a b (List.finRange ℓ) s (t :: tail) := by
  have ho := t.2.trans s.2.symm
  have hi := crossingIntoKernelMap_injective_of_ordinary_test Q Λ s.2 ho j hstep a b hlt hQ test
  have hu := crossingIntoKernelMap_oneBlack_surjective Q Λ hs ho hlt j hj hstep hr hb
  refine .cons hlt ⟨?_⟩ chain
  have transport (κ : List (Fin ℓ)) (hκ : redWord s.1 = κ) :
      (rIdeal (orderedLoadingIdemAt Q Λ κ t.1 (ho.trans hκ))) ≃ₗ[
        (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ))ᵐᵒᵖ]
        fixedOrderKernelObj Q Λ a b κ ⟨s.1, hκ⟩ := by
    subst κ
    exact LinearEquiv.ofBijective (crossingIntoKernelMap Q Λ a b ho hlt j) ⟨hi, hu⟩
  exact transport _ s.2


/-- End a chain when all strictly higher loadings in the corner are violated. -/
theorem HigherProjectiveChain.nil_of_maximal
    {s : C} {a b : Fin ℓ}
    (hmax : ∀ w : Seq μ, redWord w = redWord s.1 →
      adjacentBlockRoot a b s.1 < adjacentBlockRoot a b w → IsViolated w) :
    HigherProjectiveChain Q Λ a b (List.finRange ℓ) s [] := by
  apply HigherProjectiveChain.nil
  have hbot := blockLoadingKernel_eq_bot_of_maximal Q Λ s.1 a b hmax
  have aux (κ : List (Fin ℓ)) (hκ : redWord s.1 = κ) :
      Subsingleton (fixedOrderKernelObj Q Λ a b κ ⟨s.1, hκ⟩) := by
    subst κ
    change Subsingleton (blockLoadingKernel Q Λ s.1 a b)
    rw [hbot]
    infer_instance
  exact aux _ s.2

end Categorification.Stendhal.BraidedStendhalAlgebra
