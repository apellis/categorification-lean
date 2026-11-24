/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OneBlackAdjacentPairFiltration
import Categorification.WeightedKLR.RedStrands.BlockKernelRelabel

/-!
# Projectivity of the one-black higher loading kernel

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The first step of a higher-projective chain identifies the kernel with a
loading projective. Red relabelling transports that projectivity to any
red word.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
variable (Q : I → I → MvPolynomial (Fin 2) k)
local notation "ν₁" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν₁

/-- A one-black kernel is projective in any red word once the ordinary
crossing tests are given for every permuted red weight. -/
theorem oneBlack_kernel_projective_of_tests
    (hQ : KLRSymm Q)
    (tests : ∀ Λ : Fin ℓ → I →₀ ℕ, OrdinaryOneBlackTests Q Λ (i := i))
    (Λ : Fin ℓ → I →₀ ℕ) (a b : Fin ℓ) {κ L M : List (Fin ℓ)}
    (hword : κ = L ++ a :: b :: M) (s : {s : Seq μ // redWord s = κ}) :
    Module.Projective
      (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₁ κ))ᵐᵒᵖ
      (fixedOrderKernelObj Q Λ a b κ s) := by
  refine adjacentPairProperty_of_canonical
    (ν := (Singleton.singleton i : Multiset I))
    (fun W c d order t =>
      Module.Projective
        (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q W ν₁ order))ᵐᵒᵖ
        (fixedOrderKernelObj Q W c d order t)) ?_ ?_ Λ a b hword s
  · intro σ W c d order t proj
    let e := fixedOrderKernelObj_redPermSemilinearEquiv Q (Λ := W) (Λ' := W ∘ σ)
      σ (fun _ => rfl) t.1 order t.2 c d
    exact @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ e proj
  · intro W c d L₀ M₀ hcanonical t
    have hm : (Sum.inl i : I ⊕ Fin ℓ) ∈ μ := by simp [stendhalWeight]
    rw [← show Finset.univ.val.map t.1.lbl = μ from t.1.2, Multiset.mem_map] at hm
    obtain ⟨p, _, hp⟩ := hm
    obtain ⟨tail, chain⟩ := oneBlack_pair_higherProjectiveChain_of_tests
      Q W c d (canonicalAdjacentRedValues hcanonical) hcanonical hQ (tests W) t p hp
    exact HigherProjectiveChain.projective_source Q W c d (List.finRange ℓ) chain

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR QuantumGroup KL3.Diagram
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {D : CartanDatum I}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- The actual one-black loading kernel in (6.21) is projective at standard parameters. -/
theorem oneBlack_kernel_projective_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (i : I) (Λ : Fin ℓ → I →₀ ℕ)
    (a b : Fin ℓ) {L M : List (Fin ℓ)}
    (s : Seq (stendhalWeight ℓ ({i} : Multiset I))) (hword : redWord s = L ++ a :: b :: M) :
    Module.Projective
      (IsIdempotentElem.Corner
        (isIdempotentElem_violMk_redProj k QL Λ ({i} : Multiset I) (redWord s)))ᵐᵒᵖ
      (blockLoadingKernel QL Λ s a b) := by
  have tests (W : Fin ℓ → I →₀ ℕ) : OrdinaryOneBlackTests QL W (i := i) :=
    oneBlack_crossing_injective_standard hR hQ i W
  exact oneBlack_kernel_projective_of_tests QL hQ tests Λ a b hword ⟨s, rfl⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
