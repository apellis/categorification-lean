/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockIC

/-!
# The mirror identity (IC′)

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the mirror (IC′) of the identity (IC),
at `ℓ = 0`. Write `c^♭(w) = flip_D(c(flip w))` for the flipped trace, with `flip` the top–bottom
flip of `A = T̃^{λ⁺}` and `flip_D` the flip of both factors of `D`. Then every `k`-linear
`G : A → D` with `G(ι_R(d') y) = swap(d') G(y)` is `y ↦ c^♭(y z)` for exactly one `z ∈ A e_L`
(`existsUnique_flipTrace_mul_eq`): the map `A e_L → Hom_{D_R}(e_R A, D)`, `z ↦ (y ↦ c^♭(y z))`,
is bijective.

Proof: the flip is an anti-automorphism exchanging `e_L A` with `A e_L` and `A e_R` with `e_R A`;
it carries `ι` to `ι ∘ flip_D` and `ι_R` to `ι_R ∘ flip_{D_R}`, and `flip_D ∘ swap = swap ∘
flip_{D_R}` (`flipD_comm`). So `F = flip_D ∘ G ∘ flip` satisfies the hypothesis of (IC)
(`existsUnique_blockTrace_mul_eq`), and `z ↦ flip z` matches the two solutions.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, `ℓ = 0`.

## Main results

* `CupCap.flipD_comm`: the flips commute with the exchange of the factors.
* `CupCap.existsUnique_flipTrace_mul_eq`: (IC′).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 0 → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 le_rfl) (ν + ν₀)

/-- The flips of `D` and `D_R` commute with the exchange of the factors. -/
theorem flipD_comm (d' : Tc ⊗[k] T) :
    flipD Q Λ Λc ν ν₀ (TensorProduct.comm k Tc T d') =
      TensorProduct.comm k Tc T (flipDF Q Λ Λc ν ν₀ d') := by
  induction d' using TensorProduct.inductionOn with
  | tmul y x => rw [TensorProduct.comm_tmul, flipD_tmul, flipDF_tmul, TensorProduct.comm_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight 0 ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}
  [DecidableEq (EndGen ν₀ ρ₁)]

variable (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)

include hQ hρ₁ hρ₂ hρ₃

/-- **(IC′)**: every `k`-linear `G : A → D` with `G(ι_R(d') y) = swap(d') G(y)` is
`y ↦ flip_D(c(flip(y z)))` for exactly one `z` with `z e_L = z`. -/
theorem existsUnique_flipTrace_mul_eq (G : Tp →ₗ[k] T ⊗[k] Tc)
    (hG : ∀ (y : Tp) (d' : Tc ⊗[k] T),
      G (blockTensorR Q Λ Λc ν ν₀ d' * y) = TensorProduct.comm k Tc T d' * G y) :
    ∃! z : Tp, z * endStendhal Q Λ Λc ν ν₀ 1 = z ∧
      ∀ y : Tp, flipD Q Λ Λc ν ν₀
        (blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (StendhalAlgebra.flip (y * z))) = G y := by
  set F : Tp →ₗ[k] T ⊗[k] Tc :=
    (flipD Q Λ Λc ν ν₀).comp (G.comp (flipLin Q (plusLabels Λ Λc 0 le_rfl) (ν + ν₀))) with hFd
  have hFa : ∀ y, F y = flipD Q Λ Λc ν ν₀ (G (StendhalAlgebra.flip y)) := fun _ => rfl
  have hF : ∀ (y : Tp) (d' : Tc ⊗[k] T),
      F (y * blockTensorR Q Λ Λc ν ν₀ d') = F y * TensorProduct.comm k Tc T d' := by
    intro y d'
    rw [hFa, hFa, StendhalAlgebra.flip_mul, flip_blockTensorR, hG, flipD_mul, ← flipD_comm,
      flipD_flipD]
  obtain ⟨z₀, ⟨hz₀, hz₀F⟩, huniq⟩ := existsUnique_blockTrace_mul_eq hQ hρ₁ hρ₂ hρ₃ F hF
  refine ⟨StendhalAlgebra.flip z₀, ⟨?_, fun y => ?_⟩, fun z ⟨hz, hzG⟩ => ?_⟩
  · rw [← flip_endStendhal_one, ← StendhalAlgebra.flip_mul, hz₀]
  · rw [StendhalAlgebra.flip_mul, StendhalAlgebra.flip_flip, hz₀F, hFa, flipD_flipD,
      StendhalAlgebra.flip_flip]
  · have h1 : StendhalAlgebra.flip z = z₀ := by
      refine huniq _ ⟨?_, fun y => ?_⟩
      · rw [← flip_endStendhal_one, ← StendhalAlgebra.flip_mul, hz]
      · rw [hFa, ← hzG, flipD_flipD, StendhalAlgebra.flip_mul, StendhalAlgebra.flip_flip]
    rw [← h1, StendhalAlgebra.flip_flip]

end Categorification.Stendhal.CupCap
