/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleAction
import Categorification.KLR.IndPrefixVanish

/-!
# Loadings with no last red strand near the left kill the parabolic shuffle module

Webster, arXiv:1309.3796v3, proof of Proposition 5.5. In the module induced from the
preceding tensor product algebra and the final cyclotomic factor, the final factor kills every
loading that starts with a black strand. Hence `e(s)` acts by zero whenever the last red strand
does not occur among the first `|α| + 1` positions of `s`, where `α` is the weight of the
preceding factor (`e_smul_ind_eq_zero`). This disposes of the error terms of the Mackey
intertwining used to build the map `δ₁` of that proof.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) (α+δ)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

omit [DecidableEq I] in
private theorem card_last_pos : 0 < Multiset.card δ := by
  simp [stendhalWeight]

/-- **`e(s)` kills the parabolic shuffle module** if the last red strand does not occur among
the first `|α| + 1` positions of `s`. -/
theorem parabolicShuffle_e_eq_zero_of_prefix (hQ : KLRSymm Q) (s : Seq (α+δ))
    (hs : ∀ q : Fin (Multiset.card (α+δ)), q.val ≤ Multiset.card α →
      s.lbl q ≠ .inr (Fin.last ℓ)) :
    parabolicShuffleAction Q Λ θ β N (e s) = 0 := by
  apply LinearMap.ext; intro z
  refine e_smul_ind_eq_zero (stendhalQ_swap_symm Q Λ hQ) (.inr (Fin.last ℓ)) ?_ s hs z
  intro a b n hb
  have h0 := card_last_pos (ℓ := ℓ) β
  have hv : IsViolated b := by
    refine ⟨h0, ?_⟩
    rcases hlab : b.lbl ⟨0, h0⟩ with i | r
    · rfl
    · exact absurd (hlab.trans (by rw [parabolicLast_red_eq_last β b _ hlab])) (hb h0)
  change parabolicInputMap Q Λ θ β (e a ⊗ₜ[k] e b) • (n : N) = 0
  have : parabolicInputMap Q Λ θ β (e a ⊗ₜ[k] e b) = 0 := by
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul, parabolicLastCyclotomic,
      AlgHom.comp_apply, parabolicLastProjection_e_violated Q Λ β b hv, map_zero, tmul_zero]
  rw [this]; exact zero_smul (parabolicFactorAlgebra Q Λ θ β) (n : N)

end Categorification.Stendhal
