/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLoading
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyIdentity

/-!
# The leading piece of the head-strand filtration of `S_+` at a window loading

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L3 at `S_+`.

On the `N`-th Mackey layer of the induced model of `S_+(X)`, for the top cut at the end
`p + N` of the window of the cap generators at a loading `s` (`p = midPos s`,
`N = |window|`), the idempotent `ι_s(e(w))` of a window loading lands in the span of the
images under `Ξ_λ` of the identity-shuffle parts `mackeyTopOneSpan` of the data `λ` whose
weight is the window weight (`indMackeyLayerAct_windowLoading_mem_mackeyTopOne`). On these
parts the parabolic part of `R(ν) ⊗ R(ν')`, and so the window, acts through the bottom factor
(`KLRAlgebra.castAlg_concat_tmul_one_smul_tmul_mackeyTopOne`).

Webster's proof does not spell this out. This refines `indMackeyLayerAct_windowLoading_mem`.
The statement is on the layer of the induced model; the passage to `S_+` is elementwise,
through `cutMackeyLayerMap_act`.

## Main results

* `Stendhal.CupCap.indMackeyLayerAct_windowLoading_mem_mackeyTopOne`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I} (hQ : KLRSymm Q)
  {N : Type*} [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]

include hQ in
/-- **L2 and L3 at a window loading**: on the `N`-th layer of the induced model of `S_+` for
the top cut at the end `p + N` of the window, `ι_s(e(w))` lands in the span of the images
under `Ξ_λ` of the identity-shuffle parts of the Mackey data `λ` of the window weight. -/
theorem indMackeyLayerAct_windowLoading_mem_mackeyTopOne
    (hsym : KLRSymm (stendhalQ Q (plusBlockLabels Λ Λc j hj)))
    (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (y : IndMackeyLayer (stendhalQ Q (plusBlockLabels Λ Λc j hj))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)))
      (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
        (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ))
      (Multiset.card (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)))
      (Multiset.card (stendhalWeight 2 ν₀))) :
    indMackeyLayerAct (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
        (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ))
        (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀)) y ∈
      ⨆ (q : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
        (_ : q.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj)),
        (mackeyTopOneSpan q.1 (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
          (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N)
            hQ))).map
        (indMackeyLeftMap (Q := stendhalQ Q (plusBlockLabels Λ Λc j hj))
          (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
            (midPos_add_le_card (hj := hj) s)).symm
          (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
            (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ))
          q.1 q.2) := by
  exact indMackeyLayerAct_e_mem_of_black_mackeyTopOne hsym (windowLoading j hj θ γ ν₀ s w)
    (midPos_add_le_card (hj := hj) s) (fun x hx hmem => windowLoading_black s w hs x hx hmem)
    _ (windowWt_windowLoading s w) y

end CupCap

end Categorification.Stendhal
