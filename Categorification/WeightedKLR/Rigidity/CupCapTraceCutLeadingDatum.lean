/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutBotMatch
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowIdentity

/-!
# The leading Mackey datum of `S_+` and of `S_cut`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

A Mackey datum is determined by its weight `λ = q.β` (`MackeyQuad.ext_of_β`). So the suprema
in `indMackeyLayerAct_windowLoading_mem_mackeyTopOne` (weight of the window, at `S_+`) and
`indMackeyLayerAct_cutLoading_mem_mackeyTopOne` (weight `0`, at `S_cut`) have at most one
summand. Given the leading datum `q₀`, the image of the loading idempotent on the layer lies
in `Ξ_{q₀}` of the identity-shuffle span of `q₀`
(`indMackeyLayerAct_windowLoading_mem_leading`, `indMackeyLayerAct_cutLoading_mem_leading`).
These are the two summands that L5 compares, with bottom factors identified by
`plusBotCornerEquiv`. Their second top blocks carry the same weight, read in `λ⁺` and in
the cut labels: that of the strands of `s` right of `midPos s` (`suffixWt_windowLoading`,
`suffixWt_cutLoading`).

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `Stendhal.mem_of_mem_iSup_iSup_eq`,
  `Stendhal.CupCap.indMackeyLayerAct_windowLoading_mem_leading`,
  `Stendhal.CupCap.indMackeyLayerAct_cutLoading_mem_leading`,
  `Stendhal.CupCap.suffixWt_windowLoading`, `Stendhal.CupCap.suffixWt_cutLoading`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

/-- A supremum over the indices satisfying a predicate with at most one solution lies in the
summand of that solution. -/
theorem mem_of_mem_iSup_iSup_eq {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {S : ι → Submodule R M} {P : ι → Prop} (hP : ∀ i i', P i → P i' → i = i') {x : M}
    (hx : x ∈ ⨆ (i : ι) (_ : P i), S i) (i₀ : ι) (hi₀ : P i₀) : x ∈ S i₀ := by
  refine (iSup_le fun i => iSup_le fun hi => ?_ : (⨆ (i : ι) (_ : P i), S i) ≤ S i₀) hx
  rw [hP i i₀ hi hi₀]

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I} (hQ : KLRSymm Q)
  {N : Type*} [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]

include hQ in
/-- **The leading datum at `S_+`** (Webster v3, Lemma 7.19, trace half, L5): on the `N`-th
layer of the induced model of `S_+`, `ι_s(e(w))` lands in `Ξ_{q₀}` of the identity-shuffle span
of the datum `q₀` of the window weight. -/
theorem indMackeyLayerAct_windowLoading_mem_leading
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
      (Multiset.card (stendhalWeight 2 ν₀)))
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj)) :
    indMackeyLayerAct (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
        (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ))
        (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀)) y ∈
      (mackeyTopOneSpan q₀.1 (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
          (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N)
            hQ))).map
        (indMackeyLeftMap (Q := stendhalQ Q (plusBlockLabels Λ Λc j hj))
          (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
            (midPos_add_le_card (hj := hj) s)).symm
          (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
            (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ))
          q₀.1 q₀.2) :=
  mem_of_mem_iSup_iSup_eq
    (fun _ _ hq hq' => Subtype.ext (MackeyQuad.ext_of_β (hq.trans hq'.symm)))
    (indMackeyLayerAct_windowLoading_mem_mackeyTopOne hQ hsym s w hs y) q₀ hq₀

variable (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]

/-- **The leading datum at `S_cut`** (Webster v3, Lemma 7.19, trace half, L5): on the layer
`0` of the induced model of `S_cut(Y)`, `e(cutLoading s)` lands in `Ξ_{q₀}` of the
identity-shuffle span of the datum `q₀` of weight `0`. -/
theorem indMackeyLayerAct_cutLoading_mem_leading
    (hsym : KLRSymm (stendhalQ Q (cutLabels j hj Λ)))
    (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (y : IndMackeyLayer (stendhalQ Q (cutLabels j hj Λ))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))
      (CutInput Q (cutLabels j hj Λ) θ γ Y)
      (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))) 0)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₀ : q₀.1.β = 0) :
    indMackeyLayerAct (CutInput Q (cutLabels j hj Λ) θ γ Y) (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0 y ∈
      (mackeyTopOneSpan q₀.1 (CutInput Q (cutLabels j hj Λ) θ γ Y)).map
        (indMackeyLeftMap (Q := stendhalQ Q (cutLabels j hj Λ))
          (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
          (CutInput Q (cutLabels j hj Λ) θ γ Y) q₀.1 q₀.2) :=
  mem_of_mem_iSup_iSup_eq
    (fun _ _ hq hq' => Subtype.ext (MackeyQuad.ext_of_β (hq.trans hq'.symm)))
    (indMackeyLayerAct_cutLoading_mem_mackeyTopOne Y hsym s hs y) q₀ hq₀

end CupCap

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {θ γ ν₀ : Multiset I}

/-- **The weight of the strands right of the window** of the window loading is the weight of
the strands of `s` right of `p = midPos s`, read in `λ⁺`. -/
theorem suffixWt_windowLoading (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) :
    Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) =
      (Seq.suffixWt s (midPos j s) (midPos_le j s)).map
        (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) := by
  have hm := midPos_le j s
  have hc : Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) -
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) =
      Multiset.card (stendhalWeight ℓ (θ + γ)) - midPos j s := by
    rw [card_windowLoading_weight (hj := hj), card_plus j hj, Multiset.card_map]
    omega
  rw [Seq.suffixWt, Seq.suffixWt, Multiset.map_map, ← map_univ_fin_cast hc]
  refine Multiset.map_congr rfl fun b _ => ?_
  have hb : b.val < Multiset.card (stendhalWeight ℓ (θ + γ)) - midPos j s :=
    (Fin.cast hc b).2
  have hy : midPos j s + Multiset.card (stendhalWeight 2 ν₀) + b.val <
      Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
    rw [card_plus j hj, Multiset.card_map]
    omega
  simp only [Function.comp_apply]
  rw [windowLoading_lbl (hj := hj) s w _ ⟨_, hy⟩ rfl,
    insertSeq_lbl_ge s (midPos_le j s) _ ⟨midPos j s + b.val, by omega⟩ (by simp)
      (by simp only; omega)]
  rfl

/-- **The weight of the strands right of `p` of the cut loading** is that of `s`. -/
theorem suffixWt_cutLoading (s : Seq (stendhalWeight ℓ (θ + γ))) :
    Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s) =
      (Seq.suffixWt s (midPos j s) (midPos_le j s)).map
        (Sum.map (id : I → I) (Fin.cast (Nat.add_sub_of_le hj).symm)) := by
  have hm := midPos_le j s
  have hc : Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) -
        (midPos j s + 0) = Multiset.card (stendhalWeight ℓ (θ + γ)) - midPos j s := by
    rw [cutInputWeights_add]
    simp only [stendhalWeight, Multiset.card_add, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [Seq.suffixWt, Seq.suffixWt, Multiset.map_map, ← map_univ_fin_cast hc]
  refine Multiset.map_congr rfl fun b _ => ?_
  exact cutLoading_apply s _ _ (by simp)

end Categorification.Stendhal.CupCap
