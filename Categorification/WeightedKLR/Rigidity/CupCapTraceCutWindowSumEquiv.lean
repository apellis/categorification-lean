/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingQuadExists

/-!
# (T) for the red-ordered window idempotent

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

On the layer `N` of the head-strand filtration of `𝕊(S_+ X)` at the cut `midPos s + N`, the
window `e'_s = ι_s(1_{red-ordered})` is the sum of the orthogonal idempotents `ι_s(e(w))` over
the red-ordered loadings `w` of the window (`windowLayerAct_redOrdered`,
`windowLayerAct_orthIdem`), and `ι_s(e(w))` acts as the window loading `e(l⁺_w)`
(`windowLayerAct_e`). On the layer `0` of `S_cut(Res X)` at the cut `midPos s`, `e_red · e(l)`
is the sum of the orthogonal idempotents `e_w · e(l)` (`cutWindowCorner_sum`,
`cutWindowCorner_orthIdem`). Summing (T_w) (`windowLoadingCornerMidPosEquiv`) over `w` with
`Categorification.orthRangeSumEquiv` gives (T):

`e'_s · Lay⁺_N ≃ₗ e_red · e(l) · 𝕊Lay^c_0` (`windowRedOrderedCornerEquiv`),

whose `w`-component is (T_w) (`windowRedOrderedCornerEquiv_proj`).

The leading Mackey data are those of `CupCapTraceCutLeadingQuadExists`: when the strands of `s`
left of the maximum fit in the first block, (T_w) is `windowLoadingLayerCornerEquivOfQuad` at
`windowLeadingQuad`, `cutLeadingQuad`; otherwise both corners vanish. Webster's proof does not
spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.windowLoadingLayerCornerEquivOfQuad`,
  `Stendhal.CupCap.windowLoadingLayerCornerEquiv`,
  `Stendhal.CupCap.windowRedOrderedCornerEquiv`.

## Main results

* `Stendhal.CupCap.windowLoadingLayerCornerEquiv_of_prefixInFirstBlock`,
  `Stendhal.CupCap.windowRedOrderedCornerEquiv_proj`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)
  (s : Seq (stendhalWeight ℓ (θ + γ)))

/-- **(T_w) on the layers, given the leading data** (Webster v3, Lemma 7.19, trace half, step
L5): for a red-ordered loading `w` of the window, the image of `ι_s(e(w))` on the layer `N` of
`𝕊(S_+ X)` at the cut `midPos s + N` is isomorphic to the image of `e_w · e(l)` on the layer `0`
of `S_cut(Res X)` at the cut `midPos s` (`windowLoadingCornerMidPosEquiv`). -/
def windowLoadingLayerCornerEquivOfQuad (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (w : Seq (stendhalWeight 2 ν₀))
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (e w))) :=
  (LinearEquiv.ofEq _ _ (congrArg LinearMap.range
      (windowLayerAct_e X hQ s w (Multiset.card (stendhalWeight 2 ν₀))))).trans
    ((windowLoadingCornerMidPosEquiv X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ hsr hwr).trans
      (LinearEquiv.ofEq _ _ (range_cutWindowCorner X hQ s _).symm))

open Classical in
/-- **(T_w) on the layers** (Webster v3, Lemma 7.19, trace half, step L5): for red-ordered `s`
satisfying the head condition and a red-ordered loading `w` of the window, the image of
`ι_s(e(w))` on the layer `N` of `𝕊(S_+ X)` at the cut `midPos s + N` is isomorphic to the image
of `e_w · e(l)` on the layer `0` of `S_cut(Res X)` at the cut `midPos s`. When the strands of `s`
left of the maximum fit in the first block, this is `windowLoadingLayerCornerEquivOfQuad` at the
leading data `windowLeadingQuad`, `cutLeadingQuad`; otherwise both sides are zero
(`subsingleton_range_windowLayerAct_e`, `subsingleton_range_cutWindowCorner`). -/
def windowLoadingLayerCornerEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (w : Seq (stendhalWeight 2 ν₀)) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (e w))) :=
  if h : PrefixInFirstBlock j hj θ s then
    windowLoadingLayerCornerEquivOfQuad X hQ s hsc hsp hs w (windowLeadingQuad j hj θ γ ν₀ s w h)
      rfl (cutLeadingQuad j hj θ γ s h) rfl hsr hwr
  else
    haveI := subsingleton_range_windowLayerAct_e X hQ s hsp w hs hsr hwr h
    haveI := subsingleton_range_cutWindowCorner X hQ s hsc hs hsr h (tensorOfKLR Q Λc ν₀ (e w))
    LinearEquiv.ofSubsingleton _ _

open Classical in
theorem windowLoadingLayerCornerEquiv_of_prefixInFirstBlock (hsc : KLRSymm Sc)
    (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (w : Seq (stendhalWeight 2 ν₀)) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w)
    (h : PrefixInFirstBlock j hj θ s) :
    windowLoadingLayerCornerEquiv X hQ s hsc hsp hs w hsr hwr =
      windowLoadingLayerCornerEquivOfQuad X hQ s hsc hsp hs w
        (windowLeadingQuad j hj θ γ ν₀ s w h) rfl (cutLeadingQuad j hj θ γ s h) rfl hsr hwr :=
  dite_eq_left h

open Classical in
/-- **(T) for the red-ordered window idempotent** (Webster v3, Lemma 7.19, trace half,
step L5): for a red-ordered loading `s` satisfying the head condition, the image of
`e'_s = ι_s(1_{red-ordered})` on the layer `N` of `𝕊(S_+ X)` at the cut `midPos s + N` is
isomorphic to the image of `e_red · e(l)` on the layer `0` of `S_cut(Res X)` at the cut
`midPos s`, `l` the cut loading of `s` and `e_red` the red-ordered idempotent of the window
acting on `Res X`. The isomorphism is the sum of the (T_w) over the red-ordered `w`. -/
def windowRedOrderedCornerEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hsr : IsRedOrdered s) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (redOrderedKLR k Q Λc ν₀))) :=
  (LinearEquiv.ofEq _ _ (congrArg LinearMap.range
      (windowLayerAct_redOrdered X hQ s (Multiset.card (stendhalWeight 2 ν₀))))).trans
    ((orthRangeSumEquiv (windowLayerAct_orthIdem X hQ s (Multiset.card (stendhalWeight 2 ν₀)))
      (cutWindowCorner_orthIdem X hQ s)
      (fun w => windowLoadingLayerCornerEquiv X hQ s hsc hsp hs w.1 hsr w.2)).trans
      (LinearEquiv.ofEq _ _ (congrArg LinearMap.range (cutWindowCorner_sum X hQ s).symm)))

open Classical in
/-- **The `w`-component of (T) is (T_w)**: `e_w · e(l)` applied to the image of `x` under (T) is
(T_w) of `ι_s(e(w)) x`. -/
theorem windowRedOrderedCornerEquiv_proj (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hsr : IsRedOrdered s) (w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w})
    (x : LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀)
        (Multiset.card (stendhalWeight 2 ν₀)))) :
    cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s
        (tensorOfKLR Q Λc ν₀ (e w.1))
        (windowRedOrderedCornerEquiv (ν₀ := ν₀) X hQ s hsc hsp hs hsr x).1 =
      (windowLoadingLayerCornerEquiv X hQ s hsc hsp hs w.1 hsr w.2
        ⟨windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w.1)
          (Multiset.card (stendhalWeight 2 ν₀)) x, LinearMap.mem_range_self _ _⟩).1 :=
  orthRangeSumEquiv_proj (windowLayerAct_orthIdem X hQ s (Multiset.card (stendhalWeight 2 ν₀)))
    (cutWindowCorner_orthIdem X hQ s)
    (fun w => windowLoadingLayerCornerEquiv X hQ s hsc hsp hs w.1 hsr w.2) (Finset.mem_univ w) _

end Categorification.Stendhal.CupCap
