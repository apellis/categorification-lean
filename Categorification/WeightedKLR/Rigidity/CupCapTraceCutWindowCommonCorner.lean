/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowCommonDatum

/-!
# (T_w) and (T) through the common leading datum

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

(T_w) is rebuilt with the leading datum `windowCommonQuad` common to all window loadings
(`CupCapTraceCutWindowCommonDatum`), so that its plus side goes through one map
`windowCommonSpanMap` for every `w`. Read at the layer index `|windowPrefixWt s|`
(`cutLayerCornerCast` along `card_windowPrefixWt`), it factors as

* `windowCommonPlusEquiv`: the corner of `ι_s(e(w))` in the layer `N` of `𝕊(S_+ X)` at the cut
  `midPos s + N` ≃ the range of the window endomorphism `cutWindowSpanEnd` of `w`, through
  `cutLoadingIndLayerEquiv` and the inverse of `windowCommonSpanMap`
  (`windowCommonCornerSpanEquiv`);
* `cutWindowSpanCornerEquiv`: the range of the window endomorphism ≃ the corner of `e_w · e(l)`
  in the layer `0` of `S_cut(Res X)` at the cut `midPos s` (the cut side of
  `windowLoadingCornerMidPosEquiv`, which does not involve the plus datum).

`windowCommonCornerEquiv` is their composite (when `PrefixInFirstBlock`; otherwise both sides
vanish), and `windowCommonRedOrderedEquiv` their sum over the red-ordered `w`, with
`w`-components `windowCommonRedOrderedEquiv_proj`. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.windowCommonCornerSpanEquiv`, `Stendhal.CupCap.windowCommonPlusEquiv`,
  `Stendhal.CupCap.cutWindowSpanCornerEquiv`, `Stendhal.CupCap.windowCommonCornerEquivOfBlock`,
  `Stendhal.CupCap.windowCommonCornerEquiv`, `Stendhal.CupCap.windowCommonRedOrderedEquiv`.

## Main results

* `Stendhal.CupCap.windowCommonCornerSpanEquiv_apply`,
  `Stendhal.CupCap.windowCommonCornerEquiv_of_prefixInFirstBlock`,
  `Stendhal.CupCap.windowCommonRedOrderedEquiv_proj`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)
local notation "αP" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))))
  (stendhalWeight j θ)
local notation "δP" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Bp" => BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp

variable (s : Seq (stendhalWeight ℓ (θ + γ)))
  (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
  (h : PrefixInFirstBlock j hj θ s)

/-! ### The plus side -/

/-- **The range of the window endomorphism of `w` is the corner of `e(l⁺_w)`**, through the
common span map. -/
def windowCommonCornerSpanEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀)) :
    LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w
        (cutLeadingQuad j hj θ γ s h) rfl) ≃ₗ[k]
      LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀)) :
        IndMackeyLayer Sp αP δP Nₒ (Multiset.card (windowPrefixWt j hj ν₀ s))
          (Multiset.card (stendhalWeight 2 ν₀)) →ₗ[k] _) :=
  (Submodule.equivMapOfInjective (windowCommonSpanMap (ν₀ := ν₀) X hQ s hs h hsc hsp)
      (windowCommonSpanMap_injective X hQ s hs h hsc hsp) _).trans
    (LinearEquiv.ofEq _ _ (map_range_windowCommonSpanMap X hQ s hs h hsc hsp w))

theorem windowCommonCornerSpanEquiv_apply (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀))
    (y : LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w
        (cutLeadingQuad j hj θ γ s h) rfl)) :
    (windowCommonCornerSpanEquiv X hQ s hs h hsc hsp w y).1 =
      windowCommonSpanMap (ν₀ := ν₀) X hQ s hs h hsc hsp y.1 :=
  rfl

/-- **(T_w), plus side, through the common datum** (Webster v3, Lemma 7.19, trace half, step
L5): the corner of `ι_s(e(w))` in the layer `N` of `𝕊(S_+ X)` at the cut `midPos s + N` is
isomorphic to the range of the window endomorphism of `w`, through `cutLoadingIndLayerEquiv` at
the cut `|windowPrefixWt s|` and the inverse of the common span map. -/
def windowCommonPlusEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀)) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w
        (cutLeadingQuad j hj θ γ s h) rfl) :=
  (LinearEquiv.ofEq _ _ (congrArg LinearMap.range
      (windowLayerAct_e X hQ s w (Multiset.card (stendhalWeight 2 ν₀))))).trans
    ((cutLayerCornerCast (Λ := plusBlockLabels Λ Λc j hj) (N := Bp) hQ
      (card_windowPrefixWt (ν₀ := ν₀) (hj := hj) s) (windowLoading j hj θ γ ν₀ s w)
      (Multiset.card (stendhalWeight 2 ν₀))).trans
    ((cutLoadingIndLayerEquiv (Λ := plusBlockLabels Λ Λc j hj) (N := Bp) hQ
      (windowLoading j hj θ γ ν₀ s w) (windowLoading_mem_cutOrderedLoadings hsr hwr)
      (Multiset.card (windowPrefixWt j hj ν₀ s)) (Multiset.card (stendhalWeight 2 ν₀))).trans
    (windowCommonCornerSpanEquiv X hQ s hs h hsc hsp w).symm))

/-! ### The cut side -/

local notation "εR" => cutWindowResEnd Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) X

/-- **(T_w), cut side** (Webster v3, Lemma 7.19, trace half, step L5): `Ξ_{q₁}` carries the
range of the window endomorphism of `w` onto `e_w · e(l) · 𝕊Lay^c`, the corner of `e_w · e(l)`
in the layer `0` of `S_cut(Res X)` at the cut `midPos s`. -/
def cutWindowSpanCornerEquiv (hsc : KLRSymm Sc) (w : Seq (stendhalWeight 2 ν₀))
    (hsr : IsRedOrdered s) :
    LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w
        (cutLeadingQuad j hj θ γ s h) rfl) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (e w))) :=
  ((cutWindowLayerEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc (cutLeadingQuad j hj θ γ s h) rfl).trans
    (LinearEquiv.ofEq _ _
      (cutWindowLayer_eq_map_range X hQ s w hsc hs (cutLeadingQuad j hj θ γ s h) rfl))).trans
    (((cutLoadingIndLayerMapEquiv (Λ := cutLabels j hj Λ) (εR w)
      (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))) 0 hQ (cutWindowResEnd_idem X w) (cutLoading j hj θ γ s)
      (cutLoading_mem_cutOrderedLoadings hsr)).symm.trans
    (cutLayerMapCornerCast (Λ := cutLabels j hj Λ) hQ
      (Seq.card_prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (εR w) (cutLoading j hj θ γ s) 0)).trans
    (LinearEquiv.ofEq _ _ (range_cutWindowCorner X hQ s _).symm))

/-! ### (T_w) and (T) -/

/-- **(T_w) through the common leading datum** (Webster v3, Lemma 7.19, trace half, step L5),
when the strands of `s` left of the maximum fit in the first block. -/
def windowCommonCornerEquivOfBlock (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀)) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (e w))) :=
  (windowCommonPlusEquiv X hQ s hs h hsc hsp w hsr hwr).trans
    (cutWindowSpanCornerEquiv X hQ s hs h hsc w hsr)

open Classical in
/-- **(T_w) through the common leading datum** (Webster v3, Lemma 7.19, trace half, step L5):
`windowCommonCornerEquivOfBlock` when `PrefixInFirstBlock`; otherwise both sides are zero. -/
def windowCommonCornerEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀)) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (e w))) :=
  if h : PrefixInFirstBlock j hj θ s then
    windowCommonCornerEquivOfBlock X hQ s hs h hsc hsp w hsr hwr
  else
    haveI := subsingleton_range_windowLayerAct_e X hQ s hsp w hs hsr hwr h
    haveI := subsingleton_range_cutWindowCorner X hQ s hsc hs hsr h (tensorOfKLR Q Λc ν₀ (e w))
    LinearEquiv.ofSubsingleton _ _

open Classical in
theorem windowCommonCornerEquiv_of_prefixInFirstBlock (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀)) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    windowCommonCornerEquiv X hQ s hs hsc hsp w hsr hwr =
      windowCommonCornerEquivOfBlock X hQ s hs h hsc hsp w hsr hwr :=
  dite_eq_left h

open Classical in
/-- **(T) for the red-ordered window idempotent, through the common leading datum** (Webster
v3, Lemma 7.19, trace half, step L5): the sum over the red-ordered `w` of
`windowCommonCornerEquiv`. -/
def windowCommonRedOrderedEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp) (hsr : IsRedOrdered s) :
    LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀)
        (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
        (ν₀ := ν₀) X hQ s (tensorOfKLR Q Λc ν₀ (redOrderedKLR k Q Λc ν₀))) :=
  (LinearEquiv.ofEq _ _ (congrArg LinearMap.range
      (windowLayerAct_redOrdered X hQ s (Multiset.card (stendhalWeight 2 ν₀))))).trans
    ((orthRangeSumEquiv (windowLayerAct_orthIdem X hQ s (Multiset.card (stendhalWeight 2 ν₀)))
      (cutWindowCorner_orthIdem X hQ s)
      (fun w => windowCommonCornerEquiv X hQ s hs hsc hsp w.1 hsr w.2)).trans
      (LinearEquiv.ofEq _ _ (congrArg LinearMap.range (cutWindowCorner_sum X hQ s).symm)))

open Classical in
/-- **The `w`-component of (T) is (T_w)**, through the common leading datum. -/
theorem windowCommonRedOrderedEquiv_proj (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hsr : IsRedOrdered s) (w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w})
    (x : LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀)
        (Multiset.card (stendhalWeight 2 ν₀)))) :
    cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s
        (tensorOfKLR Q Λc ν₀ (e w.1))
        (windowCommonRedOrderedEquiv (ν₀ := ν₀) X hQ s hs hsc hsp hsr x).1 =
      (windowCommonCornerEquiv X hQ s hs hsc hsp w.1 hsr w.2
        ⟨windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w.1)
          (Multiset.card (stendhalWeight 2 ν₀)) x, LinearMap.mem_range_self _ _⟩).1 :=
  orthRangeSumEquiv_proj (windowLayerAct_orthIdem X hQ s (Multiset.card (stendhalWeight 2 ν₀)))
    (cutWindowCorner_orthIdem X hQ s)
    (fun w => windowCommonCornerEquiv X hQ s hs hsc hsp w.1 hsr w.2) (Finset.mem_univ w) _

end Categorification.Stendhal.CupCap
