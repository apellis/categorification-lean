/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingGeneral

/-!
# One leading Mackey datum for every window loading

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the `W`-linearity
of (T)).

For a loading `s` and a loading `w` of the window, the weights of the strands of the window
loading `l⁺_w` left and right of the cut `p + N` (`p = midPos s`, `N` the number of window
strands) do not depend on `w`: they are `windowPrefixWt s` (the strands of `s` left of `p` and
the window) and `windowSuffixWt s` (`prefixWt_windowLoading`, `suffixWt_windowLoading`). So the
leading datum of step L5 can be taken with these top weights, once for all `w`
(`windowCommonQuad`, when `PrefixInFirstBlock`), and with it one injective map
`Ξ ∘ leadingTopOneOf` from the identity-shuffle span at the cut of `S_cut(Res X)` to the layer
`N` of the induced model of `S_+(X)` at the cut `|windowPrefixWt s|` (`windowCommonSpanMap`).
It carries the range of the window endomorphism of `w` onto the corner of `e(l⁺_w)`, for every
`w` (`map_range_windowCommonSpanMap`, from `map_range_cutWindowSpanEnd_of_eq`).

This gives (T_w) through a map that does not depend on `w` (`windowCommonCornerEquiv`), and (T)
as their sum (`windowCommonRedOrderedEquiv`, `windowCommonRedOrderedEquiv_proj`). No new
hypothesis.

## Main definitions

* `Stendhal.CupCap.windowPrefixWt`, `Stendhal.CupCap.windowSuffixWt`,
  `Stendhal.CupCap.windowCommonQuad`, `Stendhal.CupCap.windowCommonSpanMap`.
* `Stendhal.CupCap.windowCommonCornerSpanEquiv`, `Stendhal.CupCap.cutWindowSpanCornerEquiv`,
  `Stendhal.CupCap.windowCommonCornerEquiv`, `Stendhal.CupCap.windowCommonRedOrderedEquiv`.

## Main results

* `Stendhal.CupCap.map_range_windowCommonSpanMap`,
  `Stendhal.CupCap.windowCommonRedOrderedEquiv_proj`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "φ" => cutToPlusColour (I := I) j hj
local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)
local notation "αP" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))))
  (stendhalWeight j θ)
local notation "δP" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))
local notation "αC" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
  (stendhalWeight j θ)
local notation "δC" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (ℓ - j) γ)

/-! ### The common top weights and the common datum -/

variable (j hj ν₀) in
/-- **The weight left of the cut `p + N` of every window loading**: the strands of `s` left
of `p = midPos s`, read in `λ⁺`, and the window. -/
def windowPrefixWt (s : Seq (stendhalWeight ℓ (θ + γ))) :
    Multiset (I ⊕ Fin (j + (2 + (ℓ - j)))) :=
  (Seq.prefixWt s (midPos j s) (midPos_le j s)).map
      (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) +
    (stendhalWeight 2 ν₀).map (windowColour j hj)

variable (j hj) in
/-- **The weight right of the cut `p + N` of every window loading**: the strands of `s` right of
`p = midPos s`, read in `λ⁺`. -/
def windowSuffixWt (s : Seq (stendhalWeight ℓ (θ + γ))) :
    Multiset (I ⊕ Fin (j + (2 + (ℓ - j)))) :=
  (Seq.suffixWt s (midPos j s) (midPos_le j s)).map
    (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj)

omit [DecidableEq I] in
theorem windowPrefixWt_eq (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀)) :
    windowPrefixWt j hj ν₀ s = Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) :=
  (prefixWt_windowLoading s w).symm

omit [DecidableEq I] in
theorem windowSuffixWt_eq (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀)) :
    windowSuffixWt j hj s = Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) :=
  (suffixWt_windowLoading s w).symm

variable (ν₀) in
/-- A loading of the window, used only inside proofs. -/
def windowSeqWitness : Seq (stendhalWeight 2 ν₀) :=
  Seq.ofList (stendhalWeight 2 ν₀).toList (Multiset.coe_toList _)

omit [DecidableEq I] in
theorem windowPrefixWt_add_windowSuffixWt (s : Seq (stendhalWeight ℓ (θ + γ))) :
    αP + δP = windowPrefixWt j hj ν₀ s + windowSuffixWt j hj s :=
  (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s (windowSeqWitness ν₀)) _
    (midPos_add_le_card (hj := hj) s)).symm.trans
    (congrArg₂ (· + ·) (windowPrefixWt_eq s _).symm (windowSuffixWt_eq s _).symm)

omit [DecidableEq I] in
theorem card_windowPrefixWt (s : Seq (stendhalWeight ℓ (θ + γ))) :
    midPos j s + Multiset.card (stendhalWeight 2 ν₀) =
      Multiset.card (windowPrefixWt j hj ν₀ s) :=
  ((Seq.card_prefixWt (windowLoading j hj θ γ ν₀ s (windowSeqWitness ν₀)) _
    (midPos_add_le_card (hj := hj) s)).symm.trans
    (congrArg Multiset.card (windowPrefixWt_eq s _).symm))

variable (j hj θ γ ν₀) in
/-- **The leading datum at `S_+`, common to all window loadings**: the Mackey datum of the
weight of the window at the top weights `windowPrefixWt s`, `windowSuffixWt s`. -/
def windowCommonQuad (s : Seq (stendhalWeight ℓ (θ + γ))) (h : PrefixInFirstBlock j hj θ s) :
    {q : MackeyQuad (windowPrefixWt j hj ν₀ s) (windowSuffixWt j hj s) αP δP //
      Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)} :=
  ⟨MackeyQuad.ofLe (windowPrefixWt_add_windowSuffixWt s).symm
    ((stendhalWeight 2 ν₀).map (windowColour j hj))
    (Multiset.le_add_left _ _)
    (by rw [plusTailWeight_eq j hj ν₀ γ]; exact Multiset.le_add_right _ _)
    (by
      rw [windowPrefixWt, add_tsub_cancel_right, firstBlock_plus_eq_map (hj := hj)]
      exact Multiset.map_le_map h),
    Multiset.card_map _ _⟩

theorem windowCommonQuad_β (s : Seq (stendhalWeight ℓ (θ + γ)))
    (h : PrefixInFirstBlock j hj θ s) :
    (windowCommonQuad j hj θ γ ν₀ s h).1.β = (stendhalWeight 2 ν₀).map (windowColour j hj) :=
  rfl

theorem windowCommonQuad_γ (s : Seq (stendhalWeight ℓ (θ + γ)))
    (h : PrefixInFirstBlock j hj θ s) :
    (cutLeadingQuad j hj θ γ s h).1.γ.map φ = (windowCommonQuad j hj θ γ ν₀ s h).1.γ :=
  leadingQuad_γ_eq_map_of_eq s (windowSeqWitness ν₀) (windowSuffixWt_eq s _) _ rfl _ rfl

theorem windowCommonQuad_δ (s : Seq (stendhalWeight ℓ (θ + γ)))
    (h : PrefixInFirstBlock j hj θ s) :
    (cutLeadingQuad j hj θ γ s h).1.δ.map φ = (windowCommonQuad j hj θ γ ν₀ s h).1.δ :=
  leadingQuad_δ_eq_map_of_β _ rfl _ rfl

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
local notation "Inner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
  (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))

variable (s : Seq (stendhalWeight ℓ (θ + γ)))
  (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
  (h : PrefixInFirstBlock j hj θ s)

include hQ hs in
theorem windowCommonQuad_mem (x : Inner) :
    x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) (windowCommonQuad j hj θ γ ν₀ s h).1 ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc (cutLeadingQuad j hj θ γ s h).1 Yc :=
  mem_botBlocksCorner_plus_iff_of_eq X hQ s (windowSeqWitness ν₀) hs (windowPrefixWt_eq s _)
    (windowSuffixWt_eq s _) _ rfl _ rfl x

theorem windowCommonQuad_symm_smul
    (t : TensorKLR Sc (cutLeadingQuad j hj θ γ s h).1.γ (cutLeadingQuad j hj θ γ s h).1.δ)
    (n : botCorner Sc (cutLeadingQuad j hj θ γ s h).1 Yc) :
    (plusBotCornerEquivOf X hQ (windowCommonQuad j hj θ γ ν₀ s h).1 rfl
        (cutLeadingQuad j hj θ γ s h).1 (windowCommonQuad_mem X hQ s hs h)).symm (t • n) =
      tensorRelabel (cutPlusRelabel j hj Q Λ Λc (windowCommonQuad_γ (ν₀ := ν₀) s h))
        (cutPlusRelabel j hj Q Λ Λc (windowCommonQuad_δ (ν₀ := ν₀) s h)) t •
        (plusBotCornerEquivOf X hQ (windowCommonQuad j hj θ γ ν₀ s h).1 rfl
          (cutLeadingQuad j hj θ γ s h).1 (windowCommonQuad_mem X hQ s hs h)).symm n :=
  plusBotCornerEquivOf_symm_smul_of_eq X hQ s (windowSeqWitness ν₀) hs (windowPrefixWt_eq s _)
    (windowSuffixWt_eq s _) _ rfl _ rfl _ _ _ t n

/-- **The leading span map common to all window loadings** (Webster v3, Lemma 7.19, trace
half, step L5): `Ξ ∘ leadingTopOneOf` at `windowCommonQuad`, from the identity-shuffle span at
the cut of `S_cut(Res X)` to the layer `N` of the induced model of `S_+(X)` at the cut
`|windowPrefixWt s|`. It does not depend on a loading of the window. -/
def windowCommonSpanMap (hsc : KLRSymm Sc) (hsp : KLRSymm Sp) :
    mackeyTopOneSpan (Q := Sc) (cutLeadingQuad j hj θ γ s h).1 Yc →ₗ[k]
      IndMackeyLayer Sp αP δP Nₒ (Multiset.card (windowPrefixWt j hj ν₀ s))
        (Multiset.card (stendhalWeight 2 ν₀)) :=
  leadingSpanLayerMapOf X hQ hsc hsp (windowCommonQuad j hj θ γ ν₀ s h)
    (windowPrefixWt_add_windowSuffixWt s) rfl (cutLeadingQuad j hj θ γ s h)
    (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
    (windowCommonQuad_γ s h) (windowCommonQuad_δ s h) (windowCommonQuad_mem X hQ s hs h)
    (windowCommonQuad_symm_smul X hQ s hs h)

theorem windowCommonSpanMap_injective (hsc : KLRSymm Sc) (hsp : KLRSymm Sp) :
    Function.Injective (windowCommonSpanMap (ν₀ := ν₀) X hQ s hs h hsc hsp) :=
  leadingSpanLayerMapOf_injective _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The common span map carries the range of the window endomorphism of `w` onto the corner
of `e(l⁺_w)`**, for every loading `w` of the window. -/
theorem map_range_windowCommonSpanMap (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀)) :
    (LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w
        (cutLeadingQuad j hj θ γ s h) rfl)).map
        (windowCommonSpanMap (ν₀ := ν₀) X hQ s hs h hsc hsp) =
      LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))) :=
  map_range_cutWindowSpanEnd_of_eq X hQ s w hsc hsp hs (windowPrefixWt_eq s w)
    (windowSuffixWt_eq s w) _ _ rfl _ rfl _ _ _ _

end Categorification.Stendhal.CupCap
