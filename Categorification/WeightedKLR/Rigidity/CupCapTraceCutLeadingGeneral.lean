/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingRecast
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowSumEquiv

/-!
# The leading comparison for a Mackey datum with arbitrary top weights

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the `W`-linearity
of (T)).

The leading comparison of step L5 (`plusBotCornerEquiv`, `leadingTopOneSpanEquiv`,
`leadingLayerSpanEquiv`, `leadingSpanLayerMap`) is built for a Mackey datum `q` whose top
weights are those of the window loading `l⁺_w`, so its type depends on `w`. None of the
constructions uses the top weights except through the proofs. Here they are rebuilt for a datum
`q : MackeyQuad ν ν' αP δP` with arbitrary top weights `ν, ν'`, with the needed facts as
arguments (`plusBotCornerEquivOf`, `leadingTopOneOf`, `leadingLayerSpanEquivOf`,
`leadingSpanLayerMapOf`). When `ν, ν'` are the top weights of `l⁺_w` (hypotheses `hν`, `hν'`),
the old statements give the new ones after `subst` (`mem_botBlocksCorner_plus_iff_of_eq`,
`leadingQuad_γ_eq_map_of_eq`, `plusBotCornerEquivOf_symm_smul_of_eq`,
`map_range_cutWindowSpanEnd_of_eq`). So one datum, with top weights independent of `w`, serves
every `w`. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.plusBotCornerEquivOf`, `Stendhal.CupCap.leadingTopOneOf`,
  `Stendhal.CupCap.leadingLayerSpanEquivOf`, `Stendhal.CupCap.leadingSpanLayerMapOf`.

## Main results

* `Stendhal.CupCap.leadingSpanLayerMapOf_injective`,
  `Stendhal.CupCap.map_range_cutWindowSpanEnd_of_eq`.
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

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
local notation "Inner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
  (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))

variable {ν ν' : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
  {μ μ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}

/-! ### The bottom corners -/

/-- **The bottom corners of `S_+(X)` and `S_cut(Res X)`, for any top weights**:
`plusBotCornerEquiv` with the membership criterion `hmem` as an argument. -/
def plusBotCornerEquivOf (q : MackeyQuad ν ν' αP δP)
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj)) (q' : MackeyQuad μ μ' αC δC)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q' Yc) :
    botCorner Sp q Nₒ ≃ₗ[k] botCorner Sc q' Yc :=
  (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X)
      hQ (hq.trans (windowWeight_eq_map j hj ν₀))).trans
    (LinearEquiv.ofSubmodules (innerToRes j hj Q Λ Λc θ γ ν₀ X) _ _ (by
      ext y
      rw [Submodule.mem_map_equiv]
      exact (hmem _).trans Iff.rfl))

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))

theorem plusBotCornerEquivOf_eq
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      αP δP)
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)) αC δC)
    (hq' : q'.β = 0)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q' Yc) :
    plusBotCornerEquivOf X hQ q hq q' hmem = plusBotCornerEquiv X hQ s w hs q hq q' hq' :=
  rfl

include hQ in
/-- The membership criterion of `plusBotCornerEquivOf`, for top weights equal to those of the
window loading. -/
theorem mem_botBlocksCorner_plus_iff_of_eq
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hν : ν = Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (hν' : ν' = Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (q : MackeyQuad ν ν' αP δP) (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)) αC δC)
    (hq' : q'.β = 0) (x : Inner) :
    x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q' Yc := by
  subst hν hν'
  exact mem_botBlocksCorner_plus_iff X hQ s w hs q hq q' hq' x

omit [DecidableEq I] in
/-- `leadingQuad_γ_eq_map` for top weights equal to those of the window loading. -/
theorem leadingQuad_γ_eq_map_of_eq
    (hν' : ν' = Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (q : MackeyQuad ν ν' αP δP) (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)) αC δC)
    (hq' : q'.β = 0) : q'.γ.map φ = q.γ := by
  have h4 := q.h₄.trans (plusTailWeight_eq j hj ν₀ γ)
  rw [hq] at h4
  have h4' := q'.h₄
  rw [hq', zero_add] at h4'
  have hδ : q.δ = q'.δ.map φ := by rw [h4']; exact add_left_cancel h4
  have h2 := (q.h₂.trans (hν'.trans (suffixWt_windowLoading_eq_map_cut j hj s w))).trans
    (congrArg (Multiset.map φ) q'.h₂.symm)
  rw [Multiset.map_add, ← hδ] at h2
  exact (add_right_cancel h2).symm

omit [DecidableEq I] in
/-- `leadingQuad_δ_eq_map`, which does not see the top weights. -/
theorem leadingQuad_δ_eq_map_of_β (q : MackeyQuad ν ν' αP δP)
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj)) (q' : MackeyQuad μ μ' αC δC)
    (hq' : q'.β = 0) : q'.δ.map φ = q.δ := by
  have h4 := q.h₄.trans (plusTailWeight_eq j hj ν₀ γ)
  rw [hq] at h4
  have h4' := q'.h₄
  rw [hq', zero_add] at h4'
  rw [h4']
  exact (add_left_cancel h4).symm

/-- `plusBotCornerEquiv_symm_smul` for top weights equal to those of the window loading. -/
theorem plusBotCornerEquivOf_symm_smul_of_eq
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hν : ν = Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (hν' : ν' = Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (q : MackeyQuad ν ν' αP δP) (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)) αC δC)
    (hq' : q'.β = 0) (hγ : q'.γ.map φ = q.γ) (hδ : q'.δ.map φ = q.δ)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q' Yc)
    (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc) :
    (plusBotCornerEquivOf X hQ q hq q' hmem).symm (t • n) =
      tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ) t •
        (plusBotCornerEquivOf X hQ q hq q' hmem).symm n := by
  subst hν hν'
  exact plusBotCornerEquiv_symm_smul X hQ s w hs q hq q' hq' t n

/-! ### The identity-shuffle spans and their images in the layers -/

/-- **The comparison of the identity-shuffle parts, for any top weights**: `leadingTopOneGen`
at `plusBotCornerEquivOf`. -/
def leadingTopOneOf (q : MackeyQuad ν ν' αP δP)
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj)) (q' : MackeyQuad μ μ' αC δC)
    (hγ : q'.γ.map φ = q.γ) (hδ : q'.δ.map φ = q.δ)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q' Yc)
    (hg : ∀ (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc),
      (plusBotCornerEquivOf X hQ q hq q' hmem).symm (t • n) =
        tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ) t •
          (plusBotCornerEquivOf X hQ q hq q' hmem).symm n) :
    mackeyTopOneSpan (Q := Sc) q' Yc ≃ₗ[k] mackeyTopOneSpan (Q := Sp) q Nₒ :=
  leadingTopOneGen (Λ := Λ) (Λc := Λc) X hQ q q' hγ hδ (plusBotCornerEquivOf X hQ q hq q' hmem)
    hg

/-- **The leading summands of the two layers, for any top weights**: `leadingLayerSpanEquiv`
at `leadingTopOneOf`. -/
def leadingLayerSpanEquivOf (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (q : {q : MackeyQuad ν ν' αP δP // Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hsum : αP + δP = ν + ν') (hq : q.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : {q' : MackeyQuad μ μ' αC δC // Multiset.card q'.β = 0}) (hsum' : αC + δC = μ + μ')
    (hγ : q'.1.γ.map φ = q.1.γ) (hδ : q'.1.δ.map φ = q.1.δ)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q.1 ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q'.1 Yc)
    (hg : ∀ (t : TensorKLR Sc q'.1.γ q'.1.δ) (n : botCorner Sc q'.1 Yc),
      (plusBotCornerEquivOf X hQ q.1 hq q'.1 hmem).symm (t • n) =
        tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ) t •
          (plusBotCornerEquivOf X hQ q.1 hq q'.1 hmem).symm n) :
    (mackeyTopOneSpan (Q := Sc) q'.1 Yc).map (indMackeyLeftMap (Q := Sc) hsum' Yc q'.1 q'.2)
      ≃ₗ[k] (mackeyTopOneSpan (Q := Sp) q.1 Nₒ).map
        (indMackeyLeftMap (Q := Sp) hsum Nₒ q.1 q.2) :=
  (Submodule.equivMapOfInjective _
      (indMackeyLeftMap_injective_of_klrSymm hsum' Yc hsc q') _).symm.trans
    ((leadingTopOneOf X hQ q.1 hq q'.1 hγ hδ hmem hg).trans
      (Submodule.equivMapOfInjective _ (indMackeyLeftMap_injective_of_klrSymm hsum Nₒ hsp q) _))

/-- **The leading span map, for any top weights**: `y ↦ (leadingLayerSpanEquivOf (Ξ_{q'} y)).1`,
from the identity-shuffle span at the cut to the layer `|q.β|` of the induced model of
`S_+(X)` at the cut `|ν|`. -/
def leadingSpanLayerMapOf (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (q : {q : MackeyQuad ν ν' αP δP // Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hsum : αP + δP = ν + ν') (hq : q.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : {q' : MackeyQuad μ μ' αC δC // Multiset.card q'.β = 0}) (hsum' : αC + δC = μ + μ')
    (hγ : q'.1.γ.map φ = q.1.γ) (hδ : q'.1.δ.map φ = q.1.δ)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q.1 ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q'.1 Yc)
    (hg : ∀ (t : TensorKLR Sc q'.1.γ q'.1.δ) (n : botCorner Sc q'.1 Yc),
      (plusBotCornerEquivOf X hQ q.1 hq q'.1 hmem).symm (t • n) =
        tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ) t •
          (plusBotCornerEquivOf X hQ q.1 hq q'.1 hmem).symm n) :
    mackeyTopOneSpan (Q := Sc) q'.1 Yc →ₗ[k]
      IndMackeyLayer Sp αP δP Nₒ (Multiset.card ν) (Multiset.card (stendhalWeight 2 ν₀)) :=
  mapEquivSubtypeMap (mackeyTopOneSpan (Q := Sc) q'.1 Yc)
    (indMackeyLeftMap (Q := Sc) hsum' Yc q'.1 q'.2)
    (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q')
    ((mackeyTopOneSpan (Q := Sp) q.1 Nₒ).map (indMackeyLeftMap (Q := Sp) hsum Nₒ q.1 q.2))
    (leadingLayerSpanEquivOf X hQ hsc hsp q hsum hq q' hsum' hγ hδ hmem hg)

theorem leadingSpanLayerMapOf_injective (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (q : {q : MackeyQuad ν ν' αP δP // Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hsum : αP + δP = ν + ν') (hq : q.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : {q' : MackeyQuad μ μ' αC δC // Multiset.card q'.β = 0}) (hsum' : αC + δC = μ + μ')
    (hγ : q'.1.γ.map φ = q.1.γ) (hδ : q'.1.δ.map φ = q.1.δ)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q.1 ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q'.1 Yc)
    (hg : ∀ (t : TensorKLR Sc q'.1.γ q'.1.δ) (n : botCorner Sc q'.1 Yc),
      (plusBotCornerEquivOf X hQ q.1 hq q'.1 hmem).symm (t • n) =
        tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ) t •
          (plusBotCornerEquivOf X hQ q.1 hq q'.1 hmem).symm n) :
    Function.Injective
      (leadingSpanLayerMapOf X hQ hsc hsp q hsum hq q' hsum' hγ hδ hmem hg) :=
  mapEquivSubtypeMap_injective _ _ _ _ _

/-- **The corner of the window loading is the image of the window endomorphism, for any top
weights equal to those of the window loading** (`map_range_cutWindowSpanEnd`). -/
theorem map_range_cutWindowSpanEnd_of_eq (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hν : ν = Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (hν' : ν' = Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (q : {q : MackeyQuad ν ν' αP δP // Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hsum : αP + δP = ν + ν') (hq : q.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          αC δC // Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0)
    (hγ : q₁.1.γ.map φ = q.1.γ) (hδ : q₁.1.δ.map φ = q.1.δ)
    (hmem : ∀ x : Inner,
      x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) q.1 ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈ botCorner Sc q₁.1 Yc)
    (hg : ∀ (t : TensorKLR Sc q₁.1.γ q₁.1.δ) (n : botCorner Sc q₁.1 Yc),
      (plusBotCornerEquivOf X hQ q.1 hq q₁.1 hmem).symm (t • n) =
        tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ) t •
          (plusBotCornerEquivOf X hQ q.1 hq q₁.1 hmem).symm n) :
    (LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁)).map
        (leadingSpanLayerMapOf X hQ hsc hsp q hsum hq q₁
          (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
          hγ hδ hmem hg) =
      LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))) := by
  subst hν hν'
  exact map_range_cutWindowSpanEnd X hQ s w hsc hsp hs q hq q₁ hq₁

end Categorification.Stendhal.CupCap
