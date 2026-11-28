/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneIntertwine

/-!
# Recasting a Mackey datum along equal top weights

Used for Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the
`W`-linearity of (T)).

A Mackey datum `q` for the top cut `ν + ν'` is a datum for any `ν₁ + ν₁'` with `ν = ν₁`,
`ν' = ν₁'`, keeping `α, β, γ, δ` (`MackeyQuad.recast`). The bottom corner, the induced module
`Ind_{γ,δ}(E N)` and the identity-shuffle part do not see the top weights, and `Ξ_λ` on the
identity-shuffle part is unchanged up to the cast of the layer index `|ν| = |ν₁|`
(`indMackeyLeftMap_topOneCornerEquiv_recast`). No new hypothesis.

## Main definitions

* `KLR.KLRAlgebra.MackeyQuad.recast`, `KLR.KLRAlgebra.indLayerIndexCast`.
* `Stendhal.CupCap.leadingTopOneGen`: the identity-shuffle comparison of the leading datum for
  any bottom-corner isomorphism (`leadingTopOneSpanEquiv_eq_gen`).

## Main results

* `KLR.KLRAlgebra.indLayerIndexCast_act`,
  `KLR.KLRAlgebra.indMackeyLeftMap_topOneCornerEquiv_recast`,
  `KLR.KLRAlgebra.indMackeyLeftMap_proof_irrel`, `Stendhal.CupCap.leadingTopOneGen_congr`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν₁ ν₁' ν'' ν''' : Multiset I}

/-- **A Mackey datum read at equal top weights**, with the same `α, β, γ, δ`. -/
abbrev MackeyQuad.recast (q : MackeyQuad ν ν' ν'' ν''') (h : ν = ν₁) (h' : ν' = ν₁') :
    MackeyQuad ν₁ ν₁' ν'' ν''' where
  α := q.α
  β := q.β
  γ := q.γ
  δ := q.δ
  h₁ := q.h₁.trans h
  h₂ := q.h₂.trans h'
  h₃ := q.h₃
  h₄ := q.h₄

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

/-- **The layers of `Ind N` depend on the cut only through its value.** -/
def indLayerIndexCast {n n' : ℕ} (h : n = n') (c : ℕ) :
    IndMackeyLayer Q ν'' ν''' N n c ≃ₗ[k] IndMackeyLayer Q ν'' ν''' N n' c := by
  subst h
  exact LinearEquiv.refl k _

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indLayerIndexCast_rfl {n : ℕ} (c : ℕ) (y : IndMackeyLayer Q ν'' ν''' N n c) :
    indLayerIndexCast N (rfl : n = n) c y = y :=
  rfl

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indLayerIndexCast_self {n : ℕ} (h : n = n) (c : ℕ)
    (y : IndMackeyLayer Q ν'' ν''' N n c) : indLayerIndexCast N h c y = y :=
  rfl

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- `indMackeyLeftMap` does not depend on the proof of the weight equation. -/
theorem indMackeyLeftMap_proof_irrel (h h₀ : ν'' + ν''' = ν + ν') (q : MackeyQuad ν ν' ν'' ν''')
    {c : ℕ} (hc : Multiset.card q.β = c) :
    indMackeyLeftMap (k := k) (Q := Q) h N q hc = indMackeyLeftMap h₀ N q hc :=
  rfl

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- The cast of the layer index commutes with the action of `R(ν'' + ν''')`. -/
theorem indLayerIndexCast_act {n n' : ℕ} (h : n = n') (c : ℕ)
    {z : KLRAlgebra k Q (ν'' + ν''')}
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c →
      z * y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c)
    (hz' : ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n' (Multiset.card ν'') c →
      z * y ∈ mackeyFilt k Q (ν'' + ν''') n' (Multiset.card ν'') c)
    (y : IndMackeyLayer Q ν'' ν''' N n c) :
    indLayerIndexCast N h c (indMackeyLayerAct N z hz c y) =
      indMackeyLayerAct N z hz' c (indLayerIndexCast N h c y) := by
  subst h
  rfl

attribute [local instance] botCornerModuleRight

variable (hsym : KLRSymm Q)

/-- **`Ξ_λ` on the identity-shuffle part does not see the top weights**: for two recasts of a
Mackey datum `q` to equal top weights `ν₁ = ν₂`, `Ξ ∘ T` agree up to the cast of the layer
index. -/
theorem indMackeyLeftMap_topOneCornerEquiv_recast (q : MackeyQuad ν ν' ν'' ν''')
    {ν₂ ν₂' : Multiset I} (h : ν = ν₁) (h' : ν' = ν₁') (g : ν = ν₂) (g' : ν' = ν₂')
    (e : ν₁ = ν₂) (e' : ν₁' = ν₂') (hh₁ : ν'' + ν''' = ν₁ + ν₁') (hh₂ : ν'' + ν''' = ν₂ + ν₂')
    {c : ℕ} (hc : Multiset.card q.β = c) (x : Ind Q q.γ q.δ (botCorner Q q N)) :
    indMackeyLeftMap hh₂ N (q.recast g g') hc
        (topOneCornerEquiv (q.recast g g') N hsym x : MackeyLeftInd Q N (q.recast g g')) =
      indLayerIndexCast N (congrArg Multiset.card e) c
        (indMackeyLeftMap hh₁ N (q.recast h h') hc
          (topOneCornerEquiv (q.recast h h') N hsym x : MackeyLeftInd Q N (q.recast h h'))) := by
  subst e e'
  obtain rfl : h = g := rfl
  obtain rfl : h' = g' := rfl
  obtain rfl : hh₁ = hh₂ := rfl
  exact (indLayerIndexCast_rfl N c _).symm

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "φ" => cutToPlusColour (I := I) j hj
local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)
local notation "αP" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))))
  (stendhalWeight j θ)
local notation "δP" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))

attribute [local instance] botCornerModuleRight

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

variable {ν ν' : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
  {μ μ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}

/-- **The comparison of the identity-shuffle parts, for any bottom-corner isomorphism** `E`
intertwining the relabelled bottom algebras: `leadingTopOneEquiv` with `plusBotCornerEquiv`
replaced by `E`. -/
def leadingTopOneGen (q : MackeyQuad ν ν' αP δP)
    (q' : MackeyQuad μ μ' (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
      (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hγ : q'.γ.map φ = q.γ) (hδ : q'.δ.map φ = q.δ)
    (E : botCorner Sp q Nₒ ≃ₗ[k] botCorner Sc q' Yc)
    (hg : ∀ (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc),
      E.symm (t • n) = tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ)
        (cutPlusRelabel j hj Q Λ Λc hδ) t • E.symm n) :
    mackeyTopOneSpan (Q := Sc) q' Yc ≃ₗ[k] mackeyTopOneSpan (Q := Sp) q Nₒ :=
  ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm.trans
    (cutPlusInd j hj Q Λ Λc hγ hδ E.symm hg)).trans
    (topOneCornerEquiv q Nₒ (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ))

theorem leadingTopOneSpanEquiv_eq_gen (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
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
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) :
    leadingTopOneSpanEquiv (Λ := Λ) (Λc := Λc) X hQ s w hs q hq q' hq' =
      leadingTopOneGen (Λ := Λ) (Λc := Λc) X hQ q q'
        (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm
        (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm
        (plusBotCornerEquiv X hQ s w hs q hq q' hq')
        (plusBotCornerEquiv_symm_smul X hQ s w hs q hq q' hq') :=
  rfl

/-- `leadingTopOneGen` does not depend on the proofs `hγ`, `hδ`, `hg`. -/
theorem leadingTopOneGen_congr (q : MackeyQuad ν ν' αP δP)
    (q' : MackeyQuad μ μ' (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
      (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hγ hγ₁ : q'.γ.map φ = q.γ) (hδ hδ₁ : q'.δ.map φ = q.δ)
    (E : botCorner Sp q Nₒ ≃ₗ[k] botCorner Sc q' Yc)
    (hg : ∀ (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc),
      E.symm (t • n) = tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ)
        (cutPlusRelabel j hj Q Λ Λc hδ) t • E.symm n)
    (hg₁ : ∀ (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc),
      E.symm (t • n) = tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ₁)
        (cutPlusRelabel j hj Q Λ Λc hδ₁) t • E.symm n) :
    leadingTopOneGen (Λ := Λ) (Λc := Λc) X hQ q q' hγ hδ E hg =
      leadingTopOneGen (Λ := Λ) (Λc := Λc) X hQ q q' hγ₁ hδ₁ E hg₁ := rfl

end Categorification.Stendhal.CupCap
