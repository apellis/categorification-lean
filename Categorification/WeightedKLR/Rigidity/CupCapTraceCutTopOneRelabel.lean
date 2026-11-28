/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneLabels
import Categorification.KLR.ReindexConcat

/-!
# Relabelling the induced corner of the leading Mackey layer

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the top factor).

The identity-shuffle part of the leading Mackey layer is `Ind_{γ,δ}(E N)`
(`topOneCornerEquiv`). At the cut of `S_cut` (datum `q'`, labels of `λ`) and at the outer cut
of `S_+` (datum `q`, labels of `λ⁺`) the weights are related by `q.γ = q'.γ.map φ`,
`q.δ = q'.δ.map φ` for `φ = cutToPlusColour` (`leadingQuad_γ_eq_map`, `leadingQuad_δ_eq_map`).

`cutPlusRelabel` is the relabelling `Seq μ' ≃ Seq μ`, `𝐣 ↦ φ ∘ 𝐣`, for any `μ = μ'.map φ`; it
carries the Stendhal parameters of `λ` to those of `λ⁺` (`stendhalQ_cutToPlusColour`) and is
compatible with concatenation (`cutPlusRelabel_append`). Hence (`KLR.KLRAlgebra.relabelInd`)
a `k`-linear isomorphism `N' ≅ N` intertwining `R(γ') ⊗ R(δ') ≅ R(γ) ⊗ R(δ)` induces
`Ind_{γ',δ'} N' ≅ Ind_{γ,δ} N` (`cutPlusInd`), linear along `R(γ' + δ') ≅ R(γ + δ)`
(`cutPlusInd_smul`).

For the leading data, with `N' = E' · Res X` and `N = E · BlocksMid X` and the inverse of
`plusBotCornerEquiv`, this gives the comparison of the identity-shuffle parts
`mackeyTopOneSpan q' (Res X) ≅ mackeyTopOneSpan q (BlocksMid X)` (`leadingTopOneEquiv`),
once `plusBotCornerEquiv` is known to intertwine the actions of `R(q'.γ) ⊗ R(q'.δ)` and
`R(q.γ) ⊗ R(q.δ)`. That intertwining (step 2 of the handoff) is an argument of
`leadingTopOneEquiv`, a construction datum of this intermediate step, not a hypothesis of
Lemma 7.19.

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.cutPlusRelabel`, `Stendhal.CupCap.cutPlusInd`,
  `Stendhal.CupCap.leadingTopOneEquiv`.

## Main results

* `Stendhal.CupCap.cutPlusRelabel_equiv`, `Stendhal.CupCap.cutPlusRelabel_append`,
  `Stendhal.CupCap.cutPlusInd_tmul`, `Stendhal.CupCap.cutPlusInd_smul`,
  `Stendhal.CupCap.leadingQuad_add_eq_map`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)

local notation "φ" => cutToPlusColour (I := I) j hj
local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

/-! ### Relabelling along `cutToPlusColour` -/

/-- **Relabelling the cut labels as labels of `λ⁺`**: `Seq μ' ≃ Seq μ`, `𝐣 ↦ φ ∘ 𝐣`, for
`μ = μ'.map φ`, `φ = cutToPlusColour`, from the Stendhal parameters of `λ` to those of `λ⁺`. -/
def cutPlusRelabel {μ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {μ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))} (h : μ'.map φ = μ) :
    SeqRelabel k Sc Sp μ' μ :=
  (SeqRelabel.ofInjectiveOf (cutToPlusColour_injective j hj) Sp Sc
    (fun a b _ => stendhalQ_cutToPlusColour j hj Q Λ Λc a b) μ').castRight h

omit [DecidableEq I] in
theorem cutPlusRelabel_equiv {μ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {μ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))} (h : μ'.map φ = μ) (i : Seq μ') :
    (cutPlusRelabel j hj Q Λ Λc h).equiv i = seqCast h (Seq.map φ i) :=
  SeqRelabel.castRight_equiv _ h i

omit [DecidableEq I] in
/-- `cutPlusRelabel` is compatible with concatenation. -/
theorem cutPlusRelabel_append {γ' δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {γ δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))} (hγ : γ'.map φ = γ) (hδ : δ'.map φ = δ)
    (h : (γ' + δ').map φ = γ + δ) (i₁ : Seq γ') (i₂ : Seq δ') :
    (cutPlusRelabel j hj Q Λ Λc h).equiv (i₁.append i₂) =
      ((cutPlusRelabel j hj Q Λ Λc hγ).equiv i₁).append
        ((cutPlusRelabel j hj Q Λ Λc hδ).equiv i₂) := by
  simp only [cutPlusRelabel_equiv]
  exact Seq.seqCast_map_append hγ hδ h i₁ i₂

omit [DecidableEq I] in
theorem map_add_eq_of_map_eq {γ' δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {γ δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))} (hγ : γ'.map φ = γ) (hδ : δ'.map φ = δ) :
    (γ' + δ').map φ = γ + δ := by
  rw [Multiset.map_add, hγ, hδ]

/-! ### Relabelling induced modules -/

section Ind

variable {γ' δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
  {γ δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
  (hγ : γ'.map (cutToPlusColour (I := I) j hj) = γ)
  (hδ : δ'.map (cutToPlusColour (I := I) j hj) = δ)
  {N' N : Type*} [AddCommGroup N'] [Module k N']
  [Module (TensorKLR (stendhalQ Q (cutLabels j hj Λ)) γ' δ') N']
  [AddCommGroup N] [Module k N]
  [Module (TensorKLR (stendhalQ Q (plusBlockLabels Λ Λc j hj)) γ δ) N]
  (g : N' ≃ₗ[k] N) (hg : ∀ (t : TensorKLR (stendhalQ Q (cutLabels j hj Λ)) γ' δ') (n : N'),
    g (t • n) = tensorRelabel (cutPlusRelabel j hj Q Λ Λc hγ)
      (cutPlusRelabel j hj Q Λ Λc hδ) t • g n)

/-- **`Ind_{γ',δ'} N' ≅ Ind_{γ,δ} N`** for the cut labels `γ', δ'` of `λ` read as labels
`γ = γ'.map φ`, `δ = δ'.map φ` of `λ⁺`, along an isomorphism `N' ≅ N` intertwining the
relabelling `R(γ') ⊗ R(δ') ≅ R(γ) ⊗ R(δ)`. -/
def cutPlusInd : Ind Sc γ' δ' N' ≃ₗ[k] Ind Sp γ δ N :=
  relabelInd (cutPlusRelabel j hj Q Λ Λc hγ) (cutPlusRelabel j hj Q Λ Λc hδ)
    (cutPlusRelabel j hj Q Λ Λc (map_add_eq_of_map_eq j hj hγ hδ))
    (cutPlusRelabel_append j hj Q Λ Λc hγ hδ _) g hg

theorem cutPlusInd_tmul (m : IndBimod Sc γ' δ') (n : N') :
    cutPlusInd j hj Q Λ Λc hγ hδ g hg (BalancedTensor.tmul m n) =
      BalancedTensor.tmul (relabelIndBimod (cutPlusRelabel j hj Q Λ Λc hγ)
        (cutPlusRelabel j hj Q Λ Λc hδ)
        (cutPlusRelabel j hj Q Λ Λc (map_add_eq_of_map_eq j hj hγ hδ))
        (cutPlusRelabel_append j hj Q Λ Λc hγ hδ _) m) (g n) := rfl

/-- `cutPlusInd` is linear along `R(γ' + δ') ≅ R(γ + δ)`. -/
theorem cutPlusInd_smul (r : KLRAlgebra k Sc (γ' + δ')) (y : Ind Sc γ' δ' N') :
    cutPlusInd j hj Q Λ Λc hγ hδ g hg (r • y) =
      relabelHom (cutPlusRelabel j hj Q Λ Λc (map_add_eq_of_map_eq j hj hγ hδ)) r •
        cutPlusInd j hj Q Λ Λc hγ hδ g hg y :=
  relabelInd_smul _ _ _ _ g hg r y

end Ind

/-! ### The leading data -/

variable {Q Λ Λc} {θ γ ν₀ : Multiset I}

omit [DecidableEq I] in
/-- `q.γ + q.δ = (q'.γ + q'.δ).map φ` for the leading data. -/
theorem leadingQuad_add_eq_map (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) :
    (q'.γ + q'.δ).map φ = q.γ + q.δ :=
  map_add_eq_of_map_eq j hj (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm
    (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm

attribute [local instance] botCornerModuleRight

variable (Q Λ Λc)
variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

/-- **The identity-shuffle parts of the leading layers of `S_cut(Res X)` and `S_+(X)`**:
`mackeyTopOneSpan q' (Res X) ≅ Ind_{q'.γ,q'.δ}(E' · Res X) ≅ Ind_{q.γ,q.δ}(E · BlocksMid X)
≅ mackeyTopOneSpan q (BlocksMid X)`, along the inverse of `plusBotCornerEquiv` and the
relabelling `cutPlusRelabel`. The argument `hg` says that the inverse of `plusBotCornerEquiv`
intertwines `R(q'.γ) ⊗ R(q'.δ)` and `R(q.γ) ⊗ R(q.δ)` through `cutPlusRelabel`; it is the
remaining step 2 of the L5 top factor (route datum of this intermediate construction). -/
def leadingTopOneEquiv (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0)
    (hg : ∀ (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc),
      (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm (t • n) =
        tensorRelabel
          (cutPlusRelabel j hj Q Λ Λc (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm)
          (cutPlusRelabel j hj Q Λ Λc (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm) t •
          (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm n) :
    mackeyTopOneSpan (Q := Sc) q' Yc ≃ₗ[k] mackeyTopOneSpan (Q := Sp) q Nₒ :=
  ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm.trans
    (cutPlusInd j hj Q Λ Λc (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm
      (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm
      (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm hg)).trans
    (topOneCornerEquiv q Nₒ (stendhalQ_symm Q (plusBlockLabels Λ Λc j hj) hQ))

end Categorification.Stendhal.CupCap
