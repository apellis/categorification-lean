/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingFactors
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneAction

/-!
# The bottom corners of the leading Mackey data intertwine `R(γ) ⊗ R(δ)`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the intertwining
of the bottom corners).

`plusBotCornerEquiv : E · BlocksMid X ≅ E' · Res X` is the identity of `X` read through the
identity coordinate of the inner standardization. Along the relabelling
`R(q'.γ) ⊗ R(q'.δ) ≅ R(q.γ) ⊗ R(q.δ)` of `cutPlusRelabel`, it intertwines the actions through the
bottom idempotents (`plusBotCornerEquiv_tensorRelabel_smul`): for `a ⊗ b`, both sides act on `X`
by `H ⊗ (1 ⊗ T)`, where the head factors agree by (H)
(`relabel_cutPrefixProjection_leading_head`) and the tail factors by (T)
(`cutSuffixProjection_leading_tail`, `cutSuffixProjection_plus_tail`,
`relabel_cutSuffixProjection_tailLift`), through `botCornerBlocksEquiv_smul`.

This discharges the construction datum `hg` of `leadingTopOneEquiv`
(`plusBotCornerEquiv_symm_smul`), and gives the comparison of the identity-shuffle parts of the
leading layers, `mackeyTopOneSpan q' (Res X) ≅ mackeyTopOneSpan q (BlocksMid X)`, with no
extra argument (`leadingTopOneSpanEquiv`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.leadingTopOneSpanEquiv`.

## Main results

* `Stendhal.CupCap.plusBotCornerEquiv_tensorRelabel_smul`,
  `Stendhal.CupCap.plusBotCornerEquiv_symm_smul`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
local notation "Inner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
  (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))

/-- **`plusBotCornerEquiv` intertwines `R(q.γ) ⊗ R(q.δ)` and `R(q'.γ) ⊗ R(q'.δ)`** along the
relabelling `cutPlusRelabel` (Webster v3, Lemma 7.19, trace half, step L5). -/
theorem plusBotCornerEquiv_tensorRelabel_smul (s : Seq (stendhalWeight ℓ (θ + γ)))
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
    (hq' : q'.β = 0) (t : TensorKLR Sc q'.γ q'.δ) (z : botCorner Sp q Nₒ) :
    plusBotCornerEquiv X hQ s w hs q hq q' hq'
        (tensorRelabel
          (cutPlusRelabel j hj Q Λ Λc (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm)
          (cutPlusRelabel j hj Q Λ Λc (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm) t • z) =
      t • plusBotCornerEquiv X hQ s w hs q hq q' hq' z := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => rw [map_add, add_smul, map_add, h₁, h₂, add_smul]
  | tmul a b =>
    have hδ' : (stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd j)) = q'.δ := by
      have h4 := q'.h₄
      rw [hq', zero_add] at h4
      exact h4.symm
    have hγt : ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))).map
        (Sum.map (id : I → I) (Fin.natAdd j)) = q.δ := by
      rw [leadingQuad_δ_eq_map j hj s w q hq q' hq', ← hδ', Multiset.map_map, Multiset.map_map,
        cutToPlusColour_comp_natAdd]
    have hβ := hq.trans (windowWeight_eq_map j hj ν₀)
    obtain ⟨c, rfl⟩ : ∃ c, relabelHom (subfamilyRelabel Q (cutLabels j hj Λ)
        (Fin.natAdd_injective _ j) hδ') c = b :=
      ⟨(relabelEquiv _).symm b, (relabelEquiv _).apply_symm_apply b⟩
    apply Subtype.ext
    rw [tensorRelabel_tmul, cutPlusRelabel_subfamilyRelabel_tail j hj Q Λ Λc hδ' _ hγt]
    have hfz : ∀ z' : botCorner Sp q Nₒ, (plusBotCornerEquiv X hQ s w hs q hq q' hq' z' : Yc) =
        innerToRes j hj Q Λ Λc θ γ ν₀ X
          (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
            (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ z' : Inner) := by
      intro z'
      rw [plusBotCornerEquiv_apply, botCornerBlocksEquiv_apply]
    rw [hfz, coe_botCornerModuleRight_smul, hfz,
      botCornerBlocksEquiv_smul Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ hβ _ _ (1 ⊗ₜ tailLift j hj Q Λ Λc c)
        (cutSuffixProjection_plus_tail j hj Q Λ Λc hβ.symm hγt q.h₄ _) z]
    have hL : ∀ (H : TensorProductAlgebra k Q
          (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))) θ) (W : Inner),
        (innerToRes j hj Q Λ Λc θ γ ν₀ X (blocksHeadEnd Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ X) H
            ((1 ⊗ₜ tailLift j hj Q Λ Λc c : TensorKLR (stendhalQ Q
              (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
              ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))) _) •
                W)) : X) =
        ((relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ H ⊗ₜ
          ((1 : TensorProductAlgebra k Q Λc ν₀) ⊗ₜ
            relabelTensorProductAlgebra Q (plusBlockLabels_tail Λ Λc j hj) γ
              (cutSuffixProjection (a := 2) (r := ℓ - j) Q
                (blocksTailLabels (plusBlockLabels Λ Λc j hj)) γ (tailLift j hj Q Λ Λc c))) :
          PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from W)) := by
      intro H W
      change (plusFactorEquiv Q Λ Λc j hj θ ν₀ γ (H ⊗ₜ 1) •
        (plusFactorEquiv Q Λ Λc j hj θ ν₀ γ ((1 : TensorProductAlgebra k Q
          (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))) θ) ⊗ₜ
          cutInputMap (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
            (1 ⊗ₜ tailLift j hj Q Λ Λc c)) • (show X from W)) : X) = _
      have e1 : plusFactorEquiv Q Λ Λc j hj θ ν₀ γ (H ⊗ₜ 1) =
          relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ H ⊗ₜ 1 := by
        rw [plusFactorEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
          map_one]
        rfl
      have e2 : plusFactorEquiv Q Λ Λc j hj θ ν₀ γ ((1 : TensorProductAlgebra k Q
          (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))) θ) ⊗ₜ
          cutInputMap (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
            (1 ⊗ₜ tailLift j hj Q Λ Λc c)) =
          (1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
            ((1 : TensorProductAlgebra k Q Λc ν₀) ⊗ₜ
              relabelTensorProductAlgebra Q (plusBlockLabels_tail Λ Λc j hj) γ
                (cutSuffixProjection (a := 2) (r := ℓ - j) Q
                  (blocksTailLabels (plusBlockLabels Λ Λc j hj)) γ (tailLift j hj Q Λ Λc c))) := by
        rw [cutInputMap, Algebra.TensorProduct.map_tmul, map_one, plusFactorEquiv,
          Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
          AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
          map_one]
        rfl
      rw [e1, e2, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hR : ∀ (W : Inner),
        (((quadBot q' ((1 : TensorKLR Sc q'.α q'.β) ⊗ₜ (a ⊗ₜ relabelHom (subfamilyRelabel Q
          (cutLabels j hj Λ) (Fin.natAdd_injective _ j) hδ') c))) •
            innerToRes j hj Q Λ Λc θ γ ν₀ X W : Yc) : X) =
        ((cutPrefixProjection (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ
            (castAlg Sc q'.h₃ (concat Sc q'.α q'.γ (1 ⊗ₜ a))) ⊗ₜ
          ((1 : TensorProductAlgebra k Q Λc ν₀) ⊗ₜ
            cutSuffixProjection (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) γ
              (castAlg Sc q'.h₄ (concat Sc q'.β q'.δ (1 ⊗ₜ relabelHom (subfamilyRelabel Q
                (cutLabels j hj Λ) (Fin.natAdd_injective _ j) hδ') c)))) :
          PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from W)) := by
      intro W
      change (plusOuterIncl j hj Q Λ Λc θ γ ν₀ (cutInputMap (a := j) (r := ℓ - j) Q
        (cutLabels j hj Λ) θ γ (quadBot q' (((1 : KLRAlgebra k Sc q'.α) ⊗ₜ
          (1 : KLRAlgebra k Sc q'.β)) ⊗ₜ (a ⊗ₜ relabelHom (subfamilyRelabel Q
            (cutLabels j hj Λ) (Fin.natAdd_injective _ j) hδ') c)))) • (show X from W) : X) = _
      rw [quadBot_tmul]
      rfl
    refine (hL _ _).trans (Eq.trans ?_ (hR _).symm)
    have hA := relabel_cutPrefixProjection_leading_head (Λc := Λc) j hj s w hs q hq q' hq' a
    have hB := (relabel_cutSuffixProjection_tailLift j hj Q Λ Λc c).trans
      (cutSuffixProjection_leading_tail j hj Q Λ hq' q'.h₄ hδ' c).symm
    exact congrArg₂ (fun A B => ((A ⊗ₜ ((1 : TensorProductAlgebra k Q Λc ν₀) ⊗ₜ B) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from _))) hA hB

/-- **The construction datum of `leadingTopOneEquiv`**: the inverse of `plusBotCornerEquiv`
intertwines `R(q'.γ) ⊗ R(q'.δ)` and `R(q.γ) ⊗ R(q.δ)` through `cutPlusRelabel`. -/
theorem plusBotCornerEquiv_symm_smul (s : Seq (stendhalWeight ℓ (θ + γ)))
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
    (hq' : q'.β = 0) (t : TensorKLR Sc q'.γ q'.δ) (n : botCorner Sc q' Yc) :
    (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm (t • n) =
      tensorRelabel
        (cutPlusRelabel j hj Q Λ Λc (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm)
        (cutPlusRelabel j hj Q Λ Λc (leadingQuad_δ_eq_map j hj s w q hq q' hq').symm) t •
        (plusBotCornerEquiv X hQ s w hs q hq q' hq').symm n := by
  apply (plusBotCornerEquiv X hQ s w hs q hq q' hq').injective
  rw [LinearEquiv.apply_symm_apply, plusBotCornerEquiv_tensorRelabel_smul,
    LinearEquiv.apply_symm_apply]

local notation "Sp'" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

/-- **The identity-shuffle parts of the leading layers of `S_cut(Res X)` and `S_+(X)`**
(Webster v3, Lemma 7.19, trace half, step L5):
`mackeyTopOneSpan q' (Res X) ≅ mackeyTopOneSpan q (BlocksMid X)`, i.e. `leadingTopOneEquiv`
with its intertwining datum discharged by `plusBotCornerEquiv_symm_smul`. -/
def leadingTopOneSpanEquiv (s : Seq (stendhalWeight ℓ (θ + γ)))
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
    (hq' : q'.β = 0) :
    mackeyTopOneSpan (Q := Sc) q' Yc ≃ₗ[k] mackeyTopOneSpan (Q := Sp') q Nₒ :=
  leadingTopOneEquiv j hj Q Λ Λc X hQ s w hs q hq q' hq'
    (plusBotCornerEquiv_symm_smul X hQ s w hs q hq q' hq')

theorem leadingTopOneSpanEquiv_eq (s : Seq (stendhalWeight ℓ (θ + γ)))
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
    (hq' : q'.β = 0) :
    leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' =
      leadingTopOneEquiv j hj Q Λ Λc X hQ s w hs q hq q' hq'
        (plusBotCornerEquiv_symm_smul X hQ s w hs q hq q' hq') := rfl

end Categorification.Stendhal.CupCap
