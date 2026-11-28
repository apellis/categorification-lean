/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutData
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLoading
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyIdentity

/-!
# The head-strand filtration of the partial standardization at the cut on a loading

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L4: the same Mackey
step for `S_cut(Y)` (`KCutStd`, the partial standardization of the cut `A | R` of `λ`) at
the position `p = midPos s` of the red strand `λ_{j+1}` in a loading `s` of `λ`.

* `cutLoading s` is `s` read in the two blocks of the cut (`kCutStdAction_e`).
* Left of `p`, the strands of the tail block `R` are black, when the red strands of `s` left
  of `p` are among `λ_1, …, λ_j` (`cutLoading_black`).
* Hence `e(s)` maps `S_cut(Y)` into the bottom step `F_0` of the Mackey filtration for the top
  cut at `p` (`kCutStdAction_e_mem`), and, on the layer `0` of the induced model, lands in the
  span of the images under `Ξ_λ` of the identity-shuffle parts of the data `λ = 0`
  (`indMackeyLayerAct_cutLoading_mem_mackeyTopOne`): no tail strand reaches `s^<`.

This is the shape of `e_s S_+(X)` on its top layer (`CupCapTraceCutWindowIdentity`) with the
window removed. Webster's proof does not spell this out.

## Main results

* `Stendhal.CupCap.cutLoading`, `Stendhal.CupCap.kCutStdAction_e`,
  `Stendhal.CupCap.cutLoading_black`, `Stendhal.CupCap.kCutStdAction_e_mem`,
  `Stendhal.CupCap.indMackeyLayerAct_cutLoading_mem_mackeyTopOne`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {θ γ : Multiset I}

variable (j hj θ γ) in
/-- **A loading `s` of `λ` read in the two blocks of the cut** at the `j`-th red strand. -/
def cutLoading (s : Seq (stendhalWeight ℓ (θ + γ))) :
    Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :=
  Seq.cast (cutInputWeights_add θ γ).symm (castLabelsSeq (Nat.add_sub_of_le hj).symm rfl s)

omit [DecidableEq I] in
theorem cutLoading_apply (s : Seq (stendhalWeight ℓ (θ + γ)))
    (x : Fin (Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))))
    (y : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)))) (hxy : x.val = y.val) :
    (cutLoading j hj θ γ s).1 x =
      Sum.map id (Fin.cast (Nat.add_sub_of_le hj).symm) (s.lbl y) := by
  rw [cutLoading, Seq.cast_apply]
  refine (castLabelsSeq_lbl (Nat.add_sub_of_le hj).symm rfl _ _).trans ?_
  exact congrArg _ (congrArg s.1 (Fin.ext (by simp [hxy])))

variable (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)

/-- **`e(s)` acts on `S_cut(Y)` as the affine idempotent of `cutLoading s`.** -/
theorem kCutStdAction_e (s : Seq (stendhalWeight ℓ (θ + γ))) :
    kCutStdAction j hj Q Λ θ γ Y hQ (tensorOfKLR Q Λ (θ + γ) (e s)) =
      cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ
        (affineToTensor Q (cutLabels j hj Λ) θ γ (e (cutLoading j hj θ γ s))) := by
  change cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ
    ((castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)).symm
      (tensorOfKLR Q Λ (θ + γ) (e s))) = _
  congr 1
  rw [AlgEquiv.symm_apply_eq]
  have h := castLabels_tensorOfKLR_e Q (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ) Λ rfl
    (cutLoading j hj θ γ s) s (fun p q hpq => by
      rw [show (cutLoading j hj θ γ s).lbl q = (cutLoading j hj θ γ s).1 q from rfl,
        cutLoading_apply s q p hpq.symm]
      rcases s.lbl p with b | u <;> rfl)
  exact h.symm

omit [DecidableEq I] in
/-- **Left of `midPos s`, the strands of the tail block are black**, for a loading `s` whose
red strands left of `midPos s` are among `λ_1, …, λ_j`. -/
theorem cutLoading_black (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (x : Fin (Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))))
    (hx : x.val < midPos j s)
    (hmem : (cutLoading j hj θ γ s).1 x ∈
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :
    ((cutLoading j hj θ γ s).1 x).isLeft := by
  have hm := midPos_le j s
  have hl := cutLoading_apply (hj := hj) s x ⟨x.val, by omega⟩ rfl
  rw [hl] at hmem ⊢
  rcases hsl : s.lbl ⟨x.val, by omega⟩ with b | u
  · rfl
  · exfalso
    have hu := hs _ hx u hsl
    rw [hsl] at hmem
    obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hmem
    rcases z with b | r
    · exact Sum.inl_ne_inr hz
    · have hv := congrArg (fun z => match z with | .inl _ => 0 | .inr t => t.val) hz
      simp only [Sum.map_inr, Fin.natAdd, Fin.val_cast] at hv
      omega

omit [DecidableEq I] in
theorem midPos_le_card_cut (s : Seq (stendhalWeight ℓ (θ + γ))) :
    midPos j s + 0 ≤ Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) := by
  rw [cutInputWeights_add]
  have := midPos_le j s
  simp only [stendhalWeight, Multiset.card_add, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin] at this ⊢
  omega

/-- **L4: `e(s)` maps `S_cut(Y)` into the bottom step** of the Mackey filtration for the top
cut at `midPos s`. -/
theorem kCutStdAction_e_mem (hsym : KLRSymm (stendhalQ Q (cutLabels j hj Λ)))
    (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (v : KCutStd j hj Q Λ θ γ Y hQ) :
    kCutStdAction j hj Q Λ θ γ Y hQ (tensorOfKLR Q Λ (θ + γ) (e s)) v ∈
      cutMackeyFilt Q (cutLabels j hj Λ) θ γ Y (midPos j s + 0) 0 := by
  rw [kCutStdAction_e]
  exact cutStandardAction_e_mem_of_black hQ hsym (cutLoading j hj θ γ s)
    (midPos_le_card_cut s) (fun x hx hmem => cutLoading_black s hs x hx hmem) v

/-- **L4 on the layer**: on the layer `0` of the induced model of `S_cut(Y)` for the top cut
at `midPos s`, `e(cutLoading s)` lands in the span of the images under `Ξ_λ` of the
identity-shuffle parts of the data with `λ = 0`. -/
theorem indMackeyLayerAct_cutLoading_mem_mackeyTopOne
    (hsym : KLRSymm (stendhalQ Q (cutLabels j hj Λ)))
    (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (y : IndMackeyLayer (stendhalQ Q (cutLabels j hj Λ))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))
      (CutInput Q (cutLabels j hj Λ) θ γ Y)
      (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))) 0) :
    indMackeyLayerAct (CutInput Q (cutLabels j hj Λ) θ γ Y) (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0 y ∈
      ⨆ (q : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0}) (_ : q.1.β = 0),
        (mackeyTopOneSpan q.1 (CutInput Q (cutLabels j hj Λ) θ γ Y)).map
        (indMackeyLeftMap (Q := stendhalQ Q (cutLabels j hj Λ))
          (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
          (CutInput Q (cutLabels j hj Λ) θ γ Y) q.1 q.2) :=
  indMackeyLayerAct_e_mem_of_black_mackeyTopOne hsym (cutLoading j hj θ γ s)
    (midPos_le_card_cut s) (fun x hx hmem => cutLoading_black s hs x hx hmem) 0 rfl y

end Categorification.Stendhal.CupCap
