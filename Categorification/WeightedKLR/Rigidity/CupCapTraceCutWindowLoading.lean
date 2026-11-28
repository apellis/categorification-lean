/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowFilt
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KTransport
import Categorification.WeightedKLR.Rigidity.CupCapSpanning
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLoading
import Categorification.WeightedKLR.Rigidity.CupCapLeftDescent

/-!
# The window loadings on the head-strand filtration of `S_+`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L2 at the cut at the
`j`-th red strand. Let `s` be a loading of `λ` whose red strands left of the maximum
`p = midPos s` are among `λ_1, …, λ_j` (true for every loading with the red strands in order),
and let `w` be a loading of the strands at the maximum, so that `ι_s(e(w))` is the idempotent of
the loading `s` with `w` inserted at `p`. Read in the three blocks `A | M | R` of `λ⁺`
(`windowLoading`), every strand of the blocks `M R` left of `p` is black. Hence, with
`N = |window|`:

* `ι_s(e(w))` maps `S_+(X)` into the step `F_N` of the filtration by the head strands passing
  the end `p + N` of the window (`plusStandardAction_insertMap_e_mem`);
* on the `N`-th layer of the induced model, `ι_s(e(w))` lands in the span of the images of the
  maps `Ξ_λ` of the Mackey data `λ` whose weight is that of `w`
  (`indMackeyLayerAct_windowLoading_mem`), i.e. of the window strands alone.

Webster's proof does not spell this out. No hypothesis beyond the position condition on `s`.

## Main definitions

* `Stendhal.CupCap.windowLoading`.

## Main results

* `Stendhal.CupCap.windowAffine_e`, `Stendhal.CupCap.windowLoading_black`,
  `Stendhal.CupCap.plusStandardAction_insertMap_e_mem`,
  `Stendhal.CupCap.plusStandardAction_insertMap_redOrdered_mem`,
  `Stendhal.CupCap.windowWt_windowLoading`,
  `Stendhal.CupCap.indMackeyLayerAct_windowLoading_mem`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

section Casts

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

theorem castLabelsKLR_symm_e {n n' : ℕ} (h : n = n') (Λ : Fin n' → I →₀ ℕ) (ν : Multiset I)
    (t : Seq (stendhalWeight n' ν)) :
    (castLabelsKLR Q h Λ ν).symm (e t) = e (castLabelsSeq h.symm rfl t) := by
  subst h
  have ht : castLabelsSeq rfl rfl t = t := by
    apply Subtype.ext
    funext p
    change (castLabelsSeq rfl rfl t).lbl p = t.lbl p
    rw [castLabelsSeq_lbl]
    change Sum.map id (Fin.cast rfl) (t.lbl p) = t.lbl p
    rcases t.lbl p with b | r <;> rfl
  rw [ht]
  rfl

theorem castKLR_symm_e {J : Type*} [DecidableEq J] {P : J → J → MvPolynomial (Fin 2) k}
    {μ μ' : Multiset J} (h : μ = μ') (t : Seq μ') :
    (castKLR P h).symm (e t) = e (Seq.cast h.symm t) := by
  subst h
  rfl

end Casts

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I) (hQ : KLRSymm Q)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]

/-- **The loading `s` with `w` inserted at the maximum**, read in the three blocks of `λ⁺`. -/
def windowLoading (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀)) :
    Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) :=
  Seq.cast (cutInputWeights_add θ (ν₀ + γ)).symm
    (castLabelsSeq (plusBlock_card j hj).symm rfl
      (Seq.cast (congrArg (stendhalWeight (ℓ + 2)) (plusWeight_eq θ γ ν₀).symm)
        (insertSeq (j := j) (hj := hj) s (midPos j s) (midPos_le j s)
          (Seq.map (cupColour j hj) w))))

variable {j hj θ γ ν₀}

theorem windowAffine_e (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀)) :
    windowAffine j hj Q Λ Λc θ γ ν₀ s (e w) = e (windowLoading j hj θ γ ν₀ s w) := by
  rw [windowAffine, insertMap_e, castKLR_e, castLabelsKLR_symm_e]
  exact castKLR_symm_e (P := stendhalQ Q (plusBlockLabels Λ Λc j hj)) _ _

omit [DecidableEq I] in
theorem windowLoading_lbl (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (x : Fin (Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)))))
    (y : Fin (Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)))) (hxy : x.val = y.val) :
    (windowLoading j hj θ γ ν₀ s w).1 x = Sum.map id (Fin.cast (plusBlock_card j hj).symm)
      ((insertSeq (j := j) (hj := hj) s (midPos j s) (midPos_le j s)
        (Seq.map (cupColour j hj) w)).lbl y) := by
  rw [windowLoading, Seq.cast_apply]
  refine (castLabelsSeq_lbl (plusBlock_card j hj).symm rfl _ _).trans ?_
  exact congrArg _ (congrArg (insertSeq (j := j) (hj := hj) s (midPos j s) (midPos_le j s)
    (Seq.map (cupColour j hj) w)).1 (Fin.ext (by simp [hxy])))

omit [DecidableEq I] in
include hj in
theorem card_windowLoading_weight :
    Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) =
      Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
  rw [cutInputWeights_add]
  simp only [stendhalWeight, Multiset.card_add, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin]
  omega

omit [DecidableEq I] in
/-- **Left of the maximum, the strands of the blocks `M R` are black**, for a loading `s`
whose red strands left of `midPos s` are among `λ_1, …, λ_j`. -/
theorem windowLoading_black (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (x : Fin (Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)))))
    (hx : x.val < midPos j s)
    (hmem : (windowLoading j hj θ γ ν₀ s w).1 x ∈ Multiset.map (Sum.map (id : I → I)
      (Fin.natAdd j)) (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) :
    ((windowLoading j hj θ γ ν₀ s w).1 x).isLeft := by
  have hm := midPos_le j s
  have hy : x.val < Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
    exact lt_of_lt_of_eq x.2 (card_windowLoading_weight (hj := hj))
  have hl := windowLoading_lbl (hj := hj) s w x ⟨x.val, hy⟩ rfl
  rw [insertSeq_lbl_lt s (midPos_le j s) _ ⟨x.val, by omega⟩ hx rfl] at hl
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
      simp only [Sum.map_inr, Fin.natAdd, oldColour, oldRed, insertPos_inl_val, Fin.val_cast,
        hu, ite_true] at hv
      omega

variable {N}

/-- **The window loading maps `S_+` into `F_N`**: for a loading `s` whose red strands left of
the maximum are among `λ_1, …, λ_j`, the idempotent `ι_s(e(w))` maps `S_+(X)` into the step
`N = |window|` of the filtration by the head strands passing the end of the window. -/
theorem plusStandardAction_insertMap_e_mem
    (hsym : KLRSymm (stendhalQ Q (plusBlockLabels Λ Λc j hj)))
    (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (v : PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ) :
    plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ
        ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm
          (tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
            (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) (e w)))) v ∈
      plusMackeyFilt Q Λ Λc j hj θ ν₀ γ N hQ
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀))
        (Multiset.card (stendhalWeight 2 ν₀)) := by
  rw [← castLabels_affineToTensor_windowAffine]
  change blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ _ hQ
    ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
      (θ + (ν₀ + γ))).symm (castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
        (plusLabels Λ Λc j hj) (θ + (ν₀ + γ))
          (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
            (windowAffine j hj Q Λ Λc θ γ ν₀ s (e w))))) v ∈ _
  have he := AlgEquiv.symm_apply_apply (castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
    (plusLabels Λ Λc j hj) (θ + (ν₀ + γ))) (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ
      (ν₀ + γ) (windowAffine j hj Q Λ Λc θ γ ν₀ s (e w)))
  rw [he, windowAffine_e]
  have hpM : midPos j s + Multiset.card (stendhalWeight 2 ν₀) ≤ Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) := by
    rw [card_windowLoading_weight (hj := hj), card_plus j hj, Multiset.card_map]
    have := midPos_le j s
    omega
  exact cutStandardAction_e_mem_of_black hQ hsym _ hpM
    (fun x hx hmem => windowLoading_black s w hs x hx hmem) v

omit [DecidableEq I] in
include hj in
theorem midPos_add_le_card (s : Seq (stendhalWeight ℓ (θ + γ))) :
    midPos j s + Multiset.card (stendhalWeight 2 ν₀) ≤ Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) := by
  rw [card_windowLoading_weight (hj := hj), card_plus j hj, Multiset.card_map]
  have := midPos_le j s
  omega

variable (j hj) in
/-- The colours of the strands at the maximum in the three blocks of `λ⁺`. -/
abbrev windowColour : I ⊕ Fin 2 → I ⊕ Fin (j + (2 + (ℓ - j))) :=
  Sum.map id (Fin.cast (plusBlock_card j hj).symm) ∘ cupColour j hj

omit [DecidableEq I] in
/-- **The labels of the window** of `windowLoading s w` are the strands at the maximum. -/
theorem windowWt_windowLoading (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) :
    windowWt (midPos j s) (Multiset.card (stendhalWeight 2 ν₀)) (windowLoading j hj θ γ ν₀ s w)
        (midPos_add_le_card (hj := hj) s) = (stendhalWeight 2 ν₀).map (windowColour j hj) := by
  conv_rhs => rw [← w.2, Multiset.map_map]
  rw [windowWt]
  refine Multiset.map_congr rfl fun b _ => ?_
  have hy : midPos j s + b.val < Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
    have := midPos_add_le_card (ν₀ := ν₀) (hj := hj) s
    rw [card_windowLoading_weight (hj := hj)] at this
    have := b.2; omega
  rw [windowLoading_lbl (hj := hj) s w _ ⟨midPos j s + b.val, hy⟩ rfl,
    insertSeq_lbl_win s (midPos_le j s) _ (Fin.cast (Multiset.card_map (cupColour j hj) _).symm b)
      rfl, Seq.map_lbl]
  rfl

include hQ in
/-- **The top layer on a window loading**: on the `N`-th layer of the induced model of `S_+`
for the top cut at the end `p + N` of the window, `ι_s(e(w))` lands in the span of the images of
the maps `Ξ_λ` of the Mackey data `λ` whose weight is that of the strands at the maximum. -/
theorem indMackeyLayerAct_windowLoading_mem
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
        (_ : q.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj)), LinearMap.range
        (indMackeyLeftMap (Q := stendhalQ Q (plusBlockLabels Λ Λc j hj))
          (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
            (midPos_add_le_card (hj := hj) s)).symm
          (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
            (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ))
          q.1 q.2) := by
  exact indMackeyLayerAct_e_mem_of_black hsym (windowLoading j hj θ γ ν₀ s w)
    (midPos_add_le_card (hj := hj) s) (fun x hx hmem => windowLoading_black s w hs x hx hmem)
    _ (windowWt_windowLoading s w) y

/-- **The red-ordered window idempotent maps `S_+` into `F_N`**: `ι_s(1_{red-ordered})`, the
idempotent `e'_s` of the window at `s`, maps `S_+(X)` into the step `N = |window|` of the
head-strand filtration, for `s` as in `plusStandardAction_insertMap_e_mem`. -/
theorem plusStandardAction_insertMap_redOrdered_mem
    (hsym : KLRSymm (stendhalQ Q (plusBlockLabels Λ Λc j hj)))
    (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (v : PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ) :
    plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ
        ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm
          (tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
            (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s)
              (redOrderedKLR k Q Λc ν₀)))) v ∈
      plusMackeyFilt Q Λ Λc j hj θ ν₀ γ N hQ
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀))
        (Multiset.card (stendhalWeight 2 ν₀)) := by
  let φ : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
      (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) →+
        Module.End k (PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ) :=
    ((plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ).toRingHom.toAddMonoidHom.comp
      (castTensorProductAlgebra Q (plusLabels Λ Λc j hj)
        (plusWeight_eq θ γ ν₀)).symm.toRingEquiv.toRingHom.toAddMonoidHom).comp
      ((TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)).comp
        ((orderProjection Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)).comp
          (StendhalAlgebraAllOrders.ofKLR k Q (plusLabels Λ Λc j hj)
            ((θ + γ) + ν₀)))).toRingHom.toAddMonoidHom
  have key : ∀ w : Seq (stendhalWeight 2 ν₀),
      φ (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) (e w)) v ∈
        plusMackeyFilt Q Λ Λc j hj θ ν₀ γ N hQ
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀))
          (Multiset.card (stendhalWeight 2 ν₀)) :=
    fun w => plusStandardAction_insertMap_e_mem Q Λ Λc hQ hsym s w hs v
  rw [redOrderedKLR, insertMap_sum]
  change φ (∑ _ ∈ _, _) v ∈ _
  rw [map_sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun w _ => key w

end CupCap

end Categorification.Stendhal
