/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyWindow
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutData
import Categorification.WeightedKLR.Rigidity.CupCapMidDescent

/-!
# Claim A at the cut: the window preserves the head-strand filtration

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, at the cut at the `j`-th red
strand. For a loading `s` of `λ`, the window of the cap generators at `s` occupies the positions
`[p, p + N)`, with `p = midPos s` and `N` the number of strands at the maximum. The filtration of
`S_+(X)` by the head strands passing the end of the window is the Mackey filtration of the outer
cut at `p + N` (`plusMackeyFilt`). Every diagram `ι_s(x)` on the window, acting on `S_+(X)`
through `T^{λ⁺}`, preserves each of its steps (`plusMackeyFilt_insertMap`): this is Claim A of
the filtration for the action of the window algebra.

The proof transports the statement for the affine KLR algebra (`plusMackeyFilt_action`,
`preservesMackeyFilt_blockEmb`) along the reindexing of the red labels and the equalities of
black weights, all of which preserve positions.

## Main results

* `Stendhal.CupCap.plusMackeyFilt_insertMap`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

section Casts

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The KLR algebra of the strands of `λ` with the red labels reindexed along `Fin.cast`. -/
def castLabelsKLR {n n' : ℕ} (h : n = n') (Λ : Fin n' → I →₀ ℕ) (ν : Multiset I) :
    KLRAlgebra k (stendhalQ Q (Λ ∘ Fin.cast h)) (stendhalWeight n ν) ≃ₐ[k]
      KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight n' ν) := by
  subst h
  exact AlgEquiv.refl

theorem castLabelsTensorProductAlgebra_tensorOfKLR {n n' : ℕ} (h : n = n')
    (Λ : Fin n' → I →₀ ℕ) (ν : Multiset I)
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ Fin.cast h)) (stendhalWeight n ν)) :
    castLabelsTensorProductAlgebra Q h Λ ν (tensorOfKLR Q (Λ ∘ Fin.cast h) ν z) =
      tensorOfKLR Q Λ ν (castLabelsKLR Q h Λ ν z) := by
  subst h
  rfl

theorem preservesMackeyFilt_castLabelsKLR_iff {n n' : ℕ} (h : n = n') (Λ : Fin n' → I →₀ ℕ)
    (ν : Multiset I) (a b : ℕ)
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ Fin.cast h)) (stendhalWeight n ν)) :
    PreservesMackeyFilt a b (castLabelsKLR Q h Λ ν z) ↔ PreservesMackeyFilt a b z := by
  subst h
  rfl

theorem preservesMackeyFilt_castKLR_iff {J : Type*} [DecidableEq J]
    {P : J → J → MvPolynomial (Fin 2) k} {μ μ' : Multiset J} (h : μ = μ') (a b : ℕ)
    (z : KLRAlgebra k P μ) :
    PreservesMackeyFilt a b (castKLR P h z) ↔ PreservesMackeyFilt a b z := by
  subst h
  rfl

theorem preservesMackeyFilt_castLabelsKLR_symm_iff {n n' : ℕ} (h : n = n')
    (Λ : Fin n' → I →₀ ℕ) (ν : Multiset I) (a b : ℕ)
    (z : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight n' ν)) :
    PreservesMackeyFilt a b ((castLabelsKLR Q h Λ ν).symm z) ↔ PreservesMackeyFilt a b z := by
  subst h
  rfl

theorem preservesMackeyFilt_castKLR_symm_iff {J : Type*} [DecidableEq J]
    {P : J → J → MvPolynomial (Fin 2) k} {μ μ' : Multiset J} (h : μ = μ') (a b : ℕ)
    (z : KLRAlgebra k P μ') :
    PreservesMackeyFilt a b ((castKLR P h).symm z) ↔ PreservesMackeyFilt a b z := by
  subst h
  rfl

theorem castTensorProductAlgebra_symm_apply {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {ν ν' : Multiset I}
    (h : ν = ν') (t : TensorProductAlgebra k Q Λ ν') :
    (castTensorProductAlgebra Q Λ h).symm t = castTensorProductAlgebra Q Λ h.symm t := by
  subst h
  rfl

end Casts

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I) (hQ : KLRSymm Q)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]

/-- The window `ι_s(x)` as an affine element of the three blocks of `λ⁺`. -/
def windowAffine (s : Seq (stendhalWeight ℓ (θ + γ)))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    KLRAlgebra k (stendhalQ Q (plusBlockLabels Λ Λc j hj))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) :=
  (castKLR _ (cutInputWeights_add θ (ν₀ + γ))).symm
    ((castLabelsKLR Q (plusBlock_card j hj) (plusLabels Λ Λc j hj) (θ + (ν₀ + γ))).symm
      (castKLR _ (congrArg (stendhalWeight (ℓ + 2)) (plusWeight_eq θ γ ν₀).symm)
        (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) x)))

theorem castLabels_affineToTensor_windowAffine (s : Seq (stendhalWeight ℓ (θ + γ)))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj) (θ + (ν₀ + γ))
        (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
          (windowAffine j hj Q Λ Λc θ γ ν₀ s x)) =
      (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm
        (tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
          (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) x)) := by
  rw [castTensorProductAlgebra_symm_apply, castTensorProductAlgebra_mk]
  change castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
      (θ + (ν₀ + γ)) (tensorOfKLR Q (plusBlockLabels Λ Λc j hj) (θ + (ν₀ + γ))
        (castKLR _ (cutInputWeights_add θ (ν₀ + γ)) (windowAffine j hj Q Λ Λc θ γ ν₀ s x))) = _
  refine (castLabelsTensorProductAlgebra_tensorOfKLR Q (plusBlock_card j hj)
    (plusLabels Λ Λc j hj) _ _).trans ?_
  exact congrArg (tensorOfKLR Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
    ((congrArg (castLabelsKLR Q (plusBlock_card j hj) (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
      (AlgEquiv.apply_symm_apply _ _)).trans (AlgEquiv.apply_symm_apply _ _))

theorem preservesMackeyFilt_windowAffine (s : Seq (stendhalWeight ℓ (θ + γ)))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) (n'' : ℕ) :
    PreservesMackeyFilt (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) n''
      (windowAffine j hj Q Λ Λc θ γ ν₀ s x) := by
  have hw := preservesMackeyFilt_blockEmb (n'' := n'') (insertEmb (j := j) (hj := hj)
    (ν₀ := ν₀) s (midPos j s) (midPos_le j s)) (Or.inl (by rw [Multiset.card_map]))
    (relabelHom (cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc) x)
  exact (preservesMackeyFilt_castKLR_symm_iff _ _ _ _).2
    ((preservesMackeyFilt_castLabelsKLR_symm_iff Q _ _ _ _ _ _).2
      ((preservesMackeyFilt_castKLR_iff _ _ _ _).2 hw))

/-- **Claim A at the cut** (Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19): a diagram
`ι_s(x)` on the window of the cap generators at `s`, acting on `S_+(N)` through `T^{λ⁺}`,
preserves every step of the filtration by the head strands passing the end `midPos s + N` of
the window. -/
theorem plusMackeyFilt_insertMap (s : Seq (stendhalWeight ℓ (θ + γ)))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) {c : ℕ}
    {v : PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ}
    (hv : v ∈ plusMackeyFilt Q Λ Λc j hj θ ν₀ γ N hQ
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c) :
    plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ
        ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm
          (tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
            (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) x))) v ∈
      plusMackeyFilt Q Λ Λc j hj θ ν₀ γ N hQ
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c := by
  rw [← castLabels_affineToTensor_windowAffine]
  exact plusMackeyFilt_action Q Λ Λc j hj θ ν₀ γ N hQ
    (preservesMackeyFilt_windowAffine j hj Q Λ Λc θ γ ν₀ s x _) hv

end CupCap

end Categorification.Stendhal
