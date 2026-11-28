/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutSrc

/-!
# The unit of the right side of Lemma 7.19 (K) at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the inverse `Ψ` of the comparison map sends
a cap generator to the unit `1 ⊗ (y ⊠ v)` of the partial standardization `S_+(Y ⊠ L')` of `λ⁺`,
acted on by the diagram below the cap. This file records how the diagrams of `λ⁺` act on that
unit: the juxtaposed affine diagrams of the three blocks act through `Y ⊠ L'`
(`kSrcUnit_isInd3InputHom`), and an idempotent `e(s)` of `λ⁺` selects the triple of loadings of
the blocks whose concatenation is `s` (`kSrc_e_smul_unit`).

## Main definitions

* `Stendhal.CupCap.kSrcOneStepRep`: the affine diagrams of all strands of `λ⁺` acting on the
  right side.
* `Stendhal.CupCap.kSrcUnit`: the unit `Y ⊠ L' → S_+(Y ⊠ L')`.
* `Stendhal.CupCap.plusCutSeq`: the loading of `λ⁺` with the loadings of the three blocks.

## Main results

* `Stendhal.CupCap.kSrcUnit_isInd3InputHom`: the unit intertwines the three blocks.
* `Stendhal.CupCap.kSrc_e_smul_unit`: an idempotent of `λ⁺` acts on the unit through the
  triples of loadings of the blocks.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Vanishing

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {ν' : Multiset I}

/-- **A violated idempotent vanishes in the tensor product algebra.** -/
theorem tensorOfKLR_e_of_isViolated {s : Seq (stendhalWeight ℓ' ν')} (hs : IsViolated s) :
    tensorOfKLR Q Λ' ν' (e s) = 0 := by
  by_cases ho : IsRedOrdered s
  · change TensorProductAlgebra.mk Q Λ' ν' (topMap k Q Λ' ν' (e s)) = 0
    rw [topMap_e_of_isRedOrdered
      s ho]
    rw [← map_zero (TensorProductAlgebra.mk Q Λ' ν')]
    exact (RingCon.eq _).2 (((StendhalAlgebra.violatedIdeal k Q Λ' ν').rel_iff _ 0).2
      (by rw [sub_zero]; exact TwoSidedIdeal.subset_span ⟨s, ho, hs, rfl⟩))
  · change TensorProductAlgebra.mk Q Λ' ν' (orderProjection Q Λ' ν'
      (StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' (e s))) = 0
    rw [orderProjection_e_of_not
      (Λ' := Λ') ho, map_zero]

/-- **An idempotent with red strands out of order vanishes in the tensor product algebra.** -/
theorem tensorOfKLR_e_of_not_isRedOrdered {s : Seq (stendhalWeight ℓ' ν')}
    (hs : ¬ IsRedOrdered s) : tensorOfKLR Q Λ' ν' (e s) = 0 := by
  change TensorProductAlgebra.mk Q Λ' ν' (orderProjection Q Λ' ν'
    (StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' (e s))) = 0
  rw [orderProjection_e_of_not
    (Λ' := Λ') hs, map_zero]

end Vanishing

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Xs" => KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)
set_option hygiene false in
local notation "Ap" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
    (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))
set_option hygiene false in
local notation "Mp" => Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))

/-- The action of `T^{λ⁺}(θ + (ν₀ + γ))` on the right side, through the weight cast. -/
def kSrcRep : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)) →ₐ[k]
    Module.End k Xs :=
  (Algebra.lsmul k k Xs).comp
    (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).toAlgHom

/-- **`T^{λ⁺}(θ + (ν₀ + γ))` acts on the right side by the action of the partial
standardization.** -/
theorem kSrcRep_apply (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
    (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kSrcRep j hj Q Λ Λc θ γ ν₀ Y hQ L' t (toKCutSrc u) =
      toKCutSrc (plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ t u) := by
  change castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) t •
    toKCutSrc u = _
  rw [smul_toKCutSrc]
  simp only [kCutSrcAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]

/-- The affine diagrams of all strands of `λ⁺` acting on the right side. -/
abbrev kSrcOneStepRep :=
  blocksOneStepRep Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
    (plusBlocksRep (ρ := kSrcRep j hj Q Λ Λc θ γ ν₀ Y hQ L'))

/-- **The affine diagrams of `λ⁺` act on the right side through `T^{λ⁺}`.** -/
theorem kSrcOneStepRep_apply (z : KLRAlgebra k Sp Ap) (X : Xs) :
    kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' z X =
      castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)
        (castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
          (θ + (ν₀ + γ)) (tensorOfKLR Q (plusLabels Λ Λc j hj ∘ Fin.cast (plusBlock_card j hj))
            (θ + (ν₀ + γ)) (castKLR _ (kCutOneStepWeight_eq j θ γ ν₀) z))) • X := by
  rw [blocksOneStepRep_apply, castKLR_symm_eq, cutAffineMap_apply, castKLR_castKLR]
  rfl

theorem kSrcOneStepRep_x (p : Fin (Multiset.card Ap)) (p' : Fin Mp) (hp : p'.val = p.val)
    (X : Xs) : kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (x p) X = mkp (botp (x p')) • X := by
  rw [kSrcOneStepRep_apply, castLabels_tensorOfKLR_x Q (plusBlock_card j hj)
    (kCutOneStepWeight_eq j θ γ ν₀) (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) p p' hp]
  rfl

theorem kSrcOneStepRep_ψ (p : ℕ) (X : Xs) :
    kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (ψ p) X = mkp (botp (ψ p)) • X := by
  rw [kSrcOneStepRep_apply, castLabels_tensorOfKLR_ψ Q (plusBlock_card j hj)
    (kCutOneStepWeight_eq j θ γ ν₀) (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) p]
  rfl

theorem kSrcOneStepRep_e (s : Seq Ap) (s' : Seq (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)))
    (hs : ∀ (p : Fin Mp) (q : Fin (Multiset.card Ap)),
      p.val = q.val → s'.lbl p = Sum.map id (Fin.cast (plusBlock_card j hj)) (s.lbl q))
    (X : Xs) : kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (e s) X = mkp (botp (e s')) • X := by
  rw [kSrcOneStepRep_apply, castLabels_tensorOfKLR_e Q (plusBlock_card j hj)
    (kCutOneStepWeight_eq j θ γ ν₀) (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) s s' hs]
  rfl

/-- **The unit of the right side**: `n ↦ 1 ⊗ n`. -/
def kSrcUnit : Np →ₗ[k] Xs :=
  blocksStandardUnit Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
    (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L')) hQ

theorem kSrcUnit_apply (n : MidSpect (k := k) Y L') :
    kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n = toKCutSrc (plusStandardUnit hQ n) := rfl

/-- The affine diagrams of all strands of the one-step model act on the right side through the
one-step model of the partial standardization. -/
theorem kSrcOneStepRep_oneStep (z : KLRAlgebra k Sp Ap)
    (y : Ind3 Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))) Np) :
    (blocksStandardOneStepEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
        (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L')) hQ).symm
        (Submodule.Quotient.mk (z • y)) =
      kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' z
        ((blocksStandardOneStepEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
          (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L')) hQ).symm
          (Submodule.Quotient.mk y)) := by
  obtain ⟨z, rfl⟩ := (castKLR Sp (blocksAllWeight_eq (I := I) (a := j) (m := 2) (r := ℓ - j)
    θ ν₀ γ)).surjective z
  refine (blocksStandardOneStepEquiv_symm_smul hQ z y).trans ?_
  refine Eq.trans ?_ (LinearMap.congr_fun (blocksOneStepRep_castKLR Q (plusBlockLabels Λ Λc j hj)
    θ ν₀ γ (plusBlocksRep (ρ := kSrcRep j hj Q Λ Λc θ γ ν₀ Y hQ L')) z) _).symm
  refine Eq.trans ?_ (kSrcRep_apply j hj Q Λ Λc θ γ ν₀ Y hQ L' _ _).symm
  exact congrArg (fun t => blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ _ hQ t _)
    (AlgEquiv.symm_apply_apply _ _).symm

/-- **The unit intertwines the three blocks**: the juxtaposed affine diagrams of the blocks of
`λ⁺` act on `1 ⊗ n` through `n`. -/
theorem kSrcUnit_isInd3InputHom :
    IsInd3InputHom (kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L')
      (kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  isInd3InputHom_comp_unit (g := (blocksStandardOneStepEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
    (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L')) hQ).symm.toLinearMap ∘ₗ
      Submodule.mkQ _) fun z y => kSrcOneStepRep_oneStep j hj Q Λ Λc θ γ ν₀ Y hQ L' z y

/-- The idempotent of the one-step model fixes the unit. -/
theorem kSrc_oneConcat3 (n : Np) :
    kSrcOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L' (oneConcat3 _ _ _ _)
      (kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n) = kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n := by
  rw [← kSrcUnit_isInd3InputHom, one_smul]

variable {j Λ θ γ ν₀} in
/-- **The loading of `λ⁺` with the loadings `i`, `w`, `l` of the three blocks**: the cap window
`w` inserted at the cut into the loading `i ⊔ l` of `λ`. -/
abbrev plusCutSeq (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) : Seq (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) :=
  insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (cutSeq hj i l) (cutPos j hj θ γ)
    (Nat.lt_succ_iff.1 (cutPos j hj θ γ).2) (Seq.map (cupColour j hj) w)

/-- The triple of idempotents of the blocks, as a juxtaposed diagram. -/
theorem plusEmb_e_tmul (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) :
    plusHeadEmb j hj Q Λ Λc θ (e i) ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ (e w) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (e l)) =
      e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) i) ⊗ₜ[k]
        (e (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)) ⊗ₜ[k]
        e (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Seq.map (Sum.map (id : I → I) (Fin.natAdd 2)) l))) := by
  simp only [plusHeadEmb, plusMidEmb, plusMidEmb₀, plusTailEmb, plusTailEmb₀,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, relabelEquiv_apply, relabelHom_e]
  rfl

/-- **The idempotent of the loading with given block loadings acts on the unit through the
blocks.** -/
theorem kSrc_e_plusCutSeq_smul_unit (i : Seq (stendhalWeight j θ))
    (w : Seq (stendhalWeight 2 ν₀)) (l : Seq (stendhalWeight (ℓ - j) γ)) (n : Np) :
    mkp (botp (e (plusCutSeq hj i w l))) • kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n =
      kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' ((plusHeadEmb j hj Q Λ Λc θ (e i) ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ (e w) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (e l))) • n) := by
  rw [kSrcUnit_isInd3InputHom, plusEmb_e_tmul, concat3_e_tmul_e_tmul_e]
  erw [kSrcOneStepRep_e j hj Q Λ Λc θ γ ν₀ Y hQ L' (plusSeq i w l) _
      (fun p q hpq => insertSeq_cutSeq_lbl hj i w l _ p q hpq)]

/-- **The unit is the sum of its parts at the loadings with given block loadings.** -/
theorem kSrcUnit_eq_sum (n : Np) :
    kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n =
      ∑ i : Seq (stendhalWeight j θ), ∑ w : Seq (stendhalWeight 2 ν₀),
        ∑ l : Seq (stendhalWeight (ℓ - j) γ),
          mkp (botp (e (plusCutSeq hj i w l))) • kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n := by
  conv_lhs => rw [← kSrc_oneConcat3, oneConcat3,
    one_eq_sum_e_tmul_e_tmul_e (plusHeadEmb j hj Q Λ Λc θ) (plusMidEmb j hj Q Λ Λc ν₀)
      (plusTailEmb j hj Q Λ Λc γ)]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [plusEmb_e_tmul, concat3_e_tmul_e_tmul_e]
  erw [kSrcOneStepRep_e j hj Q Λ Λc θ γ ν₀ Y hQ L' (plusSeq i w l) _
      (fun p q hpq => insertSeq_cutSeq_lbl hj i w l _ p q hpq)]

/-- **An idempotent of `λ⁺` acts on the unit through the block loadings it concatenates.** -/
theorem kSrc_e_smul_unit (s : Seq (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))) (n : Np) :
    mkp (botp (e s)) • kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' n =
      ∑ i : Seq (stendhalWeight j θ), ∑ w : Seq (stendhalWeight 2 ν₀),
        ∑ l : Seq (stendhalWeight (ℓ - j) γ),
          if s = plusCutSeq hj i w l then
            kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' ((plusHeadEmb j hj Q Λ Λc θ (e i) ⊗ₜ[k]
              (plusMidEmb j hj Q Λ Λc ν₀ (e w) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (e l))) • n)
          else 0 := by
  conv_lhs => rw [kSrcUnit_eq_sum]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, ← map_mul, ← map_mul, e_mul_e]
  split_ifs with h
  · rw [h, kSrc_e_plusCutSeq_smul_unit]
  · rw [map_zero, map_zero, zero_smul]

end Categorification.Stendhal.CupCap
