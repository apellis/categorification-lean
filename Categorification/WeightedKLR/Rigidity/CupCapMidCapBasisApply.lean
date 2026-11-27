/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCapBasis

/-!
# The elements of the basis `B″` for a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.17. The element of `midCapBasis` indexed by a triple
`τ` of `B″` and `b′ ∈ B′_t` is Webster's diagram: the cap generator with the maximum at its
canonical position `midPos j s` (just before the red strand `λ_{j+1}`) at the top of the loading
`s`, carrying `b′`, followed below by the diagram `γ_g = e(midSeq s t) x^d ψ_u e(bot)` of the
generator `g` of `τ`, in which every strand passes under the maximum (`midCapBasis_apply`).

## Main results

* `midModelBasis_apply`: the element `b′ γ_g` of the basis of the model.
* `midCapBasis_apply`: the element of index `(τ, b′)` is `capElt 1 s (midPos s) b′ γ_g`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

attribute [local instance 1200] Ring.toIntAlgebra

theorem _root_.DFinsupp.basis_apply' {R : Type*} [Semiring R] {η : Type*}
    {ι' : η → Type*} {M : η → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [DecidableEq η] (b : ∀ i, Module.Basis (ι' i) R (M i)) (x : Σ i, ι' i) :
    DFinsupp.basis b x = DFinsupp.single x.1 (b x.1 x.2) := by
  obtain ⟨i, y⟩ := x
  rw [Module.Basis.apply_eq_iff]
  simp [DFinsupp.basis]
  rw [Equiv.symm_apply_eq]
  exact (sigmaFinsuppEquivDFinsupp_single ⟨i, y⟩ (1 : R)).symm

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

theorem midModelEquiv_symm_single {L : Type*} [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    {ρ₂ : Equiv.Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
    {ρ₃ : Equiv.Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ₂ : ∀ b, IsReduced _ (ρ₂ b) ∧ wordProd _ (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced _ (ρ₃ w) ∧ wordProd _ (ρ₃ w) = w) (g : MidGen j hj ν ν₀)
    (n : BalancedTensor.idemPart ℤ L (midGenIdem (k := k) Q Λc g)) :
    (midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃).symm (DFinsupp.single g n) =
      Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (n : L) :=
  BalancedTensor.idemEquiv_symm_single _ _ _ g n

/-- **The elements of the basis of the model**: the element of index `(g, b′)` of
`midModelBasis` is `b′ γ_g`. -/
theorem midModelBasis_apply {L : Type*} [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [Module k L]
    [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [DecidableEq (MidGen j hj ν ν₀)]
    (hQ : KLRSymm Q)
    {ρ₂ : Equiv.Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
    {ρ₃ : Equiv.Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ₂ : ∀ b, IsReduced _ (ρ₂ b) ∧ wordProd _ (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced _ (ρ₃ w) ∧ wordProd _ (ρ₃ w) = w)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2))))
    (x : Σ g : MidGen j hj ν ν₀, ι ⟨g.t, g.ht⟩) :
    midModelBasis j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ B' x =
      Ind.tmul (midGenCorner Q Λ Λc ρ₃ x.1) ((B' ⟨x.1.t, x.1.ht⟩ x.2 : _) : L) := by
  rw [midModelBasis, Module.Basis.map_apply, DFinsupp.basis_apply']
  change (midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃).symm
    (DFinsupp.mapRange (fun g => (idemPartEquiv L (midGenIdem (k := k) Q Λc g)).symm)
      (fun _ => map_zero _) (DFinsupp.single x.1 (B' ⟨x.1.t, x.1.ht⟩ x.2))) = _
  rw [DFinsupp.mapRange_single, midModelEquiv_symm_single]
  rfl


/-- The diagram `γ_g` of a generator starts at the window idempotent of its top loading
`s = g.s`, so the window idempotents of the other loadings kill it. -/
theorem eSum_mul_midGenKLR {ρ₃ : Equiv.Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))))
      → List ℕ} (g : MidGen j hj ν ν₀) (s : Seq (stendhalWeight ℓ ν)) :
    KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s)) *
        midGenKLR Q Λ Λc ρ₃ g =
      if s = g.s then midGenKLR Q Λ Λc ρ₃ g else 0 := by
  have hmem : midSeq j hj g.s g.t ∈
      insertSet (j := j) (hj := hj) (ν₀ := ν₀) g.s (midPos j g.s) (midPos_le j g.s) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have he : (KLRAlgebra.e (midSeq j hj g.s g.t) :
      KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))) =
      KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) g.s (midPos j g.s) (midPos_le j g.s)) *
        KLRAlgebra.e (midSeq j hj g.s g.t) := by
    rw [KLRAlgebra.eSum_mul_e, ite_eq_left_of_eq_true _ _ (eq_true hmem)]
  have hΓ : midGenKLR Q Λ Λc ρ₃ g =
      KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) g.s (midPos j g.s) (midPos_le j g.s)) *
        midGenKLR Q Λ Λc ρ₃ g := by
    unfold midGenKLR
    conv_lhs => rw [he]
    simp only [mul_assoc]
  split_ifs with h
  · subst h
    exact hΓ.symm
  · rw [hΓ, ← mul_assoc, eSum_mid_mul_eSum_mid, ite_eq_right_of_eq_false _ _ (eq_false h), zero_mul]

/-- **The elements of the basis `B″`** (Webster, arXiv:1309.3796v3, Lemma 7.17, for a cap after
`λ_j`): the element of `midCapBasis` indexed by the triple of a generator `g = (s, t, d, u)` and
`b′ ∈ B′_t` is Webster's diagram `capElt 1 s (midPos j s) b′ γ_g`: the cap generator with the
maximum at its canonical position at the top of `s`, carrying `b′`, followed below by
`γ_g = e(midSeq s t) x^d ψ_u e(bot)`, in which every strand passes under the maximum. -/
theorem midCapBasis_apply {L : Type*} [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [Module k L]
    [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] [DecidableEq (MidGen j hj ν ν₀)]
    [Nontrivial k] (hQ : KLRSymm Q)
    {ρ₂ : Equiv.Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
    {ρ₃ : Equiv.Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ₂ : ∀ b, IsReduced _ (ρ₂ b) ∧ wordProd _ (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced _ (ρ₃ w) ∧ wordProd _ (ρ₃ w) = w)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2))))
    (x : Σ g : MidGen j hj ν ν₀, ι ⟨g.t, g.ht⟩) :
    midCapBasis hQ hρ₂ hρ₃ hκ hL hP hPL B' (midTripleIndexEquiv hL B' x) =
      capElt 1 x.1.s (midCPos j x.1.s) ((B' ⟨x.1.t, x.1.ht⟩ x.2 : _) : L)
        (midGenKLR Q Λ Λc ρ₃ x.1) := by
  rw [midCapBasis, Module.Basis.map_apply, midTripleBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply, midModelBasis_apply]
  change midModelToCapAdd j hj Q Λ Λc ν ν₀ L
    (Ind.tmul (midGenCorner Q Λ Λc ρ₃ x.1) ((B' ⟨x.1.t, x.1.ht⟩ x.2 : _) : L)) = _
  rw [midModelToCapAdd_tmul]
  change midInvFun j hj Q Λ Λc ν ν₀ (midGenElt Q Λ Λc ρ₃ x.1) _ = _
  rw [midInvFun, midGenElt]
  simp_rw [smul_midGenCap, capElt_mid_eSum 1 _ _ (midGenKLR Q Λ Λc ρ₃ x.1),
    eSum_mul_midGenKLR]
  rw [Finset.sum_eq_single x.1.s (fun s _ h => by
      rw [ite_eq_right_of_eq_false _ _ (eq_false h), capElt_zero_right]) (by simp)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl
