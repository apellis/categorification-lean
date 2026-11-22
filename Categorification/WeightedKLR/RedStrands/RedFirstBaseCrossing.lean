/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstReach
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

set_option backward.isDefEq.respectTransparency false

/-!
# The base crossing of Lemma 5.23

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Lemma 5.23,
one red and one black strand. The diagram `G` of `redCross_eq_zero` moves the last red strand
left across the last black strand: `e(s, i, λ_ℓ) G = e(s, i, λ_ℓ) G e(s, λ_ℓ, i)`
(`e_mul_firstG`), so it is a crossing from the loading `(s, i, λ_ℓ)` to `(s, λ_ℓ, i)`. At the
standard Khovanov–Lauda parameters right multiplication by it is injective, which gives the
input `BaseCrossing` of `exists_mul_redFirstIdem_ne_zero`.

## Main results

* `e_mul_firstG`: `e(w) G = G e(d w)` in the KLR algebra.
* `baseCrossing_std`: the base crossing at the standard parameters.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong TypeA Equiv

section KLRPart

variable {J : Type*} [DecidableEq J] {k : Type*} [CommRing k] {P : J → J → MvPolynomial (Fin 2) k}

/-- **The idempotents through `G`**: `e(w) G = G e(d w)`, `d` the Mackey permutation. -/
theorem e_mul_firstG (ν₀ ν' : Multiset J) (j : J) (w : Seq (ν₀ + ν' + {j})) :
    (e w * firstG P ν₀ ν' j : KLRAlgebra k P (ν₀ + ν' + {j})) =
      firstG P ν₀ ν' j * e (quadPerm (firstQuad_h ν₀ ν' j) (firstQuad ν₀ ν' j) • w) := by
  have hc : ∀ (T : Finset (Seq (ν₀ + ν' + {j}))) (s : Seq (ν₀ + ν' + {j})),
      (e s * eSum P T : KLRAlgebra k P _) = eSum P T * e s := fun T s => by
    rw [e_mul_eSum, eSum_mul_e]
  unfold firstG firstψ botOne oneConcat
  rw [hflip_ψw, ← mul_assoc, ← mul_assoc, hc, mul_assoc (eSum _ _) (e w), e_mul_ψw,
    wordProd_reverse, wordProd_canWord, inv_inv]
  simp only [mul_assoc]
  rw [hc]

end KLRPart

section Loadings

variable {I : Type} {ℓ : ℕ}

theorem appendRedLoading_lbl_of_lt {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)))
    (ha : a.val < Multiset.card (stendhalWeight ℓ ν)) :
    (appendRedLoading s).lbl a = addRedColor ℓ (s.lbl ⟨a.val, ha⟩) := by
  have h := appendRedLoading_lbl s ⟨a.val, ha⟩
  rwa [show appendRedPosition ⟨a.val, ha⟩ = a from Fin.ext rfl] at h

theorem appendRedLoading_lbl_of_eq {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)))
    (ha : a.val = Multiset.card (stendhalWeight ℓ ν)) :
    (appendRedLoading s).lbl a = .inr (Fin.last ℓ) := by
  change ((Seq.map (addRedColor ℓ) s).append (singletonRedSeq ℓ)).1 (Fin.cast _ a) = _
  rw [Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast, Multiset.card_map]; omega)]
  exact singletonRedSeq_lbl _

end Loadings

section Base

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)
  (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s)

theorem castTensorProductAlgebra_cast_symm {m : ℕ} (Λ' : Fin m → I →₀ ℕ) {ν ν' : Multiset I}
    (h : ν = ν') (x : TensorProductAlgebra k Q Λ' ν') :
    castTensorProductAlgebra Q Λ' h (castTensorProductAlgebra Q Λ' h.symm x) = x := by
  subst h; rfl

theorem redCrossIdem_eq :
    redCrossIdem Q Λ i θ s hs = redLoadingIdem Q Λ ({i} + (θ + 0))
      (appendRedLoading (appendBlackLoading i (θ + 0) s))
      ((appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered i (θ + 0) s hs)) := by
  have h := appendBlackOld_emptyFactorToOld Q Λ i θ
    ((emptyFactorToOld Q Λ θ).symm (oldIdem Q Λ θ s hs))
  rw [AlgEquiv.apply_symm_apply] at h
  change appendBlack Q (Λ ∘ Fin.castSucc) i (θ + 0) (oldIdem Q Λ θ s hs) =
    castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (firstInd_blackWeight i θ 0).symm _ at h
  rw [appendBlack_mk_e] at h
  have h' := congrArg (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc)
    (firstInd_blackWeight i θ 0)) h
  rw [castTensorProductAlgebra_cast_symm] at h'
  have h'' : emptyFactorToOld Q Λ ({i} + θ)
      (leftAppendHom Q Λ i θ 0 ((emptyFactorToOld Q Λ θ).symm (oldIdem Q Λ θ s hs))) =
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (firstInd_blackWeight i θ 0)
        (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) ({i} + (θ + 0))
          (StendhalAlgebra.e (appendBlackLoading i (θ + 0) s)
            (appendBlackLoading_ordered i (θ + 0) s hs))) := h'.symm
  unfold redCrossIdem redFactorHom
  rw [emptyRedHom_apply]
  simp only [h'']
  rw [appendRed_castTensorProductAlgebra, castTensorProductAlgebra_symm',
    castTensorProductAlgebra_cast_symm]
  exact appendRed_mk_e Q Λ _ _ _

local notation "S" => stendhalQ Q Λ
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 (0 : Multiset I))

/-- `affT` sends the idempotent of a loading to the idempotent of the cast loading. -/
theorem firstIndAffine_e_cast (β : Multiset I) (t : Seq (stendhalWeight (ℓ + 1) ({i} + (θ + β))))
    (ht : IsRedOrdered t) :
    firstIndAffine Q Λ i θ β (e (Seq.cast (firstInd_klrWeight i θ β).symm t)) =
      redLoadingIdem Q Λ _ t ht := by
  rw [firstIndAffine_apply, castKLR_e, Seq.cast_cast_symm, tensorOfKLR_e_of_ordered _ _ ht]

omit [DecidableEq I] in
theorem card_stendhalWeight_addRed_base (ν : Multiset I) :
    Multiset.card (stendhalWeight (ℓ + 1) ν) = Multiset.card (stendhalWeight ℓ ν) + 1 := by
  rw [← stendhalWeight_addRed]
  simp [stendhalWeight]

omit [DecidableEq I] in
/-- The double coset representative of the first factor exchanges the last red strand with
the black strand `i`. -/
theorem cast_quadPerm_smul_base :
    Seq.cast (firstInd_klrWeight i θ 0)
      (quadPerm (firstQuad_h Aₚ Aₗ (Sum.inl i)) (firstQuad Aₚ Aₗ (Sum.inl i)) •
        Seq.cast (firstInd_klrWeight i θ 0).symm
          (appendRedLoading (appendBlackLoading i (θ + 0) s))) =
      appendBlackLoading i (θ + 0) (appendRedLoading s) := by
  have hA : Multiset.card (stendhalWeight ℓ (θ + 0)) = Multiset.card (Aₚ) := by simp
  have hB := card_stendhalWeight_addBlack_reach (ℓ := ℓ) i (θ + 0)
  have hR1 := card_stendhalWeight_addRed_base (ℓ := ℓ) ({i} + (θ + 0))
  have hR0 := card_stendhalWeight_addRed_base (ℓ := ℓ) (θ + 0)
  have hl : Multiset.card (Aₗ) = 1 := by simp [stendhalWeight]
  apply Subtype.ext
  funext q
  rw [Seq.cast_apply, Seq.smul_apply, Seq.cast_apply]
  set d := quadPerm (firstQuad_h Aₚ Aₗ (Sum.inl i)) (firstQuad Aₚ Aₗ (Sum.inl i))
  set p := d.symm (Fin.cast (congrArg Multiset.card (firstInd_klrWeight i θ 0)).symm q) with hpd
  have hp : (d p).val = q.val := by rw [hpd, Equiv.apply_symm_apply]; rfl
  rw [quadPerm_val] at hp
  simp only [Multiset.card_add, Multiset.card_singleton, hl] at hp
  have hq := q.isLt
  change (appendRedLoading (appendBlackLoading i (θ + 0) s)).lbl (Fin.cast _ p) =
    (appendBlackLoading i (θ + 0) (appendRedLoading s)).lbl q
  rcases lt_trichotomy q.val (Multiset.card (stendhalWeight ℓ (θ + 0))) with h | h | h
  · have hpv : p.val = q.val := by split_ifs at hp <;> omega
    rw [appendRedLoading_lbl_of_lt _ _ (by simp only [Fin.val_cast]; omega),
      appendBlackLoading_lbl_of_lt _ _ _ _ (by simp only [Fin.val_cast]; omega),
      appendBlackLoading_lbl_of_lt _ _ _ _ (by omega),
      appendRedLoading_lbl_of_lt _ _ (by omega)]
    simp only [Fin.val_cast, hpv]
  · have hpv : p.val = q.val + 1 := by split_ifs at hp <;> omega
    rw [appendRedLoading_lbl_of_eq _ _ (by simp only [Fin.val_cast]; omega),
      appendBlackLoading_lbl_of_lt _ _ _ _ (by omega),
      appendRedLoading_lbl_of_eq _ _ (by simp only; omega)]
  · have hpv : p.val = q.val - 1 := by split_ifs at hp <;> omega
    rw [appendRedLoading_lbl_of_lt _ _ (by simp only [Fin.val_cast]; omega),
      appendBlackLoading_lbl_of_eq _ _ _ _ (by simp only [Fin.val_cast]; omega),
      appendBlackLoading_lbl_of_eq _ _ _ _ (by omega)]
    rfl

end Base

section Std

open KL3.Diagram

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

include hR hQs in
/-- **The base crossing of Lemma 5.23** (Webster, arXiv:1309.3796v2, proof of Lemma 5.23):
pulling the last red strand left across one black strand, `(s, i, λ_ℓ) ⟶ (s, λ_ℓ, i)`. -/
theorem crossPair_base_std {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)
    (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    CrossPair QL Λ ({i} + (θ + 0)) (appendRedLoading (appendBlackLoading i (θ + 0) s))
      (appendBlackLoading i (θ + 0) (appendRedLoading s)) := by
  have hsrc : IsRedOrdered (appendRedLoading (appendBlackLoading i (θ + 0) s)) :=
    (appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered i (θ + 0) s hs)
  have htgt : IsRedOrdered (appendBlackLoading i (θ + 0) (appendRedLoading s)) :=
    appendBlackLoading_ordered i (θ + 0) _ ((appendRedLoading_ordered_iff _).2 hs)
  set G := firstG (stendhalQ QL Λ) (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
    (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
      (stendhalWeight 1 (0 : Multiset I))) (Sum.inl i : I ⊕ Fin (ℓ + 1)) with hG
  refine ⟨hsrc, htgt, redLoadingIdem QL Λ _ _ hsrc * firstIndAffine QL Λ i θ 0 G, ?_, ?_⟩
  · intro x hx h0
    have := finiteDimensional_redFactorModule _ hR Λ θ s hs
    refine redCross_eq_zero _ Λ i θ s hs hQs (firstIndDeltaInjective_std hR hQs i θ 0 _) x ?_ ?_
    · rw [redCrossIdem_eq]
      exact hx
    · calc x * firstIndAffine QL Λ i θ 0 G
          = x * redLoadingIdem QL Λ _ _ hsrc * firstIndAffine QL Λ i θ 0 G := by rw [hx]
        _ = 0 := by rw [mul_assoc]; exact h0
  · have hdw := congrArg (Seq.cast (firstInd_klrWeight i θ 0).symm)
      (cast_quadPerm_smul_base i θ s)
    rw [Seq.cast_symm_cast] at hdw
    rw [← firstIndAffine_e_cast QL Λ i θ 0 _ hsrc, ← map_mul, e_mul_firstG, hdw,
      ← firstIndAffine_e_cast QL Λ i θ 0 _ htgt, ← map_mul, mul_assoc, e_mul_self]

include hR hQs in
/-- The base crossing at the standard Khovanov–Lauda parameters. -/
theorem baseCrossing_std : BaseCrossing QL := by
  intro ℓ Λ i β u hu
  have key : ∀ (u : Seq (stendhalWeight ℓ (β + 0))), IsRedOrdered u →
      CrossPair QL Λ ({i} + (β + 0)) (appendRedLoading (appendBlackLoading i (β + 0) u))
        (appendBlackLoading i (β + 0) (appendRedLoading u)) :=
    fun u hu => crossPair_base_std hR hQs Λ i β u hu
  rw [add_zero] at key
  exact key u hu

end Std

end Categorification.Stendhal
