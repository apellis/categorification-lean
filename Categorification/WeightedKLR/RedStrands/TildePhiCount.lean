/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeGradedCount
import Categorification.WeightedKLR.RedStrands.PrependRedAssignments
import Categorification.WeightedKLR.RedStrands.BlockInsertLoading
import Categorification.KLR.GradedBasis

/-!
# The graded dimension identity for `T̃^λ e(s)`, indexed by the block assignments of `s`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Corollary 5.23 for `T̃^λ`, the count in a fixed degree. The identity
`finrank_tilde_lIdeal_grade_eq_sum` runs over the block assignments of `λ₀ s`; here it is
reindexed by those of `s`. A block assignment `g` of `s` extends to one of `λ₀ s`
(`extPhiIndex`) whose bottom is `λ₀` followed by the bottom of `g`
(`phiBottom_extAssign`) and whose `x_φ` has the degree of the old one
(`degW_phiPerm_extAssign`); the other assignments of `λ₀ s` contribute zero. So

`dim (T̃^λ e(s))_n = ∑_{φ ∈ Φ(s)} dim (S̃_{φ • s})_{n - deg x_φ}`

(`finrank_tilde_lIdeal_grade_eq_sum_phiIndex`). Route hypothesis: `AllFiniteDeltaInjective`,
inherited from `phiLayerEquiv`.

## Main definitions

* `extPhiIndex`: the extension of a block assignment of `s` to `λ₀ s`.

## Main results

* `phiBottom_extAssign`, `degW_phiPerm_extAssign`, `exists_extPhiIndex_of_prepend`.
* `finrank_tilde_lIdeal_grade_eq_sum_phiIndex`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR DirectSum _root_.Categorification.Graded _root_.Module TypeA Equiv

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Combinatorics

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

theorem card_stendhalWeight_succ :
    Multiset.card (stendhalWeight (ℓ + 1) ν) = Multiset.card (stendhalWeight ℓ ν) + 1 := by
  simp [stendhalWeight]
  omega

theorem prependRedLoading_lbl_zero (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) (ha : a.val = 0) :
    (prependRedLoading s).lbl a = .inr 0 := by
  rw [show a = firstPosition ℓ ν from Fin.ext ha, prependRedLoading_head]

theorem prependRedLoading_lbl_succ (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)))
    (p : Fin (Multiset.card (stendhalWeight ℓ ν))) (ha : a.val = p.val + 1) :
    (prependRedLoading s).lbl a = prependRedColor ℓ (s.lbl p) := by
  rw [show a = prependRedPosition p from Fin.ext (by simp [ha]), prependRedLoading_lbl]

/-- The extension of a block assignment of `s` to `λ₀ s`. -/
def extPhiIndex (s : Seq (stendhalWeight ℓ ν)) (g : PhiIndex s) :
    PhiIndex (prependRedLoading s) :=
  ⟨extAssign card_stendhalWeight_succ g.1, List.mem_toFinset.2 (extAssign_mem
    card_stendhalWeight_succ (prependRedLoading_lbl_zero s) (prependRedLoading_lbl_succ s)
    g.mem)⟩

theorem extPhiIndex_injective (s : Seq (stendhalWeight ℓ ν)) :
    Function.Injective (extPhiIndex s) := fun _ _ h =>
  Subtype.ext (extAssign_injective card_stendhalWeight_succ (congrArg Subtype.val h))

/-- **The bottom of an extended assignment** is `λ₀` added to the old bottom. -/
theorem phiBottom_extAssign (s : Seq (stendhalWeight ℓ ν)) (g : PhiIndex s) :
    phiBottom (prependRedLoading s) (extPhiIndex s g).1 = prependRedLoading (phiBottom s g.1) := by
  apply seq_ext_ofFn'
  rw [ofFn_phiBottom (extPhiIndex s g).mem, extPhiIndex,
    assignWord_extAssign card_stendhalWeight_succ (prependRedLoading_lbl_zero s)
      (prependRedLoading_lbl_succ s),
    ofFn_eq_cons_map_prependRedColor card_stendhalWeight_succ
      (prependRedLoading_lbl_zero (phiBottom s g.1)) (prependRedLoading_lbl_succ (phiBottom s g.1)),
    ofFn_phiBottom g.mem]

/-- **The assignments of `λ₀ s` with bottom of the form `λ₀ t`** are the extended ones. -/
theorem exists_extPhiIndex_of_prepend (s : Seq (stendhalWeight ℓ ν))
    (g' : PhiIndex (prependRedLoading s))
    (h : ∃ t, prependRedLoading t = phiBottom (prependRedLoading s) g'.1) :
    ∃ g, extPhiIndex s g = g' := by
  obtain ⟨t, ht⟩ := h
  have hhead : (assignWord (prependRedLoading s).lbl g'.1).head? = .some (.inr 0) := by
    rw [← ofFn_phiBottom g'.mem, ← ht,
      ofFn_eq_cons_map_prependRedColor card_stendhalWeight_succ
        (prependRedLoading_lbl_zero t) (prependRedLoading_lbl_succ t)]
    rfl
  obtain ⟨g, hg, hgg⟩ := exists_extAssign_of_head_eq card_stendhalWeight_succ
    (prependRedLoading_lbl_zero s) (prependRedLoading_lbl_succ s) g'.mem hhead
  exact ⟨⟨g, List.mem_toFinset.2 hg⟩, Subtype.ext hgg⟩

end Combinatorics

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "G₀" => restrictFirstRedGrading Q Λ G

omit [DecidableEq I] in
/-- **The degree of `x_φ` is unchanged by the extension**: computed with reduced words for
`λ₀ s` and for `s`, it is the same. -/
theorem degW_phiPerm_extAssign
    {ρ : Perm (Fin (Multiset.card μ')) → List ℕ}
    (hρ : ∀ w : Perm (Fin (Multiset.card μ')),
      TypeA.IsReduced (Multiset.card μ') (ρ w) ∧ TypeA.wordProd (Multiset.card μ') (ρ w) = w)
    {ρ₀ : Perm (Fin (Multiset.card μ)) → List ℕ}
    (hρ₀ : ∀ w : Perm (Fin (Multiset.card μ)),
      TypeA.IsReduced (Multiset.card μ) (ρ₀ w) ∧ TypeA.wordProd (Multiset.card μ) (ρ₀ w) = w)
    (s : Seq μ) (g : PhiIndex s) :
    G.degW (ρ (phiPerm (prependRedLoading s) (extPhiIndex s g).1)) (prependRedLoading s) =
      GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s := by
  rw [G.degW_eq_sum_invSet (hρ _).1, GradingDatum.degW_eq_sum_invSet G₀ (hρ₀ _).1, (hρ _).2,
    (hρ₀ _).2]
  exact sum_invSet_keyPerm_extAssign card_stendhalWeight_succ (prependRedLoading_lbl_zero s)
    (prependRedLoading_lbl_succ s) g.1 G.degΨ

private theorem tildeStdGradedRank_congr (G' : KLR.GradingDatum (stendhalQ Q (Λ ∘ Fin.succ)))
    {t₁ t₂ : Seq μ} (h : t₁ = t₂) (h₁ : IsRedOrdered t₁) (h₂ : IsRedOrdered t₂) (m : ℤ) :
    tildeStdGradedRank Q Λ ν G' t₁ h₁ m = tildeStdGradedRank Q Λ ν G' t₂ h₂ m := by
  subst h
  rfl

theorem tildeTerm_of_eq (G' : KLR.GradingDatum (stendhalQ Q (Λ ∘ Fin.succ))) {t : Seq μ}
    {t' : Seq μ'} (h : prependRedLoading t = t') (ht : IsRedOrdered t) (ht' : IsRedOrdered t')
    (m : ℤ) : tildeTerm Q Λ ν G' t' ht' m = tildeStdGradedRank Q Λ ν G' t ht m := by
  have he : ∃ t₀, prependRedLoading t₀ = t' := ⟨t, h⟩
  rw [tildeTerm]
  split_ifs
  exact tildeStdGradedRank_congr Q Λ ν G'
    (prependRedLoading_injective (he.choose_spec.trans h.symm)) _ _ m

theorem tildeTerm_of_not (G' : KLR.GradingDatum (stendhalQ Q (Λ ∘ Fin.succ))) {t' : Seq μ'}
    (h : ¬ ∃ t, prependRedLoading t = t') (ht' : IsRedOrdered t') (m : ℤ) :
    tildeTerm Q Λ ν G' t' ht' m = 0 := by
  rw [tildeTerm]
  split_ifs
  rfl

/-- **Graded dimension identity for `T̃^λ e(s)`, indexed by `Φ(s)`** (Webster,
arXiv:1309.3796v3, Corollary 5.23, the count in degree `n`). Under the hypotheses of
`finrank_tilde_lIdeal_grade_eq_sum`, `dim (T̃^λ e(s))_n` is the sum over the block assignments
`φ` of `s` of the degree-`(n - deg x_φ)` dimensions of the standard modules `S̃_{φ • s}` of
`T̃^λ`. Route hypothesis: `AllFiniteDeltaInjective`, inherited from `phiLayerEquiv`. -/
theorem finrank_tilde_lIdeal_grade_eq_sum_phiIndex {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ : Perm (Fin (Multiset.card μ')) → List ℕ)
    (hρ : ∀ w : Perm (Fin (Multiset.card μ')),
      TypeA.IsReduced (Multiset.card μ') (ρ w) ∧ TypeA.wordProd (Multiset.card μ') (ρ w) = w)
    (ρ₀ : Perm (Fin (Multiset.card μ)) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin (Multiset.card μ)),
      TypeA.IsReduced (Multiset.card μ) (ρ₀ w) ∧ TypeA.wordProd (Multiset.card μ) (ρ₀ w) = w)
    {c N n : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, N + 2 * c < Λ 0 i * G.degX (.inl i)) (s : Seq μ) (hs : IsRedOrdered s)
    (hnN : n ≤ N)
    (hN : ∀ g : PhiIndex (prependRedLoading s),
      n - G.degW (ρ (phiPerm (prependRedLoading s) g.1)) (prependRedLoading s) ≤ N) :
    finrank k ((lIdeal (StendhalAlgebra.e s hs)).restrictScalars k ⊓ stendhalGrade G₀ ν n :) =
      ∑ g : PhiIndex s, tildeStdGradedRank Q Λ ν G₀ (phiBottom s g.1) (g.isRedOrdered hs)
        (n - GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s) := by
  classical
  rw [finrank_tilde_lIdeal_grade_eq_sum Q Λ ν G hQ hR hall ρ hρ hc hΛ s hs hnN hN]
  have hs' := (prependRedLoading_ordered_iff s).2 hs
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (extPhiIndex s)))
    (fun g' _ hg' => tildeTerm_of_not Q Λ ν G₀ (fun h => hg' (by
      obtain ⟨g, hg⟩ := exists_extPhiIndex_of_prepend s g' h
      exact Finset.mem_image.2 ⟨g, Finset.mem_univ _, hg⟩)) _ _),
    Finset.sum_image fun g _ g' _ h => extPhiIndex_injective s h]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [degW_phiPerm_extAssign Q Λ ν G hρ hρ₀ s g]
  exact tildeTerm_of_eq Q Λ ν G₀ (phiBottom_extAssign s g).symm _ _ _

end Categorification.Stendhal
