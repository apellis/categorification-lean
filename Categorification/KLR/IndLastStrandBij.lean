/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandQuot
import Categorification.TypeA.LastStrand

/-!
# The last strand of an induced module: the quotient map in shuffle coordinates

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, in the case where one strand coloured
`i` is restricted off the right of `Ind_{ν,ν'} N`, `ν = ν₀ + i`, `ν' = ν₀' + i`; the KLR input
of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5.

We choose reduced words for the shuffles of `(ν, ν')` adapted to the last strand: the canonical
word of `v` at the shuffles `v ⊕ 1` whose last strand comes from `ν'`, and the word
`d⁻¹ · (v ⊕ 1)` (with `d` the last-strand Mackey representative) at the shuffles whose last strand
comes from `ν`. In these coordinates `Ψ(ŵ_v^* ⊗ n) = [ŵ_{d⁻¹(v ⊕ 1)}^* ⊗ n]`.
-/

namespace Categorification.TypeA

open Equiv

/-- Canonical words of permutations of `Fin m` and `Fin m'`, `m = m'`, agreeing after
reindexing, are equal. -/
theorem canWord_congr {m m' : ℕ} (e : m = m') (d : Perm (Fin m)) (d' : Perm (Fin m'))
    (hd : ∀ p : Fin m, (d' (Fin.cast e p)).val = (d p).val) : canWord m' d' = canWord m d := by
  subst e
  congr 1
  ext p
  simpa using hd p

variable {n n' m m' : ℕ}

/-- The shuffles of `(n, n')` for two proofs `n + n' = m`, `n + n' = m'`. -/
def shuffleCongr (h : n + n' = m) (h' : n + n' = m') : Shuffle h ≃ Shuffle h' := by
  obtain rfl : m = m' := h.symm.trans h'
  exact Equiv.refl _

theorem canWord_shuffleCongr (h : n + n' = m) (h' : n + n' = m') (v : Shuffle h) :
    canWord m' (shuffleCongr h h' v).1 = canWord m v.1 := by
  obtain rfl : m = m' := h.symm.trans h'
  rfl

end Categorification.TypeA

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

section LastPerm

variable (ν₀ ν₀' : Multiset I) (i : I)

omit [DecidableEq I] in
theorem exists_lastPerm :
    ∃ d, IsDoubleShuffle (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))
      (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i)) d ∧
      crossCount (Multiset.card (ν₀ + Si i + ν₀')) (Multiset.card (ν₀ + Si i)) d =
        Multiset.card (ν₀' + Si i) := by
  refine (exists_isDoubleShuffle_iff _ _ _).2 ?_
  simp only [Multiset.card_add, Multiset.card_singleton]
  omega

/-- The minimal double coset representative `d` for `(S_{|ν + ν₀'|} × S_1) \ S / (S_ν × S_ν')`
moving the last strand of `ν` across `ν'`. -/
noncomputable def lastPerm : Perm (Fin (Multiset.card (ν₀ + Si i + (ν₀' + Si i)))) :=
  Classical.choose (exists_lastPerm ν₀ ν₀' i)

omit [DecidableEq I] in
theorem lastPerm_spec :
    IsDoubleShuffle (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))
      (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i)) (lastPerm ν₀ ν₀' i) ∧
      crossCount (Multiset.card (ν₀ + Si i + ν₀')) (Multiset.card (ν₀ + Si i))
        (lastPerm ν₀ ν₀' i) = Multiset.card (ν₀' + Si i) :=
  Classical.choose_spec (exists_lastPerm ν₀ ν₀' i)

omit [DecidableEq I] in
theorem lastTop_card : Multiset.card ν₀ + Multiset.card (ν₀' + Si i) =
    Multiset.card (ν₀ + Si i + ν₀') := by
  simp only [Multiset.card_add, Multiset.card_singleton]; omega

/-- The shuffles of `(ν, ν')`, sorted by the block of their last strand. -/
noncomputable def lastShuffles :
    Shuffle (Seq.card_add' (ν₀ + Si i) ν₀') ⊕ Shuffle (lastTop_card ν₀ ν₀' i) ≃
      Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i)) :=
  lastShuffleEquiv (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i))
    (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)) (Seq.card_add' (ν₀ + Si i) ν₀')
    (lastTop_card ν₀ ν₀' i) (lastPerm_spec ν₀ ν₀' i).1 (lastPerm_spec ν₀ ν₀' i).2

/-- The reduced words adapted to the last strand. -/
noncomputable def lastStrandWord (u : Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i))) :
    List ℕ :=
  Sum.elim (fun v => canWord _ v.1)
    (fun v => (canWord _ (lastPerm ν₀ ν₀' i)).reverse ++ canWord _ v.1)
    ((lastShuffles ν₀ ν₀' i).symm u)

omit [DecidableEq I] in
theorem lastStrandWord_spec (u : Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i))) :
    IsReduced (Multiset.card (ν₀ + Si i + (ν₀' + Si i))) (lastStrandWord ν₀ ν₀' i u) ∧
      wordProd (Multiset.card (ν₀ + Si i + (ν₀' + Si i))) (lastStrandWord ν₀ ν₀' i u) = u.1 := by
  obtain ⟨x, rfl⟩ := (lastShuffles ν₀ ν₀' i).surjective u
  rcases x with v | v
  · simp only [lastStrandWord, Equiv.symm_apply_apply, Sum.elim_inl]
    refine ⟨isReduced_canWord_ext (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))
      v.1, ?_⟩
    rw [wordProd_canWord_ext (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))]
    rfl
  · simp only [lastStrandWord, Equiv.symm_apply_apply, Sum.elim_inr]
    refine ⟨isReduced_topWord (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))
      (lastPerm_spec ν₀ ν₀' i).1.1 v.1, ?_⟩
    rw [wordProd_topWord (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))]
    rfl

omit [DecidableEq I] in
theorem lastStrandWord_ext (v : Shuffle (Seq.card_add' (ν₀ + Si i) ν₀')) :
    lastStrandWord ν₀ ν₀' i (extShuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + ({i} : Multiset I)))
      (card_add_singleton_eq (i := i)) (Seq.card_add' (ν₀ + Si i) ν₀') v) = canWord _ v.1 := by
  change lastStrandWord ν₀ ν₀' i (lastShuffles ν₀ ν₀' i (Sum.inl v)) = _
  simp only [lastStrandWord, Equiv.symm_apply_apply, Sum.elim_inl]

omit [DecidableEq I] in
theorem lastStrandWord_top (v : Shuffle (lastTop_card ν₀ ν₀' i)) :
    lastStrandWord ν₀ ν₀' i (lastShuffles ν₀ ν₀' i (Sum.inr v)) =
      (canWord _ (lastPerm ν₀ ν₀' i)).reverse ++ canWord _ v.1 := by
  simp only [lastStrandWord, Equiv.symm_apply_apply, Sum.elim_inr]

omit [DecidableEq I] in
/-- The Mackey crossing `ψ_d` of the last strand is `ψ` of the canonical word of `lastPerm`. -/
theorem canWord_quadPerm_lastQuad :
    canWord _ (quadPerm (lastQuad_h ν₀ ν₀' i) (lastQuad ν₀ ν₀' i)) =
      canWord _ (lastPerm ν₀ ν₀' i) := by
  refine canWord_congr (by simp only [Multiset.card_add]; omega) _ _ fun p => ?_
  rw [quadPerm_val, dval (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i))
    (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)) (lastTop_card ν₀ ν₀' i)
    (lastPerm_spec ν₀ ν₀' i).1 (lastPerm_spec ν₀ ν₀' i).2]
  have hp := p.isLt
  simp only [Multiset.card_add, Multiset.card_singleton, Fin.val_cast] at hp ⊢
  split_ifs <;> omega

end LastPerm

/-! ### `Ψ` on the shuffle basis -/

section ShuffleBasis

variable {ν₀ ν₀' : Multiset I} {i : I}

/-- The intertwining property of `ψ_d` on the idempotent `ι(1_{ν₀,ν'} ⊗ 1_i)`. -/
theorem appendR_castKLR_oneConcat_mul_lastψ :
    appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) (oneConcat Q ν₀ (ν₀' + Si i))) *
        lastψ Q ν₀ ν₀' i =
      lastψ Q ν₀ ν₀' i *
        botConcat Q (lastQuad_h ν₀ ν₀' i) (tensorAppendL Q ν₀ (ν₀' + Si i) i 1) := by
  have h := concat_quadTop_one_mul_ψD (Q := Q) (lastQuad_h ν₀ ν₀' i) (lastQuad ν₀ ν₀' i)
  rw [Algebra.TensorProduct.one_def (A := TensorKLR Q ν₀ (ν₀' + Si i)), quadTop_lastQuad,
    quadBot_lastQuad, concat_one, ← appendR_apply] at h
  exact h

/-- **`Ψ` on the shuffle basis, bimodule level**: `ι(ŵ_v^* ⊗ 1_i) ψ_d 1_{ν,ν'}` is
`ŵ_{d⁻¹(v ⊕ 1)}^*` times `ι(1_{ν₀,i} ⊗ 1_{ν'})`. -/
theorem lastBimod_hatWRevSub (v₀ : Shuffle (Seq.card_add' ν₀ (ν₀' + Si i))) :
    lastBimod Q ν₀ ν₀' i (hatWRevSub v₀) =
      op (tensorAppendL Q ν₀ (ν₀' + Si i) i 1) • hatWRevSubOf (lastStrandWord ν₀ ν₀' i)
        (lastShuffles ν₀ ν₀' i
          (Sum.inr (shuffleCongr (Seq.card_add' ν₀ (ν₀' + Si i)) (lastTop_card ν₀ ν₀' i) v₀))) := by
  have hα : ValidWord (Multiset.card (ν₀ + Si i + ν₀')) (shufWord v₀).reverse := by
    rw [validWord_reverse, ← lastQuad_h₁ ν₀ ν₀' i]
    exact validWord_canWord _ _
  have hE := appendR_castKLR_oneConcat_mul_lastψ (Q := Q) (ν₀ := ν₀) (ν₀' := ν₀') (i := i)
  have hO : oneConcat Q (ν₀ + Si i + ν₀') (Si i) * (lastψ Q ν₀ ν₀' i *
      botConcat Q (lastQuad_h ν₀ ν₀' i) (tensorAppendL Q ν₀ (ν₀' + Si i) i 1)) =
      lastψ Q ν₀ ν₀' i *
        botConcat Q (lastQuad_h ν₀ ν₀' i) (tensorAppendL Q ν₀ (ν₀' + Si i) i 1) := by
    rw [← hE, ← mul_assoc, ← appendR_one, ← map_mul, one_mul]
  have hY : appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i)
      (hatWRev v₀ : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))) * lastψ Q ν₀ ν₀' i =
      ψw (shufWord v₀).reverse * lastψ Q ν₀ ν₀' i *
        botConcat Q (lastQuad_h ν₀ ν₀' i) (tensorAppendL Q ν₀ (ν₀' + Si i) i 1) := by
    rw [hatWRev_eq, map_mul, map_mul, mul_assoc, hE, castKLR_ψw', appendR_ψw hα, mul_assoc, hO,
      mul_assoc]
  rw [lastBimod_apply, coe_hatWRevSub, hY, lastElt_mul_botConcat]
  congr 1
  apply Subtype.ext
  rw [coe_lastElt, coe_hatWRevSubOf, hatWRevOf, lastStrandWord_top, List.reverse_append,
    List.reverse_reverse, ψw_append, map_mul, castKLR_ψw', lastψ, castKLR_ψw',
    canWord_quadPerm_lastQuad, canWord_shuffleCongr]
  rfl

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]

/-- **`Ψ` on the shuffle basis**: `Ψ(ŵ_v^* ⊗ n) = [ŵ_{d⁻¹(v ⊕ 1)}^* ⊗ n]`. -/
theorem indLast_tmul_hatWRevSub (v₀ : Shuffle (Seq.card_add' ν₀ (ν₀' + Si i)))
    (n : ResLeft Q ν₀ ν₀' i N) :
    indLast (BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v₀) n) =
      Submodule.Quotient.mk (BalancedTensor.tmul (hatWRevSubOf (lastStrandWord ν₀ ν₀' i)
        (lastShuffles ν₀ ν₀' i
          (Sum.inr (shuffleCongr (Seq.card_add' ν₀ (ν₀' + Si i)) (lastTop_card ν₀ ν₀' i) v₀))))
        n.val) := by
  rw [indLast_tmul, lastBimod_hatWRevSub, BalancedTensor.op_smul_tmul]
  exact congrArg (fun m => Submodule.Quotient.mk (BalancedTensor.tmul _ m)) n.prop

end ShuffleBasis

end KLRAlgebra

end Categorification.KLR
