/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalSeqIdem
import Categorification.WeightedKLR.Rigidity.SMoveReflectFlip
import Categorification.WeightedKLR.Rigidity.SMoveStdLayerSeparation
import Categorification.WeightedKLR.RedStrands.PrependRedStandardDegree
import Categorification.WeightedKLR.RedStrands.LeftStandardTensorFixed

/-!
# The S-move module `𝕊(P_∅ ⊠ N)` is killed by the loadings above the diagonal

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. Let
`s = (red₁ red₂ 𝐮 red₃)` be a loading of the three red strands of the S-move with every black
strand between the second and the third red strand. For every module `N` over `T^{λ_2, λ_3}(β)`,
the partial standardization `W = 𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ N)` (`SMove.leftStd`) is killed by
`e(t)` for every loading `t > s` (Webster's order of §5.1):

* `t > s` forces a black strand left of the second red strand
  (`SMove.ne_prependRed_prependRed_of_stendhalLT`), since `t ≤ s` whenever `t` starts with
  `red₁ red₂`;
* if `t` does not start with `red₁`, then `e(t) = 0` in `T^{λ_1, λ_2, λ_3}`
  (`seqIdem_eq_zero_of_not_prepend`);
* if `t = (red₁ t')`, then in the shuffle coordinates of the cut `{1} | {2, 3}` only the
  identity coordinate can be nonzero (`isUnshuffledLoading_append_emptyLeft`), and there `e(t)`
  acts on `P_∅ ⊠ N` through `e(t')`, which vanishes in `T^{λ_2, λ_3}` because `t'` has a black
  strand left of its first red strand.

The reflection of left modules at the trivial braid is restriction along the horizontal flip,
which fixes loading idempotents (`tensorFlip_mk_e`); hence the reflected module `W^r` satisfies
the hypothesis of `leftStandardTensorEquivFixed`, so `W^r ⊗_T S_s ≅ W^r e(s)`
(`SMove.leftStdReflectTensorEquivFixed`, in `SMoveDiagonalCoefficientCovers`). No route
hypotheses; any `N`.

## Main results

* `Stendhal.cutLoadingEnd_emptyLeft_eq_zero`: `e(i j)` kills `𝕊(P_∅ ⊠ Z)` when `e(j)` is zero.
* `Stendhal.SMove.seqIdem_smul_leftStd_eq_zero`: `e(t)` kills `SMove.leftStd N` when `t` has a
  black strand left of the second red strand.
* `Stendhal.SMove.ne_prependRed_prependRed_of_stendhalLT`: the order statement.
* `Stendhal.SMove.seqIdem_smul_leftStd_eq_zero_of_stendhalLT`.
* `Stendhal.SMove.op_seqIdem_smul_reflectOne_leftStd_eq_zero_of_stendhalLT`: the reflected form.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite BraidedStendhalAlgebra
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-! ### The cut with the outer block `P_∅` on the left -/

section EmptyLeft

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {r : ℕ} (Λ : Fin (1 + r) → I →₀ ℕ) (β : Multiset I)
  (Z : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β))

local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight 1 (0 : Multiset I))
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd 1)) (stendhalWeight r β)

/-- **A vanishing suffix idempotent kills the partial standardization** (Webster,
arXiv:1309.3796v3, §5.1, the cut `{1} | {2, …}` with the outer block `P_∅`): if the loading
idempotent of `j` is zero in `T^{λ_2, …}`, then `e(i j)` is zero on `𝕊(P_∅ ⊠ Z)`. -/
theorem cutLoadingEnd_emptyLeft_eq_zero (i : Seq α) (j : Seq δ)
    (hj : cutSuffixProjection Q Λ β (e j) = 0)
    (w : CutStandard Q Λ 0 β (emptyLeftInput Q Λ β Z)) :
    cutLoadingEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) hQ (i.append j) w = 0 := by
  have key : ∀ u : Shuffle (Seq.card_add' α δ),
      (cutStandardShuffleEquiv Q Λ 0 β (emptyLeftInput Q Λ β Z) hQ
        (cutLoadingEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) hQ (i.append j) w) :
          Shuffle (Seq.card_add' α δ) → CutInput Q Λ 0 β (emptyLeftInput Q Λ β Z)) u = 0 := by
    intro u
    rw [cutStandardShuffleEquiv_action_e]
    by_cases hu : u = shufOne
    · subst hu
      change cutInputIdemEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) (i.append j) _ = 0
      apply (emptyLeftScalarEquiv Q Λ β Z).injective
      refine (cutInputIdemEnd_regularLeft Q Λ β Z i j _).trans ?_
      refine (congrArg (fun c => c • emptyLeftScalarEquiv Q Λ β Z _) hj).trans ?_
      exact (zero_smul _ _).trans (map_zero _).symm
    · exact (congrArg (fun c => c • _)
        (isUnshuffledLoading_append_emptyLeft Q Λ β i j u hu)).trans (zero_smul _ _)
  refine (cutStandardShuffleEquiv Q Λ 0 β _ hQ).injective
    (Subtype.ext (funext fun u => (key u).trans ?_))
  exact (congrFun (congrArg Subtype.val
    (map_zero (cutStandardShuffleEquiv Q Λ 0 β (emptyLeftInput Q Λ β Z) hQ))) u).symm

end EmptyLeft

/-! ### Three red strands -/

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β : Multiset I)

omit [DecidableEq I] in
/-- In cut coordinates of `{1} | {2, 3}`, the loading `(red₁ t')` is the concatenation of the
loading of `red₁` with the relabelled loading `t'`. -/
theorem seqCast_append_eq_prependRedLoading (t' : Seq (stendhalWeight (1 + 1) β))
    (i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (1 + 1)))
      (stendhalWeight 1 (0 : Multiset I)))) :
    Seq.cast (congrArg (stendhalWeight (1 + (1 + 1))) (zero_add β))
        (Seq.cast (cutInputWeights_add (a := 1) (r := 1 + 1) (0 : Multiset I) β)
          (i.append ((redSubfamilyRelabel Q Λ (Fin.natAdd 1) (Fin.natAdd_injective (1 + 1) 1)
            β).equiv t'))) =
      prependRedLoading (ℓ := 1 + 1) t' := by
  apply seq_eq_of_seqWord_eq
  unfold prependRedLoading
  simp only [redSubfamilyRelabel, SeqRelabel.ofInjective, Seq.mapEquiv_apply]
  simp only [seqWord_cast, seqWord_append, seqWord_map,
    seqWord_singleton (x := (Sum.inr (Fin.castAdd (1 + 1) 0) : I ⊕ Fin (1 + (1 + 1))))
      (by simp [stendhalWeight]) i,
    seqWord_singleton (x := (Sum.inr 0 : I ⊕ Fin (1 + 1 + 1))) rfl (firstRedSeq (1 + 1))]
  simp only [List.singleton_append, List.cons.injEq]
  refine ⟨rfl, List.map_congr_left fun c _ => ?_⟩
  rcases c with c | c
  · rfl
  · exact congrArg Sum.inr (Fin.ext (by simp [add_comm]))

/-- The loading idempotent of `(red₁ t')` in cut coordinates. -/
theorem seqIdem_prependRedLoading_eq_cutLoad (t' : Seq (stendhalWeight (1 + 1) β))
    (ht : IsRedOrdered (prependRedLoading (ℓ := 1 + 1) t'))
    (i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (1 + 1)))
      (stendhalWeight 1 (0 : Multiset I)))) :
    seqIdem Q Λ (prependRedLoading (ℓ := 1 + 1) t') ht =
      cutLoad Q Λ (zero_add β) (i.append ((redSubfamilyRelabel Q Λ (Fin.natAdd 1)
        (Fin.natAdd_injective (1 + 1) 1) β).equiv t')) := by
  rw [cutLoad, ← seq_cast_symm_cast (cutInputWeights_add (a := 1) (r := 1 + 1) (0 : Multiset I) β)
      (i.append _), ← tensorLoad_eq_affineToTensor (a := 1) (r := 1 + 1), cast_tensorLoad,
    seqCast_append_eq_prependRedLoading Q Λ β t' i, tensorLoad_eq_seqIdem]

/-- **`e(t)` kills `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ N)` when `t` has a black strand left of the second
red strand** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, `Tor₀` of the
diagonal pair): if `t` is not of the form `(red₁ red₂ t'')`, then `e(t) W = 0` for
`W = SMove.leftStd N`, for every module `N`. -/
theorem seqIdem_smul_leftStd_eq_zero
    (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β))
    (t : Seq (stendhalWeight (1 + (1 + 1)) β)) (ht : IsRedOrdered t)
    (hne : ∀ t'' : Seq (stendhalWeight 1 β),
      prependRedLoading (ℓ := 1 + 1) (prependRedLoading (ℓ := 1) t'') ≠ t)
    (w : (leftStd Q hQ Λ β).obj N) : seqIdem Q Λ t ht • w = 0 := by
  by_cases hp : ∃ t' : Seq (stendhalWeight (1 + 1) β), prependRedLoading (ℓ := 1 + 1) t' = t
  · obtain ⟨t', rfl⟩ := hp
    have ht' : IsRedOrdered t' := (prependRedLoading_ordered_iff t').mp ht
    have h0 : seqIdem Q (Λ ∘ Fin.natAdd 1) t' ht' = 0 :=
      seqIdem_eq_zero_of_not_prepend (ℓ := 1) Q (Λ ∘ Fin.natAdd 1) β t' ht'
        (fun t'' h => hne t'' (congrArg _ h))
    obtain ⟨i, -⟩ : ∃ _i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (1 + 1)))
        (stendhalWeight 1 (0 : Multiset I))), True :=
      ⟨Seq.map (Sum.map (id : I → I) (Fin.castAdd (1 + 1))) (firstRedSeq (I := I) 0), trivial⟩
    have hj : cutSuffixProjection Q Λ β (e ((redSubfamilyRelabel Q Λ (Fin.natAdd 1)
        (Fin.natAdd_injective (1 + 1) 1) β).equiv t')) = 0 := by
      rw [cutSuffixProjection_e, Equiv.symm_apply_apply, tensorLoad_eq_seqIdem _ _ _ _ ht', h0]
    have hw : cutLoad Q Λ (zero_add β) (i.append ((redSubfamilyRelabel Q Λ (Fin.natAdd 1)
        (Fin.natAdd_injective (1 + 1) 1) β).equiv t')) •
          (show (emptyLeftStd Q hQ Λ β).obj N from w) = 0 :=
      (cutLoad_smul Q hQ Λ (zero_add β) (emptyLeftInput Q Λ β N) _ w).trans
        (cutLoadingEnd_emptyLeft_eq_zero Q hQ Λ β N i _ hj w)
    rw [seqIdem_prependRedLoading_eq_cutLoad Q Λ β t' ht i]
    exact hw
  · rw [seqIdem_eq_zero_of_not_prepend (ℓ := 1 + 1) Q Λ β t ht (fun t' h => hp ⟨t', h⟩),
      zero_smul]

/-- The number of black `i`-strands left of a red strand is at most the multiplicity of `i`. -/
theorem blackCount_le_count {ℓ : ℕ} (t : Seq (stendhalWeight ℓ β)) (r : Fin ℓ) (i : I) :
    blackCount t r i ≤ β.count i := by
  classical
  calc blackCount t r i ≤ (Finset.univ.filter fun a => t.lbl a = .inl i).card :=
        Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.1)
    _ = (stendhalWeight ℓ β).count (.inl i) := card_filter_lbl_eq t _
    _ = β.count i := by
      simp [stendhalWeight, Multiset.count_map, Multiset.count_add]
      exact (Multiset.count_eq_card_filter_eq _ _).symm

/-- **A loading above the diagonal has a black strand left of the second red strand**
(Webster, arXiv:1309.3796v3, §5.1 order; §7.3, proof of Proposition 7.22): if every black
strand of `s` lies left of the last red strand and `s < t`, then `t` is not of the form
`(red₁ red₂ t'')`. -/
theorem ne_prependRed_prependRed_of_stendhalLT (s t : Seq (stendhalWeight (1 + (1 + 1)) β))
    (hs : ∀ i, blackCount s (Fin.last 2) i = β.count i) (hst : StendhalLT s t)
    (t'' : Seq (stendhalWeight 1 β)) :
    prependRedLoading (ℓ := 1 + 1) (prependRedLoading (ℓ := 1) t'') ≠ t := by
  rintro rfl
  refine hst.2 fun r i => ?_
  match r with
  | ⟨0, _⟩ =>
    have h := blackCount_prependRedLoading_zero (ℓ := 1 + 1) (prependRedLoading (ℓ := 1) t'') i
    exact (Nat.le_of_eq h).trans (Nat.zero_le _)
  | ⟨1, _⟩ =>
    have h := blackCount_prependRedLoading_succ (ℓ := 1 + 1) (prependRedLoading (ℓ := 1) t'')
      0 i
    rw [blackCount_prependRedLoading_zero] at h
    exact (Nat.le_of_eq h).trans (Nat.zero_le _)
  | ⟨2, _⟩ =>
    exact (blackCount_le_count β _ _ i).trans_eq (hs i).symm

/-- **The loadings above the diagonal kill `SMove.leftStd N`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22, `Tor₀` of the diagonal pair): for every module `N` and every
loading `s` with all black strands left of the last red strand, `e(t) W = 0` for
`W = SMove.leftStd N` and all `t > s`. -/
theorem seqIdem_smul_leftStd_eq_zero_of_stendhalLT
    (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β))
    (s : Seq (stendhalWeight (1 + (1 + 1)) β))
    (hs : ∀ i, blackCount s (Fin.last 2) i = β.count i)
    (t : Seq (stendhalWeight (1 + (1 + 1)) β)) (ht : IsRedOrdered t) (hst : StendhalLT s t)
    (w : (leftStd Q hQ Λ β).obj N) : seqIdem Q Λ t ht • w = 0 :=
  seqIdem_smul_leftStd_eq_zero Q hQ Λ β N t ht
    (ne_prependRed_prependRed_of_stendhalLT β s t hs hst) w

variable {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight (1 + (1 + 1)) β))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

/-- **The reflected form**: for `W^r` the reflection of `W = SMove.leftStd N`,
`W^r e(t) = 0` for every `t > s` (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): the reflection at the trivial braid fixes loading idempotents. -/
theorem op_seqIdem_smul_reflectOne_leftStd_eq_zero_of_stendhalLT
    (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β))
    (s : Seq (stendhalWeight (1 + (1 + 1)) β))
    (hs : ∀ i, blackCount s (Fin.last 2) i = β.count i)
    (t : Seq (stendhalWeight (1 + (1 + 1)) β)) (ht : IsRedOrdered t) (hst : StendhalLT s t)
    (w : (reflectOne (ℓ := 1 + 1) Q Λ hQ hρ).obj ((leftStd Q hQ Λ β).obj N)) :
    op (seqIdem Q Λ t ht) • w = 0 := by
  change (cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1 (op (seqIdem Q Λ t ht))) •
    (show (leftStd Q hQ Λ β).obj N from w) = 0
  rw [cornerFlipTensorEquiv_one_apply, unop_op, seqIdem]
  erw [tensorFlip_mk_e]
  exact seqIdem_smul_leftStd_eq_zero_of_stendhalLT Q hQ Λ β N s hs t ht hst w

end SMove

end Categorification.Stendhal
