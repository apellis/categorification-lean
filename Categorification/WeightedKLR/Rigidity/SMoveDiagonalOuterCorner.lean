/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTorOneDimensional
import Categorification.WeightedKLR.Rigidity.SMoveLeftStdUpperIdem
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalCornerDimension

/-!
# The diagonal corner of `SMove.leftStd L` is a corner of `L`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the normalization of the `Tor₀` of the diagonal pair. The diagonal
loading `s = (red₁ red₂ 𝐮' red₃)` of the three red strands of the S-move is the loading
`(red₁ t')` with `t' = (red₂ 𝐮' red₃)` the loading of the last two red strands
(`SMove.prependRedLoading_diagonalOuterLoading`). Since the outer block of `SMove.leftStd` is
`P_∅`, the vectors of `SMove.leftStd L` fixed by `e(s)` are the vectors of `L` fixed by `e(t')`
(`emptyLeftStdCornerEquiv`), so

  `dim e(s) SMove.leftStd L = dim e(red₂ 𝐮' red₃) L`

(`SMove.finrank_fixSub_leftStd_diagonalTwoPiece`). The loading `(red₂ 𝐮' red₃)` is the wrap
loading of the word `𝐮'`, whose idempotent generates the coevaluation standard module of
Lemma 7.3 (`SMove.diagonalOuterLoading_reverse_eq_wrap`, in `SMoveTorWrapHead`). Hence the route
hypothesis `hnorm` of `SMove.derivedTensorHomology_reflect_leftStd_rightStd_one_dimensional` is
the corner count `dim e(red₂ 𝐮' red₃) L = |J|`, proved for the head of the wrap projective in
`SMove.derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional`. No route hypotheses.

## Main definitions

* `SMove.diagonalOuterLoading`: the loading `(red₂ 𝐮' red₃)` of `T^{λ_2, λ_3}(ν)`.

## Main results

* `SMove.prependRedLoading_diagonalOuterLoading`.
* `SMove.finrank_fixSub_leftStd_diagonalTwoPiece`.
* `SMove.isRedOrdered_diagonalOuterLoading`.
* `SMove.fixSubLeftStdPrependRedEquiv`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits Abelian KLR KLRAlgebra Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}

omit [DecidableEq I] in
/-- The weight identity `wordWt u 0 = ν` read off `0 + wordWt u 0 = ν`. -/
theorem wordWt_eq_of_zero_add {u : List I} (h₀ : 0 + wordWt u 0 = ν) : wordWt u 0 = ν :=
  (zero_add _).symm.trans h₀

/-- The loading `(red₂ 𝐮' red₃)` of the last two red strands of the S-move, `𝐮'` the reverse of
`𝐮`: the one-red loading `(red₂ 𝐮')` followed by the third red strand. -/
def diagonalOuterLoading (u : List I) (h₀ : 0 + wordWt u 0 = ν) :
    Seq (stendhalWeight (1 + 1) ν) :=
  appendRedLoading (ℓ := 1) (Seq.cast (congrArg (stendhalWeight 1) (wordWt_eq_of_zero_add h₀))
    (SingleRed.insertWord (wordWt u 0)
      (KLRAlgebra.Seq.ofList u.reverse (coe_reverse_eq_wordWt u))))

omit [DecidableEq I] in
/-- **The diagonal loading is `(red₁ t')`** for `t' = (red₂ 𝐮' red₃)`. -/
theorem prependRedLoading_diagonalOuterLoading (u : List I) (h₀ : 0 + wordWt u 0 = ν)
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    prependRedLoading (ℓ := 1 + 1) (diagonalOuterLoading u h₀) =
      (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).1 := by
  apply seq_eq_of_seqWord_eq
  unfold prependRedLoading diagonalOuterLoading appendRedLoading diagonalTwoPiece
    diagonalInnerLoading twoPieceLabel twoPieceLoading concatLoading
  simp only [seqWord_cast, seqWord_append, seqWord_map, seqWord_insertWord, seqWord_oneZero t,
    seqWord_zero rfl (default : Seq (0 : Multiset I)),
    seqWord_singleton (x := (Sum.inr 0 : I ⊕ Fin (1 + 1 + 1))) rfl (firstRedSeq (1 + 1)),
    seqWord_singleton (x := (Sum.inr (Fin.last 1) : I ⊕ Fin (1 + 1))) rfl (singletonRedSeq 1)]
  simp only [List.map_cons, List.map_nil, List.map_map, List.cons_append, List.nil_append,
    List.map_append, Sum.map_inr]
  rfl

omit [DecidableEq I] in
/-- `t' = (red₂ 𝐮' red₃)` is red-ordered. -/
theorem isRedOrdered_diagonalOuterLoading (u : List I) (h₀ : 0 + wordWt u 0 = ν)
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    IsRedOrdered (diagonalOuterLoading u h₀) :=
  (prependRedLoading_ordered_iff _).mp
    ((prependRedLoading_diagonalOuterLoading u h₀ t ht).symm ▸
      (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).2)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- The loading corners of `SMove.leftStd N` at `(red₁ t')` and of `N` at `t'`. -/
def fixSubLeftStdPrependRedEquiv
    (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))
    (t' : Seq (stendhalWeight (1 + 1) ν)) (ht : IsRedOrdered (prependRedLoading (ℓ := 1 + 1) t')) :
    fixSub k ((leftStd Q hQ Λ ν).obj N) (seqIdem Q Λ (prependRedLoading (ℓ := 1 + 1) t') ht) ≃ₗ[k]
      fixSub k N (tensorLoad Q (Λ ∘ Fin.natAdd 1) ν t') :=
  let i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (1 + 1)))
      (stendhalWeight 1 (0 : Multiset I))) :=
    Seq.map (Sum.map (id : I → I) (Fin.castAdd (1 + 1))) (firstRedSeq (I := I) 0)
  let j := (redSubfamilyRelabel Q Λ (Fin.natAdd 1) (Fin.natAdd_injective (1 + 1) 1) ν).equiv t'
  (LinearEquiv.ofEq _ _ (by rw [seqIdem_prependRedLoading_eq_cutLoad Q Λ ν t' ht i])).trans
    ((show fixSub k ((leftStd Q hQ Λ ν).obj N) (cutLoad Q Λ (zero_add ν) (i.append j)) ≃ₗ[k]
        fixSub k N (cutSuffixProjection Q Λ ν (e j)) from
      emptyLeftStdCornerEquiv Q hQ Λ ν N i j).trans
      (LinearEquiv.ofEq _ _ (by rw [cutSuffixProjection_e, Equiv.symm_apply_apply])))

/-- **The diagonal corner of `SMove.leftStd N`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, gap (c)): for every module `N` over `T^{λ_2, λ_3}(ν)` and the diagonal loading
`s = (red₁ red₂ 𝐮' red₃)`, `dim e(s) SMove.leftStd N = dim e(red₂ 𝐮' red₃) N`. -/
theorem finrank_fixSub_leftStd_diagonalTwoPiece
    (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) :
    Module.finrank k (fixSub k ((leftStd Q hQ Λ ν).obj N)
        (seqIdem Q Λ (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).1
          (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).2)) =
      Module.finrank k (fixSub k N
        (tensorLoad Q (Λ ∘ Fin.natAdd 1) ν (diagonalOuterLoading u h₀))) := by
  have key : ∀ (s : Seq (stendhalWeight (1 + (1 + 1)) ν)) (hs : IsRedOrdered s),
      prependRedLoading (ℓ := 1 + 1) (diagonalOuterLoading u h₀) = s →
      Module.finrank k (fixSub k ((leftStd Q hQ Λ ν).obj N) (seqIdem Q Λ s hs)) =
        Module.finrank k (fixSub k N
          (tensorLoad Q (Λ ∘ Fin.natAdd 1) ν (diagonalOuterLoading u h₀))) := by
    rintro s hs rfl
    exact (fixSubLeftStdPrependRedEquiv Q hQ Λ N _ hs).finrank_eq
  exact key _ _ (prependRedLoading_diagonalOuterLoading u h₀ t ht)

end Categorification.Stendhal.SMove
