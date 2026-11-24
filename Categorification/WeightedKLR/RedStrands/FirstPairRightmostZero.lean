/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairTwoAfterSpectator
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer

/-!
# The rightmost partial standard at spectator weight zero

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21).
When the final spectator pairing is zero, its bigon across a black strand
gives an equivalent higher loading and the partial standard vanishes.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "B" => firstPairOneAfterSpectator true
local notation "Rtop" => firstPairTwoAfterSpectator

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ

private theorem firstPair_ncEvalTwoDots_one :
    ncEval ![(x ⟨2, by decide⟩ : A), x ⟨3, by decide⟩] (1 : MvPolynomial (Fin 2) k) = 1 := by
  let f : Fin 2 → Fin N := ![⟨2, by decide⟩, ⟨3, by decide⟩]
  have vector : ![(x ⟨2, by decide⟩ : A), x ⟨3, by decide⟩] = fun a => x (f a) := by
    funext a
    fin_cases a <;> rfl
  rw [vector,ncEval_eq_pol,map_one,map_one]

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_rightmost_zeroBigon (v : Seq μ)
    (h : (v.lbl ⟨2,by decide⟩ = .inr 2 ∧ v.lbl ⟨3,by decide⟩ = .inl ()) ∨
      (v.lbl ⟨2,by decide⟩ = .inl () ∧ v.lbl ⟨3,by decide⟩ = .inr 2))
    (zero : Λ 2 () = 0) :
    (ψ 2 * ψ 2 * e v : A) = e v := by
  have eq := ψ_sq (k := k) (Q := stendhalQ Q Λ) 2 (by decide) v
  rcases h with ⟨left,right⟩ | ⟨left,right⟩
  · have ne : (Sum.inr (2 : Fin 3) : Unit ⊕ Fin 3) ≠ Sum.inl () := by decide
    rw [left,right,ite_eq_right ne,stendhalQ_inr_inl,zero,pow_zero] at eq
    exact eq.trans ((congrArg (· * e v) (firstPair_ncEvalTwoDots_one Q Λ)).trans (one_mul _))
  · have ne : (Sum.inl () : Unit ⊕ Fin 3) ≠ Sum.inr 2 := by decide
    rw [left,right,ite_eq_right ne,stendhalQ_inl_inr,zero,pow_zero] at eq
    exact eq.trans ((congrArg (· * e v) (firstPair_ncEvalTwoDots_one Q Λ)).trans (one_mul _))

/-- The rightmost first-pair loading has zero partial standard when the
final spectator has weight zero. Its whole projective is the higher kernel. -/
theorem firstPairRightmost_blockLoadingKernel_eq_top_of_zeroSpectator (zero : Λ 2 () = 0) :
    blockLoadingKernel Q Λ Rtop 0 1 = ⊤ := by
  have same : redWord B = redWord Rtop := by decide
  have strict : adjacentBlockRoot 0 1 Rtop < adjacentBlockRoot 0 1 B := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro h
      exact (by decide : ¬ adjacentBlockRoot 0 1 B 2 () ≤ adjacentBlockRoot 0 1 Rtop 2 ())
        (h 2 ())
  have swap : sadj N 2 • Rtop = B := by decide +kernel
  exact blockLoadingKernel_eq_top_of_equiv Q Λ Rtop B 0 1 same strict
    (loadingIdemEquiv_of_unit_bigon Q Λ Rtop B same 2 swap
      (firstPair_rightmost_zeroBigon Q Λ Rtop (Or.inl ⟨by decide, by decide⟩) zero)
      (firstPair_rightmost_zeroBigon Q Λ B (Or.inr ⟨by decide, by decide⟩) zero))

open CategoryTheory CategoryTheory.Limits
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

set_option backward.isDefEq.respectTransparency false in
/-- With zero final spectator weight, the rightmost first-pair partial
standard is the zero module in its original red-order corner. -/
theorem firstPairRightmost_partialStandard_isZero_of_zeroSpectator (zero : Λ 2 () = 0) :
    IsZero (blockPartialStandardAt Q Λ Rtop 0 1 (redWord Rtop) rfl) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let T := (isIdempotentElem_violMk_redProj k Q Λ ν (redWord Rtop)).Corner
  let P := rIdeal (orderedLoadingIdem Q Λ Rtop)
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let K := blockLoadingKernel Q Λ Rtop 0 1
  change Subsingleton (P ⧸ K)
  exact Submodule.Quotient.subsingleton_iff.mpr
    (firstPairRightmost_blockLoadingKernel_eq_top_of_zeroSpectator Q Λ zero)

end Categorification.Stendhal.BraidedStendhalAlgebra
