/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer
import Categorification.WeightedKLR.RedStrands.OneBlackRetainedOrder

/-!
# The retained kernel across two zero-weight spectators

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 at (6.21).
With one black strand following the paired reds and two zero-weight spectators,
the two unit bigons identify the source kernel with a single higher partial standard.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev ν : Multiset Unit := {()}
private abbrev μ := stendhalWeight 4 ν
private abbrev n := Multiset.card μ

/-- The black strand follows both spectator reds. -/
def source : Seq μ :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2, .inr 3, .inl ()] (by decide)

private def middle : Seq μ :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inr 3] (by decide)

/-- The black lies between the pair and both spectator reds. -/
def higher : Seq μ :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl (), .inr 2, .inr 3] (by decide)

/-- Both loadings put the reds in the same order. -/
theorem sameOrder : redWord higher = redWord source := by decide
private theorem middleOrder : redWord middle = redWord source := by decide
private theorem higherMiddleOrder : redWord higher = redWord middle := by decide

private theorem finalSwap : TypeA.sadj n 3 • source = middle := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

private theorem firstSwap : TypeA.sadj n 2 • middle = higher := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

private theorem source_lt_higher : adjacentBlockRoot 0 1 source < adjacentBlockRoot 0 1 higher := by
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad : (0 : ℕ) = 1 := congrFun (congrFun h (2 : Fin 4)) ()
    contradiction

private theorem higher_maximal : ∀ w : Seq μ, redWord w = redWord higher →
    adjacentBlockRoot 0 1 higher < adjacentBlockRoot 0 1 w → IsViolated w := by
  intro w ho hlt
  let head : Fin n := ⟨0, by decide⟩
  cases hlabel : w.lbl head with
  | inl c => exact ⟨by decide, by change (w.lbl head).isLeft; simp [hlabel]⟩
  | inr r =>
    exfalso
    have hred : redWord higher = ([] : List (Fin 4)) ++ 0 :: 1 :: [2, 3] := by decide
    have hr : r = 0 := by
      have hhead : (redWord w).head? = some r := by
        change ((List.finRange 5).filterMap fun a => (w.lbl a).getRight?).head? = some r
        rw [List.finRange_succ (n := 4)]
        change ((head :: (List.finRange 4).map Fin.succ).filterMap
          fun a => (w.lbl a).getRight?).head? = some r
        rw [List.filterMap_cons, hlabel]
        rfl
      rw [ho, hred] at hhead
      exact (Option.some.inj hhead).symm
    subst r
    have hm : (Sum.inl () : Unit ⊕ Fin 4) ∈ μ := by simp [stendhalWeight]
    rw [← show Finset.univ.val.map w.lbl = μ from w.2, Multiset.mem_map] at hm
    obtain ⟨x, _, hx⟩ := hm
    apply hlt.not_ge
    apply (adjacentBlockRoot_oneBlack_le_iff (ho.trans hred) hred x
      ⟨2, by decide⟩ hx rfl).2
    intro r hr p q hp hq hxp
    fin_cases r
    · have hp0 : p = head := by
        have huniq : Function.Injective w.lbl :=
          fun a b hab => Multiset.inj_on_of_nodup_map (by rw [w.2]; decide) a (by simp) b (by simp) hab
        exact huniq (hp.trans hlabel.symm)
      subst p
      exact (Nat.not_lt_zero _ (show x.val < 0 from hxp)).elim
    · exact (hr rfl).elim
    · fin_cases q <;> revert hq <;> decide
    · fin_cases q <;> revert hq <;> decide

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)

local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))

private theorem unitEval (v : Fin 2 → R) : ncEval v (1 : MvPolynomial (Fin 2) k) = 1 := by
  unfold ncEval
  rw [show (1 : MvPolynomial (Fin 2) k).coeff = Finsupp.single 0 1 from rfl,
    Finsupp.sum_single_index (by simp)]
  simp

private theorem redBlackBigon (w : Seq μ) (j : ℕ) (hj : j + 1 < n) (r : Fin 4)
    (hr : w.lbl ⟨j, lt_trans (Nat.lt_succ_self j) hj⟩ = .inr r) (hb : w.lbl ⟨j + 1, hj⟩ = .inl ())
    (hz : Λ r () = 0) :
    (KLRAlgebra.ψ j * KLRAlgebra.ψ j * KLRAlgebra.e w : R) = KLRAlgebra.e w := by
  rw [KLRAlgebra.ψ_sq j hj, hr, hb]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, hz, pow_zero, unitEval, one_mul]

private theorem blackRedBigon (w : Seq μ) (j : ℕ) (hj : j + 1 < n) (r : Fin 4)
    (hb : w.lbl ⟨j, lt_trans (Nat.lt_succ_self j) hj⟩ = .inl ()) (hr : w.lbl ⟨j + 1, hj⟩ = .inr r)
    (hz : Λ r () = 0) :
    (KLRAlgebra.ψ j * KLRAlgebra.ψ j * KLRAlgebra.e w : R) = KLRAlgebra.e w := by
  rw [KLRAlgebra.ψ_sq j hj, hb, hr]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, hz, pow_zero, unitEval, one_mul]

private theorem sourceIdemEquiv (h2 : Λ 2 () = 0) (h3 : Λ 3 () = 0) :
    IdemEquiv (orderedLoadingIdem Q Λ source)
      (orderedLoadingIdemAt Q Λ (redWord source) higher sameOrder) := by
  have hlast := loadingIdemEquiv_of_unit_bigon Q Λ source middle middleOrder 3 finalSwap
    (redBlackBigon Q Λ source 3 (by decide) 3 rfl rfl h3)
    (blackRedBigon Q Λ middle 3 (by decide) 3 rfl rfl h3)
  have hfirst := loadingIdemEquiv_of_unit_bigon Q Λ middle higher higherMiddleOrder 2 firstSwap
    (redBlackBigon Q Λ middle 2 (by decide) 2 rfl rfl h2)
    (blackRedBigon Q Λ higher 2 (by decide) 2 rfl rfl h2)
  exact hlast.trans hfirst

/-- The two spectator crossings identify the source kernel with the partial
standard quotient of the loading before both zero-weight spectators. -/
def kernelEquivHigherPartialStandard (h2 : Λ 2 () = 0) (h3 : Λ 3 () = 0) :
    (blockLoadingKernel Q Λ source 0 1) ≃ₗ[Tᵐᵒᵖ]
      blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder := by
  have he := sourceIdemEquiv Q Λ h2 h3
  have htop := blockLoadingKernel_eq_top_of_equiv Q Λ source higher 0 1
    sameOrder source_lt_higher he
  let p := blockLoadingKernel Q Λ source 0 1
  let φ := Classical.choose_spec (Classical.choose_spec he)
  exact (LinearEquiv.ofEq p ⊤ htop).trans (Submodule.topEquiv.trans
    (φ.rIdealEquiv.trans (blockPartialStandardAt_equiv_projective
      Q Λ higher 0 1 (redWord source) sameOrder higher_maximal).symm))

/-- The source kernel has the one higher partial standard as its filtration layer. -/
theorem kernel_hasHigherFiltration (h2 : Λ 2 () = 0) (h3 : Λ 3 () = 0) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of Tᵐᵒᵖ (blockLoadingKernel Q Λ source 0 1)) :=
  ModuleFiltration.HasFiltration.single (kernelEquivHigherPartialStandard Q Λ h2 h3)

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack
