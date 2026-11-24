/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ZeroSpectatorKernelChain

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

private theorem higher_beforeSpectators (r : Fin 4) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (q : Fin n) (hq : higher.lbl q = .inr r) : (⟨2, by decide⟩ : Fin n) < q := by
  fin_cases r
  · exact (hr0 rfl).elim
  · exact (hr1 rfl).elim
  · fin_cases q <;> revert hq <;> decide
  · fin_cases q <;> revert hq <;> decide

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)

local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))

private theorem sourcePath (h2 : Λ 2 () = 0) (h3 : Λ 3 () = 0) :
    ZeroWeightSpectatorPath Λ source higher := by
  have step : ZeroWeightSpectatorPath Λ source middle := by
    rw [← finalSwap]
    exact ZeroWeightSpectatorPath.swap .nil 3 (by decide) 3 rfl rfl h3
  rw [← firstSwap]
  exact ZeroWeightSpectatorPath.swap step 2 (by decide) 2 rfl rfl h2

/-- The two spectator crossings identify the source kernel with the partial
standard quotient of the loading before both zero-weight spectators. -/
def kernelEquivHigherPartialStandard (h2 : Λ 2 () = 0) (h3 : Λ 3 () = 0) :
    (blockLoadingKernel Q Λ source 0 1) ≃ₗ[Tᵐᵒᵖ]
      blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder :=
  kernelEquivPartialStandard_beforeSpectators Λ Q (sourcePath Λ h2 h3)
    0 1 (M := [2, 3]) (by decide) ⟨2, by decide⟩ rfl higher_beforeSpectators source_lt_higher

/-- The source kernel has the one higher partial standard as its filtration layer. -/
theorem kernel_hasHigherFiltration (h2 : Λ 2 () = 0) (h3 : Λ 3 () = 0) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of Tᵐᵒᵖ (blockLoadingKernel Q Λ source 0 1)) :=
  ModuleFiltration.HasFiltration.single (kernelEquivHigherPartialStandard Q Λ h2 h3)

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack
