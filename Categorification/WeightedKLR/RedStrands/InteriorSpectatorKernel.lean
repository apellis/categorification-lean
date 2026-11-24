/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TerminalSpectatorCuts
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt
import Categorification.WeightedKLR.RedStrands.HigherKernelFiltrationStep
import Categorification.WeightedKLR.RedStrands.OrdinaryRetainedCrossing
import Categorification.WeightedKLR.RedStrands.RightmostRedCrossingInjectivity
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingTest

/-!
# The interior spectator crossing and two higher layers

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The interior retained crossing surjects onto the kernel of the next projective.
Injectivity of both crossing maps then gives the two actual partial-standard
quotients in the source kernel.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA Equiv

private abbrev μ := stendhalWeight 4 ({()} : Multiset Unit)
private abbrev n := Multiset.card μ

private theorem interiorDescent (w : Seq μ) (ho : redWord w = redWord terminalHigher)
    (hlt : adjacentBlockRoot 0 1 terminalHigher < adjacentBlockRoot 0 1 w)
    (v : Perm (Fin n)) (hv : v • w = terminalHigher) : v⁻¹ (3 : Fin 5) < v⁻¹ (2 : Fin 5) := by
  have hoff : redWord terminalHigher = ([] : List (Fin 4)) ++ 0 :: 1 :: [2, 3] := by decide
  have hlabel (j : Fin n) : w.lbl (v⁻¹ j) = terminalHigher.lbl j :=
    congrArg (fun y : Seq μ => y.lbl j) hv
  have hb : w.lbl (v⁻¹ (3 : Fin 5)) = .inl () := (hlabel _).trans rfl
  have ht : w.lbl (v⁻¹ (2 : Fin 5)) = .inr 2 := (hlabel _).trans rfl
  obtain ⟨_, r, ps, pt, hr, hps, hpt, hsep, hp⟩ :=
    (adjacentBlockRoot_oneBlack_lt_iff hoff (ho.trans hoff) ⟨3, by decide⟩
      (v⁻¹ (3 : Fin 5)) rfl hb).1 hlt
  have hpairs := redWord_pairwise_one w
  rw [ho, hoff] at hpairs
  fin_cases r
  · exact hp.trans ((List.pairwise_cons.mp hpairs).1 2 (by decide) _ _ hpt ht)
  · exact (hr rfl).elim
  · have heq := lbl_inj_of_inr w 2 hpt ht
    simpa only [heq] using hp
  · have heq : ps = (4 : Fin 5) := lbl_inj_of_inr terminalHigher 3 hps rfl
    subst ps
    exact (by decide : ¬ (4 : Fin 5) ≤ 3) hsep |>.elim

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA Equiv MulOpposite ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)

private theorem interiorOrder : redWord higher = redWord terminalHigher := by decide
private theorem outerOrder : redWord terminalHigher = redWord source := by decide
private theorem actualHigherOrder : redWord higher = redWord source := by decide

private theorem terminalHigher_lt_higher :
    adjacentBlockRoot 0 1 terminalHigher < adjacentBlockRoot 0 1 higher := by
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad : (0 : ℕ) = 1 := congrFun (congrFun h (2 : Fin 4)) ()
    contradiction

private theorem interiorSwap : TypeA.sadj n 2 • higher = terminalHigher := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

private theorem interiorStep : TypeA.sadj n 2 • terminalHigher = higher := by
  rw [← interiorSwap, KLRAlgebra.sadj_smul_smul]

/-- The interior crossing of the first spectator maps into the intermediate kernel. -/
abbrev interiorCrossingMap :=
  crossingIntoKernelMap Q Λ 0 1 interiorOrder terminalHigher_lt_higher 2

/-- The first spectator crossing surjects onto the intermediate higher-cut kernel. -/
theorem interiorCrossingMap_surjective : Function.Surjective (interiorCrossingMap Q Λ) := by
  apply crossingIntoKernelMap_surjective_of_factors
    Q Λ 0 1 interiorOrder terminalHigher_lt_higher 2 interiorSwap
  intro w ho hlt _ z
  have h := cut_factors_of_leftDescent 2 (by decide) terminalHigher w z (interiorDescent w ho hlt)
  rw [interiorStep] at h
  exact h

private theorem higher_beforeSpectators (r : Fin 4) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (q : Fin n) (hq : higher.lbl q = .inr r) : (⟨2, by decide⟩ : Fin n) < q := by
  fin_cases r
  · exact (hr0 rfl).elim
  · exact (hr1 rfl).elim
  · fin_cases q <;> revert hq <;> decide
  · fin_cases q <;> revert hq <;> decide

local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Q Λ ({()} : Multiset Unit) (redWord source))

/-- The candidate layers for two retained spectator boundaries. -/
def twoSpectatorLayer : Bool → ModuleCat Tᵐᵒᵖ
  | false => blockPartialStandardAt Q Λ terminalHigher 0 1 (redWord source) outerOrder
  | true => blockPartialStandardAt Q Λ higher 0 1 (redWord source) actualHigherOrder

/-- The two crossing maps give a two-layer filtration once their injectivity
is established. Both layers are the actual retained loading quotients. -/
theorem kernel_hasTwoHigherLayers_of_crossings_injective
    (hterminal : Function.Injective (terminalCrossingMap Q Λ))
    (hinterior : Function.Injective (interiorCrossingMap Q Λ)) :
    HasFiltration (twoSpectatorLayer Q Λ) [false, true]
      (ModuleCat.of Tᵐᵒᵖ (blockLoadingKernel Q Λ source 0 1)) := by
  let f := LinearEquiv.ofBijective (terminalCrossingMap Q Λ)
    ⟨hterminal, terminalCrossingMap_surjective Q Λ⟩
  let g := LinearEquiv.ofBijective (interiorCrossingMap Q Λ)
    ⟨hinterior, interiorCrossingMap_surjective Q Λ⟩
  have hmax : ∀ w : Seq μ, redWord w = redWord higher →
      adjacentBlockRoot 0 1 higher < adjacentBlockRoot 0 1 w → IsViolated w :=
    fun _ ho hlt => isViolated_of_strictly_higher_beforeSpectators (M := [2,3])
      (by decide) ho ⟨2, by decide⟩ rfl higher_beforeSpectators hlt
  let h := blockPartialStandardAt_equiv_projective Q Λ higher 0 1 (redWord source)
    actualHigherOrder hmax
  let g' : rIdeal (orderedLoadingIdemAt Q Λ (redWord source) higher actualHigherOrder) ≃ₗ[Tᵐᵒᵖ]
      blockLoadingKernelObjAt Q Λ source terminalHigher 0 1 outerOrder := g
  have hinner : HasFiltration (twoSpectatorLayer Q Λ) [true]
      (blockLoadingKernelObjAt Q Λ source terminalHigher 0 1 outerOrder) :=
    HasFiltration.single (g'.symm.trans h.symm)
  exact blockLoadingKernel_hasFiltration_cons_of_equiv Q Λ source terminalHigher 0 1 outerOrder
    false f hinner (LinearEquiv.refl _ _)

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)
private abbrev νInterior : Multiset Unit := {()}
private theorem word : redWord terminalHigher = List.finRange 4 := by decide

/-- A right multiplication test in the ordinary ordered algebra transports, by
the quotient corner equivalence and diagram flip, to the interior right-projective map. -/
theorem interiorCrossingMap_injective_of_ordinary_test (hQ : KLRSymm Q)
    (h : ∀ x : TensorProductAlgebra k Q Λ νInterior,
      x * tensorOfKLR Q Λ νInterior (KLRAlgebra.e higher) = x →
      x * tensorOfKLR Q Λ νInterior (ψ 2 * KLRAlgebra.e terminalHigher) = 0 →
      x = 0) :
    Function.Injective (interiorCrossingMap Q Λ) :=
  crossingIntoKernelMap_injective_of_ordinary_test Q Λ word interiorOrder 2 interiorStep
    0 1 terminalHigher_lt_higher hQ h


private theorem appendHigher :
    appendRedLoading ThreeRedOneBlack.higher = higher := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

private theorem appendSource :
    appendRedLoading ThreeRedOneBlack.source = terminalHigher := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

private theorem threeHigherOrdered : IsRedOrdered ThreeRedOneBlack.higher := by
  unfold IsRedOrdered
  decide

private theorem threeSourceOrdered : IsRedOrdered ThreeRedOneBlack.source := by
  unfold IsRedOrdered
  decide

section EarlierField

variable {k₁ : Type} [Field k₁]

/-- The ordinary three-red test gives the four-red interior test by appending red `3`. -/
private theorem interiorCrossingMap_of_threeRed_test
    (parameter : Unit → Unit → MvPolynomial (Fin 2) k₁)
    (weights : Fin 4 → Unit →₀ ℕ) (hQ : KLRSymm parameter)
    (hbase : ∀ x : TensorProductAlgebra k₁ parameter (weights ∘ Fin.castSucc) (νInterior + 0),
      x * tensorOfKLR parameter (weights ∘ Fin.castSucc) (νInterior + 0)
        (KLRAlgebra.e ThreeRedOneBlack.higher) = x →
      x * tensorOfKLR parameter (weights ∘ Fin.castSucc) (νInterior + 0)
        (ψ 2 * KLRAlgebra.e ThreeRedOneBlack.source) = 0 → x = 0) :
    Function.Injective (interiorCrossingMap parameter weights) := by
  apply interiorCrossingMap_injective_of_ordinary_test parameter weights hQ
  intro x hx hc
  apply eq_zero_of_mul_appendRedCrossing parameter weights νInterior hQ
    ThreeRedOneBlack.higher ThreeRedOneBlack.source threeHigherOrdered threeSourceOrdered
    2 (by decide) hbase x
  · change x * tensorOfKLR parameter weights νInterior
      (KLRAlgebra.e (appendRedLoading ThreeRedOneBlack.higher)) = x
    rw [appendHigher]
    exact hx
  · have hc' : x * tensorOfKLR parameter weights νInterior
        ((ψ 2 : KLRAlgebra k₁ (stendhalQ parameter weights) (stendhalWeight 4 νInterior)) *
          KLRAlgebra.e (appendRedLoading (ν := νInterior) ThreeRedOneBlack.source)) = 0 := by
      rw [appendSource]
      exact hc
    exact hc'

end EarlierField

section Standard

open QuantumGroup KL3.Diagram

variable {F : Type} [Field F] {C : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C F)

private def pairedPrefix : Seq (stendhalWeight 2 ((0 : Multiset Unit) + 0)) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1] (by decide)

private theorem pairedPrefix_ordered : IsRedOrdered pairedPrefix := by unfold IsRedOrdered; decide

private theorem rankOneHigherAppend :
    appendRedLoading (appendBlackLoading () (0 + 0) pairedPrefix) = ThreeRedOneBlack.higher := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private theorem rankOneSourceAppend :
    appendBlackLoading () (0 + 0) (appendRedLoading pairedPrefix) = ThreeRedOneBlack.source := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private theorem threeRedTest_of_exact (weights : Fin 3 → Unit →₀ ℕ)
    (h : ∀ x : TensorProductAlgebra k Q weights ({()} + ((0 : Multiset Unit) + 0)),
      x * tensorOfKLR Q weights _ (KLRAlgebra.e
        (appendRedLoading (appendBlackLoading () (0 + 0) pairedPrefix))) = x →
      x * tensorOfKLR Q weights _ (ψ ((stendhalWeight 2 ((0 : Multiset Unit) + 0)).card) *
        KLRAlgebra.e (appendBlackLoading () (0 + 0) (appendRedLoading pairedPrefix))) = 0 →
      x = 0)
    (x : TensorProductAlgebra k Q weights (νInterior + 0))
    (hx : x * tensorOfKLR Q weights (νInterior + 0) (KLRAlgebra.e ThreeRedOneBlack.higher) = x)
    (hc : x * tensorOfKLR Q weights (νInterior + 0)
      (ψ 2 * KLRAlgebra.e ThreeRedOneBlack.source) = 0) : x = 0 := by
  have hcsize : (stendhalWeight 2 ((0 : Multiset Unit) + 0)).card = 2 := by decide
  apply h x
  · rw [rankOneHigherAppend]
    exact hx
  · rw [hcsize, rankOneSourceAppend]
    exact hc

/-- The interior map is injective at the standard Khovanov–Lauda parameters. -/
theorem interiorCrossingMap_standard_injective
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ) :
    Function.Injective (interiorCrossingMap QL weights) :=
  interiorCrossingMap_of_threeRed_test QL weights hQ
    (threeRedTest_of_exact QL (weights ∘ Fin.castSucc)
      (eq_zero_of_mul_rightmostRedCrossing (k := F) (C := C) (ℓ := 2)
        hR hQ _ () 0 pairedPrefix pairedPrefix_ordered))

/-- The two actual partial-standard quotients filter the four-red source kernel
at standard Khovanov–Lauda parameters. -/
theorem kernel_hasTwoHigherLayers_standard
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ) :
    ModuleFiltration.HasFiltration (twoSpectatorLayer QL weights) [false, true]
      (ModuleCat.of _ (blockLoadingKernel QL weights source 0 1)) :=
  kernel_hasTwoHigherLayers_of_crossings_injective QL weights
    (terminalCrossingMap_standard_injective hR hQ weights)
    (interiorCrossingMap_standard_injective hR hQ weights)

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack
