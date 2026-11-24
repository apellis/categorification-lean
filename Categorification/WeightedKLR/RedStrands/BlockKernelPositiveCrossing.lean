/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelCrossingGenerator
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.RightmostRedCrossingInjectivity

/-!
# The higher partial-standard layer across the spectator

Webster, arXiv:1309.3796v2, Lemma 5.23 and the proof of Lemma 6.8 at (6.21).
The rightmost-red crossing is injective in the ordinary ordered algebra. Diagram
reflection and the quotient corner equivalence give injectivity of the crossing
from the higher loading projective into the kernel.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
private abbrev ν : Multiset Unit := {()}
private abbrev μ := stendhalWeight 3 ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "B" => BraidedStendhalAlgebra k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (List.finRange 3))
local notation "p" => fun s => π (KLRAlgebra.e s)

private theorem word : redWord source = List.finRange 3 := by decide
private theorem highWord : redWord higher = List.finRange 3 := sameOrder.trans word
private theorem step : sadj (Multiset.card μ) 2 • source = higher := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private def cornerImage (z : R) : (isIdempotentElem_violRedProj k Q Λ ν).Corner :=
  violCornerHom k Q Λ ν (cornerMk (ofKLR k Q Λ ν z))

private theorem cornerImage_idem :
    (cornerImage Q Λ (KLRAlgebra.e higher)).1 = p higher := by
  rw [cornerImage, violCornerHom_val, cornerMk_e_val highWord]
  rfl

private theorem cornerImage_cross :
    (cornerImage Q Λ (ψ 2 * KLRAlgebra.e source)).1 = π (ψ 2 * KLRAlgebra.e source) := by
  let eR := redProj k Q Λ ν (List.finRange 3)
  let c := ofKLR k Q Λ ν (ψ 2 * KLRAlgebra.e source)
  have hc : (ψ 2 * KLRAlgebra.e source : R) = KLRAlgebra.e higher * ψ 2 := by
    rw [e_mul_ψ, ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  have hleft : eR * c = c := by
    dsimp [eR, c]
    rw [hc, map_mul, redProj_mul_e_of_eq highWord]
  have hright : c * eR = c := by
    dsimp [eR, c]
    rw [map_mul, mul_assoc, e_mul_redProj, ite_eq_left word]
  change violMk k Q Λ ν (eR * c * eR) = _
  rw [hleft, hright]
  rfl

private theorem flipMul (x y : V) : violFlip (x * y) = violFlip y * violFlip x :=
  congrArg MulOpposite.unop (map_mul (violFlipHom k Q Λ ν) x y)

private theorem flipE : violFlip E = E := by
  rw [violFlip_violMk, flip_redProj]

private theorem flipHigh : violFlip (p higher) = p higher := by
  change violFlip (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_e]
  rfl

private theorem flipCross :
    violFlip (π (ψ 2 * KLRAlgebra.e higher)) = π (ψ 2 * KLRAlgebra.e source) := by
  change violFlip (violMk k Q Λ ν (ofKLR k Q Λ ν (ψ 2 * KLRAlgebra.e higher))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_mul, hflip_e, hflip_ψ, e_mul_ψ,
    ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  rfl

private theorem ordinaryImage (z : R) :
    identityCornerToTensor k Q Λ ν (cornerMk (ofKLR k Q Λ ν z)) = tensorOfKLR Q Λ ν z := by
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  rw [identityCornerHom_val, cornerMk_val, map_mul, map_mul,
    toAllOrders_ofKLR]
  change toAllOrders k Q Λ ν (ofKLR k Q Λ ν (redIdem k Q Λ (List.finRange 3))) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν z *
      toAllOrders k Q Λ ν (ofKLR k Q Λ ν (redIdem k Q Λ (List.finRange 3))) = _
  rw [toAllOrders_redIdem]
  let eR := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  let a := StendhalAlgebraAllOrders.ofKLR k Q Λ ν z
  change eR * a * eR = a * eR
  rw [(redOrderedIdem_commute Q Λ ν a).eq, mul_assoc,
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq]

/-- A right multiplication test in the ordinary ordered algebra transports, by
the quotient corner equivalence and diagram flip, to the higher right-projective map. -/
theorem higherCrossingMap_injective_of_ordinary_test (hQ : KLRSymm Q)
    (h : ∀ x : TensorProductAlgebra k Q Λ ν,
      x * tensorOfKLR Q Λ ν (KLRAlgebra.e higher) = x →
      x * tensorOfKLR Q Λ ν (ψ 2 * KLRAlgebra.e source) = 0 →
      x = 0) :
    Function.Injective (higherCrossingMap Q Λ) := by
  let ρ := TypeA.canWord (Multiset.card μ)
  have hρ : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let q := violCornerEquiv (ν := ν) (Λ := Λ) hρ hQ
  let projective := rIdeal (orderedLoadingIdemAt Q Λ (redWord source) higher sameOrder)
  let : AddCommGroup projective := Submodule.addCommGroup projective
  let : AddCommGroup (blockLoadingKernel Q Λ source 0 1) := blockKernelAddGroup Q Λ source 0 1
  suffices hz : ∀ y : projective, higherCrossingMap Q Λ y = 0 → y = 0 by
    intro y z hyz
    have hs : higherCrossingMap Q Λ (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    exact sub_eq_zero.mp (hz (y - z) hs)
  intro y hy
  have hY : E * y.1.1 = y.1.1 ∧ y.1.1 * E = y.1.1 := by
    have inner := (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))).1 y.1.2
    have hEeq : violMk k Q Λ ν (redProj k Q Λ ν (redWord source)) = E :=
      congrArg (fun order => violMk k Q Λ ν (redProj k Q Λ ν order)) word
    exact ⟨(congrArg (fun z => z * y.1.1) hEeq).symm.trans inner.1,
      (congrArg (fun z => y.1.1 * z) hEeq).symm.trans inner.2⟩
  let fy : (isIdempotentElem_violRedProj k Q Λ ν).Corner := ⟨violFlip y.1.1,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violRedProj k Q Λ ν)).2
    ⟨by rw [← flipE Q Λ, ← flipMul Q Λ, hY.2],
     by rw [← flipE Q Λ, ← flipMul Q Λ, hY.1]⟩⟩
  have hf : fy * cornerImage Q Λ (KLRAlgebra.e higher) = fy := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (KLRAlgebra.e higher)).1 = violFlip y.1.1
    have hp : p higher * y.1.1 = y.1.1 := congrArg Subtype.val y.2
    rw [cornerImage_idem, ← flipHigh Q Λ, ← flipMul Q Λ, hp]
  have hh : fy * cornerImage Q Λ (ψ 2 * KLRAlgebra.e source) = 0 := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (ψ 2 * KLRAlgebra.e source)).1 = 0
    have hx : π (ψ 2 * KLRAlgebra.e higher) * y.1.1 = 0 := by
      rw [← higherCrossingMap_val, hy]
      rfl
    rw [cornerImage_cross, ← flipCross Q Λ, ← flipMul Q Λ, hx]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν))
  have himg (z : R) : q (cornerImage Q Λ z) = tensorOfKLR Q Λ ν z :=
    (violCornerEquiv_violCornerHom hρ hQ (cornerMk (ofKLR k Q Λ ν z))).trans (ordinaryImage Q Λ z)
  have hq : q fy = 0 := h (q fy) (by rw [← himg, ← map_mul q, hf])
    (by rw [← himg, ← map_mul q, hh, map_zero])
  have hfy : fy = 0 := q.injective (hq.trans (map_zero q).symm)
  apply Subtype.ext; apply Subtype.ext
  have hhf : violFlip y.1.1 = 0 := congrArg Subtype.val hfy
  exact (violFlip_violFlip y.1.1).symm.trans (by
    rw [hhf]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν)))

private def prefixLoading : Seq (stendhalWeight 2 ((0 : Multiset Unit) + 0)) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1] (by decide)

private theorem prefix_ordered : IsRedOrdered prefixLoading := by unfold IsRedOrdered; decide

private theorem higher_append :
    appendRedLoading (appendBlackLoading () (0 + 0) prefixLoading) = higher := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private theorem source_append :
    appendBlackLoading () (0 + 0) (appendRedLoading prefixLoading) = source := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

/-- Applying the ordinary test to the two-red prefix uses the exact two loadings. -/
private theorem higherCrossingMap_of_exact_prefix (hQ : KLRSymm Q)
    (hLast : ∀ x : TensorProductAlgebra k Q Λ ({()} + ((0 : Multiset Unit) + 0)),
      x * tensorOfKLR Q Λ _ (KLRAlgebra.e (appendRedLoading (appendBlackLoading () (0 + 0) prefixLoading))) = x →
      x * tensorOfKLR Q Λ _ (ψ ((stendhalWeight 2 ((0 : Multiset Unit) + 0)).card) *
        KLRAlgebra.e (appendBlackLoading () (0 + 0) (appendRedLoading prefixLoading))) = 0 →
      x = 0) :
    Function.Injective (higherCrossingMap Q Λ) := by
  apply higherCrossingMap_injective_of_ordinary_test Q Λ hQ
  intro x hx hc
  have hedges :
      (stendhalWeight 2 ((0 : Multiset Unit) + 0)).card = 2 := by decide
  apply hLast x
  · rw [higher_append]
    exact hx
  · rw [hedges, source_append]
    exact hc

section Standard

open QuantumGroup KL3.Diagram

variable {F : Type*} [Field F] {C : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C F)

/-- The crossing into the loading kernel is injective at the standard
Khovanov–Lauda parameters, including positive spectator weight. -/
theorem higherCrossingMap_standard_injective
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (weights : Fin 3 → Unit →₀ ℕ) :
    Function.Injective (higherCrossingMap QL weights) :=
  higherCrossingMap_of_exact_prefix QL weights hQ
    (eq_zero_of_mul_rightmostRedCrossing hR hQ weights () 0 prefixLoading prefix_ordered)

/-- The kernel has the higher partial standard as a single layer for the standard
Khovanov–Lauda parameters and arbitrary spectator weight. -/
theorem kernel_hasHigherFiltration_standard
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (weights : Fin 3 → Unit →₀ ℕ) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt QL weights higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of _ (blockLoadingKernel QL weights source 0 1)) :=
  kernel_hasHigherFiltration_of_crossing_injective QL weights
    (higherCrossingMap_standard_injective hR hQ weights)

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack
