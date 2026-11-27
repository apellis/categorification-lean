/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionAdditive
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionQ

/-!
# The black action is additive on 2-morphisms

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. The action `ψ ↦` (action of `ψ`) of
Khovanov–Lauda 2-morphisms on the violating quotients is additive: sums of diagrams act by
sums of natural transformations. This is what lets the decompositions of the
Khovanov–Lauda 2-category (for instance `E_i F_i ≅ F_i E_i ⊕ 1^{⊕ n}`) pass to the action.

This is the version of `DoubleBlackActionAdditive` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

section Whisker

variable {μ ν : X} {v v' : List (DoubleStrand I ℓ)} (hv : RedFree v) (hv' : RedFree v')
  (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
  (hν' : endWeight RD (fun r => (Λ r).val) μ v' = ν)

end Whisker

variable (hP : ∀ r : (CLQ.pres RD k sc).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

section Black

variable {μ ν : X} {s t : List (Letter I)} (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)

theorem blackMirrorHom_addQ (ψ ψ' : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    blackMirrorHomQ P hP (ψ + ψ') = blackMirrorHomQ P hP ψ + blackMirrorHomQ P hP ψ' := by
  simp only [blackMirrorHomQ, conjMap]
  erw [Functor.map_add]
  rw [Preadditive.add_comp, Preadditive.comp_add]

theorem blackMirrorHom_smulQ (c : k)
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    blackMirrorHomQ P hP (c • ψ) = c • blackMirrorHomQ P hP ψ := by
  simp only [blackMirrorHomQ, conjMap]
  erw [Functor.map_smul]
  rw [Linear.smul_comp, Linear.comp_smul]

/-- Sums of Khovanov–Lauda diagrams act by sums. -/
theorem blackMap_addQ (ψ ψ' : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    blackMapQ P hP hs ht (ψ + ψ') = blackMapQ P hP hs ht ψ + blackMapQ P hP hs ht ψ' := by
  rw [blackMapQ, blackMirrorHom_addQ]
  exact violatingWhiskerLeft_add P _ _ _ _ _ _

/-- Scalar multiples of Khovanov–Lauda diagrams act by scalar multiples. -/
theorem blackMap_smulQ (c : k)
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    blackMapQ P hP hs ht (c • ψ) = c • blackMapQ P hP hs ht ψ := by
  rw [blackMapQ, blackMirrorHom_smulQ]
  exact violatingWhiskerLeft_smul P _ _ _ _ _ _

theorem blackMap_zeroQ : blackMapQ P hP hs ht 0 = 0 := by
  simpa using blackMap_smulQ P hP hs ht (0 : k) 0

theorem blackMap_sumQ {ι : Type*} (S : Finset ι)
    (ψ : ι → ((CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t))) :
    blackMapQ P hP hs ht (∑ j ∈ S, ψ j) = ∑ j ∈ S, blackMapQ P hP hs ht (ψ j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, blackMap_zeroQ]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, blackMap_addQ, ih]

end Black

end Categorification.Stendhal.DoubleDiagram
