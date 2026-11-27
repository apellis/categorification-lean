/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackAction
import Categorification.WeightedKLR.RedStrands.DoubleRightWhisker
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation

/-!
# Black Khovanov–Lauda diagrams act on the violating quotient

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. A 1-morphism of the Khovanov–Lauda
2-category, a word `s` in the letters `E_i`, `F_i`, acts on the violating quotient by
appending its mirror word `blackWord s` on the right of every boundary. A 2-morphism
`ψ : s ⟶ t` acts by placing its mirror image to the right of every diagram. This file
constructs these functors and natural transformations and proves that the assignment
`ψ ↦` (action of `ψ`) preserves identities and composition, in any signed presentation in
which the mirrored Khovanov–Lauda relations hold.

This is the version of `DoubleBlackAction` in which the black strands carry the relations of
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

variable (hP : ∀ r : (CLQ.pres RD k sc).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

/-- The mirror image of a Khovanov–Lauda diagram, as a diagram between mirror words. -/
def blackMirrorHomQ {μ : X} {s t : List (Letter I)}
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    P.obj (obj RD (fun r => (Λ r).val) μ (blackWord s)) ⟶
      P.obj (obj RD (fun r => (Λ r).val) μ (blackWord t)) :=
  conjMap (blackMirrorIntoOf RD (fun r => (Λ r).val) (CLQ.pres RD k sc) (clqPres_wfDomQ RD k sc) P hP)
    (congrArg P.obj (blackMirror_obj_ob RD _ μ s))
    (congrArg P.obj (blackMirror_obj_ob RD _ μ t)) ψ

theorem blackMirrorHom_idQ {μ : X} (s : List (Letter I)) :
    blackMirrorHomQ P hP (𝟙 ((CLQ.pres RD k sc).obj (ob RD μ s))) = 𝟙 _ :=
  conjMap_id _ _

theorem blackMirrorHom_compQ {μ : X} {s t u : List (Letter I)}
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t))
    (ψ' : (CLQ.pres RD k sc).obj (ob RD μ t) ⟶ (CLQ.pres RD k sc).obj (ob RD μ u)) :
    blackMirrorHomQ P hP (ψ ≫ ψ') = blackMirrorHomQ P hP ψ ≫ blackMirrorHomQ P hP ψ' :=
  conjMap_comp _ _ _ _ _ _

/-- The action of a Khovanov–Lauda 2-morphism `ψ : s ⟶ t` on the violating quotient. -/
def blackMapQ {μ ν : X} {s t : List (Letter I)} (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    blackAct P s hs ⟶ blackAct P t ht :=
  violatingWhiskerLeft P (blackWord_redFree s) (blackWord_redFree t)
    ((endWeight_blackWord RD _ μ s).trans hs) ((endWeight_blackWord RD _ μ t).trans ht)
    (blackMirrorHomQ P hP ψ)

/-- Identity diagrams act by identities. -/
theorem blackMap_idQ {μ ν : X} {s : List (Letter I)} (hs : wt RD μ s = ν) :
    blackMapQ P hP hs hs (𝟙 _) = 𝟙 (blackAct P s hs) := by
  rw [blackMapQ, blackMirrorHom_idQ]
  exact violatingWhiskerLeft_id P _ _

/-- Vertical composition of diagrams acts by composition. -/
theorem blackMap_compQ {μ ν : X} {s t u : List (Letter I)} (hs : wt RD μ s = ν)
    (ht : wt RD μ t = ν) (hu : wt RD μ u = ν)
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t))
    (ψ' : (CLQ.pres RD k sc).obj (ob RD μ t) ⟶ (CLQ.pres RD k sc).obj (ob RD μ u)) :
    blackMapQ P hP hs hu (ψ ≫ ψ') = blackMapQ P hP hs ht ψ ≫ blackMapQ P hP ht hu ψ' := by
  rw [blackMapQ, blackMirrorHom_compQ]
  exact violatingWhiskerLeft_comp P _ _ _ _ _ _ _ _

end Categorification.Stendhal.DoubleDiagram
