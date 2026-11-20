/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackAction

/-!
# The black action is additive on 2-morphisms

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. The action `ψ ↦` (action of `ψ`) of
Khovanov–Lauda 2-morphisms on the violating quotients is additive: sums of diagrams act by
sums of natural transformations. This is what lets the decompositions of the
Khovanov–Lauda 2-category (for instance `E_i F_i ≅ F_i E_i ⊕ 1^{⊕ n}`) pass to the action.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

section Whisker

variable {μ ν : X} {v v' : List (DoubleStrand I ℓ)} (hv : RedFree v) (hv' : RedFree v')
  (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
  (hν' : endWeight RD (fun r => (Λ r).val) μ v' = ν)

theorem violatingWhiskerLeft_add
    (φ φ' : P.obj (obj RD (fun r => (Λ r).val) μ v) ⟶
      P.obj (obj RD (fun r => (Λ r).val) μ v')) :
    violatingWhiskerLeft P hv hv' hν hν' (φ + φ') =
      violatingWhiskerLeft P hv hv' hν hν' φ + violatingWhiskerLeft P hv hv' hν hν' φ' := by
  ext ⟨x⟩
  rw [NatTrans.app_add]
  change (violatingFunctor P ν).map ((whiskerLeft P hv hv' hν hν' (φ + φ')).app x) =
    (violatingFunctor P ν).map ((whiskerLeft P hv hv' hν hν' φ).app x) +
      (violatingFunctor P ν).map ((whiskerLeft P hv hv' hν hν' φ').app x)
  rw [← Functor.map_add]
  congr 1
  ext
  rw [whiskerLeft_app_hom]
  change _ = ((whiskerLeft P hv hv' hν hν' φ).app x).hom + ((whiskerLeft P hv hv' hν hν' φ').app x).hom
  rw [whiskerLeft_app_hom, whiskerLeft_app_hom, P.wL_add, Preadditive.add_comp,
    Preadditive.comp_add]
  rfl

theorem violatingWhiskerLeft_smul (c : k)
    (φ : P.obj (obj RD (fun r => (Λ r).val) μ v) ⟶ P.obj (obj RD (fun r => (Λ r).val) μ v')) :
    violatingWhiskerLeft P hv hv' hν hν' (c • φ) = c • violatingWhiskerLeft P hv hv' hν hν' φ := by
  ext ⟨x⟩
  rw [NatTrans.app_smul]
  change (violatingFunctor P ν).map ((whiskerLeft P hv hv' hν hν' (c • φ)).app x) =
    c • (violatingFunctor P ν).map ((whiskerLeft P hv hv' hν hν' φ).app x)
  rw [← Functor.map_smul]
  congr 1
  ext
  rw [whiskerLeft_app_hom]
  change _ = c • ((whiskerLeft P hv hv' hν hν' φ).app x).hom
  rw [whiskerLeft_app_hom, P.wL_smul, Linear.smul_comp, Linear.comp_smul]
  rfl

theorem violatingWhiskerLeft_zero :
    violatingWhiskerLeft P hv hv' hν hν' 0 = 0 := by
  simpa using violatingWhiskerLeft_smul P hv hv' hν hν' (0 : k) 0

end Whisker

variable (hP : ∀ r : (pres RD k).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

section Black

variable {μ ν : X} {s t : List (Letter I)} (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)

theorem blackMirrorHom_add (ψ ψ' : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    blackMirrorHom P hP (ψ + ψ') = blackMirrorHom P hP ψ + blackMirrorHom P hP ψ' := by
  simp only [blackMirrorHom, conjMap]
  erw [Functor.map_add]
  rw [Preadditive.add_comp, Preadditive.comp_add]

theorem blackMirrorHom_smul (c : k)
    (ψ : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    blackMirrorHom P hP (c • ψ) = c • blackMirrorHom P hP ψ := by
  simp only [blackMirrorHom, conjMap]
  erw [Functor.map_smul]
  rw [Linear.smul_comp, Linear.comp_smul]

/-- Sums of Khovanov–Lauda diagrams act by sums. -/
theorem blackMap_add (ψ ψ' : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    blackMap P hP hs ht (ψ + ψ') = blackMap P hP hs ht ψ + blackMap P hP hs ht ψ' := by
  rw [blackMap, blackMirrorHom_add]
  exact violatingWhiskerLeft_add P _ _ _ _ _ _

/-- Scalar multiples of Khovanov–Lauda diagrams act by scalar multiples. -/
theorem blackMap_smul (c : k)
    (ψ : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    blackMap P hP hs ht (c • ψ) = c • blackMap P hP hs ht ψ := by
  rw [blackMap, blackMirrorHom_smul]
  exact violatingWhiskerLeft_smul P _ _ _ _ _ _

theorem blackMap_zero : blackMap P hP hs ht 0 = 0 := by
  simpa using blackMap_smul P hP hs ht (0 : k) 0

theorem blackMap_sum {ι : Type*} (S : Finset ι)
    (ψ : ι → ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))) :
    blackMap P hP hs ht (∑ j ∈ S, ψ j) = ∑ j ∈ S, blackMap P hP hs ht (ψ j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, blackMap_zero]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, blackMap_add, ih]

end Black

end Categorification.Stendhal.DoubleDiagram
