/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRightWhisker
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
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

omit [AddCommGroup Y] in
/-- Mirror words of Khovanov–Lauda words contain no red strands. -/
theorem blackWord_redFree (s : List (Letter I)) : RedFree (ℓ := ℓ) (blackWord s) := by
  simp [RedFree, blackWord, List.filterMap_map]

/-- The action of a Khovanov–Lauda word `s` on the violating quotient: append its mirror
word on the right of every boundary. -/
def blackAct {μ ν : X} (s : List (Letter I)) (hs : wt RD μ s = ν) :
    ViolatingCategory P μ ⥤ ViolatingCategory P ν :=
  violatingWhiskerRight P (blackWord s) (blackWord_redFree s)
    ((endWeight_blackWord RD _ μ s).trans hs)

variable (hP : ∀ r : (pres RD k).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

/-- A functor followed and preceded by transport along equalities of objects. -/
def conjMap {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {a b : 𝒞} {a' b' : 𝒟}
    (ha : F.obj a = a') (hb : F.obj b = b') (f : a ⟶ b) : a' ⟶ b' :=
  eqToHom ha.symm ≫ F.map f ≫ eqToHom hb

theorem conjMap_id {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {a : 𝒞} {a' : 𝒟}
    (ha : F.obj a = a') : conjMap F ha ha (𝟙 a) = 𝟙 a' := by
  simp [conjMap]

theorem conjMap_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {a b c : 𝒞}
    {a' b' c' : 𝒟} (ha : F.obj a = a') (hb : F.obj b = b') (hc : F.obj c = c')
    (f : a ⟶ b) (g : b ⟶ c) :
    conjMap F ha hc (f ≫ g) = conjMap F ha hb f ≫ conjMap F hb hc g := by
  simp [conjMap]

/-- The mirror image of a Khovanov–Lauda diagram, as a diagram between mirror words. -/
def blackMirrorHom {μ : X} {s t : List (Letter I)}
    (ψ : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    P.obj (obj RD (fun r => (Λ r).val) μ (blackWord s)) ⟶
      P.obj (obj RD (fun r => (Λ r).val) μ (blackWord t)) :=
  conjMap (blackMirrorInto RD (fun r => (Λ r).val) P hP)
    (congrArg P.obj (blackMirror_obj_ob RD _ μ s))
    (congrArg P.obj (blackMirror_obj_ob RD _ μ t)) ψ

theorem blackMirrorHom_id {μ : X} (s : List (Letter I)) :
    blackMirrorHom P hP (𝟙 ((pres RD k).obj (ob RD μ s))) = 𝟙 _ :=
  conjMap_id _ _

theorem blackMirrorHom_comp {μ : X} {s t u : List (Letter I)}
    (ψ : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))
    (ψ' : (pres RD k).obj (ob RD μ t) ⟶ (pres RD k).obj (ob RD μ u)) :
    blackMirrorHom P hP (ψ ≫ ψ') = blackMirrorHom P hP ψ ≫ blackMirrorHom P hP ψ' :=
  conjMap_comp _ _ _ _ _ _

/-- The action of a Khovanov–Lauda 2-morphism `ψ : s ⟶ t` on the violating quotient. -/
def blackMap {μ ν : X} {s t : List (Letter I)} (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (ψ : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    blackAct P s hs ⟶ blackAct P t ht :=
  violatingWhiskerLeft P (blackWord_redFree s) (blackWord_redFree t)
    ((endWeight_blackWord RD _ μ s).trans hs) ((endWeight_blackWord RD _ μ t).trans ht)
    (blackMirrorHom P hP ψ)

/-- Identity diagrams act by identities. -/
theorem blackMap_id {μ ν : X} {s : List (Letter I)} (hs : wt RD μ s = ν) :
    blackMap P hP hs hs (𝟙 _) = 𝟙 (blackAct P s hs) := by
  rw [blackMap, blackMirrorHom_id]
  exact violatingWhiskerLeft_id P _ _

/-- Vertical composition of diagrams acts by composition. -/
theorem blackMap_comp {μ ν : X} {s t u : List (Letter I)} (hs : wt RD μ s = ν)
    (ht : wt RD μ t = ν) (hu : wt RD μ u = ν)
    (ψ : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))
    (ψ' : (pres RD k).obj (ob RD μ t) ⟶ (pres RD k).obj (ob RD μ u)) :
    blackMap P hP hs hu (ψ ≫ ψ') = blackMap P hP hs ht ψ ≫ blackMap P hP ht hu ψ' := by
  rw [blackMap, blackMirrorHom_comp]
  exact violatingWhiskerLeft_comp P _ _ _ _ _ _ _ _

end Categorification.Stendhal.DoubleDiagram
