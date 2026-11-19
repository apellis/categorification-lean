/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackAction
import Categorification.WeightedKLR.RedStrands.DoubleRightWhiskerComp

/-!
# The action of a composite Khovanov–Lauda word

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. The action of a concatenation `s ++ t` of
Khovanov–Lauda words on the violating quotient is the action of `t` followed by the action
of `s`: the mirror word of `s ++ t` is the mirror word of `t` followed by that of `s`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

/-- Right whiskering depends only on the word. -/
theorem violatingWhiskerRight_congr {μ ν : X} {v v' : List (DoubleStrand I ℓ)} (h : v = v')
    (hv : RedFree v) (hv' : RedFree v') (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    (hν' : endWeight RD (fun r => (Λ r).val) μ v' = ν) :
    violatingWhiskerRight P v hv hν = violatingWhiskerRight P v' hv' hν' := by
  subst h; rfl

omit [AddCommGroup X] [AddCommGroup Y] in
theorem blackWord_append' (s t : List (Letter I)) :
    blackWord (ℓ := ℓ) (s ++ t) = blackWord t ++ blackWord s := by
  simp [blackWord]

/-- The action of `s ++ t` is the action of `t` followed by the action of `s` (Webster,
arXiv:1309.3796v3, §4.5, Theorem 4.28). -/
def blackActAppend {μ ν₁ ν₂ : X} (s t : List (Letter I)) (ht : wt RD μ t = ν₁)
    (hs : wt RD ν₁ s = ν₂) (hst : wt RD μ (s ++ t) = ν₂) :
    blackAct P (s ++ t) hst ≅ blackAct P t ht ⋙ blackAct P s hs :=
  eqToIso (violatingWhiskerRight_congr P (blackWord_append' s t) _
      (redFree_append (blackWord_redFree t) (blackWord_redFree s)) _
      (endWeight_append_of_eq ((endWeight_blackWord RD _ μ t).trans ht)
        ((endWeight_blackWord RD _ ν₁ s).trans hs))) ≪≫
    violatingWhiskerRightAppend P (blackWord_redFree t) (blackWord_redFree s)
      ((endWeight_blackWord RD _ μ t).trans ht) ((endWeight_blackWord RD _ ν₁ s).trans hs)

end Categorification.Stendhal.DoubleDiagram
